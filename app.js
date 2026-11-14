"use strict";

/* ==========================================================
   مختبر تصميم شبكات المياه V4
   Darcy-Weisbach / Hazen-Williams
   Hardy Cross / Newton–Raphson / Global Gradient Algorithm (GGA)
   منحنيات أداء مضخات التقوية (افتراضي / كتالوج)
   ========================================================== */

const SVG_NS = "http://www.w3.org/2000/svg";
const svg = document.getElementById("network");
const pipesLayer = document.getElementById("pipesLayer");
const nodesLayer = document.getElementById("nodesLayer");
const statusBox = document.getElementById("status");
const detailsContent = document.getElementById("detailsContent");
const modeBadge = document.getElementById("modeBadge");
const analysisReport = document.getElementById("analysisReport");
const analysisBadge = document.getElementById("analysisBadge");
const solverMethodSelect = document.getElementById("solverMethod");
const waterTempInput = document.getElementById("waterTemp");

const materialSelect = document.getElementById("materialSelect");
const materialRoughnessInput = document.getElementById("materialRoughness");

const STANDARD_DIAMETERS = {
  20: 0.016, 25: 0.020, 32: 0.026, 40: 0.032, 50: 0.040,
  63: 0.051, 75: 0.061, 90: 0.073, 110: 0.090, 125: 0.102,
  160: 0.131, 200: 0.163, 250: 0.204, 315: 0.257,
  400: 0.326, 500: 0.408, 630: 0.514
};

// قيم العناصر الجاهزة هي القيم المستخدمة في الإصدار السابق؛
// يمكن تعديل K لكل عنصر من نموذج خصائص الأنبوب.
const MINOR_LOSS_PRESETS = [
  { id: "elbow_90_short", name: "كوع 90° قصير", k: 0.9 },
  { id: "elbow_90_long", name: "كوع 90° طويل", k: 0.6 },
  { id: "elbow_45", name: "كوع 45°", k: 0.4 },
  { id: "elbow_180", name: "كوع 180°", k: 1.5 },
  { id: "tee_run", name: "تي مرور مباشر", k: 0.4 },
  { id: "tee_branch", name: "تي تفرع جانبي", k: 1.5 },
  { id: "coupler", name: "وصلة مستقيمة", k: 0.05 },
  { id: "valve_gate", name: "محبس بوابي", kind: "valve", valveType: "gate", valveOpen: 100 },
  { id: "valve_globe", name: "محبس غلوب", kind: "valve", valveType: "globe", valveOpen: 100 },
  { id: "valve_butterfly", name: "محبس فراشة", kind: "valve", valveType: "butterfly", valveOpen: 100 }
];

const buttons = {
  source: document.getElementById("addSource"),
  junction: document.getElementById("addJunction"),
  demand: document.getElementById("addDemand"),
  connect: document.getElementById("connect"),
  calculate: document.getElementById("calculateNetwork"),
  delete: document.getElementById("deleteElement"),
  clear: document.getElementById("clearNetwork"),
  undo: document.getElementById("undoAction"),
  saveProject: document.getElementById("saveProject"),
  loadProject: document.getElementById("loadProject"),
  exportProject: document.getElementById("exportProject"),
  applyMaterial: document.getElementById("applyMaterial")
};

const STORAGE_KEY = "waterNetworkLab_v4";
const LEGACY_STORAGE_KEYS = ["waterNetworkLab_v1"];
const GRAVITY = 9.80665;

const HC_MAX_ITER = 300;
const HC_FLOW_TOL = 1e-8;       // m3/s
const HC_HEAD_TOL = 1e-5;       // m
const NEWTON_MAX_ITER = 100;
const NEWTON_HEAD_TOL = 1e-5;   // m
const NEWTON_REL_TOL = 1e-6;

const GGA_MAX_ITER = 250;
const GGA_HEAD_TOL = 1e-5;      // m
const GGA_FLOW_REL_TOL = 1e-8;
const GGA_CG_REL_TOL = 1e-13;

const MAX_HISTORY = 40;

const nodeTitles = {
  source: "مصدر",
  junction: "عقدة ربط",
  demand: "عقدة استهلاك"
};

let nodes = [];
let pipes = [];
let nextNodeId = 1;
let nextPipeId = 1;

let mode = "select";
let firstNodeId = null;
let selected = null;
let draggingNodeId = null;
let pointerStart = null;
let dragMoved = false;
let dragHistorySaved = false;
let suppressClick = false;

let hydraulicResults = null;
let historyStack = [];

/* ==========================================================
   أدوات عامة والتحقق من القيم
   ========================================================== */

function setStatus(message) {
  if (statusBox) statusBox.textContent = message;
}

function finiteNumber(value, fallback = 0) {
  if (value === null || value === undefined || value === "") return fallback;
  const number = Number(value);
  return Number.isFinite(number) ? number : fallback;
}

function hasFormValue(data, name) {
  return data.has(name) && data.get(name) !== "";
}

function formNumber(data, name, fallback = 0) {
  return hasFormValue(data, name)
    ? finiteNumber(data.get(name), fallback)
    : fallback;
}

function escapeHTML(value) {
  return String(value).replace(/[&<>"']/g, character => ({
    "&": "&amp;",
    "<": "&lt;",
    ">": "&gt;",
    '"': "&quot;",
    "'": "&#39;"
  })[character]);
}

function fmt(value, digits = 3) {
  const number = Number(value);
  if (!Number.isFinite(number)) return "--";
  return number.toLocaleString("en-US", {
    minimumFractionDigits: 0,
    maximumFractionDigits: digits
  });
}

function svgElement(tag, attributes = {}) {
  const element = document.createElementNS(SVG_NS, tag);
  Object.entries(attributes).forEach(([name, value]) => {
    element.setAttribute(name, String(value));
  });
  return element;
}

function nodeById(id) {
  return nodes.find(node => Number(node.id) === Number(id));
}

function pipeById(id) {
  return pipes.find(pipe => Number(pipe.id) === Number(id));
}

function invalidateHydraulics() {
  hydraulicResults = null;
}

function setButtonAction(element, callback) {
  if (element) element.addEventListener("click", callback);
}

/* ==========================================================
   خواص الماء عند الضغط الجوي تقريباً
   ========================================================== */

/*
  كثافة الماء:
  علاقة Kell التقريبية للماء النقي قرب الضغط الجوي.
  مجال الاستخدام في هذا التطبيق: 0 إلى 100 درجة مئوية.

  اللزوجة الديناميكية:
  علاقة IAPWS المبسطة للماء السائل عند 0.1 MPa،
  ومجالها الموصى به 253.15 إلى 383.15 K.
*/

function getWaterDensity(tempC) {
  if (!Number.isFinite(tempC) || tempC < 0 || tempC > 100) {
    throw new Error("درجة حرارة الماء يجب أن تكون بين 0 و100 °C.");
  }

  const density = 1000 * (
    1 -
    ((tempC + 288.9414) /
      (508929.2 * (tempC + 68.12963))) *
    Math.pow(tempC - 3.9863, 2)
  );

  if (!(density > 0) || !Number.isFinite(density)) {
    throw new Error("تعذر حساب كثافة الماء عند درجة الحرارة المحددة.");
  }

  return density;
}

function getWaterDynamicViscosity(tempC) {
  if (!Number.isFinite(tempC) || tempC < 0 || tempC > 100) {
    throw new Error("درجة حرارة الماء خارج مجال الحساب المعتمد.");
  }

  const T = tempC + 273.15;
  const t = T / 300;

  const mu = (
    280.68 * Math.pow(t, -1.9) +
    511.45 * Math.pow(t, -7.7) +
    61.131 * Math.pow(t, -19.6) +
    0.45903 * Math.pow(t, -40)
  ) * 1e-6;

  if (!(mu > 0) || !Number.isFinite(mu)) {
    throw new Error("تعذر حساب اللزوجة الديناميكية للماء.");
  }

  return mu;
}

function getWaterProperties() {
  const temp = waterTempInput
    ? finiteNumber(waterTempInput.value, 20)
    : 20;

  const rho = getWaterDensity(temp);
  const mu = getWaterDynamicViscosity(temp);
  const nu = mu / rho;

  return {
    temperature: temp,
    density: rho,
    dynamicViscosity: mu,
    kinematicViscosity: nu
  };
}

function getWaterViscosity() {
  return getWaterProperties().kinematicViscosity;
}

/* ==========================================================
   مكتبة الفواقد الموضعية
   ========================================================== */

function interpolate(value, table) {
  if (!Array.isArray(table) || table.length < 2) {
    throw new Error("جدول الاستيفاء غير صالح.");
  }

  // نرتب نسخة، ولا نغيّر جدول المصدر الأصلي.
  const sorted = table
    .map(row => [Number(row[0]), Number(row[1])])
    .sort((a, b) => a[0] - b[0]);

  if (value <= sorted[0][0]) return sorted[0][1];

  const last = sorted[sorted.length - 1];
  if (value >= last[0]) return last[1];

  for (let i = 0; i < sorted.length - 1; i++) {
    const [x1, y1] = sorted[i];
    const [x2, y2] = sorted[i + 1];

    if (value >= x1 && value <= x2) {
      const ratio = (value - x1) / (x2 - x1);
      return y1 + ratio * (y2 - y1);
    }
  }

  return NaN;
}

function getElbowK(type) {
  const map = {
    "90_short": 0.9,
    "90_long": 0.6,
    "45": 0.4,
    "180": 1.5
  };

  return map[type] ?? 0.9;
}

function getTeeK(type) {
  const map = {
    run: 0.4,
    branch: 1.5
  };

  return map[type] ?? 1.5;
}

function getValveK(type, openPercent) {
  const opening = Number(openPercent);

  if (!Number.isFinite(opening) || opening < 0 || opening > 100) {
    throw new Error("نسبة فتح المحبس يجب أن تكون بين 0 و100%.");
  }

  if (opening === 0) return Infinity;

  const tables = {
    gate: [
      [10, 35.0], [25, 10.0], [50, 2.06],
      [75, 1.15], [100, 0.2]
    ],
    globe: [
      [25, 200.0], [50, 50.0], [75, 20.0], [100, 10.0]
    ],
    butterfly: [
      [33, 118.0], [66, 3.9], [100, 0.4]
    ]
  };

  const table = tables[type];
  if (!table) throw new Error("نوع المحبس غير معروف.");

  // لا نستقرئ خارج مجال الجدول.
  if (opening < table[0][0]) {
    throw new Error(
      "نسبة الفتح أقل من مجال بيانات K المتاح لهذا المحبس."
    );
  }

  return interpolate(opening, table);
}

function minorLossItemK(item) {
  if (item && item.kind === "valve") {
    const open = finiteNumber(item.valveOpen, 100);
    if (open === 0) return Infinity;
    return getValveK(item.valveType || "gate", open);
  }
  return finiteNumber(item && item.k, 0);
}

function isPipeClosed(pipe) {
  // يدعم المشاريع القديمة التي لم تُحوّل بعد، وكذلك صمامات الصفوف الجديدة.
  const legacyClosed = finiteNumber(pipe.n_valve, 0) > 0 &&
    finiteNumber(pipe.valveOpen, 100) === 0;
  const listClosed = Array.isArray(pipe.minorLosses) &&
    pipe.minorLosses.some(item => item && item.kind === "valve" &&
      finiteNumber(item.count, 0) > 0 && finiteNumber(item.valveOpen, 100) === 0);
  return legacyClosed || listClosed;
}

function getPipeMinorK(pipe) {
  // الصمام المغلق يعزل الوصلة هيدروليكياً؛ لا نمثله بمعامل K ضخم.
  if (isPipeClosed(pipe)) return 0;

  if (Array.isArray(pipe.minorLosses)) {
    return pipe.minorLosses.reduce((sum, item) => {
      const count = finiteNumber(item && item.count, 0);
      if (!(count > 0)) return sum;
      return sum + count * minorLossItemK(item);
    }, 0);
  }

  // توافق احتياطي مع كائنات الأنابيب قبل إدخال قائمة الفواقد.
  let totalK = finiteNumber(pipe.kMinor, 0);
  totalK += finiteNumber(pipe.n_elbow, 0) * getElbowK(pipe.elbowType);
  totalK += finiteNumber(pipe.n_tee, 0) * getTeeK(pipe.teeType);
  if (finiteNumber(pipe.n_valve, 0) > 0) {
    totalK += finiteNumber(pipe.n_valve, 0) *
      getValveK(pipe.valveType, finiteNumber(pipe.valveOpen, 100));
  }
  totalK += finiteNumber(pipe.n_coupler, 0) * 0.05;
  return totalK;
}

function normalizeMinorLosses(pipe) {
  if (Array.isArray(pipe.minorLosses) && pipe.minorLosses.length) {
    return pipe.minorLosses.map((item, index) => {
      const kind = item && item.kind === "valve" ? "valve" : "fixed";
      const count = Math.max(0, Math.round(finiteNumber(item && item.count, 0)));
      const name = String(item && item.name || "فاقد ثانوي " + (index + 1)).trim();
      if (kind === "valve") {
        return {
          kind,
          name: name || "محبس",
          count,
          valveType: ["gate", "globe", "butterfly"].includes(item.valveType)
            ? item.valveType : "gate",
          valveOpen: Math.min(100, Math.max(0, finiteNumber(item.valveOpen, 100)))
        };
      }
      return {
        kind: "fixed",
        name: name || "فاقد ثانوي " + (index + 1),
        k: Math.max(0, finiteNumber(item && item.k, 0)),
        count
      };
    });
  }

  // ترحيل عناصر الإصدار السابق إلى صفوف مستقلة دون فقد بيانات المشروع.
  const migrated = [];
  const pushFixed = (name, k, count) => {
    const safeCount = Math.max(0, Math.round(finiteNumber(count, 0)));
    if (safeCount > 0) migrated.push({
      kind: "fixed", name, k: Math.max(0, finiteNumber(k, 0)), count: safeCount
    });
  };

  pushFixed("فاقد إضافي محفوظ من الإصدار السابق", pipe.kMinor, pipe.kMinor > 0 ? 1 : 0);
  if (finiteNumber(pipe.n_elbow, 0) > 0) {
    const map = {
      "90_short": ["كوع 90° قصير", 0.9],
      "90_long": ["كوع 90° طويل", 0.6],
      "45": ["كوع 45°", 0.4],
      "180": ["كوع 180°", 1.5]
    };
    const item = map[pipe.elbowType] || map["90_short"];
    pushFixed(item[0], item[1], pipe.n_elbow);
  }
  if (finiteNumber(pipe.n_tee, 0) > 0) {
    const isRun = pipe.teeType === "run";
    pushFixed(isRun ? "تي مرور مباشر" : "تي تفرع جانبي", isRun ? 0.4 : 1.5, pipe.n_tee);
  }
  if (finiteNumber(pipe.n_valve, 0) > 0) {
    const type = ["gate", "globe", "butterfly"].includes(pipe.valveType)
      ? pipe.valveType : "gate";
    const typeName = { gate: "بوابي", globe: "غلوب", butterfly: "فراشة" }[type];
    migrated.push({
      kind: "valve", name: "محبس " + typeName,
      count: Math.max(0, Math.round(finiteNumber(pipe.n_valve, 0))),
      valveType: type,
      valveOpen: Math.min(100, Math.max(0, finiteNumber(pipe.valveOpen, 100)))
    });
  }
  pushFixed("وصلة مستقيمة", 0.05, pipe.n_coupler);
  return migrated;
}

function renderMinorLossRows(items) {
  if (!items.length) {
    return '<p class="minor-loss-empty">لم تُضف فواقد ثانوية لهذا الأنبوب بعد.</p>';
  }

  return items.map((item, index) => {
    const isValve = item.kind === "valve";
    let k = isValve ? NaN : finiteNumber(item.k, 0);
    if (isValve) {
      try { k = minorLossItemK(item); } catch (_) { k = NaN; }
    }
    const valveOptions = [
      ["gate", "بوابي"], ["globe", "غلوب"], ["butterfly", "فراشة"]
    ].map(([value, label]) =>
      `<option value="${value}" ${item.valveType === value ? "selected" : ""}>${label}</option>`
    ).join("");

    return `
      <div class="minor-loss-row" data-minor-row="${index}" data-kind="${isValve ? "valve" : "fixed"}">
        <div class="minor-loss-field minor-loss-name">
          <label>اسم الفاقد</label>
          <input type="text" data-minor-name value="${escapeHTML(item.name)}" maxlength="80" required>
        </div>
        <div class="minor-loss-field">
          <label>معامل K</label>
          <input type="number" data-minor-k min="0" step="any"
                 value="${Number.isFinite(k) ? escapeHTML(k) : ""}" ${isValve ? "readonly" : "required"}
                 ${isValve && !Number.isFinite(k) ? 'placeholder="مغلق"' : ""}>
        </div>
        <div class="minor-loss-field">
          <label>العدد</label>
          <input type="number" data-minor-count min="0" step="1"
                 value="${escapeHTML(item.count)}" required>
        </div>
        <button type="button" class="minor-loss-remove" data-remove-minor="${index}" aria-label="حذف عنصر الفقد">حذف</button>
        ${isValve ? `
          <div class="minor-loss-valve-settings">
            <label>نوع المحبس</label>
            <select data-valve-type>${valveOptions}</select>
            <label>نسبة الفتح (%)</label>
            <input type="number" data-valve-open min="0" max="100" step="1" value="${escapeHTML(item.valveOpen)}" required>
            <small class="field-help">K معروض ومحسوب من نوع المحبس ونسبة فتحه.</small>
          </div>` : ""}
      </div>`;
  }).join("");
}

function minorLossesFromEditor(container) {
  if (!container) return [];
  return Array.from(container.querySelectorAll("[data-minor-row]")).map(row => {
    const kind = row.dataset.kind === "valve" ? "valve" : "fixed";
    const name = row.querySelector("[data-minor-name]").value.trim();
    const count = Number(row.querySelector("[data-minor-count]").value);
    if (kind === "valve") {
      return {
        kind,
        name,
        count,
        valveType: row.querySelector("[data-valve-type]").value,
        valveOpen: Number(row.querySelector("[data-valve-open]").value)
      };
    }
    return {
      kind: "fixed",
      name,
      k: Number(row.querySelector("[data-minor-k]").value),
      count
    };
  });
}

function minorLossesTotalK(items) {
  if (items.some(item => item.kind === "valve" &&
      finiteNumber(item.count, 0) > 0 && finiteNumber(item.valveOpen, 100) === 0)) {
    return 0;
  }
  return items.reduce((sum, item) => {
    const count = finiteNumber(item.count, 0);
    if (!(count > 0)) return sum;
    return sum + count * minorLossItemK(item);
  }, 0);
}

/* ==========================================================
   تطبيع بيانات المشاريع القديمة والتحقق منها
   ========================================================== */

function nearestCommercialDiameter(oldDiameter) {
  const keys = Object.keys(STANDARD_DIAMETERS).map(Number);

  return keys.reduce((best, current) => {
    const currentDiff = Math.abs(STANDARD_DIAMETERS[current] - oldDiameter);
    const bestDiff = Math.abs(STANDARD_DIAMETERS[best] - oldDiameter);
    return currentDiff < bestDiff ? current : best;
  }, keys[0]);
}

function normalizeNode(node, index) {
  const type = ["source", "junction", "demand"].includes(node.type)
    ? node.type
    : "junction";

  return {
    id: Math.max(1, Math.round(finiteNumber(node.id, index + 1))),
    type,
    x: finiteNumber(node.x, 100 + index * 50),
    y: finiteNumber(node.y, 100),
    name: String(node.name || (nodeTitles[type] + " " + (index + 1))),
    elevation: finiteNumber(node.elevation, 0),
    demand: Math.max(0, finiteNumber(node.demand, type === "demand" ? 5 : 0)),
    sourceType: node.sourceType || "tank",
    sourceMode: node.sourceMode === "flow" ? "flow" : "head",
    head: finiteNumber(node.head, 100),
    sourceFlow: Math.max(0, finiteNumber(node.sourceFlow, 30))
  };
}

/* ==========================================================
   أدوات منحنيات مضخات التقوية V4
   Q بوحدة لتر/ث و H بوحدة متر داخل بيانات المنحنى.
   ========================================================== */

function normalizePumpCurvePoints(points) {
  if (!Array.isArray(points)) return [];

  return points.map(point => ({
    q: Number(point?.q),
    h: Number(point?.h)
  })).filter(point =>
    Number.isFinite(point.q) && Number.isFinite(point.h)
  ).sort((a, b) => a.q - b.q);
}

function defaultPumpCurvePoints(H0, Qmax, segments = 12) {
  const shutoffHead = Math.max(0, finiteNumber(H0, 0));
  const maximumFlow = Math.max(0.001, finiteNumber(Qmax, 0.001));
  const count = Math.max(2, Math.round(segments));
  const points = [];

  for (let i = 0; i <= count; i++) {
    const q = maximumFlow * i / count;
    const ratio = q / maximumFlow;
    points.push({
      q,
      h: shutoffHead * (1 - ratio * ratio)
    });
  }

  return points;
}

function validatePumpCurvePoints(points, pipeId) {
  if (!Array.isArray(points) || points.length < 2) {
    throw new Error(
      "أدخل نقطتين على الأقل لمنحنى المضخة في P" + pipeId + "."
    );
  }

  const sorted = normalizePumpCurvePoints(points);
  if (sorted.length !== points.length) {
    throw new Error(
      "توجد قيمة غير رقمية في نقاط منحنى المضخة في P" + pipeId + "."
    );
  }

  for (let i = 0; i < sorted.length; i++) {
    const point = sorted[i];
    if (point.q < 0 || point.h < 0) {
      throw new Error(
        "يجب ألا يكون التصريف أو الرفع سالباً في منحنى المضخة P" + pipeId + "."
      );
    }

    if (i > 0 && point.q - sorted[i - 1].q <= 1e-9) {
      throw new Error(
        "قيم التصريف في منحنى المضخة يجب أن تكون مختلفة في P" + pipeId + "."
      );
    }
  }

  return sorted;
}

function renderPumpCurveRows(points) {
  const safePoints = Array.isArray(points) ? points : [];
  if (!safePoints.length) {
    return '<p class="muted pump-empty">لم تُدخل نقاطاً بعد. أضف النقاط يدوياً أو استورد ملف CSV.</p>';
  }

  return `
    <div class="table-wrap pump-curve-table-wrap">
      <table class="results-table pump-curve-table">
        <thead><tr><th>#</th><th>Q (لتر/ث)</th><th>H (م)</th><th>إجراء</th></tr></thead>
        <tbody>
          ${safePoints.map((point, index) => `
            <tr data-pump-point-row="${index}">
              <td>${index + 1}</td>
              <td><input type="number" min="0" step="any" data-pump-q value="${escapeHTML(point.q)}" aria-label="التصريف للنقطة ${index + 1}"></td>
              <td><input type="number" min="0" step="any" data-pump-h value="${escapeHTML(point.h)}" aria-label="الرفع للنقطة ${index + 1}"></td>
              <td><button type="button" class="secondary-button pump-remove-point" data-remove-pump-point="${index}" aria-label="حذف النقطة ${index + 1}">حذف</button></td>
            </tr>`).join("")}
        </tbody>
      </table>
    </div>`;
}

function renderPumpCurvePreview(points) {
  const safePoints = normalizePumpCurvePoints(points);
  if (safePoints.length < 2) {
    return '<p class="muted">يظهر رسم H–Q بعد إدخال نقطتين صحيحتين على الأقل.</p>';
  }

  const width = 320;
  const height = 178;
  const left = 38;
  const right = 12;
  const top = 12;
  const bottom = 30;
  const plotW = width - left - right;
  const plotH = height - top - bottom;
  const maxQ = Math.max(safePoints[safePoints.length - 1].q, 1e-9);
  const maxH = Math.max(...safePoints.map(point => point.h), 1e-9);
  const coords = safePoints.map(point => {
    const x = left + (point.q / maxQ) * plotW;
    const y = top + (1 - point.h / maxH) * plotH;
    return `${x.toFixed(2)},${y.toFixed(2)}`;
  }).join(" ");

  return `
    <svg class="pump-curve-svg" viewBox="0 0 ${width} ${height}" role="img" aria-label="منحنى أداء المضخة: الرفع مقابل التصريف">
      <line x1="${left}" y1="${top}" x2="${left}" y2="${top + plotH}" />
      <line x1="${left}" y1="${top + plotH}" x2="${width - right}" y2="${top + plotH}" />
      <polyline points="${coords}" />
      ${safePoints.map(point => {
        const x = left + (point.q / maxQ) * plotW;
        const y = top + (1 - point.h / maxH) * plotH;
        return `<circle cx="${x.toFixed(2)}" cy="${y.toFixed(2)}" r="3" />`;
      }).join("")}
      <text x="${left - 8}" y="${top + 4}" text-anchor="end">${maxH.toFixed(2)}</text>
      <text x="${left - 8}" y="${top + plotH + 3}" text-anchor="end">0</text>
      <text x="${left + plotW / 2}" y="${height - 5}" text-anchor="middle">Q (لتر/ث)</text>
      <text x="9" y="${top + plotH / 2}" text-anchor="middle" transform="rotate(-90 9 ${top + plotH / 2})">H (م)</text>
    </svg>`;
}

function parsePumpCurveCSV(text) {
  const lines = String(text || "").replace(/^\uFEFF/, "").split(/\r?\n/);
  const points = [];
  let firstNonEmptySeen = false;

  lines.forEach((line, index) => {
    const trimmed = line.trim();
    if (!trimmed) return;
    const parts = trimmed.split(/[;,\t]/).map(value => value.trim());
    if (parts.length < 2) {
      throw new Error("تنسيق CSV غير صحيح في السطر " + (index + 1) + ".");
    }

    const q = Number(parts[0]);
    const h = Number(parts[1]);
    if (!Number.isFinite(q) || !Number.isFinite(h)) {
      // يسمح بسطر عناوين واحد في أول سطر غير فارغ.
      if (!points.length && !firstNonEmptySeen) {
        firstNonEmptySeen = true;
        return;
      }
      throw new Error("تعذر قراءة Q وH في السطر " + (index + 1) + ". استخدم Q,H بالأرقام.");
    }
    firstNonEmptySeen = true;
    points.push({ q, h });
  });

  if (points.length < 2) {
    throw new Error("ملف CSV يجب أن يحتوي على نقطتين رقميتين على الأقل.");
  }
  return validatePumpCurvePoints(points, "CSV");
}

function readPumpCurveEditorPoints(container) {
  if (!container) return [];
  const rows = Array.from(container.querySelectorAll("[data-pump-point-row]"));
  return rows.map((row, index) => {
    const qInput = row.querySelector("[data-pump-q]");
    const hInput = row.querySelector("[data-pump-h]");
    const q = qInput && qInput.value.trim() !== "" ? Number(qInput.value) : NaN;
    const h = hInput && hInput.value.trim() !== "" ? Number(hInput.value) : NaN;
    if (!Number.isFinite(q) || !Number.isFinite(h)) {
      throw new Error("أكمل قيمتي Q وH في نقطة المنحنى رقم " + (index + 1) + ".");
    }
    return { q, h };
  });
}

function normalizePipe(pipe, index) {
  const oldD = finiteNumber(pipe.D, 0.2);

  let diameterMm = Number(pipe.D_mm);
  if (!STANDARD_DIAMETERS[diameterMm]) {
    diameterMm = nearestCommercialDiameter(oldD);
  }

  // توافق خلفي: المشاريع القديمة تبقى على القطر التجاري المختار.
  // في الوضع اليدوي تكون قيمة D_inner_mm هي القطر الفعلي المستخدم حسابياً.
  const diameterMode = pipe.diameterMode === "manual" ? "manual" : "commercial";
  const manualInnerMm = finiteNumber(
    pipe.D_inner_mm,
    STANDARD_DIAMETERS[diameterMm] * 1000
  );
  const innerDiameterMm = diameterMode === "manual"
    ? manualInnerMm
    : STANDARD_DIAMETERS[diameterMm] * 1000;

  return {
    id: Math.max(1, Math.round(finiteNumber(pipe.id, index + 1))),
    a: Math.round(finiteNumber(pipe.a, 0)),
    b: Math.round(finiteNumber(pipe.b, 0)),

    L: finiteNumber(pipe.L, 100),
    diameterMode,
    D_mm: diameterMm,
    D_inner_mm: innerDiameterMm,
    D: innerDiameterMm / 1000,

    eps: finiteNumber(pipe.eps, 0.00015),
    // القائمة الجديدة تحفظ كل عنصر فقد ثانوي منفرداً للأنبوب نفسه.
    minorLosses: normalizeMinorLosses(pipe),
    kMinor: 0,
    q0: finiteNumber(pipe.q0, 0),
    flowMode: pipe.flowMode === "manualInitial" ? "manualInitial" : "auto",
    qTarget: Math.max(0, finiteNumber(pipe.qTarget, 0)),
    velocityMin: Math.max(0, finiteNumber(pipe.velocityMin, 0.5)),
    velocityTarget: Math.max(0, finiteNumber(pipe.velocityTarget, 1.2)),
    velocityMax: Math.max(0, finiteNumber(pipe.velocityMax, 2.0)),
    pMaxBar: finiteNumber(pipe.pMaxBar, 10),

    equation: pipe.equation === "hw" ? "hw" : "dw",
    C: finiteNumber(pipe.C, 130),

    isPump: pipe.isPump === true,
    pumpType: "booster",
    pumpMode: pipe.pumpMode === "catalog" ? "catalog" : "default",
    H0: finiteNumber(pipe.H0, 50),
    Qmax: finiteNumber(pipe.Qmax, 50),
    pumpCompany: String(pipe.pumpCompany || ""),
    pumpModel: String(pipe.pumpModel || ""),
    pumpRpm: finiteNumber(pipe.pumpRpm, 1450),
    pumpCurvePoints: normalizePumpCurvePoints(pipe.pumpCurvePoints),

    // الحقول القديمة أبقيناها بصفر للتوافق مع استيراد المشاريع القديمة فقط.
    n_elbow: 0,
    elbowType: "90_short",
    n_tee: 0,
    teeType: "branch",
    n_valve: 0,
    valveType: "gate",
    valveOpen: 100,
    n_coupler: 0
  };
}

function validateNetworkData() {
  if (nodes.length < 2 || pipes.length < 1) {
    throw new Error("أضف عقدتين على الأقل وأنبوباً واحداً.");
  }

  const nodeIds = new Set();

  for (const node of nodes) {
    if (nodeIds.has(node.id)) {
      throw new Error("يوجد رقم عقدة مكرر.");
    }

    nodeIds.add(node.id);

    if (!Number.isFinite(node.x) || !Number.isFinite(node.y)) {
      throw new Error("إحداثيات إحدى العقد غير صحيحة.");
    }

    if (node.type === "demand" && node.demand < 0) {
      throw new Error("طلب عقدة الاستهلاك لا يمكن أن يكون سالباً.");
    }

    if (node.type === "source" && node.sourceFlow < 0) {
      throw new Error("تصريف المصدر لا يمكن أن يكون سالباً.");
    }
  }

  const pipeIds = new Set();

  for (const pipe of pipes) {
    if (pipeIds.has(pipe.id)) {
      throw new Error("يوجد رقم أنبوب مكرر.");
    }

    pipeIds.add(pipe.id);

    if (!nodeIds.has(pipe.a) || !nodeIds.has(pipe.b)) {
      throw new Error("الأنبوب P" + pipe.id + " مرتبط بعقدة غير موجودة.");
    }

    if (pipe.a === pipe.b) {
      throw new Error("لا يمكن توصيل الأنبوب بالعقدة نفسها من الطرفين.");
    }

    if (!(pipe.L > 0) || !(pipe.D > 0)) {
      throw new Error("الطول والقطر يجب أن يكونا أكبر من الصفر في P" + pipe.id + ".");
    }

    if (pipe.eps < 0) {
      throw new Error("الخشونة المطلقة لا يمكن أن تكون سالبة.");
    }

    if (pipe.C <= 0) {
      throw new Error("معامل Hazen-Williams يجب أن يكون أكبر من الصفر.");
    }

    if (!Array.isArray(pipe.minorLosses)) {
      throw new Error("قائمة الفواقد الثانوية غير صحيحة في الأنبوب P" + pipe.id + ".");
    }

    for (const item of pipe.minorLosses) {
      if (!String(item.name || "").trim()) {
        throw new Error("اكتب اسم كل فاقد ثانوي في الأنبوب P" + pipe.id + ".");
      }
      if (!Number.isInteger(item.count) || item.count < 0) {
        throw new Error("عدد عناصر الفقد يجب أن يكون عدداً صحيحاً غير سالب في P" + pipe.id + ".");
      }
      if (item.kind === "valve") {
        if (!Number.isFinite(item.valveOpen) || item.valveOpen < 0 || item.valveOpen > 100) {
          throw new Error("نسبة فتح المحبس يجب أن تكون بين 0 و100% في P" + pipe.id + ".");
        }
        if (item.valveOpen > 0) getValveK(item.valveType, item.valveOpen);
      } else if (!Number.isFinite(item.k) || item.k < 0) {
        throw new Error("قيمة K يجب أن تكون رقماً غير سالب في P" + pipe.id + ".");
      }
    }

    if (pipe.isPump) {
      if (pipe.pumpMode === "catalog") {
        validatePumpCurvePoints(pipe.pumpCurvePoints, pipe.id);
        if (!(pipe.pumpRpm > 0)) {
          throw new Error("سرعة دوران المضخة يجب أن تكون أكبر من الصفر في P" + pipe.id + ".");
        }
      } else if (!(pipe.H0 >= 0) || !(pipe.Qmax > 0)) {
        throw new Error("بيانات المنحنى الافتراضي غير صحيحة: H0 يجب ألا يكون سالباً وQmax أكبر من الصفر في P" + pipe.id + ".");
      }
    }
  }

  getWaterProperties();
}

/* ==========================================================
   الحفظ التلقائي والتراجع
   ========================================================== */

function getNetworkSnapshot() {
  return JSON.stringify({
    nodes,
    pipes,
    nextNodeId,
    nextPipeId
  });
}

/*
  تحفظ الحالة السابقة مباشرة قبل التعديل.
  لذلك لا نحتاج إلى إدخال الحالة الجديدة في سجل التراجع.
*/

function saveHistory() {
  const state = getNetworkSnapshot();

  if (historyStack.length &&
      historyStack[historyStack.length - 1] === state) {
    return;
  }

  historyStack.push(state);

  if (historyStack.length > MAX_HISTORY) {
    historyStack.shift();
  }
}

function saveNetwork() {
  try {
    localStorage.setItem(STORAGE_KEY, getNetworkSnapshot());
    return true;
  } catch (error) {
    setStatus("تعذر الحفظ التلقائي في المتصفح.");
    return false;
  }
}

function restoreNetworkState(data) {
  if (!data ||
      !Array.isArray(data.nodes) ||
      !Array.isArray(data.pipes)) {
    throw new Error("ملف المشروع لا يحتوي على بيانات شبكة صالحة.");
  }

  nodes = data.nodes.map(normalizeNode);
  pipes = data.pipes.map(normalizePipe);

  const nodeIds = new Set();

  for (const node of nodes) {
    if (nodeIds.has(node.id)) {
      throw new Error("ملف المشروع يحتوي على أرقام عقد مكررة.");
    }
    nodeIds.add(node.id);
  }

  const pipeIds = new Set();

  for (const pipe of pipes) {
    if (pipeIds.has(pipe.id)) {
      throw new Error("ملف المشروع يحتوي على أرقام أنابيب مكررة.");
    }
    pipeIds.add(pipe.id);

    if (!nodeIds.has(pipe.a) || !nodeIds.has(pipe.b)) {
      throw new Error(
        "الأنبوب P" + pipe.id +
        " يشير إلى عقدة غير موجودة في ملف المشروع."
      );
    }
  }

  const maxNodeId = nodes.reduce(
    (max, node) => Math.max(max, node.id), 0
  );

  const maxPipeId = pipes.reduce(
    (max, pipe) => Math.max(max, pipe.id), 0
  );

  nextNodeId = Math.max(
    maxNodeId + 1,
    Math.round(finiteNumber(data.nextNodeId, maxNodeId + 1))
  );

  nextPipeId = Math.max(
    maxPipeId + 1,
    Math.round(finiteNumber(data.nextPipeId, maxPipeId + 1))
  );

  selected = null;
  firstNodeId = null;
  mode = "select";

  invalidateHydraulics();
}

function loadNetwork() {
  try {
    let raw = localStorage.getItem(STORAGE_KEY);
    let loadedLegacy = false;

    if (!raw) {
      for (const legacyKey of LEGACY_STORAGE_KEYS) {
        raw = localStorage.getItem(legacyKey);
        if (raw) {
          loadedLegacy = true;
          break;
        }
      }
    }

    if (!raw) return false;

    const data = JSON.parse(raw);
    restoreNetworkState(data);
    if (loadedLegacy) saveNetwork();
    return true;
  } catch (error) {
    nodes = [];
    pipes = [];
    nextNodeId = 1;
    nextPipeId = 1;
    invalidateHydraulics();

    setStatus("تعذر تحميل الحفظ السابق: " + error.message);
    return false;
  }
}

function undoAction() {
  if (!historyStack.length) {
    setStatus("لا توجد خطوات سابقة للتراجع عنها.");
    return;
  }

  try {
    const previous = JSON.parse(historyStack.pop());
    restoreNetworkState(previous);
    saveNetwork();
    render();
    setStatus("تم التراجع عن آخر تعديل.");
  } catch (error) {
    setStatus("تعذر تنفيذ التراجع: " + error.message);
  }
}

/* ==========================================================
   إدارة العقد والأنابيب
   ========================================================== */

function addNode(type) {
  if (!nodeTitles[type]) return;

  saveHistory();

  const count = nodes.length;
  const id = nextNodeId++;

  const node = {
    id,
    type,
    x: 130 + (count % 4) * 155,
    y: 100 + Math.floor(count / 4) * 115,
    name: nodeTitles[type] + " " + id,
    elevation: 0,
    demand: type === "demand" ? 5 : 0,
    sourceType: "tank",
    sourceMode: "head",
    head: 100,
    sourceFlow: 30
  };

  nodes.push(node);

  invalidateHydraulics();
  saveNetwork();

  selected = { type: "node", id };
  mode = "select";
  firstNodeId = null;

  render();
  setStatus("أضيفت " + nodeTitles[type] + ".");
}

function handleConnectClick(id) {
  const node = nodeById(id);

  if (!node) {
    setStatus("لم يتم العثور على العقدة.");
    return;
  }

  if (firstNodeId === null) {
    firstNodeId = id;
    selected = { type: "node", id };
    render();
    setStatus("تم اختيار " + node.name + ". اختر العقدة الثانية.");
    return;
  }

  if (Number(firstNodeId) === Number(id)) {
    setStatus("اختر عقدة أخرى.");
    return;
  }

  const startId = Number(firstNodeId);
  const endId = Number(id);

  const parallelExists = pipes.some(pipe =>
    (pipe.a === startId && pipe.b === endId) ||
    (pipe.a === endId && pipe.b === startId)
  );

  // يسمح التطبيق بالأنابيب المتوازية؛ لكل أنبوب خواصه ونتائجه المستقلة.
  saveHistory();

  const defaultDmm = 110;

  const pipe = normalizePipe({
    id: nextPipeId++,
    a: startId,
    b: endId,
    L: 100,
    diameterMode: "commercial",
    D_mm: defaultDmm,
    D_inner_mm: STANDARD_DIAMETERS[defaultDmm] * 1000,
    D: STANDARD_DIAMETERS[defaultDmm],
    eps: materialRoughnessInput
      ? finiteNumber(materialRoughnessInput.value, 0.00015)
      : 0.00015,
    kMinor: 0,
    q0: 0,
    pMaxBar: 10,
    equation: "dw",
    C: 130
  }, pipes.length);

  pipes.push(pipe);

  invalidateHydraulics();
  saveNetwork();

  firstNodeId = null;
  mode = "select";
  selected = { type: "pipe", id: pipe.id };

  render();
  setStatus(parallelExists
    ? "تم إنشاء أنبوب متوازٍ إضافي بين العقدتين."
    : "تم إنشاء الأنبوب.");
}

function selectNode(id) {
  selected = { type: "node", id: Number(id) };
  render();
}

function selectPipe(id) {
  selected = { type: "pipe", id: Number(id) };
  render();
}

function screenToSvg(event) {
  const rect = svg.getBoundingClientRect();

  if (!rect.width || !rect.height) {
    return { x: 100, y: 100 };
  }

  return {
    x: (event.clientX - rect.left) * 800 / rect.width,
    y: (event.clientY - rect.top) * 500 / rect.height
  };
}

function suggestCommercialDiameter(pipeId) {
  const pipe = pipeById(pipeId);
  if (!pipe) return;

  let flow = null;

  if (hydraulicResults &&
      hydraulicResults.pipeData.has(pipe.id)) {
    flow = Math.abs(hydraulicResults.pipeData.get(pipe.id).q);
  } else if (Number.isFinite(Number(pipe.q0)) &&
             Number(pipe.q0) !== 0) {
    flow = Math.abs(Number(pipe.q0)) / 1000;
  }

  if (flow === null) {
    setStatus("أدخل تصريفاً ابتدائياً أو نفّذ تحليلاً أولياً قبل اقتراح القطر.");
    return;
  }

  if (flow < 1e-8) {
    setStatus("لا يمكن اقتراح قطر من تصريف يساوي صفراً.");
    return;
  }

  // سرعة 1 م/ث افتراض مبدئي للاقتراح، وليست معيار تصميم إلزامياً.
  const targetVelocity = 1.0;
  const theoreticalD = Math.sqrt(
    4 * (flow / targetVelocity) / Math.PI
  );

  const commercialKeys = Object.keys(STANDARD_DIAMETERS)
    .map(Number)
    .sort((a, b) => a - b);

  let selectedMm = commercialKeys[commercialKeys.length - 1];

  for (const mm of commercialKeys) {
    if (STANDARD_DIAMETERS[mm] >= theoreticalD) {
      selectedMm = mm;
      break;
    }
  }

  saveHistory();

  pipe.diameterMode = "commercial";
  pipe.D_mm = selectedMm;
  pipe.D_inner_mm = STANDARD_DIAMETERS[selectedMm] * 1000;
  pipe.D = STANDARD_DIAMETERS[selectedMm];

  invalidateHydraulics();
  saveNetwork();
  render();

  setStatus(
    "القطر المقترح " + selectedMm +
    " مم بناءً على سرعة افتراضية 1 م/ث. راجع معايير التصميم."
  );
}

/* ==========================================================
   الرسم والتحديث العام
   ========================================================== */

function render() {
  renderPipes();
  renderNodes();
  renderSummary();
  renderDetails();
  renderAnalysisReport();
  updateToolbar();
}

function getParallelPipeOffset(pipe) {
  const siblings = pipes
    .filter(item =>
      (item.a === pipe.a && item.b === pipe.b) ||
      (item.a === pipe.b && item.b === pipe.a)
    )
    .sort((a, b) => a.id - b.id);

  if (siblings.length <= 1) return 0;

  const index = siblings.findIndex(item => item.id === pipe.id);
  const spacing = 13;
  return (index - (siblings.length - 1) / 2) * spacing;
}

function renderPipes() {
  if (!pipesLayer) return;

  pipesLayer.replaceChildren();

  pipes.forEach(pipe => {
    const a = nodeById(pipe.a);
    const b = nodeById(pipe.b);

    if (!a || !b) return;

    const hasResult = hydraulicResults &&
      hydraulicResults.pipeData.has(pipe.id);

    const result = hasResult
      ? hydraulicResults.pipeData.get(pipe.id)
      : null;

    let start = a;
    let end = b;

    if (result && result.q < 0) {
      start = b;
      end = a;
    }

    const canonicalA = pipe.a < pipe.b ? a : b;
    const canonicalB = pipe.a < pipe.b ? b : a;
    const dx = canonicalB.x - canonicalA.x;
    const dy = canonicalB.y - canonicalA.y;
    const length = Math.hypot(dx, dy) || 1;
    const offset = getParallelPipeOffset(pipe);
    const offsetX = (-dy / length) * offset;
    const offsetY = (dx / length) * offset;
    start = { x: start.x + offsetX, y: start.y + offsetY };
    end = { x: end.x + offsetX, y: end.y + offsetY };

    const isSelected =
      selected?.type === "pipe" &&
      Number(selected.id) === pipe.id;

    const line = svgElement("line", {
      x1: start.x,
      y1: start.y,
      x2: end.x,
      y2: end.y,
      stroke: isSelected
        ? "#f2b84b"
        : (pipe.isPump ? "#8e44ad" : "#738797"),
      "stroke-width": isSelected ? 8 : 5,
      "stroke-linecap": "round",
      "stroke-dasharray": isPipeClosed(pipe) ? "7 6" : "none",
      opacity: isPipeClosed(pipe) ? 0.55 : 1,
      class: "pipe",
      "data-pipe-id": pipe.id
    });

    if (result && Math.abs(result.q) > 1e-12) {
      line.setAttribute("marker-end", "url(#flowArrow)");
    }

    pipesLayer.appendChild(line);

    const midX = (a.x + b.x) / 2 + offsetX;
    const midY = (a.y + b.y) / 2 + offsetY;

    if (pipe.isPump) {
      pipesLayer.appendChild(svgElement("circle", {
        cx: midX,
        cy: midY,
        r: 9,
        fill: "#8e44ad",
        stroke: "white",
        "stroke-width": 2,
        "pointer-events": "none"
      }));

      const pumpText = svgElement("text", {
        x: midX,
        y: midY + 4,
        fill: "white",
        "font-size": "11px",
        "font-weight": "bold",
        "text-anchor": "middle",
        "pointer-events": "none"
      });

      pumpText.textContent = "P";
      pipesLayer.appendChild(pumpText);
    }

    const label = svgElement("text", {
      x: midX,
      y: midY - 15,
      class: "pipe-label"
    });

    label.textContent = "P" + pipe.id + (isPipeClosed(pipe) ? " (مغلق)" : "");
    pipesLayer.appendChild(label);

    const flowLabel = svgElement("text", {
      x: midX,
      y: midY + 22,
      class: "pipe-label"
    });

    if (result && result.isClosed) {
      flowLabel.textContent = "صمام مغلق";
    } else if (result) {
      flowLabel.textContent =
        "Q=" + fmt(Math.abs(result.q * 1000), 3) + " L/s";
    } else {
      flowLabel.textContent = Number(pipe.q0) !== 0
        ? "Q₀=" + fmt(Math.abs(pipe.q0), 3) + " L/s"
        : "لم يُحسب";
    }

    pipesLayer.appendChild(flowLabel);
  });
}

function renderNodes() {
  if (!nodesLayer) return;

  nodesLayer.replaceChildren();

  nodes.forEach(node => {
    const isSelected =
      selected?.type === "node" &&
      Number(selected.id) === node.id;

    const group = svgElement("g", {
      class: "node " + node.type +
        (isSelected ? " selected" : ""),
      "data-node-id": node.id,
      transform: "translate(" + node.x + " " + node.y + ")"
    });

    group.appendChild(svgElement("circle", {
      r: node.type === "source" ? 17 : 14,
      class: "node-shape"
    }));

    const label = svgElement("text", {
      y: 34,
      class: "node-label"
    });

    label.textContent = node.name;

    const subtitle = svgElement("text", {
      y: 48,
      class: "node-subtitle"
    });

    if (hydraulicResults &&
        hydraulicResults.nodeHeads.has(node.id)) {
      const head = hydraulicResults.nodeHeads.get(node.id);
      const relative =
        hydraulicResults.relativeHeadNodeIds.has(node.id);

      if (relative) {
        subtitle.textContent =
          "حمل نسبي: " + fmt(head, 2) + " م";
      } else if (node.type === "source") {
        subtitle.textContent =
          "الحمل: " + fmt(head, 2) + " م";
      } else {
        const pressure = head - Number(node.elevation || 0);
        subtitle.textContent =
          "H=" + fmt(head, 2) +
          " م • ضغط=" + fmt(pressure, 2) + " م";
      }
    } else if (node.type === "demand") {
      subtitle.textContent =
        fmt(node.demand, 3) + " لتر/ث";
    } else if (node.type === "source") {
      subtitle.textContent = node.sourceMode === "flow"
        ? "التصريف: " + fmt(node.sourceFlow, 3) + " لتر/ث"
        : "الحمل: " + fmt(node.head, 2) + " م";
    } else {
      subtitle.textContent =
        "منسوب: " + fmt(node.elevation, 2) + " م";
    }

    group.append(label, subtitle);
    nodesLayer.appendChild(group);
  });
}

function renderSummary() {
  const nodeCount = document.getElementById("nodeCount");
  const pipeCount = document.getElementById("pipeCount");
  const totalDemand = document.getElementById("totalDemand");

  if (nodeCount) nodeCount.textContent = nodes.length;
  if (pipeCount) pipeCount.textContent = pipes.length;

  if (totalDemand) {
    totalDemand.textContent = fmt(
      nodes.reduce((sum, node) =>
        sum + (node.type === "demand" ? node.demand : 0), 0),
      3
    );
  }
}

function updateToolbar() {
  if (buttons.connect) {
    buttons.connect.classList.toggle("active", mode === "connect");
  }

  if (modeBadge) {
    modeBadge.textContent = mode === "connect"
      ? "وضع توصيل الأنابيب"
      : "وضع التحديد";
  }
}
/* ==========================================================
   تفاصيل العقد والأنابيب
   ========================================================== */

function renderDetails() {
  if (!detailsContent) return;

  if (!selected) {
    detailsContent.innerHTML =
      '<p class="muted">اختر عقدة أو أنبوباً لعرض بياناته.</p>';
    return;
  }

  if (selected.type === "node") {
    const node = nodeById(selected.id);

    if (!node) {
      selected = null;
      renderDetails();
      return;
    }

    let extraFields = "";

    if (node.type === "source") {
      extraFields = `
        <div class="field full">
          <label>شرط المصدر</label>
          <select id="edit_sourceMode" name="sourceMode">
            <option value="head" ${node.sourceMode === "head" ? "selected" : ""}>
              حمل معلوم
            </option>
            <option value="flow" ${node.sourceMode === "flow" ? "selected" : ""}>
              تصريف معلوم
            </option>
          </select>
        </div>

        <div id="sourceHeadField" class="field full"
             ${node.sourceMode === "head" ? "" : "hidden"}>
          <label>الحمل (م)</label>
          <input name="head" type="number" step="any"
                 value="${escapeHTML(node.head)}">
        </div>

        <div id="sourceFlowField" class="field full"
             ${node.sourceMode === "flow" ? "" : "hidden"}>
          <label>التصريف (لتر/ث)</label>
          <input name="sourceFlow" type="number" min="0" step="any"
                 value="${escapeHTML(node.sourceFlow)}">
        </div>`;
    }

    if (node.type === "demand") {
      extraFields += `
        <div class="field full">
          <label>الطلب (لتر/ث)</label>
          <input name="demand" type="number" min="0" step="any"
                 value="${escapeHTML(node.demand)}">
        </div>`;
    }

    detailsContent.innerHTML = `
      <form id="detailsForm">
        <div class="field-grid">
          <div class="field full">
            <label>اسم العقدة</label>
            <input name="name" value="${escapeHTML(node.name)}" required>
          </div>

          <div class="field full">
            <label>المنسوب (م)</label>
            <input name="elevation" type="number" step="any"
                   value="${escapeHTML(node.elevation)}">
          </div>

          ${extraFields}
        </div>

        <div class="save-row">
          <button class="save-button" type="submit">حفظ التعديلات</button>
        </div>
      </form>`;

    const form = document.getElementById("detailsForm");

    if (node.type === "source") {
      const modeInput = document.getElementById("edit_sourceMode");

      modeInput.addEventListener("change", event => {
        const isHead = event.target.value === "head";
        document.getElementById("sourceHeadField").hidden = !isHead;
        document.getElementById("sourceFlowField").hidden = isHead;
      });
    }

    form.addEventListener("submit", event => {
      event.preventDefault();

      const data = new FormData(form);
      const name = String(data.get("name") || "").trim();
      const elevation = formNumber(data, "elevation", node.elevation);

      if (!name) {
        setStatus("اكتب اسماً للعقدة.");
        return;
      }

      const draft = { ...node };
      draft.name = name;
      draft.elevation = elevation;

      if (draft.type === "source") {
        draft.sourceMode = data.get("sourceMode") === "flow"
          ? "flow"
          : "head";

        draft.head = formNumber(data, "head", node.head);
        draft.sourceFlow = formNumber(
          data,
          "sourceFlow",
          node.sourceFlow
        );

        if (draft.sourceFlow < 0) {
          setStatus("تصريف المصدر لا يمكن أن يكون سالباً.");
          return;
        }
      }

      if (draft.type === "demand") {
        draft.demand = formNumber(data, "demand", node.demand);

        if (draft.demand < 0) {
          setStatus("طلب العقدة لا يمكن أن يكون سالباً.");
          return;
        }
      }

      saveHistory();
      Object.assign(node, draft);

      invalidateHydraulics();
      saveNetwork();
      render();
      setStatus("تم حفظ بيانات العقدة.");
    });

    return;
  }

  if (selected.type !== "pipe") return;

  const pipe = pipeById(selected.id);

  if (!pipe) {
    selected = null;
    renderDetails();
    return;
  }

  let diameterOptions = "";

  Object.keys(STANDARD_DIAMETERS).forEach(key => {
    const mm = Number(key);
    const diameter = STANDARD_DIAMETERS[key];

    diameterOptions += `
      <option value="${mm}" ${pipe.D_mm === mm ? "selected" : ""}>
        خارجي ${mm} مم — داخلي ${fmt(diameter * 1000, 1)} مم
      </option>`;
  });

  const initialPumpCurvePoints = pipe.pumpMode === "catalog"
    ? pipe.pumpCurvePoints
    : defaultPumpCurvePoints(pipe.H0, pipe.Qmax);

  detailsContent.innerHTML = `
    <form id="detailsForm">
      <div class="field-grid">

        <div class="field full">
          <label>معادلة حساب الفقد</label>
          <select id="edit_equation" name="equation">
            <option value="dw" ${pipe.equation === "dw" ? "selected" : ""}>
              Darcy-Weisbach (دارسي)
            </option>
            <option value="hw" ${pipe.equation === "hw" ? "selected" : ""}>
              Hazen-Williams (هازن)
            </option>
          </select>
        </div>

        <div class="field">
          <label>الطول (م)</label>
          <input name="L" type="number" min="0.001" step="any"
                 value="${pipe.L}" required>
        </div>

        <details class="pipe-extra-section" open>
          <summary>إعدادات التدفق ومعايير التصميم</summary>
          <div class="pipe-extra-content">
            <div class="field full">
              <label for="edit_flowMode">طريقة تحديد التدفق</label>
              <select id="edit_flowMode" name="flowMode">
                <option value="auto" ${pipe.flowMode !== "manualInitial" ? "selected" : ""}>تلقائي — يحدد المحلل التصريف من الشبكة</option>
                <option value="manualInitial" ${pipe.flowMode === "manualInitial" ? "selected" : ""}>إدخال تصريف ابتدائي يدوي للمحلل</option>
              </select>
              <small class="field-help">التصريف اليدوي قيمة ابتدائية للحل وليست تصريفاً نهائياً مفروضاً؛ يحافظ المحلل على استمرارية العقد واتزان الطاقة.</small>
            </div>
            <div id="initialFlowGroup" class="field full"
                 style="display:${pipe.flowMode === "manualInitial" ? "flex" : "none"};">
              <label>التصريف الابتدائي Q₀ (لتر/ثانية) — موجب من A إلى B وسالب بالعكس</label>
              <input name="q0" type="number" step="any" value="${fmt(pipe.q0, 4)}">
            </div>
            <div class="field full">
              <label>التصريف المستهدف للمقارنة فقط (لتر/ثانية)</label>
              <input name="qTarget" type="number" min="0" step="any" value="${fmt(pipe.qTarget, 3)}">
              <small class="field-help">لا يفرض هذا التصريف على الشبكة؛ يستخدم للمقارنة والتنبيه التصميمي لاحقاً.</small>
            </div>
            <div class="field-grid">
              <div class="field">
                <label>السرعة الدنيا (م/ث)</label>
                <input name="velocityMin" type="number" min="0" step="any" value="${fmt(pipe.velocityMin, 2)}">
              </div>
              <div class="field">
                <label>السرعة المستهدفة (م/ث)</label>
                <input name="velocityTarget" type="number" min="0" step="any" value="${fmt(pipe.velocityTarget, 2)}">
              </div>
              <div class="field full">
                <label>السرعة القصوى (م/ث)</label>
                <input name="velocityMax" type="number" min="0" step="any" value="${fmt(pipe.velocityMax, 2)}">
              </div>
            </div>
          </div>
        </details>

        <div class="field full">
          <label for="edit_diameterMode">طريقة تحديد القطر</label>
          <select id="edit_diameterMode" name="diameterMode">
            <option value="commercial" ${pipe.diameterMode !== "manual" ? "selected" : ""}>
              اختيار قطر تجاري من القائمة
            </option>
            <option value="manual" ${pipe.diameterMode === "manual" ? "selected" : ""}>
              إدخال القطر الداخلي يدويًا
            </option>
          </select>
        </div>

        <div id="commercialDiameterGroup" class="field full"
             style="display:${pipe.diameterMode === "manual" ? "none" : "flex"};">
          <label for="edit_D_mm">القطر التجاري الخارجي / الاسمي (مم)</label>
          <select id="edit_D_mm" name="D_mm">${diameterOptions}</select>
          <small class="field-help">
            القطر الداخلي المقابل: <strong id="commercialInnerPreview">${fmt(pipe.D, 4)} م (${fmt(pipe.D_inner_mm, 1)} مم)</strong>
          </small>
        </div>

        <div id="manualDiameterGroup" class="field full"
             style="display:${pipe.diameterMode === "manual" ? "flex" : "none"};">
          <label for="edit_D_inner_mm">القطر الداخلي الفعلي المستخدم في التحليل (مم)</label>
          <input id="edit_D_inner_mm" name="D_inner_mm" type="number"
                 min="0.1" step="0.1" value="${fmt(pipe.D_inner_mm, 3)}">
          <small class="field-help">
            هذا القطر هو الذي يدخل في حساب المساحة والسرعة وفقد الحمل ورقم Reynolds.
          </small>
        </div>

        <button type="button" id="suggestDiameterBtn"
                class="save-button secondary-button"
                style="margin-top:5px;font-size:12px;width:100%;">
          اقتراح قطر تجاري
        </button>

        <details class="pipe-extra-section" open>
          <summary>الفواقد الثانوية للأنبوب (تدخل في التحليل الهيدروليكي)</summary>
          <div class="pipe-extra-content">

          <div class="minor-loss-manager">
            <div class="minor-loss-toolbar">
              <select id="minorLossPreset" aria-label="اختيار فاقد ثانوي جاهز">
                ${MINOR_LOSS_PRESETS.map(item =>
                  `<option value="${item.id}">${item.name}</option>`
                ).join("")}
              </select>
              <button type="button" id="addMinorLossPreset" class="secondary-button">إضافة عنصر جاهز</button>
              <button type="button" id="addCustomMinorLoss" class="secondary-button">إضافة فاقد يدوي</button>
            </div>
            <div id="minorLossRows">
              ${renderMinorLossRows(pipe.minorLosses || [])}
            </div>
            <div class="minor-loss-total">
              مجموع معاملات K للأنبوب: <strong id="minorLossTotalK">${fmt(getPipeMinorK(pipe), 4)}</strong>
            </div>
            <small class="field-help">
              كل صف يمثل نوع فاقد مستقلًا؛ يمكنك تكرار النوع أو الجمع بين الأكواع والتيات والمحابس وأي فاقد آخر. أدخل الاسم وقيمة K والعدد، وسيجمع المحلل مساهمتها لهذا الأنبوب في كل تكرار للحل.
            </small>
          </div>
        </div>
        </details>

        <div id="dwFields" class="field full"
             style="display:${pipe.equation === "dw" ? "flex" : "none"};
                    gap:10px;flex-direction:row;margin-top:10px;">

          <div style="flex:1;">
            <label>الخشونة المطلقة ε (م)</label>
            <input name="eps" type="number" min="0" step="any"
                   value="${pipe.eps}">
          </div>

        </div>

        <div id="hwFields" class="field full"
             style="display:${pipe.equation === "hw" ? "flex" : "none"};
                    margin-top:10px;">

          <label>معامل Hazen-Williams C</label>
          <input name="C" type="number" min="1" step="any"
                 value="${pipe.C}">
        </div>

        <div class="field full">
          <label>أقصى ضغط يتحمله الأنبوب (بار)</label>
          <input name="pMaxBar" type="number" min="0.01" step="any"
                 value="${pipe.pMaxBar}">
        </div>

        <div class="field full"
             style="display:flex;align-items:center;gap:10px;
                    margin-top:10px;padding:10px;background:#e5f2f6;
                    border-radius:8px;">

          <input type="checkbox" id="edit_isPump" name="isPump"
                 style="width:22px;height:22px;margin:0;"
                 ${pipe.isPump ? "checked" : ""}>

          <label for="edit_isPump" style="margin:0;font-weight:bold;">
            إضافة مضخة تقوية مرتبطة بهذا الأنبوب
          </label>
        </div>

        <div id="pumpFields" class="field full pump-fields"
             style="display:${pipe.isPump ? "flex" : "none"};">
          <div class="field full">
            <label>مصدر منحنى أداء المضخة</label>
            <select id="edit_pumpMode" name="pumpMode">
              <option value="default" ${pipe.pumpMode !== "catalog" ? "selected" : ""}>منحنى افتراضي تقريبي</option>
              <option value="catalog" ${pipe.pumpMode === "catalog" ? "selected" : ""}>منحنى كتالوج الشركة المصنعة</option>
            </select>
            <small class="field-help">
              المنحنى H–Q يدخل في معادلة الطاقة أثناء تكرارات المحلل، وليس مجرد رسم للعرض.
            </small>
          </div>

          <div id="pumpDefaultFields" class="field full"
               style="display:${pipe.pumpMode === "catalog" ? "none" : "flex"};">
            <div class="pump-two-columns">
              <div class="field">
                <label>ارتفاع الإغلاق H0 (م)</label>
                <input id="edit_pumpH0" name="H0" type="number" min="0" step="any" value="${pipe.H0}">
              </div>
              <div class="field">
                <label>تصريف انعدام الرفع Qmax (لتر/ث)</label>
                <input id="edit_pumpQmax" name="Qmax" type="number" min="0.001" step="any" value="${pipe.Qmax}">
              </div>
            </div>
            <small class="field-help">
              النموذج الافتراضي: H = H0 × [1 − (Q/Qmax)²]، ويُستخدم فقط من Q=0 حتى Q=Qmax. لا يمثل منحنى مصنع.
            </small>
            <div id="pumpDefaultPreview" class="pump-curve-preview">
              ${renderPumpCurvePreview(initialPumpCurvePoints)}
            </div>
          </div>

          <div id="pumpCatalogFields" class="field full"
               style="display:${pipe.pumpMode === "catalog" ? "flex" : "none"};">
            <div class="pump-two-columns">
              <div class="field">
                <label>الشركة المصنعة</label>
                <input name="pumpCompany" type="text" maxlength="100" value="${escapeHTML(pipe.pumpCompany)}" placeholder="اسم الشركة">
              </div>
              <div class="field">
                <label>الموديل</label>
                <input name="pumpModel" type="text" maxlength="100" value="${escapeHTML(pipe.pumpModel)}" placeholder="رقم الموديل">
              </div>
            </div>
            <div class="field">
              <label>سرعة الدوران RPM</label>
              <input name="pumpRpm" type="number" min="1" step="1" value="${pipe.pumpRpm || 1450}">
            </div>
            <div class="pump-curve-import">
              <label for="pumpCurveFile">استيراد نقاط المنحنى من CSV</label>
              <input id="pumpCurveFile" type="file" accept=".csv,text/csv">
              <small class="field-help">يحتوي الملف على عمودين بالترتيب Q (لتر/ث) ثم H (م)، ويمكن أن يحتوي على صف عناوين.</small>
            </div>
            <div class="pump-curve-toolbar">
              <strong>نقاط منحنى H–Q</strong>
              <button type="button" id="addPumpCurvePoint" class="secondary-button">إضافة نقطة</button>
            </div>
            <div id="pumpCurveRows">${renderPumpCurveRows(pipe.pumpCurvePoints)}</div>
            <div id="pumpCatalogPreview" class="pump-curve-preview">
              ${renderPumpCurvePreview(pipe.pumpCurvePoints)}
            </div>
            <small class="field-help">
              يجب أن تكون قيم Q مختلفة وغير سالبة، وقيم H غير سالبة. يستخدم المحلل الاستيفاء الخطي بين النقاط، ويعلن النقطة خارج المجال عند تجاوز أول أو آخر تصريف مدخل دون استقراء.
            </small>
          </div>

          <p class="field-help pump-npsh-note">
            منحنى H–Q وحده لا يثبت سلامة السحب. يلزم لاحقاً إدخال منحنى NPSHr وحساب NPSHa بصورة مستقلة.
          </p>
        </div>

      </div>

      <div class="save-row">
        <button class="save-button" type="submit">حفظ التعديلات</button>
      </div>
    </form>`;

  const form = document.getElementById("detailsForm");

  const flowModeSelect = document.getElementById("edit_flowMode");
  flowModeSelect.addEventListener("change", () => {
    document.getElementById("initialFlowGroup").style.display =
      flowModeSelect.value === "manualInitial" ? "flex" : "none";
  });

  document.getElementById("edit_equation").addEventListener("change", event => {
    const isDW = event.target.value === "dw";
    document.getElementById("dwFields").style.display =
      isDW ? "flex" : "none";
    document.getElementById("hwFields").style.display =
      isDW ? "none" : "flex";
  });

  const diameterModeSelect = document.getElementById("edit_diameterMode");
  const commercialDiameterSelect = document.getElementById("edit_D_mm");

  function updateDiameterEditor() {
    const manual = diameterModeSelect.value === "manual";
    document.getElementById("commercialDiameterGroup").style.display =
      manual ? "none" : "flex";
    document.getElementById("manualDiameterGroup").style.display =
      manual ? "flex" : "none";
  }

  diameterModeSelect.addEventListener("change", updateDiameterEditor);
  commercialDiameterSelect.addEventListener("change", event => {
    const innerM = STANDARD_DIAMETERS[Number(event.target.value)];
    document.getElementById("commercialInnerPreview").textContent =
      fmt(innerM, 4) + " م (" + fmt(innerM * 1000, 1) + " مم)";
  });

  const pumpCheckbox = document.getElementById("edit_isPump");
  const pumpFields = document.getElementById("pumpFields");
  const pumpModeSelect = document.getElementById("edit_pumpMode");
  const pumpCurveRows = document.getElementById("pumpCurveRows");

  pumpCheckbox.addEventListener("change", event => {
    pumpFields.style.display = event.target.checked ? "flex" : "none";
  });

  function currentDefaultPumpPreviewPoints() {
    const h0 = Number(document.getElementById("edit_pumpH0")?.value);
    const qmax = Number(document.getElementById("edit_pumpQmax")?.value);
    if (!Number.isFinite(h0) || !Number.isFinite(qmax) || h0 < 0 || qmax <= 0) return [];
    return defaultPumpCurvePoints(h0, qmax);
  }

  function refreshPumpCurvePreview() {
    if (pumpModeSelect.value === "catalog") {
      try {
        document.getElementById("pumpCatalogPreview").innerHTML =
          renderPumpCurvePreview(readPumpCurveEditorPoints(pumpCurveRows));
      } catch (_) {
        document.getElementById("pumpCatalogPreview").innerHTML =
          '<p class="muted">أكمل نقاط Q وH لعرض المنحنى.</p>';
      }
    } else {
      document.getElementById("pumpDefaultPreview").innerHTML =
        renderPumpCurvePreview(currentDefaultPumpPreviewPoints());
    }
  }

  function redrawPumpCurveRows(points) {
    pumpCurveRows.innerHTML = renderPumpCurveRows(points);
    refreshPumpCurvePreview();
  }

  function updatePumpEditorMode() {
    const isCatalog = pumpModeSelect.value === "catalog";
    document.getElementById("pumpDefaultFields").style.display = isCatalog ? "none" : "flex";
    document.getElementById("pumpCatalogFields").style.display = isCatalog ? "flex" : "none";
    refreshPumpCurvePreview();
  }

  pumpModeSelect.addEventListener("change", updatePumpEditorMode);
  document.getElementById("edit_pumpH0").addEventListener("input", refreshPumpCurvePreview);
  document.getElementById("edit_pumpQmax").addEventListener("input", refreshPumpCurvePreview);

  function pumpCurveEditorRowsRaw() {
    return Array.from(pumpCurveRows.querySelectorAll("[data-pump-point-row]"))
      .map(row => ({
        q: row.querySelector("[data-pump-q]")?.value ?? "",
        h: row.querySelector("[data-pump-h]")?.value ?? ""
      }));
  }

  document.getElementById("addPumpCurvePoint").addEventListener("click", () => {
    const points = pumpCurveEditorRowsRaw();
    const last = points.length ? points[points.length - 1] : null;
    const lastQ = Number(last?.q);
    const lastH = Number(last?.h);
    const next = last && Number.isFinite(lastQ) && Number.isFinite(lastH)
      ? { q: Number((lastQ + Math.max(1, lastQ * 0.1)).toFixed(4)), h: Math.max(0, Number((lastH * 0.9).toFixed(4))) }
      : { q: 0, h: 0 };
    points.push(next);
    redrawPumpCurveRows(points);
  });

  pumpCurveRows.addEventListener("click", event => {
    const button = event.target.closest("[data-remove-pump-point]");
    if (!button) return;
    const points = pumpCurveEditorRowsRaw();
    const index = Number(button.dataset.removePumpPoint);
    if (Number.isInteger(index) && index >= 0 && index < points.length) {
      points.splice(index, 1);
      redrawPumpCurveRows(points);
    }
  });

  pumpCurveRows.addEventListener("input", refreshPumpCurvePreview);
  pumpCurveRows.addEventListener("change", refreshPumpCurvePreview);

  document.getElementById("pumpCurveFile").addEventListener("change", event => {
    const file = event.target.files?.[0];
    if (!file) return;
    const reader = new FileReader();
    reader.onload = () => {
      try {
        const points = parsePumpCurveCSV(reader.result);
        redrawPumpCurveRows(points);
        setStatus("تم استيراد " + points.length + " نقطة من منحنى المضخة. احفظ بيانات الأنبوب لاعتمادها.");
      } catch (error) {
        setStatus("تعذر استيراد منحنى المضخة: " + error.message);
        event.target.value = "";
      }
    };
    reader.onerror = () => setStatus("تعذر قراءة ملف CSV.");
    reader.readAsText(file);
  });

  const minorLossRows = document.getElementById("minorLossRows");
  const minorLossPreset = document.getElementById("minorLossPreset");

  function refreshMinorLossPreview() {
    try {
      const items = minorLossesFromEditor(minorLossRows);
      const total = minorLossesTotalK(items);
      document.getElementById("minorLossTotalK").textContent =
        Number.isFinite(total) ? fmt(total, 4) : "غير صالح";

      minorLossRows.querySelectorAll('[data-minor-row][data-kind="valve"]').forEach(row => {
        const item = minorLossesFromEditor({
          querySelectorAll: () => [row]
        })[0];
        const kInput = row.querySelector("[data-minor-k]");
        try {
          if (item.valveOpen === 0) {
            kInput.value = "";
            kInput.placeholder = "مغلق";
          } else {
            kInput.placeholder = "";
            kInput.value = fmt(minorLossItemK(item), 4);
          }
        } catch (_) {
          kInput.value = "راجع نسبة الفتح";
        }
      });
    } catch (_) {
      document.getElementById("minorLossTotalK").textContent = "--";
    }
  }

  function readMinorLossEditorItems() {
    return minorLossesFromEditor(minorLossRows);
  }

  function redrawMinorLossRows(items) {
    minorLossRows.innerHTML = renderMinorLossRows(items);
    refreshMinorLossPreview();
  }

  document.getElementById("addMinorLossPreset").addEventListener("click", () => {
    const preset = MINOR_LOSS_PRESETS.find(item => item.id === minorLossPreset.value);
    if (!preset) return;
    const items = readMinorLossEditorItems();
    if (preset.kind === "valve") {
      items.push({
        kind: "valve", name: preset.name, count: 1,
        valveType: preset.valveType, valveOpen: preset.valveOpen
      });
    } else {
      items.push({ kind: "fixed", name: preset.name, k: preset.k, count: 1 });
    }
    redrawMinorLossRows(items);
  });

  document.getElementById("addCustomMinorLoss").addEventListener("click", () => {
    const items = readMinorLossEditorItems();
    items.push({ kind: "fixed", name: "فاقد مخصص", k: 0, count: 1 });
    redrawMinorLossRows(items);
    const lastName = minorLossRows.querySelector('[data-minor-row]:last-child [data-minor-name]');
    if (lastName) lastName.focus();
  });

  minorLossRows.addEventListener("click", event => {
    const removeButton = event.target.closest("[data-remove-minor]");
    if (!removeButton) return;
    const items = readMinorLossEditorItems();
    const index = Number(removeButton.dataset.removeMinor);
    if (Number.isInteger(index) && index >= 0 && index < items.length) {
      items.splice(index, 1);
      redrawMinorLossRows(items);
    }
  });

  minorLossRows.addEventListener("input", refreshMinorLossPreview);
  minorLossRows.addEventListener("change", refreshMinorLossPreview);

  document.getElementById("suggestDiameterBtn").addEventListener("click", () => {
    suggestCommercialDiameter(pipe.id);
  });

  form.addEventListener("submit", event => {
    event.preventDefault();

    const data = new FormData(form);
    const draft = { ...pipe };

    draft.diameterMode = data.get("diameterMode") === "manual"
      ? "manual"
      : "commercial";

    if (draft.diameterMode === "commercial") {
      const diameterMm = Number(data.get("D_mm"));
      if (!STANDARD_DIAMETERS[diameterMm]) {
        setStatus("اختر قطراً تجارياً صحيحاً.");
        return;
      }
      draft.D_mm = diameterMm;
      draft.D_inner_mm = STANDARD_DIAMETERS[diameterMm] * 1000;
    } else {
      const innerMm = formNumber(data, "D_inner_mm", NaN);
      if (!Number.isFinite(innerMm) || innerMm <= 0) {
        setStatus("أدخل قطرًا داخليًا يدويًا أكبر من الصفر بالمليمتر.");
        return;
      }
      draft.D_inner_mm = innerMm;
    }

    draft.D = draft.D_inner_mm / 1000;

    draft.equation = data.get("equation") === "hw" ? "hw" : "dw";
    draft.L = formNumber(data, "L", pipe.L);
    draft.pMaxBar = formNumber(data, "pMaxBar", pipe.pMaxBar);
    draft.flowMode = data.get("flowMode") === "manualInitial" ? "manualInitial" : "auto";
    draft.q0 = draft.flowMode === "manualInitial"
      ? formNumber(data, "q0", pipe.q0) : 0;
    draft.qTarget = formNumber(data, "qTarget", pipe.qTarget);
    draft.velocityMin = formNumber(data, "velocityMin", pipe.velocityMin);
    draft.velocityTarget = formNumber(data, "velocityTarget", pipe.velocityTarget);
    draft.velocityMax = formNumber(data, "velocityMax", pipe.velocityMax);

    if (draft.qTarget < 0 || draft.velocityMin < 0 ||
        draft.velocityTarget < 0 || draft.velocityMax < 0 ||
        !(draft.velocityMin < draft.velocityTarget &&
          draft.velocityTarget < draft.velocityMax)) {
      setStatus("تحقق من التصريف المستهدف وترتيب السرعات: الدنيا < المستهدفة < القصوى.");
      return;
    }
    if (!Number.isFinite(draft.q0)) {
      setStatus("أدخل تصريفاً ابتدائياً رقمياً صحيحاً.");
      return;
    }

    if (!(draft.L > 0) || !(draft.pMaxBar > 0)) {
      setStatus("تحقق من الطول وحد الضغط.");
      return;
    }

    if (draft.equation === "dw") {
      draft.eps = formNumber(data, "eps", pipe.eps);
    } else {
      draft.C = formNumber(data, "C", pipe.C);
    }

    if (!(draft.D > 0) || draft.eps < 0 || draft.C <= 0) {
      setStatus("تحقق من القطر الداخلي والخشونة ومعامل Hazen-Williams.");
      return;
    }

    draft.isPump = data.get("isPump") === "on";
    draft.pumpType = "booster";
    draft.pumpMode = data.get("pumpMode") === "catalog" ? "catalog" : "default";
    draft.H0 = formNumber(data, "H0", pipe.H0);
    draft.Qmax = formNumber(data, "Qmax", pipe.Qmax);
    draft.pumpCompany = String(data.get("pumpCompany") || "").trim();
    draft.pumpModel = String(data.get("pumpModel") || "").trim();
    draft.pumpRpm = formNumber(data, "pumpRpm", pipe.pumpRpm || 1450);

    if (draft.isPump && draft.pumpMode === "catalog") {
      try {
        draft.pumpCurvePoints = validatePumpCurvePoints(
          readPumpCurveEditorPoints(pumpCurveRows), pipe.id
        );
      } catch (error) {
        setStatus(error.message);
        return;
      }
      if (!(draft.pumpRpm > 0)) {
        setStatus("أدخل سرعة دوران صحيحة للمضخة في P" + pipe.id + ".");
        return;
      }
      // قيم توافقية فقط للملفات القديمة؛ المحلل يستخدم نقاط الكتالوج.
      draft.H0 = draft.pumpCurvePoints[0].h;
      draft.Qmax = draft.pumpCurvePoints[draft.pumpCurvePoints.length - 1].q;
    } else if (draft.isPump &&
        (!(draft.H0 >= 0) || !(draft.Qmax > 0))) {
      setStatus("تحقق من H0 وQmax في المنحنى الافتراضي.");
      return;
    }

    draft.minorLosses = readMinorLossEditorItems();
    draft.kMinor = 0;
    draft.n_elbow = 0;
    draft.n_tee = 0;
    draft.n_valve = 0;
    draft.n_coupler = 0;

    for (const item of draft.minorLosses) {
      if (!item.name) {
        setStatus("اكتب اسم كل عنصر من عناصر الفواقد الثانوية.");
        return;
      }
      if (!Number.isInteger(item.count) || item.count < 0) {
        setStatus("عدد كل عنصر يجب أن يكون عدداً صحيحاً غير سالب.");
        return;
      }
      if (item.kind === "valve") {
        if (!Number.isFinite(item.valveOpen) || item.valveOpen < 0 || item.valveOpen > 100) {
          setStatus("نسبة فتح المحبس يجب أن تكون بين 0 و100%.");
          return;
        }
        try {
          if (item.valveOpen > 0) getValveK(item.valveType, item.valveOpen);
        } catch (error) {
          setStatus(error.message);
          return;
        }
      } else if (!Number.isFinite(item.k) || item.k < 0) {
        setStatus("أدخل قيمة K صحيحة وغير سالبة لكل فاقد.");
        return;
      }
    }

    saveHistory();
    Object.assign(pipe, draft);

    invalidateHydraulics();
    saveNetwork();
    render();
    setStatus("تم حفظ بيانات الأنبوب.");
  });
}

/* ==========================================================
   النموذج الهيدروليكي: المساحة والاحتكاك والفواقد
   ========================================================== */

function pipeArea(pipe) {
  return Math.PI * Math.pow(pipe.D, 2) / 4;
}

function classifyFlow(reynolds) {
  if (!Number.isFinite(reynolds) || reynolds < 0) {
    return "غير محدد";
  }

  if (reynolds <= 1e-12) {
    return "لا يوجد جريان";
  }

  if (reynolds < 2300) {
    return "صفحي (Laminar)";
  }

  if (reynolds < 4000) {
    return "انتقالي (Transitional)";
  }

  return "مضطرب (Turbulent)";
}

/*
  معامل Darcy:
  صفحي: 64/Re
  مضطرب: Swamee-Jain
  انتقالي: مزج رياضي سلس بين الحدين 2300 و4000.
  منطقة الانتقال تقريبية وليست حداً فيزيائياً حاداً.
*/

function frictionFactor(pipe, qAbs, nu) {
  if (qAbs <= 1e-14) return 0;

  const velocity = qAbs / pipeArea(pipe);
  const reynolds = velocity * pipe.D / nu;

  if (!(reynolds > 0)) return 0;

  const laminar = 64 / reynolds;

  const relativeRoughness = pipe.eps / (3.7 * pipe.D);
  const turbulent = 0.25 / Math.pow(
    Math.log10(
      relativeRoughness + 5.74 / Math.pow(reynolds, 0.9)
    ),
    2
  );

  if (reynolds < 2300) return laminar;
  if (reynolds >= 4000) return turbulent;

  const t = (reynolds - 2300) / (4000 - 2300);
  const blend = t * t * (3 - 2 * t);

  return laminar * (1 - blend) + turbulent * blend;
}

function getPipeLossBreakdown(pipe, qAbs, nu) {
  if (qAbs <= 0) {
    return {
      hf: 0,
      hm: 0,
      totalK: getPipeMinorK(pipe),
      totalLoss: 0,
      velocity: 0,
      reynolds: 0,
      frictionFactor: NaN
    };
  }

  const area = pipeArea(pipe);
  const velocity = qAbs / area;
  const reynolds = velocity * pipe.D / nu;

  const totalK = getPipeMinorK(pipe);
  const hm = totalK * velocity * velocity / (2 * GRAVITY);

  let hf;
  let factor = NaN;

  if (pipe.equation === "hw") {
    hf = 10.67 * pipe.L * Math.pow(qAbs, 1.852) /
      (
        Math.pow(pipe.C, 1.852) *
        Math.pow(pipe.D, 4.87)
      );
  } else {
    factor = frictionFactor(pipe, qAbs, nu);
    hf = factor * (pipe.L / pipe.D) *
      velocity * velocity / (2 * GRAVITY);
  }

  return {
    hf,
    hm,
    totalK,
    totalLoss: hf + hm,
    velocity,
    reynolds,
    frictionFactor: factor
  };
}

/*
  signedHeadLoss يمثل:
  H(a) - H(b)

  عندما يكون q موجباً:
    الجريان من a إلى b.

  وعندما يكون q سالباً:
    الجريان من b إلى a.

  المضخة تضيف ارتفاعاً فقط عند الجريان في اتجاهها
  المعتمد من a إلى b. عند عكس الاتجاه لا نضيف رفع مضخة.
*/

function getPumpCurveEvaluation(pipe, q) {
  if (!pipe.isPump) {
    return { head: 0, derivative: 0, inRange: true, active: false, mode: "none" };
  }

  // المضخة مركبة باتجاه a -> b. عند الجريان العكسي لا تضيف رفعاً.
  if (q < -1e-12) {
    return { head: 0, derivative: 0, inRange: true, active: false, reverse: true, mode: pipe.pumpMode || "default" };
  }

  const qLps = Math.max(0, q * 1000);

  if (pipe.pumpMode !== "catalog") {
    const qMax = Number(pipe.Qmax);
    const h0 = Number(pipe.H0);
    if (!(qMax > 0) || !(h0 >= 0)) {
      return { head: 0, derivative: 0, inRange: false, active: true, mode: "default", reason: "invalid-default" };
    }

    const inRange = qLps <= qMax + 1e-9;
    const boundedQ = Math.min(qLps, qMax);
    const ratio = boundedQ / qMax;
    const head = h0 * (1 - ratio * ratio);
    const derivative = inRange
      ? (-2 * h0 * boundedQ / (qMax * qMax)) * 1000
      : 0;

    return {
      head: Math.max(0, head),
      derivative,
      inRange,
      active: true,
      mode: "default",
      qMin: 0,
      qMax,
      actualQ: qLps,
      reason: inRange ? "within-range" : "above-range"
    };
  }

  const points = normalizePumpCurvePoints(pipe.pumpCurvePoints);
  if (points.length < 2) {
    return { head: 0, derivative: 0, inRange: false, active: true, mode: "catalog", reason: "missing-curve" };
  }

  const first = points[0];
  const last = points[points.length - 1];
  const qMin = first.q;
  const qMax = last.q;

  if (qLps < qMin - 1e-9) {
    return {
      head: first.h, derivative: 0, inRange: false, active: true,
      mode: "catalog", qMin, qMax, actualQ: qLps, reason: "below-range"
    };
  }

  if (qLps > qMax + 1e-9) {
    return {
      head: last.h, derivative: 0, inRange: false, active: true,
      mode: "catalog", qMin, qMax, actualQ: qLps, reason: "above-range"
    };
  }

  let segmentIndex = points.length - 2;
  for (let i = 0; i < points.length - 1; i++) {
    if (qLps <= points[i + 1].q + 1e-9) {
      segmentIndex = i;
      break;
    }
  }

  const p1 = points[segmentIndex];
  const p2 = points[segmentIndex + 1];
  const span = p2.q - p1.q;
  const fraction = Math.max(0, Math.min(1, (qLps - p1.q) / span));
  const head = p1.h + fraction * (p2.h - p1.h);
  const derivative = ((p2.h - p1.h) / span) * 1000;

  return {
    head: Math.max(0, head),
    derivative,
    inRange: true,
    active: true,
    mode: "catalog",
    qMin,
    qMax,
    actualQ: qLps,
    reason: "within-range"
  };
}

function getPumpHead(pipe, q) {
  return getPumpCurveEvaluation(pipe, q).head;
}

function signedHeadLoss(pipe, q, nu) {
  const qAbs = Math.abs(q);
  const losses = getPipeLossBreakdown(pipe, qAbs, nu);

  const frictionAndMinor =
    Math.sign(q) * losses.totalLoss;

  const pumpHead = getPumpHead(pipe, q);

  return frictionAndMinor - pumpHead;
}

/*
  مشتقة الفقد بالنسبة إلى التصريف الموقّع.
  مقاومة الأنبوب مشتقتها موجبة على جانبي الصفر.
*/

function derivativeHeadLoss(pipe, q, nu) {
  const qAbs = Math.abs(q);
  const area = pipeArea(pipe);

  let baseDerivative;

  if (qAbs < 1e-8) {
    if (pipe.equation === "hw") {
      baseDerivative = 1e-8;
    } else {
      // مشتقة الفقد الصفحي عند التصريف القريب من الصفر.
      baseDerivative =
        (32 * nu * pipe.L) /
        (GRAVITY * pipe.D * pipe.D * area);

      // مساهمة الفقد الموضعي تؤول إلى الصفر عند Q=0.
    }
  } else if (pipe.equation === "hw") {
    const breakdown = getPipeLossBreakdown(pipe, qAbs, nu);

    const frictionDerivative =
      1.852 * breakdown.hf / qAbs;

    const minorDerivative =
      getPipeMinorK(pipe) * qAbs /
      (GRAVITY * area * area);

    baseDerivative = frictionDerivative + minorDerivative;
  } else {
    const step = Math.max(qAbs * 1e-4, 1e-9);
    const q1 = Math.max(0, qAbs - step);
    const q2 = qAbs + step;

    baseDerivative = (
      getPipeLossBreakdown(pipe, q2, nu).totalLoss -
      getPipeLossBreakdown(pipe, q1, nu).totalLoss
    ) / (q2 - q1);
  }

  if (pipe.isPump && q >= 0) {
    const pumpEvaluation = getPumpCurveEvaluation(pipe, q);
    if (pumpEvaluation.inRange && Number.isFinite(pumpEvaluation.derivative)) {
      // d[loss - Hp(Q)]/dQ = d(loss)/dQ - d(Hp)/dQ.
      baseDerivative -= pumpEvaluation.derivative;
    }
  }

  return Math.max(baseDerivative, 1e-10);
}

/* ==========================================================
   بناء مكونات الشبكة
   ========================================================== */

function buildComponents() {
  const adjacency = new Map(
    nodes.map(node => [node.id, []])
  );

  pipes.forEach(pipe => {
    if (!adjacency.has(pipe.a) || !adjacency.has(pipe.b)) {
      throw new Error("أنبوب مرتبط بعقدة غير موجودة.");
    }
    if (isPipeClosed(pipe)) return;

    adjacency.get(pipe.a).push({
      pipe,
      other: pipe.b
    });

    adjacency.get(pipe.b).push({
      pipe,
      other: pipe.a
    });
  });

  for (const node of nodes) {
    if (!adjacency.get(node.id).length) {
      throw new Error("العقدة «" + node.name + "» غير متصلة.");
    }
  }

  const seen = new Set();
  const components = [];

  for (const node of nodes) {
    if (seen.has(node.id)) continue;

    const queue = [node.id];
    const ids = [];
    seen.add(node.id);

    while (queue.length) {
      const current = queue.shift();
      ids.push(current);

      for (const item of adjacency.get(current)) {
        if (!seen.has(item.other)) {
          seen.add(item.other);
          queue.push(item.other);
        }
      }
    }

    components.push({
      ids,
      nodes: ids.map(nodeById)
    });
  }

  return { components, adjacency };
}

/* ==========================================================
   حل نظام خطي بطريقة الحذف الغاوسي مع اختيار المحور
   ========================================================== */

function solveLinearSystem(matrix, rhs) {
  const n = rhs.length;

  if (!n || matrix.length !== n) {
    throw new Error("أبعاد نظام المعادلات غير صحيحة.");
  }

  const A = matrix.map((row, i) =>
    row.slice().concat(rhs[i])
  );

  for (let col = 0; col < n; col++) {
    let pivotRow = col;
    let largest = Math.abs(A[col][col]);

    for (let row = col + 1; row < n; row++) {
      const value = Math.abs(A[row][col]);

      if (value > largest) {
        largest = value;
        pivotRow = row;
      }
    }

    if (!Number.isFinite(largest) || largest < 1e-13) {
      throw new Error(
        "تعذر حل النظام الخطي؛ تحقق من اتصال الشبكة وشروط المصادر."
      );
    }

    if (pivotRow !== col) {
      [A[pivotRow], A[col]] = [A[col], A[pivotRow]];
    }

    const pivot = A[col][col];

    for (let row = col + 1; row < n; row++) {
      const factor = A[row][col] / pivot;

      if (factor === 0) continue;

      A[row][col] = 0;

      for (let j = col + 1; j <= n; j++) {
        A[row][j] -= factor * A[col][j];
      }
    }
  }

  const solution = Array(n).fill(0);

  for (let i = n - 1; i >= 0; i--) {
    let total = A[i][n];

    for (let j = i + 1; j < n; j++) {
      total -= A[i][j] * solution[j];
    }

    solution[i] = total / A[i][i];

    if (!Number.isFinite(solution[i])) {
      throw new Error("ظهرت قيمة غير محدودة أثناء حل المعادلات.");
    }
  }

  return solution;
}

/* ==========================================================
   بناء شجرة الامتداد والحلقات الأساسية لهاردي كروس
   ========================================================== */

function buildLoopsWithSigns(nodesArr, pipesArr, refNodeId) {
  const adjacency = new Map(
    nodesArr.map(node => [node.id, []])
  );

  pipesArr.forEach(pipe => {
    adjacency.get(pipe.a).push({
      pipe,
      other: pipe.b
    });

    adjacency.get(pipe.b).push({
      pipe,
      other: pipe.a
    });
  });

  const visited = new Set([refNodeId]);
  const parentNode = new Map([[refNodeId, null]]);
  const parentPipe = new Map();
  const treePipeIds = new Set();
  const treeChildren = new Map(
    nodesArr.map(node => [node.id, []])
  );

  const queue = [refNodeId];

  while (queue.length) {
    const current = queue.shift();

    for (const item of adjacency.get(current)) {
      if (visited.has(item.other)) continue;

      visited.add(item.other);
      parentNode.set(item.other, current);
      parentPipe.set(item.other, item.pipe);
      treePipeIds.add(item.pipe.id);
      treeChildren.get(current).push(item.other);

      queue.push(item.other);
    }
  }

  if (visited.size !== nodesArr.length) {
    throw new Error("الشبكة غير متصلة.");
  }

  function treePathFinder(from, to) {
    const upFrom = [];
    let current = from;

    while (current !== null) {
      upFrom.push(current);
      current = parentNode.get(current);
    }

    const upTo = [];
    current = to;

    while (current !== null) {
      upTo.push(current);
      current = parentNode.get(current);
    }

    const fromSet = new Set(upFrom);
    let lowestCommonAncestor = null;

    for (const id of upTo) {
      if (fromSet.has(id)) {
        lowestCommonAncestor = id;
        break;
      }
    }

    if (lowestCommonAncestor === null) return null;

    const firstPart = [];
    current = from;

    while (current !== lowestCommonAncestor) {
      firstPart.push(current);
      current = parentNode.get(current);
    }

    firstPart.push(lowestCommonAncestor);

    const secondPart = [];
    current = to;

    while (current !== lowestCommonAncestor) {
      secondPart.push(current);
      current = parentNode.get(current);
    }

    secondPart.reverse();

    return firstPart.concat(secondPart);
  }

  function findTreePipe(a, b) {
    const child = parentNode.get(a) === b ? a :
      parentNode.get(b) === a ? b : null;

    return child === null ? null : parentPipe.get(child);
  }

  const chordPipes = pipesArr.filter(
    pipe => !treePipeIds.has(pipe.id)
  );

  const loops = [];

  for (const chord of chordPipes) {
    const path = treePathFinder(chord.a, chord.b);

    if (!path) {
      throw new Error("تعذر بناء أحد مسارات الحلقات.");
    }

    // اتجاه الحلقة: الوتر من a إلى b، ثم مسار الشجرة من b إلى a.
    const orderedNodes = [chord.a, chord.b];
    const orderedPipes = [chord];
    const orderedSigns = [+1];

    for (let k = path.length - 2; k >= 0; k--) {
      const from = path[k + 1];
      const to = path[k];
      const pipe = findTreePipe(from, to);

      if (!pipe) {
        throw new Error("تعذر تحديد أنبوب في شجرة الامتداد.");
      }

      orderedPipes.push(pipe);

      orderedSigns.push(
        pipe.a === from && pipe.b === to ? +1 : -1
      );

      orderedNodes.push(to);
    }

    // إحداثيات SVG لها محور رأسي متجه إلى الأسفل.
    // لذلك نعكس تفسير إشارة مساحة المضلع لتحديد CW/CCW.
    let area2 = 0;

    for (let i = 0; i < orderedNodes.length - 1; i++) {
      const p1 = nodeById(orderedNodes[i]);
      const p2 = nodeById(orderedNodes[i + 1]);

      area2 += p1.x * p2.y - p2.x * p1.y;
    }

    loops.push({
      nodes: orderedNodes,
      pipes: orderedPipes,
      signs: orderedSigns,
      orientation: area2 > 0 ? "CW" : "CCW",
      chordPipeId: chord.id
    });
  }

  return {
    loops,
    treePipeIds,
    parentNode,
    parentPipe,
    treeChildren
  };
}

/* ==========================================================
   تصريف ابتدائي متزن لهاردي كروس
   ========================================================== */

/*
  نحتفظ بتصريفات الأوتار q0 كقيم ابتدائية.
  ثم نحسب تصريفات أنابيب شجرة الامتداد بحيث يتحقق
  اتزان الكتلة عند العقد غير المثبتة.
*/

function initializeHardyCrossFlows(
  nodesArr,
  pipesArr,
  treePipeIds,
  parentNode,
  parentPipe,
  treeChildren,
  rootId
) {
  const netAtNode = new Map();

  nodesArr.forEach(node => {
    let demand = 0;

    if (node.type === "demand") {
      demand += node.demand / 1000;
    }

    if (node.type === "source" && node.sourceMode === "flow") {
      demand -= node.sourceFlow / 1000;
    }

    netAtNode.set(node.id, demand);
  });

  const Q = new Map(
    pipesArr.map(pipe => [pipe.id, 0])
  );

  // التصريفات الابتدائية للأوتار.
  pipesArr.forEach(pipe => {
    if (treePipeIds.has(pipe.id)) return;

    const q = finiteNumber(pipe.q0, 0) / 1000;
    Q.set(pipe.id, q);

    netAtNode.set(pipe.a, netAtNode.get(pipe.a) + q);
    netAtNode.set(pipe.b, netAtNode.get(pipe.b) - q);
  });

  // ترتيب عكسي للعقد حتى نحسب مجموع كل مجموعة فرعية.
  const order = [];
  const stack = [rootId];

  while (stack.length) {
    const id = stack.pop();
    order.push(id);

    for (const child of treeChildren.get(id) || []) {
      stack.push(child);
    }
  }

  const subtreeNet = new Map();

  for (let i = order.length - 1; i >= 0; i--) {
    const id = order[i];
    let sum = netAtNode.get(id);

    for (const child of treeChildren.get(id) || []) {
      sum += subtreeNet.get(child);
    }

    subtreeNet.set(id, sum);

    const parentId = parentNode.get(id);

    if (parentId !== null && parentId !== undefined) {
      const pipe = parentPipe.get(id);
      const sign = pipe.a === parentId && pipe.b === id ? +1 : -1;

      Q.set(pipe.id, sum / sign);
    }
  }

  return Q;
}

/* ==========================================================
   حساب مؤشرات الحلقات والاتزان
   ========================================================== */

function getLoopResidual(loop, Q, nu) {
  let residual = 0;
  let derivativeSum = 0;

  for (let i = 0; i < loop.pipes.length; i++) {
    const pipe = loop.pipes[i];
    const flow = Q.get(pipe.id) || 0;
    const sign = loop.signs[i];

    // الفقد يظل مرتبطاً باتجاه الأنبوب a -> b.
    // إشارة المسار تضرب الفقد، ولا نعيد تفسير اتجاه المضخة.
    residual += sign * signedHeadLoss(pipe, flow, nu);
    derivativeSum += derivativeHeadLoss(pipe, flow, nu);
  }

  return {
    residual,
    derivativeSum
  };
}

function calculateContinuityError(nodesArr, pipesArr, Q, excludedIds) {
  const netOut = new Map(nodesArr.map(node => [node.id, 0]));

  pipesArr.forEach(pipe => {
    const flow = Q.get(pipe.id) || 0;

    netOut.set(pipe.a, netOut.get(pipe.a) + flow);
    netOut.set(pipe.b, netOut.get(pipe.b) - flow);
  });

  let maximum = 0;

  nodesArr.forEach(node => {
    if (excludedIds.has(node.id)) return;

    const demand = node.type === "demand"
      ? node.demand / 1000
      : 0;

    const injection =
      node.type === "source" && node.sourceMode === "flow"
        ? node.sourceFlow / 1000
        : 0;

    const residual = netOut.get(node.id) + demand - injection;

    maximum = Math.max(maximum, Math.abs(residual * 1000));
  });

  return {
    maxContinuityLps: maximum,
    netOut
  };
}

function calculateHeadsOnTree(
  nodesArr,
  pipesArr,
  parentNode,
  parentPipe,
  rootId,
  rootHead,
  Q,
  nu
) {
  const heads = new Map([[rootId, rootHead]]);
  const children = new Map(nodesArr.map(node => [node.id, []]));

  for (const [nodeId, parentId] of parentNode) {
    if (parentId !== null && parentId !== undefined) {
      children.get(parentId).push(nodeId);
    }
  }

  const queue = [rootId];

  while (queue.length) {
    const parentId = queue.shift();
    const parentHead = heads.get(parentId);

    for (const childId of children.get(parentId) || []) {
      const pipe = parentPipe.get(childId);
      const flow = Q.get(pipe.id) || 0;
      const lossAB = signedHeadLoss(pipe, flow, nu);

      let childHead;

      if (pipe.a === parentId && pipe.b === childId) {
        childHead = parentHead - lossAB;
      } else {
        childHead = parentHead + lossAB;
      }

      heads.set(childId, childHead);
      queue.push(childId);
    }
  }

  return heads;
}

function calculateEnergyEquationError(pipesArr, heads, Q, nu) {
  let maximum = 0;

  pipesArr.forEach(pipe => {
    if (isPipeClosed(pipe)) return;
    const ha = heads.get(pipe.a);
    const hb = heads.get(pipe.b);
    const flow = Q.get(pipe.id) || 0;

    const residual =
      ha - hb - signedHeadLoss(pipe, flow, nu);

    maximum = Math.max(maximum, Math.abs(residual));
  });

  return maximum;
}

/* ==========================================================
   بناء بيانات نتائج الأنابيب
   ========================================================== */

function buildPipeResults(Q, nu) {
  const pipeData = new Map();

  pipes.forEach(pipe => {
    const q = isPipeClosed(pipe) ? 0 : (Q.get(pipe.id) || 0);
    const absQ = Math.abs(q);

    if (isPipeClosed(pipe)) {
      pipeData.set(pipe.id, {
        q: 0,
        velocity: 0,
        reynolds: 0,
        frictionFactor: NaN,
        hf: NaN,
        hm: NaN,
        totalK: NaN,
        pumpHead: 0,
        pumpRangeValid: true,
        pumpOperatingPointValid: true,
        pumpRange: null,
        pumpStatus: "غير عامل",
        headloss: NaN,
        flowRegime: "مغلق بواسطة المحبس",
        isClosed: true
      });
      return;
    }

    const losses = getPipeLossBreakdown(pipe, absQ, nu);
    const pumpEvaluation = getPumpCurveEvaluation(pipe, q);
    const pumpHead = pumpEvaluation.head;
    const pumpStatus = !pipe.isPump
      ? "لا توجد مضخة"
      : q < -1e-12
        ? "عكس اتجاه المضخة"
        : !pumpEvaluation.inRange
          ? "خارج مجال المنحنى"
          : "ضمن مجال المنحنى";

    pipeData.set(pipe.id, {
      q,
      velocity: losses.velocity,
      reynolds: losses.reynolds,
      frictionFactor: losses.frictionFactor,
      hf: losses.hf,
      hm: losses.hm,
      totalK: losses.totalK,
      pumpHead,
      pumpRangeValid: !pipe.isPump || pumpEvaluation.inRange,
      pumpOperatingPointValid: !pipe.isPump || (pumpEvaluation.inRange && !pumpEvaluation.reverse),
      pumpRange: pipe.isPump ? {
        min: pumpEvaluation.qMin ?? 0,
        max: pumpEvaluation.qMax ?? (pipe.pumpMode === "catalog" ? 0 : pipe.Qmax),
        actual: Math.abs(q * 1000),
        mode: pumpEvaluation.mode
      } : null,
      pumpStatus,
      headloss: signedHeadLoss(pipe, q, nu),
      flowRegime: classifyFlow(losses.reynolds),
      isClosed: false
    });
  });

  return pipeData;
}

/* ==========================================================
   التحذيرات الهندسية الإرشادية
   ========================================================== */

function buildHydraulicWarnings(
  nodeHeads,
  relativeHeadNodeIds,
  pipeData,
  density
) {
  const warnings = [];

  nodes.forEach(node => {
    if (relativeHeadNodeIds.has(node.id)) return;

    if (node.type === "source" && node.sourceMode === "head") {
      return;
    }

    const head = nodeHeads.get(node.id);
    const pressureHead = head - node.elevation;

    if (pressureHead < -0.01) {
      warnings.push(
        "ضغط سالب عند «" + node.name +
        "»؛ تحقق من مناسيب المصدر والعقدة وفواقد الشبكة."
      );
    } else if (node.type === "demand" && pressureHead < 15) {
      warnings.push(
        "الضغط المتاح منخفض نسبياً عند «" + node.name +
        "» (" + fmt(pressureHead, 2) + " م)."
      );
    } else if (node.type === "demand" && pressureHead > 60) {
      warnings.push(
        "الضغط مرتفع نسبياً عند «" + node.name +
        "» (" + fmt(pressureHead, 2) + " م). راجع تصنيف الأنابيب والمعدات."
      );
    }
  });

  pipes.forEach(pipe => {
    const result = pipeData.get(pipe.id);
    if (!result || result.isClosed) return;

    if (result.velocity > pipe.velocityMax) {
      warnings.push(
        "السرعة في P" + pipe.id + " أعلى من الحد الأقصى المحدد (" +
        fmt(result.velocity, 2) + " م/ث؛ الحد " +
        fmt(pipe.velocityMax, 2) + " م/ث)."
      );
    } else if (result.velocity > 0 && result.velocity < pipe.velocityMin) {
      warnings.push(
        "السرعة في P" + pipe.id + " أقل من الحد الأدنى المحدد (" +
        fmt(result.velocity, 2) + " م/ث؛ الحد " +
        fmt(pipe.velocityMin, 2) + " م/ث)."
      );
    }

    if (pipe.qTarget > 0 &&
        Math.abs(result.q * 1000 - pipe.qTarget) > Math.max(0.01, pipe.qTarget * 0.05)) {
      warnings.push(
        "التصريف المحسوب في P" + pipe.id + " (" +
        fmt(Math.abs(result.q * 1000), 2) +
        " لتر/ث) يختلف عن التصريف المستهدف (" +
        fmt(pipe.qTarget, 2) + " لتر/ث) بأكثر من 5%."
      );
    }

    if (pipe.isPump) {
      const qLps = Math.abs(result.q * 1000);
      const range = result.pumpRange || {
        min: pipe.pumpMode === "catalog" ? 0 : 0,
        max: pipe.pumpMode === "catalog" ? 0 : pipe.Qmax
      };

      if (result.pumpRangeValid === false) {
        warnings.push(
          "نقطة تشغيل مضخة P" + pipe.id + " خارج مجال المنحنى " +
          "(التصريف المحسوب " + fmt(qLps, 4) + " لتر/ث، والمجال المدخل " +
          fmt(range.min, 4) + " إلى " + fmt(range.max, 4) + " لتر/ث). " +
          "استُخدمت قيمة طرف المنحنى كامتداد عددي مؤقت فقط؛ هذه النتيجة غير صالحة لاعتماد أداء المضخة أو تصميمها. " +
          "وسّع بيانات المنحنى أو راجع اختيار المضخة."
        );
      } else if (qLps > 0 && qLps < Math.max(range.max || pipe.Qmax, 0.001) * 0.1) {
        warnings.push(
          "تصريف المضخة في P" + pipe.id +
          " منخفض مقارنة بمجال المنحنى؛ راجع مجال التشغيل المسموح لدى الشركة المصنعة."
        );
      }

      if (result.q < 0) {
        warnings.push(
          "الجريان في P" + pipe.id +
          " عكس اتجاه المضخة المعرف من a إلى b؛ " +
          "نموذج المضخة لا يضيف رفعاً عند الجريان العكسي."
        );
      }
    }
  });

  return warnings;
}

/* ==========================================================
   محلل هاردي كروس
   ========================================================== */

function solveHydraulicsHardyCross() {
  validateNetworkData();

  const water = getWaterProperties();
  const nu = water.kinematicViscosity;

  const { components } = buildComponents();

  const Q = new Map(pipes.map(pipe => [pipe.id, 0]));
  const heads = new Map();
  const fixedHeadIds = new Set();
  const anchorIds = new Set();
  const relativeHeadNodeIds = new Set();

  const allLoopInfo = [];
  const iterationLog = [];
  const loopResiduals = [];

  let totalIterations = 0;
  let maxDeltaOverall = 0;
  let loopCounter = 0;
  let allComponentsConverged = true;

  for (const component of components) {
    const compNodes = component.nodes;
    const compIds = new Set(compNodes.map(node => node.id));
    const compPipes = pipes.filter(pipe =>
      !isPipeClosed(pipe) &&
      compIds.has(pipe.a) && compIds.has(pipe.b)
    );

    const headSources = compNodes.filter(node =>
      node.type === "source" && node.sourceMode === "head"
    );

    const flowSources = compNodes.filter(node =>
      node.type === "source" && node.sourceMode === "flow"
    );

    if (!headSources.length && !flowSources.length) {
      throw new Error("أحد مكونات الشبكة لا يحتوي على مصدر.");
    }

    if (headSources.length > 1) {
      throw new Error(
        "هاردي كروس في هذه النسخة يدعم مصدراً واحداً ذا حمل معلوم " +
        "في كل مكوّن. استخدم طريقة التدرج العام عند وجود عدة مصادر حمل."
      );
    }

    let refNode;
    let refHead;

    if (headSources.length === 1) {
      refNode = headSources[0];
      refHead = refNode.head;
      fixedHeadIds.add(refNode.id);
      heads.set(refNode.id, refHead);
    } else {
      const sourceIn = flowSources.reduce(
        (sum, node) => sum + node.sourceFlow / 1000,
        0
      );

      const demandOut = compNodes.reduce(
        (sum, node) =>
          sum + (node.type === "demand" ? node.demand / 1000 : 0),
        0
      );

      if (Math.abs(sourceIn - demandOut) > 1e-8) {
        throw new Error(
          "مكوّن الشبكة الذي يعتمد على تصريف معلوم غير متزن: " +
          "مجموع تصريف المصادر لا يساوي مجموع الطلب."
        );
      }

      refNode = flowSources[0];
      refHead = 0;

      anchorIds.add(refNode.id);
      relativeHeadNodeIds.add(refNode.id);
      heads.set(refNode.id, 0);

      compNodes.forEach(node => {
        relativeHeadNodeIds.add(node.id);
      });
    }

    const tree = buildLoopsWithSigns(
      compNodes,
      compPipes,
      refNode.id
    );

    const initQ = initializeHardyCrossFlows(
      compNodes,
      compPipes,
      tree.treePipeIds,
      tree.parentNode,
      tree.parentPipe,
      tree.treeChildren,
      refNode.id
    );

    compPipes.forEach(pipe => {
      Q.set(pipe.id, initQ.get(pipe.id) ?? 0);
    });

    const totalSpecifiedFlow =
      compNodes.reduce((sum, node) => {
        if (node.type === "demand") return sum + node.demand / 1000;
        if (node.type === "source" && node.sourceMode === "flow") {
          return sum + node.sourceFlow / 1000;
        }
        return sum;
      }, 0);

    const dqCap = Math.max(0.05, totalSpecifiedFlow * 0.5);

    let iter = 0;
    let maxDelta = 0;
    let maxLoopResidual = 0;
    let converged = tree.loops.length === 0;

    const componentSteps = [];

    while (iter < HC_MAX_ITER && !converged) {
      maxDelta = 0;

      const stepLog = {
        iteration: iter + 1,
        loops: []
      };

      for (let loopIndex = 0;
           loopIndex < tree.loops.length;
           loopIndex++) {
        const loop = tree.loops[loopIndex];

        const balance = getLoopResidual(loop, Q, nu);

        if (!(balance.derivativeSum > 0)) {
          throw new Error(
            "مجموع مشتقات الفقد غير صالح في إحدى الحلقات."
          );
        }

        let deltaQ =
          -balance.residual / balance.derivativeSum;

        if (Math.abs(deltaQ) > dqCap) {
          deltaQ = Math.sign(deltaQ) * dqCap;
        }

        for (let k = 0; k < loop.pipes.length; k++) {
          const pipe = loop.pipes[k];
          const sign = loop.signs[k];

          Q.set(
            pipe.id,
            Q.get(pipe.id) + deltaQ * sign
          );
        }

        maxDelta = Math.max(maxDelta, Math.abs(deltaQ));

        stepLog.loops.push({
          loopLocalId: loopIndex + 1,
          deltaQ,
          residualBefore: balance.residual,
          derivativeSum: balance.derivativeSum
        });
      }

      componentSteps.push(stepLog);
      iter++;

      maxLoopResidual = 0;

      for (const loop of tree.loops) {
        const balance = getLoopResidual(loop, Q, nu);

        maxLoopResidual = Math.max(
          maxLoopResidual,
          Math.abs(balance.residual)
        );
      }

      converged =
        maxDelta <= HC_FLOW_TOL &&
        maxLoopResidual <= HC_HEAD_TOL;
    }

    totalIterations = Math.max(totalIterations, iter);
    maxDeltaOverall = Math.max(maxDeltaOverall, maxDelta);

    if (!converged) allComponentsConverged = false;

    iterationLog.push({
      component: compNodes[0].name,
      iterations: iter,
      converged,
      finalMaxDelta: maxDelta,
      maxLoopResidual,
      steps: componentSteps
    });

    for (const loop of tree.loops) {
      loopCounter++;

      const balance = getLoopResidual(loop, Q, nu);

      const detail = {
        globalId: loopCounter,
        component: compNodes[0].name,
        nodeNames: loop.nodes.map(id =>
          nodeById(id)?.name || ("N" + id)
        ),
        nodeIds: loop.nodes,
        pipeIds: loop.pipes.map(pipe => pipe.id),
        pipeLabels: loop.pipes.map((pipe, index) =>
          "P" + pipe.id +
          (loop.signs[index] > 0 ? "(+)" : "(−)")
        ),
        signs: loop.signs,
        orientation: loop.orientation,
        chordPipeId: loop.chordPipeId
      };

      allLoopInfo.push(detail);

      loopResiduals.push({
        loopId: loopCounter,
        chordPipeId: loop.chordPipeId,
        residual: balance.residual
      });
    }

    const componentHeads = calculateHeadsOnTree(
      compNodes,
      compPipes,
      tree.parentNode,
      tree.parentPipe,
      refNode.id,
      refHead,
      Q,
      nu
    );

    componentHeads.forEach((value, id) => {
      heads.set(id, value);
    });
  }

  const pipeData = buildPipeResults(Q, nu);

  const nodeHeads = new Map(
    nodes.map(node => [node.id, heads.get(node.id) ?? 0])
  );

  const continuity = calculateContinuityError(
    nodes,
    pipes,
    Q,
    new Set([...fixedHeadIds, ...anchorIds])
  );

  const maxHeadEquationResidual =
    calculateEnergyEquationError(pipes, nodeHeads, Q, nu);

  const maxLoopResidual = loopResiduals.reduce(
    (maximum, item) =>
      Math.max(maximum, Math.abs(item.residual)),
    0
  );

  const fixedSourceFlows = new Map();

  fixedHeadIds.forEach(id => {
    fixedSourceFlows.set(
      id,
      (continuity.netOut.get(id) || 0) * 1000
    );
  });

  const converged =
    allComponentsConverged &&
    continuity.maxContinuityLps <= 1e-5 &&
    maxHeadEquationResidual <= HC_HEAD_TOL;

  const warnings = buildHydraulicWarnings(
    nodeHeads,
    relativeHeadNodeIds,
    pipeData,
    water.density
  );

  if (!converged) {
    warnings.unshift(
      "لم يتحقق التقارب الكامل لهاردي كروس. " +
      "راجع بواقي الحلقات والطاقة والاستمرارية قبل اعتماد النتائج."
    );
  }

  return {
    method: "hardyCross",
    converged,
    iterations: totalIterations,
    convergenceMaxDelta: maxDeltaOverall,
    pipeData,
    nodeHeads,
    fixedSourceFlows,
    relativeHeadNodeIds,
    maxContinuityLps: continuity.maxContinuityLps,
    maxHeadEquationResidual,
    loopCount: allLoopInfo.length,
    maxLoopResidual,
    loopResiduals,
    loopDetails: allLoopInfo,
    iterationLog,
    warnings,
    componentCount: components.length,
    water
  };
}

/* ==========================================================
   فحص موازين الحلقات بطريقة عامة
   ========================================================== */

function computeLoopBalances(allNodes, allPipes, pipeData) {
  const activePipes = allPipes.filter(pipe => !isPipeClosed(pipe));
  const adjacency = new Map(
    allNodes.map(node => [node.id, []])
  );

  activePipes.forEach(pipe => {
    adjacency.get(pipe.a).push({
      pipe,
      other: pipe.b
    });

    adjacency.get(pipe.b).push({
      pipe,
      other: pipe.a
    });
  });

  const visited = new Set();
  const treeEdgeIds = new Set();
  const treeAdjacency = new Map(
    allNodes.map(node => [node.id, []])
  );

  for (const root of allNodes) {
    if (visited.has(root.id)) continue;

    visited.add(root.id);
    const queue = [root.id];

    while (queue.length) {
      const current = queue.shift();

      for (const item of adjacency.get(current)) {
        if (visited.has(item.other)) continue;

        visited.add(item.other);
        treeEdgeIds.add(item.pipe.id);

        treeAdjacency.get(current).push({
          pipe: item.pipe,
          other: item.other
        });

        treeAdjacency.get(item.other).push({
          pipe: item.pipe,
          other: current
        });

        queue.push(item.other);
      }
    }
  }

  const chords = activePipes.filter(
    pipe => !treeEdgeIds.has(pipe.id)
  );

  const residuals = [];

  for (const chord of chords) {
    const queue = [chord.b];
    const parent = new Map([[chord.b, null]]);
    const parentEdge = new Map();

    while (queue.length && !parent.has(chord.a)) {
      const current = queue.shift();

      for (const item of treeAdjacency.get(current)) {
        if (parent.has(item.other)) continue;

        parent.set(item.other, current);
        parentEdge.set(item.other, item.pipe);
        queue.push(item.other);
      }
    }

    if (!parent.has(chord.a)) continue;

    // الوتر في اتجاه a -> b.
    let sum = pipeData.get(chord.id).headloss;
    let current = chord.a;

    // ثم مسار الشجرة من b -> a.
    while (current !== chord.b) {
      const previous = parent.get(current);
      const pipe = parentEdge.get(current);

      if (previous === null || !pipe) {
        throw new Error("تعذر استكمال مسار إحدى الحلقات.");
      }

      const h = pipeData.get(pipe.id).headloss;

      const lossAlongPath =
        previous === pipe.a && current === pipe.b
          ? h
          : -h;

      sum += lossAlongPath;
      current = previous;
    }

    residuals.push({
      chordPipeId: chord.id,
      residual: sum
    });
  }

  return {
    loopCount: residuals.length,
    residuals,
    maxResidual: residuals.reduce(
      (maximum, item) =>
        Math.max(maximum, Math.abs(item.residual)),
      0
    )
  };
}

/* ==========================================================
   محلل نيوتن–رافسون المتزامن (Simultaneous Newton-Raphson)
   ========================================================== */

function solveHydraulicsNewton() {
  validateNetworkData();

  const water = getWaterProperties();
  const nu = water.kinematicViscosity;

  const { components } = buildComponents();
  const activePipes = pipes.filter(pipe => !isPipeClosed(pipe));

  const fixedHeadIds = new Set();
  const anchorIds = new Set();
  const knownHeads = new Map();
  const relativeHeadNodeIds = new Set();
  const initialHeads = new Map();

  for (const component of components) {
    const fixedSources = component.nodes.filter(node =>
      node.type === "source" && node.sourceMode === "head"
    );

    if (fixedSources.length) {
      const averageHead = fixedSources.reduce(
        (sum, node) => sum + node.head,
        0
      ) / fixedSources.length;

      component.nodes.forEach(node => {
        initialHeads.set(node.id, averageHead);
      });

      fixedSources.forEach(node => {
        fixedHeadIds.add(node.id);
        knownHeads.set(node.id, node.head);
        initialHeads.set(node.id, node.head);
      });
    } else {
      const sourceNodes = component.nodes.filter(node =>
        node.type === "source" && node.sourceMode === "flow"
      );

      if (!sourceNodes.length) {
        throw new Error("أحد مكونات الشبكة لا يحتوي على مصدر.");
      }

      const sourceIn = sourceNodes.reduce(
        (sum, node) => sum + node.sourceFlow / 1000,
        0
      );

      const demandOut = component.nodes.reduce(
        (sum, node) =>
          sum + (node.type === "demand" ? node.demand / 1000 : 0),
        0
      );

      if (Math.abs(sourceIn - demandOut) > 1e-8) {
        throw new Error(
          "مكوّن الشبكة الذي يعتمد على تصريف معلوم غير متزن."
        );
      }

      const anchor = sourceNodes[0];

      anchorIds.add(anchor.id);
      knownHeads.set(anchor.id, 0);

      component.nodes.forEach(node => {
        initialHeads.set(node.id, 0);
        relativeHeadNodeIds.add(node.id);
      });
    }
  }

  const headVariableNodes = nodes.filter(
    node => !knownHeads.has(node.id)
  );

  const headColumn = new Map(
    headVariableNodes.map((node, index) => [
      node.id,
      activePipes.length + index
    ])
  );

  const continuityNodes = nodes.filter(
    node => !fixedHeadIds.has(node.id) &&
            !anchorIds.has(node.id)
  );

  const dimension = activePipes.length + headVariableNodes.length;

  if (continuityNodes.length !== headVariableNodes.length) {
    throw new Error(
      "عدد معادلات الاستمرارية لا يطابق عدد مجاهيل الأحمال."
    );
  }

  let heads = new Map(
    nodes.map(node => [
      node.id,
      initialHeads.get(node.id) ?? 0
    ])
  );

  knownHeads.forEach((value, id) => {
    heads.set(id, value);
  });

  const totalDemand = nodes.reduce(
    (sum, node) =>
      sum + (node.type === "demand" ? node.demand / 1000 : 0),
    0
  );

  const totalKnownInflow = nodes.reduce(
    (sum, node) =>
      sum + (
        node.type === "source" && node.sourceMode === "flow"
          ? node.sourceFlow / 1000
          : 0
      ),
    0
  );

  const initialMagnitude = Math.max(
    1e-4,
    (totalDemand + totalKnownInflow) / Math.max(1, activePipes.length)
  );

  let flows = activePipes.map(pipe => {
    const q0 = finiteNumber(pipe.q0, 0) / 1000;
    return q0 !== 0 ? q0 : initialMagnitude;
  });

  const flowScale = Math.max(
    1e-3,
    totalDemand + totalKnownInflow,
    flows.reduce((sum, flow) => sum + Math.abs(flow), 0)
  );

  const headScale = Math.max(
    1,
    ...components.map(component => {
      const values = component.nodes
        .filter(node => fixedHeadIds.has(node.id))
        .map(node => node.head);

      return values.length
        ? Math.max(...values) - Math.min(...values)
        : 1;
    })
  );

  function evaluate(qValues, hValues, withJacobian) {
    const residual = Array(dimension).fill(0);
    const massByNode = new Map(
      nodes.map(node => [node.id, 0])
    );

    const energyResiduals = [];
    const massResiduals = [];

    const J = withJacobian
      ? Array.from(
          { length: dimension },
          () => Array(dimension).fill(0)
        )
      : null;

    activePipes.forEach((pipe, index) => {
      const q = qValues[index];
      const loss = signedHeadLoss(pipe, q, nu);

      const energy =
        hValues.get(pipe.a) -
        hValues.get(pipe.b) -
        loss;

      residual[index] = energy;
      energyResiduals.push(energy);

      massByNode.set(
        pipe.a,
        massByNode.get(pipe.a) + q
      );

      massByNode.set(
        pipe.b,
        massByNode.get(pipe.b) - q
      );

      if (J) {
        J[index][index] =
          -derivativeHeadLoss(pipe, q, nu);

        const columnA = headColumn.get(pipe.a);
        const columnB = headColumn.get(pipe.b);

        if (columnA !== undefined) {
          J[index][columnA] = 1;
        }

        if (columnB !== undefined) {
          J[index][columnB] = -1;
        }
      }
    });

    continuityNodes.forEach((node, rowIndex) => {
      const demand = node.type === "demand"
        ? node.demand / 1000
        : 0;

      const injection =
        node.type === "source" && node.sourceMode === "flow"
          ? node.sourceFlow / 1000
          : 0;

      const mass =
        massByNode.get(node.id) + demand - injection;

      const row = activePipes.length + rowIndex;

      residual[row] = mass;
      massResiduals.push(mass);

      if (J) {
        activePipes.forEach((pipe, pipeIndex) => {
          if (pipe.a === node.id) {
            J[row][pipeIndex] = 1;
          } else if (pipe.b === node.id) {
            J[row][pipeIndex] = -1;
          }
        });
      }
    });

    let normSquared = 0;

    energyResiduals.forEach(value => {
      normSquared += Math.pow(value / headScale, 2);
    });

    massResiduals.forEach(value => {
      normSquared += Math.pow(value / flowScale, 2);
    });

    return {
      residual,
      J,
      maxEnergy: energyResiduals.reduce(
        (maximum, value) =>
          Math.max(maximum, Math.abs(value)),
        0
      ),
      maxMass: massResiduals.reduce(
        (maximum, value) =>
          Math.max(maximum, Math.abs(value)),
        0
      ),
      norm: Math.sqrt(normSquared)
    };
  }

  const massTolerance = Math.max(
    1e-9,
    flowScale * NEWTON_REL_TOL
  );

  let converged = false;
  let iterations = 0;

  for (; iterations < NEWTON_MAX_ITER; iterations++) {
    const current = evaluate(flows, heads, true);

    if (
      current.maxEnergy <= NEWTON_HEAD_TOL &&
      current.maxMass <= massTolerance
    ) {
      converged = true;
      break;
    }

    const delta = solveLinearSystem(
      current.J,
      current.residual.map(value => -value)
    );

    let accepted = false;

    for (
      let lambda = 1;
      lambda >= 1 / 4096;
      lambda /= 2
    ) {
      const candidateFlows = flows.map(
        (value, index) =>
          value + lambda * delta[index]
      );

      const candidateHeads = new Map(heads);

      headVariableNodes.forEach((node, index) => {
        candidateHeads.set(
          node.id,
          heads.get(node.id) +
          lambda * delta[activePipes.length + index]
        );
      });

      if (
        candidateFlows.some(value => !Number.isFinite(value)) ||
        Array.from(candidateHeads.values()).some(
          value => !Number.isFinite(value)
        )
      ) {
        continue;
      }

      const candidate = evaluate(
        candidateFlows,
        candidateHeads,
        false
      );

      if (
        candidate.norm < current.norm ||
        (
          candidate.maxEnergy <= NEWTON_HEAD_TOL &&
          candidate.maxMass <= massTolerance
        )
      ) {
        flows = candidateFlows;
        heads = candidateHeads;
        accepted = true;
        break;
      }
    }

    if (!accepted) {
      throw new Error(
        "لم يتمكن التدرج العام من تحسين الحل. " +
        "راجع القيم الابتدائية وشروط المصادر والمضخات."
      );
    }
  }

  const finalCheck = evaluate(flows, heads, false);

  converged =
    finalCheck.maxEnergy <= NEWTON_HEAD_TOL &&
    finalCheck.maxMass <= massTolerance;

  const Q = new Map(pipes.map(pipe => [pipe.id, 0]));
  activePipes.forEach((pipe, index) => Q.set(pipe.id, flows[index]));

  const pipeData = buildPipeResults(Q, nu);

  const nodeHeads = new Map(
    nodes.map(node => [
      node.id,
      heads.get(node.id) ?? 0
    ])
  );

  const continuity = calculateContinuityError(
    nodes,
    pipes,
    Q,
    new Set([...fixedHeadIds, ...anchorIds])
  );

  const fixedSourceFlows = new Map();

  const netOut = continuity.netOut;

  fixedHeadIds.forEach(id => {
    fixedSourceFlows.set(
      id,
      (netOut.get(id) || 0) * 1000
    );
  });

  const loopDiagnostics = computeLoopBalances(
    nodes,
    pipes,
    pipeData
  );

  const maxHeadEquationResidual = finalCheck.maxEnergy;

  const warnings = buildHydraulicWarnings(
    nodeHeads,
    relativeHeadNodeIds,
    pipeData,
    water.density
  );

  if (!converged) {
    warnings.unshift(
      "بلغ المحلل الحد الأقصى للتكرارات دون تحقق شروط التقارب. " +
      "النتائج المعروضة مؤقتة ولا تعتمد قبل معالجة السبب."
    );
  }

  return {
    method: "newton",
    converged,
    iterations: Math.min(iterations + (converged ? 0 : 0), NEWTON_MAX_ITER),
    pipeData,
    nodeHeads,
    fixedSourceFlows,
    relativeHeadNodeIds,
    maxContinuityLps: continuity.maxContinuityLps,
    maxHeadEquationResidual,
    loopCount: loopDiagnostics.loopCount,
    maxLoopResidual: loopDiagnostics.maxResidual,
    loopResiduals: loopDiagnostics.residuals,
    warnings,
    componentCount: components.length,
    water
  };
}

/* ==========================================================
   حل نظام متناثر متماثل موجب التعريف بطريقة PCG
   يستخدمه محلل التدرج العام GGA
   ========================================================== */

function solveSparsePCG(diagonal, offDiagonal, rhs, initialGuess = null) {
  const n = rhs.length;
  if (n === 0) return { x: [], iterations: 0, residual: 0 };
  if (diagonal.length !== n || offDiagonal.length !== n) {
    throw new Error("أبعاد مصفوفة GGA غير متوافقة.");
  }

  const multiply = vector => {
    const result = Array(n).fill(0);
    for (let i = 0; i < n; i++) {
      let value = diagonal[i] * vector[i];
      for (const [j, coefficient] of offDiagonal[i]) {
        value += coefficient * vector[j];
      }
      result[i] = value;
    }
    return result;
  };

  const x = initialGuess && initialGuess.length === n
    ? initialGuess.slice()
    : Array(n).fill(0);

  const Ax = multiply(x);
  let r = rhs.map((value, i) => value - Ax[i]);
  const normB = Math.sqrt(rhs.reduce((sum, value) => sum + value * value, 0));
  const target = Math.max(
    1e-13,
    Math.min(1e-10, GGA_CG_REL_TOL * Math.max(1, normB))
  );
  let residualNorm = Math.sqrt(r.reduce((sum, value) => sum + value * value, 0));

  if (residualNorm <= target) {
    return { x, iterations: 0, residual: residualNorm };
  }

  const z = r.map((value, i) => {
    if (!(diagonal[i] > 0) || !Number.isFinite(diagonal[i])) {
      throw new Error("ظهرت قيمة قطرية غير موجبة في مصفوفة GGA.");
    }
    return value / diagonal[i];
  });

  let p = z.slice();
  let rz = r.reduce((sum, value, i) => sum + value * z[i], 0);
  const maxIterations = Math.max(100, Math.min(10000, n * 30));

  for (let iteration = 1; iteration <= maxIterations; iteration++) {
    const Ap = multiply(p);
    const pAp = p.reduce((sum, value, i) => sum + value * Ap[i], 0);

    if (!(pAp > 0) || !Number.isFinite(pAp)) {
      throw new Error(
        "فشل PCG: المصفوفة ليست موجبة التعريف أو أن الشبكة غير مهيأة جيداً."
      );
    }

    const alpha = rz / pAp;
    for (let i = 0; i < n; i++) {
      x[i] += alpha * p[i];
      r[i] -= alpha * Ap[i];
    }

    residualNorm = Math.sqrt(
      r.reduce((sum, value) => sum + value * value, 0)
    );

    if (residualNorm <= target) {
      return { x, iterations: iteration, residual: residualNorm };
    }

    const zNew = r.map((value, i) => value / diagonal[i]);
    const rzNew = r.reduce((sum, value, i) => sum + value * zNew[i], 0);
    const beta = rzNew / rz;

    p = zNew.map((value, i) => value + beta * p[i]);
    for (let i = 0; i < n; i++) z[i] = zNew[i];
    rz = rzNew;
  }

  throw new Error(
    "لم يتقارب حل المصفوفة المتناثرة داخل GGA. " +
    "قد تكون الشبكة سيئة التهيئة أو تحتوي على مقاومات شديدة التفاوت."
  );
}

/* ==========================================================
   محلل التدرج العام الحقيقي Global Gradient Algorithm

   في كل تكرار:
   1) يبني مصفوفة العقد A = B G^-1 B^T.
   2) يحل أحمال العقد بطريقة PCG متناثرة.
   3) يحدّث تصريف كل وصلة بالعلاقة التصحيحية GGA.
   ========================================================== */

function solveHydraulicsGGA() {
  validateNetworkData();

  const water = getWaterProperties();
  const nu = water.kinematicViscosity;
  const { components } = buildComponents();
  const activePipes = pipes.filter(pipe => !isPipeClosed(pipe));

  const fixedHeadIds = new Set();
  const anchorIds = new Set();
  const knownHeads = new Map();
  const relativeHeadNodeIds = new Set();
  const initialHeads = new Map();

  for (const component of components) {
    const componentNodes = component.nodes;
    const fixedSources = componentNodes.filter(node =>
      node.type === "source" && node.sourceMode === "head"
    );

    if (fixedSources.length) {
      const averageHead = fixedSources.reduce(
        (sum, node) => sum + node.head, 0
      ) / fixedSources.length;

      componentNodes.forEach(node => initialHeads.set(node.id, averageHead));
      fixedSources.forEach(node => {
        fixedHeadIds.add(node.id);
        knownHeads.set(node.id, node.head);
        initialHeads.set(node.id, node.head);
      });
    } else {
      const flowSources = componentNodes.filter(node =>
        node.type === "source" && node.sourceMode === "flow"
      );

      if (!flowSources.length) {
        throw new Error("أحد مكونات الشبكة لا يحتوي على مصدر معلوم.");
      }

      const sourceFlow = flowSources.reduce(
        (sum, node) => sum + node.sourceFlow / 1000, 0
      );
      const demandFlow = componentNodes.reduce(
        (sum, node) => sum + (node.type === "demand" ? node.demand / 1000 : 0),
        0
      );

      if (Math.abs(sourceFlow - demandFlow) > 1e-8) {
        throw new Error(
          "مكوّن يعتمد على تصريف معلوم، لكن مجموع تصريفات المصادر " +
          "لا يساوي مجموع الطلبات."
        );
      }

      // مرجع حمل صفري لإزالة حرية اختيار مستوى الحمل المطلق.
      // مع تحقق الاتزان الكلي، يصبح اتزان هذه العقدة تابعاً لبقية العقد.
      const anchor = flowSources[0];
      anchorIds.add(anchor.id);
      knownHeads.set(anchor.id, 0);
      componentNodes.forEach(node => {
        initialHeads.set(node.id, 0);
        relativeHeadNodeIds.add(node.id);
      });
    }
  }

  const unknownNodes = nodes.filter(node => !knownHeads.has(node.id));
  const unknownIndex = new Map(
    unknownNodes.map((node, index) => [node.id, index])
  );
  const nUnknown = unknownNodes.length;

  const continuityNodes = nodes.filter(node =>
    !fixedHeadIds.has(node.id) && !anchorIds.has(node.id)
  );

  if (continuityNodes.length !== nUnknown) {
    throw new Error("عدد معادلات الاستمرارية لا يطابق مجاهيل الحمل في GGA.");
  }

  const totalDemand = nodes.reduce(
    (sum, node) => sum + (node.type === "demand" ? node.demand / 1000 : 0),
    0
  );
  const totalFlowSources = nodes.reduce(
    (sum, node) => sum + (
      node.type === "source" && node.sourceMode === "flow"
        ? node.sourceFlow / 1000 : 0
    ),
    0
  );
  const flowScale = Math.max(1e-4, totalDemand + totalFlowSources);
  const massTolerance = Math.max(1e-9, flowScale * GGA_FLOW_REL_TOL);
  const headScale = Math.max(
    1,
    ...components.map(component => {
      const values = component.nodes
        .filter(node => fixedHeadIds.has(node.id))
        .map(node => node.head);
      return values.length ? Math.max(...values) - Math.min(...values) : 1;
    })
  );

  let flows = activePipes.map(pipe => {
    const q0 = finiteNumber(pipe.q0, 0) / 1000;
    if (q0 !== 0) return q0;
    return Math.max(1e-5, flowScale / Math.max(1, activePipes.length));
  });

  let heads = new Map(nodes.map(node => [
    node.id,
    initialHeads.get(node.id) ?? 0
  ]));
  knownHeads.forEach((value, id) => heads.set(id, value));

  function evaluateState(qValues, headValues) {
    const netOut = new Map(nodes.map(node => [node.id, 0]));
    let maxEnergy = 0;
    let energyNormSquared = 0;

    activePipes.forEach((pipe, index) => {
      const q = qValues[index];
      const loss = signedHeadLoss(pipe, q, nu);
      const residual = headValues.get(pipe.a) - headValues.get(pipe.b) - loss;
      maxEnergy = Math.max(maxEnergy, Math.abs(residual));
      energyNormSquared += Math.pow(residual / headScale, 2);
      netOut.set(pipe.a, netOut.get(pipe.a) + q);
      netOut.set(pipe.b, netOut.get(pipe.b) - q);
    });

    let maxMass = 0;
    let massNormSquared = 0;
    for (const node of continuityNodes) {
      const demand = node.type === "demand" ? node.demand / 1000 : 0;
      const injection = node.type === "source" && node.sourceMode === "flow"
        ? node.sourceFlow / 1000 : 0;
      const residual = netOut.get(node.id) + demand - injection;
      maxMass = Math.max(maxMass, Math.abs(residual));
      massNormSquared += Math.pow(residual / flowScale, 2);
    }

    // نفحص عقدة المرجع ذات التصريف المعلوم أيضًا؛ اتزانها يتبع نظرياً
    // من اتزان بقية العقد وموازنة التدفق الكلية، لكنه يُقاس صراحةً هنا.
    for (const id of anchorIds) {
      const node = nodeById(id);
      const injection = node.sourceFlow / 1000;
      const residual = netOut.get(id) - injection;
      maxMass = Math.max(maxMass, Math.abs(residual));
      massNormSquared += Math.pow(residual / flowScale, 2);
    }

    return {
      maxEnergy,
      maxMassLps: maxMass * 1000,
      norm: Math.sqrt(energyNormSquared + massNormSquared),
      netOut
    };
  }

  let converged = false;
  let iterations = 0;
  let totalLinearIterations = 0;
  let lastCgResidual = 0;

  for (iterations = 1; iterations <= GGA_MAX_ITER; iterations++) {
    const currentState = evaluateState(flows, heads);

    if (currentState.maxEnergy <= GGA_HEAD_TOL &&
        currentState.maxMassLps <= massTolerance * 1000) {
      converged = true;
      iterations--;
      break;
    }

    const diagonal = Array(nUnknown).fill(0);
    const offDiagonal = Array.from({ length: nUnknown }, () => new Map());
    const rhs = Array(nUnknown).fill(0);
    const massBase = new Map(nodes.map(node => [node.id, 0]));
    const linkTerms = [];

    // تكوين مقاومات التدرج g=d(hL)/dQ ومساهمات المصفوفة المتناثرة.
    activePipes.forEach((pipe, index) => {
      const q = flows[index];
      const loss = signedHeadLoss(pipe, q, nu);
      const derivative = derivativeHeadLoss(pipe, q, nu);
      if (!(derivative > 0) || !Number.isFinite(derivative)) {
        throw new Error("مشتقة الفقد غير موجبة أو غير محدودة في P" + pipe.id + ".");
      }

      const conductance = 1 / derivative;
      if (!(conductance > 0) || !Number.isFinite(conductance)) {
        throw new Error("تعذر تكوين موصلية هيدروليكية صالحة في P" + pipe.id + ".");
      }

      massBase.set(pipe.a, massBase.get(pipe.a) + q);
      massBase.set(pipe.b, massBase.get(pipe.b) - q);
      linkTerms.push({ pipe, index, loss, conductance });

      const ia = unknownIndex.get(pipe.a);
      const ib = unknownIndex.get(pipe.b);
      const c = conductance;

      if (ia !== undefined) diagonal[ia] += c;
      if (ib !== undefined) diagonal[ib] += c;

      if (ia !== undefined && ib !== undefined) {
        offDiagonal[ia].set(ib, (offDiagonal[ia].get(ib) || 0) - c);
        offDiagonal[ib].set(ia, (offDiagonal[ib].get(ia) || 0) - c);
      }
    });

    for (const node of nodes) {
      const demand = node.type === "demand" ? node.demand / 1000 : 0;
      const injection = node.type === "source" && node.sourceMode === "flow"
        ? node.sourceFlow / 1000 : 0;
      massBase.set(node.id, massBase.get(node.id) + demand - injection);
    }

    unknownNodes.forEach((node, index) => {
      rhs[index] = -massBase.get(node.id);
    });

    for (const term of linkTerms) {
      const { pipe, loss, conductance: c } = term;
      const ia = unknownIndex.get(pipe.a);
      const ib = unknownIndex.get(pipe.b);
      const haKnown = knownHeads.get(pipe.a);
      const hbKnown = knownHeads.get(pipe.b);

      if (ia !== undefined) rhs[ia] += c * loss;
      if (ib !== undefined) rhs[ib] -= c * loss;
      if (ia !== undefined && ib === undefined) rhs[ia] += c * hbKnown;
      if (ib !== undefined && ia === undefined) rhs[ib] += c * haKnown;
    }

    let solvedHeads = [];
    if (nUnknown) {
      const initialGuess = unknownNodes.map(node => heads.get(node.id) ?? 0);
      const linear = solveSparsePCG(
        diagonal, offDiagonal, rhs, initialGuess
      );
      solvedHeads = linear.x;
      totalLinearIterations += linear.iterations;
      lastCgResidual = linear.residual;
    }

    const candidateHeads = new Map(heads);
    unknownNodes.forEach((node, index) => {
      candidateHeads.set(node.id, solvedHeads[index]);
    });
    knownHeads.forEach((value, id) => candidateHeads.set(id, value));

    const calculatedFlows = flows.map((q, index) => {
      const pipe = activePipes[index];
      const term = linkTerms[index];
      const headDifference = candidateHeads.get(pipe.a) - candidateHeads.get(pipe.b);
      return q + term.conductance * (headDifference - term.loss);
    });

    if (calculatedFlows.some(value => !Number.isFinite(value)) ||
        Array.from(candidateHeads.values()).some(value => !Number.isFinite(value))) {
      throw new Error("ظهرت قيم غير محدودة أثناء تحديث GGA.");
    }

    // تحديث GGA المباشر: بعد حل معادلات الأحمال، تحدّث كل وصلة
    // بتصحيح قياسي واحد. تُراقب شروط التقارب بعد التحديث، ولا يُعلن
    // النجاح إلا بعد تحقق بواقي الطاقة والاستمرارية معاً.
    let nextFlows = calculatedFlows;
    let nextHeads = candidateHeads;

    flows = nextFlows;
    heads = nextHeads;
  }

  const finalState = evaluateState(flows, heads);
  converged = finalState.maxEnergy <= GGA_HEAD_TOL &&
    finalState.maxMassLps <= massTolerance * 1000;
  if (iterations > GGA_MAX_ITER) iterations = GGA_MAX_ITER;

  const Q = new Map(pipes.map(pipe => [pipe.id, 0]));
  activePipes.forEach((pipe, index) => Q.set(pipe.id, flows[index]));
  const pipeData = buildPipeResults(Q, nu);
  const nodeHeads = new Map(nodes.map(node => [
    node.id,
    heads.get(node.id) ?? 0
  ]));

  const continuity = calculateContinuityError(
    nodes, pipes, Q, new Set([...fixedHeadIds, ...anchorIds])
  );
  const loopDiagnostics = computeLoopBalances(nodes, pipes, pipeData);
  const maxHeadEquationResidual = calculateEnergyEquationError(
    pipes, nodeHeads, Q, nu
  );

  // بواقي الحلقات تشخيص مستقل؛ لا نستبدل بها فحص الطاقة على كل أنبوب.
  const maxLoopResidual = loopDiagnostics.maxResidual;
  const fixedSourceFlows = new Map();
  fixedHeadIds.forEach(id => {
    fixedSourceFlows.set(id, (continuity.netOut.get(id) || 0) * 1000);
  });

  const warnings = buildHydraulicWarnings(
    nodeHeads, relativeHeadNodeIds, pipeData, water.density
  );
  if (!converged) {
    warnings.unshift(
      "لم تتحقق شروط التقارب في GGA؛ لا تعتمد النتائج قبل مراجعة " +
      "أخطاء الطاقة والاستمرارية وباقي الحلقات."
    );
  }

  if (maxLoopResidual > GGA_HEAD_TOL) {
    warnings.push(
      "باقي اتزان إحدى الحلقات يتجاوز حد الطاقة؛ راجع تشخيص الحلقات."
    );
  }

  return {
    method: "globalGradient",
    converged: converged && continuity.maxContinuityLps <= massTolerance * 1000 &&
      maxHeadEquationResidual <= GGA_HEAD_TOL,
    iterations,
    linearIterations: totalLinearIterations,
    linearResidual: lastCgResidual,
    pipeData,
    nodeHeads,
    fixedSourceFlows,
    relativeHeadNodeIds,
    maxContinuityLps: continuity.maxContinuityLps,
    maxHeadEquationResidual,
    loopCount: loopDiagnostics.loopCount,
    maxLoopResidual,
    loopResiduals: loopDiagnostics.residuals,
    warnings,
    componentCount: components.length,
    water
  };
}

/* ==========================================================
   تقرير النتائج
   ========================================================== */

function renderAnalysisReport() {
  if (!analysisReport || !analysisBadge) return;

  if (!hydraulicResults) {
    analysisBadge.textContent = "لم يُحسب بعد";
    analysisBadge.dataset.state = "idle";

    analysisReport.innerHTML =
      '<p class="muted">أكمل البيانات ثم اضغط «تحليل هيدروليكي».</p>';

    return;
  }

  const result = hydraulicResults;
  const water = result.water || getWaterProperties();

  const methodLabel = result.method === "hardyCross"
    ? "هاردي كروس (Hardy Cross)"
    : result.method === "newton"
      ? "نيوتن–رافسون المتزامن (Newton–Raphson)"
      : "التدرج العام الحقيقي (Global Gradient Algorithm — GGA)";

  const pumpRows = pipes.filter(pipe => pipe.isPump).map(pipe => {
    const pumpResult = result.pipeData.get(pipe.id);
    if (!pumpResult) return "";
    const curveSource = pipe.pumpMode === "catalog"
      ? "كتالوج: " + (pipe.pumpCompany || "شركة غير محددة") + " / " + (pipe.pumpModel || "موديل غير محدد") + " — " + fmt(pipe.pumpRpm, 0) + " RPM"
      : "افتراضي: H0=" + fmt(pipe.H0, 3) + " م، Qmax=" + fmt(pipe.Qmax, 3) + " لتر/ث";
    const rangeText = pumpResult.pumpRange
      ? fmt(pumpResult.pumpRange.min, 3) + " – " + fmt(pumpResult.pumpRange.max, 3) + " لتر/ث"
      : "--";
    return `<tr>
      <td>P${pipe.id}</td>
      <td>${escapeHTML(curveSource)}</td>
      <td dir="ltr">${fmt(Math.abs(pumpResult.q * 1000), 4)}</td>
      <td dir="ltr">${fmt(pumpResult.pumpHead, 5)}</td>
      <td dir="ltr">${rangeText}</td>
      <td>${escapeHTML(pumpResult.pumpStatus || "--")}</td>
    </tr>`;
  }).join("");
  const invalidPumpResults = pipes.filter(pipe => {
    if (!pipe.isPump || isPipeClosed(pipe)) return false;
    const pumpResult = result.pipeData.get(pipe.id);
    return !pumpResult || pumpResult.pumpOperatingPointValid === false;
  }).map(pipe => result.pipeData.get(pipe.id));
  const hasPumpRangeError = invalidPumpResults.some(item => item?.pumpRangeValid === false);
  const hasPumpDirectionError = invalidPumpResults.some(item => item?.pumpStatus === "عكس اتجاه المضخة");
  const pumpValidityText = result.pumpOperatingPointsValid === false
    ? (hasPumpRangeError && hasPumpDirectionError
        ? "غير صالح — توجد نقطة خارج مجال المنحنى وجريان عكسي في مضخة أخرى أو الأنبوب نفسه"
        : hasPumpRangeError
          ? "غير صالح — توجد نقطة تشغيل خارج مجال المنحنى؛ نتائج المضخة مؤقتة ولا تعتمد"
          : "غير صالح — اتجاه الجريان عكسي بالنسبة لاتجاه المضخة المعرف")
    : "ضمن المجال للمنحنيات المستخدمة أو لا توجد مضخة";

  const pumpSummarySection = pumpRows
    ? `<section class="analysis-section">
        <h3>نقاط تشغيل مضخات التقوية</h3>
        <div class="table-wrap">
          <table class="results-table">
            <thead><tr><th>الأنبوب</th><th>مصدر المنحنى</th><th>Q الفعلي (لتر/ث)</th><th>Hp (م)</th><th>مجال المنحنى</th><th>الحالة</th></tr></thead>
            <tbody>${pumpRows}</tbody>
          </table>
        </div>
        <p class="field-help">يُحسب Hp من منحنى H–Q أثناء الحل. عند خروج Q عن المجال، تُعرض نقطة تشغيل عددية مؤقتة مع وسمها بأنها غير صالحة للاعتماد.</p>
      </section>`
    : "";

  if (result.converged && result.pumpOperatingPointsValid !== false) {
    analysisBadge.textContent = "تحقق التقارب وصلاحية نطاق المضخة";
    analysisBadge.dataset.state = "success";
  } else if (result.converged) {
    analysisBadge.textContent = "تقارب عددي — تشغيل المضخة غير صالح";
    analysisBadge.dataset.state = "warning";
  } else {
    analysisBadge.textContent = "لم يتحقق التقارب العددي";
    analysisBadge.dataset.state = "warning";
  }

  const pipeRows = pipes.map(pipe => {
    const res = result.pipeData.get(pipe.id);
    if (!res) return "";

    const from = res.q >= 0
      ? nodeById(pipe.a)
      : nodeById(pipe.b);

    const to = res.q >= 0
      ? nodeById(pipe.b)
      : nodeById(pipe.a);

    const headA = result.nodeHeads.get(pipe.a);
    const headB = result.nodeHeads.get(pipe.b);

    const nodeA = nodeById(pipe.a);
    const nodeB = nodeById(pipe.b);

    const pressureHeadA =
      headA - Number(nodeA?.elevation || 0);

    const pressureHeadB =
      headB - Number(nodeB?.elevation || 0);

    const pressureA =
      pressureHeadA * water.density * GRAVITY / 100000;

    const pressureB =
      pressureHeadB * water.density * GRAVITY / 100000;

    const maxPressure = Math.max(pressureA, pressureB);
    const limit = pipe.pMaxBar;

    const isSafe = maxPressure <= limit;

    const statusHTML = isSafe
      ? '<span style="color:green;font-weight:bold;">ضمن الحد المدخل</span>'
      : '<span style="color:red;font-weight:bold;">تجاوز الحد المدخل</span>';

    const flowValue = Math.abs(res.q * 1000);
    const direction = res.isClosed
      ? "مغلق بواسطة المحبس"
      : flowValue <= 1e-10
        ? "لا يوجد جريان"
        : "من " + escapeHTML(from?.name || "--") +
          " إلى " + escapeHTML(to?.name || "--");

    const frictionText = Number.isFinite(res.frictionFactor)
      ? fmt(res.frictionFactor, 6)
      : "--";

    const pressureText =
      fmt(pressureA, 3) + " / " + fmt(pressureB, 3);
    const pumpHeadText = !pipe.isPump || res.isClosed
      ? "--"
      : res.pumpOperatingPointValid === false
        ? "مؤقت: " + fmt(res.pumpHead, 5)
        : fmt(res.pumpHead, 5);
    const netHeadlossText = res.isClosed
      ? "--"
      : pipe.isPump && res.pumpOperatingPointValid === false
        ? "مؤقت: " + fmt(res.headloss, 5)
        : fmt(res.headloss, 5);

    return `
      <tr>
        <td>P${pipe.id} ${pipe.isPump ? "(مضخة)" : ""}</td>
        <td>${direction}</td>
        <td dir="ltr">${fmt(flowValue, 4)}</td>
        <td dir="ltr">${fmt(res.velocity, 4)}</td>
        <td dir="ltr">${res.isClosed ? "--" : fmt(res.hf, 5)}</td>
        <td dir="ltr">${res.isClosed ? "--" : fmt(res.hm, 5)}</td>
        <td dir="ltr">${escapeHTML(pumpHeadText)}</td>
        <td>${pipe.isPump && !res.isClosed ? escapeHTML(res.pumpStatus) : "--"}</td>
        <td dir="ltr">${escapeHTML(netHeadlossText)}</td>
        <td dir="ltr">${pressureText}</td>
        <td>${statusHTML}</td>
        <td dir="ltr">${res.isClosed ? "--" : fmt(res.reynolds, 0)}</td>
        <td dir="ltr">${res.isClosed ? "--" : frictionText}</td>
        <td>${res.flowRegime}</td>
      </tr>`;
  }).join("");

  const nodeRows = nodes.map(node => {
    const head = result.nodeHeads.get(node.id);
    const relative = result.relativeHeadNodeIds.has(node.id);

    const pressureHead = head - Number(node.elevation || 0);

    const pressureBar = relative
      ? "غير مطلق"
      : fmt(
          pressureHead * water.density * GRAVITY / 100000,
          4
        );

    let sourceText = "--";

    if (node.type === "source" && node.sourceMode === "flow") {
      sourceText =
        fmt(node.sourceFlow, 4) + " (تصريف معلوم)";
    } else if (
      node.type === "source" &&
      node.sourceMode === "head"
    ) {
      const supply = result.fixedSourceFlows.get(node.id) || 0;

      sourceText =
        fmt(Math.abs(supply), 4) +
        (supply >= 0 ? " (تغذية)" : " (استقبال)");
    }

    return `
      <tr>
        <td>${escapeHTML(node.name)}</td>
        <td>${nodeTitles[node.type]}</td>
        <td dir="ltr">${fmt(head, 4)}</td>
        <td dir="ltr">${relative ? "نسبي" : fmt(pressureHead, 4)}</td>
        <td dir="ltr">${pressureBar}</td>
        <td dir="ltr">${sourceText}</td>
      </tr>`;
  }).join("");

  const warningsHTML = result.warnings.length
    ? `
      <div class="analysis-warnings">
        <strong>تنبيهات وملاحظات:</strong>
        <ul>
          ${result.warnings.map(warning =>
            "<li>" + escapeHTML(warning) + "</li>"
          ).join("")}
        </ul>
      </div>`
    : `
      <p class="field-help">
        لم تظهر تنبيهات وفق حدود الفحص الإرشادية المستخدمة.
        هذا لا يغني عن مراجعة معايير التصميم والتشغيل.
      </p>`;

  const loopDetailsSection =
    result.loopDetails?.length
      ? `
        <section class="analysis-section">
          <h3>تفاصيل الحلقات</h3>

          <div class="table-wrap">
            <table class="results-table">
              <thead>
                <tr>
                  <th>الحلقة</th>
                  <th>الاتجاه</th>
                  <th>الأنابيب وإشارات المسار</th>
                  <th>ΣhL المتبقي (م)</th>
                </tr>
              </thead>

              <tbody>
                ${result.loopDetails.map(loop => {
                  const residual = result.loopResiduals.find(item =>
                    item.loopId === loop.globalId
                  );

                  const badge = loop.orientation === "CW"
                    ? '<span class="loop-badge cw">مع عقارب الساعة ↻</span>'
                    : '<span class="loop-badge ccw">عكس عقارب الساعة ↺</span>';

                  return `
                    <tr>
                      <td>L${loop.globalId}</td>
                      <td>${badge}</td>
                      <td dir="ltr" style="font-size:11px;white-space:normal;">
                        ${loop.pipeLabels.join(" ")}
                      </td>
                      <td dir="ltr">${fmt(residual?.residual ?? 0, 8)}</td>
                    </tr>`;
                }).join("")}
              </tbody>
            </table>
          </div>
        </section>`
      : "";

  const warningsAndConvergence = `
    <section class="analysis-section">
      <h3>فحوص التقارب والاتزان</h3>

      <div class="field-help">
        <p>
          <strong>حالة التقارب:</strong>
          ${result.converged ? "تحقق ضمن حدود التقارب المحددة" : "لم يتحقق"}
        </p>

        <p>
          <strong>صلاحية نقطة تشغيل المضخة:</strong>
          ${escapeHTML(pumpValidityText)}
        </p>

        <p>
          <strong>أقصى خطأ استمرارية:</strong>
          ${fmt(result.maxContinuityLps, 8)} لتر/ث
        </p>

        <p>
          <strong>أقصى خطأ في معادلة الطاقة:</strong>
          ${fmt(result.maxHeadEquationResidual, 8)} م
        </p>

        <p>
          <strong>أقصى باقي للحلقات:</strong>
          ${fmt(result.maxLoopResidual, 8)} م
        </p>
      </div>

      ${warningsHTML}
    </section>`;

  analysisReport.innerHTML = `
    <section class="analysis-section">
      <h3>ملخص الحل</h3>

      <div class="field-help">
        <p><strong>الطريقة:</strong> ${methodLabel}</p>

        <p>
          <strong>درجة حرارة الماء:</strong>
          ${fmt(water.temperature, 2)} °C
        </p>

        <p>
          <strong>كثافة الماء:</strong>
          ${fmt(water.density, 3)} kg/m³
        </p>

        <p>
          <strong>اللزوجة الديناميكية:</strong>
          ${fmt(water.dynamicViscosity * 1000, 5)} mPa·s
        </p>

        <p>
          <strong>اللزوجة الحركية:</strong>
          ${water.kinematicViscosity.toExponential(5)} m²/s
        </p>

        <p><strong>التكرارات الخارجية:</strong> ${result.iterations}</p>
        ${result.method === "globalGradient" ? `<p><strong>تكرارات PCG الداخلية:</strong> ${result.linearIterations}</p>` : ""}
        <p><strong>عدد مكونات الشبكة:</strong> ${result.componentCount}</p>
        <p><strong>عدد الحلقات:</strong> ${result.loopCount}</p>
      </div>
    </section>

    ${pumpSummarySection}

    <section class="analysis-section">
      <h3>نتائج الأنابيب</h3>

      <div class="table-wrap">
        <table class="results-table">
          <thead>
            <tr>
              <th>الأنبوب</th>
              <th>الاتجاه الفعلي</th>
              <th>التصريف (لتر/ث)</th>
              <th>السرعة (م/ث)</th>
              <th>فقد الاحتكاك hf (م)</th>
              <th>الفقد الموضعي hm (م)</th>
              <th>رفع المضخة Hp (م)</th>
              <th>حالة مجال المنحنى</th>
              <th>صافي الفقد الموقّع (م)</th>
              <th>الضغط عند الطرفين (بار)</th>
              <th>حد الضغط المدخل</th>
              <th>Re</th>
              <th>Darcy f</th>
              <th>نوع الجريان</th>
            </tr>
          </thead>

          <tbody>${pipeRows}</tbody>
        </table>
      </div>

      <p class="field-help">
        صافي الفقد الموقّع يساوي فقد الاحتكاك والفقد الموضعي
        مطروحاً منه رفع المضخة عندما تعمل في اتجاهها المعتمد.
        وقد تكون قيمته سالبة في الأنبوب الذي يحتوي على مضخة.
      </p>
    </section>

    <section class="analysis-section">
      <h3>نتائج العقد</h3>

      <div class="table-wrap">
        <table class="results-table">
          <thead>
            <tr>
              <th>العقدة</th>
              <th>النوع</th>
              <th>الحمل H (م)</th>
              <th>ضغط القياس (م ماء)</th>
              <th>الضغط (بار)</th>
              <th>تصريف المصدر</th>
            </tr>
          </thead>

          <tbody>${nodeRows}</tbody>
        </table>
      </div>
    </section>

    ${loopDetailsSection}

    ${warningsAndConvergence}
  `;
}

/* ==========================================================
   تنزيل الملفات واستيراد المشروع
   ========================================================== */

function downloadTextFile(filename, content, mimeType) {
  const blob = new Blob([content], { type: mimeType });
  const url = URL.createObjectURL(blob);

  const link = document.createElement("a");
  link.href = url;
  link.download = filename;

  document.body.appendChild(link);
  link.click();
  link.remove();

  URL.revokeObjectURL(url);
}

function saveProjectFile() {
  const project = {
    format: "WaterNetworkLab",
    version: 4,
    exportedAt: new Date().toISOString(),
    nodes,
    pipes,
    nextNodeId,
    nextPipeId
  };

  downloadTextFile(
    "water-network-project.json",
    JSON.stringify(project, null, 2),
    "application/json;charset=utf-8"
  );

  setStatus("تم إعداد ملف المشروع بصيغة JSON.");
}

function loadProjectFile() {
  const input = document.createElement("input");

  input.type = "file";
  input.accept = ".json,application/json";

  input.addEventListener("change", async () => {
    const file = input.files?.[0];
    if (!file) return;

    try {
      const text = await file.text();
      const data = JSON.parse(text);

      if (!Array.isArray(data.nodes) || !Array.isArray(data.pipes)) {
        throw new Error("الملف لا يحتوي على بيانات مشروع صحيحة.");
      }

      // احفظ الحالة الحالية حتى يمكن التراجع عن الاستيراد.
      saveHistory();

      restoreNetworkState(data);

      historyStack = [];
      saveNetwork();
      render();

      setStatus("تم تحميل المشروع بنجاح.");
    } catch (error) {
      setStatus("تعذر تحميل المشروع: " + error.message);
    }
  });

  input.click();
}

function csvSafe(value) {
  let text = String(value ?? "");

  // حماية أولية من تفسير محتوى الخلية كصيغة في برامج الجداول.
  if (/^[=+\-@]/.test(text)) {
    text = "'" + text;
  }

  return '"' + text.replace(/"/g, '""') + '"';
}

function exportResultsCSV() {
  if (!hydraulicResults) {
    setStatus("نفّذ التحليل أولاً قبل تصدير النتائج.");
    return;
  }

  const rows = [];

  rows.push([
    "الأنبوب",
    "من",
    "إلى",
    "Q_L_s",
    "V_m_s",
    "hf_m",
    "hm_m",
    "net_headloss_m",
    "Reynolds",
    "Darcy_f",
    "Flow_regime",
    "Pump_head_m",
    "Pump_curve_mode",
    "Pump_curve_range_valid",
    "Pump_company",
    "Pump_model",
    "Pump_RPM"
  ]);

  pipes.forEach(pipe => {
    const result = hydraulicResults.pipeData.get(pipe.id);
    if (!result) return;

    const from = result.q >= 0
      ? nodeById(pipe.a)
      : nodeById(pipe.b);

    const to = result.q >= 0
      ? nodeById(pipe.b)
      : nodeById(pipe.a);

    rows.push([
      "P" + pipe.id,
      from?.name || "",
      to?.name || "",
      result.isClosed ? 0 : Math.abs(result.q * 1000),
      result.isClosed ? "" : result.velocity,
      result.isClosed ? "" : result.hf,
      result.isClosed ? "" : result.hm,
      result.isClosed ? "" : result.headloss,
      result.isClosed ? "" : result.reynolds,
      Number.isFinite(result.frictionFactor)
        ? result.frictionFactor
        : "",
      result.flowRegime,
      result.pumpHead,
      pipe.isPump ? pipe.pumpMode : "",
      pipe.isPump ? (result.pumpRangeValid ? "within-range" : "out-of-range-or-reverse") : "",
      pipe.isPump ? pipe.pumpCompany : "",
      pipe.isPump ? pipe.pumpModel : "",
      pipe.isPump ? pipe.pumpRpm : ""
    ]);
  });

  rows.push([]);
  rows.push([
    "العقدة",
    "النوع",
    "الحمل_m",
    "منسوب_العقدة_m",
    "ضغط_القياس_m"
  ]);

  nodes.forEach(node => {
    const head = hydraulicResults.nodeHeads.get(node.id);
    const pressureHead = head - node.elevation;

    rows.push([
      node.name,
      nodeTitles[node.type],
      head,
      node.elevation,
      hydraulicResults.relativeHeadNodeIds.has(node.id)
        ? "نسبي"
        : pressureHead
    ]);
  });

  const csv = "\uFEFF" +
    rows.map(row => row.map(csvSafe).join(",")).join("\r\n");

  downloadTextFile(
    "water-network-results.csv",
    csv,
    "text/csv;charset=utf-8"
  );

  setStatus("تم تصدير نتائج الشبكة بصيغة CSV.");
}

/* ==========================================================
   تطبيق خشونة المادة على الأنبوب المحدد
   ========================================================== */

function applyMaterialToSelectedPipe() {
  if (!selected || selected.type !== "pipe") {
    setStatus("حدد أنبوباً أولاً لتطبيق خشونة المادة عليه.");
    return;
  }

  const pipe = pipeById(selected.id);
  if (!pipe) return;

  const roughness = materialRoughnessInput
    ? Number(materialRoughnessInput.value)
    : NaN;

  if (!Number.isFinite(roughness) || roughness < 0) {
    setStatus("قيمة الخشونة المطلقة يجب أن تكون صفراً أو أكبر.");
    return;
  }

  saveHistory();

  pipe.eps = roughness;

  invalidateHydraulics();
  saveNetwork();
  render();

  setStatus(
    "تم تطبيق الخشونة " + roughness +
    " م على الأنبوب P" + pipe.id + "."
  );
}

/* ==========================================================
   تنفيذ التحليل بالطريقة المختارة
   ========================================================== */

function runHydraulicAnalysis() {
  const method = solverMethodSelect?.value || "globalGradient";

  let result;
  if (method === "hardyCross") {
    result = solveHydraulicsHardyCross();
  } else if (method === "newton") {
    result = solveHydraulicsNewton();
  } else {
    // globalGradient هو المحلل الثالث المستقل، وليس اسمًا للمحلل القديم.
    result = solveHydraulicsGGA();
  }

  result.pumpOperatingPointsValid = pipes.every(pipe => {
    if (!pipe.isPump || isPipeClosed(pipe)) return true;
    const pipeResult = result.pipeData.get(pipe.id);
    return !!pipeResult && pipeResult.pumpOperatingPointValid !== false;
  });

  hydraulicResults = result;
  render();

  if (result.converged && result.pumpOperatingPointsValid) {
    setStatus("اكتمل التحليل وتحققت شروط التقارب، وجميع نقاط تشغيل المضخات ضمن مجالات منحنياتها.");
  } else if (result.converged) {
    const hasOutOfRangePump = pipes.some(pipe => {
      const item = result.pipeData.get(pipe.id);
      return pipe.isPump && !isPipeClosed(pipe) && item?.pumpRangeValid === false;
    });
    const hasReversePumpFlow = pipes.some(pipe => {
      const item = result.pipeData.get(pipe.id);
      return pipe.isPump && !isPipeClosed(pipe) && item?.pumpStatus === "عكس اتجاه المضخة";
    });
    if (hasOutOfRangePump) {
      setStatus("تحقق التقارب العددي، لكن توجد مضخة تعمل خارج مجال منحناها؛ نتائج الرفع وصافي الفقد في هذا الأنبوب مؤقتة ولا تعتمد.");
    } else if (hasReversePumpFlow) {
      setStatus("تحقق التقارب العددي، لكن يوجد جريان عكسي بالنسبة لاتجاه مضخة تقوية؛ راجع اتجاه تركيب المضخة وصمام عدم الرجوع.");
    } else {
      setStatus("تحقق التقارب العددي، لكن إحدى نقاط تشغيل المضخات غير صالحة؛ راجع تنبيهات التقرير.");
    }
  } else {
    setStatus("أعيدت نتائج عددية، لكن شروط التقارب لم تتحقق؛ لا تعتمد النتائج قبل مراجعة التنبيهات.");
  }

  return result;
}

/* ==========================================================
   أحداث الواجهة والتفاعل
   ========================================================== */

setButtonAction(buttons.source, () => addNode("source"));
setButtonAction(buttons.junction, () => addNode("junction"));
setButtonAction(buttons.demand, () => addNode("demand"));
setButtonAction(buttons.undo, undoAction);

setButtonAction(buttons.connect, () => {
  if (mode === "connect") {
    mode = "select";
    firstNodeId = null;
    setStatus("تم إلغاء وضع التوصيل.");
  } else {
    mode = "connect";
    firstNodeId = null;
    setStatus("اضغط العقدة الأولى ثم العقدة الثانية.");
  }

  render();
});

setButtonAction(buttons.calculate, () => {
  try {
    invalidateHydraulics();
    runHydraulicAnalysis();
  } catch (error) {
    invalidateHydraulics();
    render();
    setStatus("تعذر التحليل: " + (error.message || "خطأ غير معروف"));
  }
});

setButtonAction(buttons.delete, () => {
  if (!selected) {
    setStatus("حدد عقدة أو أنبوباً أولاً.");
    return;
  }

  if (selected.type === "node") {
    const id = Number(selected.id);
    const node = nodeById(id);

    const confirmed = confirm(
      "حذف العقدة «" + (node?.name || "") +
      "» والأنابيب المرتبطة بها؟"
    );

    if (!confirmed) return;

    saveHistory();

    nodes = nodes.filter(item => item.id !== id);
    pipes = pipes.filter(pipe =>
      pipe.a !== id && pipe.b !== id
    );
  } else {
    const id = Number(selected.id);
    saveHistory();
    pipes = pipes.filter(pipe => pipe.id !== id);
  }

  selected = null;
  firstNodeId = null;
  mode = "select";

  invalidateHydraulics();
  saveNetwork();
  render();

  setStatus("تم حذف العنصر المحدد.");
});

setButtonAction(buttons.clear, () => {
  if (!confirm("هل تريد حذف جميع العقد والأنابيب؟")) return;

  saveHistory();

  nodes = [];
  pipes = [];
  nextNodeId = 1;
  nextPipeId = 1;

  mode = "select";
  firstNodeId = null;
  selected = null;

  draggingNodeId = null;
  pointerStart = null;
  dragMoved = false;
  dragHistorySaved = false;
  suppressClick = false;

  invalidateHydraulics();
  saveNetwork();
  render();

  setStatus("تم تفريغ مساحة العمل.");
});

setButtonAction(buttons.saveProject, saveProjectFile);
setButtonAction(buttons.loadProject, loadProjectFile);
setButtonAction(buttons.exportProject, exportResultsCSV);
setButtonAction(buttons.applyMaterial, applyMaterialToSelectedPipe);

/* ==========================================================
   تحديث التحليل عند تغيير درجة حرارة الماء
   ========================================================== */

if (waterTempInput) {
  waterTempInput.addEventListener("change", () => {
    try {
      const properties = getWaterProperties();

      if (hydraulicResults) {
        runHydraulicAnalysis();
      } else {
        setStatus(
          "تم تحديث خواص الماء عند " +
          fmt(properties.temperature, 1) + " °C. أجرِ التحليل."
        );
      }
    } catch (error) {
      invalidateHydraulics();
      render();
      setStatus(error.message);
    }
  });
}

/* ==========================================================
   اختيار العقد والأنابيب من الرسم
   ========================================================== */

if (svg) {
  svg.addEventListener("click", event => {
    if (suppressClick) {
      suppressClick = false;
      return;
    }

    const nodeElement = event.target.closest?.(".node");

    if (nodeElement && svg.contains(nodeElement)) {
      const id = Number(nodeElement.dataset.nodeId);

      if (mode === "connect") {
        handleConnectClick(id);
      } else if (
        draggingNodeId === null &&
        !dragMoved
      ) {
        selectNode(id);
        setStatus("تم تحديد العقدة.");
      }

      return;
    }

    const pipeElement = event.target.closest?.(".pipe");

    if (pipeElement && svg.contains(pipeElement)) {
      if (mode === "connect") {
        setStatus("في وضع التوصيل اختر عقدتين.");
        return;
      }

      selectPipe(Number(pipeElement.dataset.pipeId));
      setStatus("تم تحديد الأنبوب.");
    }
  });

  /* ========================================================
     سحب العقد مع حفظ الحالة السابقة قبل أول حركة
     ======================================================== */

  svg.addEventListener("pointerdown", event => {
    if (mode !== "select") return;

    const nodeElement = event.target.closest?.(".node");
    if (!nodeElement || !svg.contains(nodeElement)) return;

    const id = Number(nodeElement.dataset.nodeId);
    const node = nodeById(id);
    if (!node) return;

    draggingNodeId = id;

    const point = screenToSvg(event);

    pointerStart = {
      x: point.x - node.x,
      y: point.y - node.y
    };

    dragMoved = false;
    dragHistorySaved = false;
    selected = { type: "node", id };

    render();

    try {
      svg.setPointerCapture(event.pointerId);
    } catch (_) {}

    event.preventDefault();
  });

  svg.addEventListener("pointermove", event => {
    if (draggingNodeId === null || !pointerStart) return;

    const node = nodeById(draggingNodeId);
    if (!node) return;

    const point = screenToSvg(event);
    const newX = point.x - pointerStart.x;
    const newY = point.y - pointerStart.y;

    if (
      !dragMoved &&
      Math.hypot(newX - node.x, newY - node.y) < 2
    ) {
      return;
    }

    if (!dragHistorySaved) {
      saveHistory();
      dragHistorySaved = true;
    }

    dragMoved = true;

    node.x = Math.max(20, Math.min(780, newX));
    node.y = Math.max(20, Math.min(480, newY));

    render();
    event.preventDefault();
  });

  function finishDrag() {
    if (draggingNodeId === null) return;

    if (dragMoved) {
      saveNetwork();
      suppressClick = true;
      setStatus("تم تحريك العقدة.");
    }

    draggingNodeId = null;
    pointerStart = null;
    dragMoved = false;
    dragHistorySaved = false;

    render();
  }

  svg.addEventListener("pointerup", finishDrag);
  svg.addEventListener("pointercancel", finishDrag);
}

/* ==========================================================
   بدء التشغيل
   ========================================================== */

loadNetwork();
render();

if (nodes.length || pipes.length) {
  setStatus("تم تحميل بيانات الشبكة المحفوظة.");
}