// ==UserScript==
// @name         Elevn – FPL assistant
// @description  Elevn, your Fantasy Premier League assistant: squad, transfers, captain, chips, leagues, news.
// @version      3.71.0
// @match        https://fantasy.premierleague.com/*
// @run-at       document-idle
// @noframes
// @grant        GM.xmlHttpRequest
// @grant        GM_xmlhttpRequest
// @connect      footballapi.pulselive.com
// @connect      *
// @connect      raw.githubusercontent.com
// @homepageURL  https://github.com/Ragxonal/elevn
// @updateURL    https://raw.githubusercontent.com/Ragxonal/elevn/main/dist/Elevn.user.js
// @downloadURL  https://raw.githubusercontent.com/Ragxonal/elevn/main/dist/Elevn.user.js
// ==/UserScript==
(function () {
if (window.__fplA) return; window.__fplA = 1;
// Stand-in for the Chrome extension API (no extension id, so alerts use in-panel toasts)
const chrome = { runtime: { sendMessage() {}, onMessage: { addListener() {} } } };
const runFplAnalyst = async () => {
  const ELEVN_VER = '3.71';
  // v3.45: exact squad optimiser (javascript-lp-solver 1.0.3, Unlicense). Built in, created on first use.
  let LPS_ = null; const LPS = () => LPS_ || (LPS_ = (function () {
var solver = (function () {
    'use strict';

    /**
     * Represents a solution to a linear programming problem.
     */
    class Solution {
        constructor(tableau, evaluation, feasible, bounded) {
            this.feasible = feasible;
            this.evaluation = evaluation;
            this.bounded = bounded;
            this._tableau = tableau;
            this.solutionSet = {};
        }
        /**
         * Generate the solution set mapping variable IDs to their values.
         */
        generateSolutionSet() {
            const solutionSet = {};
            const tableau = this._tableau;
            const varIndexByRow = tableau.varIndexByRow;
            const variablesPerIndex = tableau.variablesPerIndex;
            const matrix = tableau.matrix;
            const width = tableau.width;
            const rhsColumn = tableau.rhsColumn;
            const lastRow = tableau.height - 1;
            const roundingCoeff = Math.round(1 / tableau.precision);
            for (let r = 1; r <= lastRow; r += 1) {
                const varIndex = varIndexByRow[r];
                const variable = variablesPerIndex[varIndex];
                if (variable === undefined || variable.isSlack === true) {
                    continue;
                }
                const varValue = matrix[r * width + rhsColumn];
                solutionSet[variable.id] =
                    Math.round((Number.EPSILON + varValue) * roundingCoeff) / roundingCoeff;
            }
            return solutionSet;
        }
    }
    /**
     * Represents a solution to a mixed-integer programming problem.
     * Extends Solution with branch-and-cut iteration tracking.
     */
    class MilpSolution extends Solution {
        constructor(tableau, evaluation, feasible, bounded, branchAndCutIterations) {
            super(tableau, evaluation, feasible, bounded);
            this.iter = branchAndCutIterations;
        }
    }

    class BranchMinHeap {
        constructor(initialCapacity = 64) {
            this.heap = new Array(initialCapacity);
            this.size = 0;
            this.seqCounter = 0;
            this.pool = new Array(64);
            this.poolSize = 0;
        }
        allocEntry(branch, seq) {
            if (this.poolSize > 0) {
                const entry = this.pool[--this.poolSize];
                entry.branch = branch;
                entry.seq = seq;
                return entry;
            }
            return { branch, seq };
        }
        freeEntry(entry) {
            if (this.poolSize < 256) {
                this.pool[this.poolSize++] = entry;
            }
        }
        get length() {
            return this.size;
        }
        isEmpty() {
            return this.size === 0;
        }
        clear() {
            this.size = 0;
            this.seqCounter = 0;
        }
        // Compare: returns true if a should be before b (a has higher priority)
        isBefore(a, b) {
            if (a.branch.relaxedEvaluation !== b.branch.relaxedEvaluation) {
                return a.branch.relaxedEvaluation < b.branch.relaxedEvaluation;
            }
            // LIFO tie-breaking: higher seq (more recent) comes first
            return a.seq > b.seq;
        }
        push(branch) {
            const heap = this.heap;
            let idx = this.size;
            this.size++;
            // Grow if needed
            if (idx >= heap.length) {
                heap.length = heap.length * 2;
            }
            const entry = this.allocEntry(branch, this.seqCounter++);
            // Bubble up
            while (idx > 0) {
                const parentIdx = (idx - 1) >> 1;
                const parent = heap[parentIdx];
                if (!this.isBefore(entry, parent)) {
                    break;
                }
                heap[idx] = parent;
                idx = parentIdx;
            }
            heap[idx] = entry;
        }
        pop() {
            if (this.size === 0) {
                return undefined;
            }
            const heap = this.heap;
            const poppedEntry = heap[0];
            const result = poppedEntry.branch;
            this.size--;
            // Return entry to pool
            this.freeEntry(poppedEntry);
            if (this.size === 0) {
                return result;
            }
            // Move last element to root and bubble down
            const last = heap[this.size];
            let idx = 0;
            const halfSize = this.size >> 1;
            while (idx < halfSize) {
                let childIdx = (idx << 1) + 1;
                let child = heap[childIdx];
                const rightIdx = childIdx + 1;
                if (rightIdx < this.size && this.isBefore(heap[rightIdx], child)) {
                    childIdx = rightIdx;
                    child = heap[rightIdx];
                }
                if (!this.isBefore(child, last)) {
                    break;
                }
                heap[idx] = child;
                idx = childIdx;
            }
            heap[idx] = last;
            return result;
        }
        peek() {
            return this.size > 0 ? this.heap[0].branch : undefined;
        }
    }

    function createCut$2(type, varIndex, value) {
        return { type, varIndex, value };
    }
    function createBranch$2(relaxedEvaluation, cuts) {
        return { relaxedEvaluation, cuts };
    }
    function createBranchAndCutService() {
        const applyCuts = (tableau, branchingCuts) => {
            var _a;
            tableau.restore();
            tableau.addCutConstraints(branchingCuts);
            tableau.simplex();
            if ((_a = tableau.model) === null || _a === void 0 ? void 0 : _a.useMIRCuts) {
                // Optimization: reuse previous "after" as next "before" to avoid redundant computation
                let fractionalVolume = tableau.computeFractionalVolume(true);
                while (fractionalVolume > 0) {
                    tableau.applyMIRCuts();
                    tableau.simplex();
                    const fractionalVolumeAfter = tableau.computeFractionalVolume(true);
                    if (fractionalVolumeAfter >= 0.9 * fractionalVolume) {
                        break;
                    }
                    fractionalVolume = fractionalVolumeAfter;
                }
            }
        };
        const branchAndCut = (tableau) => {
            var _a, _b, _c, _d, _e;
            const branches = new BranchMinHeap();
            let iterations = 0;
            const tolerance = (_b = (_a = tableau.model) === null || _a === void 0 ? void 0 : _a.tolerance) !== null && _b !== void 0 ? _b : 0;
            let toleranceFlag = true;
            let terminalTime = 1e99;
            if ((_c = tableau.model) === null || _c === void 0 ? void 0 : _c.timeout) {
                terminalTime = Date.now() + tableau.model.timeout;
            }
            let bestEvaluation = Infinity;
            let bestBranch = null;
            const bestOptionalObjectivesEvaluations = [];
            // Cache optionalObjectives reference to avoid repeated property lookups in hot loop
            const optionalObjectives = tableau.optionalObjectives;
            const nOptionalObjectives = optionalObjectives.length;
            for (let oInit = 0; oInit < nOptionalObjectives; oInit += 1) {
                bestOptionalObjectivesEvaluations.push(Infinity);
            }
            const branch = createBranch$2(-Infinity, []);
            let acceptableThreshold;
            branches.push(branch);
            while (!branches.isEmpty() && toleranceFlag === true && Date.now() < terminalTime) {
                if ((_d = tableau.model) === null || _d === void 0 ? void 0 : _d.isMinimization) {
                    acceptableThreshold = tableau.bestPossibleEval * (1 + tolerance);
                }
                else {
                    acceptableThreshold = tableau.bestPossibleEval * (1 - tolerance);
                }
                if (tolerance > 0) {
                    if (bestEvaluation < acceptableThreshold) {
                        toleranceFlag = false;
                    }
                }
                const activeBranch = branches.pop();
                if (activeBranch.relaxedEvaluation >= bestEvaluation) {
                    continue;
                }
                const cuts = activeBranch.cuts;
                applyCuts(tableau, cuts);
                iterations++;
                if (tableau.feasible === false) {
                    continue;
                }
                const evaluation = tableau.evaluation;
                if (evaluation > bestEvaluation) {
                    continue;
                }
                if (evaluation === bestEvaluation) {
                    let isCurrentEvaluationWorse = true;
                    for (let o = 0; o < nOptionalObjectives; o += 1) {
                        const currentCost = optionalObjectives[o].reducedCosts[0];
                        const bestCost = bestOptionalObjectivesEvaluations[o];
                        if (currentCost > bestCost) {
                            break;
                        }
                        else if (currentCost < bestCost) {
                            isCurrentEvaluationWorse = false;
                            break;
                        }
                    }
                    if (isCurrentEvaluationWorse) {
                        continue;
                    }
                }
                if (tableau.isIntegral() === true) {
                    tableau.__isIntegral = true;
                    if (iterations === 1) {
                        tableau.branchAndCutIterations = iterations;
                        return;
                    }
                    bestBranch = activeBranch;
                    bestEvaluation = evaluation;
                    for (let oCopy = 0; oCopy < nOptionalObjectives; oCopy += 1) {
                        bestOptionalObjectivesEvaluations[oCopy] =
                            optionalObjectives[oCopy].reducedCosts[0];
                    }
                    if ((_e = tableau.model) === null || _e === void 0 ? void 0 : _e.keep_solutions) {
                        const nowSolution = tableau.model.tableau.getSolution();
                        const store = nowSolution.generateSolutionSet();
                        store.result = nowSolution.evaluation;
                        if (!tableau.model.solutions) {
                            tableau.model.solutions = [];
                        }
                        tableau.model.solutions.push(store);
                    }
                }
                else {
                    if (iterations === 1) {
                        tableau.save();
                    }
                    const variable = tableau.getMostFractionalVar();
                    const varIndex = variable.index;
                    const varValue = variable.value;
                    const cutsHigh = [];
                    const cutsLow = [];
                    const nCuts = cuts.length;
                    for (let c = 0; c < nCuts; c += 1) {
                        const cut = cuts[c];
                        if (cut.varIndex === varIndex) {
                            if (cut.type === "min") {
                                cutsLow.push(cut);
                            }
                            else {
                                cutsHigh.push(cut);
                            }
                        }
                        else {
                            cutsHigh.push(cut);
                            cutsLow.push(cut);
                        }
                    }
                    const cutHigh = createCut$2("min", varIndex, Math.ceil(varValue));
                    cutsHigh.push(cutHigh);
                    const cutLow = createCut$2("max", varIndex, Math.floor(varValue));
                    cutsLow.push(cutLow);
                    branches.push(createBranch$2(evaluation, cutsHigh));
                    branches.push(createBranch$2(evaluation, cutsLow));
                }
            }
            if (bestBranch !== null) {
                applyCuts(tableau, bestBranch.cuts);
            }
            tableau.branchAndCutIterations = iterations;
        };
        return { applyCuts, branchAndCut };
    }

    /**
     * Optimized cycle detector using hash-based O(1) lookup.
     * The original checkForCycles was O(n²) - comparing every pair against all others.
     * This version uses a Map to track where each (leaving,entering) pair occurred,
     * making duplicate detection O(1) average case.
     */
    class CycleDetector {
        constructor() {
            this.pairs = [];
            this.positions = new Map();
        }
        add(leaving, entering) {
            const key = `${leaving}_${entering}`;
            const pos = this.pairs.length;
            this.pairs.push([leaving, entering]);
            const prevPositions = this.positions.get(key);
            if (prevPositions === undefined) {
                this.positions.set(key, [pos]);
                return [];
            }
            // Check if any previous occurrence starts a repeating cycle
            for (const startPos of prevPositions) {
                const cycleLength = pos - startPos;
                // Need at least cycleLength more elements to verify
                if (cycleLength > this.pairs.length - pos) {
                    continue;
                }
                let cycleFound = true;
                for (let i = 1; i < cycleLength && startPos + cycleLength + i < this.pairs.length; i++) {
                    const p1 = this.pairs[startPos + i];
                    const p2 = this.pairs[startPos + cycleLength + i];
                    if (p1[0] !== p2[0] || p1[1] !== p2[1]) {
                        cycleFound = false;
                        break;
                    }
                }
                if (cycleFound) {
                    return [startPos, cycleLength];
                }
            }
            prevPositions.push(pos);
            return [];
        }
    }
    function simplex() {
        this.bounded = true;
        this.phase1();
        if (this.feasible === true) {
            this.phase2();
        }
        return this;
    }
    /**
     * Dual simplex algorithm for warm-starting after adding constraints.
     *
     * Use when: The current solution is dual feasible (reduced costs valid) but
     * may be primal infeasible (some RHS values negative). This is common after
     * adding bound constraints in branch-and-cut.
     *
     * Algorithm:
     * 1. Find a basic variable with negative value (leaving variable)
     * 2. Find entering variable using dual ratio test
     * 3. Pivot to restore primal feasibility
     * 4. Repeat until all basic variables are non-negative
     *
     * @returns Number of iterations, or -1 if dual infeasible
     */
    function dualSimplex() {
        const matrix = this.matrix;
        const width = this.width;
        const rhsColumn = this.rhsColumn;
        const lastColumn = width - 1;
        const lastRow = this.height - 1;
        const precision = this.precision;
        const negPrecision = -precision;
        let iterations = 0;
        const maxIterations = 10000; // Safety limit
        while (iterations < maxIterations) {
            // Step 1: Find leaving variable (row with most negative RHS)
            let leavingRow = 0;
            let minRHS = negPrecision;
            for (let r = 1; r <= lastRow; r++) {
                const rhsValue = matrix[r * width + rhsColumn];
                if (rhsValue < minRHS) {
                    minRHS = rhsValue;
                    leavingRow = r;
                }
            }
            // If no negative RHS, we're primal feasible - done!
            if (leavingRow === 0) {
                this.feasible = true;
                this.setEvaluation();
                return iterations;
            }
            // Step 2: Find entering variable using dual ratio test
            // For each non-basic variable j with a_ij < 0 (negative coefficient in leaving row),
            // compute ratio = reduced_cost[j] / |a_ij|
            // Choose the one with minimum ratio (to maintain dual feasibility)
            let enteringColumn = 0;
            let minRatio = Infinity;
            const leavingRowOffset = leavingRow * width;
            for (let c = 1; c <= lastColumn; c++) {
                const coefficient = matrix[leavingRowOffset + c];
                // Only consider columns with negative coefficient in leaving row
                if (coefficient < negPrecision) {
                    // Reduced cost is in row 0 (cost row)
                    const reducedCost = matrix[c];
                    // For minimization, reduced costs should be >= 0 for optimality
                    // Ratio test: reducedCost / |coefficient|
                    if (reducedCost >= negPrecision) {
                        const ratio = reducedCost / -coefficient;
                        if (ratio < minRatio) {
                            minRatio = ratio;
                            enteringColumn = c;
                        }
                    }
                }
            }
            // If no entering column found, the problem is dual infeasible (primal unbounded)
            if (enteringColumn === 0) {
                this.feasible = false;
                return -1;
            }
            // Step 3: Pivot
            this.pivot(leavingRow, enteringColumn);
            iterations++;
        }
        // Hit iteration limit - something went wrong
        this.feasible = false;
        return iterations;
    }
    function phase1() {
        const debugCheckForCycles = this.model.checkForCycles;
        const cycleDetector = debugCheckForCycles ? new CycleDetector() : null;
        const matrix = this.matrix;
        const width = this.width;
        const rhsColumn = this.rhsColumn;
        const lastColumn = this.width - 1;
        const lastRow = this.height - 1;
        const precision = this.precision;
        const negPrecision = -precision;
        // Cache arrays for faster access in hot loops
        const unrestrictedVars = this.unrestrictedVars;
        const varIndexByRow = this.varIndexByRow;
        const varIndexByCol = this.varIndexByCol;
        // Anti-cycling: on degenerate problems, the max-quotient pivot rule
        // can oscillate, corrupting the matrix. We detect stalling early
        // (after SAVE_THRESHOLD iterations without RHS improvement) and save
        // the matrix state. If still stuck after maxQuotientLimit iterations,
        // we restore the clean matrix and switch to Bland's rule. The lazy
        // save avoids the copy cost on the vast majority of phase1 calls
        // that converge quickly.
        const SAVE_THRESHOLD = 10;
        const maxQuotientLimit = Math.max(lastRow, lastColumn);
        let iterations = 0;
        let useBland = false;
        let initialRHS = -Infinity;
        let savedMatrix = null;
        let savedVarIndexByRow = null;
        let savedVarIndexByCol = null;
        let savedRowByVarIndex = null;
        let savedColByVarIndex = null;
        while (true) {
            // Find leaving row (most negative RHS among restricted basic vars).
            // Unrestricted variables can validly have negative values, so rows
            // where the basic variable is unrestricted are not infeasible.
            let leavingRowIndex = 0;
            let rhsValue = negPrecision;
            for (let r = 1; r <= lastRow; r++) {
                if (unrestrictedVars[varIndexByRow[r]] === true)
                    continue;
                const value = matrix[r * width + rhsColumn];
                if (value < rhsValue) {
                    rhsValue = value;
                    leavingRowIndex = r;
                }
            }
            if (leavingRowIndex === 0) {
                this.feasible = true;
                return iterations;
            }
            // Detect non-convergence and apply anti-cycling.
            if (!useBland && iterations > 0 && rhsValue <= initialRHS) {
                if (iterations >= SAVE_THRESHOLD && savedMatrix === null) {
                    // Stalling detected: save matrix for potential rollback
                    savedMatrix = matrix.slice();
                    savedVarIndexByRow = varIndexByRow.slice();
                    savedVarIndexByCol = varIndexByCol.slice();
                    savedRowByVarIndex = this.rowByVarIndex.slice();
                    savedColByVarIndex = this.colByVarIndex.slice();
                }
                if (iterations >= maxQuotientLimit) {
                    // Still stuck after generous budget: restore and switch
                    useBland = true;
                    if (savedMatrix) {
                        matrix.set(savedMatrix);
                        for (let i = 0; i < savedVarIndexByRow.length; i++) {
                            varIndexByRow[i] = savedVarIndexByRow[i];
                        }
                        for (let i = 0; i < savedVarIndexByCol.length; i++) {
                            varIndexByCol[i] = savedVarIndexByCol[i];
                        }
                        for (let i = 0; i < savedRowByVarIndex.length; i++) {
                            this.rowByVarIndex[i] = savedRowByVarIndex[i];
                        }
                        for (let i = 0; i < savedColByVarIndex.length; i++) {
                            this.colByVarIndex[i] = savedColByVarIndex[i];
                        }
                        iterations = 0;
                        continue;
                    }
                }
            }
            if (iterations === 0) {
                initialRHS = rhsValue;
            }
            // Find entering column.
            // Prefer columns with negative coefficient in leaving row (these directly
            // fix the infeasibility by making RHS positive after pivot).
            // Only fall back to unrestricted variables with positive coefficient when
            // no negative coefficient column exists - this "swaps" the infeasibility
            // to an unrestricted variable (which is allowed to be negative).
            let enteringColumn = 0;
            const leavingRowOffset = leavingRowIndex * width;
            if (useBland) {
                // Bland's rule: pick the first eligible column (smallest index).
                // First pass: negative coefficients only (directly fix infeasibility)
                for (let c = 1; c <= lastColumn; c++) {
                    const coefficient = matrix[leavingRowOffset + c];
                    if (coefficient < negPrecision) {
                        enteringColumn = c;
                        break;
                    }
                }
                // Fallback: unrestricted with non-zero coefficient (swap infeasibility)
                if (enteringColumn === 0) {
                    for (let c = 1; c <= lastColumn; c++) {
                        const coefficient = matrix[leavingRowOffset + c];
                        if (unrestrictedVars[varIndexByCol[c]] === true &&
                            (coefficient < negPrecision || coefficient > precision)) {
                            enteringColumn = c;
                            break;
                        }
                    }
                }
            }
            else {
                // Max-quotient rule: faster in practice but can oscillate on
                // degenerate problems.
                // First pass: negative coefficients only
                let maxQuotient = -Infinity;
                for (let c = 1; c <= lastColumn; c++) {
                    const coefficient = matrix[leavingRowOffset + c];
                    if (coefficient < negPrecision) {
                        const quotient = -matrix[c] / coefficient;
                        if (maxQuotient < quotient) {
                            maxQuotient = quotient;
                            enteringColumn = c;
                        }
                    }
                }
                // Fallback: unrestricted with non-zero coefficient
                if (enteringColumn === 0) {
                    for (let c = 1; c <= lastColumn; c++) {
                        const coefficient = matrix[leavingRowOffset + c];
                        if (unrestrictedVars[varIndexByCol[c]] === true &&
                            (coefficient < negPrecision || coefficient > precision)) {
                            enteringColumn = c;
                            break;
                        }
                    }
                }
            }
            if (enteringColumn === 0) {
                this.feasible = false;
                return iterations;
            }
            if (cycleDetector) {
                const cycleData = cycleDetector.add(varIndexByRow[leavingRowIndex], varIndexByCol[enteringColumn]);
                if (cycleData.length > 0) {
                    this.model.messages.push("Cycle in phase 1");
                    this.model.messages.push("Start :" + cycleData[0]);
                    this.model.messages.push("Length :" + cycleData[1]);
                    this.feasible = false;
                    return iterations;
                }
            }
            this.pivot(leavingRowIndex, enteringColumn);
            iterations += 1;
        }
    }
    function phase2() {
        const debugCheckForCycles = this.model.checkForCycles;
        const cycleDetector = debugCheckForCycles ? new CycleDetector() : null;
        const matrix = this.matrix;
        const width = this.width;
        const rhsColumn = this.rhsColumn;
        const lastColumn = this.width - 1;
        const lastRow = this.height - 1;
        const precision = this.precision;
        const negPrecision = -precision;
        const nOptionalObjectives = this.optionalObjectives.length;
        let optionalCostsColumns = null;
        // Cache arrays for faster access in hot loops
        const unrestrictedVars = this.unrestrictedVars;
        const varIndexByCol = this.varIndexByCol;
        const varIndexByRow = this.varIndexByRow;
        // Note: costRowIndex is always 0, so we access matrix[c] directly
        let iterations = 0;
        let reducedCost;
        let unrestricted;
        // Anti-cycling for phase 2: if the objective stalls (no meaningful
        // improvement over several hundred iterations), the simplex is
        // cycling through degenerate vertices. Switch to Bland's rule which
        // guarantees termination in exact arithmetic. In floating-point,
        // even Bland's can cycle indefinitely, so we also impose a limit:
        // if Bland's runs for lastRow iterations without improving the
        // objective, we accept the current solution as optimal.
        const PHASE2_WINDOW = 100;
        const PHASE2_STALE_LIMIT = 5; // consecutive stale windows before switching
        let useBland = false;
        let windowStartObj = matrix[rhsColumn];
        let staleWindows = 0;
        let blandStartIter = 0;
        let blandStartObj = 0;
        // Partial pricing setup
        // Batch size: use configured value or auto-compute (sqrt of columns, min 50, max 500)
        const nColumns = lastColumn;
        const batchSize = this.pricingBatchSize > 0
            ? this.pricingBatchSize
            : Math.min(500, Math.max(50, Math.floor(Math.sqrt(nColumns))));
        // For small problems, just scan everything (no benefit from partial pricing)
        const usePartialPricing = nColumns > batchSize * 2;
        while (true) {
            if (nOptionalObjectives > 0) {
                optionalCostsColumns = [];
            }
            // Detect degenerate cycling: check every WINDOW iterations
            // whether the objective has made meaningful progress.
            if (!useBland && iterations > 0 && iterations % PHASE2_WINDOW === 0) {
                const currentObj = matrix[rhsColumn];
                const delta = Math.abs(currentObj - windowStartObj);
                const scale = Math.max(1, Math.abs(windowStartObj));
                if (delta / scale < 1e-10) {
                    staleWindows++;
                    if (staleWindows >= PHASE2_STALE_LIMIT) {
                        useBland = true;
                        blandStartIter = iterations;
                        blandStartObj = currentObj;
                    }
                }
                else {
                    staleWindows = 0;
                }
                windowStartObj = currentObj;
            }
            // Bland's termination: in floating-point arithmetic, Bland's rule
            // can cycle through degenerate bases indefinitely. If it hasn't
            // improved the objective after lastRow pivots, accept the current
            // solution (reduced costs are within floating-point noise of zero).
            if (useBland && iterations - blandStartIter > lastRow) {
                const currentObj = matrix[rhsColumn];
                const delta = Math.abs(currentObj - blandStartObj);
                const scale = Math.max(1, Math.abs(blandStartObj));
                if (delta / scale < 1e-10) {
                    this.setEvaluation();
                    this.simplexIters += 1;
                    return iterations;
                }
                // Objective did improve; reset the counter
                blandStartIter = iterations;
                blandStartObj = currentObj;
            }
            let enteringColumn = 0;
            let enteringValue = precision;
            let isReducedCostNegative = false;
            if (useBland) {
                // Bland's rule: pick first eligible column (smallest index)
                for (let c = 1; c <= lastColumn; c++) {
                    reducedCost = matrix[c];
                    unrestricted = unrestrictedVars[varIndexByCol[c]] === true;
                    if (unrestricted && reducedCost < 0) {
                        enteringColumn = c;
                        enteringValue = -reducedCost;
                        isReducedCostNegative = true;
                        break;
                    }
                    if (reducedCost > precision) {
                        enteringColumn = c;
                        enteringValue = reducedCost;
                        isReducedCostNegative = false;
                        break;
                    }
                }
            }
            else if (usePartialPricing) {
                // Partial pricing: scan columns in batches
                const startBatch = this.pricingBatchStart;
                let batchesScanned = 0;
                const totalBatches = Math.ceil(nColumns / batchSize);
                // Scan batches until we find an improving column or exhaust all batches
                while (enteringColumn === 0 && batchesScanned < totalBatches) {
                    const batchStart = this.pricingBatchStart;
                    const batchEnd = Math.min(batchStart + batchSize - 1, lastColumn);
                    for (let c = batchStart; c <= batchEnd; c++) {
                        reducedCost = matrix[c]; // costRowOffset is 0
                        unrestricted = unrestrictedVars[varIndexByCol[c]] === true;
                        if (nOptionalObjectives > 0 &&
                            negPrecision < reducedCost &&
                            reducedCost < precision) {
                            optionalCostsColumns === null || optionalCostsColumns === void 0 ? void 0 : optionalCostsColumns.push(c);
                            continue;
                        }
                        if (unrestricted && reducedCost < 0) {
                            if (-reducedCost > enteringValue) {
                                enteringValue = -reducedCost;
                                enteringColumn = c;
                                isReducedCostNegative = true;
                            }
                            continue;
                        }
                        if (reducedCost > enteringValue) {
                            enteringValue = reducedCost;
                            enteringColumn = c;
                            isReducedCostNegative = false;
                        }
                    }
                    // Move to next batch (wrap around)
                    this.pricingBatchStart = batchEnd >= lastColumn ? 1 : batchEnd + 1;
                    batchesScanned++;
                }
                // Reset batch start if we found an improving column
                if (enteringColumn !== 0) {
                    this.pricingBatchStart = startBatch;
                }
            }
            else {
                // Full pricing for small problems
                for (let c = 1; c <= lastColumn; c++) {
                    reducedCost = matrix[c]; // costRowOffset is 0
                    unrestricted = unrestrictedVars[varIndexByCol[c]] === true;
                    if (nOptionalObjectives > 0 &&
                        negPrecision < reducedCost &&
                        reducedCost < precision) {
                        optionalCostsColumns === null || optionalCostsColumns === void 0 ? void 0 : optionalCostsColumns.push(c);
                        continue;
                    }
                    if (unrestricted && reducedCost < 0) {
                        if (-reducedCost > enteringValue) {
                            enteringValue = -reducedCost;
                            enteringColumn = c;
                            isReducedCostNegative = true;
                        }
                        continue;
                    }
                    if (reducedCost > enteringValue) {
                        enteringValue = reducedCost;
                        enteringColumn = c;
                        isReducedCostNegative = false;
                    }
                }
            }
            if (nOptionalObjectives > 0) {
                let o = 0;
                while (enteringColumn === 0 &&
                    optionalCostsColumns &&
                    optionalCostsColumns.length > 0 &&
                    o < nOptionalObjectives) {
                    const optionalCostsColumns2 = [];
                    const reducedCosts = this.optionalObjectives[o].reducedCosts;
                    enteringValue = precision;
                    for (let i = 0; i < optionalCostsColumns.length; i++) {
                        const c = optionalCostsColumns[i];
                        reducedCost = reducedCosts[c];
                        unrestricted = unrestrictedVars[varIndexByCol[c]] === true;
                        if (negPrecision < reducedCost && reducedCost < precision) {
                            optionalCostsColumns2.push(c);
                            continue;
                        }
                        if (unrestricted && reducedCost < 0) {
                            if (-reducedCost > enteringValue) {
                                enteringValue = -reducedCost;
                                enteringColumn = c;
                                isReducedCostNegative = true;
                            }
                            continue;
                        }
                        if (reducedCost > enteringValue) {
                            enteringValue = reducedCost;
                            enteringColumn = c;
                            isReducedCostNegative = false;
                        }
                    }
                    optionalCostsColumns = optionalCostsColumns2;
                    o += 1;
                }
            }
            if (enteringColumn === 0) {
                this.setEvaluation();
                this.simplexIters += 1;
                return iterations;
            }
            let leavingRow = 0;
            let minQuotient = Infinity;
            for (let r = 1; r <= lastRow; r++) {
                const rowOffset = r * width;
                const rhsValue = matrix[rowOffset + rhsColumn];
                const colValue = matrix[rowOffset + enteringColumn];
                if (negPrecision < colValue && colValue < precision) {
                    continue;
                }
                if (colValue > 0 && precision > rhsValue && rhsValue > negPrecision) {
                    minQuotient = 0;
                    leavingRow = r;
                    break;
                }
                const quotient = isReducedCostNegative ? -rhsValue / colValue : rhsValue / colValue;
                if (quotient > precision && minQuotient > quotient) {
                    minQuotient = quotient;
                    leavingRow = r;
                }
            }
            if (minQuotient === Infinity) {
                this.evaluation = -Infinity;
                this.bounded = false;
                this.unboundedVarIndex = varIndexByCol[enteringColumn];
                return iterations;
            }
            if (cycleDetector) {
                const cycleData = cycleDetector.add(varIndexByRow[leavingRow], varIndexByCol[enteringColumn]);
                if (cycleData.length > 0) {
                    this.model.messages.push("Cycle in phase 2");
                    this.model.messages.push("Start :" + cycleData[0]);
                    this.model.messages.push("Length :" + cycleData[1]);
                    this.feasible = false;
                    return iterations;
                }
            }
            this.pivot(leavingRow, enteringColumn);
            iterations += 1;
        }
    }
    // Pre-allocated typed arrays for pivot optimization (better cache performance)
    let nonZeroColumns = new Int32Array(1024);
    let pivotRowCache = new Float64Array(1024);
    function pivot(pivotRowIndex, pivotColumnIndex) {
        const matrix = this.matrix;
        const width = this.width;
        // Ensure work arrays are large enough
        if (width > nonZeroColumns.length) {
            nonZeroColumns = new Int32Array(width * 2);
            pivotRowCache = new Float64Array(width * 2);
        }
        const pivotRowOffset = pivotRowIndex * width;
        const quotient = matrix[pivotRowOffset + pivotColumnIndex];
        const invQuotient = 1 / quotient;
        const height = this.height;
        const leavingBasicIndex = this.varIndexByRow[pivotRowIndex];
        const enteringBasicIndex = this.varIndexByCol[pivotColumnIndex];
        this.varIndexByRow[pivotRowIndex] = enteringBasicIndex;
        this.varIndexByCol[pivotColumnIndex] = leavingBasicIndex;
        this.rowByVarIndex[enteringBasicIndex] = pivotRowIndex;
        this.rowByVarIndex[leavingBasicIndex] = -1;
        this.colByVarIndex[enteringBasicIndex] = -1;
        this.colByVarIndex[leavingBasicIndex] = pivotColumnIndex;
        // Normalize pivot row, track non-zero columns, and cache values for locality
        let nNonZeroColumns = 0;
        for (let c = 0; c < width; c++) {
            const idx = pivotRowOffset + c;
            const val = matrix[idx];
            if (!(val >= -1e-16 && val <= 1e-16)) {
                const normalized = val / quotient;
                matrix[idx] = normalized;
                nonZeroColumns[nNonZeroColumns] = c;
                pivotRowCache[nNonZeroColumns] = normalized;
                nNonZeroColumns++;
            }
            else {
                matrix[idx] = 0;
            }
        }
        matrix[pivotRowOffset + pivotColumnIndex] = invQuotient;
        // Update all other rows using cached pivot row values
        for (let r = 0; r < height; r++) {
            if (r !== pivotRowIndex) {
                const rowOffset = r * width;
                const pivotColVal = matrix[rowOffset + pivotColumnIndex];
                if (!(pivotColVal >= -1e-16 && pivotColVal <= 1e-16)) {
                    const coefficient = pivotColVal;
                    if (!(coefficient >= -1e-16 && coefficient <= 1e-16)) {
                        // Use cached pivot row values for better cache locality
                        for (let i = 0; i < nNonZeroColumns; i++) {
                            const c = nonZeroColumns[i];
                            const v0 = pivotRowCache[i];
                            // Inner zero check is critical for numerical stability
                            if (!(v0 >= -1e-16 && v0 <= 1e-16)) {
                                matrix[rowOffset + c] -= coefficient * v0;
                            }
                            else if (v0 !== 0) {
                                // Clean up near-zero values in pivot row
                                matrix[pivotRowOffset + c] = 0;
                            }
                        }
                        matrix[rowOffset + pivotColumnIndex] = -coefficient / quotient;
                    }
                    else if (coefficient !== 0) {
                        matrix[rowOffset + pivotColumnIndex] = 0;
                    }
                }
            }
        }
        // Update optional objectives using cached pivot row values
        const optionalObjectives = this.optionalObjectives;
        const nOptionalObjectives = optionalObjectives.length;
        if (nOptionalObjectives > 0) {
            for (let o = 0; o < nOptionalObjectives; o++) {
                const reducedCosts = optionalObjectives[o].reducedCosts;
                const coefficient = reducedCosts[pivotColumnIndex];
                if (coefficient !== 0) {
                    for (let i = 0; i < nNonZeroColumns; i++) {
                        const c = nonZeroColumns[i];
                        reducedCosts[c] -= coefficient * pivotRowCache[i];
                    }
                    reducedCosts[pivotColumnIndex] = -coefficient * invQuotient;
                }
            }
        }
    }
    function checkForCycles(varIndexes) {
        for (let e1 = 0; e1 < varIndexes.length - 1; e1++) {
            for (let e2 = e1 + 1; e2 < varIndexes.length; e2++) {
                const elt1 = varIndexes[e1];
                const elt2 = varIndexes[e2];
                if (elt1[0] === elt2[0] && elt1[1] === elt2[1]) {
                    if (e2 - e1 > varIndexes.length - e2) {
                        break;
                    }
                    let cycleFound = true;
                    for (let i = 1; i < e2 - e1; i++) {
                        const tmp1 = varIndexes[e1 + i];
                        const tmp2 = varIndexes[e2 + i];
                        if (tmp1[0] !== tmp2[0] || tmp1[1] !== tmp2[1]) {
                            cycleFound = false;
                            break;
                        }
                    }
                    if (cycleFound) {
                        return [e1, e2 - e1];
                    }
                }
            }
        }
        return [];
    }

    class Variable {
        constructor(id, cost, index, priority) {
            this.id = id;
            this.cost = cost;
            this.index = index;
            this.value = 0;
            this.priority = priority;
        }
    }
    class IntegerVariable extends Variable {
        constructor(id, cost, index, priority) {
            super(id, cost, index, priority);
            this.isInteger = true;
        }
    }
    class SlackVariable extends Variable {
        constructor(id, index) {
            super(id, 0, index, 0);
            this.isSlack = true;
        }
    }
    class Term {
        constructor(variable, coefficient) {
            this.variable = variable;
            this.coefficient = coefficient;
        }
    }
    function createRelaxationVariable(model, weight, priority) {
        if (priority === 0 || priority === "required") {
            return null;
        }
        const normalizedWeight = weight === undefined ? 1 : weight;
        const normalizedPriority = priority === undefined ? 1 : priority;
        const actualWeight = model.isMinimization === false ? -normalizedWeight : normalizedWeight;
        return model.addVariable(actualWeight, "r" + model.relaxationIndex++, false, false, normalizedPriority);
    }
    class Constraint {
        constructor(rhs, isUpperBound, index, model) {
            this.slack = new SlackVariable("s" + index, index);
            this.index = index;
            this.model = model;
            this.rhs = rhs;
            this.isUpperBound = isUpperBound;
            this.terms = [];
            this.termsByVarIndex = {};
            this.relaxation = null;
        }
        addTerm(coefficient, variable) {
            const varIndex = variable.index;
            const term = this.termsByVarIndex[varIndex];
            if (term === undefined) {
                // No term for given variable
                const newTerm = new Term(variable, coefficient);
                this.termsByVarIndex[varIndex] = newTerm;
                this.terms.push(newTerm);
                const signedCoefficient = this.isUpperBound === true ? -coefficient : coefficient;
                this.model.updateConstraintCoefficient(this, variable, signedCoefficient);
            }
            else {
                // Term for given variable already exists
                // updating its coefficient
                const newCoefficient = term.coefficient + coefficient;
                this.setVariableCoefficient(newCoefficient, variable);
            }
            return this;
        }
        // TODO: Implement term removal if required by consumers.
        removeTerm(_term) {
            return this;
        }
        setRightHandSide(newRhs) {
            if (newRhs !== this.rhs) {
                let difference = newRhs - this.rhs;
                if (this.isUpperBound === true) {
                    difference = -difference;
                }
                this.rhs = newRhs;
                this.model.updateRightHandSide(this, difference);
            }
            return this;
        }
        setVariableCoefficient(newCoefficient, variable) {
            const varIndex = variable.index;
            if (varIndex === -1) {
                // eslint-disable-next-line no-console
                console.warn("[Constraint.setVariableCoefficient] Trying to change coefficient of inexistant variable.");
                return;
            }
            const term = this.termsByVarIndex[varIndex];
            if (term === undefined) {
                // No term for given variable
                this.addTerm(newCoefficient, variable);
            }
            else if (newCoefficient !== term.coefficient) {
                // Term for given variable already exists
                // updating its coefficient if changed
                let difference = newCoefficient - term.coefficient;
                if (this.isUpperBound === true) {
                    difference = -difference;
                }
                term.coefficient = newCoefficient;
                this.model.updateConstraintCoefficient(this, variable, difference);
            }
            return this;
        }
        relax(weight, priority) {
            this.relaxation = createRelaxationVariable(this.model, weight, priority);
            this._relax(this.relaxation);
        }
        _relax(relaxationVariable) {
            if (relaxationVariable === null) {
                // Relaxation variable not created, priority was probably "required"
                return;
            }
            if (this.isUpperBound) {
                this.setVariableCoefficient(-1, relaxationVariable);
            }
            else {
                this.setVariableCoefficient(1, relaxationVariable);
            }
        }
    }
    class Equality {
        constructor(constraintUpper, constraintLower) {
            this.isEquality = true;
            this.upperBound = constraintUpper;
            this.lowerBound = constraintLower;
            this.model = constraintUpper.model;
            this.rhs = constraintUpper.rhs;
            this.relaxation = null;
        }
        addTerm(coefficient, variable) {
            this.upperBound.addTerm(coefficient, variable);
            this.lowerBound.addTerm(coefficient, variable);
            return this;
        }
        // TODO: Implement term removal if required by consumers.
        removeTerm(_term) {
            this.upperBound.removeTerm(_term);
            this.lowerBound.removeTerm(_term);
            return this;
        }
        setRightHandSide(rhs) {
            this.upperBound.setRightHandSide(rhs);
            this.lowerBound.setRightHandSide(rhs);
            this.rhs = rhs;
        }
        relax(weight, priority) {
            this.relaxation = createRelaxationVariable(this.model, weight, priority);
            this.upperBound.relaxation = this.relaxation;
            this.upperBound._relax(this.relaxation);
            this.lowerBound.relaxation = this.relaxation;
            this.lowerBound._relax(this.relaxation);
        }
    }
    class Numeral {
        constructor(value) {
            this.value = value;
        }
    }

    function addCutConstraints(cutConstraints) {
        const nCutConstraints = cutConstraints.length;
        const height = this.height;
        const heightWithCuts = height + nCutConstraints;
        const width = this.width;
        const lastColumn = width - 1;
        // Grow the matrix to accommodate new rows (with over-allocation to reduce reallocation frequency)
        const oldMatrix = this.matrix;
        const newSize = heightWithCuts * width;
        if (oldMatrix.length < newSize) {
            // Over-allocate by 50% to reduce future reallocations
            const allocSize = Math.ceil(newSize * 1.5);
            const newMatrix = new Float64Array(allocSize);
            newMatrix.set(oldMatrix);
            this.matrix = newMatrix;
        }
        const matrix = this.matrix;
        this.height = heightWithCuts;
        this.nVars = this.width + this.height - 2;
        // Cache array references for faster access in loop
        const rhsColumn = this.rhsColumn;
        const rowByVarIndex = this.rowByVarIndex;
        const colByVarIndex = this.colByVarIndex;
        const varIndexByRow = this.varIndexByRow;
        const variablesPerIndex = this.variablesPerIndex;
        for (let h = 0; h < nCutConstraints; h += 1) {
            const cut = cutConstraints[h];
            const cutRow = height + h;
            const cutRowOffset = cutRow * width;
            const sign = cut.type === "min" ? -1 : 1;
            const varIndex = cut.varIndex;
            let varRowIndex = rowByVarIndex[varIndex];
            if (varRowIndex === -1) {
                matrix[cutRowOffset + rhsColumn] = sign * cut.value;
                for (let c = 1; c <= lastColumn; c += 1) {
                    matrix[cutRowOffset + c] = 0;
                }
                matrix[cutRowOffset + colByVarIndex[varIndex]] = sign;
            }
            else {
                const varRowOffset = varRowIndex * width;
                const varValue = matrix[varRowOffset + rhsColumn];
                matrix[cutRowOffset + rhsColumn] = sign * (cut.value - varValue);
                for (let c = 1; c <= lastColumn; c += 1) {
                    matrix[cutRowOffset + c] = -sign * matrix[varRowOffset + c];
                }
            }
            varRowIndex = this.getNewElementIndex();
            varIndexByRow[cutRow] = varRowIndex;
            rowByVarIndex[varRowIndex] = cutRow;
            colByVarIndex[varRowIndex] = -1;
            variablesPerIndex[varRowIndex] = new SlackVariable("s" + varRowIndex, varRowIndex);
            this.nVars += 1;
        }
    }
    function addLowerBoundMIRCut(rowIndex) {
        if (rowIndex === this.costRowIndex) {
            return false;
        }
        const width = this.width;
        const matrix = this.matrix;
        const cutRowOffset = rowIndex * width;
        const integerVar = this.variablesPerIndex[this.varIndexByRow[rowIndex]];
        if (integerVar === undefined || !integerVar.isInteger) {
            return false;
        }
        const rhsValue = matrix[cutRowOffset + this.rhsColumn];
        const fractionalPart = rhsValue - Math.floor(rhsValue);
        if (fractionalPart < this.precision || fractionalPart > 1 - this.precision) {
            return false;
        }
        const height = this.height;
        const newRowOffset = height * width;
        // Grow matrix to add new row (with over-allocation to reduce reallocation frequency)
        const newSize = (height + 1) * width;
        if (matrix.length < newSize) {
            // Over-allocate by 50% to reduce future reallocations
            const allocSize = Math.ceil(newSize * 1.5);
            const newMatrix = new Float64Array(allocSize);
            newMatrix.set(matrix);
            this.matrix = newMatrix;
        }
        const mat = this.matrix;
        this.height += 1;
        this.nVars += 1;
        const slackVarIndex = this.getNewElementIndex();
        this.varIndexByRow[height] = slackVarIndex;
        this.rowByVarIndex[slackVarIndex] = height;
        this.colByVarIndex[slackVarIndex] = -1;
        this.variablesPerIndex[slackVarIndex] = new SlackVariable("s" + slackVarIndex, slackVarIndex);
        const rhsColumn = this.rhsColumn;
        mat[newRowOffset + rhsColumn] = Math.floor(rhsValue);
        // Cache array references for faster access in hot loop
        const variablesPerIndex = this.variablesPerIndex;
        const varIndexByCol = this.varIndexByCol;
        const varIndexByColLen = varIndexByCol.length;
        const oneMinusFrac = 1 - fractionalPart;
        for (let colIndex = 1; colIndex < varIndexByColLen; colIndex += 1) {
            const variable = variablesPerIndex[varIndexByCol[colIndex]];
            const coefficient = mat[cutRowOffset + colIndex];
            if (variable !== undefined && variable.isInteger) {
                const floorCoeff = Math.floor(coefficient);
                const termCoeff = floorCoeff + Math.max(0, coefficient - floorCoeff - fractionalPart) / oneMinusFrac;
                mat[newRowOffset + colIndex] = termCoeff;
            }
            else {
                mat[newRowOffset + colIndex] = Math.min(0, coefficient / oneMinusFrac);
            }
        }
        for (let c = 0; c < width; c += 1) {
            mat[newRowOffset + c] -= mat[cutRowOffset + c];
        }
        return true;
    }
    function addUpperBoundMIRCut(rowIndex) {
        if (rowIndex === this.costRowIndex) {
            return false;
        }
        const width = this.width;
        const matrix = this.matrix;
        const cutRowOffset = rowIndex * width;
        const integerVar = this.variablesPerIndex[this.varIndexByRow[rowIndex]];
        if (integerVar === undefined || !integerVar.isInteger) {
            return false;
        }
        const rhsValue = matrix[cutRowOffset + this.rhsColumn];
        const fractionalPart = rhsValue - Math.floor(rhsValue);
        if (fractionalPart < this.precision || fractionalPart > 1 - this.precision) {
            return false;
        }
        const height = this.height;
        const newRowOffset = height * width;
        // Grow matrix to add new row (with over-allocation to reduce reallocation frequency)
        const newSize = (height + 1) * width;
        if (matrix.length < newSize) {
            // Over-allocate by 50% to reduce future reallocations
            const allocSize = Math.ceil(newSize * 1.5);
            const newMatrix = new Float64Array(allocSize);
            newMatrix.set(matrix);
            this.matrix = newMatrix;
        }
        const mat = this.matrix;
        this.height += 1;
        this.nVars += 1;
        const slackVarIndex = this.getNewElementIndex();
        this.varIndexByRow[height] = slackVarIndex;
        this.rowByVarIndex[slackVarIndex] = height;
        this.colByVarIndex[slackVarIndex] = -1;
        this.variablesPerIndex[slackVarIndex] = new SlackVariable("s" + slackVarIndex, slackVarIndex);
        const rhsColumn = this.rhsColumn;
        mat[newRowOffset + rhsColumn] = -fractionalPart;
        // Cache array references for faster access in hot loop
        const variablesPerIndex = this.variablesPerIndex;
        const varIndexByCol = this.varIndexByCol;
        const varIndexByColLen = varIndexByCol.length;
        const oneMinusFrac = 1 - fractionalPart;
        for (let colIndex = 1; colIndex < varIndexByColLen; colIndex += 1) {
            const variable = variablesPerIndex[varIndexByCol[colIndex]];
            const coefficient = mat[cutRowOffset + colIndex];
            const termCoeff = coefficient - Math.floor(coefficient);
            if (variable !== undefined && variable.isInteger) {
                mat[newRowOffset + colIndex] =
                    termCoeff <= fractionalPart
                        ? -termCoeff
                        : (-(1 - termCoeff) * fractionalPart) / termCoeff;
            }
            else {
                mat[newRowOffset + colIndex] =
                    coefficient >= 0 ? -coefficient : (coefficient * fractionalPart) / oneMinusFrac;
            }
        }
        return true;
    }
    function applyMIRCuts() {
        // Apply MIR (Mixed Integer Rounding) cuts to all rows with fractional integer variables
        // This tightens the LP relaxation and can help prune the branch-and-bound tree
        const height = this.height;
        let cutsAdded = 0;
        const maxCuts = 10; // Limit cuts per iteration to avoid excessive growth
        for (let r = 1; r < height && cutsAdded < maxCuts; r++) {
            // Try lower bound MIR cut first (typically more effective)
            if (this.addLowerBoundMIRCut(r)) {
                cutsAdded++;
            }
        }
    }

    function putInBase(varIndex) {
        const width = this.width;
        let r = this.rowByVarIndex[varIndex];
        if (r === -1) {
            const c = this.colByVarIndex[varIndex];
            for (let r1 = 1; r1 < this.height; r1 += 1) {
                const coefficient = this.matrix[r1 * width + c];
                if (coefficient < -this.precision || this.precision < coefficient) {
                    r = r1;
                    break;
                }
            }
            this.pivot(r, c);
        }
        return r;
    }
    function takeOutOfBase(varIndex) {
        const width = this.width;
        let c = this.colByVarIndex[varIndex];
        if (c === -1) {
            const r = this.rowByVarIndex[varIndex];
            const pivotRowOffset = r * width;
            for (let c1 = 1; c1 < this.height; c1 += 1) {
                const coefficient = this.matrix[pivotRowOffset + c1];
                if (coefficient < -this.precision || this.precision < coefficient) {
                    c = c1;
                    break;
                }
            }
            this.pivot(r, c);
        }
        return c;
    }
    function updateVariableValues() {
        const width = this.width;
        const matrix = this.matrix;
        const rhsColumn = this.rhsColumn;
        const nVars = this.variables.length;
        const roundingCoeff = Math.round(1 / this.precision);
        for (let v = 0; v < nVars; v += 1) {
            const variable = this.variables[v];
            const varIndex = variable.index;
            const r = this.rowByVarIndex[varIndex];
            if (r === -1) {
                variable.value = 0;
            }
            else {
                const varValue = matrix[r * width + rhsColumn];
                variable.value =
                    Math.round((varValue + Number.EPSILON) * roundingCoeff) / roundingCoeff;
            }
        }
    }
    function updateRightHandSide(constraint, difference) {
        const width = this.width;
        const matrix = this.matrix;
        const rhsColumn = this.rhsColumn;
        const lastRow = this.height - 1;
        const constraintRow = this.rowByVarIndex[constraint.index];
        if (constraintRow === -1) {
            const slackColumn = this.colByVarIndex[constraint.index];
            for (let r = 0; r <= lastRow; r += 1) {
                const rowOffset = r * width;
                matrix[rowOffset + rhsColumn] -= difference * matrix[rowOffset + slackColumn];
            }
            const nOptionalObjectives = this.optionalObjectives.length;
            if (nOptionalObjectives > 0) {
                for (let o = 0; o < nOptionalObjectives; o += 1) {
                    const reducedCosts = this.optionalObjectives[o].reducedCosts;
                    reducedCosts[rhsColumn] -= difference * reducedCosts[slackColumn];
                }
            }
        }
        else {
            matrix[constraintRow * width + rhsColumn] -= difference;
        }
    }
    function updateConstraintCoefficient(constraint, variable, difference) {
        if (constraint.index === variable.index) {
            throw new Error("[Tableau.updateConstraintCoefficient] constraint index should not be equal to variable index !");
        }
        const width = this.width;
        const matrix = this.matrix;
        const r = this.putInBase(constraint.index);
        const rowOffset = r * width;
        const colVar = this.colByVarIndex[variable.index];
        if (colVar === -1) {
            const rowVar = this.rowByVarIndex[variable.index];
            const rowVarOffset = rowVar * width;
            for (let c = 0; c < width; c += 1) {
                matrix[rowOffset + c] += difference * matrix[rowVarOffset + c];
            }
        }
        else {
            matrix[rowOffset + colVar] -= difference;
        }
    }
    function updateCost(variable, difference) {
        const width = this.width;
        const matrix = this.matrix;
        const varIndex = variable.index;
        const lastColumn = width - 1;
        const varColumn = this.colByVarIndex[varIndex];
        if (varColumn === -1) {
            const variableRowOffset = this.rowByVarIndex[varIndex] * width;
            if (variable.priority === 0) {
                // Cost row is row 0
                for (let c = 0; c <= lastColumn; c += 1) {
                    matrix[c] += difference * matrix[variableRowOffset + c];
                }
            }
            else {
                const reducedCosts = this.objectivesByPriority[variable.priority].reducedCosts;
                for (let c = 0; c <= lastColumn; c += 1) {
                    reducedCosts[c] += difference * matrix[variableRowOffset + c];
                }
            }
        }
        else {
            matrix[varColumn] -= difference; // row 0, col varColumn
        }
    }
    function addConstraint(constraint) {
        const sign = constraint.isUpperBound ? 1 : -1;
        const lastRow = this.height;
        const width = this.width;
        const lastColumn = width - 1;
        // Check if we need to grow the matrix capacity (using exponential growth)
        const newRowCount = lastRow + 1;
        const requiredSize = newRowCount * width;
        if (this.matrix.length < requiredSize) {
            // Use exponential growth strategy (1.5x) with minimum increment
            const currentCapacity = this.matrix.length;
            const minGrowth = Math.max(width * 16, Math.floor(currentCapacity * 0.5));
            const newCapacity = currentCapacity + minGrowth;
            const oldMatrix = this.matrix;
            const newMatrix = new Float64Array(newCapacity);
            newMatrix.set(oldMatrix);
            this.matrix = newMatrix;
        }
        const matrix = this.matrix;
        const constraintRowOffset = lastRow * width;
        // Zero out the new row
        for (let c = 0; c <= lastColumn; c += 1) {
            matrix[constraintRowOffset + c] = 0;
        }
        matrix[constraintRowOffset + this.rhsColumn] = sign * constraint.rhs;
        const terms = constraint.terms;
        const nTerms = terms.length;
        for (let t = 0; t < nTerms; t += 1) {
            const term = terms[t];
            const coefficient = term.coefficient;
            const varIndex = term.variable.index;
            const varRowIndex = this.rowByVarIndex[varIndex];
            if (varRowIndex === -1) {
                matrix[constraintRowOffset + this.colByVarIndex[varIndex]] += sign * coefficient;
            }
            else {
                const varRowOffset = varRowIndex * width;
                for (let c = 0; c <= lastColumn; c += 1) {
                    matrix[constraintRowOffset + c] -= sign * coefficient * matrix[varRowOffset + c];
                }
            }
        }
        const slackIndex = constraint.index;
        this.varIndexByRow[lastRow] = slackIndex;
        this.rowByVarIndex[slackIndex] = lastRow;
        this.colByVarIndex[slackIndex] = -1;
        this.height += 1;
    }
    function removeConstraint(constraint) {
        const slackIndex = constraint.index;
        const lastRow = this.height - 1;
        const width = this.width;
        const matrix = this.matrix;
        const r = this.putInBase(slackIndex);
        // Swap row r with lastRow
        const rowOffset = r * width;
        const lastRowOffset = lastRow * width;
        for (let c = 0; c < width; c++) {
            const tmp = matrix[lastRowOffset + c];
            matrix[lastRowOffset + c] = matrix[rowOffset + c];
            matrix[rowOffset + c] = tmp;
        }
        this.varIndexByRow[r] = this.varIndexByRow[lastRow];
        this.varIndexByRow[lastRow] = -1;
        this.rowByVarIndex[slackIndex] = -1;
        this.availableIndexes[this.availableIndexes.length] = slackIndex;
        constraint.slack.index = -1;
        this.height -= 1;
    }
    function addVariable(variable) {
        this.height - 1;
        const oldWidth = this.width;
        const newWidth = oldWidth + 1;
        const height = this.height;
        const cost = this.model.isMinimization === true ? -variable.cost : variable.cost;
        const priority = variable.priority;
        // Need to expand the matrix to add a new column
        // This requires reallocating and copying with new layout
        // Note: Column capacity optimization would require changing all matrix access
        // to use capacity as stride, which is too invasive. Keep simple reallocation.
        const oldMatrix = this.matrix;
        const newMatrix = new Float64Array(height * newWidth);
        // Copy old data with new width
        for (let r = 0; r < height; r++) {
            const oldOffset = r * oldWidth;
            const newOffset = r * newWidth;
            for (let c = 0; c < oldWidth; c++) {
                newMatrix[newOffset + c] = oldMatrix[oldOffset + c];
            }
            // New column is 0 by default
        }
        this.matrix = newMatrix;
        this.width = newWidth;
        const lastColumn = newWidth - 1;
        const nOptionalObjectives = this.optionalObjectives.length;
        if (nOptionalObjectives > 0) {
            for (let o = 0; o < nOptionalObjectives; o += 1) {
                this.optionalObjectives[o].reducedCosts[lastColumn] = 0;
            }
        }
        if (priority === 0) {
            newMatrix[lastColumn] = cost; // row 0, col lastColumn
        }
        else {
            this.setOptionalObjective(priority, lastColumn, cost);
            newMatrix[lastColumn] = 0;
        }
        this.colByVarIndex[variable.index] = lastColumn;
        this.varIndexByCol[lastColumn] = variable.index;
    }
    function removeVariable(variable) {
        const varIndex = variable.index;
        const width = this.width;
        const matrix = this.matrix;
        const lastColumn = width - 1;
        const c = this.takeOutOfBase(varIndex);
        const lastRow = this.height - 1;
        for (let r = 0; r <= lastRow; r += 1) {
            const rowOffset = r * width;
            matrix[rowOffset + c] = matrix[rowOffset + lastColumn];
        }
        this.varIndexByCol[c] = this.varIndexByCol[lastColumn];
        this.rowByVarIndex[varIndex] = -1;
        this.colByVarIndex[varIndex] = -1;
        this.availableIndexes[this.availableIndexes.length] = varIndex;
        this.width -= 1;
    }

    function copy() {
        const copy = new this.constructor(this.precision, this.branchAndCutService);
        copy.width = this.width;
        copy.height = this.height;
        copy.nVars = this.nVars;
        copy.model = this.model;
        copy.variables = this.variables;
        copy.variablesPerIndex = this.variablesPerIndex;
        copy.unrestrictedVars = this.unrestrictedVars;
        copy.lastElementIndex = this.lastElementIndex;
        copy.varIndexByRow = this.varIndexByRow.slice();
        copy.varIndexByCol = this.varIndexByCol.slice();
        copy.rowByVarIndex = this.rowByVarIndex.slice();
        copy.colByVarIndex = this.colByVarIndex.slice();
        copy.availableIndexes = this.availableIndexes.slice();
        const optionalObjectivesCopy = [];
        for (let o = 0; o < this.optionalObjectives.length; o++) {
            optionalObjectivesCopy[o] = this.optionalObjectives[o].copy();
        }
        copy.optionalObjectives = optionalObjectivesCopy;
        copy.objectivesByPriority = { ...this.objectivesByPriority };
        copy.optionalObjectivePerPriority = { ...this.optionalObjectivePerPriority };
        // Fast Float64Array copy using constructor
        copy.matrix = new Float64Array(this.matrix);
        return copy;
    }
    function save() {
        this.savedState = this.copy();
    }
    function restore() {
        if (this.savedState === null) {
            return;
        }
        const save = this.savedState;
        this.nVars = save.nVars;
        this.model = save.model;
        this.variables = save.variables;
        this.variablesPerIndex = save.variablesPerIndex;
        this.unrestrictedVars = save.unrestrictedVars;
        this.lastElementIndex = save.lastElementIndex;
        this.width = save.width;
        this.height = save.height;
        // Fast Float64Array restore using set()
        this.matrix.set(save.matrix);
        const savedBasicIndexes = save.varIndexByRow;
        const height = this.height;
        for (let c = 0; c < height; c += 1) {
            this.varIndexByRow[c] = savedBasicIndexes[c];
        }
        this.varIndexByRow.length = height;
        const savedNonBasicIndexes = save.varIndexByCol;
        const width = this.width;
        for (let r = 0; r < width; r += 1) {
            this.varIndexByCol[r] = savedNonBasicIndexes[r];
        }
        this.varIndexByCol.length = width;
        const savedRows = save.rowByVarIndex;
        const savedCols = save.colByVarIndex;
        for (let v = 0; v < this.nVars; v += 1) {
            this.rowByVarIndex[v] = savedRows[v];
            this.colByVarIndex[v] = savedCols[v];
        }
        if (save.optionalObjectives.length > 0 && this.optionalObjectives.length > 0) {
            this.optionalObjectives = [];
            this.optionalObjectivePerPriority = {};
            for (let o = 0; o < save.optionalObjectives.length; o++) {
                const optionalObjectiveCopy = save.optionalObjectives[o].copy();
                this.optionalObjectives[o] = optionalObjectiveCopy;
                this.optionalObjectivePerPriority[optionalObjectiveCopy.priority] =
                    optionalObjectiveCopy;
                this.objectivesByPriority[optionalObjectiveCopy.priority] = optionalObjectiveCopy;
            }
        }
    }

    // ========== Integer Property Functions ==========
    /**
     * Count how many integer variables currently have integral values.
     */
    function countIntegerValues() {
        let count = 0;
        const width = this.width;
        const matrix = this.matrix;
        const rhsColumn = this.rhsColumn;
        for (let r = 1; r < this.height; r += 1) {
            const variable = this.variablesPerIndex[this.varIndexByRow[r]];
            if (variable !== undefined && variable.isInteger) {
                const value = matrix[r * width + rhsColumn];
                const decimalPart = value - Math.floor(value);
                if (decimalPart < this.precision && -decimalPart < this.precision) {
                    count += 1;
                }
            }
        }
        return count;
    }
    /**
     * Check if all integer variables have integral values.
     * Returns true if the current solution is integral.
     */
    function isIntegral() {
        const width = this.width;
        const matrix = this.matrix;
        const rhsColumn = this.rhsColumn;
        const integerVariables = this.model.integerVariables;
        const nIntegerVars = integerVariables.length;
        // Cache array reference for faster access in hot loop
        const rowByVarIndex = this.rowByVarIndex;
        const precision = this.precision;
        for (let v = 0; v < nIntegerVars; v++) {
            const varIndex = integerVariables[v].index;
            const row = rowByVarIndex[varIndex];
            if (row !== -1) {
                const value = matrix[row * width + rhsColumn];
                if (Math.abs(value - Math.round(value)) > precision) {
                    return false;
                }
            }
        }
        return true;
    }
    /**
     * Compute a measure of how fractional the current solution is.
     * Used for evaluating the quality of cutting planes.
     */
    function computeFractionalVolume(ignoreIntegerValues) {
        let volume = -1;
        const width = this.width;
        const matrix = this.matrix;
        const rhsColumn = this.rhsColumn;
        const height = this.height;
        // Cache array references for faster access in hot loop
        const variablesPerIndex = this.variablesPerIndex;
        const varIndexByRow = this.varIndexByRow;
        const precision = this.precision;
        for (let r = 1; r < height; r += 1) {
            const variable = variablesPerIndex[varIndexByRow[r]];
            if (variable !== undefined && variable.isInteger) {
                const value = matrix[r * width + rhsColumn];
                const distance = Math.abs(value);
                if (Math.min(distance - Math.floor(distance), Math.floor(distance + 1)) < precision) {
                    if (ignoreIntegerValues !== true) {
                        return 0;
                    }
                }
                else if (volume === -1) {
                    volume = distance;
                }
                else {
                    volume *= distance;
                }
            }
        }
        return volume === -1 ? 0 : volume;
    }
    // ========== Branching Variable Selection ==========
    /**
     * Select the integer variable with the most fractional value.
     * Standard branching strategy - picks the variable closest to 0.5 fractionality.
     */
    function getMostFractionalVar() {
        let biggestFraction = 0;
        let selectedVarIndex = null;
        let selectedVarValue = 0;
        const width = this.width;
        const matrix = this.matrix;
        const rhsColumn = this.rhsColumn;
        const integerVars = this.model.integerVariables;
        const nIntegerVars = integerVars.length;
        // Cache array reference for faster access in hot loop
        const rowByVarIndex = this.rowByVarIndex;
        for (let v = 0; v < nIntegerVars; v += 1) {
            const varIndex = integerVars[v].index;
            const row = rowByVarIndex[varIndex];
            if (row !== -1) {
                const varValue = matrix[row * width + rhsColumn];
                const fraction = Math.abs(varValue - Math.round(varValue));
                if (fraction > biggestFraction) {
                    biggestFraction = fraction;
                    selectedVarIndex = varIndex;
                    selectedVarValue = varValue;
                }
            }
        }
        return { index: selectedVarIndex, value: selectedVarValue };
    }
    /**
     * Select the fractional integer variable with the lowest cost coefficient.
     * Alternative branching strategy that considers objective function impact.
     */
    function getFractionalVarWithLowestCost() {
        let highestCost = Infinity;
        let selectedVarIndex = null;
        let selectedVarValue = null;
        const width = this.width;
        const matrix = this.matrix;
        const rhsColumn = this.rhsColumn;
        const integerVars = this.model.integerVariables;
        const nIntegerVars = integerVars.length;
        for (let v = 0; v < nIntegerVars; v += 1) {
            const variable = integerVars[v];
            const varIndex = variable.index;
            const varRow = this.rowByVarIndex[varIndex];
            if (varRow !== -1) {
                const varValue = matrix[varRow * width + rhsColumn];
                if (Math.abs(varValue - Math.round(varValue)) > this.precision &&
                    variable.cost < highestCost) {
                    highestCost = variable.cost;
                    selectedVarIndex = varIndex;
                    selectedVarValue = varValue;
                }
            }
        }
        return { index: selectedVarIndex, value: selectedVarValue };
    }

    function log(message, force) {
        if (!force) {
            return this;
        }
        // eslint-disable-next-line no-console
        console.log("****", message, "****");
        // eslint-disable-next-line no-console
        console.log("Nb Variables", this.width - 1);
        // eslint-disable-next-line no-console
        console.log("Nb Constraints", this.height - 1);
        // console.log("Variable Ids", this.variablesPerIndex);
        // eslint-disable-next-line no-console
        console.log("Basic Indexes", this.varIndexByRow);
        // eslint-disable-next-line no-console
        console.log("Non Basic Indexes", this.varIndexByCol);
        // eslint-disable-next-line no-console
        console.log("Rows", this.rowByVarIndex);
        // eslint-disable-next-line no-console
        console.log("Cols", this.colByVarIndex);
        const digitPrecision = 5;
        const matrix = this.matrix;
        const width = this.width;
        let varNameRowString = "";
        const spacePerColumn = [" "];
        let j;
        let c;
        let varIndex;
        let varName;
        let varNameLength;
        let valueSpace;
        let nameSpace;
        for (c = 1; c < this.width; c += 1) {
            varIndex = this.varIndexByCol[c];
            const variable = this.variablesPerIndex[varIndex];
            if (variable === undefined) {
                varName = "c" + varIndex;
            }
            else {
                varName = variable.id;
            }
            varNameLength = varName.length;
            valueSpace = " ";
            nameSpace = "\t";
            if (varNameLength > 5) {
                valueSpace += " ";
            }
            else {
                nameSpace += "\t";
            }
            spacePerColumn[c] = valueSpace;
            varNameRowString += nameSpace + varName;
        }
        // eslint-disable-next-line no-console
        console.log(varNameRowString);
        let signSpace;
        const costRowOffset = this.costRowIndex * width;
        let firstRowString = "\t";
        for (j = 1; j < this.width; j += 1) {
            signSpace = "\t";
            firstRowString += signSpace;
            firstRowString += spacePerColumn[j];
            firstRowString += matrix[costRowOffset + j].toFixed(digitPrecision);
        }
        signSpace = "\t";
        firstRowString += signSpace + spacePerColumn[0] + matrix[costRowOffset].toFixed(digitPrecision);
        // eslint-disable-next-line no-console
        console.log(firstRowString + "\tZ");
        for (let r = 1; r < this.height; r += 1) {
            const rowOffset = r * width;
            let rowString = "\t";
            for (c = 1; c < this.width; c += 1) {
                signSpace = "\t";
                rowString +=
                    signSpace + spacePerColumn[c] + matrix[rowOffset + c].toFixed(digitPrecision);
            }
            signSpace = "\t";
            rowString += signSpace + spacePerColumn[0] + matrix[rowOffset].toFixed(digitPrecision);
            varIndex = this.varIndexByRow[r];
            const variable = this.variablesPerIndex[varIndex];
            if (variable === undefined) {
                varName = "c" + varIndex;
            }
            else {
                varName = variable.id;
            }
            // eslint-disable-next-line no-console
            console.log(rowString + "\t" + varName);
        }
        // eslint-disable-next-line no-console
        console.log("");
        const nOptionalObjectives = this.optionalObjectives.length;
        if (nOptionalObjectives > 0) {
            // eslint-disable-next-line no-console
            console.log("    Optional objectives:");
            for (let o = 0; o < nOptionalObjectives; o += 1) {
                const reducedCosts = this.optionalObjectives[o].reducedCosts;
                let reducedCostsString = "";
                for (j = 1; j < this.width; j += 1) {
                    signSpace = reducedCosts[j] < 0 ? "" : " ";
                    reducedCostsString += signSpace;
                    reducedCostsString += spacePerColumn[j];
                    reducedCostsString += reducedCosts[j].toFixed(digitPrecision);
                }
                signSpace = reducedCosts[0] < 0 ? "" : " ";
                reducedCostsString +=
                    signSpace + spacePerColumn[0] + reducedCosts[0].toFixed(digitPrecision);
                // eslint-disable-next-line no-console
                console.log(reducedCostsString + " z" + o);
            }
        }
        // eslint-disable-next-line no-console
        console.log("Feasible?", this.feasible);
        // eslint-disable-next-line no-console
        console.log("evaluation", this.evaluation);
        return this;
    }

    /**
     * @file src/tableau/tableau.ts
     * @description Core Tableau class for the simplex algorithm
     *
     * The Tableau represents the LP problem in matrix form and provides:
     * - Matrix storage using Float64Array for numerical precision
     * - Variable and constraint index management
     * - Simplex operations (via bound function imports)
     * - Branch-and-cut integration for MIP solving
     * - Save/restore for backtracking during B&B
     */
    function createOptionalObjective(priority, nColumns, reducedCosts) {
        return {
            priority,
            reducedCosts: reducedCosts ? reducedCosts.slice() : new Array(nColumns).fill(0),
            copy() {
                return createOptionalObjective(this.priority, this.reducedCosts.length, this.reducedCosts);
            },
        };
    }
    class Tableau {
        constructor(precision = 1e-8, branchAndCutService) {
            this.model = null;
            this.matrix = new Float64Array(0);
            this.width = 0;
            this.height = 0;
            this.costRowIndex = 0;
            this.rhsColumn = 0;
            this.variablesPerIndex = [];
            this.unrestrictedVars = {};
            this.feasible = true;
            this.evaluation = 0;
            this.simplexIters = 0;
            this.varIndexByRow = [];
            this.varIndexByCol = [];
            this.rowByVarIndex = [];
            this.colByVarIndex = [];
            this.optionalObjectives = [];
            this.objectivesByPriority = {};
            this.optionalObjectivePerPriority = {};
            this.savedState = null;
            this.availableIndexes = [];
            this.lastElementIndex = 0;
            this.variables = [];
            this.nVars = 0;
            this.bounded = true;
            this.unboundedVarIndex = null;
            this.branchAndCutIterations = 0;
            this.bestPossibleEval = 0;
            // Partial pricing state for phase2 optimization
            this.pricingBatchStart = 1;
            this.pricingBatchSize = 0; // 0 means auto-compute based on problem size
            this.precision = precision;
            this.branchAndCutService = branchAndCutService !== null && branchAndCutService !== void 0 ? branchAndCutService : createBranchAndCutService();
        }
        // ========== Core Simplex Operations ==========
        simplex() {
            simplex.call(this);
            return this;
        }
        phase1() {
            return phase1.call(this);
        }
        phase2() {
            return phase2.call(this);
        }
        /**
         * Dual simplex for warm-starting after adding bound constraints.
         * Use when solution is dual feasible but may be primal infeasible.
         * @returns Number of iterations, or -1 if dual infeasible
         */
        dualSimplex() {
            return dualSimplex.call(this);
        }
        pivot(pivotRowIndex, pivotColumnIndex) {
            pivot.call(this, pivotRowIndex, pivotColumnIndex);
        }
        checkForCycles(varIndexes) {
            return checkForCycles.call(this, varIndexes);
        }
        // ========== Integer/MIP Properties ==========
        countIntegerValues() {
            return countIntegerValues.call(this);
        }
        isIntegral() {
            return isIntegral.call(this);
        }
        computeFractionalVolume(ignoreIntegerValues) {
            return computeFractionalVolume.call(this, ignoreIntegerValues);
        }
        // ========== Cutting Strategies ==========
        addCutConstraints(branchingCuts) {
            addCutConstraints.call(this, branchingCuts);
        }
        applyMIRCuts() {
            applyMIRCuts.call(this);
        }
        addLowerBoundMIRCut(rowIndex) {
            return addLowerBoundMIRCut.call(this, rowIndex);
        }
        addUpperBoundMIRCut(rowIndex) {
            return addUpperBoundMIRCut.call(this, rowIndex);
        }
        // ========== Branching Strategies ==========
        getMostFractionalVar() {
            return getMostFractionalVar.call(this);
        }
        getFractionalVarWithLowestCost() {
            return getFractionalVarWithLowestCost.call(this);
        }
        // ========== Dynamic Modification ==========
        putInBase(varIndex) {
            return putInBase.call(this, varIndex);
        }
        takeOutOfBase(varIndex) {
            return takeOutOfBase.call(this, varIndex);
        }
        updateVariableValues() {
            updateVariableValues.call(this);
        }
        updateRightHandSide(constraint, difference) {
            updateRightHandSide.call(this, constraint, difference);
        }
        updateConstraintCoefficient(constraint, variable, difference) {
            updateConstraintCoefficient.call(this, constraint, variable, difference);
        }
        updateCost(variable, difference) {
            updateCost.call(this, variable, difference);
        }
        addConstraint(constraint) {
            addConstraint.call(this, constraint);
        }
        removeConstraint(constraint) {
            removeConstraint.call(this, constraint);
        }
        addVariable(variable) {
            addVariable.call(this, variable);
        }
        removeVariable(variable) {
            removeVariable.call(this, variable);
        }
        // ========== Backup/Restore ==========
        copy() {
            return copy.call(this);
        }
        save() {
            save.call(this);
        }
        restore() {
            restore.call(this);
        }
        // ========== Debug ==========
        log(message) {
            log.call(this, message);
            return this;
        }
        // ========== Branch and Cut ==========
        applyCuts(branchingCuts) {
            this.branchAndCutService.applyCuts(this, branchingCuts);
        }
        branchAndCut() {
            this.branchAndCutService.branchAndCut(this);
        }
        // ========== Solution ==========
        solve() {
            var _a, _b;
            if (((_b = (_a = this.model) === null || _a === void 0 ? void 0 : _a.getNumberOfIntegerVariables()) !== null && _b !== void 0 ? _b : 0) > 0) {
                this.branchAndCut();
            }
            else {
                this.simplex();
            }
            this.updateVariableValues();
            return this.getSolution();
        }
        getSolution() {
            var _a, _b, _c;
            const evaluation = ((_a = this.model) === null || _a === void 0 ? void 0 : _a.isMinimization) === true ? this.evaluation : -this.evaluation;
            if (((_c = (_b = this.model) === null || _b === void 0 ? void 0 : _b.getNumberOfIntegerVariables()) !== null && _c !== void 0 ? _c : 0) > 0) {
                return new MilpSolution(this, evaluation, this.feasible, this.bounded, this.branchAndCutIterations);
            }
            else {
                return new Solution(this, evaluation, this.feasible, this.bounded);
            }
        }
        // ========== Initialization ==========
        setOptionalObjective(priority, column, cost) {
            let objectiveForPriority = this.objectivesByPriority[priority];
            if (objectiveForPriority === undefined) {
                const nColumns = Math.max(this.width, column + 1);
                objectiveForPriority = createOptionalObjective(priority, nColumns);
                this.objectivesByPriority[priority] = objectiveForPriority;
                this.optionalObjectivePerPriority[priority] = objectiveForPriority;
                this.optionalObjectives.push(objectiveForPriority);
                this.optionalObjectives.sort((a, b) => a.priority - b.priority);
            }
            objectiveForPriority.reducedCosts[column] = cost;
        }
        initialize(width, height, variables, unrestrictedVars) {
            this.variables = variables;
            this.unrestrictedVars = unrestrictedVars;
            this.width = width;
            this.height = height;
            this.matrix = new Float64Array(width * height);
            this.varIndexByRow = new Array(this.height);
            this.varIndexByCol = new Array(this.width);
            this.varIndexByRow[0] = -1;
            this.varIndexByCol[0] = -1;
            this.nVars = width + height - 2;
            this.rowByVarIndex = new Array(this.nVars);
            this.colByVarIndex = new Array(this.nVars);
            this.lastElementIndex = this.nVars;
        }
        _resetMatrix() {
            if (this.model === null) {
                throw new Error("[Tableau._resetMatrix] Model not set");
            }
            const matrix = this.matrix;
            const width = this.width;
            const variables = this.model.variables;
            const constraints = this.model.constraints;
            const nVars = variables.length;
            const nConstraints = constraints.length;
            const coeff = this.model.isMinimization === true ? -1 : 1;
            for (let v = 0; v < nVars; v += 1) {
                const variable = variables[v];
                const priority = variable.priority;
                const cost = coeff * variable.cost;
                if (priority === 0) {
                    matrix[v + 1] = cost;
                }
                else {
                    this.setOptionalObjective(priority, v + 1, cost);
                }
                const varIndex = variables[v].index;
                this.rowByVarIndex[varIndex] = -1;
                this.colByVarIndex[varIndex] = v + 1;
                this.varIndexByCol[v + 1] = varIndex;
            }
            let rowIndex = 1;
            for (let c = 0; c < nConstraints; c += 1) {
                const constraint = constraints[c];
                const constraintIndex = constraint.index;
                this.rowByVarIndex[constraintIndex] = rowIndex;
                this.colByVarIndex[constraintIndex] = -1;
                this.varIndexByRow[rowIndex] = constraintIndex;
                const terms = constraint.terms;
                const nTerms = terms.length;
                const rowOffset = rowIndex * width;
                rowIndex++;
                if (constraint.isUpperBound) {
                    for (let t = 0; t < nTerms; t += 1) {
                        const term = terms[t];
                        const column = this.colByVarIndex[term.variable.index];
                        matrix[rowOffset + column] = term.coefficient;
                    }
                    matrix[rowOffset] = constraint.rhs;
                }
                else {
                    for (let t = 0; t < nTerms; t += 1) {
                        const term = terms[t];
                        const column = this.colByVarIndex[term.variable.index];
                        matrix[rowOffset + column] = -term.coefficient;
                    }
                    matrix[rowOffset] = -constraint.rhs;
                }
            }
        }
        setModel(model) {
            this.model = model;
            const width = model.nVariables + 1;
            const height = model.nConstraints + 1;
            this.initialize(width, height, model.variables, model.unrestrictedVariables);
            this._resetMatrix();
            return this;
        }
        getNewElementIndex() {
            if (this.availableIndexes.length > 0) {
                return this.availableIndexes.pop();
            }
            const index = this.lastElementIndex;
            this.lastElementIndex += 1;
            return index;
        }
        density() {
            let density = 0;
            const matrix = this.matrix;
            const width = this.width;
            for (let r = 0; r < this.height; r++) {
                const rowOffset = r * width;
                for (let c = 0; c < width; c++) {
                    if (matrix[rowOffset + c] !== 0) {
                        density += 1;
                    }
                }
            }
            return density / (this.height * this.width);
        }
        setEvaluation() {
            const roundingCoeff = Math.round(1 / this.precision);
            const evaluation = this.matrix[this.costRowIndex * this.width + this.rhsColumn];
            const roundedEvaluation = Math.round((Number.EPSILON + evaluation) * roundingCoeff) / roundingCoeff;
            this.evaluation = roundedEvaluation;
            if (this.simplexIters === 0) {
                this.bestPossibleEval = roundedEvaluation;
            }
        }
    }

    /**
     * Probing: Temporarily fix binary variables and propagate to find implications.
     * If fixing x=0 causes infeasibility, then x must be 1 (and vice versa).
     * If both x=0 and x=1 imply y has same bound, that bound is valid.
     */
    /**
     * Coefficient tightening for knapsack-like constraints.
     * If a coefficient is larger than the remaining capacity, reduce it.
     */
    function tightenCoefficients(model, result) {
        var _a, _b, _c, _d, _e, _f, _g;
        let changed = false;
        for (const constraint of model.constraints) {
            if (result.removedConstraints.has(constraint))
                continue;
            if (!constraint.isUpperBound)
                continue; // Only for <= constraints
            // Calculate min activity (all variables at their lower bounds)
            let minActivity = 0;
            for (const term of constraint.terms) {
                if (result.fixedVariables.has(term.variable)) {
                    minActivity += term.coefficient * result.fixedVariables.get(term.variable);
                }
                else {
                    const bounds = (_a = result.tightenedBounds.get(term.variable)) !== null && _a !== void 0 ? _a : {};
                    const lower = (_b = bounds.lower) !== null && _b !== void 0 ? _b : 0;
                    if (term.coefficient > 0) {
                        minActivity += term.coefficient * lower;
                    }
                    else {
                        const upper = (_c = bounds.upper) !== null && _c !== void 0 ? _c : Infinity;
                        minActivity += term.coefficient * upper;
                    }
                }
            }
            // For each variable, check if coefficient can be tightened
            const slack = constraint.rhs - minActivity;
            if (slack < 0)
                continue; // Constraint may be infeasible
            for (const term of constraint.terms) {
                if (result.fixedVariables.has(term.variable))
                    continue;
                if (!term.variable.isInteger)
                    continue;
                if (term.coefficient <= 0)
                    continue;
                const bounds = (_d = result.tightenedBounds.get(term.variable)) !== null && _d !== void 0 ? _d : {};
                const lower = (_e = bounds.lower) !== null && _e !== void 0 ? _e : 0;
                const upper = (_f = bounds.upper) !== null && _f !== void 0 ? _f : 1;
                // For binary variables: if coeff > slack, can reduce to slack
                if (lower >= -0.5 && upper <= 1.5) {
                    const effectiveCoeff = term.coefficient * (upper - lower);
                    if (effectiveCoeff > slack + 1e-6) {
                        // Could tighten coefficient - but we don't modify the model
                        // Instead, derive an upper bound on the variable
                        const impliedUpper = lower + slack / term.coefficient;
                        if (impliedUpper < upper - 1e-6) {
                            const current = (_g = result.tightenedBounds.get(term.variable)) !== null && _g !== void 0 ? _g : {};
                            if (!current.upper || impliedUpper < current.upper) {
                                result.tightenedBounds.set(term.variable, {
                                    ...current,
                                    upper: impliedUpper,
                                });
                                result.stats.boundsTightened++;
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
        return changed;
    }
    /**
     * Detect redundant constraints using activity bounds.
     * If max activity <= RHS for <= constraint, it's redundant.
     */
    function removeRedundantConstraints(model, result) {
        var _a, _b, _c;
        let changed = false;
        for (const constraint of model.constraints) {
            if (result.removedConstraints.has(constraint))
                continue;
            // Calculate activity bounds
            let minActivity = 0;
            let maxActivity = 0;
            for (const term of constraint.terms) {
                const fixed = result.fixedVariables.get(term.variable);
                if (fixed !== undefined) {
                    minActivity += term.coefficient * fixed;
                    maxActivity += term.coefficient * fixed;
                    continue;
                }
                const bounds = (_a = result.tightenedBounds.get(term.variable)) !== null && _a !== void 0 ? _a : {};
                const lower = (_b = bounds.lower) !== null && _b !== void 0 ? _b : 0;
                const upper = (_c = bounds.upper) !== null && _c !== void 0 ? _c : Infinity;
                if (term.coefficient > 0) {
                    minActivity += term.coefficient * lower;
                    maxActivity += term.coefficient * (upper === Infinity ? 1e10 : upper);
                }
                else {
                    minActivity += term.coefficient * (upper === Infinity ? 1e10 : upper);
                    maxActivity += term.coefficient * lower;
                }
            }
            // Check redundancy
            if (constraint.isUpperBound) {
                // <= constraint is redundant if max activity <= RHS
                if (maxActivity <= constraint.rhs + 1e-6) {
                    result.removedConstraints.add(constraint);
                    result.stats.constraintsRemoved++;
                    changed = true;
                }
                // Infeasible if min activity > RHS
                if (minActivity > constraint.rhs + 1e-6) {
                    result.isInfeasible = true;
                    return false;
                }
            }
            else {
                // >= constraint is redundant if min activity >= RHS
                if (minActivity >= constraint.rhs - 1e-6) {
                    result.removedConstraints.add(constraint);
                    result.stats.constraintsRemoved++;
                    changed = true;
                }
                // Infeasible if max activity < RHS
                if (maxActivity < constraint.rhs - 1e-6) {
                    result.isInfeasible = true;
                    return false;
                }
            }
        }
        return changed;
    }
    /**
     * Presolve reductions for Mixed Integer Programs.
     * Based on techniques from COIN-OR CBC, CPLEX, and Gurobi.
     *
     * Key techniques:
     * 1. Fixed variable removal
     * 2. Singleton row detection
     * 3. Bound tightening
     * 4. Redundant constraint removal
     * 5. Probing (for binary variables)
     * 6. Coefficient tightening
     */
    function presolve(model) {
        var _a, _b;
        const result = {
            fixedVariables: new Map(),
            removedConstraints: new Set(),
            tightenedBounds: new Map(),
            isInfeasible: false,
            stats: {
                variablesFixed: 0,
                constraintsRemoved: 0,
                boundsTightened: 0,
            },
        };
        // Multiple passes for propagation
        let changed = true;
        let passes = 0;
        const maxPasses = 5;
        while (changed && passes < maxPasses) {
            changed = false;
            passes++;
            // Pass 1: Singleton rows - constraints with single variable
            for (const constraint of model.constraints) {
                if (result.removedConstraints.has(constraint))
                    continue;
                const activeTerms = constraint.terms.filter((t) => !result.fixedVariables.has(t.variable));
                if (activeTerms.length === 0) {
                    // All variables fixed - check feasibility
                    let lhs = 0;
                    for (const term of constraint.terms) {
                        const fixedVal = result.fixedVariables.get(term.variable);
                        if (fixedVal !== undefined) {
                            lhs += term.coefficient * fixedVal;
                        }
                    }
                    const satisfied = constraint.isUpperBound
                        ? lhs <= constraint.rhs + 1e-6
                        : lhs >= constraint.rhs - 1e-6;
                    if (!satisfied) {
                        result.isInfeasible = true;
                        return result;
                    }
                    result.removedConstraints.add(constraint);
                    result.stats.constraintsRemoved++;
                    changed = true;
                }
                else if (activeTerms.length === 1) {
                    // Singleton row - can fix or tighten bounds
                    const term = activeTerms[0];
                    const variable = term.variable;
                    const coeff = term.coefficient;
                    // Calculate RHS adjustment for fixed variables
                    let rhsAdj = constraint.rhs;
                    for (const t of constraint.terms) {
                        if (t.variable !== variable) {
                            const fixedVal = result.fixedVariables.get(t.variable);
                            if (fixedVal !== undefined) {
                                rhsAdj -= t.coefficient * fixedVal;
                            }
                        }
                    }
                    const bound = rhsAdj / coeff;
                    if (constraint.isUpperBound) {
                        // x <= bound (if coeff > 0) or x >= bound (if coeff < 0)
                        if (coeff > 0) {
                            // Upper bound
                            const current = result.tightenedBounds.get(variable);
                            if (!(current === null || current === void 0 ? void 0 : current.upper) || bound < current.upper) {
                                result.tightenedBounds.set(variable, {
                                    ...current,
                                    upper: bound,
                                });
                                result.stats.boundsTightened++;
                                changed = true;
                            }
                        }
                        else {
                            // Lower bound (coefficient is negative)
                            const current = result.tightenedBounds.get(variable);
                            if (!(current === null || current === void 0 ? void 0 : current.lower) || bound > current.lower) {
                                result.tightenedBounds.set(variable, {
                                    ...current,
                                    lower: bound,
                                });
                                result.stats.boundsTightened++;
                                changed = true;
                            }
                        }
                    }
                    result.removedConstraints.add(constraint);
                    result.stats.constraintsRemoved++;
                }
            }
            // Pass 2: Check for fixed variables from bounds
            for (const [variable, bounds] of result.tightenedBounds) {
                if (result.fixedVariables.has(variable))
                    continue;
                if (bounds.lower !== undefined && bounds.upper !== undefined) {
                    if (bounds.lower > bounds.upper + 1e-6) {
                        result.isInfeasible = true;
                        return result;
                    }
                    if (Math.abs(bounds.lower - bounds.upper) < 1e-6) {
                        // Variable is fixed
                        let fixedValue = bounds.lower;
                        // If integer, round to nearest integer
                        if (variable.isInteger) {
                            fixedValue = Math.round(fixedValue);
                        }
                        result.fixedVariables.set(variable, fixedValue);
                        result.stats.variablesFixed++;
                        changed = true;
                    }
                }
                // Binary variables with lower bound >= 0.5 are fixed to 1
                if (variable.isInteger && bounds.lower !== undefined && bounds.lower >= 0.5) {
                    const upperBound = (_a = bounds.upper) !== null && _a !== void 0 ? _a : Infinity;
                    if (upperBound <= 1.5) {
                        result.fixedVariables.set(variable, 1);
                        result.stats.variablesFixed++;
                        changed = true;
                    }
                }
                // Binary variables with upper bound <= 0.5 are fixed to 0
                if (variable.isInteger && bounds.upper !== undefined && bounds.upper <= 0.5) {
                    const lowerBound = (_b = bounds.lower) !== null && _b !== void 0 ? _b : 0;
                    if (lowerBound >= -0.5) {
                        result.fixedVariables.set(variable, 0);
                        result.stats.variablesFixed++;
                        changed = true;
                    }
                }
            }
            // Pass 3: Remove redundant constraints using activity bounds
            if (removeRedundantConstraints(model, result)) {
                changed = true;
            }
            if (result.isInfeasible)
                return result;
            // Pass 4: Coefficient tightening for knapsack-like constraints
            if (tightenCoefficients(model, result)) {
                changed = true;
            }
            // Pass 5: Probing for binary variables (disabled - needs more work on equality constraints)
            // TODO: Fix probing to handle equality constraints correctly
            // if (passes <= 2 && model.integerVariables.length > 0) {
            //     const probeLimit = Math.min(50, model.integerVariables.length);
            //     if (probe(model, result, probeLimit)) {
            //         changed = true;
            //     }
            //     if (result.isInfeasible) return result;
            // }
        }
        return result;
    }

    /**
     * @file src/model.ts
     * @description Model class for LP/MIP problem representation
     *
     * Provides the programmatic API for building optimization problems:
     * - Add variables with costs and integer constraints
     * - Define constraints (<=, >=, =) with coefficients
     * - Load problems from JSON model definitions
     * - Dynamic model modification after initialization
     *
     * The Model converts high-level problem definitions into the internal
     * Tableau representation used by the simplex algorithm.
     */
    class Model {
        constructor(precision, name, branchAndCutService) {
            this.tableau = new Tableau(precision, branchAndCutService);
            this.name = name;
            this.variables = [];
            this.integerVariables = [];
            this.unrestrictedVariables = {};
            this.constraints = [];
            this.nConstraints = 0;
            this.nVariables = 0;
            this.isMinimization = true;
            this.tableauInitialized = false;
            this.relaxationIndex = 1;
            this.useMIRCuts = false;
            this.checkForCycles = true;
            // Collect diagnostic messages for debugging without console output
            this.messages = [];
            this.availableIndexes = [];
            this.lastElementIndex = 0;
            this.usePresolve = true;
            this.presolveResult = null;
        }
        minimize() {
            this.isMinimization = true;
            return this;
        }
        maximize() {
            this.isMinimization = false;
            return this;
        }
        _getNewElementIndex() {
            if (this.availableIndexes.length > 0) {
                return this.availableIndexes.pop();
            }
            const index = this.lastElementIndex;
            this.lastElementIndex += 1;
            return index;
        }
        _addConstraint(constraint) {
            const slackVariable = constraint.slack;
            this.tableau.variablesPerIndex[slackVariable.index] = slackVariable;
            this.constraints.push(constraint);
            this.nConstraints += 1;
            if (this.tableauInitialized === true) {
                this.tableau.addConstraint(constraint);
            }
        }
        smallerThan(rhs) {
            const constraint = new Constraint(rhs, true, this.tableau.getNewElementIndex(), this);
            this._addConstraint(constraint);
            return constraint;
        }
        greaterThan(rhs) {
            const constraint = new Constraint(rhs, false, this.tableau.getNewElementIndex(), this);
            this._addConstraint(constraint);
            return constraint;
        }
        equal(rhs) {
            const constraintUpper = new Constraint(rhs, true, this.tableau.getNewElementIndex(), this);
            this._addConstraint(constraintUpper);
            const constraintLower = new Constraint(rhs, false, this.tableau.getNewElementIndex(), this);
            this._addConstraint(constraintLower);
            return new Equality(constraintUpper, constraintLower);
        }
        addVariable(cost, id, isInteger, isUnrestricted, priority) {
            if (typeof priority === "string") {
                switch (priority) {
                    case "required":
                        priority = 0;
                        break;
                    case "strong":
                        priority = 1;
                        break;
                    case "medium":
                        priority = 2;
                        break;
                    case "weak":
                        priority = 3;
                        break;
                    default:
                        priority = 0;
                        break;
                }
            }
            const varIndex = this.tableau.getNewElementIndex();
            const identifier = id !== null && id !== void 0 ? id : "v" + varIndex;
            const normalizedCost = cost !== null && cost !== void 0 ? cost : 0;
            const normalizedPriority = priority !== null && priority !== void 0 ? priority : 0;
            let variable;
            if (isInteger) {
                const integerVariable = new IntegerVariable(identifier, normalizedCost, varIndex, normalizedPriority);
                this.integerVariables.push(integerVariable);
                variable = integerVariable;
            }
            else {
                variable = new Variable(identifier, normalizedCost, varIndex, normalizedPriority);
            }
            this.variables.push(variable);
            this.tableau.variablesPerIndex[varIndex] = variable;
            if (isUnrestricted) {
                this.unrestrictedVariables[varIndex] = true;
            }
            this.nVariables += 1;
            if (this.tableauInitialized === true) {
                this.tableau.addVariable(variable);
            }
            return variable;
        }
        _removeConstraint(constraint) {
            const idx = this.constraints.indexOf(constraint);
            if (idx === -1) {
                // eslint-disable-next-line no-console
                console.warn("[Model.removeConstraint] Constraint not present in model");
                return;
            }
            this.constraints.splice(idx, 1);
            this.nConstraints -= 1;
            if (this.tableauInitialized === true) {
                this.tableau.removeConstraint(constraint);
            }
            if (constraint.relaxation) {
                this.removeVariable(constraint.relaxation);
            }
        }
        //-------------------------------------------------------------------
        // For dynamic model modification
        //-------------------------------------------------------------------
        removeConstraint(constraint) {
            if (constraint.isEquality) {
                const equalityConstraint = constraint;
                this._removeConstraint(equalityConstraint.upperBound);
                this._removeConstraint(equalityConstraint.lowerBound);
            }
            else {
                this._removeConstraint(constraint);
            }
            return this;
        }
        removeVariable(variable) {
            const idx = this.variables.indexOf(variable);
            if (idx === -1) {
                // eslint-disable-next-line no-console
                console.warn("[Model.removeVariable] Variable not present in model");
                return;
            }
            this.variables.splice(idx, 1);
            if (this.tableauInitialized === true) {
                this.tableau.removeVariable(variable);
            }
            return this;
        }
        updateRightHandSide(constraint, difference) {
            if (this.tableauInitialized === true) {
                this.tableau.updateRightHandSide(constraint, difference);
            }
            return this;
        }
        updateConstraintCoefficient(constraint, variable, difference) {
            if (this.tableauInitialized === true) {
                this.tableau.updateConstraintCoefficient(constraint, variable, difference);
            }
            return this;
        }
        setCost(cost, variable) {
            let difference = cost - variable.cost;
            if (this.isMinimization === false) {
                difference = -difference;
            }
            variable.cost = cost;
            this.tableau.updateCost(variable, difference);
            return this;
        }
        //-------------------------------------------------------------------
        //-------------------------------------------------------------------
        loadJson(jsonModel) {
            this.isMinimization = jsonModel.opType !== "max";
            const variables = jsonModel.variables;
            const constraints = jsonModel.constraints;
            const constraintsMin = {};
            const constraintsMax = {};
            // Instantiating constraints
            const constraintIds = Object.keys(constraints);
            const nConstraintIds = constraintIds.length;
            for (let c = 0; c < nConstraintIds; c += 1) {
                const constraintId = constraintIds[c];
                const constraint = constraints[constraintId];
                const equal = constraint.equal;
                const weight = constraint.weight;
                const priority = constraint.priority;
                const relaxed = weight !== undefined || priority !== undefined;
                let lowerBound;
                let upperBound;
                if (equal === undefined) {
                    const min = constraint.min;
                    if (min !== undefined) {
                        lowerBound = this.greaterThan(min);
                        constraintsMin[constraintId] = lowerBound;
                        if (relaxed) {
                            lowerBound.relax(weight, priority);
                        }
                    }
                    const max = constraint.max;
                    if (max !== undefined) {
                        upperBound = this.smallerThan(max);
                        constraintsMax[constraintId] = upperBound;
                        if (relaxed) {
                            upperBound.relax(weight, priority);
                        }
                    }
                }
                else {
                    lowerBound = this.greaterThan(equal);
                    constraintsMin[constraintId] = lowerBound;
                    upperBound = this.smallerThan(equal);
                    constraintsMax[constraintId] = upperBound;
                    const equality = new Equality(lowerBound, upperBound);
                    if (relaxed) {
                        equality.relax(weight, priority);
                    }
                }
            }
            const variableIds = Object.keys(variables);
            const nVariables = variableIds.length;
            // Parse solver options
            this.tolerance = jsonModel.tolerance || 0;
            if (jsonModel.timeout) {
                this.timeout = jsonModel.timeout;
            }
            // Options object takes precedence over top-level properties
            if (jsonModel.options) {
                if (jsonModel.options.timeout) {
                    this.timeout = jsonModel.options.timeout;
                }
                if (this.tolerance === 0) {
                    this.tolerance = jsonModel.options.tolerance || 0;
                }
                if (jsonModel.options.useMIRCuts) {
                    this.useMIRCuts = jsonModel.options.useMIRCuts;
                }
                // Cycle detection defaults to true
                if (typeof jsonModel.options.exitOnCycles === "undefined") {
                    this.checkForCycles = true;
                }
                else {
                    this.checkForCycles = jsonModel.options.exitOnCycles;
                }
                if (jsonModel.options.keep_solutions) {
                    this.keep_solutions = jsonModel.options.keep_solutions;
                }
                else {
                    this.keep_solutions = false;
                }
                if (jsonModel.options.presolve !== undefined) {
                    this.usePresolve = jsonModel.options.presolve;
                }
            }
            const integerVarIds = jsonModel.ints || {};
            const binaryVarIds = jsonModel.binaries || {};
            const unrestrictedVarIds = jsonModel.unrestricted || {};
            // Instantiating variables and constraint terms
            const objectiveName = jsonModel.optimize;
            // Check if objectiveName exists as a coefficient key in any variable.
            // If not, and it matches a variable name, the user wants to optimize
            // that variable directly (implicit cost of 1).
            const objectiveIsAttribute = variableIds.some((id) => objectiveName in variables[id]);
            const objectiveIsVariable = !objectiveIsAttribute && variableIds.includes(objectiveName);
            for (let v = 0; v < nVariables; v += 1) {
                // Creation of the variables
                const variableId = variableIds[v];
                const variableConstraints = variables[variableId];
                const cost = objectiveIsVariable
                    ? variableId === objectiveName
                        ? 1
                        : 0
                    : variableConstraints[objectiveName] || 0;
                const isBinary = !!binaryVarIds[variableId];
                const isInteger = !!integerVarIds[variableId] || isBinary;
                const isUnrestricted = !!unrestrictedVarIds[variableId];
                const variable = this.addVariable(cost, variableId, isInteger, isUnrestricted);
                if (isBinary) {
                    // Creating an upperbound constraint for this variable
                    this.smallerThan(1).addTerm(1, variable);
                }
                const constraintNames = Object.keys(variableConstraints);
                for (let c = 0; c < constraintNames.length; c += 1) {
                    const constraintName = constraintNames[c];
                    if (constraintName === objectiveName) {
                        continue;
                    }
                    const coefficient = variableConstraints[constraintName];
                    const constraintMin = constraintsMin[constraintName];
                    if (constraintMin !== undefined) {
                        constraintMin.addTerm(coefficient, variable);
                    }
                    const constraintMax = constraintsMax[constraintName];
                    if (constraintMax !== undefined) {
                        constraintMax.addTerm(coefficient, variable);
                    }
                }
            }
            return this;
        }
        //-------------------------------------------------------------------
        //-------------------------------------------------------------------
        getNumberOfIntegerVariables() {
            return this.integerVariables.length;
        }
        solve() {
            // Apply presolve to reduce problem size
            if (this.usePresolve && this.presolveResult === null) {
                this.presolveResult = presolve(this);
                if (this.presolveResult.isInfeasible) {
                    // Problem is infeasible - return early
                    this.tableau.feasible = false;
                    return this.tableau.getSolution();
                }
                // Apply fixed variables to constraints
                this.applyPresolveReductions(this.presolveResult);
            }
            // Setting tableau if not done
            if (this.tableauInitialized === false) {
                this.tableau.setModel(this);
                this.tableauInitialized = true;
            }
            return this.tableau.solve();
        }
        /**
         * Apply presolve reductions to the model.
         * Sets fixed variable values and removes redundant constraints.
         */
        applyPresolveReductions(result) {
            // Set fixed variable values
            for (const [variable, value] of result.fixedVariables) {
                variable.value = value;
                // Zero out the cost since variable is fixed
                variable.cost = 0;
            }
            // Note: We don't actually remove constraints/variables from the model
            // as that would require complex bookkeeping. Instead, the presolve
            // information is used to detect early infeasibility and fix variable values.
            // A more aggressive presolve would rebuild the model without fixed variables.
        }
        isFeasible() {
            return this.tableau.feasible;
        }
        save() {
            this.tableau.save();
        }
        restore() {
            this.tableau.restore();
        }
        activateMIRCuts(useMIRCuts) {
            this.useMIRCuts = useMIRCuts;
        }
        debug(debugCheckForCycles) {
            this.checkForCycles = debugCheckForCycles;
        }
        log(message) {
            return this.tableau.log(message);
        }
    }

    /**
     * Common typos and their corrections for model properties.
     */
    const PROPERTY_TYPOS = {
        optype: "opType",
        OpType: "opType",
        op_type: "opType",
        type: "opType",
        optimise: "optimize",
        Optimize: "optimize",
        objective: "optimize",
        constraint: "constraints",
        Constraints: "constraints",
        variable: "variables",
        Variables: "variables",
        vars: "variables",
        int: "ints",
        integers: "ints",
        Ints: "ints",
        binary: "binaries",
        Binaries: "binaries",
    };
    /**
     * Common typos for constraint properties.
     */
    const CONSTRAINT_TYPOS = {
        minimum: "min",
        maximum: "max",
        Min: "min",
        Max: "max",
        eq: "equal",
        equals: "equal",
        Equal: "equal",
    };
    /**
     * Checks for common typos in model properties and logs warnings.
     *
     * This helps users identify issues like using 'optype' instead of 'opType'
     * which would cause the solver to silently use default behavior.
     */
    function WarnOnTypos(model) {
        const modelKeys = Object.keys(model);
        // Check top-level property typos
        for (const key of modelKeys) {
            const correction = PROPERTY_TYPOS[key];
            if (correction) {
                console.warn(`[jsLPSolver] Warning: Model has '${key}' but expected '${correction}'. ` +
                    `This may cause unexpected behavior.`);
            }
        }
        // Check for missing required properties
        if (!model.optimize && !modelKeys.some((k) => PROPERTY_TYPOS[k] === "optimize")) {
            console.warn(`[jsLPSolver] Warning: Model is missing 'optimize' property. ` +
                `The solver needs to know which attribute to optimize.`);
        }
        if (!model.opType && !modelKeys.some((k) => PROPERTY_TYPOS[k] === "opType")) {
            console.warn(`[jsLPSolver] Warning: Model is missing 'opType' property. ` +
                `Defaulting to 'max'. Use 'opType: "max"' or 'opType: "min"' to be explicit.`);
        }
        // Check constraint property typos
        if (model.constraints) {
            for (const [constraintName, constraint] of Object.entries(model.constraints)) {
                if (typeof constraint === "object" && constraint !== null) {
                    for (const prop of Object.keys(constraint)) {
                        const correction = CONSTRAINT_TYPOS[prop];
                        if (correction) {
                            console.warn(`[jsLPSolver] Warning: Constraint '${constraintName}' has '${prop}' ` +
                                `but expected '${correction}'.`);
                        }
                    }
                }
            }
        }
        return model;
    }
    /**
     * Renames objective attributes that conflict with constraint names.
     *
     * If the optimize attribute is also used as a constraint name, this function
     * creates a new random attribute name to avoid the collision.
     */
    function CleanObjectiveAttributes(model) {
        let fakeAttr;
        let x;
        let z;
        if (typeof model.optimize === "string") {
            if (model.constraints[model.optimize]) {
                // Conflict: objective name matches a constraint name
                fakeAttr = Math.random();
                for (x in model.variables) {
                    if (model.variables[x][model.optimize]) {
                        model.variables[x][fakeAttr] = model.variables[x][model.optimize];
                    }
                }
                model.constraints[fakeAttr] = model.constraints[model.optimize];
                delete model.constraints[model.optimize];
                return model;
            }
            return model;
        }
        else {
            // Multi-objective case
            for (z in model.optimize) {
                if (model.constraints[z]) {
                    if (model.constraints[z] === "equal") {
                        // Can't optimize an equality-constrained attribute
                        delete model.optimize[z];
                    }
                    else {
                        fakeAttr = Math.random();
                        for (x in model.variables) {
                            if (model.variables[x][z]) {
                                model.variables[x][fakeAttr] = model.variables[x][z];
                            }
                        }
                        model.constraints[fakeAttr] = model.constraints[z];
                        delete model.constraints[z];
                    }
                }
            }
            return model;
        }
    }

    var validation = /*#__PURE__*/Object.freeze({
        __proto__: null,
        CleanObjectiveAttributes: CleanObjectiveAttributes,
        WarnOnTypos: WarnOnTypos
    });

    const External = {};

    /**
     * Create a structured, JSON-friendly clone of the incoming model so we can
     * mutate it freely during the multi-objective solve without affecting callers.
     */
    function cloneModel(model) {
        return JSON.parse(JSON.stringify(model));
    }
    function asPolyoptSolution(value) {
        if (value && typeof value === "object") {
            return value;
        }
        throw new Error("Polyopt requires the solver to return an object result.");
    }
    /**
     * Populate the solution object with synthetic values for any objective
     * attribute that is not a standalone variable by aggregating contributions
     * from the model's variables.
     */
    function backfillObjectiveAttributes(solution, workingModel, objectiveKeys) {
        for (const attribute of objectiveKeys) {
            // Skip attributes that already exist as explicit variables.
            if (workingModel.variables[attribute]) {
                continue;
            }
            if (typeof solution[attribute] !== "number") {
                solution[attribute] = 0;
            }
            for (const [variableName, coefficients] of Object.entries(workingModel.variables)) {
                const variableContribution = coefficients[attribute];
                const solvedValue = solution[variableName];
                if (typeof variableContribution === "number" && typeof solvedValue === "number") {
                    solution[attribute] += solvedValue * variableContribution;
                }
            }
        }
    }
    /**
     * Build a string key for a solution vector so we can detect identical vertices
     * (within a small rounding tolerance) and avoid double-counting them when
     * computing the midpoint.
     */
    function buildVectorKey(solution, objectiveKeys) {
        const suffix = objectiveKeys
            .map((key) => {
            const value = solution[key];
            // Round to three decimals so tiny floating point differences do not
            // create distinct vector identifiers.
            return typeof value === "number" ? Math.round(value * 1000) / 1000 : 0;
        })
            .join("-");
        return `base-${suffix}`;
    }
    /**
     * Ensure each vertex object contains all attribute keys and capture the min/max
     * range for each objective across the Pareto set.
     */
    function computeRanges(vertices) {
        var _a;
        const ranges = {};
        // First pass: establish keys and initial ranges from observed values.
        for (const vertex of vertices) {
            for (const [key, value] of Object.entries(vertex)) {
                if (typeof value !== "number") {
                    continue;
                }
                const current = (_a = ranges[key]) !== null && _a !== void 0 ? _a : {
                    min: Number.POSITIVE_INFINITY,
                    max: Number.NEGATIVE_INFINITY,
                };
                ranges[key] = {
                    min: Math.min(current.min, value),
                    max: Math.max(current.max, value),
                };
            }
        }
        // Second pass: fill missing attributes with zero so all vertices are aligned
        // and ranges account for implicit zeros.
        for (const vertex of vertices) {
            for (const key of Object.keys(ranges)) {
                if (typeof vertex[key] !== "number") {
                    vertex[key] = 0;
                }
                ranges[key].min = Math.min(ranges[key].min, vertex[key]);
                ranges[key].max = Math.max(ranges[key].max, vertex[key]);
            }
        }
        // Normalize any untouched ranges to zero so callers never see infinities.
        for (const [key, range] of Object.entries(ranges)) {
            if (!Number.isFinite(range.min)) {
                ranges[key] = { min: 0, max: 0 };
            }
        }
        return ranges;
    }
    /**
     * Solve a model with multiple objective functions by optimizing each objective
     * independently, collecting the resulting Pareto vertices, and solving a
     * derived model that targets the midpoint across all objectives.
     */
    function Polyopt(solver, model) {
        const workingModel = cloneModel(model);
        const objectives = workingModel.optimize;
        const objectiveKeys = Object.keys(objectives);
        if (objectiveKeys.length === 0) {
            throw new Error("Multi-objective solve requires at least one objective definition.");
        }
        // We'll replace optimize/opType repeatedly, so start with a clean slate.
        const workingRecord = workingModel;
        delete workingRecord.optimize;
        delete workingRecord.opType;
        const aggregatedTargets = {};
        const uniqueVectors = new Set();
        const paretoVertices = [];
        for (const key of objectiveKeys) {
            aggregatedTargets[key] = 0;
        }
        for (const objectiveName of objectiveKeys) {
            // Configure the working model to focus solely on the current objective.
            workingModel.optimize = objectiveName;
            workingModel.opType = objectives[objectiveName];
            const solution = asPolyoptSolution(solver.Solve(workingModel, undefined, undefined, true));
            // Ensure attributes that are not explicit variables still get values we can compare.
            backfillObjectiveAttributes(solution, workingModel, objectiveKeys);
            const vectorKey = buildVectorKey(solution, objectiveKeys);
            if (uniqueVectors.has(vectorKey)) {
                continue;
            }
            uniqueVectors.add(vectorKey);
            for (const key of objectiveKeys) {
                const value = solution[key];
                if (typeof value === "number") {
                    aggregatedTargets[key] += value;
                }
            }
            // Strip metadata so each Pareto vertex only contains value-bearing fields.
            const { feasible: _feasible, result: _result, bounded: _bounded, ...paretoPayload } = solution;
            paretoVertices.push(paretoPayload);
        }
        // Derive equality constraints that represent the averaged objective values.
        for (const key of objectiveKeys) {
            workingModel.constraints[key] = { equal: aggregatedTargets[key] / uniqueVectors.size };
        }
        // Add a synthetic objective so the solver has something concrete to maximize.
        const syntheticObjective = `cheater-${Math.random()}`;
        workingModel.optimize = syntheticObjective;
        workingModel.opType = "max";
        for (const variable of Object.values(workingModel.variables)) {
            variable[syntheticObjective] = 1;
        }
        const ranges = computeRanges(paretoVertices);
        const midpoint = asPolyoptSolution(solver.Solve(workingModel, undefined, undefined, true));
        return {
            midpoint,
            vertices: paretoVertices,
            ranges,
        };
    }

    function getDefaultExportFromCjs (x) {
    	return x && x.__esModule && Object.prototype.hasOwnProperty.call(x, 'default') ? x['default'] : x;
    }

    /**
     * @file src/external/lpsolve/reformat.js
     * @description LP format conversion utilities
     *
     * Converts between jsLPSolver's JSON model format and the standard
     * LP file format used by lp_solve and other solvers:
     * - to_JSON: Parse LP text format into JSON model
     * - to_lpsolve: Convert JSON model to LP text format
     *
     * Supports objectives, constraints, integer/binary variables.
     */

    /*global describe*/
    /*global require*/
    /*global module*/
    /*global it*/
    /*global console*/
    /*global process*/
    /*jshint -W083 */
    function to_JSON(input) {
        var rxo = {
                /* jshint ignore:start */
                is_blank: /^\W{0,}$/,
                is_objective: /(max|min)(imize){0,}\:/i,
                is_int: /^(?!\/\*)\W{0,}int/i,
                is_bin: /^(?!\/\*)\W{0,}bin/i,
                is_constraint: /(\>|\<){0,}\=/i,
                is_unrestricted: /^\S{0,}unrestricted/i,
                parse_lhs: /(\-|\+){0,1}\s{0,1}\d{0,}\.{0,}\d{0,}\s{0,}[A-Za-z]\S{0,}/gi,
                parse_rhs: /(\-|\+){0,1}\d{1,}\.{0,}\d{0,}\W{0,}\;{0,1}$/i,
                parse_dir: /(\>|\<){0,}\=/gi,
                parse_int: /[^\s|^\,]+/gi,
                parse_bin: /[^\s|^\,]+/gi,
                get_num: /(\-|\+){0,1}(\W|^)\d+\.{0,1}\d{0,}/g,
                get_word: /[A-Za-z].*/,
                /* jshint ignore:end */
            },
            model = {
                opType: "",
                optimize: "_obj",
                constraints: {},
                variables: {},
            },
            constraints = {
                ">=": "min",
                "<=": "max",
                "=": "equal",
            },
            tmp = "",
            ary = null,
            hldr = "",
            hldr2 = "",
            constraint = "",
            rhs = 0;

        // Handle input if its coming
        // to us as a hard string
        // instead of as an array of
        // strings
        if (typeof input === "string") {
            input = input.split("\n");
        }

        // Start iterating over the rows
        // to see what all we have
        for (var i = 0; i < input.length; i++) {
            constraint = "__" + i;

            // Get the string we're working with
            tmp = input[i];

            // Reset the array
            ary = null;

            // Test to see if we're the objective
            if (rxo.is_objective.test(tmp)) {
                // Set up in model the opType
                model.opType = tmp.match(/(max|min)/gi)[0];

                // Pull apart lhs
                ary = tmp
                    .match(rxo.parse_lhs)
                    .map(function (d) {
                        return d.replace(/\s+/, "");
                    })
                    .slice(1);

                // *** STEP 1 *** ///
                // Get the variables out
                ary.forEach(function (d) {
                    // Get the number if its there
                    hldr = d.match(rxo.get_num);

                    // If it isn't a number, it might
                    // be a standalone variable
                    if (hldr === null) {
                        if (d.substr(0, 1) === "-") {
                            hldr = -1;
                        } else {
                            hldr = 1;
                        }
                    } else {
                        hldr = hldr[0];
                    }

                    hldr = parseFloat(hldr);

                    // Get the variable type
                    hldr2 = d.match(rxo.get_word)[0].replace(/\;$/, "");

                    // Make sure the variable is in the model
                    model.variables[hldr2] = model.variables[hldr2] || {};
                    model.variables[hldr2]._obj = hldr;
                });
                ////////////////////////////////////
            } else if (rxo.is_int.test(tmp)) {
                // Get the array of ints
                ary = tmp.match(rxo.parse_int).slice(1);

                // Since we have an int, our model should too
                model.ints = model.ints || {};

                ary.forEach(function (d) {
                    d = d.replace(";", "");
                    model.ints[d] = 1;
                });
                ////////////////////////////////////
            } else if (rxo.is_bin.test(tmp)) {
                // Get the array of bins
                ary = tmp.match(rxo.parse_bin).slice(1);

                // Since we have an binary, our model should too
                model.binaries = model.binaries || {};

                ary.forEach(function (d) {
                    d = d.replace(";", "");
                    model.binaries[d] = 1;
                });
                ////////////////////////////////////
            } else if (rxo.is_constraint.test(tmp)) {
                var separatorIndex = tmp.indexOf(":");
                var constraintExpression = separatorIndex === -1 ? tmp : tmp.slice(separatorIndex + 1);

                // Pull apart lhs
                ary = constraintExpression.match(rxo.parse_lhs).map(function (d) {
                    return d.replace(/\s+/, "");
                });

                // *** STEP 1 *** ///
                // Get the variables out
                ary.forEach(function (d) {
                    // Get the number if its there
                    hldr = d.match(rxo.get_num);

                    if (hldr === null) {
                        if (d.substr(0, 1) === "-") {
                            hldr = -1;
                        } else {
                            hldr = 1;
                        }
                    } else {
                        hldr = hldr[0];
                    }

                    hldr = parseFloat(hldr);

                    // Get the variable name
                    hldr2 = d.match(rxo.get_word)[0];

                    // Make sure the variable is in the model
                    model.variables[hldr2] = model.variables[hldr2] || {};
                    model.variables[hldr2][constraint] = hldr;
                });

                // *** STEP 2 *** ///
                // Get the RHS out
                rhs = parseFloat(tmp.match(rxo.parse_rhs)[0]);

                // *** STEP 3 *** ///
                // Get the Constrainer out
                tmp = constraints[tmp.match(rxo.parse_dir)[0]];
                model.constraints[constraint] = model.constraints[constraint] || {};
                model.constraints[constraint][tmp] = rhs;
                ////////////////////////////////////
            } else if (rxo.is_unrestricted.test(tmp)) {
                // Get the array of unrestricted
                ary = tmp.match(rxo.parse_int).slice(1);

                // Since we have an int, our model should too
                model.unrestricted = model.unrestricted || {};

                ary.forEach(function (d) {
                    d = d.replace(";", "");
                    model.unrestricted[d] = 1;
                });
            }
        }
        return model;
    }

    /*************************************************************
     * Method: from_JSON
     * Scope: Public:
     * Agruments: model: The model we want solver to operate on
     * Purpose: Convert a friendly JSON model into a model for a
     *          real solving library...in this case
     *          lp_solver
     **************************************************************/
    function from_JSON(model) {
        // Make sure we at least have a model
        if (!model) {
            throw new Error("Solver requires a model to operate on");
        }

        var output = "",
            lookup = {
                max: "<=",
                min: ">=",
                equal: "=",
            },
            rxClean = new RegExp("[^A-Za-z0-9_\[\{\}\/\.\&\#\$\%\~\'\@\^]", "gi");

        // Build the objective statement

        if (model.opType) {
            output += model.opType + ":";

            // Iterate over the variables
            for (var x in model.variables) {
                // Give each variable a self of 1 unless
                // it exists already
                model.variables[x][x] = model.variables[x][x] ? model.variables[x][x] : 1;

                // Does our objective exist here?
                if (model.variables[x][model.optimize]) {
                    output += " " + model.variables[x][model.optimize] + " " + x.replace(rxClean, "_");
                }
            }
        } else {
            output += "max:";
        }

        // Add some closure to our line thing
        output += ";\n\n";

        // And now... to iterate over the constraints
        for (var xx in model.constraints) {
            for (var y in model.constraints[xx]) {
                if (typeof lookup[y] !== "undefined") {
                    for (var z in model.variables) {
                        // Does our Constraint exist here?
                        if (typeof model.variables[z][xx] !== "undefined") {
                            output += " " + model.variables[z][xx] + " " + z.replace(rxClean, "_");
                        }
                    }
                    // Add the constraint type and value...

                    output += " " + lookup[y] + " " + model.constraints[xx][y];
                    output += ";\n";
                }
            }
        }

        // Are there any ints?
        if (model.ints) {
            output += "\n\n";
            for (var xxx in model.ints) {
                output += "int " + xxx.replace(rxClean, "_") + ";\n";
            }
        }

        // Are there any unrestricted?
        if (model.unrestricted) {
            output += "\n\n";
            for (var xxxx in model.unrestricted) {
                output += "unrestricted " + xxxx.replace(rxClean, "_") + ";\n";
            }
        }

        // And kick the string back
        return output;
    }

    var reformat = function (model) {
        // If the user is giving us an array
        // or a string, convert it to a JSON Model
        // otherwise, spit it out as a string
        if (model.length) {
            return to_JSON(model);
        } else {
            return from_JSON(model);
        }
    };

    var ReformatLP = /*@__PURE__*/getDefaultExportFromCjs(reformat);

    function createCut$1(type, varIndex, value) {
        return { type, varIndex, value };
    }
    function createBranch$1(relaxedEvaluation, cuts, depth, branchVarIndex, branchDirection, branchFractionality, parentEvaluation) {
        return {
            relaxedEvaluation,
            cuts,
            depth,
            branchVarIndex,
            branchDirection,
            branchFractionality,
            parentEvaluation,
        };
    }
    /**
     * Enhanced branch-and-cut with:
     * - Pseudocost branching
     * - Hybrid node selection (depth-first early, best-first later)
     * - Diving heuristic for quick feasible solutions
     */
    function createEnhancedBranchAndCutService(options = {}) {
        const { nodeSelection = "hybrid", branching = "pseudocost", useDiving: _useDiving = true, // Reserved for future diving heuristic
        strongBranchingCandidates = 5, } = options;
        // Pseudocost data per variable index
        const pseudoCosts = new Map();
        const getPseudoCost = (varIndex) => {
            let data = pseudoCosts.get(varIndex);
            if (!data) {
                data = { upSum: 0, upCount: 0, downSum: 0, downCount: 0 };
                pseudoCosts.set(varIndex, data);
            }
            return data;
        };
        const updatePseudoCost = (varIndex, direction, improvement, fraction) => {
            const data = getPseudoCost(varIndex);
            const normalizedImprovement = improvement / (direction === "up" ? 1 - fraction : fraction);
            if (direction === "up") {
                data.upSum += normalizedImprovement;
                data.upCount++;
            }
            else {
                data.downSum += normalizedImprovement;
                data.downCount++;
            }
        };
        const getScore = (varIndex, fraction) => {
            const data = getPseudoCost(varIndex);
            // Use geometric mean of up and down pseudocosts
            const upPseudo = data.upCount > 0 ? data.upSum / data.upCount : 1;
            const downPseudo = data.downCount > 0 ? data.downSum / data.downCount : 1;
            const upEstimate = upPseudo * (1 - fraction);
            const downEstimate = downPseudo * fraction;
            // Product score (like SCIP's default)
            return Math.max(upEstimate, 1e-6) * Math.max(downEstimate, 1e-6);
        };
        const selectBranchingVariable = (tableau, _currentEval) => {
            const width = tableau.width;
            const matrix = tableau.matrix;
            const rhsColumn = tableau.rhsColumn;
            const integerVars = tableau.model.integerVariables;
            const precision = tableau.precision;
            let candidates = [];
            // Collect fractional variables
            for (const variable of integerVars) {
                const varIndex = variable.index;
                const row = tableau.rowByVarIndex[varIndex];
                if (row !== -1) {
                    const value = matrix[row * width + rhsColumn];
                    const fraction = Math.abs(value - Math.round(value));
                    if (fraction > precision) {
                        candidates.push({ index: varIndex, value, fraction });
                    }
                }
            }
            if (candidates.length === 0)
                return null;
            if (branching === "most-fractional") {
                // Original strategy - pick most fractional
                candidates.sort((a, b) => b.fraction - a.fraction);
                return { index: candidates[0].index, value: candidates[0].value };
            }
            if (branching === "pseudocost") {
                // Score by pseudocosts
                let bestScore = -Infinity;
                let bestCandidate = candidates[0];
                for (const candidate of candidates) {
                    const score = getScore(candidate.index, candidate.fraction);
                    if (score > bestScore) {
                        bestScore = score;
                        bestCandidate = candidate;
                    }
                }
                return { index: bestCandidate.index, value: bestCandidate.value };
            }
            if (branching === "strong") {
                // Strong branching on top candidates
                // Sort by most fractional first
                candidates.sort((a, b) => b.fraction - a.fraction);
                candidates = candidates.slice(0, strongBranchingCandidates);
                let bestScore = -Infinity;
                let bestCandidate = candidates[0];
                // For strong branching, we'd solve LP relaxations
                // Here we use a simplified version with pseudocost estimation
                for (const candidate of candidates) {
                    const data = getPseudoCost(candidate.index);
                    // If we have enough pseudocost data, use it
                    if (data.upCount >= 2 && data.downCount >= 2) {
                        const score = getScore(candidate.index, candidate.fraction);
                        if (score > bestScore) {
                            bestScore = score;
                            bestCandidate = candidate;
                        }
                    }
                    else {
                        // Fall back to most fractional
                        const score = candidate.fraction * (1 - candidate.fraction);
                        if (score > bestScore) {
                            bestScore = score;
                            bestCandidate = candidate;
                        }
                    }
                }
                return { index: bestCandidate.index, value: bestCandidate.value };
            }
            return { index: candidates[0].index, value: candidates[0].value };
        };
        const applyCuts = (tableau, branchingCuts) => {
            var _a;
            tableau.restore();
            tableau.addCutConstraints(branchingCuts);
            tableau.simplex();
            if (((_a = tableau.model) === null || _a === void 0 ? void 0 : _a.useMIRCuts) && tableau.feasible) {
                let fractionalVolumeImproved = true;
                let mirIterations = 0;
                const maxMIRIterations = 3;
                while (fractionalVolumeImproved && mirIterations < maxMIRIterations) {
                    const fractionalVolumeBefore = tableau.computeFractionalVolume(true);
                    tableau.applyMIRCuts();
                    tableau.simplex();
                    const fractionalVolumeAfter = tableau.computeFractionalVolume(true);
                    mirIterations++;
                    if (fractionalVolumeAfter >= 0.9 * fractionalVolumeBefore) {
                        fractionalVolumeImproved = false;
                    }
                }
            }
        };
        const branchAndCut = (tableau) => {
            var _a, _b, _c, _d, _e;
            const branches = new BranchMinHeap();
            const depthFirstStack = [];
            let iterations = 0;
            const tolerance = (_b = (_a = tableau.model) === null || _a === void 0 ? void 0 : _a.tolerance) !== null && _b !== void 0 ? _b : 0;
            let toleranceFlag = true;
            let terminalTime = 1e99;
            if ((_c = tableau.model) === null || _c === void 0 ? void 0 : _c.timeout) {
                terminalTime = Date.now() + tableau.model.timeout;
            }
            let bestEvaluation = Infinity;
            let bestBranch = null;
            const bestOptionalObjectivesEvaluations = [];
            for (let oInit = 0; oInit < tableau.optionalObjectives.length; oInit += 1) {
                bestOptionalObjectivesEvaluations.push(Infinity);
            }
            // Configuration for hybrid node selection
            const switchTobestFirstAfterSolutions = 1;
            let solutionsFound = 0;
            let useDepthFirst = nodeSelection === "depth-first" || nodeSelection === "hybrid";
            const branch = createBranch$1(-Infinity, [], 0);
            let acceptableThreshold;
            if (useDepthFirst) {
                depthFirstStack.push(branch);
            }
            else {
                branches.push(branch);
            }
            while ((useDepthFirst ? depthFirstStack.length > 0 : !branches.isEmpty()) &&
                toleranceFlag === true &&
                Date.now() < terminalTime) {
                if ((_d = tableau.model) === null || _d === void 0 ? void 0 : _d.isMinimization) {
                    acceptableThreshold = tableau.bestPossibleEval * (1 + tolerance);
                }
                else {
                    acceptableThreshold = tableau.bestPossibleEval * (1 - tolerance);
                }
                if (tolerance > 0 && bestEvaluation < acceptableThreshold) {
                    toleranceFlag = false;
                }
                // Select next node based on strategy
                let activeBranch;
                if (useDepthFirst && depthFirstStack.length > 0) {
                    activeBranch = depthFirstStack.pop();
                }
                else if (!branches.isEmpty()) {
                    activeBranch = branches.pop();
                }
                else {
                    break;
                }
                if (activeBranch.relaxedEvaluation >= bestEvaluation) {
                    continue;
                }
                const cuts = activeBranch.cuts;
                tableau.evaluation;
                applyCuts(tableau, cuts);
                iterations++;
                if (!tableau.feasible) {
                    continue;
                }
                const evaluation = tableau.evaluation;
                if (evaluation > bestEvaluation) {
                    continue;
                }
                // Update pseudocosts based on observed improvement
                if (activeBranch.branchVarIndex !== undefined &&
                    activeBranch.branchDirection !== undefined &&
                    activeBranch.branchFractionality !== undefined &&
                    activeBranch.parentEvaluation !== undefined) {
                    const improvement = Math.abs(evaluation - activeBranch.parentEvaluation);
                    updatePseudoCost(activeBranch.branchVarIndex, activeBranch.branchDirection, improvement, activeBranch.branchFractionality);
                }
                if (evaluation === bestEvaluation) {
                    let isCurrentEvaluationWorse = true;
                    for (let o = 0; o < tableau.optionalObjectives.length; o++) {
                        if (tableau.optionalObjectives[o].reducedCosts[0] >
                            bestOptionalObjectivesEvaluations[o]) {
                            break;
                        }
                        else if (tableau.optionalObjectives[o].reducedCosts[0] <
                            bestOptionalObjectivesEvaluations[o]) {
                            isCurrentEvaluationWorse = false;
                            break;
                        }
                    }
                    if (isCurrentEvaluationWorse) {
                        continue;
                    }
                }
                if (tableau.isIntegral()) {
                    tableau.__isIntegral = true;
                    solutionsFound++;
                    if (iterations === 1) {
                        tableau.branchAndCutIterations = iterations;
                        return;
                    }
                    bestBranch = activeBranch;
                    bestEvaluation = evaluation;
                    for (let oCopy = 0; oCopy < tableau.optionalObjectives.length; oCopy++) {
                        bestOptionalObjectivesEvaluations[oCopy] =
                            tableau.optionalObjectives[oCopy].reducedCosts[0];
                    }
                    if ((_e = tableau.model) === null || _e === void 0 ? void 0 : _e.keep_solutions) {
                        const nowSolution = tableau.model.tableau.getSolution();
                        const store = nowSolution.generateSolutionSet();
                        store.result = nowSolution.evaluation;
                        if (!tableau.model.solutions) {
                            tableau.model.solutions = [];
                        }
                        tableau.model.solutions.push(store);
                    }
                    // Switch to best-first after finding solutions
                    if (nodeSelection === "hybrid" &&
                        solutionsFound >= switchTobestFirstAfterSolutions) {
                        useDepthFirst = false;
                        // Move remaining depth-first nodes to priority queue
                        while (depthFirstStack.length > 0) {
                            branches.push(depthFirstStack.pop());
                        }
                    }
                }
                else {
                    if (iterations === 1) {
                        tableau.save();
                    }
                    // Use enhanced branching variable selection
                    const variable = selectBranchingVariable(tableau);
                    if (!variable)
                        continue;
                    const varIndex = variable.index;
                    const varValue = variable.value;
                    const cutsHigh = [];
                    const cutsLow = [];
                    const nCuts = cuts.length;
                    for (let c = 0; c < nCuts; c++) {
                        const cut = cuts[c];
                        if (cut.varIndex === varIndex) {
                            if (cut.type === "min") {
                                cutsLow.push(cut);
                            }
                            else {
                                cutsHigh.push(cut);
                            }
                        }
                        else {
                            cutsHigh.push(cut);
                            cutsLow.push(cut);
                        }
                    }
                    const ceilVal = Math.ceil(varValue);
                    const floorVal = Math.floor(varValue);
                    const fracUp = ceilVal - varValue; // Distance to ceil
                    const fracDown = varValue - floorVal; // Distance to floor
                    const cutHigh = createCut$1("min", varIndex, ceilVal);
                    cutsHigh.push(cutHigh);
                    const cutLow = createCut$1("max", varIndex, floorVal);
                    cutsLow.push(cutLow);
                    const newDepth = activeBranch.depth + 1;
                    if (useDepthFirst) {
                        // Push in reverse order so 'up' branch is explored first
                        // (often better for minimization with binary vars)
                        depthFirstStack.push(createBranch$1(evaluation, cutsLow, newDepth, varIndex, "down", fracDown, evaluation));
                        depthFirstStack.push(createBranch$1(evaluation, cutsHigh, newDepth, varIndex, "up", fracUp, evaluation));
                    }
                    else {
                        branches.push(createBranch$1(evaluation, cutsHigh, newDepth, varIndex, "up", fracUp, evaluation));
                        branches.push(createBranch$1(evaluation, cutsLow, newDepth, varIndex, "down", fracDown, evaluation));
                    }
                }
            }
            if (bestBranch !== null) {
                applyCuts(tableau, bestBranch.cuts);
            }
            tableau.branchAndCutIterations = iterations;
        };
        return { applyCuts, branchAndCut };
    }

    function createCheckpoint(tableau) {
        return {
            matrix: new Float64Array(tableau.matrix),
            width: tableau.width,
            height: tableau.height,
            nVars: tableau.nVars,
            varIndexByRow: tableau.varIndexByRow.slice(),
            varIndexByCol: tableau.varIndexByCol.slice(),
            rowByVarIndex: tableau.rowByVarIndex.slice(),
            colByVarIndex: tableau.colByVarIndex.slice(),
            availableIndexes: tableau.availableIndexes.slice(),
            lastElementIndex: tableau.lastElementIndex,
            evaluation: tableau.evaluation,
            feasible: tableau.feasible,
        };
    }
    function restoreCheckpoint(tableau, checkpoint) {
        // Only copy if sizes match, otherwise need full restore
        if (tableau.matrix.length >= checkpoint.matrix.length) {
            tableau.matrix.set(checkpoint.matrix);
        }
        else {
            tableau.matrix = new Float64Array(checkpoint.matrix);
        }
        tableau.width = checkpoint.width;
        tableau.height = checkpoint.height;
        tableau.nVars = checkpoint.nVars;
        // Restore arrays
        const height = checkpoint.height;
        for (let i = 0; i < height; i++) {
            tableau.varIndexByRow[i] = checkpoint.varIndexByRow[i];
        }
        tableau.varIndexByRow.length = height;
        const width = checkpoint.width;
        for (let i = 0; i < width; i++) {
            tableau.varIndexByCol[i] = checkpoint.varIndexByCol[i];
        }
        tableau.varIndexByCol.length = width;
        const nVars = checkpoint.nVars;
        for (let i = 0; i < nVars; i++) {
            tableau.rowByVarIndex[i] = checkpoint.rowByVarIndex[i];
            tableau.colByVarIndex[i] = checkpoint.colByVarIndex[i];
        }
        tableau.availableIndexes = checkpoint.availableIndexes.slice();
        tableau.lastElementIndex = checkpoint.lastElementIndex;
        tableau.evaluation = checkpoint.evaluation;
        tableau.feasible = checkpoint.feasible;
    }
    function createCut(type, varIndex, value) {
        return { type, varIndex, value };
    }
    function createBranch(relaxedEvaluation, cuts, depth, parentCheckpoint, newCut) {
        return { relaxedEvaluation, cuts, depth, parentCheckpoint, newCut };
    }
    function createIncrementalBranchAndCutService(options = {}) {
        const { nodeSelection = "hybrid", branching = "pseudocost", maxCheckpoints = 50, // Limit checkpoints to avoid memory overhead
         } = options;
        const pseudoCosts = new Map();
        const getPseudoCost = (varIndex) => {
            let data = pseudoCosts.get(varIndex);
            if (!data) {
                data = { upSum: 0, upCount: 0, downSum: 0, downCount: 0 };
                pseudoCosts.set(varIndex, data);
            }
            return data;
        };
        const updatePseudoCost = (varIndex, direction, improvement, fraction) => {
            const data = getPseudoCost(varIndex);
            const normalizedImprovement = improvement / (direction === "up" ? 1 - fraction : fraction);
            if (direction === "up") {
                data.upSum += normalizedImprovement;
                data.upCount++;
            }
            else {
                data.downSum += normalizedImprovement;
                data.downCount++;
            }
        };
        const getScore = (varIndex, fraction) => {
            const data = getPseudoCost(varIndex);
            const upPseudo = data.upCount > 0 ? data.upSum / data.upCount : 1;
            const downPseudo = data.downCount > 0 ? data.downSum / data.downCount : 1;
            const upEstimate = upPseudo * (1 - fraction);
            const downEstimate = downPseudo * fraction;
            return Math.max(upEstimate, 1e-6) * Math.max(downEstimate, 1e-6);
        };
        const selectBranchingVariable = (tableau) => {
            const width = tableau.width;
            const matrix = tableau.matrix;
            const rhsColumn = tableau.rhsColumn;
            const integerVars = tableau.model.integerVariables;
            const precision = tableau.precision;
            const candidates = [];
            for (const variable of integerVars) {
                const varIndex = variable.index;
                const row = tableau.rowByVarIndex[varIndex];
                if (row !== -1) {
                    const value = matrix[row * width + rhsColumn];
                    const fraction = Math.abs(value - Math.round(value));
                    if (fraction > precision) {
                        candidates.push({ index: varIndex, value, fraction });
                    }
                }
            }
            if (candidates.length === 0)
                return null;
            if (branching === "most-fractional") {
                candidates.sort((a, b) => b.fraction - a.fraction);
                return candidates[0];
            }
            // Pseudocost branching
            let bestScore = -Infinity;
            let bestCandidate = candidates[0];
            for (const candidate of candidates) {
                const score = getScore(candidate.index, candidate.fraction);
                if (score > bestScore) {
                    bestScore = score;
                    bestCandidate = candidate;
                }
            }
            return bestCandidate;
        };
        // Standard applyCuts - restores to root and applies all cuts
        const applyCuts = (tableau, branchingCuts) => {
            var _a;
            tableau.restore();
            tableau.addCutConstraints(branchingCuts);
            tableau.simplex();
            if (((_a = tableau.model) === null || _a === void 0 ? void 0 : _a.useMIRCuts) && tableau.feasible) {
                let fractionalVolumeImproved = true;
                let mirIterations = 0;
                const maxMIRIterations = 3;
                while (fractionalVolumeImproved && mirIterations < maxMIRIterations) {
                    const fractionalVolumeBefore = tableau.computeFractionalVolume(true);
                    tableau.applyMIRCuts();
                    tableau.simplex();
                    const fractionalVolumeAfter = tableau.computeFractionalVolume(true);
                    mirIterations++;
                    if (fractionalVolumeAfter >= 0.9 * fractionalVolumeBefore) {
                        fractionalVolumeImproved = false;
                    }
                }
            }
        };
        // Incremental applyCuts - uses parent checkpoint if available
        const applyIncrementalCuts = (tableau, branch) => {
            var _a;
            if (branch.parentCheckpoint && branch.newCut) {
                // Fast path: restore parent and apply only new cut
                restoreCheckpoint(tableau, branch.parentCheckpoint);
                tableau.addCutConstraints([branch.newCut]);
                tableau.simplex();
            }
            else {
                // Fallback: full restore from root
                tableau.restore();
                tableau.addCutConstraints(branch.cuts);
                tableau.simplex();
            }
            if (((_a = tableau.model) === null || _a === void 0 ? void 0 : _a.useMIRCuts) && tableau.feasible) {
                let fractionalVolumeImproved = true;
                let mirIterations = 0;
                const maxMIRIterations = 3;
                while (fractionalVolumeImproved && mirIterations < maxMIRIterations) {
                    const fractionalVolumeBefore = tableau.computeFractionalVolume(true);
                    tableau.applyMIRCuts();
                    tableau.simplex();
                    const fractionalVolumeAfter = tableau.computeFractionalVolume(true);
                    mirIterations++;
                    if (fractionalVolumeAfter >= 0.9 * fractionalVolumeBefore) {
                        fractionalVolumeImproved = false;
                    }
                }
            }
        };
        const branchAndCut = (tableau) => {
            var _a, _b, _c, _d, _e;
            const branches = new BranchMinHeap();
            const depthFirstStack = [];
            let iterations = 0;
            let checkpointCount = 0;
            const tolerance = (_b = (_a = tableau.model) === null || _a === void 0 ? void 0 : _a.tolerance) !== null && _b !== void 0 ? _b : 0;
            let toleranceFlag = true;
            let terminalTime = 1e99;
            if ((_c = tableau.model) === null || _c === void 0 ? void 0 : _c.timeout) {
                terminalTime = Date.now() + tableau.model.timeout;
            }
            let bestEvaluation = Infinity;
            let bestBranch = null;
            const bestOptionalObjectivesEvaluations = [];
            for (let oInit = 0; oInit < tableau.optionalObjectives.length; oInit++) {
                bestOptionalObjectivesEvaluations.push(Infinity);
            }
            const switchToBestFirstAfterSolutions = 1;
            let solutionsFound = 0;
            let useDepthFirst = nodeSelection === "depth-first" || nodeSelection === "hybrid";
            const rootBranch = createBranch(-Infinity, [], 0);
            if (useDepthFirst) {
                depthFirstStack.push(rootBranch);
            }
            else {
                branches.push(rootBranch);
            }
            while ((useDepthFirst ? depthFirstStack.length > 0 : !branches.isEmpty()) &&
                toleranceFlag === true &&
                Date.now() < terminalTime) {
                let acceptableThreshold;
                if ((_d = tableau.model) === null || _d === void 0 ? void 0 : _d.isMinimization) {
                    acceptableThreshold = tableau.bestPossibleEval * (1 + tolerance);
                }
                else {
                    acceptableThreshold = tableau.bestPossibleEval * (1 - tolerance);
                }
                if (tolerance > 0 && bestEvaluation < acceptableThreshold) {
                    toleranceFlag = false;
                }
                let activeBranch;
                if (useDepthFirst && depthFirstStack.length > 0) {
                    activeBranch = depthFirstStack.pop();
                }
                else if (!branches.isEmpty()) {
                    activeBranch = branches.pop();
                }
                else {
                    break;
                }
                if (activeBranch.relaxedEvaluation >= bestEvaluation) {
                    continue;
                }
                const parentEval = tableau.evaluation;
                // Use incremental restoration if available
                applyIncrementalCuts(tableau, activeBranch);
                iterations++;
                if (!tableau.feasible) {
                    continue;
                }
                const evaluation = tableau.evaluation;
                if (evaluation > bestEvaluation) {
                    continue;
                }
                // Update pseudocosts
                if (activeBranch.newCut && parentEval !== 0) {
                    const improvement = Math.abs(evaluation - parentEval);
                    const fraction = 0.5;
                    updatePseudoCost(activeBranch.newCut.varIndex, activeBranch.newCut.type === "min" ? "up" : "down", improvement, fraction);
                }
                if (evaluation === bestEvaluation) {
                    let isCurrentEvaluationWorse = true;
                    for (let o = 0; o < tableau.optionalObjectives.length; o++) {
                        if (tableau.optionalObjectives[o].reducedCosts[0] >
                            bestOptionalObjectivesEvaluations[o]) {
                            break;
                        }
                        else if (tableau.optionalObjectives[o].reducedCosts[0] <
                            bestOptionalObjectivesEvaluations[o]) {
                            isCurrentEvaluationWorse = false;
                            break;
                        }
                    }
                    if (isCurrentEvaluationWorse) {
                        continue;
                    }
                }
                if (tableau.isIntegral()) {
                    tableau.__isIntegral = true;
                    solutionsFound++;
                    if (iterations === 1) {
                        tableau.branchAndCutIterations = iterations;
                        return;
                    }
                    bestBranch = activeBranch;
                    bestEvaluation = evaluation;
                    for (let oCopy = 0; oCopy < tableau.optionalObjectives.length; oCopy++) {
                        bestOptionalObjectivesEvaluations[oCopy] =
                            tableau.optionalObjectives[oCopy].reducedCosts[0];
                    }
                    if ((_e = tableau.model) === null || _e === void 0 ? void 0 : _e.keep_solutions) {
                        const nowSolution = tableau.model.tableau.getSolution();
                        const store = nowSolution.generateSolutionSet();
                        store.result = nowSolution.evaluation;
                        if (!tableau.model.solutions) {
                            tableau.model.solutions = [];
                        }
                        tableau.model.solutions.push(store);
                    }
                    // Switch to best-first after finding solutions
                    if (nodeSelection === "hybrid" &&
                        solutionsFound >= switchToBestFirstAfterSolutions) {
                        useDepthFirst = false;
                        while (depthFirstStack.length > 0) {
                            branches.push(depthFirstStack.pop());
                        }
                    }
                }
                else {
                    if (iterations === 1) {
                        tableau.save();
                    }
                    const variable = selectBranchingVariable(tableau);
                    if (!variable)
                        continue;
                    const varIndex = variable.index;
                    const varValue = variable.value;
                    // Create checkpoint for children (only if under limit)
                    let checkpoint;
                    if (useDepthFirst && checkpointCount < maxCheckpoints) {
                        checkpoint = createCheckpoint(tableau);
                        checkpointCount++;
                    }
                    const cutsHigh = [];
                    const cutsLow = [];
                    const nCuts = activeBranch.cuts.length;
                    for (let c = 0; c < nCuts; c++) {
                        const cut = activeBranch.cuts[c];
                        if (cut.varIndex === varIndex) {
                            if (cut.type === "min") {
                                cutsLow.push(cut);
                            }
                            else {
                                cutsHigh.push(cut);
                            }
                        }
                        else {
                            cutsHigh.push(cut);
                            cutsLow.push(cut);
                        }
                    }
                    const min = Math.ceil(varValue);
                    const max = Math.floor(varValue);
                    const cutHigh = createCut("min", varIndex, min);
                    cutsHigh.push(cutHigh);
                    const cutLow = createCut("max", varIndex, max);
                    cutsLow.push(cutLow);
                    const newDepth = activeBranch.depth + 1;
                    if (useDepthFirst) {
                        // Push with parent checkpoint for incremental restoration
                        depthFirstStack.push(createBranch(evaluation, cutsLow, newDepth, checkpoint, cutLow));
                        depthFirstStack.push(createBranch(evaluation, cutsHigh, newDepth, checkpoint, cutHigh));
                    }
                    else {
                        // Best-first doesn't use checkpoints (would need too much memory)
                        branches.push(createBranch(evaluation, cutsHigh, newDepth));
                        branches.push(createBranch(evaluation, cutsLow, newDepth));
                    }
                }
            }
            if (bestBranch !== null) {
                applyCuts(tableau, bestBranch.cuts);
            }
            tableau.branchAndCutIterations = iterations;
        };
        return { applyCuts, branchAndCut };
    }

    /**
     * @file src/main.ts
     * @description Core Solver class implementation
     *
     * Orchestrates the complete solving pipeline:
     * - Model parsing and validation
     * - Simplex algorithm for linear programming
     * - Branch-and-cut for mixed-integer programming
     * - Multi-objective optimization via Polyopt
     * - External solver delegation (e.g., lp_solve)
     */
    /**
     * Main solver class providing the public API for solving optimization problems.
     */
    class Solver {
        constructor() {
            // Expose constructors for programmatic model building
            this.Model = Model;
            this.Tableau = Tableau;
            this.Constraint = Constraint;
            this.Variable = Variable;
            this.Numeral = Numeral;
            this.Term = Term;
            // External solver integrations
            this.External = External;
            this.ReformatLP = ReformatLP;
            // Branch-and-cut service (default implementation)
            this.branchAndCutService = createBranchAndCutService();
            this.branchAndCut = (tableau) => this.branchAndCutService.branchAndCut(tableau);
            // Reference to the last solved model (useful for debugging)
            this.lastSolvedModel = null;
        }
        /**
         * Select the appropriate branch-and-cut service based on model options.
         *
         * Enhanced strategies can be enabled via model.options:
         * - nodeSelection: 'best-first' | 'depth-first' | 'hybrid'
         * - branching: 'most-fractional' | 'pseudocost' | 'strong'
         * - useIncremental: true to use incremental state management (experimental)
         */
        selectBranchAndCutService(model) {
            var _a, _b, _c, _d;
            const options = model.options;
            const useEnhanced = (options === null || options === void 0 ? void 0 : options.nodeSelection) || (options === null || options === void 0 ? void 0 : options.branching);
            const useIncremental = (options === null || options === void 0 ? void 0 : options.useIncremental) === true; // Must explicitly enable
            if (useIncremental) {
                return createIncrementalBranchAndCutService({
                    nodeSelection: (_a = options === null || options === void 0 ? void 0 : options.nodeSelection) !== null && _a !== void 0 ? _a : "hybrid",
                    branching: (_b = options === null || options === void 0 ? void 0 : options.branching) !== null && _b !== void 0 ? _b : "pseudocost",
                });
            }
            if (useEnhanced) {
                return createEnhancedBranchAndCutService({
                    nodeSelection: (_c = options === null || options === void 0 ? void 0 : options.nodeSelection) !== null && _c !== void 0 ? _c : "hybrid",
                    branching: (_d = options === null || options === void 0 ? void 0 : options.branching) !== null && _d !== void 0 ? _d : "pseudocost",
                    useDiving: true,
                });
            }
            return createBranchAndCutService();
        }
        /**
         * Solve a linear or mixed-integer programming problem.
         *
         * @param model - Problem definition (JSON format or Model instance)
         * @param precision - Tolerance for integer constraints (default: 1e-9)
         * @param full - If true, return full Solution object; otherwise return simplified result
         * @param validate - If true, run model through validation functions
         * @returns Solution object or simplified result with variable values
         */
        Solve(model, precision, full, validate) {
            // Run validation if requested
            if (validate) {
                for (const test in validation) {
                    const validator = validation[test];
                    if (typeof validator === "function") {
                        model = validator(model);
                    }
                }
            }
            if (!model) {
                throw new Error("Solver requires a model to operate on");
            }
            // Handle multi-objective optimization
            if (typeof model.optimize === "object") {
                if (Object.keys(model.optimize).length > 1) {
                    return Polyopt(this, model);
                }
            }
            // Handle external solver delegation
            if (model.external) {
                return this.solveWithExternalSolver(model);
            }
            // Solve with internal solver
            let modelInstance;
            if (!(model instanceof Model)) {
                const branchAndCutService = this.selectBranchAndCutService(model);
                modelInstance = new Model(precision, undefined, branchAndCutService).loadJson(model);
            }
            else {
                modelInstance = model;
            }
            const solution = modelInstance.solve();
            this.lastSolvedModel = modelInstance;
            solution.solutionSet = solution.generateSolutionSet();
            // Return full solution or simplified result
            if (full) {
                return solution;
            }
            return this.buildSimplifiedResult(solution);
        }
        /**
         * Delegate solving to an external solver (e.g., lp_solve).
         */
        solveWithExternalSolver(model) {
            var _a;
            const solvers = Object.keys(External);
            const solverList = JSON.stringify(solvers);
            if (!((_a = model.external) === null || _a === void 0 ? void 0 : _a.solver)) {
                throw new Error(`Model has 'external' object without solver attribute. Available: ${solverList}`);
            }
            const requestedSolver = model.external.solver;
            if (!External[requestedSolver]) {
                throw new Error(`Solver '${requestedSolver}' not supported. Available: ${solverList}`);
            }
            return External[requestedSolver].solve(model);
        }
        /**
         * Build a simplified result object from a full solution.
         */
        buildSimplifiedResult(solution) {
            const result = {
                feasible: solution.feasible,
                result: solution.evaluation,
                bounded: solution.bounded,
            };
            if (solution._tableau.__isIntegral) {
                result.isIntegral = true;
            }
            // Add non-zero variable values
            for (const varId of Object.keys(solution.solutionSet)) {
                const value = solution.solutionSet[varId];
                if (value !== 0) {
                    result[varId] = value;
                }
            }
            return result;
        }
        /**
         * Solve a multi-objective optimization problem.
         *
         * Returns a compromise solution using the mid-point formula between
         * individually optimized objectives.
         *
         * @example
         * const model = {
         *     optimize: { profit: "max", risk: "min" },
         *     constraints: { budget: { max: 1000 } },
         *     variables: { ... }
         * };
         * const result = solver.MultiObjective(model);
         */
        MultiObjective(model) {
            return Polyopt(this, model);
        }
    }
    // Create singleton instance
    const solver = new Solver();
    // UMD module exports for various environments
    if (typeof define === "function") {
        // AMD (RequireJS)
        define([], () => solver);
    }
    else if (typeof window === "object") {
        // Browser global
        window.solver = solver;
    }
    else if (typeof self === "object") {
        // Web Worker
        self.solver = solver;
    }

    /**
     * @file src/solver.ts
     * @description Main entry point for jsLPSolver library
     *
     * Re-exports the solver instance and all public types. This is the primary
     * import target for library consumers.
     *
     * @example
     * import solver from "javascript-lp-solver";
     * const result = solver.Solve(model);
     */

    return solver;

})();


  return solver;
  })());
  const PID = 'fpl-analyst-root';
  const prev = document.getElementById(PID);
  if (prev) { prev.remove(); return; }
  if (!/fantasy\.premierleague\.com$/.test(location.hostname)) {
    
    return;
  }
  const host = document.createElement('div');
  host.id = PID;
  host.style.cssText = 'position:fixed;inset:0;z-index:2147483646;';
  document.documentElement.appendChild(host);
  const R = host.attachShadow({ mode: 'open' });

  const CSS = `
@keyframes hot{50%{box-shadow:0 0 0 4px rgba(179,38,30,.25)}}
@keyframes spin{to{transform:rotate(360deg)}}
@keyframes sheetUp{0%{transform:translateY(100%)}to{transform:none}}
@keyframes sheetDown{to{transform:translateY(100%)}}
@keyframes fadeIn{0%{opacity:0}}
@keyframes fadeOut{to{opacity:0}}
@keyframes shim{to{background-position:-200%0}}
@keyframes gpop{0%{transform:scale(.2);opacity:0}to{transform:none;opacity:1}}
@keyframes cf{0%{opacity:1;transform:translate(0,0) rotate(0)}to{opacity:0;transform:translate(var(--x),var(--y)) rotate(var(--r))}}
@keyframes pulse{0%{box-shadow:0 0 0 0 rgba(69,208,143,.6)}to{box-shadow:0 0 0 9px transparent}}
@keyframes swayA{to{transform:rotate(-19deg)}}
@keyframes swayB{to{transform:rotate(19deg)}}
@keyframes haze{to{transform:translateX(4%) scale(1.05)}}
@keyframes drift{to{transform:translate(8%,6%) scale(1.12)}}
@keyframes wipeR{0%{transform:skewX(-16deg) translateX(0)}to{transform:skewX(-16deg) translateX(190%)}}
@keyframes vinR{0%{opacity:0;transform:translateX(28px)}to{opacity:1;transform:none}}
@keyframes vinL{0%{opacity:0;transform:translateX(-28px)}to{opacity:1;transform:none}}
@keyframes vinF{0%{opacity:0}to{opacity:1}}
@keyframes rise{0%{opacity:0;transform:translateY(12px)}to{opacity:1;transform:none}}
@keyframes drop{0%{opacity:0;transform:translateY(-26px) scale(.8)}to{opacity:1;transform:none}}
@keyframes mwp{50%{opacity:.25}}
:host{all:initial}
*{box-sizing:border-box}
[hidden]{display:none!important}
.root{--bg:#0f1524;--raised:#161e30;--card:#18213a;--overlay:#202a44;--fg:#e9edf5;--mut:#aeb8cb;--t3:#8a97ad;--line:rgba(255,255,255,.08);--gold:#f6c343;--d1:#1e8e5a;--d2:#3fbf7f;--d3:#8a97ab;--d4:#e0675f;--d5:#a83246;--fd:"Barlow Semi Condensed","Arial Narrow",sans-serif;--ease:cubic-bezier(.2,.8,.2,1);--m:1;--acc:#45d08f;--acc2:#0f3a1d;--pur:#7b2cff;--pl:#37003c;--fh:"Barlow Semi Condensed","Arial Narrow",sans-serif;--good:#3fdc8a;--goodbg:#10382a;--warn:#f6b93f;--warnbg:#3d2f0f;--bad:#ff6f6f;--badbg:#42191d;--neu:#1b2942;color:var(--fg)}
.scrim{position:fixed;inset:0;background:rgba(10,14,12,.55)}
.panel{position:fixed;inset:2vh 0 2vh 0;margin:0 auto;width:min(1180px,calc(100vw - 16px));border-radius:14px;display:flex;flex-direction:column;overflow:hidden;box-shadow:0 20px 60px rgba(0,0,0,.35)}
.top,form{display:flex;align-items:center}
.top{flex-wrap:wrap;background:var(--card)}
.brand{display:flex;margin-right:auto}
.brand b{font-size:16px}
.brand span,.kpi span{font-size:12px;color:var(--mut)}
form{gap:8px}
label{font-size:12px;text-transform:uppercase;letter-spacing:.06em}
button,input{font:inherit;border-radius:8px}
input{width:130px;padding:7px 10px;border:1px solid var(--line);background:var(--bg);color:var(--fg)}
button{cursor:pointer;border:1px solid transparent;padding:7px 14px}
.go{background:var(--acc);color:var(--card);font-weight:600}
.x,label{color:var(--mut)}
.x{background:0 0;font-size:26px;line-height:1;padding:4px 10px}
a:focus-visible,button:focus-visible,input:focus-visible{outline:2px solid var(--acc);outline-offset:2px}
main,nav{display:flex}
nav{flex-wrap:wrap;background:var(--card)}
nav a,td,th{white-space:nowrap}
nav a,section.s{border:1px solid var(--line)}
nav a{text-decoration:none}
nav a:hover{background:var(--neu)}
main{overflow-x:hidden;overflow-y:auto;flex-direction:column;gap:16px;padding:16px 16px 24px}
section.s{background:var(--card);background:rgba(18,29,49,.86);background:rgba(17,28,47,.78);border-radius:16px;padding:20px;backdrop-filter:blur(4px)}
h2{font-size:16px;margin:0 0 4px}
.sub{margin:0 0 12px}
.kpis{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:10px}
.kpi,.plan li{border:1px solid var(--line);border-radius:10px;padding:10px 12px;background:var(--bg)}
.bars i,.kpi small{display:block}
.kpi b,table{font-variant-numeric:tabular-nums}
.kpi b{display:block;margin-top:2px}
.plan{margin:0;padding:0;list-style:none;display:flex;flex-direction:column;gap:8px}
.alt a,.cols3 li a,.plan li a{color:var(--fg)}
.plan li{display:flex;gap:10px}
.tag{flex:none;font-size:11px;font-weight:700;letter-spacing:.05em;text-transform:uppercase;padding:2px 8px;border-radius:999px;background:var(--acc2);color:var(--acc);margin-top:1px}
.tw{overflow-x:auto}
table{border-collapse:collapse;width:100%}
td,th{padding:7px 8px;border-bottom:1px solid var(--line);text-align:left;vertical-align:middle}
.pl small,th{color:var(--mut)}
th{text-transform:uppercase;letter-spacing:.05em}
td.n,th.n{text-align:right}
tr.bench td{opacity:.72}
.pl b{font-weight:600}
.pl small{margin-left:4px}
.fx{display:inline-flex;gap:3px}
.f,th{font-size:11px;font-weight:600}
.f{display:inline-block;text-align:center;padding:2px 4px;border-radius:5px}
.d1,.d2{background:var(--goodbg);color:var(--good)}
.d3{background:var(--neu);color:var(--mut)}
.d4{background:var(--warnbg);color:var(--warn)}
.d5{background:var(--badbg);color:var(--bad)}
.dx{background:0 0;color:var(--mut);border:1px dashed var(--line)}
.pill{display:inline-block;font-size:11px;font-weight:700;padding:2px 8px;border-radius:999px;letter-spacing:.03em}
.p-core{background:var(--acc2);color:var(--acc)}
.p-keep{background:var(--neu);color:var(--mut)}
.p-up{background:var(--warnbg);color:var(--warn)}
.p-out,.p-sell{background:var(--badbg);color:var(--bad)}
.news{font-size:12px;white-space:normal;max-width:220px}
.root .cv .up,.root .kpi .up,.root .kpi span.up,.root .up,.root small.up{color:var(--good)}
.news,.ppill b.dn,.root .cv .dn,.root .dn,.root .kpi .dn,.root .kpi span.dn,.root small.dn,.tile.alertt h3{color:var(--bad)}
.grid2{display:grid;grid-template-columns:repeat(auto-fit,minmax(320px,1fr));gap:14px}
.move{border:1px solid var(--line);border-radius:10px;padding:12px;background:var(--bg);display:flex;flex-direction:column;gap:6px}
.move .h{display:flex;justify-content:space-between;gap:8px;align-items:baseline;flex-wrap:wrap}
.gain{font-weight:700;color:var(--good)}
.alt{font-size:13px;color:var(--mut)}
.pitch{border:1px solid #2f9c5c;background:repeating-linear-gradient(180deg,#1f8a4d 0 64px,#1b7d45 64px 128px)}
.row{display:flex;flex-wrap:wrap;justify-content:center;gap:8px}
.chip{background:var(--card);border:1px solid var(--line);border-radius:8px;padding:6px 10px;text-align:center;min-width:96px}
.chip b{display:block;font-size:13px}
.bars div,.chip span{font-size:12px;color:var(--mut)}
.chip.c,button.tile:hover{border-color:var(--acc);box-shadow:0 0 0 1px var(--acc) inset}
.benchrow{display:flex;flex-wrap:wrap;gap:8px;margin-top:10px}
.chips{display:grid;grid-template-columns:repeat(auto-fit,minmax(240px,1fr));gap:12px}
.bars{display:flex;align-items:flex-end;gap:4px;height:70px;margin-top:8px}
.bars div{flex:1;display:flex;flex-direction:column;align-items:center;justify-content:flex-end;gap:2px;font-size:11px;height:100%}
.bars i{width:100%;background:var(--line);border-radius:3px 3px 0 0}
.bars .best i{background:var(--acc)}
.form{display:inline-flex;gap:2px}
.form i{font-style:normal;font-size:11px;font-weight:700;width:16px;height:16px;line-height:16px;text-align:center;border-radius:3px}
.fW{background:var(--goodbg);color:var(--good)}
.fD{background:var(--neu);color:var(--mut)}
.fL{background:var(--badbg);color:var(--bad)}
tr.mine td:first-child{box-shadow:inset 3px 0 0 var(--acc)}
.err{padding:12px;border-radius:10px;background:var(--badbg);color:var(--bad)}
svg text{fill:var(--mut);font-size:11px}
.note{font-size:12px;color:var(--mut);margin-top:10px}
.links a,.pn{text-decoration:none}
.pn{color:var(--fg);text-decoration:none}
.pn:hover{color:var(--acc);border-bottom-color:var(--acc)}
.drawer,.dx{top:0;background:var(--card)}
.drawer{position:absolute;right:0;bottom:0;width:min(560px,100%);border-left:1px solid var(--line);box-shadow:-12px 0 40px rgba(0,0,0,.25);overflow:auto;padding:18px;z-index:5}
.dx{position:sticky;float:right}
.cols3 ul,.links{display:flex;gap:8px}
.links{flex-wrap:wrap}
.links a{color:var(--acc);border:1px solid var(--line);border-radius:999px;padding:5px 12px;font-size:13px}
.links a:hover,.try:hover{background:var(--acc2)}
.kind{display:inline-block;font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:.05em;padding:1px 6px;border-radius:4px;background:var(--neu);color:var(--mut);margin-right:6px}
.k-leak{background:var(--warnbg);color:var(--warn)}
.k-social{background:var(--acc2);color:var(--acc)}
.srcs{display:flex;flex-wrap:wrap;gap:6px;margin:4px 0 12px}
.kpi .was,.srcs span{font-size:12px;color:var(--mut)}
.srcs span{padding:2px 8px;border-radius:999px;border:1px solid var(--line)}
.srcs span.on{border-color:var(--acc);color:var(--acc)}
.cols3{display:grid;grid-template-columns:repeat(auto-fit,minmax(280px,1fr));gap:14px}
.cols3 ul{list-style:none;margin:0;padding:0;flex-direction:column}
.cols3 li{font-size:13px;line-height:1.4}
.p-diff{background:#efe3fb}
@media (prefers-color-scheme:dark){
  .p-diff{background:#33214a;color:#cfa9f5}
}
.try{font:inherit;font-size:13px;background:0 0;border:1px solid var(--acc);color:var(--acc);border-radius:999px;padding:4px 12px;cursor:pointer}
.kpi .was{display:block}
.plgrid{display:grid;align-items:start}
@media (max-width:860px){
  .plgrid{grid-template-columns:1fr}
}
.plside{display:flex;flex-direction:column;gap:10px;min-width:0}
.kpis.two{grid-template-columns:repeat(2,minmax(0,1fr))}
.chip{position:relative}
.chip.new{border-color:var(--good);box-shadow:0 0 0 1px var(--good) inset}
.chip.empty{border-style:dashed;background:0 0;color:var(--mut)}
.row.bench{border-top:1px dashed var(--line);padding-top:8px;opacity:.85}
.warns{margin:0;padding-left:18px;color:var(--bad);font-size:13px}
.livebar b,.ok{color:var(--good)}
.ok{font-weight:600;margin:0}
table.cmp{margin-bottom:12px}
table.cmp td{white-space:normal}
.rf{font-size:20px;padding:5px 10px}
.livebar{display:flex;flex-wrap:wrap;gap:6px 14px;align-items:center;padding:10px 12px;border-radius:10px;background:var(--goodbg);color:var(--fg);margin:0 0 12px;font-size:13px}
.livebar b{font-size:16px}
.dot{width:9px;height:9px;border-radius:50%;background:var(--good);box-shadow:0 0 0 0 var(--good);animation:pulse 1.6s infinite}
@media (prefers-reduced-motion:reduce){
  .dot{animation:none}
}
.p-live{background:var(--goodbg);color:var(--good)}
.p-wait{background:var(--warnbg);color:var(--warn)}
.dot.still{animation:none;opacity:.5}
.board{display:grid;grid-template-columns:repeat(auto-fill,minmax(150px,1fr));gap:8px;margin:12px 0}
.fxl{display:grid;grid-template-columns:1fr auto 1fr;align-items:center;gap:6px;padding:7px 10px;border:1px solid var(--line);border-radius:9px;background:var(--bg);font-size:13px;font-variant-numeric:tabular-nums}
.fxl span:first-child{text-align:right}
.fxl b{font-size:14px}
.fxl small{grid-column:1/-1;text-align:center;font-size:11px}
.fxl.on{border-color:var(--good);box-shadow:0 0 0 1px var(--good) inset}
.fxl.on small{color:var(--good);font-weight:700}
.fxl.mine{background:var(--acc2)}
.chip.sel{border-color:var(--warn);box-shadow:0 0 0 2px var(--warn) inset}
.cands,.swappanel{display:flex;flex-direction:column}
.swappanel{border:1px solid var(--line);border-radius:10px;padding:12px;background:var(--bg);gap:8px}
.swappanel .h{display:flex;justify-content:space-between;align-items:center}
.swappanel input{width:100%}
.cands{gap:6px;max-height:420px;overflow:auto}
.cand{display:flex;justify-content:space-between;gap:10px;align-items:center;text-align:left;background:var(--card);border:1px solid var(--line);border-radius:8px;padding:7px 10px;color:var(--fg)}
.cand:hover{border-color:var(--acc)}
.cand.no{opacity:.55}
.cand small,.fxl small{color:var(--mut)}
.cn{min-width:0}
.cv{display:flex;flex-direction:column;align-items:flex-end;font-variant-numeric:tabular-nums}
.hint2{margin:0;color:var(--mut);font-size:13px}
.alerts{border:2px solid var(--bad);background:var(--badbg);border-radius:12px;padding:12px 14px;margin:0 0 14px;display:flex;flex-direction:column;gap:10px}
.alerts.hot{animation:hot 1.2s ease-in-out 3}
@media (prefers-reduced-motion:reduce){
  .alerts.hot{animation:none}
}
.ah{display:flex;justify-content:space-between;flex-wrap:wrap;gap:6px;color:var(--bad)}
.ah b{font-size:16px}
.acts,.al{display:flex;flex-direction:column}
.al{background:var(--card);border-radius:9px;padding:9px 11px;gap:4px}
.al.low{opacity:.75}
.al .alt a,.alerts.calm .ah{color:var(--fg)}
.acts{margin:2px 0 0;padding-left:18px;font-size:13px;gap:3px}
.chip.okw{border-color:var(--good);box-shadow:0 0 0 2px var(--good) inset;cursor:pointer}
.chip.dim{opacity:.45}
.bslot>small,.ptitle{font-size:11px;color:var(--mut)}
.ptitle{text-transform:uppercase;letter-spacing:.06em;text-align:center;margin-bottom:2px}
.alerts.calm,.benchbox{background:var(--bg)}
.bslot{display:flex;flex-direction:column;align-items:center;gap:3px}
.bslot>small{font-weight:700}
.btnrow2{display:flex;gap:8px;flex-wrap:wrap}
.alerts.calm{border-color:var(--line)}
.known{font-size:13px;color:var(--mut)}
.chipbar{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:8px;margin-bottom:12px}
.chipbtn{display:flex;flex-direction:column;align-items:flex-start;gap:2px;text-align:left;background:var(--bg);border:1px solid var(--line);border-radius:10px;padding:9px 12px;color:var(--fg)}
.chipbtn b{font-size:14px}
.chipbtn small,.qbtn small{font-size:12px;color:var(--mut)}
.chipbtn:hover{border-color:var(--acc)}
.chipbtn.on{background:var(--acc);color:var(--card)}
.chipbtn.on small{color:var(--card);opacity:.9}
.chipnote{border:1px solid var(--acc);background:var(--acc2);border-radius:10px;padding:10px 12px;font-size:13px;margin-bottom:12px;line-height:1.6}
.qbtn,.quick{display:flex;flex-direction:column}
.quick{gap:8px}
.qbtn{align-items:flex-start;text-align:left;border-radius:8px;padding:5px 10px;border:1px solid var(--line);background:var(--card);color:var(--fg)}
.qbtn small{font-size:11px}
.chipbtn.on,.qbtn.tg,nav a.on{border-color:var(--acc)}
.qbtn.tg{background:var(--acc2)}
.qbtn.df{background:#efe3fb}
@media (prefers-color-scheme:dark){
  .qbtn.df{background:#33214a;border-color:#7d55a8}
}
.panel{background:radial-gradient(900px 500px at 85% -10%,#12374a 0%,transparent 60%),radial-gradient(700px 500px at -10% 110%,#10323a 0%,transparent 55%),var(--bg)}
.top,nav{background:rgba(13,22,38,.92)}
.go{color:#05261c}
nav a.on{background:var(--acc)}
.hero{justify-content:space-between;background:linear-gradient(135deg,#16314a,#121d31)}
.hero h2{font-size:20px}
.herok small{display:block}
.herok b{font-size:20px}
@media (max-width:900px){
  .tiles{grid-template-columns:repeat(2,minmax(0,1fr))}
}
.tile,.tile .tl li{display:flex;align-items:flex-start}
.tile{position:relative;flex-direction:column;gap:6px;text-align:left;min-height:150px;padding:16px 18px 34px;border:1px solid var(--line);border-radius:14px;background:linear-gradient(135deg,#1a2a45,#121d31);color:var(--fg);font:inherit}
button.tile{cursor:pointer}
.tile.wide{grid-column:span 2}
.tile.full{grid-column:1/-1}
@media (max-width:560px){
  .tiles{grid-template-columns:1fr}
  .tile.wide{grid-column:auto}
}
.tile h3{margin:0;font-size:16px;font-weight:700}
.tile p{margin:0;font-size:13px}
.tile .big{font-size:26px;font-weight:700;font-variant-numeric:tabular-nums}
.tile .big small,.tile .open{font-size:12px;font-weight:500;color:var(--mut)}
.tile .open{position:absolute;right:16px;bottom:12px;color:var(--acc);font-weight:600}
.tile .tl{list-style:none;margin:0;padding:0;display:flex;flex-direction:column;gap:6px;font-size:13px}
.tile .tl li{gap:8px}
.tile.alertt{min-height:0;border-color:var(--bad);background:var(--badbg)}
.tile.newst{padding-bottom:16px}
.th{display:flex;justify-content:space-between;align-items:center;width:100%}
.slider{position:relative;width:100%;height:118px;overflow:hidden}
.newsbig .slider{height:140px;border:1px solid var(--line);border-radius:12px;background:linear-gradient(135deg,#1a2a45,#121d31);margin-bottom:12px}
.newsbig .slide{padding:14px 34px 14px 16px}
.strack{height:100%;transition:transform .55s ease}
@media (prefers-reduced-motion:reduce){
  .strack{transition:none}
}
.slide{height:100%;display:flex;flex-direction:column;justify-content:center;gap:6px;padding-right:26px}
.slide .pill{margin-left:4px}
.stitle{color:var(--fg);font-size:16px;font-weight:600;line-height:1.3;text-decoration:none;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
.stitle:hover,.tick tbody tr:hover td.pl{color:var(--acc)}
.sdots{position:absolute;right:6px;top:50%;transform:translateY(-50%);display:flex;flex-direction:column;gap:5px}
.sdots button{width:8px;height:8px;padding:0;border-radius:50%;border:0;background:var(--line)}
.sdots button.on{background:var(--acc);height:16px;border-radius:4px}
.gwpill,.kpis.six .kpi{background:var(--card)}
.kpis.six .kpi b,.pi b{display:block;white-space:nowrap}
.kpis.six .kpi b{font-size:14.5px;line-height:1.35}
.kpi span b,.kpis.six .kpi span b{display:inline;font-size:inherit;margin:0}
.pltools .grow{flex:1}
.gwpill{font-weight:700;font-size:14px;padding:6px 12px;border:1px solid var(--line);border-radius:999px}
.arm{position:absolute;top:-8px;left:50%;transform:translateX(-50%);font-style:normal;font-size:11px;font-weight:700;min-width:20px;height:20px;line-height:20px;text-align:center;border-radius:10px;background:#31486c;color:#fff;padding:0 4px}
.arm.c{background:var(--acc);color:#05261c}
.pitch .ptitle{color:#eafff3}
.benchbox{background:var(--card);border-style:solid}
.ptabs{display:grid;grid-template-columns:repeat(4,1fr);gap:4px;padding:4px;border:1px solid var(--line);border-radius:12px;background:var(--bg)}
.ptab{padding:8px 4px;border-radius:9px;background:0 0;color:var(--mut);font-weight:600;font-size:13px}
.pf.on,.ptab.on{background:var(--acc2);color:var(--acc)}
.ptab.on{box-shadow:0 0 0 1px var(--acc) inset}
.ptbody{border:1px solid var(--line);border-radius:12px;padding:12px;background:var(--card)}
.stack{display:flex;flex-direction:column;gap:10px}
.pf,.pi small{color:var(--mut)}
.pf,.prow{padding:6px 2px;font-size:13px}
.pf{border-radius:8px;background:var(--bg);border:1px solid var(--line);font-weight:600}
.pf.on{border-color:var(--acc)}
.prow{display:grid;grid-template-columns:minmax(0,1fr) 46px 34px 36px 96px 26px;gap:6px;align-items:center;border-bottom:1px solid var(--line);font-variant-numeric:tabular-nums}
.prow .n{text-align:right}
.prow.no{opacity:.5}
.pi{min-width:0}
.pi b{overflow:hidden;text-overflow:ellipsis}
.pi small{font-size:11px}
.dfx{color:#cfa9f5}
.prow .f{min-width:28px;font-size:11px;padding:1px 2px}
.add{width:24px;height:24px;padding:0;border-radius:50%;background:var(--acc2);color:var(--acc);border:1px solid var(--acc);font-weight:700;line-height:20px}
.p-diff,.qbtn.df{background:#33214a}
.p-diff{color:#cfa9f5}
.diffc{border-color:#5b3d86}
.qbtn.df{border-color:#7d55a8}
.chipnote{color:var(--fg)}
.kpi,.move,.plan li,.swappanel{background:rgba(10,19,34,.7)}
.kit{width:38px;height:33px;display:block;flex:none;filter:drop-shadow(0 2px 2px rgba(0,0,0,.45))}
.ph,.who{display:flex}
.ph{justify-content:space-between;gap:12px;align-items:flex-start}
.ph .kit{width:56px;height:49px;margin-right:40px}
.who{gap:8px;align-items:center;min-width:0}
.who .kit{width:28px;height:25px}
.sp{border:1px solid var(--line);color:var(--mut);display:inline-block}
.sp.one{border-color:var(--warn);color:var(--warn)}
.gwb{padding:0;border:1px solid var(--acc);background:var(--acc2);font-size:20px;font-weight:700}
.gwb:disabled{opacity:.3;cursor:default;border-color:var(--line);color:var(--mut);background:0 0}
.gwb:not(:disabled):hover{background:var(--acc);color:#05261c}
.gwt{text-align:center;border:1px solid var(--line);border-radius:10px;background:var(--card)}
.gwt b,.sph img{display:block}
.gwt small{color:var(--mut);font-size:12px}
.tline{display:flex;gap:6px;overflow-x:auto;padding-bottom:4px;margin-bottom:6px}
.tl1,.wcl select{border:1px solid var(--line)}
.tl1{flex:1 0 62px;display:flex;flex-direction:column;align-items:center;gap:1px;padding:5px 4px;border-radius:9px;background:var(--card);color:var(--mut)}
.tl1 b{font-size:12px;color:var(--fg)}
.tl1 small,.wco small{font-size:11px}
.tl1.has{border-color:var(--warn)}
.tl1.has small{color:var(--warn);font-weight:700}
.tl1.on{background:var(--acc2);border-color:var(--acc);box-shadow:0 0 0 1px var(--acc) inset}
.saved,.tick th{text-align:center}
.saved{margin:0 0 12px}
.lnk{background:0 0;border:0;padding:0;color:var(--acc);text-decoration:underline;font-size:inherit}
.bar{transform-box:fill-box;transform-origin:bottom}
.hit{cursor:pointer}
.hit.on,.hit:hover{fill:rgba(69,208,143,.14)}
#season-detail{margin-top:14px}
@media (prefers-reduced-motion:no-preference){
  @keyframes fadeUp{0%{opacity:0;transform:translateY(10px)}to{opacity:1;transform:none}}
  @keyframes grow{0%{transform:scaleY(0)}to{transform:scaleY(1)}}
  @keyframes sheen{0%{background-position:-200%0}to{background-position:200%0}}
  section.s:not([hidden]){animation:fadeUp .3s ease both}
  .tile{transition:transform .18s ease,border-color .18s,box-shadow .18s}
  button.tile:hover{transform:translateY(-3px);box-shadow:0 10px 24px rgba(0,0,0,.35),0 0 0 1px var(--acc) inset}
  .hero{background-image:linear-gradient(110deg,transparent 30%,rgba(69,208,143,.1) 50%,transparent 70%),linear-gradient(135deg,#16314a,#121d31);background-size:200% 100%,auto;animation:sheen 6s linear infinite}
  .bar{animation:grow .55s ease both}
  .ptbody>.chipbar,.ptbody>.stack>*{animation:fadeUp .3s ease both}
  .ptbody>.stack>:nth-child(2){animation-delay:.05s}
  .ptbody>.stack>:nth-child(3){animation-delay:.1s}
  .ptbody>.stack>:nth-child(4){animation-delay:.15s}
  .kpi b{transition:color .2s}
  .chipbtn,.go,.gwb,.ptab,.tl1,.try,nav a{transition:background .15s,color .15s,border-color .15s,transform .12s}
  .go:active,.gwb:active,.try:active{transform:scale(.96)}
  .drawer:not([hidden]){animation:slideIn .25s ease both}
  @keyframes slideIn{0%{transform:translateX(40px);opacity:0}to{transform:none;opacity:1}}
}
.wcbox{border:1px solid var(--acc);border-radius:12px;padding:12px;margin:10px 0;background:rgba(14,58,52,.35)}
.wch,.wcl{display:flex;align-items:center}
.wch{flex-wrap:wrap;justify-content:space-between;gap:8px;margin-bottom:8px}
.wcl{font-size:12px;color:var(--mut);text-transform:none;letter-spacing:0;gap:6px}
.wcl select{font:inherit;font-size:13px;padding:5px 8px;border-radius:8px;background:var(--bg);max-width:220px}
.wcopts{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:8px}
@media (max-width:900px){
  .wcopts{grid-template-columns:1fr}
}
.wco{display:flex;flex-direction:column;gap:4px;align-items:stretch;text-align:left;padding:10px;border-radius:10px;border:1px solid var(--line);background:var(--card);color:var(--fg)}
.wco.on,.wco:hover{border-color:var(--acc)}
.wco.on{box-shadow:0 0 0 2px var(--acc) inset}
.wcs,.wct{display:flex;justify-content:space-between}
.wct{flex-wrap:wrap;align-items:center;gap:4px}
.wco small{line-height:1.35}
.wcs{font-size:12px;color:var(--mut);font-variant-numeric:tabular-nums}
.wcl select,.wcs b{color:var(--fg)}
.spin{display:inline-block;width:12px;height:12px;border:2px solid var(--line);border-top-color:var(--acc);border-radius:50%;vertical-align:-2px;margin-right:6px;animation:spin .8s linear infinite}
.s{border-radius:12px}
.s h2{font-size:16px}
.h3{font-size:12px;letter-spacing:.06em;text-transform:uppercase;color:var(--mut);margin:16px 0 8px;font-weight:700}
.kpis.uni{grid-template-columns:repeat(auto-fit,minmax(140px,1fr));gap:10px}
.kpis.uni.three{grid-template-columns:repeat(3,minmax(0,1fr))}
.kpis .kpi,.kpis.uni .kpi{display:flex;flex-direction:column;justify-content:space-between;padding:10px 12px;background:var(--bg)}
.kpis .kpi{min-height:78px;border-radius:10px}
.kpi b{font-size:20px}
@media (max-width:860px){
  .kpis.uni.three{grid-template-columns:1fr 1fr 1fr}
}
.plgrid{grid-template-columns:minmax(0,1.3fr) minmax(300px,1fr);gap:12px}
@media (max-width:860px){
  .plgrid{grid-template-columns:1fr}
}
.tick tbody tr{cursor:pointer}
.slider .slide{flex-direction:row;align-items:center;justify-content:flex-start;gap:14px;padding:12px 34px 12px 12px;text-align:left}
.slider .sph{width:132px}
.tick td.pl{font-size:13px;width:150px;white-space:nowrap}
#s-live td.n,.arow .atx a,.tick td.n,.tick td.n b,.tkc b{color:var(--fg)}
.tick th{font-size:11px}
.tkc b{font-size:13px}
.tick td.n,.tick td.n b,.tick td.tk{font-size:13px;text-align:center}
.sph{flex:0 0 132px;height:100px;border-radius:10px;overflow:hidden;background:linear-gradient(135deg,#25406b,#16243c);display:grid;place-items:center}
.sph img{width:100%;height:100%;object-fit:cover}
.noimg{font-weight:700;font-size:13px;color:var(--mut);letter-spacing:.04em;text-transform:uppercase}
.cols3 li.nli img,.noimg.sm{width:56px;height:40px;flex:0 0 56px;border-radius:7px}
.noimg.sm{background:linear-gradient(135deg,#25406b,#16243c)}
.stx{display:flex;flex-direction:column;gap:6px;min-width:0}
.cols3 li.nli{display:flex;gap:10px;align-items:flex-start}
.cols3 li.nli img{object-fit:cover;background:#16243c}
@media (max-width:560px){
  .sph{flex-basis:84px;height:72px}
}
.seg.tabs{display:inline-flex;margin:4px 0 12px}
.lpanel{border:1px solid var(--line);border-radius:12px;padding:14px;background:rgba(10,19,34,.45)}
.lpanel .eobox,.lpanel .lgbox{margin-top:0}
.lpanel .board,.rotctl .seg.tabs{margin:0}
.livebar{margin-bottom:10px}
.tick td.tk{font-size:11px;font-weight:700;padding:5px 4px;line-height:1.15;min-width:44px}
.tick td.d1,.tick td.d2{background:var(--goodbg);color:var(--good)}
.tick td.d3{background:var(--neu);color:var(--fg)}
.tick td.d4,.tick td.d5{background:var(--badbg);color:var(--bad)}
.tick td.blank{background:0 0;color:var(--mut)}
.tick td.dgw{box-shadow:inset 0 0 0 2px var(--warn)}
.tick tr.own td.pl{box-shadow:inset 3px 0 0 var(--acc)}
.tkc{display:flex;align-items:center;gap:6px;white-space:nowrap}
.tkc .smini{width:22px;height:20px}
.tick table{border-collapse:separate;border-spacing:2px}
.ha,.mv i{font-style:normal;font-weight:700}
.ha{font-size:.78em;margin-left:3px;padding:0 3px;border-radius:3px;background:rgba(255,255,255,.14);vertical-align:1px}
.ha.a{background:rgba(0,0,0,.28)}
.crw{position:relative;display:inline-grid;place-items:center;width:22px;height:22px;flex:none;vertical-align:middle}
.crw .smini{width:20px;height:18px}
.crw .crest{position:absolute;inset:0;width:100%;height:100%;object-fit:contain}
.crw.ok .smini,img.gone{display:none}
.crw.big{width:58%;height:70%}
.crw.big .smini{width:70%;height:70%}
.sp{margin-left:4px;background:#f6c343;line-height:1;vertical-align:1px}
.plan li{align-items:center}
.cta{background:var(--acc2)}
.arow:hover .cta{background:var(--acc);color:#04221a}
.mv{display:inline-flex;align-items:center;gap:5px;margin-right:8px}
.mv i{font-size:11px;letter-spacing:.04em;padding:2px 6px;border-radius:5px}
.mo,.t-urgent .tag{background:var(--badbg);color:var(--bad)}
.mi{background:var(--goodbg);color:var(--good)}
.t-captain .tag{background:#3a2f0d;color:#f6c343}
.t-chip .tag,.t-diff .tag{background:#2c1f47;color:#c49bff}
.t-injuries .tag,.t-news .tag,.t-prices .tag{background:#3a2a12;color:var(--warn)}
.arow,.arows{width:100%}
.arow{background:rgba(8,14,26,.55);color:var(--fg);font:inherit;text-align:left;cursor:pointer;transition:border-color .15s,background .15s}
.arow:hover{border-color:var(--acc);background:rgba(20,60,52,.35)}
.arow .atx{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.arow .cta{padding:4px 10px;font-size:12px}
.slg i{display:inline-block;width:10px;height:10px;border-radius:3px;margin-right:5px;vertical-align:-1px}
.slg i.dash{width:16px;height:0;border-top:2px dashed var(--warn);border-radius:0;vertical-align:3px}
@media (max-width:560px){
  .sstat{grid-template-columns:1fr 1fr}
}
.schart .rk{fill:#6f7f99}
.schart .lbl{font-size:12px;font-weight:700}
.gwnav{justify-content:flex-start;flex-wrap:wrap}
.gwb{width:34px;height:34px;display:grid;place-items:center;border-radius:9px;border-color:var(--line);background:var(--bg);color:var(--fg)}
.gwb:hover:not(:disabled){border-color:var(--acc);color:var(--acc)}
.gwt{min-width:0;padding:4px 14px;display:flex;align-items:baseline;gap:8px}
.gwt b{font-size:16px}
.gwnav .note.saved{margin:0 0 0 auto;font-size:12px}
.kpis.six{grid-template-columns:repeat(6,minmax(0,1fr));gap:4px;padding:4px;border:1px solid var(--line);border-radius:12px;background:var(--bg);margin-bottom:8px}
.kpis.six .kpi{min-height:0;padding:5px 8px;border:0;border-radius:9px;background:rgba(255,255,255,.03);display:block;text-align:center;cursor:help}
.kpis.six .kpi small,.kpis.six .kpi>span{display:block;color:var(--mut);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.kpis.six .kpi small{font-size:11px;text-transform:uppercase;letter-spacing:.05em}
.kpis.six .kpi>span{font-size:11px;line-height:1.35;margin-top:1px}
.kpis.six .kpi>span b{font-size:inherit;display:inline;line-height:inherit;font-weight:700}
@media (max-width:700px){
  .kpis.six{grid-template-columns:repeat(3,minmax(0,1fr))}
}
.f,.mt b{white-space:nowrap}
.f{min-width:46px;display:inline-flex;align-items:center;justify-content:center;flex-direction:row}
.f .ha{display:inline-block}
.benchbox .row{gap:6px}
.mst{font-size:11px;color:var(--mut);text-align:center}
.mt{display:flex;align-items:center;gap:7px;min-width:0;font-size:13px}
.mt b{text-overflow:ellipsis}
.mt.r{justify-content:flex-end;text-align:right}
.mt .crw{width:26px;height:26px}
.mt b,.ncard b,.nph{overflow:hidden}
.nph{position:relative;background:#16243c}
.nph .nart{position:absolute;inset:0;display:grid;place-items:center}
.nph .nart.gen svg,.nph .nimg{position:absolute;inset:0;width:100%;height:100%}
.nph .nart.gen b{position:relative;font-size:12px;letter-spacing:.06em;text-transform:uppercase;color:#fff;background:rgba(0,0,0,.45);padding:3px 8px;border-radius:6px}
.nph .nimg{object-fit:cover}
.sph.nph{flex:0 0 150px;width:150px;height:100px;border-radius:10px}
.seg.nfilt{margin-top:14px}
#s-news .seg.nfilt{flex-wrap:wrap!important;overflow:visible!important;max-width:100%}
#s-news .seg.nfilt button{display:inline-flex;align-items:center;gap:6px}
.nfc{font-style:normal;font-size:11px;font-weight:700;min-width:18px;padding:0 5px;border-radius:999px;background:rgba(255,255,255,.08);text-align:center;line-height:18px}
.seg button.on .nfc{background:rgba(4,34,26,.18)}
#s-news .seg.nfilt button.zero:not(.on){opacity:.55}
.nfempty{padding:18px;text-align:center;border:1px dashed var(--line);border-radius:12px}
.ngrid{display:grid;grid-template-columns:repeat(auto-fill,minmax(230px,1fr));gap:10px}
.ncard,.srcd{border:1px solid var(--line)}
.ncard{display:flex;flex-direction:column;overflow:hidden;background:rgba(8,14,26,.55);color:var(--fg);text-decoration:none;transition:border-color .15s,transform .15s}
.ncard:hover{border-color:var(--acc);transform:translateY(-2px)}
.ncard[hidden],.plan3 .gwnav .note.saved{display:none}
.ncard .nph{height:120px}
.ncard .nb{padding:10px 12px;display:flex;flex-direction:column;gap:6px}
.ncard .nt{display:flex;gap:6px;align-items:center;flex-wrap:wrap}
.ncard b{line-height:1.35;display:-webkit-box;-webkit-line-clamp:3;-webkit-box-orient:vertical}
.srcd{margin-top:14px;border-radius:10px;padding:8px 12px;background:rgba(8,14,26,.4)}
.srcd summary{cursor:pointer;font-size:13px;color:var(--mut);font-weight:600}
.srcd .srcs{margin-top:10px}
.tick .crw{width:20px;height:20px}
.rt .crw{width:26px;height:26px}
.toast,.toasts{display:flex;flex-direction:column}
.toasts{position:absolute;top:128px;right:16px;z-index:20;gap:8px;width:min(340px,calc(100% - 32px));pointer-events:none}
.toast{pointer-events:auto;gap:2px;padding:10px 12px;border-radius:10px;background:#121d31;border:1px solid var(--line);border-left:4px solid var(--acc);box-shadow:0 10px 26px rgba(0,0,0,.45);font-size:13px;transition:opacity .5s,transform .5s}
.toast b{font-size:14px}
.toast.good{border-left-color:var(--good)}
.toast.bad{border-left-color:var(--bad)}
.toast.out{opacity:0;transform:translateX(30px)}
@media (prefers-reduced-motion:no-preference){
  .toast{animation:slideIn .3s ease both}
}
.alertctl{display:flex;flex-wrap:wrap;gap:8px;align-items:center;margin:10px 0}
.eobox,.lgbox{margin-top:16px}
.eol li,.lgt td,.lgt th{padding:6px 8px}
tr.me td{background:rgba(69,208,143,.08)}
.eol{list-style:none;margin:0;padding:0;display:flex;flex-direction:column;gap:6px}
.eol li{display:grid;grid-template-columns:minmax(0,1fr) auto 56px;gap:8px;align-items:center;font-size:13px;border:1px solid var(--line);border-radius:8px;background:var(--card)}
.eol li>span:last-child{text-align:right;font-weight:700;font-variant-numeric:tabular-nums}
.eol li>*:first-child{min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
@media (max-width:640px){.eol li{grid-template-columns:minmax(0,1fr) auto 46px;font-size:12px;gap:6px}.eol li>span:nth-child(2){font-size:11px;color:var(--mut)}}
.eo,.seg button{font-size:12px;color:var(--mut)}
.rotctl{display:flex;flex-wrap:wrap;gap:12px;align-items:center;justify-content:space-between;margin-bottom:14px}
.seg{display:flex;background:var(--bg)}
.seg button{font:inherit;font-size:13px;font-weight:600;border:0;background:0 0;padding:7px 14px;border-radius:9px;cursor:pointer;transition:background calc(.2s*var(--m)),color calc(.2s*var(--m))}
.seg button.on{background:var(--acc2);color:var(--acc);box-shadow:0 0 0 1px var(--acc) inset}
.rotgrid{display:grid;grid-template-columns:repeat(auto-fill,minmax(320px,1fr));gap:10px}
.rot.own{border-color:rgba(69,208,143,.45)}
.rot .rh{gap:8px}
.rot .rt{display:flex!important;flex:none;width:auto!important;gap:0}
.rot .rt .crw{width:26px;height:26px}
.rot .rt .crw+.crw{margin-left:-6px}
.rot .rx{min-width:0}
.rot .rx b{font:700 16px var(--fd);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.rot .rx small{font-size:11px}
.rot .rs{display:flex;flex-direction:column;align-items:center;padding:4px 10px;line-height:1.1}
.rot .rs b{font-size:16px}.rot .rs small{font-size:11px;font-weight:600;text-transform:uppercase;letter-spacing:.06em;opacity:.8}
.rtiles{grid-template-columns:repeat(var(--n,6),minmax(0,1fr))!important;gap:3px!important}
.rtl{gap:1px;padding:4px 0!important}
.rtl small{font-size:11px!important}
.rtl .crw{width:18px;height:18px}
.rtl b{font-size:13px!important}
.rpl{display:grid;grid-template-columns:auto minmax(0,1fr) minmax(0,1fr) auto;gap:6px;align-items:center}
.rpk{font-size:11px;font-weight:700;letter-spacing:.05em;color:var(--mut)}
.rpb{display:flex;align-items:center;gap:6px;min-width:0;padding:5px 8px;border-radius:8px;border:1px solid var(--line);background:var(--acc2);color:var(--fg);cursor:pointer;text-align:left;font:inherit}
.rpb:hover{border-color:var(--acc)}
.rpb .crw{width:18px;height:18px;flex:none}
.rpb span{display:flex;flex-direction:column;min-width:0}
.rpb b{font-size:12px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.rpb small{font-size:11px;color:var(--gold);font-weight:700}
.rpt{font-size:12px;font-weight:700;color:var(--gold)}
@media (max-width:900px){
  .rotgrid{grid-template-columns:1fr}
}
.rh,.rot{display:flex;gap:10px}
.rot{border:1px solid var(--line);border-radius:14px;background:rgba(10,19,34,.7);padding:12px 14px;flex-direction:column}
.rh{align-items:center}
.rn,.rx small{color:var(--mut)}
.rn{font-weight:700;width:18px}
.rt{display:flex}
.smini{width:30px;height:27px}
.rx{flex:1;display:flex;flex-direction:column}
.rx b{font-size:16px}
.rx small{font-size:12px}
.rs{font-weight:700;font-size:20px;padding:6px 12px;border-radius:10px;background:var(--acc2);color:var(--acc);font-variant-numeric:tabular-nums}
.rtiles{display:grid;grid-template-columns:repeat(auto-fit,minmax(48px,1fr));gap:4px}
.duo,.rtl{display:flex;align-items:center}
.rtl{flex-direction:column;padding:4px 2px;border-radius:7px;line-height:1.2}
.rtl small{font-size:11px;opacity:.85}
.rtl b{font-size:16px}
.rtl.d1,.rtl.d2{background:var(--goodbg);color:var(--good)}
.rtl.d3{background:var(--neu);color:var(--mut)}
.rtl.d4,.rtl.d5{background:var(--badbg);color:var(--bad)}
.duo{flex-wrap:wrap;gap:6px;font-size:12px}
.prog{height:6px;border-radius:3px;background:var(--line);overflow:hidden;margin-top:6px}
.prog span{display:block;height:100%;width:0;background:var(--acc);transition:width .2s}
@media (max-width:640px){
  .panel{inset:0;width:100vw;border-radius:0}
  input{width:110px}
}
#planner .plgrid{grid-template-columns:var(--lw,minmax(0,1.3fr)) 12px minmax(300px,1fr);gap:0}
#planner .splitter{align-self:stretch;cursor:col-resize;display:flex;justify-content:center;touch-action:none;border-radius:6px;min-height:120px}
#planner .splitter::before{content:"";width:4px;border-radius:2px;background:var(--line);margin:4px 0;transition:background .15s,width .15s}
#planner .splitter.drag::before,#planner .splitter:focus-visible::before,#planner .splitter:hover::before{background:var(--acc);width:5px}
#planner .splitter:focus-visible{outline:2px solid var(--acc);outline-offset:-2px}
@media (max-width:860px){
  #planner .plgrid{grid-template-columns:1fr;gap:12px}
  #planner .splitter{display:none}
}
#planner .pitch{justify-content:space-evenly;min-height:calc(var(--ps,1)*520px)}
#planner .pitch .chip.pc{zoom:var(--ps,1)}
#planner .benchbox .chip.pc{zoom:var(--pb,.88)}
#planner .pitch .row{gap:6px 4px}
#planner .benchbox .row,#planner .pitch .row{justify-content:space-evenly}
.pzoom{display:inline-flex;align-items:center;gap:6px;font-size:12px;color:var(--mut)}
.pzoom input[type=range]{width:96px;padding:0;border:0;background:0 0;accent-color:var(--acc);height:18px;cursor:pointer}
.pzoom output{min-width:38px;text-align:right;font-variant-numeric:tabular-nums;color:var(--fg);font-weight:600}
.pzoom .try.on{background:var(--acc2)}
.root{font:14px/1.5 Inter,system-ui,-apple-system,Segoe UI,Roboto,sans-serif}
.wm,h2,h3{font-family:var(--fd);letter-spacing:.2px}
section.s h2{font-size:26px;font-weight:700;margin:0 0 4px}
.h3{font-family:Inter,system-ui,sans-serif}
.panel{background:var(--bg);isolation:isolate}
.panel>.subnav,.panel>.top,.panel>main,.panel>nav{position:relative;z-index:1}
.panel>.drawer,.panel>.toasts{z-index:6}
.top{background:rgba(11,18,32,.72);backdrop-filter:blur(10px);border-bottom:1px solid var(--line);padding:10px 16px;gap:10px 14px}
.brand{flex-direction:row;align-items:center;gap:10px}
.brand>div,.herok div{display:flex;flex-direction:column}
.brand b{font:700 20px var(--fd);letter-spacing:.3px}
@media (min-width:701px){
  .top{padding:8px 16px}
  .brand #sub{font-size:12px;color:var(--t3);max-width:340px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
  nav{padding:6px 16px}
}
.logo{width:34px;height:34px;flex:none}
.ver{font:600 11px Inter,sans-serif;color:var(--t3);margin-left:4px}
.gwpill2{display:inline-flex;align-items:center;gap:8px;padding:6px 12px;border-radius:999px;background:var(--raised);border:1px solid var(--line);font-size:13px;color:var(--mut);font-variant-numeric:tabular-nums}
.gwpill2 b{color:var(--fg);font:700 16px var(--fd)}
.gwpill2.hot{border-color:var(--bad);color:var(--bad)}
.x,input{border-color:var(--line)}
input{background:var(--raised)}
.x{display:inline-grid;place-items:center;min-width:36px;min-height:36px}
nav{background:rgba(11,18,32,.6);backdrop-filter:blur(10px);border-bottom:1px solid var(--line);padding:8px 16px;gap:4px}
.nink,nav a{border-radius:999px}
nav a{z-index:1;display:inline-flex;align-items:center;gap:7px;color:var(--mut);font-weight:600;font-size:13px;padding:8px 14px;transition:color calc(.2s*var(--m))}
nav a svg{width:17px;height:17px}
nav a:hover{background:rgba(255,255,255,.05);color:var(--fg)}
nav a,nav a.on{background:0 0;border:0}
nav a.on{color:#04221a;font-weight:700}
.nink{position:absolute;left:0;top:0;background:var(--acc);box-shadow:0 6px 18px rgba(69,208,143,.35);transition:transform calc(.42s*var(--m)) cubic-bezier(.3,1.3,.5,1),width calc(.42s*var(--m)) cubic-bezier(.3,1.3,.5,1),opacity .2s;pointer-events:none;z-index:0;opacity:0}
.subnav{padding:10px 16px 0;display:none}
.navsub{margin-left:auto;display:flex;align-items:center}
.navsub .seg{padding:3px}
.navsub .seg button{padding:6px 12px}
@media (max-width:700px){
  .subnav:not([hidden]){display:flex}
  .navsub{display:none}
}
.plan3 #planner,nav,nav a{position:relative}
.plan3 .pitch{padding:6px 6px 8px}
#planner .pitch{min-height:calc(var(--ps,1)*490px)}
.plan3 .benchbox{margin-top:6px;padding:4px 6px 8px;position:relative}
.plan3 .benchbox .ptitle{position:absolute;left:12px;top:8px;margin:0}
.plan3 .pltools{position:absolute;top:2px;right:0;margin:0;z-index:2;justify-content:flex-end}
.plan3 .pzoom>span:first-child{display:none}
.plan3 .plgrid{margin-top:0}
.plan3 .warns{display:flex;flex-wrap:wrap;gap:4px 14px;list-style:none;padding:0}
@media (max-width:1120px){
  .plan3 .pltools{position:static;margin:0 0 8px}
}
section.s.plan3{padding:14px}
.plan3 .gwnav{margin-bottom:8px}
.plan3 .gwnav .note.saved{margin-left:auto}
.plan3 .warns{margin:0 0 6px;font-size:12px}
.subnav .seg{background:rgba(17,28,47,.8)}
.seg{display:inline-flex;gap:4px;padding:4px;border:1px solid var(--line);border-radius:12px;background:var(--raised)}
.seg button.on{background:var(--acc);color:#04221a;box-shadow:none}
section.s.home{background:0 0;border:0;padding:0;backdrop-filter:none;display:flex;flex-direction:column;gap:14px}
.sub{font-size:13px}
.muted,.sub{color:var(--mut)}
.fine{font-size:12px;margin:6px 0 0}
.card{background:rgba(17,28,47,.82);border-radius:16px;padding:16px;backdrop-filter:blur(4px)}
.card .th{display:flex;justify-content:space-between;align-items:center;gap:10px;margin-bottom:10px;flex-wrap:wrap}
.card h3{font:700 20px var(--fd);margin:0}
.card,.hero,.lnk2{border:1px solid var(--line)}
.lnk2{padding:6px 14px;border-radius:999px;background:0 0;color:var(--mut);font-size:12px;font-weight:600;cursor:pointer}
.lnk2:hover{border-color:var(--acc);color:var(--acc)}
.hero{display:flex;flex-wrap:wrap;gap:18px 28px;align-items:flex-end;padding:20px;border-radius:16px;background:linear-gradient(120deg,rgba(69,208,143,.14),rgba(17,28,47,.85) 45%);backdrop-filter:blur(4px)}
.hero h2{font:700 36px/1 var(--fd);margin:4px 0}
.hero .sub{margin:0}
.eyebrow,.herok small{font-size:11px;font-weight:700;letter-spacing:.12em;text-transform:uppercase;color:var(--acc)}
.herok{display:flex;gap:28px;flex-wrap:wrap;margin-left:auto}
.herok small{letter-spacing:.08em;color:var(--mut);font-weight:600}
.herok b{font:700 30px/1.1 var(--fd);font-variant-numeric:tabular-nums}
.herok span{font-size:12px;font-weight:600}
.livestrip,.lsx{display:flex;align-items:center}
.livestrip{gap:10px;width:100%;text-align:left;font:inherit;color:var(--fg);padding:10px 14px;border-radius:12px;border:1px solid rgba(69,208,143,.35);background:rgba(16,56,42,.55);cursor:pointer}
.livestrip .dotl{width:9px;height:9px;border-radius:50%;background:var(--acc);flex:none;animation:pulse calc(1.4s*var(--m)) infinite}
.lsx{gap:6px 14px;flex-wrap:wrap}
.lsx b{color:var(--acc)}
.lsx span:last-child{color:var(--mut)}
.arows{display:flex;flex-direction:column;gap:8px}
.arow{display:flex;align-items:center;gap:12px;padding:10px 12px;border-radius:12px;border:1px solid var(--line);background:rgba(11,18,32,.55);font-size:14px;transition:border-color calc(.2s*var(--m)),transform calc(.2s*var(--m))}
.arow:hover{border-color:rgba(69,208,143,.45)}
.arow .tag{min-width:84px;text-align:center}
.arow .atx{flex:1;min-width:0}
.cta,.slg{font-size:12px}
.cta{flex:none;margin-left:auto;padding:7px 14px;border-radius:999px;border:1px solid var(--acc);background:rgba(69,208,143,.12);color:var(--acc);font-weight:700;cursor:pointer;white-space:nowrap;transition:background calc(.15s*var(--m)),color calc(.15s*var(--m)),transform .12s}
.cta:hover{background:var(--acc);color:#04221a}
.cta:active,.sact:active,.seg button:active,nav a:active{transform:scale(.97)}
details.more{margin-top:8px}
details.more summary{cursor:pointer;color:var(--mut);font-size:13px;font-weight:600;padding:6px 2px}
details.more .arows{margin-top:6px}
.slg{display:flex;gap:14px;flex-wrap:wrap;color:var(--mut)}
.seast .h3{margin:4px 0 8px}
.schart{max-height:230px;width:100%;margin-top:6px}
.schart .grid{stroke:rgba(255,255,255,.07)}
.schart .ax{font-size:11px;fill:var(--mut);font-weight:600}
.schart .rk{font-size:11px;fill:var(--t3)}
.schart .lbl{font:700 13px var(--fd);fill:var(--fg)}
.schart .lbl.hi{fill:#6fe0a8}
.schart .lbl.lo{fill:#ff8a8a}
.chip.pc,.schart .hit{cursor:pointer}
.schart .hit:hover{fill:rgba(255,255,255,.05)}
.kpis.uni .kpi{background:rgba(11,18,32,.55);border:1px solid var(--line);border-radius:12px;min-height:74px}
.kpi small{color:var(--mut);font-size:11px;text-transform:uppercase;letter-spacing:.06em}
.kpi b{font:700 26px var(--fd)}
.chip.pc{position:relative;width:88px;min-width:0;max-width:88px;padding:0;border:0;background:0 0;box-shadow:none;display:flex;flex-direction:column;align-items:center;gap:0;border-radius:10px;transition:transform calc(.18s*var(--m)) var(--ease)}
.chip.pc:hover{transform:translateY(-3px)}
.chip.pc:focus-visible{outline:2px solid var(--gold);outline-offset:3px}
.chip.pc.dim{opacity:.4}
.jsh,.jsv{width:70px;height:64px}
.jsh{position:relative;margin:0 auto 2px}
.jsv{display:block;filter:drop-shadow(0 4px 5px rgba(0,0,0,.4))}
.jcode,.jrole{position:absolute;text-align:center}
.jcode{top:21px;left:0;right:0;font:700 13px/1 var(--fd);letter-spacing:.6px;pointer-events:none}
.jrole{right:-6px;bottom:-2px;min-width:20px;height:20px;line-height:17px;border-radius:10px;background:#0b1220;border:1.5px solid #fff;color:#fff;font:700 11px/17px Inter,sans-serif;padding:0 3px;box-sizing:border-box}
.jstar{width:18px;height:18px;left:23px;bottom:2px}
.jsp,.jstar,.jwarn{position:absolute}
.jwarn{width:18px;height:17px;left:-4px;bottom:0}
.jsp{top:0;right:4px;z-index:1}
.jsp .sp{margin:0}
.jname,.jval{width:100%;text-align:center;white-space:nowrap}
.jname{padding:3px 4px;background:#0d141f;color:#fff;font:600 13px/1.25 Inter,sans-serif;overflow:hidden;text-overflow:ellipsis;border-radius:6px 6px 0 0}
.pph.fl{position:relative;overflow:hidden;isolation:isolate;background:#0b1220;border-color:rgba(255,255,255,.14)}
.pph.fl{box-shadow:0 0 28px -6px rgba(255,255,255,.22),0 10px 30px rgba(0,0,0,.35),inset 0 1px 0 rgba(255,255,255,.22)!important;border-color:rgba(255,255,255,.2)!important}
.pph.fl::before{content:none}
.pph .pflag{position:absolute;top:0;bottom:0;z-index:-2;pointer-events:none;filter:saturate(1.15);background-repeat:no-repeat}
.pph .pflag.l{left:0;right:34%;background-image:var(--flagb,var(--flag));background-size:6000% 100%;background-position:0 0}
.pph .pflag.r{left:66%;right:0;background-image:var(--flagb,var(--flag));background-size:6000% 100%;background-position:100% 0}
.pph .pflag.c{left:66%;transform:translateX(-50%);aspect-ratio:3/2;background-image:var(--flagb,var(--flag));background-size:contain;background-position:center}
.pph.fl::after{content:"";position:absolute;inset:0;z-index:-1;pointer-events:none;
  background:linear-gradient(180deg,rgba(255,255,255,.14) 0%,rgba(255,255,255,0) 40%,rgba(0,0,0,.2) 100%),
    linear-gradient(90deg,rgba(9,14,24,.84) 0%,rgba(9,14,24,.6) 34%,rgba(9,14,24,.26) 72%,rgba(9,14,24,.12) 100%)}
.pph.fl .ppt h1,.pph.fl .ppt small,.pph.fl .ppfull,.pph.fl .pprice,.pph.fl .ppt b{text-shadow:0 1px 3px rgba(0,0,0,.95),0 0 1px rgba(0,0,0,.9)}
.pph.fl .ppt h1,.pph.fl .ppfull,.pph.fl small{text-shadow:0 1px 3px rgba(0,0,0,.9)}.pph.fl .ppfull{color:#e3e9f3}
.jval{padding:2px 4px;background:#1d2738;color:#e8eef7;font:700 13px/1.3 var(--fd);font-variant-numeric:tabular-nums}
.jval b{font:700 16px var(--fd)}
.hs,.jsub{display:flex}
.jsub{width:100%;justify-content:center;gap:2px;background:#1d2738;border-radius:0 0 6px 6px;padding:0 0 3px;font-size:11px;color:#c7d3e6}
.jsub.hstrip{background:0 0;padding:2px 0 0;gap:2px}
.hs{flex:1;max-width:29px;flex-direction:column;border-radius:4px;overflow:hidden;background:rgba(8,14,26,.75)}
.hs b{font:700 11px/14px var(--fd);color:#e8eef7;letter-spacing:.2px}
.hb,.ppill b i{font-style:normal}
.hb,.hs b{text-align:center}
.hb{display:block;font:700 11px/13px Inter,sans-serif;color:#0b1220}
.hb.d1{background:var(--d1);color:#fff}
.hb.d2{background:var(--d2)}
.hb.d3{background:var(--d3)}
.hb.d4{background:var(--d4);color:#fff}
.hb.d5{background:var(--d5);color:#fff}
.hb.dx{background:#3b465a;color:#c7d3e6}
.chip.pc.okw .jsh,.chip.pc.sel .jsh{outline:2px solid var(--gold);outline-offset:3px;border-radius:12px}
.chip.pc.okw .jsh{outline:2px dashed var(--acc)}
.chip.pc.new .jname{box-shadow:inset 0-2px 0 var(--acc)}
.chip.pc.ro .jval{background:#1d2738}
.sp{display:inline-grid;place-items:center;min-width:18px;height:18px;padding:0 4px;border-radius:9px;background:var(--gold);color:#1a1300;font:700 11px/1 Inter,sans-serif;border:1.5px solid #0b1220}
.legend{display:flex;flex-wrap:wrap;gap:6px 16px;margin:8px 0 0;font-size:12px;color:var(--mut);align-items:center}
.legend .hb{display:inline-block;width:18px;border-radius:3px}
.pitch,.pitch .row{justify-content:space-evenly}
.pitch{position:relative;border-radius:16px;border:1px solid rgba(80,190,120,.35);padding:14px 6px;gap:6px;background-image:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 100 100' preserveAspectRatio='none'%3E%3Cg fill='none' stroke='white' stroke-opacity='.22' stroke-width='.45'%3E%3Crect x='1.5' y='1.5' width='97' height='97' rx='1'/%3E%3Crect x='27' y='1.5' width='46' height='15'/%3E%3Crect x='39' y='1.5' width='22' height='6'/%3E%3Cpath d='M40 16.5q10 7 20 0'/%3E%3Cpath d='M1.5 98.5h97'/%3E%3Cpath d='M36 98.5q14-20 28 0'/%3E%3C/g%3E%3C/svg%3E"),repeating-linear-gradient(180deg,#1c7d47 0 11.1%,#18703f 11.1% 22.2%);background-size:100% 100%,auto;box-shadow:inset 0 0 80px rgba(0,0,0,.35)}
.pitch .row{display:flex;gap:4px;align-items:flex-start}
.pitch,.ppill,.ppills{display:flex;flex-direction:column}
.ppills{position:absolute;top:10px;gap:6px;z-index:2}
@media (max-width:760px){
  #planner .pitch{display:grid;grid-template-columns:minmax(0,1fr) auto minmax(0,1fr);align-items:start}
#planner .pitch>.ppills{min-width:0}#planner .pitch>.ppills .ppill{flex:1 1 0;min-width:0;overflow:hidden}
#planner .ppill small{white-space:nowrap;overflow:hidden;text-overflow:ellipsis;max-width:100%}
@media (max-width:420px){#planner .ppill{padding:2px 4px}#planner .ppill b{font-size:12px}#planner .ppill small{font-size:7.5px}#planner .fmpill{padding:2px 8px}#planner .fmpill b{font-size:12px}}
  #planner .pitch>*{grid-column:1/-1}
  #planner .pitch>.ppills{position:static;grid-column:auto;grid-row:1;flex-direction:row;gap:4px;padding:6px 6px 2px}
  #planner .pitch>.ppills.l{grid-column:1;justify-content:flex-start}
  #planner .pitch>.ppills.r{grid-column:3;justify-content:flex-end}
  #planner .pitch>.fmpill{position:static;grid-column:2;grid-row:1;align-self:center;margin-top:6px}
  #planner .ppill{min-width:0;padding:3px 7px;border-radius:9px}
  #planner .ppill b{font-size:13px}
  #planner .ppill small{font-size:11px;letter-spacing:.03em}
  #planner .ppill .pd{font-size:11px;margin-top:0}
}
.ppills.l{left:10px}
.ppills.r{right:10px;align-items:flex-end}
.ppill{align-items:center;min-width:86px;padding:5px 12px;border-radius:14px;background:rgba(11,18,32,.78);border:1px solid rgba(255,255,255,.12);backdrop-filter:blur(6px);cursor:help}
.ppill b{font:700 20px/1.1 var(--fd);color:#6fe0a8;font-variant-numeric:tabular-nums}
.ppill b i{color:var(--bad);font-size:14px}
.ppill small{font-size:11px;color:var(--mut);text-transform:uppercase;letter-spacing:.05em}
.benchbox{margin-top:8px;padding:8px 6px 10px;border-radius:16px;border:1px solid var(--line);background:rgba(10,30,22,.75)}
.benchbox .ptitle{font-size:11px;letter-spacing:.1em;color:var(--mut)}
.gwnav,.pltools{display:flex;align-items:center;gap:8px}
.pltools{flex-wrap:wrap;margin:0 0 8px}
.gwnav{margin:0 0 10px}
.gwt{background:var(--raised);border-color:var(--line)}
.gwt b{font:700 20px var(--fd)}
@media (max-width:860px){
  .ppill{min-width:70px;padding:4px 8px}
  .ppill b{font-size:16px}
}
.sheet,.sheetscrim{position:absolute;inset:0}
.sheet{z-index:8;display:flex;align-items:flex-end;justify-content:center}
.qa{position:absolute;inset:0;z-index:9}
.qascrim{position:absolute;inset:0;background:transparent}
.qabar{position:absolute;display:flex;gap:4px;padding:4px;border-radius:999px;background:rgba(10,16,27,.95);border:1px solid rgba(255,255,255,.12);box-shadow:0 12px 30px rgba(0,0,0,.55);animation:qaFade calc(.18s*var(--m)) ease-out both}
.qab{all:unset;box-sizing:border-box;cursor:pointer;width:35px;height:35px;border-radius:50%;display:flex;flex-direction:column;align-items:center;justify-content:center;gap:0;background:#1b2840;border:1px solid rgba(255,255,255,.10);color:#eef3fb;animation:qaPop calc(.34s*var(--m)) cubic-bezier(.2,1.45,.45,1) both;animation-delay:calc(var(--i)*45ms*var(--m))}
.qab .si{font:700 12px/1 var(--fd);color:var(--acc)}
.qab small{font:600 8px/1.05 Inter,sans-serif;color:#cfd8e6;letter-spacing:-.01em}
.qab.on{background:var(--acc)}.qab.on .si,.qab.on small{color:#04221a}
.qab.out .si{color:#ff7a86}
.qab:focus-visible{outline:2px solid var(--acc);outline-offset:2px}
.qab:active{transform:scale(.92)}
.chip.pc.qsel{outline:2px solid var(--acc);outline-offset:3px;border-radius:10px}
@keyframes qaPop{from{opacity:0;transform:translate(var(--dx,0),var(--dy,0)) scale(.25)}to{opacity:1;transform:none}}
@keyframes qaFade{from{opacity:0}to{opacity:1}}

.sheetscrim{background:rgba(4,8,16,.55);backdrop-filter:blur(2px);animation:fadeIn calc(.2s*var(--m)) ease both}
.sheetbody{position:relative;width:min(560px,100%);max-height:85%;overflow:auto;background:var(--overlay);border:1px solid rgba(255,255,255,.1);border-radius:20px 20px 0 0;padding:8px 18px 20px;box-shadow:0-20px 50px rgba(0,0,0,.45);animation:sheetUp calc(.32s*var(--m)) var(--ease) both}
.sheet.closing .sheetbody{animation:sheetDown .18s ease both}
.sheet.closing .sheetscrim{animation:fadeOut .18s ease both}
.shgrab{width:44px;height:5px;border-radius:3px;background:rgba(255,255,255,.25);margin:4px auto 12px;cursor:pointer}
.shh{display:flex;align-items:center;gap:14px;margin-bottom:14px}
.shh>div:nth-child(2){flex:1;min-width:0;display:flex;flex-direction:column;gap:3px}
.shh>div:first-child:last-child{flex:1}
.shh b{font:700 26px var(--fd)}
.shh small{color:var(--mut);font-size:13px}
.shk{width:88px;flex:none;display:flex;flex-direction:column;align-items:center}
.bg-plain .bgfx>i,.shk .jname{display:none}
.shfx{margin-top:4px}
.sgrid{display:grid;grid-template-columns:1fr 1fr;gap:8px}
.shh2{display:flex;align-items:center;gap:12px;margin:2px 0 10px}
.shk2{position:relative;width:58px;height:58px;flex:none}
.shk2 .kitw{position:absolute;inset:0}.shk2 .kitw svg,.shk2 .kitw img{position:absolute;inset:0;width:100%;height:100%;object-fit:contain}
.shi{flex:1;min-width:0;display:flex;flex-direction:column;gap:3px}
.shi>b{font:700 21px/1.1 var(--fd)}
.shi small{font-size:12px;color:var(--mut)}
.shi small b{color:var(--fg)}
.shtip{align-self:flex-start;font-size:12px;font-weight:700;padding:2px 8px;border-radius:999px;background:var(--neu);color:var(--mut)}
.shtip.good{background:var(--goodbg);color:var(--good)}.shtip.bad{background:var(--badbg);color:var(--bad)}
.shn3{display:grid;grid-template-columns:repeat(4,1fr);gap:6px;margin-bottom:10px}
.shn3>div{display:flex;flex-direction:column;align-items:center;gap:3px;padding:6px 2px;border-radius:10px;background:rgba(255,255,255,.04);border:1px solid var(--line)}
.shn3 small{font-size:11px;color:var(--mut)}
.shn3 b{font:700 16px var(--fd)}
.shn3 .tot{background:var(--acc2);border-color:rgba(69,208,143,.4)}.shn3 .tot b{color:var(--acc);font-size:20px}
.sgrid2{display:grid;grid-template-columns:repeat(auto-fit,minmax(0,1fr));grid-auto-flow:column;gap:6px}
.sgrid2.two{margin-top:6px}
.sact.sm{display:flex;flex-direction:column;align-items:center;justify-content:center;gap:3px;padding:8px 2px;min-height:0;text-align:center;text-decoration:none}
.sact.sm .si{width:28px;height:28px;font-size:14px}
.sact.sm b{font-size:12px;font-weight:700;white-space:nowrap}
b.kn{display:inline-flex;align-items:center;gap:6px}
b.kn .picon{margin:0}
@media (max-width:480px){
  .sgrid{grid-template-columns:1fr}
}
.sact{display:flex;align-items:center;gap:12px;padding:12px;border-radius:12px;border:1px solid var(--line);background:rgba(11,18,32,.6);color:var(--fg);font:inherit;text-align:left;text-decoration:none;cursor:pointer;transition:border-color calc(.15s*var(--m)),background calc(.15s*var(--m))}
.sact:focus-visible,.sact:hover{border-color:var(--acc);background:rgba(69,208,143,.1);outline:0}
.sact.on{border-color:var(--gold)}
.sact.out .si{color:var(--bad)}
.sact .si{width:34px;height:34px;flex:none;display:grid;place-items:center;border-radius:10px;background:var(--raised);font:700 16px var(--fd);color:var(--acc)}
.sact b{display:block;font-size:14px}
.setrow{display:flex;justify-content:space-between;align-items:center;gap:12px;flex-wrap:wrap;padding:12px 0;border-top:1px solid var(--line)}
.sact small,.setrow b{display:block}
.sact small,.setrow small{color:var(--mut);font-size:12px}
.tick td.tk{font:700 12px var(--fd)}
.ncard{border-radius:14px;background:rgba(11,18,32,.6)}
.ncard b{font-size:14px}
.skel{display:flex;flex-direction:column;gap:12px}
.sk{border-radius:12px;background:linear-gradient(90deg,#16243c 0,#22375a 50%,#16243c 100%)0 0/200% 100%;animation:shim calc(1.2s*var(--m)) linear infinite}
.sk.h{height:96px}
.sk.c{height:74px;flex:1}
.sk.b{height:54px}
.sk.b.s{width:70%}
.skrow{display:flex;gap:10px}
.toast{position:relative;overflow:visible}
.updbar{flex:1 1 100%;order:99;display:flex;align-items:center;gap:10px;flex-wrap:wrap;padding:8px 12px;border-radius:10px;background:rgba(69,208,143,.12);border:1px solid rgba(69,208,143,.45);font-size:14px;line-height:1.4}
.updbar[hidden]{display:none}
.updbar b{color:var(--acc)}
.updbar .updtxt{flex:1 1 220px;min-width:0}
.updbar a.updget{background:var(--acc);color:#0b1220;font-weight:700;padding:6px 14px;border-radius:8px;text-decoration:none;white-space:nowrap}
.updbar button{background:none;border:1px solid var(--line);color:inherit;border-radius:8px;padding:5px 10px;cursor:pointer;font:inherit}
.toast .gball{position:absolute;left:-14px;top:-14px;width:30px;height:30px;border-radius:50%;background:radial-gradient(circle at 35% 30%,#fff,#c9d3e0);box-shadow:0 4px 10px rgba(0,0,0,.4);animation:gpop calc(.6s*var(--m)) cubic-bezier(.3,1.6,.5,1) both}
.toast .cf{position:absolute;left:0;top:0;width:6px;height:11px;border-radius:2px;opacity:0;animation:cf calc(1.1s*var(--m)) cubic-bezier(.1,.7,.3,1) both}
.bgfx{inset:0;z-index:0;overflow:hidden;pointer-events:none;background:linear-gradient(180deg,#0a1324 0,#0b1629 45%,#0b1d22 100%)}
.bgfx>i{display:block}
.bgfx .light{width:62%;height:130%;top:-34%;background:conic-gradient(from 180deg at 50%0,transparent 0deg 165deg,rgba(210,240,255,.16) 173deg,rgba(235,250,255,.28) 180deg,rgba(210,240,255,.16) 187deg,transparent 195deg 360deg);filter:blur(4px);mix-blend-mode:screen;opacity:.75}
.bgfx .l1,.bgfx .l2{transform-origin:50%0}
.bgfx .l1{left:-20%;transform:rotate(-24deg);animation:swayA calc(10s*var(--m)) ease-in-out infinite alternate}
.bgfx .l2{right:-20%;transform:rotate(24deg);animation:swayB calc(12s*var(--m)) ease-in-out infinite alternate}
.bgfx .lamp{top:-16px;width:180px;height:62px;border-radius:50%;background:radial-gradient(ellipse,rgba(240,250,255,.8),rgba(170,220,255,.2) 40%,transparent 70%)}
.bgfx .lp1{left:5%}
.bgfx .lp2{right:5%}
.bgfx .haze{inset:0;background:radial-gradient(60% 40%at 30% 55%,rgba(120,180,220,.06),transparent 70%),radial-gradient(50% 35%at 75% 60%,rgba(120,200,190,.05),transparent 70%);animation:haze calc(20s*var(--m)) ease-in-out infinite alternate}
.bgfx .crowd{left:0;right:0;top:36%;height:16%;background:radial-gradient(circle,rgba(255,255,255,.16)0 1px,transparent 1.5px)0 0/9px 7px;opacity:.3;-webkit-mask-image:linear-gradient(to bottom,transparent,#000 50%,transparent);mask-image:linear-gradient(to bottom,transparent,#000 50%,transparent)}
.bgfx .glines,.bgfx .grass{left:-10%;right:-10%;bottom:0;height:44%;transform:perspective(520px) rotateX(58deg);transform-origin:50% 100%}
.bgfx .grass{background:repeating-linear-gradient(90deg,rgba(26,112,64,.5)0 8%,rgba(22,96,55,.5) 8% 16%);-webkit-mask-image:linear-gradient(to top,#000 20%,transparent 100%);mask-image:linear-gradient(to top,#000 20%,transparent 100%)}
.bgfx .glines{opacity:.3;-webkit-mask-image:linear-gradient(to top,#000 10%,transparent 90%);mask-image:linear-gradient(to top,#000 10%,transparent 90%)}
.bgfx .glines svg{width:100%;height:100%}
.bgfx .blob{width:60%;height:70%;border-radius:50%;filter:blur(80px);opacity:0;transition:opacity .6s}
.bgfx .b1{left:-12%;top:-22%;background:var(--c1,#c8102e);animation:drift calc(18s*var(--m)) ease-in-out infinite alternate}
.bgfx .b2{right:-16%;top:16%;background:var(--c2,#45d08f);animation:drift calc(24s*var(--m)) ease-in-out infinite alternate-reverse}
.bg-club .bgfx .blob{opacity:.32}
.bg-club .bgfx .b2{opacity:.18}
.bg-club .bgfx .crowd,.bg-club .bgfx .lamp,.bg-club .bgfx .light,.picon.ok b{opacity:0}
.m-calm .bgfx *,.paused .bgfx *{animation-play-state:paused}
.bgfx,.bgfx>i,.wipe,.wipe i{position:absolute}
.wipe{left:0;right:0;bottom:0;z-index:5;pointer-events:none;overflow:hidden;visibility:hidden}
.wipe i{top:-10%;height:120%;transform:skewX(-16deg)}
.wipe .w1{width:70%;background:linear-gradient(90deg,#0d3d31,var(--acc))}
.wipe .w2{width:5%;background:var(--gold)}
.wipe .w3{width:80%;background:#0b1220}
.wipe.go{visibility:visible}
.wipe.go .w3{animation:wipeR calc(.55s*var(--m)) cubic-bezier(.7,0,.3,1) both}
.wipe.go .w1{animation:wipeR calc(.55s*var(--m)) cubic-bezier(.7,0,.3,1) .04s both}
.wipe.go .w2{animation:wipeR calc(.55s*var(--m)) cubic-bezier(.7,0,.3,1) .08s both}
.wipe .w1,.wipe .w3{left:-12%}
.wipe .w2{left:58%}
.wipe .w1{animation-name:wipeR}
@media (prefers-reduced-motion:no-preference){
  section.s.vin-r{animation:vinR calc(.32s*var(--m)) var(--ease) both}
  section.s.vin-l{animation:vinL calc(.32s*var(--m)) var(--ease) both}
  section.s.vin-f{animation:vinF calc(.3s*var(--m)) ease both}
  section.s.vin-f>*,section.s.vin-l>*,section.s.vin-r>*{animation:rise calc(.45s*var(--m)) var(--ease) both}
  section.s>:nth-child(2){animation-delay:calc(.05s*var(--m))}
  section.s>:nth-child(3){animation-delay:calc(.1s*var(--m))}
  section.s>:nth-child(4){animation-delay:calc(.15s*var(--m))}
  section.s>:nth-child(n+5){animation-delay:calc(.2s*var(--m))}
  .lpanel.tin,.ngrid,.ptbody,.rotgrid,.tick{animation:rise calc(.32s*var(--m)) ease both}
  .pitch .chip.pc{animation:drop calc(.5s*var(--m)) cubic-bezier(.3,1.4,.5,1) both}
  .pitch .row:nth-child(4) .chip.pc{animation-delay:calc(.08s*var(--m))}
  .pitch .row:nth-child(5) .chip.pc{animation-delay:calc(.16s*var(--m))}
  .pitch .row:nth-child(6) .chip.pc{animation-delay:calc(.24s*var(--m))}
  .m-calm .pitch .chip.pc,.m-calm section.s,.m-calm section.s>*{animation:none}
}
@media (max-width:700px){
  .panel{inset:0;width:100vw;border-radius:0}
  nav{order:10;position:relative;justify-content:space-around;padding:6px 4px calc(6px + env(safe-area-inset-bottom,0));border-top:1px solid var(--line);border-bottom:0;flex-wrap:nowrap}
  nav a{flex-direction:column;gap:2px;font-size:11px;padding:6px 8px;border-radius:12px}
  nav a svg{width:20px;height:20px}
  .top{padding:8px 12px;gap:8px}
  .brand{order:1;flex:1;min-width:0}
  .brand #sub,.brand .ver,.gwt small,.top form label{display:none}
  .logo{width:30px;height:30px}
  .brand b{font-size:16px}
  .seg.nfilt,.subnav .seg{max-width:100%;overflow-x:auto;flex-wrap:nowrap}
  .brand b,.seg.nfilt button{white-space:nowrap}
  .gwpill2{order:2;padding:5px 10px}
  #setb{order:3}
  #x{order:4}
  .top form{order:5;width:100%}
  .top form input{flex:1;width:auto}
  .gwnav{flex-wrap:nowrap}
  .gwt{flex:1;min-width:0;padding:4px 10px}
  section.s{padding:14px;border-radius:14px}
  main{padding:10px 10px 16px}
  .herok{margin-left:0;gap:18px}
  .hero h2{font-size:30px}
  .arow{flex-wrap:wrap}
  .arow .cta{margin-left:0}
}
#s-live .sub{max-width:64ch;line-height:1.6;margin-bottom:16px}
#s-live .livebar{padding:14px 18px;border-radius:14px;margin-bottom:18px;gap:6px 16px}
#s-live .seg.tabs{margin:2px 0 18px}
#s-live .lpanel{padding:22px 26px;border-radius:16px;background:rgba(10,19,34,.35)}
.mwh{display:flex;align-items:center;justify-content:center;gap:24px;margin:0 0 24px}
.mwa{width:46px;height:46px;border-radius:50%;display:grid;place-items:center;padding:0;background:var(--neu);color:var(--fg);border:1px solid var(--line)}
.mwa:hover:not(:disabled){border-color:var(--acc);color:var(--acc)}
.mwa:disabled{opacity:.3;cursor:default}
.mwhc{display:flex;flex-direction:column;align-items:center;gap:4px;min-width:210px;text-align:center}
.mwhc b{font-size:20px;letter-spacing:-.01em}
.mwhc>span{font-size:13px;color:var(--mut)}
.mwday{margin-bottom:28px}
.mwday:last-child{margin-bottom:0}
.mwdh{font-size:13px;font-weight:700;margin:0 auto 6px;padding:5px 14px;text-align:center;text-transform:uppercase;letter-spacing:.06em;color:var(--mut);border-bottom:1px solid var(--line);width:fit-content}
.mwr{display:flex;flex-direction:column;align-items:stretch;gap:6px;padding:12px 4px;border-radius:10px}
.mwr.my{background:linear-gradient(90deg,transparent,rgba(69,208,143,.05),transparent)}
.mws{text-align:center;font-size:11px;line-height:1}
.mwyou{font-size:12px;color:var(--acc);margin-top:2px}
.mwyou b{color:var(--fg)}
.mwmy{display:flex;flex-wrap:wrap;justify-content:center;align-items:center;gap:4px;margin-top:2px}
.mwn{font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:.05em;color:#04221a;background:var(--acc);border-radius:999px;padding:2px 7px}
.mwp{font-size:12px;font-weight:600;padding:2px 8px;border-radius:999px;border:1px solid rgba(69,208,143,.35);background:rgba(69,208,143,.08)}
.mwp.bn{opacity:.6;border-style:dashed}
.mwodds{display:grid;grid-template-columns:minmax(0,1fr) 96px minmax(0,1fr);column-gap:14px;margin-top:6px;font-size:12px;color:var(--mut);font-variant-numeric:tabular-nums}.mwodds .r{text-align:right}.mwodds .c{text-align:center;color:var(--t3,var(--mut))}
@media (max-width:700px){.mwodds{grid-template-columns:minmax(0,1fr) 62px minmax(0,1fr);column-gap:8px;font-size:11px}}
.oddst{display:block;margin-top:6px;font-size:12px;color:var(--mut)}#odds-key{flex:1;min-width:0;font:inherit;padding:9px 10px;border-radius:9px;border:1px solid var(--line);background:var(--bg);color:var(--fg)}
.faststrip{margin:4px 0 0;font-size:12px;color:var(--mut);display:flex;align-items:center;gap:6px;flex-wrap:wrap}.fastdot{width:7px;height:7px;border-radius:50%;background:var(--gold);box-shadow:0 0 0 3px rgba(246,195,67,.2)}.fastp{display:block;color:var(--gold);font-weight:700;font-size:11px}
@media (max-width:700px){.mycnt{min-width:17px!important;height:17px!important;font-size:10px!important;padding:0 4px!important}}
.mycnt{display:inline-grid;place-items:center;min-width:20px;height:20px;padding:0 5px;border-radius:999px;font-size:11px;font-weight:800;color:#04221a;background:var(--acc);box-shadow:0 0 0 2px rgba(69,208,143,.18);flex:none}
.mwr.tap{cursor:pointer;transition:background .15s}.mwr.tap:hover{background:rgba(255,255,255,.03)}.mwr.open{background:rgba(255,255,255,.035)}
.mwinfo{text-align:center;font-size:12px;color:var(--mut);margin-top:-2px}.mwinfo b{color:var(--txt);font-variant-numeric:tabular-nums}.dotsep{opacity:.5;margin:0 6px}
.mwr{position:relative}.gblk{position:absolute;left:0;right:0;top:0;height:100%;max-height:118px;z-index:4;border-radius:10px;display:flex;align-items:center;justify-content:center;gap:10px;flex-wrap:wrap;padding:8px 12px;pointer-events:none;color:#06281a;background:linear-gradient(110deg,#2fd08a,#7cf0b9 45%,#2fd08a);background-size:220% 100%;box-shadow:0 6px 22px rgba(47,208,138,.45);animation:gblk 9s ease forwards,gsh 1.4s linear infinite;overflow:hidden}
.gblk b{font-size:24px;font-weight:900;letter-spacing:.06em;animation:gbeat .7s ease-in-out 3}.gblk .gtm{display:inline-flex;align-items:center;gap:6px;font-weight:800;font-size:14px}.gblk,.gblk b,.gblk small,.gblk span{color:#06281a!important}.gblk small{font-size:13px;font-weight:800;opacity:1}.gblk .gsc{font-size:20px;font-weight:900;font-variant-numeric:tabular-nums;background:rgba(6,40,26,.14);padding:1px 10px;border-radius:8px}
.gblk .gball{font-size:22px;display:inline-block;animation:groll 1.1s cubic-bezier(.3,1.4,.5,1) both}
@keyframes gblk{0%{opacity:0;transform:scale(.6)}5%{opacity:1;transform:scale(1.06)}9%{transform:scale(1)}85%{opacity:1;transform:none}100%{opacity:0;transform:translateY(-8px);visibility:hidden}}
@keyframes gsh{to{background-position:-220% 0}}@keyframes gbeat{50%{transform:scale(1.18)}}@keyframes groll{0%{transform:translateX(-120px) rotate(-540deg)}100%{transform:none}}
@media (prefers-reduced-motion:reduce){.gblk,.gblk *{animation-duration:.01s!important;animation-iteration-count:1!important}.gblk{animation:gblkr 9s linear forwards}@keyframes gblkr{0%,90%{opacity:1}100%{opacity:0;visibility:hidden}}}
a.mwp{color:inherit;text-decoration:none}a.mxpn{color:inherit;text-decoration:none;border-bottom:1px dotted currentColor}a.mxpn:hover,a.mwp:hover{color:var(--acc)}.mxsec h4 small{font-weight:500;font-size:11px;margin-left:4px}.tvch{white-space:nowrap}.tvch b{font-weight:700;color:var(--txt)}.mxinfo .tvch{white-space:normal}
.gmin{color:var(--txt);font-weight:700;font-variant-numeric:tabular-nums}
.mxp{margin-top:6px;border-top:1px solid var(--line);padding:12px 6px 4px;display:flex;flex-direction:column;gap:16px;cursor:default}
.mxp{grid-column:1/-1;min-width:0;width:100%;max-width:100%;box-sizing:border-box;overflow:hidden}.mxp *{box-sizing:border-box}.mxsec{min-width:0}
.mxst{max-width:min(560px,100%)!important}.mxst .r{grid-template-columns:46px minmax(0,1fr) 46px!important}.mxst .bar{min-width:0}
.mxtl{grid-template-columns:minmax(0,1fr) 38px minmax(0,1fr)!important}.mxtl>div{min-width:0}.mxtl .ev{min-width:0;max-width:100%}.mxtl .tx{min-width:0;overflow-wrap:anywhere}
@media (max-width:700px){.mxinfo{font-size:12px}.mxtl{font-size:12px;column-gap:6px}.mxtl .mn{width:32px;height:32px;font-size:10px}}
.mxinfo{text-align:center;font-size:13px;color:var(--mut)}
.mxmsg{text-align:center;margin:0}
.mxcd{text-align:center;display:flex;flex-direction:column;gap:2px}.mxcd small{color:var(--mut);font-size:12px}.mxcd b{font-size:24px;font-weight:800;font-variant-numeric:tabular-nums;color:var(--acc)}
.mxsec h4{margin:0 0 10px;text-align:center;font-size:12px;letter-spacing:.06em;text-transform:uppercase;color:var(--mut)}
.mxtl{display:grid;grid-template-columns:minmax(0,1fr) 40px minmax(0,1fr);row-gap:8px;column-gap:10px;align-items:center;font-size:13px}
.mxtl .mn{justify-self:center;width:36px;height:36px;border-radius:50%;background:rgba(255,255,255,.08);display:grid;place-items:center;font-weight:700;font-size:11px;font-variant-numeric:tabular-nums}
.mxtl .h{justify-self:end;text-align:right}.mxtl .ev{display:inline-flex;align-items:center;gap:8px}.mxtl .h .ev{flex-direction:row}
.mxtl .ev b{font-weight:600}.mxtl small{display:block;color:var(--mut);font-size:11px}.mxtl .ev>b+small,.mxtl .ev small{margin-top:1px}
.mxtl .tx{display:flex;flex-direction:column;line-height:1.3}.mxtl .h .tx{align-items:flex-end}.mxtl .in,.mxtl .out{font-size:12px}.mxtl .in{color:var(--good)}.mxtl .out{color:#f87171}.mxtl .sub{font-size:15px;color:var(--mut)}
.mxtl .sep{grid-column:1/-1;text-align:center;font-size:12px;font-weight:700;color:var(--mut);border-top:1px solid var(--line);padding-top:8px;margin-top:2px}
.cdy,.cdr{display:inline-block;width:11px;height:15px;border-radius:2px;background:#facc15}.cdr{background:#ef4444}
.mxst{display:flex;flex-direction:column;gap:9px;font-size:13px;max-width:560px;margin:0 auto;width:100%}
.mxst .r{display:grid;grid-template-columns:52px 1fr 52px;column-gap:10px;row-gap:3px;align-items:center}.mxst .mxv2{text-align:right;display:block}.mxst .r b{font-variant-numeric:tabular-nums}
.mxst .lb{grid-column:1/-1;text-align:center;font-size:11px;color:var(--mut);text-transform:uppercase;letter-spacing:.04em}
.mxst .hd b{color:var(--mut);font-size:12px}
.mxst .bar{display:flex;gap:3px;height:6px}.mxst .bar i{display:block;height:100%;border-radius:3px}.mxst .bh{background:var(--acc)}.mxst .ba{background:#8b6cf6}
.mwmy2{display:grid;grid-template-columns:minmax(0,1fr) 96px minmax(0,1fr);column-gap:14px;margin-top:8px;align-items:start}
.mws2{display:flex;flex-wrap:wrap;align-items:center;gap:4px;min-width:0}.mws2.r{justify-content:flex-end}
.mwmy2 .mwp{display:inline-flex;align-items:center;gap:5px;padding:2px 8px 2px 2px}
.mwp .picon.mwf{width:20px;height:24px;border-radius:5px;flex:none}
.mwp i.v{background:#cfd8e6}
@media (max-width:700px){.mwmy2{grid-template-columns:minmax(0,1fr) 62px minmax(0,1fr);column-gap:8px}}
.mwp i{font-style:normal;font-size:11px;font-weight:700;background:var(--gold);color:#2a1f00;border-radius:3px;padding:0 3px}
.mwp b{color:var(--acc)}
.mwr+.mwr{border-top:1px solid var(--line)}
.mwr:hover{background:rgba(255,255,255,.025)}
.mws{font-size:12px;font-weight:700;color:var(--mut);letter-spacing:.04em}
.mwlive{color:var(--bad);display:inline-flex;gap:5px}
.mwlive::before,.mwx i{width:7px;height:7px;border-radius:50%}
.mwlive::before{content:"";background:var(--bad);animation:mwp 1.4s ease-in-out infinite}
.mwlive,.mwm,.mwt{align-items:center}
.mwm{display:grid;grid-template-columns:minmax(0,1fr) 96px minmax(0,1fr);column-gap:14px}
.mwt{display:flex;gap:12px;min-width:0;font-size:16px;font-weight:700}
.mwt.h{justify-content:flex-end;text-align:right}
.mwt b{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.mwt .crw{width:32px;height:32px;flex:none}
.mwsc{text-align:center;font-size:16px;font-weight:700;font-variant-numeric:tabular-nums;background:rgba(8,14,26,.75);border-radius:9px;padding:8px 0}
.mwsc.mwv{font-size:13px;font-weight:700;color:var(--mut)}
.mwr.on .mwsc{color:var(--good);box-shadow:0 0 0 1px var(--good) inset}
.mwev{display:grid;grid-template-columns:minmax(0,1fr) 96px minmax(0,1fr);column-gap:14px;margin-top:8px;font-size:13px;color:var(--mut);line-height:1.45}
.mwev .r{text-align:right}
.mwx{justify-self:end;font-size:11px;font-weight:700;color:var(--acc);white-space:nowrap}
.mwx i{display:inline-block;background:var(--acc);margin-right:5px}
.mwnone{text-align:center;color:var(--mut);padding:18px 0}
@media (max-width:640px){
  #s-live .lpanel{padding:16px 12px}
  .mwr{grid-template-columns:42px minmax(0,1fr)}
  .mwx{display:none}
  .mwt{font-size:13px;gap:8px}
  .mwt .crw{width:24px;height:24px}
  .mwev,.mwm{grid-template-columns:minmax(0,1fr) 62px minmax(0,1fr);column-gap:8px}
  .mwh{gap:12px}
  .mwhc{min-width:150px}
}
.qbtn.done{border-color:var(--good)}
.qbtn.done::after{content:"✓";color:var(--good);margin-left:6px;font-weight:700}
.try.done{border-color:var(--good);color:var(--good)}
.toast-act{align-self:flex-start;margin-top:6px;padding:4px 12px;border-radius:999px;border:1px solid var(--acc);background:var(--acc2);color:var(--acc);font-weight:700;font-size:12px;cursor:pointer}
.toast-act:hover{background:var(--acc);color:#04221a}
.h2hempty,.h2hnote{display:flex;align-items:center}
.h2hempty{border:1px dashed var(--line);border-radius:12px;padding:22px;text-align:center;flex-direction:column;gap:12px}
.h2hnote{margin:12px 0 0;gap:10px;flex-wrap:wrap}
#planner.ci-noprice .jval{display:none}
#planner.ci-noprice .jname{border-radius:6px}
#planner.ci-nofx .jsub{display:none}
#planner.ci-nofx .jval{border-radius:0 0 6px 6px}
#planner.ci-nobadge .jsp,#planner.ci-nocode .jcode,#planner.ci-nostar .jstar,.infobar[hidden],.who>svg.kit{display:none}
#planner[data-fx="1"] .hs:nth-child(n+2),#planner[data-fx="2"] .hs:nth-child(n+3){display:none}
#planner.ci-nofx .pitch{min-height:calc(var(--ps,1)*500px)}
#planner.ci-nofx.ci-noprice .pitch{min-height:calc(var(--ps,1)*440px)}
.infobar,.iprev{align-items:center}
.infobar{display:flex;gap:18px;flex-wrap:wrap;margin:0 0 12px;padding:12px 16px;border:1px solid var(--line);border-radius:14px;background:var(--raised)}
.iprev{gap:4px;padding:10px 12px 6px;border-radius:12px;background:rgba(40,120,84,.28);pointer-events:none;flex:none}
.iprev .chip.pc,.iprev .chip.pc:hover,.iprev .pitch .chip.pc{transform:none;animation:none}
.iprev small{font-size:11px;color:var(--mut);text-transform:none;letter-spacing:0}
#s-home .herok>div,.ictl,.iprev{display:flex;flex-direction:column}
.ictl{gap:10px;flex:1;min-width:240px}
#s-home .hero,.ig,.irow{display:flex;flex-wrap:wrap}
.ig{align-items:center;gap:6px 12px}
.ig>span{font-size:13px;min-width:132px;font-weight:500}
#s-home .hero,.irow{gap:6px}
.ig>span,.ipill{color:var(--mut);text-transform:none;letter-spacing:0}
.ipill{padding:5px 13px;border-radius:999px;border:1px solid var(--line);background:0 0;font-size:13px;font-weight:600;cursor:pointer;transition:background .15s,color .15s,border-color .15s}
.ipill:hover{color:var(--fg);border-color:rgba(255,255,255,.24)}
.ipill.on{background:var(--acc2);border-color:var(--acc);color:var(--acc)}
.cdpill,.ix{border-radius:999px;font-size:13px}
.ix{align-self:flex-start;padding:5px 14px;border:1px solid var(--line);background:0 0;color:var(--mut);text-transform:none;cursor:pointer}
.ix:hover{color:var(--fg)}
#s-home .hero{align-items:center;gap:24px 32px;padding:22px 26px}
#s-home .hero .hl{flex:1 1 250px;min-width:0}
#s-home .hero .hl h2{margin:2px 0 8px}
#s-home .hero.fl{position:relative;overflow:hidden;isolation:isolate}
#s-home .hero.fl::before{content:"";position:absolute;z-index:-1;pointer-events:none;left:0;top:0;width:min(62%,300px);height:min(100%,140px);opacity:.55;border-top-left-radius:inherit;
  background:linear-gradient(90deg,rgba(0,0,0,.18),rgba(255,255,255,.28) 12%,rgba(0,0,0,.05) 24%,rgba(0,0,0,.42) 38%,rgba(255,255,255,.2) 52%,rgba(0,0,0,.08) 64%,rgba(0,0,0,.4) 78%,rgba(255,255,255,.12) 90%,rgba(0,0,0,.2)),var(--flagb) center/cover no-repeat;
  -webkit-mask-image:linear-gradient(90deg,#000 40%,transparent),linear-gradient(180deg,#000 55%,transparent);-webkit-mask-composite:source-in;mask-image:linear-gradient(90deg,#000 40%,transparent),linear-gradient(180deg,#000 55%,transparent);mask-composite:intersect}
#s-home .hero.fl .hl{text-shadow:0 1px 3px rgba(0,0,0,.95),0 0 1px rgba(0,0,0,.9)}
@media (max-width:640px){#s-home .hero.fl::before{height:96px;width:min(70%,260px)}}
.cdt,.cdpill{font-variant-numeric:tabular-nums}.cdt .cs{font-style:normal}
@media (max-width:400px){.cdt .cs{display:none}}
.cdpill{display:inline-block;margin-left:10px;padding:2px 11px;background:rgba(69,208,143,.14);color:var(--acc);font-weight:700;white-space:nowrap}
.cdpill.dn{background:var(--badbg);color:var(--bad)}
#s-home .deadline-head{min-width:145px;align-self:center;padding:8px 0}
#s-home .deadline-head .eyebrow{font-size:13px;line-height:1.25}
#s-home .herok{margin:0 0 0 auto;display:grid;grid-template-columns:repeat(5,auto);align-items:stretch}
#s-home .herok>div{padding:2px 22px;border-left:1px solid var(--line);gap:4px;min-width:112px}
#s-home .herok>div:first-child{border-left:0;padding-left:0}
#s-home .herok>div:last-child{padding-right:0}
#s-home .herok small{font-size:12px;letter-spacing:.07em;text-transform:uppercase;color:var(--mut);font-weight:600}
#s-home .herok b{font-size:26px;line-height:1.1;font-weight:700;font-variant-numeric:tabular-nums}
#s-home .herok .hs2{font-size:13px;line-height:1.35;color:var(--mut);font-weight:500}
#s-home .herok .hs2.up,.ppill .pd.up{color:var(--good)}
#s-home .herok .hs2.dn,.ppill .pd.dn{color:var(--bad)}
@media (max-width:1180px){
  #s-home .herok{margin:0;width:100%;grid-template-columns:repeat(3,minmax(0,1fr));row-gap:18px}
  #s-home .herok>div:nth-child(4){border-left:0;padding-left:0}
  #s-home .herok>div{padding:2px 16px}
}
@media (max-width:640px){
  #s-home .herok{grid-template-columns:repeat(2,minmax(0,1fr))}
  #s-home .herok>div{border-left:0;padding:2px 0}
  #s-home .herok b{font-size:23px}
}
.viewing{display:flex;align-items:center;justify-content:space-between;gap:10px 14px;flex-wrap:wrap;margin:0 0 12px;padding:10px 16px;border:1px solid var(--acc);border-radius:12px;background:var(--acc2);font-size:14px}
.lgt tr.lgopen{cursor:pointer;transition:background .15s}
.lgt tr.lgopen:hover{background:rgba(255,255,255,.045)}
.lgt tr.lgopen:focus-visible{outline:2px solid var(--acc);outline-offset:-2px}
.lgt tr.lgopen td:nth-child(3) b::after{content:" ↗";color:var(--mut);font-weight:400;opacity:0;transition:opacity .15s}
.lgt tr.lgopen:hover td:nth-child(3) b::after{opacity:1}
.ppill .pd{display:block;font-size:11px;font-weight:700;font-style:normal;margin-top:2px}
.prc{display:inline-block;margin-left:6px;padding:1px 8px;border-radius:999px;font-size:11px;font-weight:700;white-space:nowrap;vertical-align:1px;cursor:help}
.prc.up{background:var(--goodbg);color:var(--good)}
.prc.down{background:var(--badbg);color:var(--bad)}
.prc.possible{opacity:.8;background:0 0;border:1px solid currentColor}
.move.marginal{opacity:.7}
.mgn{font-size:12px;font-weight:600;color:var(--warn);margin:-2px 0 6px}
.kpis.mdl{grid-template-columns:repeat(auto-fit,minmax(150px,1fr))}
.picon{position:relative;display:inline-grid;place-items:center;width:18px;height:18px;min-width:18px;border-radius:50%;margin-right:6px;vertical-align:-4px;flex:none;overflow:hidden;box-shadow:0 0 0 1px rgba(255,255,255,.18)}
a.pn[data-pi]{display:inline-flex;align-items:center;gap:6px;max-width:100%;vertical-align:middle;text-decoration:none!important;border:0!important;color:var(--fg);font-weight:700;line-height:1.25;white-space:nowrap}
a.pn[data-pi]:hover{color:var(--acc)}
a.pn[data-pi] .picon{margin:0;vertical-align:0}
.picon.kit{background:none!important;box-shadow:none;border-radius:0;overflow:visible;width:22px;height:22px;max-width:22px;max-height:22px}
.picon.kit .kitw{position:absolute;inset:0;width:100%;height:100%}
.picon.kit .kitw svg,.picon.kit .kitw img{position:absolute;inset:0;width:100%;height:100%;object-fit:contain}
.picon b{font:700 .5em/1 Inter,sans-serif;letter-spacing:.2px}
.picon .crest{position:absolute;inset:1px;width:calc(100% - 2px);height:calc(100% - 2px);object-fit:contain;background:#f4f6fa;border-radius:50%;padding:1.5px;box-sizing:border-box}
.picon:not(.ok) .crest{opacity:0}
.picon.ok{background:#f4f6fa}
.acct td,.acct th,a.pn{white-space:nowrap}
.art-player .jsh{height:68px}
.art-player .jsv.psv{width:70px;height:68px;filter:drop-shadow(0 4px 5px rgba(0,0,0,.4))}
.art-player .jstar{left:-6px;bottom:14px}
.art-player .jcode{top:46px;font-size:11px}
.acc .kpis{margin-bottom:10px}
.accbar{height:8px;border-radius:4px;background:rgba(255,255,255,.08);overflow:hidden;margin:8px 0 4px}
.accbar i{display:block;height:100%;background:linear-gradient(90deg,#2f9a68,#45d08f);transition:width .2s}
.newpill{display:inline-block;margin-left:6px;padding:1px 8px;border-radius:999px;background:#2c1f47;color:#c49bff;font-size:11px;font-weight:700;vertical-align:1px}
.ptabs.three{grid-template-columns:repeat(3,1fr)}
.ptbody .dotab{display:flex;flex-direction:column;gap:8px}.ptbody .dotab .arow{display:grid;grid-template-columns:auto minmax(0,1fr) auto;align-items:center;gap:10px;padding:10px;border:1px solid var(--line);border-radius:12px}
.aprow,.aptl li{gap:10px;align-items:center}
.aprow{display:flex;flex-wrap:wrap;margin:8px 0}
.apk{margin:10px 0}
.apm,.aptl{display:flex;flex-direction:column}
.aptl{list-style:none;margin:6px 0;padding:0;gap:6px}
.aptl li{display:grid;grid-template-columns:78px minmax(0,1fr) 54px;padding:10px 12px;border-radius:12px;border:1px solid var(--line);background:rgba(11,18,32,.55)}
.apg b{display:block;font:700 16px var(--fd)}
.apg small{color:var(--mut);font-size:11px}
.apm{gap:4px;font-size:13px;min-width:0}
.app,.rt em{text-align:right;font:700 20px var(--fd)}
.app small{display:block;font:600 11px Inter,sans-serif}
.rt,.rtg{display:grid}
.rtg{grid-template-columns:repeat(auto-fit,minmax(220px,1fr));gap:8px 18px;margin:4px 0 6px}
.rt{grid-template-columns:112px minmax(0,1fr) 30px;align-items:center;gap:10px;font-size:13px;cursor:help}
.app small,.rt span{color:var(--mut)}
.rt i,.rt i b{display:block;border-radius:4px}
.rt i{height:8px;background:rgba(255,255,255,.08);overflow:hidden}
.rt i b{height:100%}
.rt em{font:700 16px var(--fd);font-style:normal}
.mwsc .dg{display:inline-block;font-style:normal;min-width:.6em}
.mwsc.goal{animation:goalFlash 1.6s ease-out 1}
.mwsc .dg.up{animation:digitUp .6s cubic-bezier(.3,1.5,.5,1) 1;color:var(--good)}
#t-live.bump{display:inline-block;animation:numBump .7s cubic-bezier(.3,1.6,.5,1) 1}
@keyframes digitUp{from{transform:translateY(90%);opacity:0}to{transform:none;opacity:1}}
@keyframes goalFlash{0%{box-shadow:0 0 0 0 rgba(69,208,143,.8);background:rgba(69,208,143,.35)}100%{box-shadow:0 0 0 12px rgba(69,208,143,0)}}
@keyframes numBump{0%{transform:scale(1)}40%{transform:scale(1.35);color:var(--good)}100%{transform:scale(1)}}
.alerts.clear{border-color:rgba(69,208,143,.45);background:rgba(16,56,42,.45)}
.alerts.clear .ah{color:var(--acc)}
#planner .chip.pc[data-card]{touch-action:none;user-select:none;-webkit-user-select:none}
.chip.pc.dragghost,.dragghost{position:absolute!important;left:0!important;top:0!important;margin:0!important;z-index:60;pointer-events:none;opacity:.95;filter:drop-shadow(0 12px 18px rgba(0,0,0,.5));transform-origin:center;transition:none;will-change:transform}
#planner .chip.pc[data-card] *{-webkit-user-drag:none;-webkit-touch-callout:none;user-select:none}
#planner .chip.pc[data-card] img,#planner .chip.pc[data-card] svg{pointer-events:none}
#planner .chip.pc[data-card]{-webkit-touch-callout:none;-webkit-tap-highlight-color:transparent;cursor:grab}
#planner .chip.pc.dropover .jsh{outline-color:var(--gold);outline-style:solid;transform:scale(1.06)}
.dragghost .jsh{transform:scale(1.08)}
#planner .chip.pc.dragsrc{opacity:.3}
#planner .chip.pc.droppable .jsh{outline:2px dashed var(--acc);outline-offset:3px;border-radius:12px}
#planner .chip.pc.dropover{transform:translateY(-4px) scale(1.06)}
#planner .chip.pc.dropover .jsh{outline:3px solid var(--acc);background:rgba(69,208,143,.18)}
.try.undo{display:inline-flex;align-items:center;gap:6px;max-width:260px}
.try.undo small{color:var(--mut);font-size:11px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;max-width:170px}
.try.undo:disabled{opacity:.4;cursor:default}
.cand .cn b{display:inline-flex;align-items:center}
/* ---------- v3.11 ---------- */
/* official kit images over the drawn shirt fallback */
.kitw{position:relative;display:inline-grid;place-items:center;flex:none;width:38px;height:44px}
.kitw>svg{width:38px;height:33px}
.kitw .kimg{position:absolute;inset:0;width:100%;height:100%;object-fit:contain;filter:drop-shadow(0 3px 4px rgba(0,0,0,.45))}
.kitw.ok>svg,.kitw .kimg.gone{display:none}
.who .kitw{width:24px;height:30px}.who .kitw>svg{width:24px;height:22px}
.kitw.big{width:64px;height:80px}.kitw.big>svg{width:56px;height:49px}
.ph .kitw.big{margin-right:40px}
.kitw.huge{width:120px;height:150px}.kitw.huge>svg{width:96px;height:84px}
.kitw.jk{width:70px;height:64px}.kitw.jk>svg{width:64px;height:58px}
.jsh.real .jcode{display:none}
/* planner: tools never float over the week navigation; formation sits on the pitch */
.plan3 .pltools{position:static;margin:0 0 8px;justify-content:flex-start}
.pitch{position:relative}
.fmpill{position:absolute;left:10px;bottom:10px;z-index:2;display:flex;flex-direction:column;align-items:center;min-width:70px;padding:4px 10px;border-radius:12px;background:rgba(11,18,32,.78);border:1px solid rgba(255,255,255,.12);backdrop-filter:blur(6px)}
.fmpill b{font:700 16px/1.1 var(--fd);color:#e8eef7;letter-spacing:.5px}
.fmpill small{font-size:11px;color:var(--gold);text-transform:uppercase;letter-spacing:.05em}
/* Home: compact, even 3 x 2 grid that fits the panel */
#s-home{gap:10px}
#s-home .hero{padding:12px 16px;gap:10px 20px;border-radius:12px}
#s-home .hero .hl h2{font-size:26px;margin:0 0 2px}
#s-home .hero .sub{font-size:12px}
#s-home .eyebrow{font-size:11px}
#s-home .herok>div{padding:0 14px;min-width:92px;gap:1px}
#s-home .herok small{font-size:11px}
#s-home .herok b{font-size:20px}
#s-home .herok .hs2{font-size:11px}
#s-home .livestrip{padding:6px 12px;font-size:12px}
#s-home .viewing{font-size:12px}
.hgrid{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));grid-auto-rows:minmax(260px,auto);gap:10px}
.hc{padding:12px;border-radius:12px;font-size:12px;line-height:1.45;min-width:0;display:flex;flex-direction:column;overflow:hidden}
.hc>*{flex:none}
.hc .th{margin-bottom:8px;flex-wrap:nowrap}
.hc .th h3,.hc h3{font:700 16px var(--fd);margin:0;text-transform:none;letter-spacing:.2px;color:var(--fg)}
.hc .th .muted,.hc .slg{font-size:11px;white-space:nowrap}
.hc .slg{gap:8px}
.hc .arows{gap:6px}
.hc .arow{padding:7px 9px;font-size:12px;gap:8px}
.hc .arow .tag{min-width:62px;font-size:11px}
.hc .cta{padding:5px 10px;font-size:11px}
.hc details.more summary{font-size:12px;padding:4px 0}
.hc.alc{padding:0}
.hc.alc .alerts{margin:0;flex:1;border-radius:12px;padding:10px 12px;gap:6px;font-size:12px;overflow:auto}
.hc.alc .alerts .ah{font-size:13px}
.hc.gwc .h3{margin:0 0 8px;font:700 16px var(--fd);text-transform:none;letter-spacing:.2px;color:var(--fg)}
.hc.gwc .h3 .muted{font:500 11px Inter,system-ui,sans-serif}
.hc .kpis.uni{grid-template-columns:repeat(2,minmax(0,1fr));gap:6px}
.hc .kpis.uni .kpi{min-height:0;padding:6px 9px;border-radius:9px}
.hc .kpi small{font-size:11px}
.hc .kpi b{font-size:16px;line-height:1.15}
.hc .kpi span{font-size:11px}
.hc .kpi .was{display:none}
.hc .schart{max-height:none;flex:1 1 auto;min-height:0;height:auto}
.hc .fine{font-size:11px;margin-top:4px}
.hnl{display:flex;flex-direction:column;gap:6px;min-height:0;overflow:hidden}
.hni{display:grid;grid-template-columns:58px minmax(0,1fr);gap:10px;align-items:center;text-decoration:none;color:var(--fg);padding:5px;border-radius:10px;border:1px solid transparent}
.hni:hover{border-color:var(--line);background:rgba(255,255,255,.03)}
.hnp{width:58px;height:44px;border-radius:8px;display:block}
.hnp .crw.big{transform:scale(.6)}
.hnp .nart.gen b{font-size:8px;padding:2px 4px}
.hnt{display:flex;flex-direction:column;gap:2px;min-width:0}
.hnt b{font-size:13px;font-weight:600;line-height:1.3;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
.hnt small{font-size:11px;color:var(--mut);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.hnt small i{font-style:normal;font-weight:700;color:var(--acc);margin-right:5px}.hnt small i.neg{color:var(--bad)}
@media (max-width:640px){.hni:nth-child(n+4){display:none}}
.panel>.top{position:relative;z-index:25}
.idw{position:relative;display:flex;flex:1;min-width:0}
.idw input{flex:1;min-width:0;border-top-right-radius:0!important;border-bottom-right-radius:0!important}
.idb{display:flex;align-items:center;gap:2px;padding:0 9px;border:1px solid var(--line);border-left:0;border-radius:0 10px 10px 0;background:rgba(69,208,143,.12);color:var(--acc);cursor:pointer}
.idb:hover,.idb[aria-expanded=true]{background:rgba(69,208,143,.24)}
.idmenu{position:absolute;left:0;top:calc(100% + 6px);z-index:40;width:min(340px,calc(100vw - 24px));max-height:min(440px,70vh);overflow:auto;padding:8px;border-radius:14px;border:1px solid var(--line);background:#0d1626;box-shadow:0 18px 50px rgba(0,0,0,.6);display:flex;flex-direction:column;gap:4px}
.idmenu[hidden]{display:none}
.idh{display:flex;justify-content:space-between;font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:.08em;color:var(--mut);padding:6px 6px 2px}
.idh span{color:var(--acc)}
.idn{margin:2px 6px 6px;font-size:12px;color:var(--mut)}
.idr{display:flex;align-items:center;gap:4px;border-radius:10px;border:1px solid var(--line);background:rgba(11,18,32,.6)}
.idr.on{border-color:var(--acc);background:rgba(69,208,143,.1)}
.idgo{flex:1;min-width:0;display:flex;align-items:center;gap:10px;padding:8px 10px;background:none;border:0;color:var(--fg);text-align:left;cursor:pointer;font:inherit}
.idgo span{display:flex;flex-direction:column;min-width:0}
.idgo b{font-size:14px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.idgo small{font-size:11px;color:var(--mut)}
.idme,.idav{flex:none;width:28px;height:28px;border-radius:50%;display:grid;place-items:center;font-style:normal;font-weight:700;font-size:13px}
.idme{background:var(--gold);color:#2a1f00}
.idav{background:#25406b;color:#fff}
.iddel{flex:none;width:30px;height:30px;margin-right:6px;border-radius:50%;border:0;background:none;color:var(--mut);font-size:20px;cursor:pointer}
.iddel:hover{color:var(--bad);background:rgba(255,255,255,.05)}
.idact{display:flex;flex-wrap:wrap;gap:6px;padding:8px 4px 2px;border-top:1px solid var(--line);margin-top:4px}
.hlist{display:flex;flex-direction:column;gap:4px}
.hlr{display:grid;grid-template-columns:auto minmax(0,1fr) auto;align-items:center;gap:8px;width:100%;text-align:left;font:inherit;font-size:12px;color:var(--fg);padding:6px 8px;border-radius:9px;border:1px solid var(--line);background:rgba(11,18,32,.55);cursor:pointer}
.hlr:hover:not(:disabled){border-color:rgba(69,208,143,.5)}
.hlr:disabled{cursor:default}
.hlr.pub{opacity:.75}
.hlr .ln{overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-weight:600}
.hlr .lr{white-space:nowrap;font-size:12px}
.hlr .lt{font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:.05em;padding:2px 6px;border-radius:6px;background:var(--acc2);color:var(--acc)}
.hlr .lt.t-h2h{background:#2a2350;color:#b9a8ff}
.hlr .lt.t-cup{background:var(--warnbg);color:var(--gold)}
.hlr.on{border-color:var(--acc);background:rgba(69,208,143,.1)}
/* v3.16 My Team: tools (settings style) vs player actions (accent) */
.pltools2{display:flex;flex-wrap:wrap;gap:6px;align-items:center;margin:0 0 8px}
.tbtn{display:inline-flex;align-items:center;justify-content:center;gap:5px;height:30px;padding:0 11px;border-radius:8px;border:1px solid var(--line);background:rgba(255,255,255,.05);color:#cfd8e6;font:600 12px Inter,system-ui,sans-serif;cursor:pointer;white-space:nowrap}
.tbtn:hover:not(:disabled){border-color:#8aa0bf;color:var(--fg)}
.tbtn:disabled{opacity:.35;cursor:default}
.tbtn.ico{width:30px;padding:0}
.tbtn.warn{color:#ff9f9f;border-color:rgba(255,107,107,.35)}
#planner .gwnav{display:grid!important;grid-template-columns:34px minmax(0,1fr) 34px;align-items:center;gap:6px;margin:0 0 6px;padding:0;width:100%;box-sizing:border-box}
#planner .gwnav .gwt{min-width:0!important;width:auto!important;text-align:center}
#planner .gwnav .gwt{flex:1;min-height:0;padding:5px 10px;border-radius:10px}
#planner .gwnav .gwt b{font-size:16px}#planner .gwnav .gwt small{font-size:11px}
#planner .gwnav .gwb{width:34px;height:34px}
#planner .gwnav .gwsum{grid-column:1/-1;text-align:center;font-size:11px;color:var(--gold)}
#planner .ppill{min-width:0;padding:3px 8px;border-radius:9px}
#planner .ppill b{font-size:14px}#planner .ppill small{font-size:11px;letter-spacing:.03em}#planner .ppill .pd{font-size:11px;margin-top:0}
#planner .fmpill b{font-size:14px}
#planner .pitch{display:grid;grid-template-columns:minmax(0,1fr) auto minmax(0,1fr);align-items:start}
#planner .pitch>.ppills{min-width:0}#planner .pitch>.ppills .ppill{flex:1 1 0;min-width:0;overflow:hidden}
#planner .ppill small{white-space:nowrap;overflow:hidden;text-overflow:ellipsis;max-width:100%}
@media (max-width:420px){#planner .ppill{padding:2px 4px}#planner .ppill b{font-size:12px}#planner .ppill small{font-size:7.5px}#planner .fmpill{padding:2px 8px}#planner .fmpill b{font-size:12px}}
#planner .pitch>*{grid-column:1/-1}
#planner .pitch>.ppills{position:static;grid-column:auto;grid-row:1;flex-direction:row;gap:4px;padding:6px 6px 2px}
#planner .pitch>.ppills.l{grid-column:1;justify-content:flex-start}
#planner .pitch>.ppills.r{grid-column:3;justify-content:flex-end}
#planner .pitch>.fmpill{position:static;grid-column:2;grid-row:1;align-self:center;margin-top:6px}
#planner .pzoom,#planner #pl-info,#planner .infobar{display:none!important}
#planner .plleft,#planner .plside{min-width:0}
@media (max-width:860px){#planner .plgrid{grid-template-columns:minmax(0,1fr)!important}}
#planner .pitch,#planner .benchbox{min-width:0;max-width:100%;box-sizing:border-box}
@media (min-width:861px){
  #planner.sidefit .plgrid{align-items:start}
  #planner.sidefit .plside{height:var(--plh,auto);display:flex;flex-direction:column}
  #planner.sidefit .plside .ptbody{flex:1;min-height:0;overflow:hidden;display:flex;flex-direction:column}
.sidescroll .ptbody{overflow-y:auto;overscroll-behavior:contain;display:block}
}
.tmore{all:unset;cursor:pointer;margin-top:auto;align-self:center;padding:7px 14px;border-radius:999px;border:1px solid var(--line);color:var(--acc);font:600 13px Inter,sans-serif;background:rgba(69,208,143,.06)}
.tmore:hover{background:rgba(69,208,143,.14)}
.ptbody>.chipbox{border:0!important;background:none!important;padding:0!important;border-radius:0}
.chipgrid{grid-auto-rows:1fr}
.pstool{display:flex;flex-wrap:wrap;gap:8px;align-items:center;margin:6px 0 8px}
.pstool .ps-modes{margin:0}
.pstool #ps-q{flex:1 1 200px;min-width:0;height:36px;box-sizing:border-box}
.pstool .pseg{flex:none}
#s-fix .ps-info{margin:6px 0 0;padding:6px 10px;font-size:12px}
.ps-meta{margin:4px 0 0;font-size:12px}
table.pstats td{padding:3px 9px;line-height:1.2}
table.pstats td.ps-name{white-space:nowrap}
table.pstats td.ps-name .picon.face{width:20px;height:24px;min-width:20px;max-width:20px;max-height:24px;border-radius:5px;margin-right:6px;vertical-align:middle}
table.mkt td.pl .picon.face{width:20px;height:24px;min-width:20px;max-width:20px;max-height:24px;border-radius:5px}
table.mkt td{padding-top:4px;padding-bottom:4px}
/* v3.37 Player stats: compact columns so every column fits; narrow screens pick a column group */
table.pstats{width:100%;min-width:0;table-layout:auto;font-size:12px}
table.pstats th,table.pstats td{padding:3px 3px}
table.pstats td.ps-name{max-width:none}
table.pstats td.ps-name a.pn{display:inline-block;max-width:84px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;vertical-align:middle}
table.pstats{font-size:11px}
table.pstats th.ps-group{font-size:11px;letter-spacing:.06em;white-space:nowrap;padding:6px 4px 2px}
table.pstats thead tr:nth-child(2) th{font-size:11px;padding:2px 4px 6px;white-space:nowrap}
table.pstats th.ps-base{font-size:11px;white-space:nowrap}
table.pstats td.ps-name{min-width:0;max-width:150px;overflow:hidden;text-overflow:ellipsis}
table.pstats th.ps-name{min-width:0}
.psgrp .psg-m{display:none}
.pslab{font-size:11px;font-weight:600;letter-spacing:.06em;text-transform:uppercase;color:var(--mut);align-self:center;margin:0 -2px 0 4px}
.pspos button{min-width:42px}
table.pstats td.ps-name,table.pstats th.ps-name{min-width:0!important}
@media (max-width:420px){#s-fix .ps-meta{display:none}table.pstats td.ps-name .picon.face{display:none}.pstool .pseg button,.pstool .ps-modes button{padding:6px 8px;font-size:12px}table.pstats th,table.pstats td{padding:3px 2px}}
/* desktop: three column sets */
@media (min-width:901px){
  .ps-scroll .g4,.ps-scroll .g6,.ps-scroll .g7{display:none}
  .ps-scroll:is([data-g="exp"],[data-g="g4"],[data-g="g6"]) :is(.g1,.g2,.g3){display:none}
  .ps-scroll:is([data-g="exp"],[data-g="g4"],[data-g="g6"]) :is(.g4,.g6){display:table-cell}
  .ps-scroll:is([data-g="def"],[data-g="g7"]) :is(.g1,.g2,.g3){display:none}
  .ps-scroll:is([data-g="def"],[data-g="g7"]) .g7{display:table-cell}
  table.pstats{font-size:12px}
  table.pstats th,table.pstats td{padding:4px 6px}
}
/* phones and narrow windows: one small set at a time */
@media (max-width:900px){
  .psgrp .psg-d{display:none}.psgrp .psg-m{display:inline-flex}
  .ps-scroll .g1,.ps-scroll .g2,.ps-scroll .g3,.ps-scroll .g4,.ps-scroll .g5,.ps-scroll .g6,.ps-scroll .g7,.ps-scroll .pbs{display:none}
  .ps-scroll:is([data-g="g1"],[data-g="att"]) .g1,.ps-scroll[data-g="g2"] .g2,.ps-scroll:is([data-g="g4"],[data-g="exp"]) .g4,.ps-scroll[data-g="g6"] .g6,.ps-scroll:is([data-g="g7"],[data-g="def"]) .g7{display:table-cell}
  table.pstats td.ps-name a.pn{max-width:74px}
  .pstool .ps-modes button{padding:7px 9px}
  .ps-scroll .g7x,.ps-scroll .g7w,.ps-scroll .g2x{display:none!important}
  .ps-scroll:is([data-g="g7"],[data-g="def"]) .g7n{display:table-cell}
  table.pstats th,table.pstats td{padding:3px 3px}
}
.ps-scroll .g7n{display:none}
/* v3.37 Head to head redesign */
#s-fix .cmptop{display:flex;align-items:flex-end;justify-content:space-between;gap:10px;flex-wrap:wrap;margin-bottom:10px}
#s-fix .cmpact{display:flex;gap:6px;flex-wrap:wrap}
#s-fix .cmpgrid:not(.pick) .cadd{display:inline-flex}
@media (min-width:861px){#s-fix .cadd{display:none!important}}
#s-fix .cmpsel{display:none}
#s-fix .cmpl{border-radius:14px;background:linear-gradient(180deg,rgba(255,255,255,.04),rgba(255,255,255,.01))}
#s-fix .crow{border-radius:10px}
#s-fix .cmpw{padding-top:12px}
#s-fix table.cmpv{border-collapse:separate;border-spacing:8px 0;width:100%}
#s-fix table.cmpv th.cph{vertical-align:bottom;padding:0 0 10px;min-width:118px;background:none;border:0}
#s-fix .pcard{position:relative;display:flex;flex-direction:column;align-items:center;gap:3px;padding:14px 8px 10px;border-radius:16px;
  background:linear-gradient(180deg,color-mix(in srgb,var(--kc) 32%,transparent) 0%,rgba(16,26,44,.6) 58%);border:1px solid rgba(255,255,255,.1);box-shadow:inset 0 1px 0 rgba(255,255,255,.1)}
#s-fix .pcard.lead{border-color:rgba(69,208,143,.6);box-shadow:0 0 0 1px rgba(69,208,143,.25),0 10px 26px rgba(69,208,143,.14),inset 0 1px 0 rgba(255,255,255,.12)}
#s-fix .pcard.lead::after{content:"Leader";position:absolute;top:-9px;left:50%;transform:translateX(-50%);padding:1px 8px;border-radius:999px;background:var(--acc);color:#04221a;font:700 11px Inter,sans-serif;letter-spacing:.04em}
#s-fix .pcard .cx{position:absolute;top:6px;right:6px;width:22px;height:22px;border-radius:50%;border:0;background:rgba(0,0,0,.35);color:#cfd8e6;cursor:pointer;font-size:14px;line-height:22px;padding:0}
#s-fix .pcard a.pn{font:700 14px var(--fd);text-transform:none;color:var(--fg)}
#s-fix .pcard small{font-size:11px;color:var(--mut)}
#s-fix .pcard .pkpi{display:flex;flex-direction:column;align-items:center;margin-top:4px}
#s-fix .pcard .pkpi b{font:700 26px/1 var(--fd);color:var(--fg)}
#s-fix .pcard.lead .pkpi b{color:var(--acc)}
#s-fix table.cmpv td{padding:9px 6px;text-align:center;border-top:1px solid rgba(255,255,255,.06);background:rgba(255,255,255,.015)}
#s-fix table.cmpv tr:hover td{background:rgba(255,255,255,.04)}
#s-fix table.cmpv td b{font:700 16px var(--fd);color:var(--fg)}
#s-fix table.cmpv td.win b{color:var(--acc)}
#s-fix table.cmpv td b.best::after{display:none}
#s-fix table.cmpv .cbar{display:block;height:5px;border-radius:3px;background:rgba(255,255,255,.07);margin:6px auto 0;max-width:120px;overflow:hidden}
#s-fix table.cmpv .cbar i{display:block;height:100%;border-radius:3px;background:linear-gradient(90deg,#3a5683,#5a7bb0)}
#s-fix table.cmpv td.win .cbar i{background:linear-gradient(90deg,#2f9a68,#6fe0a8)}
#s-fix table.cmpv .cfx{margin-bottom:4px}
#s-fix table.cmpv th.cmk{text-align:left;font-size:11px;letter-spacing:.06em;text-transform:uppercase;color:var(--mut);white-space:nowrap;padding:0 10px 0 4px;border-top:1px solid rgba(255,255,255,.06);background:none}
@media (max-width:600px){
  #s-fix .cmpw{padding-top:14px;overflow-y:visible}
  #s-fix table.cmpv{border-spacing:4px 0}
  #s-fix table.cmpv th.cmk{width:44px;max-width:44px;white-space:normal;font-size:11px;padding:0 2px;line-height:1.2}
  #s-fix table.cmpv th.cph{min-width:88px}
  #s-fix .pcard{padding:12px 4px 8px;border-radius:12px}
  #s-fix .pcard .picon.face.fbig{width:36px;height:44px;min-width:36px;max-width:36px;max-height:44px}
  #s-fix .pcard a.pn{font-size:13px}
  #s-fix .pcard small{font-size:11px}
  #s-fix .pcard .pkpi b{font-size:20px}
  #s-fix table.cmpv td{padding:7px 3px}
  #s-fix table.cmpv td b{font-size:14px}
}
/* v3.37 season chart */
.schart.sdiv .base{stroke:rgba(255,255,255,.28);stroke-width:1}
.schart.sdiv .lbl{font:700 12px var(--fd)}
.schart.sdiv .lbl.hi{fill:#6fe0a8}.schart.sdiv .lbl.lo{fill:#ff8a8a}
.schart.sdiv .rline{fill:none;stroke:#f6c343;stroke-width:2;stroke-linejoin:round;filter:drop-shadow(0 0 3px rgba(246,195,67,.45))}
.schart.sdiv .rdot{fill:#f6c343;stroke:#0b1220;stroke-width:1.2}
.schart.sdiv .rlab{font:700 11px Inter,sans-serif;fill:#f6c343}
.schart.sdiv .rk{font-size:11px}
.schart.sdiv .rband{fill:rgba(246,195,67,.05);stroke:rgba(246,195,67,.15)}
.schart.sdiv .rlab.dim{fill:rgba(246,195,67,.75);font-weight:600}
.schart.sdiv{max-height:300px}
.pph .pflag.t,.panel>.top .tfl .t{left:0;right:0;background-image:url(data:image/jpeg;base64,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);background-size:100% 100%;background-position:center;mix-blend-mode:hard-light;opacity:.95;transform:none}
.pph .pflag.t{animation:silkDrift 14s ease-in-out infinite alternate}
@keyframes silkDrift{from{background-position:0% 50%;background-size:115% 115%}to{background-position:100% 50%;background-size:115% 115%}}
@media (prefers-reduced-motion:reduce){.pph .pflag.t{animation:none}}
.pph.egy .pflag{display:none}
.pph.egy{--egyimg:url(data:image/jpeg;base64,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)}.pph.egy::before{content:"";position:absolute;inset:0;z-index:-2;pointer-events:none;background:var(--egyimg) center/cover no-repeat}
.panel>.top.egy .tfl i{display:none}
.panel>.top.egy .tfl{background:url(data:image/jpeg;base64,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) center/100% 100% no-repeat}

/* ===== v3.41 layout preview: icon rail (desktop), profile banner, underlined page tabs, upper-case section titles ===== */
.hbn{min-height:112px;padding:16px 20px!important;gap:16px!important;margin-bottom:12px;align-items:center}
.hbn .hbav{position:relative;flex:none;width:76px;height:76px;border-radius:50%;display:grid;place-items:center;background:radial-gradient(circle at 30% 25%,#2a4a7a,#13233f 70%);box-shadow:0 0 0 3px rgba(255,255,255,.9),0 8px 22px rgba(0,0,0,.45)}
.hbn .hbav b{font:700 26px var(--fd);color:#fff;letter-spacing:.02em}
.hbn .hbfl{position:absolute;right:-6px;bottom:2px;width:30px;height:20px;object-fit:cover;border-radius:3px;box-shadow:0 0 0 2px #0b1220,0 2px 6px rgba(0,0,0,.5)}
.hbn .hbtx{flex:1;min-width:0;display:flex;flex-direction:column;gap:2px}
.hbn .hbtx .eyebrow{color:var(--acc);font-size:11px;letter-spacing:.12em;text-transform:uppercase}
.hbn .hbtx h2{font:700 30px/1.05 var(--fd);margin:0;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;text-shadow:0 2px 6px rgba(0,0,0,.7)}
.hbn .hbsub{font-size:13px;color:#d7deea;text-shadow:0 1px 3px rgba(0,0,0,.9)}
.hbn .hbkp{display:flex;align-items:center;gap:18px;flex:none}
.hbn .hbkp>div{display:flex;flex-direction:column;align-items:flex-end;text-shadow:0 1px 4px rgba(0,0,0,.9)}
.hbn .hbkp small{font-size:11px;letter-spacing:.08em;text-transform:uppercase;color:#cfd8e6}
.hbn .hbkp b{font:700 26px var(--fd);color:#fff}
.hbn .cdpill{margin:0;backdrop-filter:blur(6px);background:rgba(11,18,32,.55);border:1px solid rgba(69,208,143,.4)}
#s-home .hero2 .deadline-head{display:none}
#s-home .hero2{padding:12px 18px!important}
#s-home .hero2 .herok{margin:0!important;width:100%;grid-template-columns:repeat(auto-fit,minmax(130px,1fr))!important}
#s-home .hero2 .herok>div:nth-child(1),#s-home .hero2 .herok>div:nth-child(2){display:none}
#s-home .hero2 .herok>div:nth-child(3){border-left:0;padding-left:0}
/* v3.53: Projected / Bank / Free transfers: centred, in the app's display font and colours */
#s-home .hero2{padding:14px 10px!important}
#s-home .hero2 .herok>div{align-items:center!important;justify-content:center;text-align:center;padding:4px 12px!important;gap:3px!important;border-left:1px solid var(--line)!important}
#s-home .hero2 .herok>div:nth-child(3){border-left:0!important}
#s-home .hero2 .herok small{font:700 12px/1.2 var(--fd)!important;letter-spacing:.14em!important;text-transform:uppercase;color:var(--acc)!important}
#s-home .hero2 .herok b{font:700 34px/1.05 var(--fd)!important;letter-spacing:.01em;color:var(--fg);font-variant-numeric:tabular-nums}
#s-home .hero2 .herok .hs2{font:500 13px/1.3 Inter,system-ui,sans-serif!important;color:var(--mut)!important}
#s-home .hero2 .herok>div{justify-content:flex-start!important}
@media (max-width:640px){#s-home .hero2 .herok small{min-height:2.5em;display:flex!important;align-items:flex-end;justify-content:center;font-size:11px!important;letter-spacing:.07em!important}#s-home .hero2 .herok b{font-size:28px!important}#s-home .hero2 .herok .hs2{font-size:12px!important}}
@media (max-width:640px){#s-home .hero2 .herok{grid-template-columns:repeat(3,minmax(0,1fr))!important;row-gap:0!important}#s-home .hero2 .herok>div{padding:0 6px!important;border-left:0!important}#s-home .hero2 .herok b{font-size:20px}#s-home .hero2 .herok .hs2{font-size:11px}}
@media (max-width:640px){
  .hbn{min-height:0;padding:12px 14px!important;gap:12px!important;flex-wrap:wrap}
  .hbn .hbav{width:54px;height:54px}.hbn .hbav b{font-size:20px}.hbn .hbfl{width:24px;height:16px;right:-5px}
  .hbn .hbtx h2{font-size:26px}
  .hbn .hbkp{width:100%;justify-content:space-between;gap:10px}.hbn .hbkp>div{align-items:flex-start}.hbn .hbkp b{font-size:20px}
}
/* section titles: upper-case, quieter */
#s-home .card.hc .th h3,.ptl h2{text-transform:uppercase;letter-spacing:.05em}
#s-home .card.hc .th h3{font-size:14px}
@media (min-width:980px){
  .panel{display:grid;grid-template-columns:86px minmax(0,1fr);grid-template-rows:auto auto minmax(0,1fr)}
  .panel>.top{grid-column:1 / -1;grid-row:1}
  .panel>nav#nav{grid-column:1;grid-row:2 / 4;flex-direction:column;flex-wrap:nowrap;align-items:stretch;justify-content:flex-start;gap:6px;padding:12px 8px;border-bottom:0;border-right:1px solid var(--line);background:rgba(8,13,24,.72)}
  .panel>nav#nav .nink{display:none}
  .panel>nav#nav a{flex-direction:column;justify-content:center;gap:5px;padding:11px 4px 9px;border-radius:14px;font-size:11px;text-align:center;border:1px solid transparent}
  .panel>nav#nav a svg{width:22px;height:22px}
  .panel>nav#nav a.on{background:linear-gradient(180deg,rgba(69,208,143,.22),rgba(69,208,143,.08));color:var(--acc);border-color:rgba(69,208,143,.45);box-shadow:inset 0 1px 0 rgba(255,255,255,.08)}
  .panel>nav#nav a:not(.on):hover{background:rgba(255,255,255,.05);color:var(--fg)}
  .panel>nav#nav .navsub{display:none}
  .panel>.subnav{grid-column:2;grid-row:2;padding:0 18px;background:transparent;border-bottom:1px solid var(--line)}
  .panel>.subnav:not([hidden]){display:flex}
  .panel>.subnav .seg{background:none;border:0;padding:0;gap:4px;border-radius:0}
  .panel>.subnav .seg button{background:none!important;color:var(--mut);border-radius:0;padding:12px 14px 10px;border-bottom:2px solid transparent;font-size:13px}
  .panel>.subnav .seg button.on{color:var(--fg)!important;background:none!important;border-bottom-color:var(--acc);box-shadow:none!important;font-weight:700}
  .panel>.subnav .seg button:hover{color:var(--fg)}
  .panel>main#out{grid-column:2;grid-row:3;min-height:0}
}

/* ===== v3.43 theme "Midnight": slate navy (not black), soft emerald + violet, upright headings, one type scale ===== */
.root{font:400 14px/1.5 Inter,system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;letter-spacing:0}
.root b,.root strong{font-weight:600}
.panel{background:radial-gradient(800px 420px at 95% -10%,rgba(124,108,240,.16),transparent 62%),radial-gradient(700px 400px at -8% 110%,rgba(69,208,143,.08),transparent 60%),#0f1524!important}
.panel>.bgfx{display:none}
.panel>.top{background:rgba(15,21,36,.92)!important;border-bottom:1px solid rgba(255,255,255,.08)!important}
.brand b{font-family:var(--fh);font-weight:700;font-size:20px;letter-spacing:.01em}
section.s,.card{background:#161e30!important;border:1px solid rgba(255,255,255,.08)!important;backdrop-filter:none}
/* headings: one family, upright, three sizes */
section.s>h2,.ptl h2,.cmptop h3{font-family:var(--fh)!important;font-weight:700!important;font-size:26px!important;text-transform:none;letter-spacing:.005em}
#s-home .card.hc .th h3,.h3{font-family:var(--fh)!important;font-weight:700!important;font-size:16px!important;text-transform:uppercase;letter-spacing:.04em}
.eyebrow{font-family:Inter,sans-serif;font-weight:600;font-size:11px!important;letter-spacing:.1em;text-transform:uppercase}
.sub,.muted,small{font-weight:400}
/* card header bars: same idea, calmer colours, no glow */
#s-home .card.hc{padding-top:0!important;border-radius:14px!important;overflow:hidden}
#s-home .card.hc>.th:first-child{margin:0 -12px 10px!important;width:auto!important;padding:9px 12px;background:var(--hbar,#26304a);border-bottom:1px solid rgba(255,255,255,.06)}
#s-home .card.hc>.th:first-child h3{color:#fff}
#s-home .card.hc>.th:first-child .muted,#s-home .card.hc>.th:first-child small,#s-home .card.hc>.th:first-child span{color:rgba(255,255,255,.82)}
#s-home .card.hc.do{--hbar:linear-gradient(90deg,#2f7d5a,#245e46)}
#s-home .card.hc.lgc,#s-home .card.hc.seast{--hbar:linear-gradient(90deg,#5a4bb3,#3f357f)}
#s-home .card.hc.gwc,#s-home .card.hc.newst{--hbar:linear-gradient(90deg,#3466a8,#284e80)}
#s-home .card.hc.alc{padding:0!important}
#s-home .card.hc.alc .alerts{border:0!important;border-radius:0!important;margin:0!important;padding:0 12px 12px!important;background:rgba(120,40,52,.18)!important}
#s-home .card.hc.alc .alerts .ah{margin:0 -12px 6px;padding:9px 12px;background:linear-gradient(90deg,#a33a4b,#7c2b39);display:flex;flex-wrap:wrap;gap:4px 10px;align-items:baseline;justify-content:space-between}
#s-home .card.hc.alc .alerts.clear .ah{background:linear-gradient(90deg,#2f7d5a,#245e46)}
#s-home .card.hc.alc .alerts .ah>b{font-family:var(--fh);font-weight:700;text-transform:uppercase;letter-spacing:.04em;font-size:16px;color:#fff}
#s-home .card.hc.alc .alerts .ah span,#s-home .card.hc.alc .alerts .ah span b{color:rgba(255,255,255,.88)!important}
#s-home .hero2{background:#161e30!important;border:1px solid rgba(255,255,255,.08)!important}
#s-home .hero2 .herok b,.hbn .hbkp b{font-family:var(--fh);font-weight:700;font-size:26px}
/* tags */
.arow .tag{font-weight:600;letter-spacing:.06em;text-transform:uppercase;font-size:11px}
.arow.t-transfer .tag{background:rgba(69,208,143,.14);color:#7fe0b2}
.arow.t-captain .tag{background:rgba(232,190,90,.14);color:#efcf7d}
.arow.t-lineup .tag{background:rgba(80,140,220,.16);color:#9fc2f2}
.arow.t-chip .tag{background:rgba(124,108,240,.18);color:#c3b8fa}
/* buttons: no italics, no glow */
#f button[type=submit],.go{background:#45d08f!important;color:#06231a!important;box-shadow:none;font-weight:600}
@media (min-width:980px){.panel>nav#nav{background:#121a2b!important;border-right:1px solid rgba(255,255,255,.07)!important}}
nav#nav a.on,.subnav .seg button.on{box-shadow:none}
/* home banner */
.hbn{border:1px solid rgba(124,108,240,.35)!important;box-shadow:0 8px 24px rgba(0,0,0,.25)!important}
.hbn .hbav{background:radial-gradient(circle at 35% 25%,#5b1a63,#37003c 70%)!important;box-shadow:0 0 0 3px #fff,0 8px 22px rgba(0,0,0,.45)!important}
.hbn .hbav .hblion{position:absolute;inset:14%;background:url(data:image/png;base64,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) center/contain no-repeat}
.hbn .hbtx h2{font-family:var(--fh);font-weight:700;font-size:32px!important;letter-spacing:.005em}
@media (max-width:640px){.hbn .hbtx h2{font-size:26px!important}}
.hbn .cdpill{border-color:rgba(69,208,143,.5)!important;color:#7fe0b2}
.selbar{display:flex;flex-wrap:wrap;align-items:center;gap:6px 8px;margin:4px 0 6px;font-size:12px;color:var(--mut)}
.selbar.on{color:var(--fg)}
.selbar b{color:var(--acc)}
.selbar button{all:unset;cursor:pointer;padding:5px 11px;border-radius:999px;border:1px solid var(--line);font:600 12px Inter,sans-serif;color:var(--fg);background:rgba(255,255,255,.04)}
.selbar button.on,.selbar [data-selcmp]{background:rgba(69,208,143,.16);border-color:rgba(69,208,143,.5);color:#7fe0b2}
.selbar button[disabled]{opacity:.45;cursor:default}
.selbar button.ghost{background:none}
td.selc,th.selc{width:26px;padding:0 2px 0 6px!important;text-align:center}
.pck{all:unset;cursor:pointer;display:inline-block;width:16px;height:16px;border-radius:5px;border:1.5px solid rgba(255,255,255,.35);vertical-align:middle;position:relative}
.pck.on{background:#45d08f;border-color:#45d08f}
.pck.on::after{content:"";position:absolute;left:4.5px;top:1.5px;width:4px;height:8px;border:solid #06231a;border-width:0 2px 2px 0;transform:rotate(45deg)}
tr.sel td{background:rgba(69,208,143,.07)!important}
.nfq{margin:8px 0 2px}
.nfq input{width:100%;box-sizing:border-box;height:38px;border-radius:10px;border:1px solid var(--line);background:#121a2b;color:var(--fg);padding:0 12px;font:400 14px Inter,sans-serif}

/* ===== v3.44 readable text: larger base size, brighter secondary text ===== */
.root{font-size:15px}
.hc{font-size:14px!important;line-height:1.5!important}
.muted,small,.sub{color:var(--mut)}
@media (max-width:640px){.root{font-size:14.5px}.hc{font-size:14px!important}}
/* ===== Matchday theme (default): the FPL-tips poster look, in eye-friendly colours ===== */
.root.th-matchday{--bg:#17142e;--raised:#1f1b3d;--card:#211d40;--overlay:#2a2550;--fg:#efedf7;--mut:#bdb9d6;--t3:#9a96b8;--acc:#5fd69a;--acc2:#183a2c;--line:rgba(255,255,255,.09)}
.root.th-matchday .panel{background:radial-gradient(760px 420px at 96% -10%,rgba(139,108,246,.30),transparent 62%),radial-gradient(640px 380px at -6% 110%,rgba(95,214,154,.10),transparent 60%),#17142e!important}
.root.th-matchday .panel::before,.root.th-matchday .panel::after{content:"";position:absolute;z-index:0;pointer-events:none;width:240px;height:240px;background:repeating-linear-gradient(-55deg,transparent 0 16px,rgba(95,214,154,.35) 16px 21px,transparent 21px 46px);opacity:.35}
.root.th-matchday .panel::before{top:-120px;left:-120px;-webkit-mask-image:radial-gradient(circle at 70% 70%,#000,transparent 70%);mask-image:radial-gradient(circle at 70% 70%,#000,transparent 70%)}
.root.th-matchday .panel::after{bottom:-120px;right:-120px;-webkit-mask-image:radial-gradient(circle at 30% 30%,#000,transparent 70%);mask-image:radial-gradient(circle at 30% 30%,#000,transparent 70%)}
.root.th-matchday .panel>.top{background:rgba(23,20,46,.94)!important;border-bottom:2px solid rgba(95,214,154,.35)!important}
.root.th-matchday section.s,.root.th-matchday .card,.root.th-matchday #s-home .hero2{background:#211d40!important;border-color:rgba(255,255,255,.09)!important}
.root.th-matchday section.s>h2,.root.th-matchday .ptl h2,.root.th-matchday .cmptop h3{text-transform:uppercase;letter-spacing:.02em}
.root.th-matchday #s-home .card.hc.do{--hbar:linear-gradient(90deg,#2e9c64,#227650)}
.root.th-matchday #s-home .card.hc.lgc,.root.th-matchday #s-home .card.hc.seast{--hbar:linear-gradient(90deg,#6c48cf,#4b3194)}
.root.th-matchday #s-home .card.hc.gwc,.root.th-matchday #s-home .card.hc.newst{--hbar:linear-gradient(90deg,#3b76c8,#2b5794)}
.root.th-matchday #s-home .card.hc.alc .alerts .ah{background:linear-gradient(90deg,#c2414f,#90303d)}
.root.th-matchday #s-home .card.hc.alc .alerts.clear .ah{background:linear-gradient(90deg,#2e9c64,#227650)}
.root.th-matchday #f button[type=submit],.root.th-matchday .go{background:#5fd69a!important;color:#0b2a1c!important}
@media (min-width:980px){.root.th-matchday .panel>nav#nav{background:#1a1735!important;border-right:1px solid rgba(139,108,246,.25)!important}}
.root.th-matchday .hbn{border-color:rgba(139,108,246,.5)!important}
/* ===== Pitch theme: dark green-grey, gold highlights ===== */
.root.th-pitch{--bg:#0f1d19;--raised:#152821;--card:#172b24;--overlay:#1e3830;--fg:#ecf3ef;--mut:#b2c4bb;--t3:#8fa69b;--acc:#7fd99f;--acc2:#1a3a2a;--line:rgba(255,255,255,.08)}
.root.th-pitch .panel{background:radial-gradient(760px 420px at 96% -10%,rgba(232,196,90,.12),transparent 62%),#0f1d19!important}
.root.th-pitch section.s,.root.th-pitch .card,.root.th-pitch #s-home .hero2{background:#172b24!important}
.root.th-pitch .panel>.top{background:rgba(15,29,25,.94)!important}
@media (min-width:980px){.root.th-pitch .panel>nav#nav{background:#132620!important}}
.root.th-pitch #s-home .card.hc.lgc,.root.th-pitch #s-home .card.hc.seast{--hbar:linear-gradient(90deg,#8a7a2e,#6b5e22)}
.root.th-pitch #f button[type=submit],.root.th-pitch .go{background:#7fd99f!important;color:#0b2a1c!important}
.psl{display:grid;grid-template-columns:auto minmax(0,1fr) auto;grid-template-areas:'h h h' 'row row out';align-items:center;gap:2px 14px;margin:0 0 8px;padding:8px 14px;border-radius:12px;border:1px solid var(--line);background:linear-gradient(90deg,rgba(95,214,154,.10),rgba(139,108,246,.10))}
.psl-h{grid-area:h;display:flex;flex-wrap:wrap;gap:2px 10px;align-items:baseline}
.psl-h b{font-family:var(--fd);font-weight:700;font-size:16px;text-transform:uppercase;letter-spacing:.03em}
.psl-h small{font-size:13px}
.psl-row{grid-area:row;display:flex;align-items:center;gap:10px}
.psl-end{display:flex;flex-direction:column;align-items:center;min-width:52px}
.psl-end small{font-size:11px;text-transform:uppercase;letter-spacing:.06em}
.psl-end b{font-family:var(--fd);font-weight:700;font-size:16px}
.psl-end{flex-direction:row!important;gap:5px;align-items:baseline!important;min-width:0!important}
@media (max-width:640px){.psl{grid-template-areas:'h h h' 'row row row' 'out out out'}.psl-out{justify-content:flex-start}}
#pl-sl{flex:1;min-width:0;accent-color:var(--acc);height:28px;cursor:pointer}
.psl-hz{display:inline-flex;gap:3px;margin-left:auto;padding:2px;border-radius:999px;border:1px solid var(--line)}
.psl-hz button{all:unset;cursor:pointer;padding:3px 10px;border-radius:999px;font:600 12px Inter,sans-serif;color:var(--mut)}
.psl-hz button.on{background:var(--acc);color:#0b2a1c}
.psl-mc{font-size:12px;color:var(--mut);border-left:1px solid var(--line);padding-left:8px}
.psl-note{grid-column:1 / -1;font-size:12px;color:#efcf7d}
.psl-alt{grid-column:1 / -1;display:flex;flex-wrap:wrap;align-items:center;gap:4px 10px;margin-top:4px;padding:7px 10px;border-radius:10px;background:rgba(124,108,240,.14);border:1px solid rgba(124,108,240,.35);font-size:13px}
.psl-alt b{color:var(--fg)}
.psl-wc{all:unset;cursor:pointer;margin-left:auto;padding:5px 12px;border-radius:999px;background:var(--acc);color:#0b2a1c;font:600 12.5px Inter,sans-serif}
.psl-best{all:unset;cursor:pointer;color:var(--acc);font-weight:600;text-decoration:underline;text-underline-offset:2px}
.psl-out{grid-area:out;min-width:150px;justify-content:flex-end;display:flex;gap:8px;align-items:baseline;flex-wrap:wrap;font-size:13px;color:var(--mut)}
.psl-out b{font-family:var(--fd);font-weight:700;font-size:20px;color:var(--acc)}
.pgbar{display:flex;align-items:center;justify-content:center;gap:12px;margin:6px 0 0;font-size:12px;color:var(--mut);font-variant-numeric:tabular-nums}
.pgbar button{all:unset;cursor:pointer;padding:7px 14px;border-radius:999px;border:1px solid var(--line);color:var(--acc);font:600 13px Inter,sans-serif;min-height:20px}
.pgbar button[disabled]{opacity:.35;cursor:default}
.panel>.top.fl{isolation:isolate;flex-shrink:0}
.panel>.top{flex-shrink:0}
.panel>.top .tfl{position:absolute;inset:0;z-index:-3;pointer-events:none;opacity:.85;filter:saturate(1.2);
  -webkit-mask-image:linear-gradient(90deg,#000 0%,rgba(0,0,0,.85) 35%,rgba(0,0,0,.3) 68%,transparent 94%);mask-image:linear-gradient(90deg,#000 0%,rgba(0,0,0,.85) 35%,rgba(0,0,0,.3) 68%,transparent 94%)}
.panel>.top:not(.fl) .tfl{display:none}
.panel>.top .tfl i{position:absolute;top:0;bottom:0;background-image:var(--flagt);background-repeat:no-repeat}
.panel>.top .tfl .l{left:0;right:72%;background-size:6000% 100%;background-position:0 0}
.panel>.top .tfl .r{left:28%;right:0;background-size:6000% 100%;background-position:100% 0}
.panel>.top .tfl .c{left:28%;transform:translateX(-50%);aspect-ratio:3/2;background-size:contain;background-position:center}
.panel>.top.fl::before{content:none}
.panel>.top.fl::after{content:"";position:absolute;inset:0;z-index:-1;pointer-events:none;background:linear-gradient(180deg,rgba(255,255,255,.18) 0%,rgba(255,255,255,.04) 45%,rgba(0,0,0,.22) 100%),linear-gradient(90deg,rgba(11,18,32,.28) 0%,rgba(11,18,32,.42) 45%,rgba(11,18,32,.7) 100%);box-shadow:inset 0 1px 0 rgba(255,255,255,.22)}
.panel>.top.fl .brand,.panel>.top.fl .brand *{text-shadow:0 1px 3px rgba(0,0,0,.85)}
.chipbox{border:1px solid var(--line);border-radius:12px;padding:8px;background:rgba(11,18,32,.5)}
.chiphd{display:flex;flex-direction:column;margin:0 2px 6px}.chiphd b{font-size:13px}.chiphd small{font-size:11px;color:var(--mut)}
.chipgrid{display:grid;grid-template-columns:1fr 1fr;gap:6px}
.chipt{display:flex;flex-direction:column;align-items:flex-start;gap:2px;padding:7px 9px;border-radius:9px;border:1px solid rgba(69,208,143,.3);background:rgba(69,208,143,.07);color:var(--fg);text-align:left;cursor:pointer;font:inherit}
.chipt b{font-size:13px}.chipt em{font-style:normal;font-size:11px;font-weight:700;color:var(--acc)}.chipt span{font-size:11px;color:var(--mut)}.chipt span b{font-size:11px;color:var(--fg)}
.chipt.on{border-color:var(--gold);background:rgba(246,195,67,.14)}.chipt.on em{color:var(--gold)}
.chipt.na{border-color:rgba(255,107,107,.45);background:rgba(168,50,70,.28)}.chipt.na em{color:#ff9f9f}
.note.tn{margin:0 0 6px;font-size:11px}
#planner .stack{gap:6px}
#planner .plside .move{padding:8px 10px;gap:4px;border-radius:9px;font-size:12px}
#planner .plside .move .h{font-size:13px}
#planner .plside .move .alt{font-size:12px;line-height:1.35}
#planner .plside .move .fxc,#planner .plside .move .hb{font-size:11px;padding:2px 4px}
#planner .plside .move .try{padding:4px 10px;font-size:12px}
.move.mv2{gap:5px;padding:8px 10px}
.mvx2 .kitw{width:22px;height:26px}.mvx2 .kitw>svg,.mvx2 .kitw img{width:22px;height:24px;object-fit:contain}
.mvx2{display:flex;align-items:center;gap:5px;flex-wrap:wrap;min-width:0}.mvx2 i{font-style:normal;color:var(--acc);font-weight:700}
.mv2 .h .gain{font:700 16px var(--fd);color:var(--acc);white-space:nowrap}
.mv2 .mvm{font-size:11px;line-height:1.3}
.mvf{display:flex;align-items:center;justify-content:space-between;gap:8px;flex-wrap:wrap}.mvf .fx{flex-wrap:nowrap}
.mv2 .alt{font-size:11px;line-height:1.35;display:-webkit-box;-webkit-line-clamp:1;-webkit-box-orient:vertical;overflow:hidden}
#planner .plside .ptabs{margin-bottom:6px}
#planner .plside .ptab{padding:7px 4px;font-size:12px}
.picon.face{width:26px;height:32px;min-width:26px;max-width:26px;max-height:32px;border-radius:6px;box-shadow:0 0 0 1px rgba(255,255,255,.15)}
.picon.face.fbig{width:44px;height:54px;min-width:44px;max-width:44px;max-height:54px;border-radius:9px;margin:0 auto 4px;display:grid}
.picon.face.fsm{width:22px;height:27px;min-width:22px;max-width:22px;max-height:27px;border-radius:5px}
.picon.face b{font-size:12px;color:#fff}
.picon.face .pfimg{position:absolute;inset:0;width:100%;height:100%;object-fit:cover;object-position:50% 8%}
.picon.face .pfimg.gone{display:none}
.vleg{display:flex;flex-wrap:wrap;gap:6px 14px;margin-top:10px;font-size:12px;color:var(--mut)}
.vleg>b{flex-basis:100%;font-size:12px;color:var(--fg)}
.vleg>span{display:flex;align-items:center;gap:6px}
.pill.p-out{background:var(--badbg);color:var(--bad)}
/* ===== v3.19 polish ===== */
/* 1, 8, 15: one tab style: sub-tabs are a single scrolling row, tinted like the other tabs; on phones they stick to the top */
.subnav .seg{display:flex;flex-wrap:nowrap;overflow-x:auto;gap:2px;scrollbar-width:none}
.subnav .seg::-webkit-scrollbar{display:none}
.subnav .seg button{flex:none;white-space:nowrap;padding:8px 14px;min-height:36px;font-size:13px}
.subnav .seg button.on{background:var(--acc2)!important;color:var(--acc)!important;box-shadow:0 0 0 1px var(--acc) inset!important}
@media (max-width:640px){
  .subnav{position:sticky;top:0;z-index:6;padding:6px 8px;background:rgba(11,18,32,.96);border-bottom:1px solid var(--line);backdrop-filter:blur(6px)}
  .subnav .seg{width:100%;border-radius:10px}
  .subnav .seg button{flex:1 0 auto}
  .subnav .seg button:last-child{margin-right:0}
}
@media (max-width:640px){#s-fix .rotctl .seg button,#s-live .seg.tabs button{min-height:36px}}
/* 2: nothing under 10 px; small labels 11 px */
.herok small,#s-home .herok small,.hc .kpi small,.eyebrow{font-size:11px!important}
.mwn,.mwp,.hnt small,.chipt span,.chipt em,.chipt span b,.ppk4 small,.ppk4 span,.ppsg small,.capc .cs small,.rvs small,.chiphd small{font-size:11px!important}
/* v3.69 */
.bpb{font-style:normal;display:inline-block;margin-left:3px;padding:0 4px;border-radius:5px;background:#f6c343;color:#2a1a00;font:800 10px/1.45 var(--fd);vertical-align:2px;box-shadow:0 0 0 1px rgba(0,0,0,.25)}.hpitch .chip.pc.ro .jval .bpb{font-size:10px;vertical-align:3px;animation:bpbp 2s ease-in-out infinite}@keyframes bpbp{50%{box-shadow:0 0 0 3px rgba(246,195,67,.35)}}.mwmy2 .mwp > b .bpb{font-size:9.5px}
.capbox{margin-bottom:14px}.capl{display:flex;flex-direction:column;gap:6px;margin-top:8px}
.capr{display:grid;grid-template-columns:auto minmax(0,1.4fr) minmax(60px,1fr) auto auto;align-items:center;column-gap:10px;padding:7px 10px;border-radius:10px;border:1px solid var(--line);background:rgba(255,255,255,.03)}
.capr.mine{border-color:rgba(69,208,143,.55);background:rgba(69,208,143,.07)}.capr .picon.face{margin:0}
.capn{min-width:0;display:flex;flex-direction:column}.capn a{font-weight:700;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}.capn small{font-size:11px;color:var(--mut);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.capbar{height:8px;border-radius:5px;background:rgba(255,255,255,.07);overflow:hidden}.capbar i{display:block;height:100%;border-radius:5px;background:linear-gradient(90deg,#f6c343,#f0a51f)}
.capv{display:flex;flex-direction:column;align-items:flex-end;min-width:64px}.capv b{font:800 16px/1.1 var(--fd);font-variant-numeric:tabular-nums}.capv small{font-size:10.5px;color:var(--mut);white-space:nowrap}
@media (max-width:560px){.capr{grid-template-columns:auto minmax(0,1fr) auto auto;row-gap:4px}.capbar{grid-column:2/-1;grid-row:2}}
.tvar{font-family:'Noto Kufi Arabic','Segoe UI',Tahoma,sans-serif;font-weight:700;font-size:.95em;color:var(--txt);display:inline-block;padding:0 7px;margin-inline-start:6px;border-radius:6px;background:rgba(255,255,255,.07);border:1px solid var(--line);line-height:1.5}
.mwtv{text-align:center;font-size:12px;color:var(--mut);margin-top:3px}.mwtv .tvch{white-space:normal}
@media (min-width:861px){#planner .plgrid.hist{grid-template-columns:minmax(0,1.3fr) minmax(300px,1fr)!important;gap:14px!important}}
.hst{display:grid;grid-template-columns:168px minmax(0,1fr);gap:10px;margin-bottom:12px}
.hhero{position:relative;overflow:hidden;border-radius:14px;padding:14px 12px;display:flex;flex-direction:column;align-items:center;justify-content:center;text-align:center;gap:2px;color:#062a1b;background:radial-gradient(120% 90% at 100% 0%,rgba(255,255,255,.35),transparent 55%),linear-gradient(145deg,#1d9a70 0%,#2fd08a 55%,#8af3c4 100%);box-shadow:0 8px 24px -10px rgba(47,208,138,.6)}
.hhero small{font:800 11px/1.2 var(--fd);letter-spacing:.08em;text-transform:uppercase;opacity:.85;display:inline-flex;align-items:center;gap:6px}
.hhero.live small::before{content:"";width:8px;height:8px;border-radius:50%;background:#e0162b;box-shadow:0 0 0 0 rgba(224,22,43,.6);animation:hlive 1.6s infinite}
@keyframes hlive{70%{box-shadow:0 0 0 7px rgba(224,22,43,0)}100%{box-shadow:0 0 0 0 rgba(224,22,43,0)}}
.hhero b{font:800 48px/1 var(--fd);font-variant-numeric:tabular-nums;letter-spacing:-.01em;margin:4px 0 2px}
.hhero span{font-size:12px;font-weight:700;line-height:1.3}.hhero .hhit{font-size:11px;opacity:.8}
.hcells{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:8px}.hcell .hsep{font-style:normal;color:var(--mut);font-weight:500}.gwlive{display:inline-block;width:7px;height:7px;border-radius:50%;background:#e0162b;margin-right:6px;animation:hlive 1.6s infinite;vertical-align:1px}
.hcell{border-radius:11px;padding:9px 10px;background:linear-gradient(180deg,rgba(255,255,255,.055),rgba(255,255,255,.02));border:1px solid var(--line);display:flex;flex-direction:column;justify-content:center;gap:3px;min-width:0;text-align:left}
.hcell small{font:700 10.5px/1.2 var(--fd);color:var(--mut);text-transform:uppercase;letter-spacing:.06em}
.hcell b{font:700 17px/1.15 var(--fd);color:var(--txt);font-variant-numeric:tabular-nums;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.hcell em{font-style:normal;font-size:11px;color:var(--mut);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
@media (max-width:640px){.hst{grid-template-columns:1fr}.hhero{padding:10px}.hhero b{font-size:40px}.hcell{padding:7px 9px;gap:2px}.hcell b{font-size:16px}.hcell small{font-size:10px}}
.hpitch .chip.pc .jname{background:#f4f7fb;color:#0f1726;font-weight:700;border-radius:6px 6px 0 0}
.hpitch .chip.pc.ro .jval{background:linear-gradient(135deg,#34405c,#252f45);color:#fff;display:flex;align-items:baseline;justify-content:center;gap:2px}
.hpitch .chip.pc.ro .jval b{color:inherit!important;font:800 17px/1.15 var(--fd)}.hpitch .chip.pc.ro .jval small{font-size:10px;opacity:.85;font-weight:700}
.hpitch .chip.pc.pt-hi .jval{background:linear-gradient(135deg,#ffd45c,#f0a51f);color:#2a1a00}
.hpitch .chip.pc.pt-ok .jval{background:linear-gradient(135deg,#3be29a,#1fa673);color:#04261a}
.hpitch .chip.pc.pt-mid .jval{background:linear-gradient(135deg,#4a5a7e,#35425f);color:#fff}
.hpitch .chip.pc.pt-lo .jval{background:linear-gradient(135deg,#5a3a4a,#43293a);color:#ffd5dc}
.hpitch .chip.pc.pt-ns .jval{background:#2a3347;color:#9fb0c8}
.hpitch .chip.pc .jsub{background:rgba(10,16,28,.88);color:#d7e0ee;border-radius:0 0 6px 6px;padding:2px 4px 3px;font-size:10.5px;font-weight:600;align-items:center;gap:4px;white-space:nowrap}
.hpitch .chip.pc.pt-ns .jsub{color:#b9c6da}.hpitch .chip.pc.ro .jval b.nsfx{font:700 12px/1.6 var(--fd);letter-spacing:.02em}
.hpitch .ldot{width:6px;height:6px;border-radius:50%;background:#e0162b;display:inline-block;animation:hlive 1.6s infinite}
.hpitch .chip.pc.plive .jname{box-shadow:inset 0 -2px 0 #e0162b}
.pph .pflag.c.wv{display:flex;background:none!important;overflow:visible}
.pph .pflag.c.wv b{flex:1 0 0;height:100%;margin-right:-.6px;background-image:var(--flagb,var(--flag));background-repeat:no-repeat;background-size:2400% 100%;background-position:calc(var(--i) * 100% / 23) 0;transform-origin:50% 50%;animation:fwave 2.6s ease-in-out infinite;animation-delay:calc(var(--i) * -.11s);will-change:transform}
@keyframes fwave{0%,100%{transform:translateY(-5%) scaleY(1.12);filter:brightness(1.16)}50%{transform:translateY(5%) scaleY(1.12);filter:brightness(.72)}}
.pph.egy .pflag.c.wv{display:none!important}.pph.egy .pflag.c.wv.ok{display:flex!important;left:0;right:0;transform:none;aspect-ratio:auto}
.pph.egy .pflag.c.wv b{margin-right:-1px;background-image:var(--egyimg);background-size:var(--bw) var(--bh);background-position:calc(var(--i) * var(--sw) * -1 - var(--bx0)) calc(var(--by0) * -1);animation-name:fwaveE}
@keyframes fwaveE{0%,100%{transform:translateY(-2.2%) scaleY(1.06);filter:brightness(1.03)}50%{transform:translateY(2.2%) scaleY(1.06);filter:brightness(.96)}}
.m-calm .pph .pflag.c.wv b,.paused .pph .pflag.c.wv b{animation-play-state:paused}
/* v3.69: your players under each club: equal-size chips in a tidy column, no overlap */
.mwmy2 .mws2{display:flex;flex-direction:column;flex-wrap:nowrap;align-items:flex-start;gap:6px}.mwmy2 .mws2.r{align-items:flex-end}
.mwmy2 a.mwp,.mwmy2 .mwp{box-sizing:border-box;display:grid!important;grid-template-columns:28px minmax(0,1fr) auto;align-items:center;column-gap:7px;width:min(176px,100%);height:34px;padding:0 10px 0 3px!important;margin:0!important;border-radius:10px;border:1px solid rgba(69,208,143,.35);background:rgba(69,208,143,.08);line-height:1;overflow:hidden;white-space:nowrap;font-size:12px!important}
.mwmy2 .mwp .picon.face,.mwmy2 .mwp .picon.mwf{width:28px!important;height:28px!important;min-width:28px!important;max-width:28px!important;max-height:28px!important;border-radius:7px!important;margin:0!important;vertical-align:0}
.mwmy2 .mwp .mwnm{overflow:hidden;text-overflow:ellipsis;min-width:0;display:flex;align-items:center;gap:4px}.mwmy2 .mwp > b{justify-self:end;font-variant-numeric:tabular-nums;font-size:13px}
.mwmy2 .mwp.bn{border-style:dashed}
#planner .ppill small{font-size:11px!important;letter-spacing:.04em}
#planner .ppill b{font-size:13px!important}
#planner .ppill .pd{font-size:11px!important}
.al small,.alc small,.hni small{font-size:11px}
.fxc,.tk{font-size:11px}
/* 3: action rows wrap to two lines rather than cutting off */
.arow .atx{white-space:normal!important;overflow:hidden;display:-webkit-box;-webkit-line-clamp:3;-webkit-box-orient:vertical;line-height:1.35}
.mvx{display:inline;font-weight:700}.mvx i{font-style:normal;color:var(--acc);margin:0 5px}.mvx a.pn{display:inline-flex}
/* 4: touch targets: 36 px controls with a 44 px tap area, wider arrows, taller pickers and name links */
.tbtn{height:36px;position:relative}.tbtn.ico{width:36px}
.tbtn::after,.gwb::after,.mwa::after{content:"";position:absolute;inset:-4px}
.gwb,.mwa{position:relative}
#s-live .mwh .mwa{flex:none;width:40px!important;height:40px!important;min-width:40px}
.alt small,.move small.muted{font-size:11px}
#nf-src,.wcl select{min-height:36px}
a.pn[data-pi]{padding:5px 0;margin:-5px 0}
.cta,.try{min-height:32px}
/* 7: page titles without the banner; search on its own row */
.ptl{margin:0 0 10px}.ptl h2{font:700 26px var(--fd);margin:0 0 2px}.ptl .sub{margin:0}
.mkctl{flex-wrap:wrap}#mk-q{flex:1 1 100%!important;width:100%;min-width:0}
.mkviews{flex-wrap:nowrap;overflow-x:auto;scrollbar-width:none}.mkviews button{flex:none;white-space:nowrap}
/* 9: first column stays put; a fade shows there is more to the right */
.tw table th:first-child,.tw table td:first-child{position:sticky;left:0;z-index:1;background:#101a2c}
.tw table thead th:first-child{z-index:2}
.tw.more{-webkit-mask-image:linear-gradient(to right,#000 88%,rgba(0,0,0,.25));mask-image:linear-gradient(to right,#000 88%,rgba(0,0,0,.25))}
.tick td.pl,.tick th:first-child{background:#101a2c}
/* 10: error state */
.errbox{border:1px solid rgba(255,107,107,.45);background:var(--badbg);border-radius:12px;padding:12px 14px}.errbox b{display:block;font-size:16px;margin-bottom:4px}.errbox p{margin:0;font-size:13px;color:#e8c8c8}
/* 11: headlines in alert cards: no underline, title in white */
.alc a:not(.pn),.al a:not(.pn){text-decoration:none!important;color:var(--fg);font-weight:600}
.alc a:not(.pn):hover,.al a:not(.pn):hover{color:var(--acc)}
/* 12: bench label above the kits */
#planner .benchbox .ptitle{position:static!important;text-align:left;margin:0 0 2px 8px;font-size:11px}
/* 5: "Show all" leagues */
.hlmore summary{cursor:pointer;font-size:12px;font-weight:700;color:var(--acc);padding:6px 4px;list-style:none}
.hlmore summary::-webkit-details-marker{display:none}
.hlmore[open] summary{display:none}
/* 14: tablet header: countdown sits on the Team ID row */
@media (min-width:641px) and (max-width:980px){.top>.brand{flex:1 1 100%}.top>#gwpill{order:3}.top>form{order:2}.top>#setb{order:4}.top>#x{order:5}}
/* 16: next gameweek strip */
.nextgw{display:flex;align-items:center;gap:8px;flex-wrap:wrap;margin:8px 0 0;padding:8px 12px;border-radius:12px;border:1px solid var(--line);background:rgba(255,255,255,.03);font-size:13px}
.nextgw span{font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:.06em;color:var(--acc)}
.updpill{position:absolute;left:50%;transform:translateX(-50%);bottom:84px;z-index:40;font-size:12px;font-weight:700;padding:5px 12px;border-radius:999px;background:#0d1626;border:1px solid var(--acc);color:var(--acc);box-shadow:0 6px 20px rgba(0,0,0,.4)}
.setrow.col{flex-direction:column;align-items:stretch;gap:8px}
.xrow{display:flex;gap:8px}
#xcode{width:100%;box-sizing:border-box;border-radius:10px;border:1px solid var(--line);background:rgba(11,18,32,.7);color:var(--fg);font:12px ui-monospace,Menlo,monospace;padding:8px;resize:vertical}
.pbar2{position:relative;display:inline-block;width:62px;height:16px;border-radius:5px;background:rgba(255,255,255,.06);overflow:hidden;vertical-align:middle}
.pbar2 i{position:absolute;left:0;top:0;bottom:0;background:rgba(69,208,143,.35)}.pbar2.down i{background:rgba(255,107,107,.35)}
.pbar2 b{position:relative;font-size:11px;padding:0 4px;line-height:16px}
.pbar2+small{display:block;font-size:11px}
.calrow{display:flex;flex-wrap:wrap;gap:8px;align-items:center}
.acch{font:700 14px Inter,system-ui,sans-serif;margin:16px 0 4px;text-transform:none;letter-spacing:0}
.shh>div:first-child:not(.shk){display:flex;flex-direction:column;flex:1}
.calrow>span{display:flex;flex-direction:column;align-items:center;padding:5px 10px;border-radius:9px;background:rgba(255,255,255,.04);border:1px solid var(--line)}
.calrow small{font-size:11px;color:var(--mut)}
.caprec{display:flex;flex-direction:column;gap:2px;padding:10px 12px;border-radius:12px;border:1px solid rgba(69,208,143,.45);background:linear-gradient(120deg,rgba(14,58,52,.8),rgba(11,18,32,.6))}
.caprec .eyebrow{color:var(--acc);font-size:11px;letter-spacing:.12em;text-transform:uppercase}
.caprec b{font:700 26px var(--fd)}.caprec span{font-size:13px;color:#cfd8e6}
.capc{display:grid;grid-template-columns:40px minmax(0,1fr) auto;grid-template-areas:"k m b" "k s s";gap:4px 10px;align-items:center;padding:8px 10px;border-radius:12px;border:1px solid var(--line);background:rgba(11,18,32,.55)}
.capc.rec{border-color:var(--acc)}
.capc .ck{grid-area:k;position:relative;width:40px;height:40px}.capc .ck .kitw{position:absolute;inset:0}.capc .ck svg,.capc .ck img{position:absolute;inset:0;width:100%;height:100%;object-fit:contain}
.capc .cm{grid-area:m;display:flex;flex-direction:column;min-width:0}.capc .cm b{font-size:14px}.capc .cm small{font-size:11px;color:var(--mut)}
.capc>button,.capc>.pill{grid-area:b}
.capc .cs{grid-area:s;display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:4px}
.capc .cs span{display:flex;flex-direction:column;align-items:center;padding:3px;border-radius:7px;background:rgba(255,255,255,.035)}
.capc .cs b{font:700 14px var(--fd)}.capc .cs small{font-size:11px;color:var(--mut);text-transform:uppercase}
.ctag{font-size:11px;font-weight:700;padding:1px 6px;border-radius:999px;background:var(--acc2);color:var(--acc);vertical-align:2px}
.rvgrid{display:grid;grid-template-columns:repeat(auto-fill,minmax(300px,1fr));gap:8px}
.rvc{display:flex;flex-direction:column;gap:6px;padding:10px 12px;border-radius:12px;border:1px solid var(--line);background:rgba(11,18,32,.55)}
.rvh{display:flex;align-items:center;gap:8px}.rvh>div{flex:1;min-width:0;display:flex;flex-direction:column}.rvh b{font-size:14px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}.rvh small{font-size:11px;color:var(--mut)}
.rvr{font:700 16px var(--fd);color:var(--mut)}
.rvg{font-size:12px;font-weight:700;white-space:nowrap}
.rvs{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:5px}
.rvs span{display:flex;flex-direction:column;padding:4px 6px;border-radius:8px;background:rgba(255,255,255,.035);min-width:0}
.rvs small{font-size:11px;color:var(--mut);text-transform:uppercase}.rvs b{font-size:13px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.rvt{display:flex;flex-wrap:wrap;gap:4px 10px;font-size:12px}
.rvd{display:flex;flex-wrap:wrap;gap:4px;align-items:center;font-size:12px}.rvd>small{font-size:11px;color:var(--mut);text-transform:uppercase;margin-right:2px}
.rvd span{padding:2px 8px;border-radius:999px;background:var(--badbg);border:1px solid rgba(255,107,107,.3)}.rvd span.done{opacity:.55}.rvd span b{color:var(--bad)}
.rvl{margin:0;font-size:12px;color:#cfd8e6}
#s-live .seg.tabs{overflow-x:auto;flex-wrap:nowrap;max-width:100%;scrollbar-width:none}.seg{max-width:100%}#s-live .seg.tabs button{white-space:nowrap;flex:none}
.pinl{margin-top:3px}.pinl small{display:inline!important;margin-left:6px}
table.lgt tr.lgtop td{background:var(--tbg)}
table.lgt tr.lgtop td:first-child{box-shadow:inset 3px 0 0 var(--tbc,transparent)}
table.lgt tr.lgtop1{--tbc:#f6c343}table.lgt tr.lgtop2{--tbc:#c8d2e1}table.lgt tr.lgtop3{--tbc:#cd7f32}
table.lgt tr.lgtop1 td{--tbg:rgba(246,195,67,.13)}table.lgt tr.lgtop2 td{--tbg:rgba(200,210,225,.08)}table.lgt tr.lgtop3 td{--tbg:rgba(205,127,50,.1)}table.lgt tr.lgtop4 td,table.lgt tr.lgtop5 td{--tbg:rgba(69,208,143,.05)}
table.lgt tr.lgtop1 td:first-child b{color:var(--gold)}
.tico{display:inline-block;margin-right:6px;font-size:16px;line-height:1;vertical-align:-1px}
.tico.t1{font-size:20px;animation:crown 2.4s ease-in-out infinite;transform-origin:50% 90%}
@keyframes crown{0%,100%{transform:rotate(-8deg)}50%{transform:rotate(8deg) translateY(-1px)}}
@media (prefers-reduced-motion:reduce){.tico.t1{animation:none}}
tr.lggap td{text-align:left;padding-left:48px!important;color:var(--mut);font-size:12px;letter-spacing:.06em;padding:6px;background:rgba(255,255,255,.02)}
.nfbar{display:flex;flex-wrap:wrap;align-items:center;justify-content:space-between;gap:8px 12px;margin:4px 0 8px}
.nfbar .seg.nfilt{margin-top:0}
.nfbar select{max-width:220px}
.srcd.top{margin:0 0 12px}
.kind.k-excl{background:#5a1630;color:#ff9fbf}
.hnt small i.ex{color:#ff9fbf}
.kitw.ckit-s{position:relative;display:inline-block;width:22px;height:22px;flex:none;vertical-align:middle}
.kitw.ckit-s svg,.kitw.ckit-s img{position:absolute;inset:0;width:100%;height:100%;object-fit:contain}
.crow .cn{display:grid;grid-template-columns:24px minmax(0,1fr);column-gap:6px;align-items:center;min-width:0;overflow:hidden}
.crow .cn small{display:block;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;min-width:0}
.crow,.clh{grid-template-columns:minmax(0,1fr) 48px 26px 74px!important}
@media (max-width:640px){.cmpempty{padding:18px 12px}}
.crow .cp{text-align:right;white-space:nowrap}
.crow .cn .kitw,.crow .cn .picon{grid-row:span 2;align-self:center}
.crow .cn .picon.face{width:24px;height:30px;min-width:24px;max-width:24px;max-height:30px;margin:0}
.crow .cn b{grid-column:2;align-self:end;line-height:1.2}.crow .cn small{grid-column:2;align-self:start;display:flex!important;align-items:center;gap:4px;color:var(--mut);font-size:11px;line-height:1.3}
.crow .cn small .pb{font-size:10px;padding:0 4px;line-height:15px;position:static}
.lgpk{position:relative;flex:1 1 100%;min-width:0;order:-1}
.wch:has(.lgpk)>b{font-size:12px;color:var(--mut);font-weight:600}
.lgbtn{display:grid;grid-template-columns:auto minmax(0,1fr) auto auto;align-items:center;gap:10px;width:100%;padding:10px 12px;border-radius:12px;border:1px solid rgba(69,208,143,.4);background:linear-gradient(135deg,rgba(14,58,52,.65),rgba(11,18,32,.85));color:var(--fg);font:600 14px Inter,system-ui,sans-serif;cursor:pointer;text-align:left}
.lgbtn:hover,.lgbtn[aria-expanded=true]{border-color:var(--acc)}
.lgbtn .ln{overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font:700 16px var(--fd);letter-spacing:.01em}
.lgbtn .lr{font-size:12px;white-space:nowrap}
.lgbtn .lt,.lgmenu .lt{font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:.05em;padding:3px 7px;border-radius:6px;background:var(--acc2);color:var(--acc)}
.lgbtn .lt.t-h2h{background:#2a2350;color:#b9a8ff}.lgbtn .lt.t-cup{background:var(--warnbg);color:var(--gold)}
.lgbtn svg{color:var(--acc);transition:transform .2s}
.lgbtn[aria-expanded=true] svg{transform:rotate(180deg)}
.lgmenu{position:absolute;left:0;right:0;top:calc(100% + 6px);z-index:20;max-height:340px;overflow:auto;display:flex;flex-direction:column;gap:4px;padding:8px;border-radius:12px;border:1px solid var(--line);background:#0d1626;box-shadow:0 14px 40px rgba(0,0,0,.55)}
.lgmenu[hidden]{display:none}
.lgg{font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:.08em;color:var(--mut);padding:6px 4px 2px}
.lgmenu .hlr{padding:8px 10px;font-size:13px}
@media (min-width:980px) and (min-height:600px){
  #s-home .hgrid{align-items:start}
}
@media (max-width:979px){.hgrid{grid-template-columns:repeat(2,minmax(0,1fr))}}
@media (max-width:640px){.hgrid{grid-template-columns:1fr}}
/* Fixtures v3.11 pages: Market, Head to head, Accuracy */
section.s.fx2{padding:16px}
.mhero{position:relative;padding:18px 22px;border-radius:14px;background:linear-gradient(120deg,rgba(14,58,52,.9),rgba(3,10,20,.9) 60%);border:1px solid var(--line);margin-bottom:14px}
.mhero .eyebrow{color:var(--acc);font-size:11px;letter-spacing:.14em}
.mhero h2{font:700 30px/1.1 var(--fd);margin:4px 0 6px}
.mhero h2 em{font-style:normal;color:var(--acc)}
.mhero p{margin:0 0 10px;color:var(--mut);font-size:13px}
.mbtn{display:inline-flex;align-items:center;gap:6px;padding:6px 14px;border-radius:999px;border:1px solid rgba(69,208,143,.45);background:rgba(69,208,143,.1);color:var(--acc);font:600 13px Inter,system-ui,sans-serif;cursor:pointer}
.mbtn:hover{background:var(--acc);color:#04221a}
.mbtn.big{padding:10px 16px;border-radius:12px;font-size:13px;width:100%;justify-content:center}
.mbtn.ghost{border-color:var(--line);background:rgba(255,255,255,.03);color:var(--fg)}
.mkctl{display:flex;gap:8px;align-items:center;margin-bottom:8px}
.mkctl input,.cmpq input{flex:1;min-width:0;padding:9px 12px;border-radius:9px;border:1px solid var(--line);background:rgba(11,18,32,.7);color:var(--fg);font:13px Inter,system-ui,sans-serif}
.mkctl input:focus,.cmpq input:focus{outline:2px solid rgba(69,208,143,.5);outline-offset:0}
.pseg{display:flex;gap:4px}
.pseg button,.mkviews button,.cseg button{padding:6px 11px;border-radius:7px;border:1px solid var(--line);background:rgba(11,18,32,.6);color:var(--mut);font:600 12px Inter,system-ui,sans-serif;cursor:pointer}
.pseg button.on,.mkviews button.on{border-color:var(--acc);background:rgba(69,208,143,.14);color:var(--acc)}
.pseg.full{display:grid;grid-template-columns:repeat(5,1fr);padding:3px;border-radius:999px;background:rgba(11,18,32,.6);border:1px solid var(--line);margin:8px 0}
.pseg.full button{border:0;border-radius:999px;background:none}
.pseg.full button.on{background:rgba(255,255,255,.1);color:var(--fg)}
.mkviews{display:flex;gap:6px;flex-wrap:wrap;margin-bottom:10px}
.mkmeta{display:flex;justify-content:space-between;font-size:12px;margin:0 0 6px}
.acc{color:var(--acc)}
b.acc{color:var(--acc)}
table.mkt{font-size:13px}
table.mkt th{font-size:11px;text-transform:uppercase;letter-spacing:.05em;color:var(--mut);white-space:nowrap}
table.mkt th.sortable{cursor:pointer;user-select:none}
table.mkt th.sortable:hover,table.mkt th.on{color:var(--acc)}
table.mkt td{font-variant-numeric:tabular-nums}
table.mkt td.pl a.pn,table.cmpt a.pn{color:var(--fg);font-weight:700;text-decoration:none}
table.mkt td.pl a.pn:hover,table.cmpt a.pn:hover{color:var(--acc)}
.pb{display:inline-block;font:700 11px/1 Inter,system-ui,sans-serif;font-style:normal;padding:2px 4px;border-radius:4px;vertical-align:middle;letter-spacing:.03em}
.pb.p1{background:#f6c343;color:#2a1f00}.pb.p2{background:#e9b23a;color:#2a1f00}.pb.p3{background:#45d08f;color:#03261b}.pb.p4{background:#3a86ff;color:#fff}
.cmpgrid{display:grid;grid-template-columns:280px minmax(0,1fr);gap:16px;align-items:start}
@media (max-width:860px){.cmpgrid{grid-template-columns:1fr}}
.ps-meta{display:flex;gap:10px;justify-content:space-between;align-items:center;flex-wrap:wrap;margin:8px 0;color:var(--mut);font-size:12px}
.ps-modes{display:inline-flex;gap:4px;padding:4px;margin:4px 0 8px;border:1px solid var(--line);border-radius:10px;background:rgba(11,18,32,.65)}
.ps-modes button{border:0;border-radius:7px;padding:8px 13px;background:transparent;color:var(--mut);font:700 12px Inter,system-ui,sans-serif;cursor:pointer}
.ps-modes button.on{background:rgba(69,208,143,.16);color:var(--acc)}
.ps-modes button:disabled{opacity:.55;cursor:wait}
.ps-scroll{overflow-x:auto;overflow-y:visible;border:1px solid var(--line);border-radius:10px}
.vscroll{overflow-y:auto!important;overscroll-behavior:contain;-webkit-overflow-scrolling:touch}.vscroll thead{position:sticky;top:0;z-index:3}.vscroll thead th{background:var(--card,#1b1433)}
@media (max-width:860px){.cmpgrid.pick .cmpl{display:flex!important;order:-1;max-height:none;min-height:0}.cmpgrid.pick .cmpl .clist{min-height:0}.cmpgrid.pick .cmpempty{display:none}}
table.pstats{width:max-content;min-width:100%;font-size:12px}
table.pstats th{position:sticky;top:0;z-index:2;background:#101a2c;text-align:center;padding:8px 9px}
table.pstats thead tr:first-child th{top:0}
table.pstats thead tr:nth-child(2) th{top:33px;z-index:2}
table.pstats th.ps-base{vertical-align:middle}
table.pstats th.ps-group{color:var(--acc);font-size:11px;letter-spacing:.08em}
table.pstats th.ps-sort{cursor:pointer;user-select:none}
table.pstats th.ps-sort:hover,table.pstats th.ps-sort.on{color:var(--acc)}
table.pstats td{text-align:right;padding:7px 9px;font-variant-numeric:tabular-nums}
table.pstats td.ps-name,table.pstats td.ps-team{text-align:left}
table.pstats td.ps-name{position:sticky;left:0;z-index:1;background:#101a2c;min-width:132px}
table.pstats th.ps-name{position:sticky;left:0;z-index:4;min-width:132px}
table.pstats thead tr:nth-child(2) th:first-child{position:static;left:auto}
table.pstats .ps-team{color:var(--mut);font-weight:700}
.ps-sortmark{color:var(--acc);margin-left:3px}
.ps-info{border:1px solid var(--line);border-radius:10px;padding:9px 12px;margin:8px 0;color:var(--mut);font-size:12px}
.ps-status{display:flex;align-items:center;gap:8px;flex-wrap:wrap}
.ps-status .mbtn{margin-left:auto}
.ps-partial{color:var(--warn)}
@media(max-width:600px){table.pstats{font-size:11px}table.pstats th,table.pstats td{padding:6px 7px}}
.cmpl{position:sticky;top:0;background:rgba(11,18,32,.7);border:1px solid var(--line);border-radius:12px;padding:10px;display:flex;flex-direction:column;max-height:calc(var(--oh,80vh) - 60px)}
.cmpl h3{font:700 14px Inter,system-ui,sans-serif;margin:2px 2px 8px}
.cmpq{display:flex}
.clh .cseg{white-space:nowrap}
.clh{display:grid;grid-template-columns:minmax(0,1fr) 44px 28px 72px;gap:4px;align-items:center;font-size:11px;text-transform:uppercase;letter-spacing:.05em;color:var(--mut);padding:4px 6px;border-bottom:1px solid var(--line)}
.clh small{text-transform:none;letter-spacing:0;color:var(--t3)}
.cseg{display:inline-flex;gap:2px;padding:2px;border-radius:999px;background:rgba(255,255,255,.04);border:1px solid var(--line)}
.cseg button{padding:3px 7px;border:0;border-radius:999px;background:none;font-size:11px}
.cseg button.on{background:rgba(255,255,255,.12);color:var(--fg)}
.clist{overflow:auto;flex:1;min-height:200px;display:flex;flex-direction:column;gap:3px;padding-top:4px}
.crow{display:grid;grid-template-columns:minmax(0,1fr) 44px 28px 72px;gap:4px;align-items:center;text-align:left;padding:6px 8px;border-radius:8px;border:1px solid transparent;border-left:3px solid transparent;background:rgba(20,40,80,.35);color:var(--fg);font:12px Inter,system-ui,sans-serif;cursor:pointer}
.crow:hover{background:rgba(30,55,100,.5)}
.crow.on{border-left-color:#3a86ff;background:rgba(58,134,255,.18)}
.crow .cn b{display:block;font-size:13px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.crow .cn small{font-size:11px;color:var(--mut);white-space:nowrap}
.crow .cp{color:var(--gold);font-weight:700;font-size:12px}
.crow .cr{color:var(--mut);font-size:11px;text-align:center}
.crow .cv{color:var(--acc);font:700 12px var(--fd);text-align:center}
.cmpl{width:300px}.cmpgrid{grid-template-columns:300px minmax(0,1fr)}
@media (max-width:860px){.cmpgrid{display:flex;flex-direction:column;gap:10px}.cmpl{width:auto;position:static;order:2;max-height:420px}.cmpr{order:1;width:100%}.cmpgrid:not(.pick) .cmpl{display:none}}
@media (min-width:861px){.cadd{display:none}}
.cmptop{display:flex;align-items:center;justify-content:space-between;gap:10px;margin:0 0 10px}
.cmptop h3{font:700 26px var(--fd);margin:2px 0 0}
.cmptop .eyebrow{color:var(--acc);font-size:11px;letter-spacing:.14em;text-transform:uppercase}
.cmpsel{display:flex;flex-wrap:wrap;gap:6px;align-items:center;margin-bottom:10px}
.cchip{display:inline-flex;align-items:center;gap:6px;padding:4px 4px 4px 8px;border-radius:999px;border:1px solid rgba(58,134,255,.5);background:rgba(58,134,255,.14);font-size:13px}
.cchip a.pn{color:var(--fg);font-weight:700;text-decoration:none}
.cchip small{color:var(--mut);font-size:11px}
.cchip .cx{width:22px;height:22px;padding:0;display:grid;place-items:center;font-size:14px}
.cmpw{overflow:auto;border-radius:12px;border:1px solid var(--line)}
table.cmpv{border-collapse:separate;border-spacing:0;width:100%;font-size:13px}
table.cmpv th,table.cmpv td{padding:8px 10px;border-bottom:1px solid var(--line);text-align:center;font-variant-numeric:tabular-nums;min-width:86px}
table.cmpv th.cmk{position:sticky;left:0;z-index:1;background:#0f1a2c;text-align:left;font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:.04em;color:var(--mut);min-width:78px;white-space:nowrap}
table.cmpv thead th{background:#0f1a2c;vertical-align:bottom}
table.cmpv th.cph a.pn{display:block;color:var(--fg);font-weight:700;font-size:14px;text-decoration:none;white-space:nowrap}
table.cmpv th.cph small{display:block;font-size:11px;color:var(--mut);font-weight:500;white-space:nowrap;margin-top:2px}
table.cmpv .kitw.ckit{display:block;position:relative;width:36px;height:36px;margin:0 auto 4px}
table.cmpv .kitw.ckit svg,table.cmpv .kitw.ckit img{position:absolute;inset:0;width:100%;height:100%;object-fit:contain}
table.cmpv td b{font-size:14px}
table.cmpv td b.best{color:var(--acc)}
table.cmpv td b.best::after{content:"";display:inline-block;width:6px;height:6px;border-radius:50%;background:var(--acc);margin-left:4px;vertical-align:middle}
table.cmpv .cfx{margin-top:3px}
table.cmpv tbody tr:hover td{background:rgba(255,255,255,.025)}
.cmpempty{display:flex;flex-direction:column;align-items:center;gap:8px;padding:60px 20px;color:var(--mut);text-align:center}
.cico{width:44px;height:44px;border-radius:50%;display:grid;place-items:center;background:rgba(69,208,143,.18);color:var(--acc);font-size:20px}
.cmph{display:flex;justify-content:space-between;align-items:flex-end;gap:10px;flex-wrap:wrap;margin:6px 0 10px;padding-bottom:10px;border-bottom:1px solid var(--line)}
.cmph h3{font:700 20px var(--fd);margin:2px 0}
.cmph p{margin:0;font-size:12px}
.cmpp{display:flex;gap:6px}
.cmpp span{font-size:11px;text-transform:uppercase;letter-spacing:.06em;color:var(--mut);padding:4px 10px;border-radius:999px;border:1px solid var(--line)}
.cmpp span.g{border-color:rgba(69,208,143,.45);color:var(--acc)}
.cmpp b{color:var(--fg)}
.cmpbar{display:flex;align-items:center;gap:8px;margin-bottom:8px;flex-wrap:wrap}
.cmpbar>b{font-size:12px;text-transform:uppercase;letter-spacing:.06em}
.cmpbar .grow{flex:1}
table.cmpt{font-size:13px}
table.cmpt th{font-size:11px;text-transform:uppercase;letter-spacing:.04em;color:var(--mut);white-space:nowrap}
table.cmpt th.now,table.cmpt td.now{background:rgba(58,134,255,.12)}
table.cmpt td{vertical-align:middle;font-variant-numeric:tabular-nums}
table.cmpt td.cpl{display:flex;align-items:center;gap:8px;min-width:150px;background:rgba(20,40,80,.35)}
table.cmpt td.cpl small{display:block;font-size:11px;color:var(--mut)}
table.cmpt td.wk{text-align:center}
table.cmpt td.wk b{display:block;margin-bottom:3px}
table.cmpt b.best{color:var(--acc)}
table.cmpt small.d{display:block;font-size:11px}
.cx{width:20px;height:20px;border-radius:50%;border:1px solid var(--line);background:none;color:var(--mut);cursor:pointer;flex:none;line-height:1}
.cx:hover{color:var(--bad);border-color:var(--bad)}
.fxc{display:inline-block;font:700 11px/1 Inter,system-ui,sans-serif;padding:4px 6px;border-radius:5px;white-space:nowrap;margin:1px}
.fxc.d1{background:#1e8e5a;color:#fff}.fxc.d2{background:#3fdc8a;color:#05261c}.fxc.d3{background:#5b6475;color:#fff}.fxc.d4{background:#ff8a8a;color:#3a0b0b}.fxc.d5{background:#a83246;color:#fff}.fxc.blank{background:#2a3446;color:var(--mut)}
.fxc.past{background:transparent;border:1px solid var(--line);color:var(--mut)}
.cmpswap{display:flex;align-items:center;gap:8px;flex-wrap:wrap;font-size:12px;margin-bottom:10px;padding:8px 10px;border:1px dashed var(--line);border-radius:10px}
/* Full player page */
.ppage{position:absolute;inset:0;z-index:30;overflow:hidden;background:rgba(2,6,14,.62);backdrop-filter:blur(2px)}
.ppage>#ppbody{position:absolute;left:50%;transform:translateX(-50%);width:min(720px,100%);top:56px;bottom:0;overflow:auto;background:radial-gradient(600px 300px at 90% -5%,#12374a 0%,transparent 60%),var(--bg);border-radius:18px 18px 0 0;border:1px solid var(--line);border-bottom:0;box-shadow:0 -20px 50px rgba(0,0,0,.5);animation:ppUp .22s ease both}
@keyframes ppUp{0%{opacity:0;transform:translate(-50%,40px)}to{opacity:1;transform:translate(-50%,0)}}
@media (max-width:640px){main{padding:10px 8px 18px;gap:10px}section.s{padding:12px;border-radius:12px}section.s>h2{font-size:20px;margin-bottom:4px}section.s>.sub{font-size:12px;line-height:1.4;margin-bottom:10px}}
@media (min-width:900px){.ppage>#ppbody{top:40px;bottom:40px;border-radius:18px;border-bottom:1px solid var(--line)}}
.pp2{padding:14px 14px 18px;display:flex;flex-direction:column;gap:10px}
.pph{position:relative;display:flex;gap:12px;align-items:center;padding:10px;border-radius:14px;background:linear-gradient(120deg,color-mix(in srgb,var(--k1,#33507e) 55%,transparent),rgba(11,18,32,.6) 70%);border:1px solid var(--line)}
.ppimg{position:relative;width:84px;height:100px;flex:none;border-radius:12px;overflow:hidden;background:radial-gradient(circle at 50% 30%,rgba(255,255,255,.18),transparent 70%)}
.ppimg .ppface{position:absolute;inset:0;width:100%;height:100%;object-fit:cover;object-position:top}
.ppimg .kitw.ppk{position:absolute;right:2px;bottom:2px;width:30px;height:30px;z-index:1;filter:drop-shadow(0 2px 3px rgba(0,0,0,.5));display:none}
.ppimg:has(.ppface.gone) .kitw.ppk{display:block}
.ppimg .kitw.ppk svg,.ppimg .kitw.ppk img{position:absolute;inset:0;width:100%;height:100%;object-fit:contain}
.ppimg:has(.ppface.gone) .kitw.ppk{inset:8px;width:auto;height:auto}
.ppt{flex:1;min-width:0;display:flex;flex-direction:column;gap:2px}
.ppt small{font-size:12px;color:#d6deea}
.ppt h1{font:700 26px/1.05 var(--fd);margin:2px 0 0;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.ppfull{font-size:12px;color:var(--mut)}
.ppchips{display:flex;flex-wrap:wrap;align-items:center;gap:4px 8px;margin-top:4px;font-size:12px;font-weight:700}
.ppp{font:700 16px var(--fd)}
.ppchips .sigchip{padding:2px 8px;font-size:11px}
.ppst2{font-size:12px;color:var(--gold);display:flex;align-items:center;gap:5px;margin-top:2px}
.ppx{position:absolute;top:6px;right:6px}
.ppk4{display:grid;grid-template-columns:repeat(4,1fr);gap:6px}
.ppk4>div{display:flex;flex-direction:column;align-items:center;gap:2px;padding:7px 4px;border-radius:11px;background:rgba(255,255,255,.04);border:1px solid var(--line);text-align:center}
.ppk4 small{font-size:11px;text-transform:uppercase;letter-spacing:.05em;color:var(--mut)}
.ppk4 b{font:700 20px var(--fd)}
.ppk4 span{font-size:11px;color:var(--mut)}
.pp2 .pchart{padding:8px 10px;border-radius:12px;border:1px solid var(--line);background:rgba(255,255,255,.02)}
.pp2 .pbars{height:auto}
.pp2 .pbw{height:56px}
.pp2 .pbar .fxc{font-size:11px;padding:2px 2px;max-width:100%;overflow:hidden;text-overflow:ellipsis}
.ppr2{display:grid;grid-template-columns:150px minmax(0,1fr);gap:10px;align-items:center}
.ppr2 .radw{position:relative;width:160px;height:150px}
.ppr2 .radar{left:34px;right:34px;top:24px;bottom:24px;width:auto!important;height:auto!important}
.ppr2 .rl small{font-size:11px}.ppr2 .rl b{font-size:11px}
.ppsg{display:grid;grid-template-columns:repeat(3,1fr);gap:5px}
.ppsg>div{display:flex;flex-direction:column;align-items:center;padding:5px 2px;border-radius:9px;background:rgba(255,255,255,.035)}
.ppsg b{font:700 16px var(--fd)}
.ppsg small{font-size:11px;color:var(--mut);text-transform:uppercase;letter-spacing:.04em}
.ppacts{display:grid;grid-template-columns:repeat(3,1fr);gap:6px}
.ppacts .mbtn{justify-content:center;padding:9px 6px;border-radius:10px;text-decoration:none;white-space:nowrap}
.ppmore{border:1px solid var(--line);border-radius:12px;padding:8px 12px;background:rgba(255,255,255,.02)}
.ppmore summary{cursor:pointer;font-size:13px;font-weight:700;color:var(--mut)}
.ppmore[open] summary{margin-bottom:8px}
.ppwhy{font-size:13px;margin:0 0 8px}
.ppmore .simg{display:grid;grid-template-columns:repeat(auto-fill,minmax(120px,1fr));gap:6px;margin:0}
.ppmore .psh{margin:12px 0 6px;font-size:13px}
@media (max-width:420px){.ppr2{grid-template-columns:150px minmax(0,1fr)}.ppr2 .radw{width:150px;height:144px}.ppt h1{font-size:23px}}
.ppage[hidden]{display:none}
.ppback{position:sticky;top:0;z-index:2;padding:10px 16px;background:rgba(11,18,32,.92);backdrop-filter:blur(6px);border-bottom:1px solid var(--line)}
.ppb{font:600 13px Inter,system-ui,sans-serif;color:var(--fg);background:rgba(255,255,255,.04);border:1px solid var(--line);border-radius:10px;padding:8px 14px;cursor:pointer}
.ppb:hover{border-color:var(--acc);color:var(--acc)}
.ppwrap,.ppage .pcols,.ppage .simg,.ppage .psh,.ppage .pexp,.ppage>div>.tw,.ppage>div>.pcard{margin-left:16px;margin-right:16px}
.pcard{background:linear-gradient(160deg,rgba(26,48,78,.75),rgba(14,26,44,.8));border:1px solid var(--line);border-radius:14px;padding:14px 16px}
.ppwrap{margin-top:14px}
.phead{display:grid;grid-template-columns:minmax(0,1fr) auto minmax(220px,300px);gap:12px 20px;padding:20px 24px}
.phl h1{font:700 34px/1.05 var(--fd);margin:0 0 6px}
.pmeta{margin:0;font-size:16px;color:var(--mut)}.pmeta b{color:var(--fg)}
.pid{margin:4px 0 8px;font-size:12px;color:var(--mut)}
.pprice{display:flex;flex-direction:column;gap:2px}
.pprice b{font:700 26px var(--fd)}
.pprice span{font-size:13px;font-weight:700}
.pupd{font-size:12px;color:var(--mut);margin:8px 0 0;display:flex;align-items:center;gap:6px}
.pupd .dot{width:8px;height:8px;border-radius:50%;background:var(--good)}.pupd .dot.warn{background:var(--warn)}
.pkit{align-self:center}
.prad{display:flex;flex-direction:column;align-items:center}
.radw{position:relative;width:240px;height:220px}
.radar{position:absolute;left:20px;top:18px;width:200px;height:184px}
.radar .rg{fill:none;stroke:rgba(255,255,255,.18);stroke-width:1}
.radar .rp{fill:rgba(255,90,106,.35);stroke:#ff5a6a;stroke-width:1.6}
.radar .rd{fill:#ff5a6a}
.radar .rc{font:700 26px var(--fd);fill:#8be08f;text-anchor:middle}
.rl{position:absolute;display:flex;flex-direction:column;align-items:center;font-size:11px;letter-spacing:.06em;text-transform:uppercase;color:var(--mut);line-height:1.1}
.rl b{font:700 13px var(--fd);color:var(--fg)}
.rl.t{top:0;left:50%;transform:translateX(-50%)}.rl.b{bottom:0;left:50%;transform:translateX(-50%)}.rl.l{left:0;top:46%}.rl.r{right:0;top:46%}
.pabout{grid-column:1/-1;border-top:1px dashed var(--line);border-bottom:1px solid var(--line);padding:10px 4px}
.pabout summary{cursor:pointer;font-weight:700}
.pabout p{color:var(--mut);font-size:13px;margin:8px 0 0}
.ptiles{grid-column:1/-1;display:grid;grid-template-columns:repeat(4,minmax(0,1fr));border:1px dashed var(--line);border-radius:10px}
.ptiles>div{padding:12px 16px;border-left:1px dashed var(--line);display:flex;flex-direction:column;gap:2px}
.ptiles>div:first-child{border-left:0}
.ptiles small{font-size:11px;letter-spacing:.1em;text-transform:uppercase;color:var(--mut)}
.ptiles b{font:700 30px/1.05 var(--fd)}
.ptiles b i{font:500 13px Inter,system-ui,sans-serif;color:var(--mut);margin-left:4px;font-style:normal}
.ptiles span{font-size:12px;color:var(--mut)}
.pchart{grid-column:1/-1}
.pch{display:flex;gap:10px;align-items:baseline;margin-bottom:8px}.pch b{font-size:14px;text-transform:uppercase;letter-spacing:.06em}
.pbars{display:grid;grid-template-columns:repeat(9,minmax(0,1fr));gap:10px;align-items:end}
.pbar{display:flex;flex-direction:column;align-items:center;gap:4px;min-width:0}
.pbar>b{font:700 16px var(--fd)}
.pbar.proj>b{color:var(--acc);font-family:ui-monospace,Consolas,monospace;font-size:16px}
.pbw{width:72%;height:90px;display:flex;align-items:flex-end}
.pbw i{display:block;width:100%;border-radius:4px 4px 0 0;background:#7c879a}
.pbar.proj .pbw i{background:rgba(69,208,143,.18);border:1.5px dashed rgba(69,208,143,.6);border-bottom:0}
.pbar small{font-size:11px;color:var(--mut)}
.pbar small.m{font-size:11px;color:var(--t3)}
.pleg{display:flex;gap:14px;justify-content:center;font-size:11px;color:var(--mut);margin-top:6px}
.pleg i{display:inline-block;width:10px;height:10px;border-radius:2px;margin-right:5px;vertical-align:-1px}
.pleg .lb{background:#7c879a}.pleg .lp{background:rgba(69,208,143,.25);border:1px dashed var(--acc)}
.pcols{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:12px;margin-top:12px}
.pcols.two{grid-template-columns:minmax(0,1fr) minmax(0,1fr)}
@media (max-width:900px){.pcols,.pcols.two,.phead{grid-template-columns:1fr}.ptiles{grid-template-columns:repeat(2,1fr)}.pbars{gap:4px}}
.pcard .eyebrow{color:var(--acc);font-size:11px;letter-spacing:.14em;display:block;margin-bottom:6px}
.pcard h3{font:700 20px var(--fd);margin:0 0 10px}
.sprows>div{display:flex;justify-content:space-between;padding:8px 0;border-bottom:1px solid var(--line);font-size:13px}
.sprows>div:last-child{border:0}
.rbig{display:flex;align-items:baseline;gap:8px;margin-bottom:6px}.rbig b{font:700 34px var(--fd);color:#8be08f}.rbig small{color:var(--mut);font-size:12px}
.pacts{display:flex;flex-direction:column;gap:10px;justify-content:center}
.sov{display:grid;grid-template-columns:repeat(5,minmax(0,1fr));gap:6px;margin-bottom:10px}
.sov>div{background:rgba(11,18,32,.55);border:1px solid var(--line);border-radius:10px;padding:8px}
.sov b{display:block;font:700 26px var(--fd)}
.sov small{display:block;font-size:11px;text-transform:uppercase;letter-spacing:.06em;color:var(--mut)}
.sov span{font-size:11px;color:var(--t3)}
.fss summary{cursor:pointer;display:flex;justify-content:space-between;font-weight:700;font-size:13px;padding:6px 0}
.fsg{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:14px;margin-top:8px}
.fsg p{display:flex;justify-content:space-between;margin:0;padding:6px 0;font-size:13px;border-bottom:1px solid rgba(255,255,255,.04)}
.fsg p b{font-family:ui-monospace,Consolas,monospace}
.fsg p.sm{font-size:11px;color:var(--t3);border:0;padding-top:0}
.sigtop{display:flex;gap:10px;align-items:stretch;margin-bottom:10px}
.sigtop>div{flex:1;background:rgba(11,18,32,.55);border:1px solid var(--line);border-radius:10px;padding:8px 10px;display:flex;flex-direction:column}
.sigtop b{font:700 26px var(--fd)}
.sigtop small{font-size:11px;color:var(--mut)}
.sigl.sbuy,.sigl.buy{color:var(--good)}.sigl.hold{color:var(--gold)}.sigl.sell{color:var(--bad)}
.psig p{font-size:13px;margin:0 0 10px}
.sigbar{display:grid;grid-template-columns:auto minmax(0,1fr) auto;gap:12px;align-items:center;margin-bottom:10px}
.sigchip{font:700 12px Inter,system-ui,sans-serif;padding:8px 12px;border-radius:8px;border:1px solid currentColor}
.sigchip.sbuy,.sigchip.buy{color:var(--good);background:rgba(63,220,138,.1)}.sigchip.hold{color:var(--gold);background:rgba(246,195,67,.1)}.sigchip.sell{color:var(--bad);background:rgba(255,111,111,.1)}
.sgt{position:relative;height:30px;background:linear-gradient(90deg,#ff5a6a,#f6c343 50%,#3fdc8a) top/100% 6px no-repeat;border-radius:4px;display:flex;justify-content:space-between;align-items:flex-end}
.sgt i{position:absolute;top:-5px;width:14px;height:14px;margin-left:-7px;border-radius:50%;background:#fff;box-shadow:0 0 0 2px rgba(0,0,0,.4)}
.sgt small{font-size:11px;text-transform:uppercase;color:var(--mut)}
.sigpts{text-align:center;padding:6px 10px;border:1px solid var(--line);border-radius:8px}.sigpts b{display:block;font:700 20px var(--fd);color:var(--acc)}.sigpts small{font-size:11px;color:var(--mut);text-transform:uppercase}
.why{border-left:3px solid var(--line);background:rgba(255,255,255,.03);border-radius:6px;padding:7px 10px;margin-top:6px;display:flex;flex-direction:column}
.why b{font-size:13px}.why small{font-size:12px;color:var(--mut)}
.why.good{border-color:var(--good)}.why.bad{border-color:var(--bad)}.why.warn{border-color:var(--gold)}
.psh{font:700 20px var(--fd);margin:18px 16px 8px}
.simg{display:grid;grid-template-columns:repeat(5,minmax(0,1fr));gap:10px}
@media (max-width:900px){.simg{grid-template-columns:repeat(2,1fr)}}
.simc{display:flex;flex-direction:column;gap:2px;padding:12px;border-radius:10px;border:1px solid var(--line);background:rgba(20,40,70,.5);color:var(--fg);text-decoration:none}
.simc:hover{border-color:var(--acc)}
.simc small{font-size:11px}
.simc span{display:flex;justify-content:space-between;margin-top:8px;font-size:13px}
.pexp{display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:10px;margin-bottom:24px}
.pexp>*{padding:10px 14px;border-radius:10px;border:1px solid var(--line);background:rgba(255,255,255,.03);color:var(--fg);font:600 13px Inter,system-ui,sans-serif;text-align:left;cursor:pointer;text-decoration:none}
.pexp>*:hover{border-color:var(--acc);color:var(--acc)}
.ppage>div>.tw{margin-bottom:6px}
/* leagues and cups */
.cuplive{display:flex;justify-content:space-between;align-items:center;gap:10px;padding:10px 12px;border-radius:10px;border:1px solid rgba(69,208,143,.35);background:rgba(16,56,42,.4);margin-bottom:10px;font-size:13px}
.cuplive>div{display:flex;align-items:baseline;gap:8px;flex-wrap:wrap}
.cuplive b{font:700 20px var(--fd)}
`;

  R.innerHTML = `<style>${CSS}</style><div class="root">
<div class="scrim" id="scrim"></div>
<div class="panel" role="dialog" aria-label="Elevn">
  <div class="bgfx" aria-hidden="true"><i class="haze"></i><i class="crowd"></i><i class="light l1"></i><i class="light l2"></i><i class="lamp lp1"></i><i class="lamp lp2"></i><i class="grass"></i><i class="glines"><svg viewBox="0 0 1000 600" preserveAspectRatio="none"><g fill="none" stroke="#fff" stroke-width="3"><rect x="40" y="20" width="920" height="560"/><path d="M500 20v560"/><circle cx="500" cy="300" r="80"/><rect x="40" y="170" width="150" height="260"/><rect x="810" y="170" width="150" height="260"/></g></svg></i><i class="blob b1"></i><i class="blob b2"></i></div>
  <div class="top">
    <div class="brand"><svg class="logo" viewBox="0 0 100 100" aria-hidden="true"><rect width="100" height="100" rx="24" fill="#2b0f45"/><g fill="#45d08f"><circle cx="50" cy="16" r="5.5"/><circle cx="40" cy="30" r="5.5"/><circle cx="60" cy="30" r="5.5"/><circle cx="30" cy="44" r="5.5"/><circle cx="50" cy="44" r="5.5"/><circle cx="70" cy="44" r="5.5"/><circle cx="20" cy="58" r="5.5"/><circle cx="50" cy="58" r="5.5"/><circle cx="80" cy="58" r="5.5"/><circle cx="50" cy="72" r="5.5"/></g><circle cx="50" cy="86" r="5.5" fill="#f6c343"/></svg><div><b>Elevn <small class="ver">v${ELEVN_VER}</small></b><span id="sub">FPL assistant · enter any team ID</span></div></div><span class="gwpill2" id="gwpill" hidden></span>
    <form id="f"><label for="tid">Team ID</label><span class="idw"><input id="tid" inputmode="numeric" autocomplete="off" placeholder="e.g. 123456"><button class="idb" id="idb" type="button" aria-label="My team and saved friends" aria-haspopup="menu" aria-expanded="false" title="My team and saved friends"><svg viewBox="0 0 24 24" width="16" height="16" aria-hidden="true"><path d="M16 11a3 3 0 1 0 0-6 3 3 0 0 0 0 6zM8 11a3 3 0 1 0 0-6 3 3 0 0 0 0 6zm0 2c-2.7 0-8 1.3-8 4v2h16v-2c0-2.7-5.3-4-8-4zm8 0c-.3 0-.7 0-1.1.1 1.2.9 2.1 2.1 2.1 3.9v2h7v-2c0-2.7-5.3-4-8-4z" fill="currentColor"/></svg><svg viewBox="0 0 24 24" width="12" height="12" aria-hidden="true"><path d="M6 9l6 6 6-6" fill="none" stroke="currentColor" stroke-width="3" stroke-linecap="round"/></svg></button><div class="idmenu" id="idmenu" role="menu" hidden></div></span><button class="go" type="submit">Analyse</button><button class="x rf" id="rf" type="button" title="Reload all data now" aria-label="Refresh data">⟳</button></form>
    <button class="x" id="setb" type="button" aria-label="Display settings" title="Display settings"><svg viewBox="0 0 24 24" width="17" height="17" aria-hidden="true"><path d="M12 15.5a3.5 3.5 0 1 0 0-7 3.5 3.5 0 0 0 0 7z" fill="none" stroke="currentColor" stroke-width="2"/><path d="M19.4 15a1.7 1.7 0 0 0 .3 1.8l.1.1a2 2 0 1 1-2.8 2.8l-.1-.1a1.7 1.7 0 0 0-1.8-.3 1.7 1.7 0 0 0-1 1.5V21a2 2 0 1 1-4 0v-.1a1.7 1.7 0 0 0-1.1-1.5 1.7 1.7 0 0 0-1.8.3l-.1.1a2 2 0 1 1-2.8-2.8l.1-.1a1.7 1.7 0 0 0 .3-1.8 1.7 1.7 0 0 0-1.5-1H3a2 2 0 1 1 0-4h.1a1.7 1.7 0 0 0 1.5-1.1 1.7 1.7 0 0 0-.3-1.8l-.1-.1a2 2 0 1 1 2.8-2.8l.1.1a1.7 1.7 0 0 0 1.8.3H9a1.7 1.7 0 0 0 1-1.5V3a2 2 0 1 1 4 0v.1a1.7 1.7 0 0 0 1 1.5 1.7 1.7 0 0 0 1.8-.3l.1-.1a2 2 0 1 1 2.8 2.8l-.1.1a1.7 1.7 0 0 0-.3 1.8V9a1.7 1.7 0 0 0 1.5 1H21a2 2 0 1 1 0 4h-.1a1.7 1.7 0 0 0-1.5 1z" fill="none" stroke="currentColor" stroke-width="1.6"/></svg></button>
    <button class="x" id="x" aria-label="Close analyst">×</button>
    <div class="updbar" id="updbar" role="status" hidden></div>
  </div>
  <nav id="nav"></nav>
  <div class="subnav" id="subnav" hidden></div>
  <main id="out"><p class="muted">Enter a team ID and press Analyse. You can find it in the address bar of any team's Points page: /entry/<b>123456</b>/event/…</p></main>
  <div class="wipe" id="wipe" aria-hidden="true"><i class="w3"></i><i class="w1"></i><i class="w2"></i></div>
  <div class="toasts" id="toasts" aria-live="polite"></div>
  <div class="qa" id="qa" hidden><div class="qascrim" id="qascrim"></div><div class="qabar" id="qabar" role="menu" aria-label="Player actions"></div></div>
  <div class="sheet" id="sheet" hidden><div class="sheetscrim" id="sheetscrim"></div><div class="sheetbody" id="sheetbody" role="dialog" aria-label="Player actions"></div></div>
  <section class="ppage" id="ppage" hidden aria-label="Player page"><div id="ppbody"></div></section>
  <aside class="drawer" id="drawer" hidden aria-label="Player profile"><button class="x dx" id="dx" type="button" aria-label="Close profile">×</button><div id="dbody"></div></aside>
</div></div>`;

  if (!document.getElementById('fpl-analyst-font')) { const fl = document.createElement('link'); fl.id = 'fpl-analyst-font'; fl.rel = 'stylesheet'; fl.href = 'https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700&family=Barlow+Semi+Condensed:wght@600;700&display=swap'; document.head.appendChild(fl); }
  const $ = (s) => R.querySelector(s);
  // ---------- v3: display settings ----------
  const UI_KEY = 'fplAnalystUI';
  let UI = { motion: 'normal', bg: 'flood', theme: 'matchday' };
  try { const u = JSON.parse(localStorage.getItem(UI_KEY) || '{}'); if (['calm', 'normal', 'lively'].includes(u.motion)) UI.motion = u.motion; if (['flood', 'club', 'plain'].includes(u.bg)) UI.bg = u.bg; if (['matchday', 'midnight', 'pitch'].includes(u.theme)) UI.theme = u.theme; } catch (e) {}
  const RM = () => window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches;
  function applyUI() { const r = R.querySelector('.root'); if (!r) return; r.classList.remove('m-calm', 'm-normal', 'm-lively', 'bg-flood', 'bg-club', 'bg-plain', 'th-matchday', 'th-midnight', 'th-pitch'); r.classList.add('m-' + UI.motion, 'bg-' + UI.bg, 'th-' + (UI.theme || 'matchday')); r.style.setProperty('--m', UI.motion === 'calm' ? 1.4 : UI.motion === 'lively' ? 0.8 : 1); }
  const saveUI = () => { try { localStorage.setItem(UI_KEY, JSON.stringify(UI)); } catch (e) {} };
  document.addEventListener('visibilitychange', () => { const r = R.querySelector('.root'); if (r) r.classList.toggle('paused', document.hidden); });
  const out = $('#out');
  applyUI();
  const close = () => { host.remove(); document.removeEventListener('keydown', onKey); };
  const onKey = (e) => { if (e.key === 'Escape') close(); };
  document.addEventListener('keydown', onKey);
  $('#x').onclick = close;
  const hasAndroid = () => { try { return !!(window.FPLAndroid && FPLAndroid.setPref); } catch (e) { return false; } };
  const aPref = (k, d) => { try { const v = FPLAndroid.getPref(k); return v == null || v === '' ? d : v; } catch (e) { return d; } };
  // v3.62 alert preferences: kick-offs of your matches, and every goal (phone keeps its own copy for background alerts)
  const alertPref = (k) => { if (hasAndroid()) return aPref(k, 'on') !== 'off'; try { return localStorage.getItem('elevnAl_' + k) !== 'off'; } catch (e) { return true; } };
  const alSeg = (k) => { const v = alertPref(k) ? 'on' : 'off'; return `<div class="seg" role="radiogroup">${[['on', 'On'], ['off', 'Off']].map(([x, l]) => `<button type="button" role="radio" aria-checked="${v === x}" class="${v === x ? 'on' : ''}" data-alp="${k}:${x}">${l}</button>`).join('')}</div>`; };
  const aSeg = (k) => { const v = aPref(k, 'on'); return `<div class="seg" role="radiogroup">${[['on', 'On'], ['off', 'Off']].map(([x, l]) => `<button type="button" role="radio" aria-checked="${v === x}" class="${v === x ? 'on' : ''}" data-ap="${k}:${x}">${l}</button>`).join('')}</div>`; };
  const XSKIP = /^(fplAnalystPast|fplAnalystAccuracy|fplAnalystNews|fplAnalystPriceSnap)/;
  function exportCode() { const o = {}; for (let i = 0; i < localStorage.length; i++) { const k = localStorage.key(i); if (/^fplAnalyst/.test(k) && !XSKIP.test(k)) o[k] = localStorage.getItem(k); } return 'FPLA1:' + btoa(unescape(encodeURIComponent(JSON.stringify(o)))); }
  function importCode(s) { try { const m = String(s || '').trim().match(/^FPLA1:([A-Za-z0-9+/=]+)$/); if (!m) return -1; const o = JSON.parse(decodeURIComponent(escape(atob(m[1])))); let n = 0; Object.entries(o).forEach(([k, v]) => { if (/^fplAnalyst/.test(k) && typeof v === 'string') { localStorage.setItem(k, v); n++; } }); return n; } catch (e) { return -1; } }
  $('#setb').onclick = () => {
    const sb = $('#sheetbody'); const seg = (k, opts) => `<div class="seg" role="radiogroup">${opts.map(([v, l]) => `<button type="button" role="radio" aria-checked="${UI[k] === v}" class="${UI[k] === v ? 'on' : ''}" data-ui="${k}:${v}">${l}</button>`).join('')}</div>`;
    const paint = () => { sb.innerHTML = `<div class="shgrab" data-close></div><div class="shh"><div><b>Settings</b><small>Saved on this device</small></div><button type="button" class="x" data-close aria-label="Close">×</button></div>
<div class="setrow"><div><b>Theme</b><small>Matchday: poster style · Midnight: calm navy · Pitch: dark green</small></div>${seg('theme', [['matchday', 'Matchday'], ['midnight', 'Midnight'], ['pitch', 'Pitch']])}</div>
<div class="setrow"><div><b>Motion</b><small>Calm stops the moving background and page wipes</small></div>${seg('motion', [['calm', 'Calm'], ['normal', 'Normal'], ['lively', 'Lively']])}</div>
<div class="setrow"><div><b>Background</b><small>Club colours follow your captain's club</small></div>${seg('bg', [['flood', 'Floodlit'], ['club', 'Club colours'], ['plain', 'Plain']])}</div>
<div class="setrow"><div><b>Kick-off, half-time and full-time alerts</b><small>For matches with one of your players</small></div>${alSeg('kickoff')}</div>
<div class="setrow"><div><b>All goals</b><small>A short alert for every Premier League goal, not only your players' (about 25–30 on a busy Saturday)</small></div>${alSeg('allgoals')}</div>
${hasAndroid() ? `<div class="setrow"><div><b>Deadline reminders</b><small>Phone notification 24 hours and 2 hours before each deadline</small></div>${aSeg('remind')}</div>
<div class="setrow"><div><b>Goal alerts with the app closed</b><small>Checks your players during matches (every minute right after you leave the app, then every 15 minutes)</small></div>${aSeg('bg')}</div>` : ''}
<div class="setrow"><div><b>Fast live feed</b><small>During matches, also reads free live score feeds (no key) and shows goals, assists and cards before FPL counts them, marked ⚡</small></div><div class="seg" role="radiogroup">${[['on', 'On'], ['off', 'Off']].map(([v, l]) => `<button type="button" role="radio" aria-checked="${(fastOn() ? 'on' : 'off') === v}" class="${(fastOn() ? 'on' : 'off') === v ? 'on' : ''}" data-fast="${v}">${l}</button>`).join('')}</div></div>
<div class="setrow"><div><b>Extra live source</b><small>Adds a third free source of live scores and match events. It is unofficial and may stop working; the other sources carry on if it does.</small></div><div class="seg" role="radiogroup">${[['on', 'On'], ['off', 'Off']].map(([v, l]) => `<button type="button" role="radio" aria-checked="${(fmOn() ? 'on' : 'off') === v}" class="${(fmOn() ? 'on' : 'off') === v ? 'on' : ''}" data-fm="${v}"${fastOn() ? '' : ' disabled'}>${l}</button>`).join('')}</div></div>
${(() => { const k = oddsKey(), o = ODDS || oddsLoadCache(); const agoT = (t) => { const m = Math.round((Date.now() - t) / 6e4); return m < 60 ? m + ' min ago' : Math.round(m / 60) + 'h ago'; };
  const st = !k ? (!oddsFreeOn() ? 'Off. Projections use the app\'s own model only.' : o && o.free && o.ok ? `On (free odds) · ${o.events.length} matches priced · updated ${agoT(o.at)}` : 'On (free odds). They load the next time you press Analyse.') : o && o.err && (!o.ok || o.errAt > o.at) ? `<span class="dn">Couldn't read odds: ${esc(o.err)}</span>` : o && o.ok ? `On · ${o.events.length} matches priced · updated ${agoT(o.at)}${o.left != null ? ` · ${esc(String(o.left))} requests left this month` : ''}` : 'Key saved. Odds load the next time you press Analyse.';
  return `<div class="setrow"><div><b>Free bookmaker odds</b><small>Used when no key is saved below.</small></div><div class="seg" role="radiogroup">${[['on', 'On'], ['off', 'Off']].map(([v, l]) => `<button type="button" role="radio" aria-checked="${(oddsFreeOn() ? 'on' : 'off') === v}" class="${(oddsFreeOn() ? 'on' : 'off') === v ? 'on' : ''}" data-oddsfree="${v}">${l}</button>`).join('')}</div></div>
<div class="setrow col"><div><b>Bookmaker odds</b><small>Adds betting-market win, draw and goals odds to the projections (half market, half model) for matches that have prices. Free odds from one bookmaker load automatically on every device. For an average of many bookmakers, add your own free key from the-odds-api.com (about 2–4 requests a day). The key stays on this device and is not included in the transfer code below.</small></div>
<div class="xrow"><input id="odds-key" type="password" autocomplete="off" spellcheck="false" placeholder="${k ? 'Key saved · paste a new one to replace it' : 'Paste your API key'}" aria-label="The Odds API key"><button type="button" class="mbtn" data-odds="save">Save</button>${k ? '<button type="button" class="mbtn ghost" data-odds="test">Refresh now</button><button type="button" class="mbtn ghost" data-odds="del">Remove</button>' : ''}</div><small class="oddst">${st}</small></div>`; })()}
<div class="setrow col"><div><b>Move your plan to another device</b><small>Planned transfers, chips, saved teams and settings. Copy the code here, paste it on the other phone or computer.</small></div>
<div class="xrow"><button type="button" class="mbtn" data-xp="1">⇪ Copy my code</button><button type="button" class="mbtn ghost" data-xi="1">⇩ Paste a code</button></div>
<textarea id="xcode" rows="3" placeholder="Your code appears here, or paste a code from another device" spellcheck="false"></textarea><button type="button" class="mbtn big" data-xgo="1" hidden>Import this code</button></div>`; };
    paint(); sheet.hidden = false;
    sb.onclick = (ev) => { const u = ev.target.closest('[data-ui]'); if (u) { const [k, v] = u.dataset.ui.split(':'); UI[k] = v; saveUI(); applyUI(); paint(); ev.stopPropagation(); return; }
      const ofb = ev.target.closest('[data-oddsfree]'); if (ofb) { ev.stopPropagation(); try { localStorage.setItem(ODDS_FREE, ofb.dataset.oddsfree); localStorage.removeItem(ODDS_CACHE); } catch (e) {} ODDS = null; paint(); const v2 = $('#tid').value.trim(); fetchOdds(true).then(() => { paint(); if (v2) run(+v2, { quiet: true }); }); return; }
      const fmb = ev.target.closest('[data-fm]'); if (fmb) { ev.stopPropagation(); try { localStorage.setItem(FMK, fmb.dataset.fm); } catch (e) {} paint(); return; }
      const fb = ev.target.closest('[data-fast]'); if (fb) { ev.stopPropagation(); try { localStorage.setItem(FASTK, fb.dataset.fast); } catch (e) {} if (fb.dataset.fast === 'on' && LASTA) { clearTimeout(FASTT); FASTT = null; fastTick(); } else { clearTimeout(FASTT); FASTT = null; } paint(); if (LASTA) { LASTA.live = LASTA.gwCmp && LASTA.gwCmp.liveC ? liveScore(LASTA.cur, LASTA.gwCmp) : LASTA.live; if (LASTA.live) fastApply(LASTA, LASTA.live); paintLiveNow(LASTA); } return; }
      const od = ev.target.closest('[data-odds]'); if (od) { ev.stopPropagation(); const act = od.dataset.odds;
        if (act === 'save') { const v = (sb.querySelector('#odds-key').value || '').trim(); if (!/^[A-Za-z0-9]{16,64}$/.test(v)) { toast('That key doesn\'t look right', 'Copy the API key from your the-odds-api.com account page.', 'bad'); return; } try { localStorage.setItem(ODDS_KEY, v); localStorage.removeItem(ODDS_CACHE); } catch (e) {} ODDS = null; od.disabled = true; fetchOdds(true).then(() => { paint(); if (ODDS && ODDS.ok && !ODDS.err) { toast('Odds on', `${ODDS.events.length} matches priced. Re-analysing…`, 'good'); const v2 = $('#tid').value.trim(); if (v2) run(+v2, { quiet: true }); } else toast('Couldn\'t read odds', (ODDS && ODDS.err) || 'Check the key', 'bad'); }); return; }
        if (act === 'test') { od.disabled = true; fetchOdds(true).then(() => { paint(); const v2 = $('#tid').value.trim(); if (v2 && ODDS && ODDS.ok) run(+v2, { quiet: true }); }); return; }
        if (act === 'del') { try { localStorage.removeItem(ODDS_KEY); localStorage.removeItem(ODDS_CACHE); } catch (e) {} ODDS = null; paint(); toast('Odds off', 'Projections use the app\'s own model only.', 'good'); const v2 = $('#tid').value.trim(); if (v2) run(+v2, { quiet: true }); return; } }
      const alp = ev.target.closest('[data-alp]'); if (alp) { const [k, v] = alp.dataset.alp.split(':'); try { localStorage.setItem('elevnAl_' + k, v); } catch (e) {} if (hasAndroid()) { try { FPLAndroid.setPref(k, v); } catch (e) {} } paint(); ev.stopPropagation(); return; }
      const ap = ev.target.closest('[data-ap]'); if (ap) { const [k, v] = ap.dataset.ap.split(':'); try { FPLAndroid.setPref(k, v); } catch (e) {} if (LASTA) androidSync(LASTA); paint(); ev.stopPropagation(); return; }
      const ta = sb.querySelector('#xcode');
      if (ev.target.closest('[data-xp]')) { const c = exportCode(); ta.value = c; ta.select(); let ok = false; try { if (hasAndroid() && FPLAndroid.copyText) { FPLAndroid.copyText(c); ok = true; } } catch (e) {} if (!ok && navigator.clipboard) navigator.clipboard.writeText(c).then(() => toast('Code copied', 'Paste it in Elevn on your other device (Display settings).', 'good')).catch(() => toast('Code ready', 'Select the text and copy it.', '')); else if (ok) toast('Code copied', 'Paste it in Elevn on your other device (Display settings).', 'good'); ev.stopPropagation(); return; }
      if (ev.target.closest('[data-xi]')) { ta.value = ''; ta.focus(); sb.querySelector('[data-xgo]').hidden = false; if (navigator.clipboard && navigator.clipboard.readText) navigator.clipboard.readText().then((x) => { if (/^FPLA1:/.test(x.trim())) ta.value = x.trim(); }).catch(() => {}); ev.stopPropagation(); return; }
      if (ev.target.closest('[data-xgo]')) { const n = importCode(ta.value); if (n < 0) { toast('That code didn\'t work', 'Copy the whole code, starting with FPLA1:', 'bad'); } else { toast('Imported', `${n} saved items restored. Reloading…`, 'good'); setTimeout(() => { close(); setTimeout(runFplAnalyst, 50); }, 900); } ev.stopPropagation(); return; }
    };
    sb.addEventListener('input', (ev) => { if (ev.target.id === 'xcode') { const g = sb.querySelector('[data-xgo]'); if (g) g.hidden = !/^\s*FPLA1:/.test(ev.target.value); } });
  };
  $('#scrim').onclick = close;

  // v3.15: every FPL answer is also kept in the browser cache, so the next start can show the last data at once
  const CKEY = 'fpl-analyst-v1'; let FAST = false;
  const cacheOk = () => { try { return typeof caches !== 'undefined' && window.isSecureContext; } catch (e) { return false; } };
  const J = async (u) => {
    if (FAST && cacheOk()) { try { const m = await (await caches.open(CKEY)).match(u); if (m) return m.json(); } catch (e) {} }
    const r = await fetch(u, { credentials: 'include', cache: 'no-store' });
    if (!r.ok) throw new Error(`${u} returned HTTP ${r.status}`);
    if (cacheOk() && !/\/api\/(me|my-team)\//.test(u)) { try { const c = r.clone(); caches.open(CKEY).then((k) => k.put(u, c)).catch(() => {}); } catch (e) {} }
    return r.json();
  };
  const esc = (s) => String(s ?? '').replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
  const f1 = (n) => (Math.round(n * 10) / 10).toFixed(1);
  const money = (n) => '£' + (n / 10).toFixed(1) + 'm';
  const POS = ['', 'GK', 'DEF', 'MID', 'FWD'];
  // Set-piece duties from FPL's own data (1 = first choice)
  const SPN = { P: 'Penalties', FK: 'Direct free kicks', CK: 'Corners and indirect free kicks' };
  const spList = (e) => { const o = []; const f = (v, l) => { if (v != null && v <= 2) o.push([l, v]); }; f(e.penalties_order, 'P'); f(e.direct_freekicks_order, 'FK'); f(e.corners_and_indirect_freekicks_order, 'CK'); return o; };
  // One small badge only: P = first-choice penalty taker, SP = first choice for free kicks or corners (details on hover)
  const spB = (e) => { const l = spList(e).filter(([, v]) => v === 1); if (!l.length) return ''; return `<i class="sp" title="First choice: ${l.map(([k]) => SPN[k].toLowerCase()).join(', ')}">${l.some(([k]) => k === 'P') ? 'P' : 'SP'}</i>`; };
  // Home / away marker used everywhere a fixture is shown
  const ha = (home) => `<i class="ha ${home ? 'h' : 'a'}">${home ? 'H' : 'A'}</i>`;
  // Club badge as served by the Premier League's own site; falls back to the club-colour shirt if it can't load
  const crest = (id, big) => { const t = BS && BS.teams.find((x) => x.id === id); if (!t) return ''; return `<span class="crw${big ? ' big' : ''}">${shirtMini(t.short_name)}${t.code ? `<img class="crest" src="https://resources.premierleague.com/premierleague/badges/70/t${t.code}.png" data-alt="https://resources.premierleague.com/premierleague25/badges/${t.code}.svg" alt="" loading="lazy" referrerpolicy="no-referrer">` : ''}</span>`; };
  // Shirt icons drawn in each club's colours: [body, trim, striped]
  const KIT = { ARS: ['#e01a22', '#ffffff'], AVL: ['#7b1e3c', '#95bfe5'], BOU: ['#d71920', '#141414', 1], BRE: ['#e30613', '#ffffff', 1], BHA: ['#0057b8', '#ffffff', 1], BUR: ['#6c1d45', '#99d6ea'], CHE: ['#034694', '#ffffff'], COV: ['#6cabdd', '#ffffff'], CRY: ['#1b458f', '#c4122e', 1], EVE: ['#003399', '#ffffff'], FUL: ['#ffffff', '#141414'], HUL: ['#f5a12d', '#141414', 1], IPS: ['#1d4fa3', '#ffffff'], LEE: ['#ffffff', '#ffcd00'], LEI: ['#0053a0', '#ffffff'], LIV: ['#c8102e', '#8e0b20'], MCI: ['#6cabdd', '#ffffff'], MUN: ['#da291c', '#141414'], NEW: ['#ffffff', '#141414', 1], NFO: ['#dd0000', '#ffffff'], SOU: ['#d71920', '#ffffff', 1], SUN: ['#eb172b', '#ffffff', 1], TOT: ['#ffffff', '#132257'], WHU: ['#7a263a', '#1bb1e7'], WOL: ['#fdb913', '#141414'] };
  // v3.11: official FPL kit images (same site), with the drawn shirt underneath as a fallback if the image can't load
  const kitUrl = (code, gk, size) => `https://fantasy.premierleague.com/dist/img/shirts/standard/shirt_${code}${gk ? '_1' : ''}-${size || 110}.webp`;
  const kitImg = (sn, gk, size, cls) => { const t = BS && BS.teams.find((x) => x.short_name === sn); return `<span class="kitw ${cls || ''}">${shirtSvg(sn, gk)}${t && t.code ? `<img class="kimg" src="${kitUrl(t.code, gk, size)}" alt="" loading="lazy">` : ''}</span>`; };
  const shirt = (sn, gk) => kitImg(sn, gk, 66);
  const shirtSvg = (sn, gk) => { const k = gk ? ['#f4c430', '#1c1c1c', 0] : KIT[sn] || ['#8a97ab', '#e6ebf2', 0]; return `<svg class="kit" viewBox="0 0 48 42" aria-hidden="true"><path d="M14 3l6 3q4 2 8 0l6-3 12 8-5 9-5-3v22H12V17l-5 3-5-9z" fill="${k[0]}" stroke="rgba(0,0,0,.45)" stroke-width="1" stroke-linejoin="round"/>${k[2] ? `<path d="M16 9h3.2v30H16zM22.4 8h3.2v31h-3.2zM28.8 9H32v30h-3.2z" fill="${k[1]}"/>` : `<path d="M14 3L2 11l5 9 5-3v-7zM34 3l12 8-5 9-5-3v-7z" fill="${k[1]}"/>`}<path d="M20 6q4 4 8 0" fill="none" stroke="${k[2] ? k[0] : k[1]}" stroke-width="2"/></svg>`; };
  // ---------- Jersey: original shirt art in club colours with the club code across the chest ----------
  // [body, sleeves, stripe colour (null = plain), trim, code colour]
  const JST = { ARS: ['#d6202a', '#f4f4f4', null, '#ffffff', '#ffffff'], AVL: ['#7b1e3c', '#95bfe5', null, '#95bfe5', '#ffffff'], BOU: ['#141414', '#141414', '#d71920', '#d71920', '#ffffff'], BRE: ['#ffffff', '#e30613', '#e30613', '#141414', '#141414'], BHA: ['#ffffff', '#0b5cc4', '#0b5cc4', '#0b5cc4', '#0b3f8a'], BUR: ['#6c1d45', '#99d6ea', null, '#99d6ea', '#ffffff'], CHE: ['#0a4fb3', '#0a4fb3', null, '#ffffff', '#ffffff'], COV: ['#7fbfe9', '#7fbfe9', null, '#ffffff', '#0a1322'], CRY: ['#1b458f', '#1b458f', '#c4122e', '#c4122e', '#ffffff'], EVE: ['#1546b8', '#1546b8', null, '#ffffff', '#ffffff'], FUL: ['#ffffff', '#ffffff', null, '#141414', '#141414'], HUL: ['#f5a12d', '#141414', null, '#141414', '#141414'], IPS: ['#1d4fa3', '#1d4fa3', null, '#ffffff', '#ffffff'], LEE: ['#ffffff', '#ffffff', null, '#1d4fa3', '#1d4fa3'], LEI: ['#0053a0', '#0053a0', null, '#ffffff', '#ffffff'], LIV: ['#c8102e', '#c8102e', null, '#ffffff', '#ffffff'], MCI: ['#8cc4ec', '#8cc4ec', null, '#ffffff', '#ffffff'], MUN: ['#da291c', '#da291c', null, '#141414', '#ffffff'], NEW: ['#ffffff', '#141414', '#141414', '#141414', '#141414'], NFO: ['#dd0000', '#dd0000', null, '#ffffff', '#ffffff'], SOU: ['#ffffff', '#d71920', '#d71920', '#141414', '#141414'], SUN: ['#ffffff', '#eb172b', '#eb172b', '#141414', '#141414'], TOT: ['#ffffff', '#ffffff', null, '#132257', '#132257'], WHU: ['#7a263a', '#1bb1e7', null, '#1bb1e7', '#ffffff'], WOL: ['#fdb913', '#141414', null, '#141414', '#141414'] };
  const GKC = ['#e64b9a', '#2dbf8a', '#2f2f35', '#f4c430', '#7b5cff', '#ff8a3d'];
  const J_SHORT = 'M38 10 L50 5 Q60 13 70 5 L82 10 L114 28 L102 52 L90 46 L90 106 Q60 110 30 106 L30 46 L18 52 L6 28 Z';
  const J_LONG = 'M38 10 L50 5 Q60 13 70 5 L82 10 L108 26 L116 86 L102 88 L92 50 L90 106 Q60 110 30 106 L28 50 L18 88 L4 86 L12 26 Z';
  const J_SLV_S = 'M38 10 L6 28 L18 52 L30 46 L30 24 Z M82 10 L114 28 L102 52 L90 46 L90 24 Z';
  const J_SLV_L = 'M38 10 L12 26 L4 86 L18 88 L28 50 L30 24 Z M82 10 L108 26 L116 86 L102 88 L92 50 L90 24 Z';
  let JID = 0;
  // form: three last-gameweek scores, oldest first ({p: points, m: minutes})
  const formTone = (f) => (!f || !f.m ? '#3a4458' : f.p >= 6 ? '#3fdc8a' : f.p >= 3 ? '#e9edf3' : '#ff5a6a');
  // Illustrated player in the club's kit (no real photos): neutral face, club shirt, stripes and sleeves from the kit palette
  let PID2 = 0;
  function playerSvg(e, sn) {
    const gk = e.element_type === 1; const s = JST[sn] || ['#8a97ab', '#8a97ab', null, '#e6ebf2', '#ffffff'];
    const body = gk ? GKC[e.team % GKC.length] : s[0], slv = gk ? body : s[1], str = gk ? null : s[2], trim = s[3] || '#ffffff'; const id = 'pp' + (++PID2);
    const torso = 'M10 100V80q2-16 24-20l8-3q8 6 16 0l8 3q22 4 24 20v20z';
    return `<svg class="jsv psv" viewBox="0 0 100 100" aria-hidden="true"><defs><clipPath id="c${id}"><path d="${torso}"/></clipPath><linearGradient id="k${id}" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#a7b2c3"/><stop offset="1" stop-color="#76839a"/></linearGradient><linearGradient id="h${id}" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="#000" stop-opacity=".28"/><stop offset=".5" stop-color="#fff" stop-opacity=".12"/><stop offset="1" stop-color="#000" stop-opacity=".28"/></linearGradient></defs>
<g clip-path="url(#c${id})"><rect width="100" height="100" fill="${body}"/>${str ? `<g fill="${str}">${[20, 32, 44, 56, 68, 80].map((x) => `<rect x="${x}" y="50" width="6" height="60"/>`).join('')}</g>` : ''}<path d="M10 100V80q2-14 16-19v39zM90 100V80q-2-14-16-19v39z" fill="${slv}"/><rect width="100" height="100" fill="url(#h${id})"/></g>
<path d="M42 57q8 7 16 0" fill="none" stroke="${trim === body ? '#ffffff' : trim}" stroke-width="2.6"/><rect x="43" y="43" width="14" height="15" rx="5" fill="url(#k${id})"/><ellipse cx="50" cy="31" rx="14" ry="16.5" fill="url(#k${id})"/><path d="M36 27q2-14 14-14t14 14q-3-7-14-7t-14 7z" fill="#4b5667"/></svg>`;
  }
  // Round club icon used beside player names in every list (club badge, or club colours with the player's initials)
  const ini = (e) => { const p = String(e.web_name || '').split(/[\s.]+/).filter(Boolean); return ((p[0] || '')[0] || '') + ((p[1] || '')[0] || ''); };
  function pface(e) { const t = BS && BS.teams.find((x) => x.id === e.team); const k = (t && JST[t.short_name]) || ['#33507e', '#1a2a45']; return `<span class="picon face" style="background:linear-gradient(160deg,${k[0]},${k[1]})" aria-hidden="true"><b>${esc((e.web_name || '?').charAt(0))}</b><img class="pfimg" src="https://resources.premierleague.com/premierleague25/photos/players/110x140/${e.code}.png" data-alt="https://resources.premierleague.com/premierleague/photos/players/110x140/p${e.code}.png" alt="" loading="lazy" referrerpolicy="no-referrer"></span>`; }
  function pkit(e) { const t = BS && BS.teams.find((x) => x.id === e.team); return `<span class="picon kit" aria-hidden="true">${t ? kitImg(t.short_name, e.element_type === 1, 66) : ''}</span>`; }
  function picon(e) {
    const t = BS && BS.teams.find((x) => x.id === e.team); const s = (t && JST[t.short_name]) || ['#3a4a66', '#3a4a66', null, '#e6ebf2', '#ffffff'];
    const fg = s[4] && s[4] !== s[0] ? s[4] : '#ffffff';
    return `<span class="picon" style="background:${s[0]};color:${fg}" aria-hidden="true"><b>${esc(ini(e)).toUpperCase()}</b>${t && t.code ? `<img class="crest" src="https://resources.premierleague.com/premierleague/badges/70/t${t.code}.png" data-alt="https://resources.premierleague.com/premierleague25/badges/${t.code}.svg" alt="" loading="lazy" referrerpolicy="no-referrer">` : ''}</span>`;
  }
  function decorateNames(root) {
    if (!root || !BS) return;
    root.querySelectorAll('a.pn[data-pid]:not([data-pi])').forEach((a) => {
      a.setAttribute('data-pi', '1');
      if (a.closest('.chip.pc, .jname, .sact, .qa, .slide, .hni, .ncard, .nodeco, .simc, #ppage')) return;
      const e = BS.elements.find((x) => x.id === +a.dataset.pid); if (!e) return;
      a.insertAdjacentHTML('afterbegin', a.closest('#s-squad, #s-live, #eo-box') ? pface(e) : a.closest('.cands, .kitn') ? pkit(e) : picon(e));
    });
  }
  function jerseySvg(e, sn) {
    if (typeof CI !== 'undefined' && CI.art === 'player') return playerSvg(e, sn);
    if (typeof CI === 'undefined' || CI.art === 'real') { const t = BS && BS.teams.find((x) => x.short_name === sn); if (t && t.code) return `<span class="kitw jk">${jerseyDrawn(e, sn)}<img class="kimg" src="${kitUrl(t.code, e.element_type === 1, 110)}" alt="" loading="lazy"></span>`; }
    return jerseyDrawn(e, sn);
  }
  function jerseyDrawn(e, sn) {
    const gk = e.element_type === 1; const s = JST[sn] || ['#8a97ab', '#8a97ab', null, '#e6ebf2', '#ffffff'];
    const body = gk ? GKC[e.team % GKC.length] : s[0]; const id = 'j' + (++JID);
    const shape = gk ? J_LONG : J_SHORT;
    return `<svg class="jsv" viewBox="0 0 120 112" aria-hidden="true"><defs><clipPath id="c${id}"><path d="${shape}"/></clipPath>
<linearGradient id="s${id}" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="#000" stop-opacity=".32"/><stop offset=".3" stop-color="#000" stop-opacity=".05"/><stop offset=".5" stop-color="#fff" stop-opacity=".14"/><stop offset=".72" stop-color="#000" stop-opacity=".04"/><stop offset="1" stop-color="#000" stop-opacity=".3"/></linearGradient>
<linearGradient id="f${id}" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#fff" stop-opacity=".1"/><stop offset="1" stop-color="#000" stop-opacity=".22"/></linearGradient></defs>
<g clip-path="url(#c${id})"><rect width="120" height="112" fill="${body}"/><path d="${gk ? J_SLV_L : J_SLV_S}" fill="${gk ? body : s[1]}"/>${!gk && s[2] ? `<g fill="${s[2]}"><rect x="34" width="7" height="112"/><rect x="48" width="7" height="112"/><rect x="62" width="7" height="112"/><rect x="76" width="7" height="112"/></g>` : ''}
<path d="M30 40 Q40 70 34 108 M90 40 Q80 72 88 108 M52 30 Q56 70 50 108" fill="none" stroke="#000" stroke-opacity=".07" stroke-width="3"/><rect width="120" height="112" fill="url(#s${id})"/><rect width="120" height="112" fill="url(#f${id})"/>
<path d="${gk ? 'M5 80 L18 82 M115 80 L102 82' : 'M8 31 L19 49 M112 31 L101 49'}" fill="none" stroke="${gk ? '#fff' : s[3]}" stroke-width="3"/></g>
<path d="${shape}" fill="none" stroke="#000" stroke-opacity=".35" stroke-width="1"/><path d="${e.id % 2 ? 'M50 5 L60 18 L70 5' : 'M50 5 Q60 14 70 5'}" fill="none" stroke="${gk ? '#fff' : s[3]}" stroke-width="3.2" stroke-linecap="round"/></svg>`;
  }
  // The full jersey block: shirt + code + badges, name bar, value bar, form strip
  function jersey(A, e, o) {
    o = o || {}; const T = A.T, sn = T[e.team].short_name; const gk = e.element_type === 1;
    const codeC = gk ? '#ffffff' : (JST[sn] || [])[4] || '#ffffff';
    const glow = codeC === '#ffffff' ? '0 0 2px rgba(0,0,0,.9),0 1px 3px rgba(0,0,0,.6)' : '0 0 2px rgba(255,255,255,.95),0 0 4px rgba(255,255,255,.7)';
    const fm = (A.form && A.form[e.id]) || [];
    const flag = e.status !== 'a';
    const star = !flag && +e.form >= 6;
    return `<div class="jsh${typeof CI === 'undefined' || CI.art === 'real' ? ' real' : ''}">${jerseySvg(e, sn)}<span class="jcode" style="color:${codeC};text-shadow:${glow}">${sn}</span>${star ? '<svg class="jstar" viewBox="0 0 24 24" role="img" aria-label="In form"><circle cx="12" cy="12" r="11" fill="#1c2433" stroke="#fff" stroke-width="1.5"/><path d="M12 5.5l1.9 3.9 4.3.6-3.1 3 .7 4.3-3.8-2-3.8 2 .7-4.3-3.1-3 4.3-.6z" fill="#f6c343"/></svg>' : ''}${flag ? `<svg class="jwarn" viewBox="0 0 24 22" role="img" aria-label="${esc(e.news || 'Flagged')}"><title>${esc(e.news || 'Flagged')}</title><path d="M12 1.5L23 20.5H1z" fill="${['i', 's', 'u', 'n'].includes(e.status) ? '#ff5a6a' : '#f6c343'}" stroke="#1c2433" stroke-width="1.5" stroke-linejoin="round"/><rect x="11" y="8" width="2" height="7" fill="#1c2433"/><rect x="11" y="16.5" width="2" height="2" fill="#1c2433"/></svg>` : ''}${o.role ? `<span class="jrole ${o.role === 'V' ? 'v' : ''}">${o.role}</span>` : ''}</div>
${o.sp ? `<span class="jsp">${o.sp}</span>` : ''}<div class="jname" title="${esc(country(e))}${country(e) ? ' · ' : ''}Last 3 gameweeks: ${fm.map((f) => (f && f.m ? f.p : '–')).join(', ')} pts">${esc(e.web_name)}</div><div class="jval">${o.val}</div>${o.sub ? `<div class="jsub${o.strip ? ' hstrip' : ''}">${o.sub}</div>` : ''}`;
  }
  // v3.20: player nationality flags (FPL region id -> flag-icons code and country name)
  const REGION = {}; '1:af:Afghanistan,2:al:Albania,3:dz:Algeria,4:as:American Samoa,5:ad:Andorra,6:ao:Angola,7:ai:Anguilla,8:aq:Antarctica,9:ag:Antigua and Barbuda,10:ar:Argentina,11:am:Armenia,12:aw:Aruba,13:au:Australia,14:at:Austria,15:az:Azerbaijan,16:bs:Bahamas,17:bh:Bahrain,18:bd:Bangladesh,19:bb:Barbados,20:by:Belarus,21:be:Belgium,22:bz:Belize,23:bj:Benin,24:bm:Bermuda,25:bt:Bhutan,26:bo:Bolivia,27:ba:Bosnia-Herzegovina,28:bw:Botswana,29:bv:Bouvet Island,30:br:Brazil,31:io:British Indian Ocean Territory,32:vg:British Virgin Islands,33:bn:Brunei Darussalam,34:bg:Bulgaria,35:bf:Burkina Faso,36:bi:Burundi,37:kh:Cambodia,38:cm:Cameroon,39:ca:Canada,40:cv:Cape Verde,41:ky:Cayman Islands,42:cf:Central African Republic,43:td:Chad,44:cl:Chile,45:cn:China,46:cx:Christmas Island,47:cc:Cocos Islands,48:co:Colombia,49:km:Comoros,50:cd:Congo Democratic Republic of,51:cg:Congo,52:ck:Cook Islands,53:cr:Costa Rica,54:ci:Ivory Coast,55:cu:Cuba,56:cy:Cyprus,57:cz:Czech Republic,58:dk:Denmark,59:dj:Djibouti,60:dm:Dominica,61:do:Dominican Republic,62:ec:Ecuador,63:eg:Egypt,64:sv:El Salvador,65:gq:Equatorial Guinea,66:er:Eritrea,67:ee:Estonia,68:et:Ethiopia,69:fo:Faeroe Islands,70:fk:Falkland Islands,71:fj:Fiji,72:fi:Finland,73:fr:France,74:gf:French Guiana,75:pf:French Polynesia,76:tf:French Southern Territories,77:ga:Gabon,78:gm:Gambia,79:ge:Georgia,80:de:Germany,81:gh:Ghana,82:gi:Gibraltar,83:gr:Greece,84:gl:Greenland,85:gd:Grenada,86:gp:Guadaloupe,87:gu:Guam,88:gt:Guatemala,89:gn:Guinea,90:gw:Guinea-Bissau,91:gy:Guyana,92:ht:Haiti,93:hm:Heard and McDonald Islands,94:va:Holy See,95:hn:Honduras,96:hk:Hong Kong China,97:hr:Croatia,98:hu:Hungary,99:is:Iceland,100:in:India,101:id:Indonesia,102:ir:Iran,103:iq:Iraq,104:ie:Ireland,105:il:Israel,106:it:Italy,107:jm:Jamaica,108:jp:Japan,109:jo:Jordan,110:kz:Kazakhstan,111:ke:Kenya,112:ki:Kiribati,113:kp:North Korea,114:kr:South Korea,115:kw:Kuwait,116:kg:Kyrgyzstan,117:la:Laos,118:lv:Latvia,119:lb:Lebanon,120:ls:Lesotho,121:lr:Liberia,122:ly:Libya,123:li:Liechtenstein,124:lt:Lithuania,125:lu:Luxembourg,126:mo:Macao China,127:mk:Macedonia,128:mg:Madagascar,129:mw:Malawi,130:my:Malaysia,131:mv:Maldives,132:ml:Mali,133:mt:Malta,134:mh:Marshall Islands,135:mq:Martinique,136:mr:Mauritania,137:mu:Mauritius,138:yt:Mayotte,139:mx:Mexico,140:fm:Micronesia,141:md:Moldova,142:mc:Monaco,143:mn:Mongolia,144:ms:Montserrat,145:ma:Morocco,146:mz:Mozambique,147:mm:Myanmar,148:na:Namibia,149:nr:Nauru,150:np:Nepal,152:nl:Netherlands,153:nc:New Caledonia,154:nz:New Zealand,155:ni:Nicaragua,156:ne:Niger,157:ng:Nigeria,158:nu:Niue,159:nf:Norfolk Island,160:mp:Northern Mariana Islands,161:no:Norway,162:om:Oman,163:pk:Pakistan,164:pw:Palau,165:ps:Palestine,166:pa:Panama,167:pg:Papua New Guinea,168:py:Paraguay,169:pe:Peru,170:ph:Philippines,171:pn:Pitcairn Island,172:pl:Poland,173:pt:Portugal,174:pr:Puerto Rico,175:qa:Qatar,176:re:Reunion,177:ro:Romania,178:ru:​,179:rw:Rwanda,180:sh:St. Helena,181:kn:St. Kitts and Nevis,182:lc:St. Lucia,183:pm:St. Pierre and Miquelon,184:vc:St. Vincent and the Grenadines,185:ws:Samoa,186:sm:San Marino,187:st:Sao Tome and Principe,188:sa:Saudi Arabia,189:sn:Senegal,190:rs:Serbia,191:sc:Seychelles,192:sl:Sierra Leone,193:sg:Singapore,194:sk:Slovakia,195:si:Slovenia,196:sb:Solomon Islands,197:so:Somalia,198:za:South Africa,199:gs:South Georgia and the South Sandwich Islands,200:es:Spain,201:lk:Sri Lanka,202:sd:Sudan,203:sr:Suriname,204:sj:Svalbard & Jan Mayen Islands,205:sz:Eswatini,206:se:Sweden,207:ch:Switzerland,208:sy:Syria,209:tw:Chinese Taipei,210:tj:Tajikistan,211:tz:Tanzania,212:th:Thailand,213:tl:Timor-Leste,214:tg:Togo,215:tk:Tokelau,216:to:Tonga,217:tt:Trinidad and Tobago,218:tn:Tunisia,219:tr:Turkey,220:tm:Turkmenistan,221:tc:Turks and Caicos Islands,222:tv:Tuvalu,223:vi:US Virgin Islands,224:ug:Uganda,225:ua:Ukraine,226:ae:United Arab Emirates,227:gb:United Kingdom,228:um:United States Minor Outlying Islands,229:us:USA,230:uy:Uruguay,231:uz:Uzbekistan,232:vu:Vanuatu,233:ve:Venezuela,234:vn:Vietnam,235:wf:Wallis and Futuna Islands,236:eh:Western Sahara,237:ye:Yemen,238:zm:Zambia,239:zw:Zimbabwe,240:me:Montenegro,241:gb-eng:England,242:gb-nir:Northern Ireland,243:gb-sct:Scotland,244:gb-wls:Wales,267:ax:Aland Islands,269:bl:Saint Barthelemy,271:gg:Guernsey,273:im:Isle of Man,275:je:Jersey,277:mf:Saint Martin,279:bq:Bonaire Saint Eustatius and Saba,281:cw:Curacao,283:sx:Sint Maarten,285:ss:South Sudan,286:xk:Kosovo'.split(',').forEach((t) => { const [i, c, n] = t.split(':'); REGION[i] = [c, n]; });
  const flagUrl = (e) => (e && REGION[e.region] ? `https://flagcdn.com/${REGION[e.region][0]}.svg` : '');
  const flagPng = (code) => `https://flagcdn.com/w1280/${code}.png`;
  const FLAGW = Array.from({ length: 24 }, (_, i) => `<b style="--i:${i}"></b>`).join('');
  // v3.71: the Egypt banner photo waves too: each strip shows its slice of the photo at "cover" size (measured, so it fits any width)
  function egyWave() { try { R.querySelectorAll('.pph.egy .pflag.c.wv').forEach((w) => { const p = w.parentElement, W = p.clientWidth, H = p.clientHeight; if (!W || !H) return; const a = 1000 / 198; let bw = W, bh = W / a; if (bh < H) { bh = H; bw = H * a; }
    const k = Math.round(W) + 'x' + Math.round(H); if (w.dataset.k === k) return; w.dataset.k = k; w.style.setProperty('--bw', bw + 'px'); w.style.setProperty('--bh', bh + 'px'); w.style.setProperty('--bx0', (bw - W) / 2 + 'px'); w.style.setProperty('--by0', (bh - H) / 2 + 'px'); w.style.setProperty('--sw', W / 24 + 'px'); w.classList.add('ok'); }); } catch (e) {} }
  let EGYT = 0; const egyKick = () => { cancelAnimationFrame(EGYT); EGYT = requestAnimationFrame(egyWave); };
  try { new MutationObserver(egyKick).observe(R, { childList: true, subtree: true }); window.addEventListener('resize', () => { R.querySelectorAll('.pph.egy .pflag.c.wv').forEach((w) => delete w.dataset.k); egyKick(); }); } catch (e) {}
  const flagSt = (e) => { const u = flagUrl(e); return u ? ` style="--flag:url('${u}');--flagb:url('${flagPng(REGION[e.region][0])}')"` : ''; };
  const flagOfRegion = (id) => (REGION[id] ? `https://flagcdn.com/${REGION[id][0]}.svg` : '');
  const country = (e) => (e && REGION[e.region] ? REGION[e.region][1] : '');
  // v3.28: deadline countdown text, e.g. 5d 12h 03m 09s
  const cdTxt = (ms) => { const s = Math.max(0, Math.floor(ms / 1000)), d = Math.floor(s / 86400), h = Math.floor(s % 86400 / 3600), m = Math.floor(s % 3600 / 60), x = s % 60, p = (n) => String(n).padStart(2, '0'); return `${d ? d + 'd ' : ''}${d || h ? p(h) + 'h ' : ''}${p(m)}m ${p(x)}s`; };
  const CHIP = { bboost: 'Bench Boost', '3xc': 'Triple Captain', freehit: 'Free Hit', wildcard: 'Wildcard', manager: 'Assistant Manager' };

  let meId = null;
  try { const me = await J('/api/me/'); meId = me && me.player ? me.player.entry : null; } catch (e) {}
  let saved = null;
  try { saved = localStorage.getItem('fplAnalystId'); } catch (e) {}
  // v3.12: my team (the default and Home team) and saved friends' team IDs
  const ID_ME = 'fplAnalystMyId', ID_FR = 'fplAnalystFriends';
  let MYID = null, MYNAME = '', FRIENDS = [];
  try { MYID = +localStorage.getItem(ID_ME) || null; MYNAME = localStorage.getItem(ID_ME + 'Name') || ''; FRIENDS = JSON.parse(localStorage.getItem(ID_FR) || '[]').filter((f) => f && +f.id); } catch (e) {}
  if (!MYID && meId) MYID = +meId;
  const saveIds = () => { try { if (MYID) localStorage.setItem(ID_ME, String(MYID)); localStorage.setItem(ID_ME + 'Name', MYNAME || ''); localStorage.setItem(ID_FR, JSON.stringify(FRIENDS.slice(0, 30))); } catch (e) {} };
  function androidSync(A) {
    if (!hasAndroid() || !BS) return;
    const nx = BS.events.filter((e) => !e.finished && new Date(e.deadline_time) > Date.now()).slice(0, 3);
    const cur = BS.events.find((e) => e.is_current);
    const gwK = (g) => FX.filter((f) => f.event === g && f.kickoff_time).map((f) => f.kickoff_time);
    const sq = PLAN && PLAN.A && PLAN.A.id === MYID ? PLAN.A.sq : A.id === MYID ? A.sq : null;
    const flagged = sq ? sq.filter((s) => s.e.status !== 'a').map((s) => s.e.web_name) : [];
    const capE = PLAN && PLAN.cap && PLAN.cap.e;
    const summ = [flagged.length ? `${flagged.length} flagged: ${flagged.slice(0, 3).join(', ')}` : 'No injury flags', capE ? `captain ${capE.web_name}` : '', PLAN && PLAN.ft0 != null && A.id === MYID ? `${PLAN.ft0} free transfer${PLAN.ft0 === 1 ? '' : 's'}` : ''].filter(Boolean).join(' · ');
    const els = {}; BS.elements.forEach((e) => (els[e.id] = [e.web_name, e.element_type]));
    const teams = {}; BS.teams.forEach((x) => (teams[x.id] = x.short_name));
    const elT = {}; BS.elements.forEach((e) => (elT[e.id] = e.team));
    const fold = (x) => String(x || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase().replace(/&/g, 'and').replace(/\b(fc|afc)\b/g, '').replace(/[^a-z]/g, '');
    const tkeys = {}; BS.teams.forEach((t) => { tkeys[fold(t.name)] = t.id; tkeys[fold(t.short_name)] = t.id; }); Object.entries(ODDS_ALIAS).forEach(([k, v]) => { const id = oddsTeam(k); if (id) tkeys[fold(k)] = id; });
    const mySq = (sq || A.sq || []).map((x) => [x.e.id, x.e.team, x.e.web_name, x.e.first_name + ' ' + x.e.second_name, x.e.second_name, x.e.element_type]);
    try { FPLAndroid.setSchedule(JSON.stringify({ tkeys, mine: mySq, entry: MYID || A.id, gw: cur ? cur.id : 0, deadlines: nx.map((e) => ({ gw: e.id, at: e.deadline_time })), summary: summ, kick: cur ? gwK(cur.id) : [], kickNext: nx[0] ? gwK(nx[0].id) : [], nextGw: nx[0] ? nx[0].id : 0, liveNow: !!(A.live && A.live.live > 0), els, teams, elT })); } catch (e) {}
  }
  function idsLoaded(A) {
    const nm = A.entry.name, mgr = `${A.entry.player_first_name || ''} ${A.entry.player_last_name || ''}`.trim();
    if (!MYID) MYID = A.id;
    if (A.id === MYID) MYNAME = nm;
    FRIENDS.forEach((f) => { if (+f.id === A.id) { f.name = nm; f.mgr = mgr; } });
    saveIds(); paintIdMenu();
  }
  function paintIdMenu() {
    const m = $('#idmenu'); if (!m) return;
    const cur = LASTA ? LASTA.id : null, curNm = LASTA ? LASTA.entry.name : '';
    const row = (id, nm, sub, me) => `<div class="idr${id === cur ? ' on' : ''}"><button type="button" role="menuitem" class="idgo" data-idgo="${id}">${me ? '<i class="idme">★</i>' : `<i class="idav">${esc((nm || '?').trim().charAt(0).toUpperCase())}</i>`}<span><b>${esc(nm || 'Team ' + id)}</b><small>${sub ? esc(sub) + ' · ' : ''}ID ${id}</small></span></button>${me ? '' : `<button type="button" class="iddel" data-iddel="${id}" aria-label="Remove ${esc(nm || id)}" title="Remove">×</button>`}</div>`;
    const isFr = cur && FRIENDS.some((f) => +f.id === cur);
    m.innerHTML = `<div class="idh">My team</div>${MYID ? row(MYID, MYNAME, 'Home team', true) : '<p class="idn">Analyse your own team ID first: it becomes your Home team.</p>'}
<div class="idh">Friends &amp; rivals <span>${FRIENDS.length}</span></div>${FRIENDS.length ? FRIENDS.map((f) => row(+f.id, f.name, f.mgr, false)).join('') : '<p class="idn">No saved IDs yet. Open a friend\'s team, then save it here.</p>'}
${cur && cur !== MYID ? `<div class="idact">${isFr ? '' : `<button type="button" class="mbtn" data-idsave="${cur}">＋ Save ${esc(curNm)}</button>`}<button type="button" class="mbtn ghost" data-idmine="${cur}">★ Make this my team</button></div>` : ''}`;
  }
  $('#idb').onclick = (ev) => { ev.stopPropagation(); const m = $('#idmenu'); paintIdMenu(); m.hidden = !m.hidden; $('#idb').setAttribute('aria-expanded', !m.hidden); };
  $('#idmenu').onclick = (ev) => {
    ev.stopPropagation(); const t = ev.target.closest('button'); if (!t) return;
    if (t.dataset.idgo) { $('#idmenu').hidden = true; const id = +t.dataset.idgo; if (!LASTA || LASTA.id !== id) openTeam(id); else showView('home'); return; }
    if (t.dataset.iddel) { FRIENDS = FRIENDS.filter((f) => +f.id !== +t.dataset.iddel); saveIds(); paintIdMenu(); return; }
    if (t.dataset.idsave && LASTA) { FRIENDS.unshift({ id: LASTA.id, name: LASTA.entry.name, mgr: `${LASTA.entry.player_first_name || ''} ${LASTA.entry.player_last_name || ''}`.trim() }); saveIds(); paintIdMenu(); toast('Saved', `${LASTA.entry.name} is in your saved teams.`, 'good'); return; }
    if (t.dataset.idmine && LASTA) { const old = MYID; MYID = LASTA.id; MYNAME = LASTA.entry.name; FRIENDS = FRIENDS.filter((f) => +f.id !== MYID); if (old && old !== MYID && !FRIENDS.some((f) => +f.id === old)) FRIENDS.unshift({ id: old, name: '', mgr: '' }); saveIds(); paintIdMenu(); toast('Home team set', `${MYNAME} opens by default and on Home.`, 'good'); run(MYID); }
  };
  R.addEventListener('click', (ev) => { const m = $('#idmenu'); if (m && !m.hidden && !ev.composedPath().some((x) => x && x.id === 'idmenu')) { m.hidden = true; $('#idb').setAttribute('aria-expanded', 'false'); } });
  $('#tid').value = MYID || saved || meId || '';

  let BS = null, FX = null, NEWS = null;

  // External news: public RSS feeds read through the rss2json reader (the FPL page cannot read other sites directly)
  const GN = (q) => 'https://news.google.com/rss/search?q=' + encodeURIComponent(q) + '&hl=en-GB&gl=GB&ceid=GB:en';
  // kind: news = outlets, leak = predicted line-ups / leaked team news, social = journalists & community
  const feedsFor = (gw) => [
    ['news', 'BBC Sport', 'https://feeds.bbci.co.uk/sport/football/premier-league/rss.xml'],
    ['news', 'Sky Sports', 'https://www.skysports.com/rss/12040'],
    ['news', 'The Guardian', 'https://www.theguardian.com/football/premierleague/rss'],
    ['news', 'The Independent', 'https://www.independent.co.uk/sport/football/premier-league/rss'],
    ['news', 'Daily Mirror', 'https://www.mirror.co.uk/sport/football/rss.xml'],
    ['news', 'talkSPORT', 'https://talksport.com/football/feed/'],
    ['news', 'Football365', 'https://www.football365.com/feed'],
    ['leak', 'Fantasy Football Scout', 'https://www.fantasyfootballscout.co.uk/feed/'],
    ['leak', 'Injury news', GN('Premier League injury news "expected to return" OR "out for" when:2d')],
    ['news', 'Team news', GN('Premier League team news injury when:2d')],
    ['news', 'Press conferences', GN('Premier League press conference injury update when:2d')],
    ['news', 'FPL news', GN('Fantasy Premier League team news when:2d')],
    ['leak', 'Gameweek leaks', GN(`FPL Gameweek ${gw} team news leaks when:2d`)],
    ['leak', 'Predicted line-ups', GN('Premier League predicted lineups when:2d')],
    ['leak', 'Leaked line-ups', GN('"leaked" lineup OR "team news leak" Premier League when:2d')],
    ['news', 'Breaking incidents', GN('Premier League player (hospital OR illness OR accident OR "personal reasons" OR "family reasons" OR "compassionate leave" OR collapsed OR arrested) when:2d')],
    ['news', 'Late fitness tests', GN('Premier League "fitness test" OR "late fitness" OR "injured in training" OR "limped off" OR "withdrawn from" squad when:2d')],
    ['leak', 'Training reports', GN('Premier League "missed training" OR "back in training" when:2d')],
    ['social', 'Fabrizio Romano', GN('"Fabrizio Romano" Premier League when:2d')],
    ['social', 'David Ornstein', GN('"David Ornstein" Premier League when:2d')],
    ['excl', 'Exclusives', GN('Premier League exclusive when:2d')],
    ['excl', 'Transfer exclusives', GN('exclusive Premier League transfer OR injury OR "team news" when:2d')],
    ['excl', 'The Athletic', GN('site:nytimes.com/athletic Premier League when:2d')],
    ['social', 'Reddit r/FantasyPL', 'https://www.reddit.com/r/FantasyPL/.rss'],
    ['social', 'Reddit r/PremierLeague', 'https://www.reddit.com/r/PremierLeague/.rss'],
  ];
  // Picture that the feed itself supplies for the story (thumbnail, enclosure, or the first image in its summary)
  const newsImg = (it) => { const u = it.thumbnail || (it.enclosure && (it.enclosure.thumbnail || (/image/.test(it.enclosure.type || '') && it.enclosure.link))) || ((String(it.description || it.content || '').match(/<img[^>]+src=["']([^"']+)/i) || [])[1]); return u && /^https:\/\//.test(u) ? u : ''; };
  const CLUBALIAS = { ARS: ['arsenal', 'gunners'], AVL: ['aston villa'], BOU: ['bournemouth'], BRE: ['brentford'], BHA: ['brighton'], BUR: ['burnley'], CHE: ['chelsea'], CRY: ['crystal palace'], EVE: ['everton'], FUL: ['fulham'], LEE: ['leeds'], LIV: ['liverpool'], MCI: ['manchester city', 'man city'], MUN: ['manchester united', 'man utd', 'man united'], NEW: ['newcastle'], NFO: ['nottingham forest', "nott'm forest"], SUN: ['sunderland'], TOT: ['tottenham', 'spurs'], WHU: ['west ham'], WOL: ['wolves', 'wolverhampton'] };
  const clubIn = (title) => { const t = String(title || '').toLowerCase(); if (!BS) return null; const hit = BS.teams.find((x) => [x.name.toLowerCase(), ...(CLUBALIAS[x.short_name] || [])].some((n) => n.length > 3 && new RegExp('\\b' + n.replace(/[.*+?^${}()|[\]\\']/g, '.') + '\\b').test(t))); return hit ? hit.id : null; };
  const PITCHART = '<svg viewBox="0 0 160 100" preserveAspectRatio="xMidYMid slice" aria-hidden="true"><rect width="160" height="100" fill="#1d7f48"/><g fill="#1a7442"><rect x="0" width="20" height="100"/><rect x="40" width="20" height="100"/><rect x="80" width="20" height="100"/><rect x="120" width="20" height="100"/></g><g fill="none" stroke="#fff" stroke-opacity=".55" stroke-width="1.2"><rect x="6" y="6" width="148" height="88"/><path d="M80 6v88"/><circle cx="80" cy="50" r="14"/><rect x="6" y="28" width="22" height="44"/><rect x="132" y="28" width="22" height="44"/></g><circle cx="80" cy="50" r="2" fill="#fff"/></svg>';
  function newsPic(it, who) {
    const cid = who ? who.team : clubIn(it.title); const t = cid && BS.teams.find((x) => x.id === cid);
    const k = t ? JST[t.short_name] || ['#33507e', '#1a2a45'] : null;
    const art = t ? `<span class="nart" style="background:radial-gradient(circle at 30% 20%,${k[0]},${k[3] && k[3] !== k[0] ? k[3] : k[1]} 140%)">${crest(cid, true)}</span>` : `<span class="nart gen">${PITCHART}<b>${esc((it.src || 'News').split(/[\s:]/)[0])}</b></span>`;
    return `${art}${it.img ? `<img class="nimg" src="${esc(it.img)}" alt="" loading="lazy" referrerpolicy="no-referrer">` : ''}`;
  }
  const NEWS_KEY = 'fplAnalystNews';
  function saveNewsCache(N) { try { localStorage.setItem(NEWS_KEY, JSON.stringify({ at: N.at, ok: N.ok, total: N.total, okBy: N.okBy, feeds: N.feeds, items: N.items.slice(0, 220) })); } catch (e) {} }
  function loadNewsCache() { try { const N = JSON.parse(localStorage.getItem(NEWS_KEY) || 'null'); if (!N || Date.now() - N.at > 6 * 36e5) return null; N.items.forEach((i) => (i.date = new Date(i.date))); N.items = N.items.filter((i) => Date.now() - i.date < 2 * 864e5); return N; } catch (e) { return null; } }
  // ======================= 4. news: on Android the app reads feeds itself; elsewhere through rss2json =======================
  const NAT = {}; let natN = 0;
  window.__fplNat = (id, ok, txt) => { const f = NAT[id]; if (!f) return; delete NAT[id]; ok ? f[0](txt) : f[1](new Error(txt || 'feed error')); };
  const hasNative = () => { try { return !!(window.FPLAndroid && FPLAndroid.fetchText); } catch (e) { return false; } };
  const nativeText = (url) => new Promise((res, rej) => { const id = 'n' + ++natN; NAT[id] = [res, rej]; try { FPLAndroid.fetchText(id, url); } catch (e) { delete NAT[id]; rej(e); } });
  const xt = (el, sel) => { const x = el.querySelector(sel); return x ? x.textContent.trim() : ''; };
  function parseFeed(xml) {
    const doc = new DOMParser().parseFromString(xml, 'text/xml');
    return [...doc.querySelectorAll('item, entry')].map((el) => {
      const lk = el.querySelector('link'); const link = lk ? lk.getAttribute('href') || lk.textContent.trim() : '';
      const raw = xt(el, 'pubDate') || xt(el, 'published') || xt(el, 'updated') || xt(el, 'date'); const d = new Date(raw);
      let thumb = ''; el.querySelectorAll('*').forEach((c) => { if (thumb) return; const n = c.localName; if ((n === 'thumbnail' || n === 'content') && c.getAttribute('url') && /image|jpg|jpeg|png|webp/i.test((c.getAttribute('type') || '') + c.getAttribute('url'))) thumb = c.getAttribute('url'); });
      const enc = el.querySelector('enclosure');
      return { title: xt(el, 'title'), link, pubDate: isNaN(d) ? '' : d.toISOString().slice(0, 19).replace('T', ' '), description: xt(el, 'description') || xt(el, 'summary') || xt(el, 'content'), thumbnail: thumb, enclosure: enc ? { link: enc.getAttribute('url'), type: enc.getAttribute('type') || '' } : {} };
    });
  }
  const viaRss2json = (url) => withTimeout(fetch('https://api.rss2json.com/v1/api.json?rss_url=' + encodeURIComponent(url)).then((r) => r.json()), 10000).then((d) => { if (d.status && d.status !== 'ok') throw new Error(d.message || 'feed error'); return d.items || []; });
  // v3.18: the Chrome extension reads feeds in its background (no CORS limit); the iPhone version uses the Userscripts
  // app's own request function; everything else falls back to rss2json
  const extId = () => { try { return typeof chrome !== 'undefined' && chrome.runtime && chrome.runtime.id && chrome.runtime.id !== 'fpl-analyst-android' ? chrome.runtime.id : null; } catch (e) { return null; } };
  const extText = (url) => new Promise((res, rej) => { try { chrome.runtime.sendMessage({ type: 'fpl-fetch', url }, (r) => { const er = chrome.runtime.lastError; if (er || !r || !r.ok) rej(new Error((er && er.message) || (r && r.text) || 'feed error')); else res(r.text); }); } catch (e) { rej(e); } });
  const gmFn = () => { try { if (typeof GM !== 'undefined' && GM && GM.xmlHttpRequest) return GM.xmlHttpRequest; if (typeof GM_xmlhttpRequest === 'function') return GM_xmlhttpRequest; } catch (e) {} return null; };
  const gmText = (url) => new Promise((res, rej) => { try { gmFn()({ method: 'GET', url, timeout: 12000, onload: (r) => (r.status >= 200 && r.status < 300 ? res(r.responseText) : rej(new Error('HTTP ' + r.status))), onerror: () => rej(new Error('feed error')), ontimeout: () => rej(new Error('timeout')) }); } catch (e) { rej(e); } });
  const directText = () => (hasNative() ? nativeText : extId() ? extText : gmFn() ? gmText : null);
  setTimeout(() => { try { checkUpdate(false); } catch (e) {} }, 3000);
  const readFeed = (url) => { const d = directText(); return d ? withTimeout(d(url), 13000).then((x) => { const its = parseFeed(x); if (!its.length) throw new Error('empty'); return its; }).catch(() => viaRss2json(url)) : viaRss2json(url); };
  const withTimeout = (p, ms) => Promise.race([p, new Promise((_, rej) => setTimeout(() => rej(new Error('timeout')), ms))]);
  async function fetchNews(gw) {
    const FEEDS = feedsFor(gw);
    const res = await Promise.allSettled(FEEDS.map(([kind, src, url]) => readFeed(url).then((its) => { return its.map((it) => ({ kind, src, title: it.title || '', link: it.link || '', img: newsImg(it), date: new Date((it.pubDate || '').replace(' ', 'T') + 'Z'), text: ((it.title || '') + ' ' + (it.description || it.content || '')).replace(/<[^>]+>/g, ' ').replace(/&[a-z#0-9]+;/gi, ' ') })); })));
    const items = []; const seen = new Set(); const okBy = {};
    res.forEach((r, i) => { const [kind, src] = FEEDS[i]; okBy[src] = r.status === 'fulfilled'; if (r.status === 'fulfilled') r.value.forEach((it) => { const k = it.title.toLowerCase().slice(0, 70); if (!seen.has(k) && it.title) { seen.add(k); items.push(it); } }); });
    // v3.12: only stories from the last 48 hours that name a Premier League club or player; exclusives are flagged
    const cutoff = Date.now() - 2 * 864e5;
    const fresh = items.filter((i) => !isNaN(i.date) && i.date.getTime() > cutoff && i.date.getTime() < Date.now() + 36e5 && plNews(i));
    fresh.forEach((i) => { i.excl = i.kind === 'excl' || /\bexclusive\b|here we go|understands|sources say/i.test(i.title) || /Romano|Ornstein/.test(i.src); if (i.kind === 'excl') i.kind = 'news'; });
    return { ok: Object.values(okBy).filter(Boolean).length, total: FEEDS.length, okBy, feeds: FEEDS, dropped: items.length - fresh.length, items: fresh.sort((a, b) => (b.date || 0) - (a.date || 0)) };
  }
  // ======================= v3.54: bookmaker odds (The Odds API, your own key) =======================
  // Prices for match result and over/under 2.5 goals are turned into probabilities (bookmaker margin removed,
  // averaged over bookmakers), then into each team's expected goals with a Poisson fit. The model then blends
  // them 50/50 with its own expected goals for those matches. The key is stored only on this device.
  const ODDS_KEY = 'elevnOddsKey', ODDS_CACHE = 'elevnOddsCache', ODDS_W = 0.5;
  let ODDS = null;
  const oddsKey = () => { try { return (localStorage.getItem(ODDS_KEY) || '').trim(); } catch (e) { return ''; } };
  const ODDS_ALIAS = { 'brighton and hove albion': 'brighton', 'wolverhampton wanderers': 'wolves', 'tottenham hotspur': 'spurs', 'nottingham forest': "nott'm forest", 'manchester city': 'man city', 'manchester united': 'man utd', 'afc bournemouth': 'bournemouth', 'west ham united': 'west ham', 'newcastle united': 'newcastle', 'leeds united': 'leeds', 'leicester city': 'leicester', 'ipswich town': 'ipswich', 'hull city': 'hull', 'coventry city': 'coventry', 'sheffield united': 'sheffield utd', 'luton town': 'luton', 'norwich city': 'norwich', 'stoke city': 'stoke', 'cardiff city': 'cardiff', 'swansea city': 'swansea', 'west bromwich albion': 'west brom', 'queens park rangers': 'qpr' };
  const oddsTeam = (name) => { if (!BS) return null; const n = String(name || '').toLowerCase().trim(); const a = ODDS_ALIAS[n] || n; const strip = (x) => x.replace(/\b(fc|afc)\b/g, '').replace(/[^a-z']/g, ''); const t = BS.teams.find((x) => x.name.toLowerCase() === a || strip(x.name.toLowerCase()) === strip(a) || strip(x.name.toLowerCase()) === strip(n)); return t ? t.id : null; };
  const poisP = (l, k) => { let p = Math.exp(-l); for (let i = 1; i <= k; i++) p *= l / i; return p; };
  function oddsProbs(lh, la) { let H = 0, D = 0, A = 0, O = 0; const ph = [], pa = []; for (let k = 0; k <= 10; k++) { ph.push(poisP(lh, k)); pa.push(poisP(la, k)); }
    for (let i = 0; i <= 10; i++) for (let j = 0; j <= 10; j++) { const p = ph[i] * pa[j]; if (i > j) H += p; else if (i === j) D += p; else A += p; if (i + j >= 3) O += p; } return { H, D, A, O }; }
  // expected goals for both teams that best reproduce the market's probabilities
  function oddsFit(m) { let best = null; for (let lh = 0.2; lh <= 4.0001; lh += 0.05) for (let la = 0.2; la <= 4.0001; la += 0.05) { const q = oddsProbs(lh, la); const err = (q.H - m.H) ** 2 + (q.D - m.D) ** 2 + (q.A - m.A) ** 2 + (m.O != null ? (q.O - m.O) ** 2 : 0); if (!best || err < best.err) best = { lh, la, err }; } return best; }
  function oddsParse(events) {
    const out = [];
    (events || []).forEach((ev) => {
      const h = oddsTeam(ev.home_team), a = oddsTeam(ev.away_team); if (!h || !a) return;
      const r1 = [], r2 = [];
      (ev.bookmakers || []).forEach((bk) => (bk.markets || []).forEach((mk) => {
        if (mk.key === 'h2h') { const g = (nm) => { const o = (mk.outcomes || []).find((x) => x.name === nm); return o && o.price > 1 ? 1 / o.price : 0; }; const H = g(ev.home_team), A = g(ev.away_team), D = g('Draw'), s = H + A + D; if (H && A && D) r1.push({ H: H / s, D: D / s, A: A / s }); }
        if (mk.key === 'totals') { const ov = (mk.outcomes || []).find((x) => x.name === 'Over' && +x.point === 2.5), un = (mk.outcomes || []).find((x) => x.name === 'Under' && +x.point === 2.5); if (ov && un && ov.price > 1 && un.price > 1) { const o = 1 / ov.price, u = 1 / un.price; r2.push(o / (o + u)); } }
      }));
      if (!r1.length) return;
      const avg = (k) => r1.reduce((x, r) => x + r[k], 0) / r1.length;
      const m = { H: avg('H'), D: avg('D'), A: avg('A'), O: r2.length ? r2.reduce((x, v) => x + v, 0) / r2.length : null };
      const f = oddsFit(m);
      out.push({ h, a, t: Date.parse(ev.commence_time), pH: m.H, pD: m.D, pA: m.A, pO: m.O, lh: Math.round(f.lh * 100) / 100, la: Math.round(f.la * 100) / 100, books: r1.length });
    });
    return out;
  }
  function oddsLoadCache() { try { const c = JSON.parse(localStorage.getItem(ODDS_CACHE) || 'null'); return c && c.events ? c : null; } catch (e) { return null; } }
  // v3.61: free odds with no key (one bookmaker, from the live score feed), loaded automatically on every device
  const ODDS_FREE = 'elevnOddsFree';
  const oddsFreeOn = () => { try { return localStorage.getItem(ODDS_FREE) !== 'off'; } catch (e) { return true; } };
  const amDec = (x) => { const v = +String(x == null ? '' : x).replace('+', ''); return !v ? 0 : v > 0 ? 1 + v / 100 : 1 + 100 / -v; };
  async function freeOddsEvents() {
    const nx = BS && (BS.events.find((e) => e.is_next) || BS.events.find((e) => e.is_current)); if (!nx) return [];
    const days = [...new Set(FX.filter((f) => f.event === nx.id && f.kickoff_time && !f.started).map((f) => f.kickoff_time.slice(0, 10).replace(/-/g, '')))];
    const out = [];
    for (const day of days) {
      const d = await fastGet('https://site.api.espn.com/apis/site/v2/sports/soccer/eng.1/scoreboard?dates=' + day);
      (d.events || []).forEach((ev) => { const c = (ev.competitions || [])[0]; const o = c && (c.odds || [])[0]; if (!o || !o.moneyline) return;
        const nm = (x) => String(x || '').replace(/&/g, 'and'); const H = nm((c.competitors.find((x) => x.homeAway === 'home') || {}).team.displayName), A = nm((c.competitors.find((x) => x.homeAway === 'away') || {}).team.displayName);
        const cl = (x) => (x && (x.close || x.open) || {}).odds; const ml = o.moneyline;
        const mk = [{ key: 'h2h', outcomes: [{ name: H, price: amDec(cl(ml.home)) }, { name: A, price: amDec(cl(ml.away)) }, { name: 'Draw', price: amDec(cl(ml.draw)) }] }];
        if (o.total && +o.overUnder === 2.5) mk.push({ key: 'totals', outcomes: [{ name: 'Over', price: amDec(cl(o.total.over)), point: 2.5 }, { name: 'Under', price: amDec(cl(o.total.under)), point: 2.5 }] });
        out.push({ home_team: H, away_team: A, commence_time: ev.date, bookmakers: [{ key: 'free', markets: mk }] }); });
    }
    return out;
  }
  async function fetchOdds(force) {
    const key = oddsKey(); const c = oddsLoadCache();
    if (!key) {
      if (!oddsFreeOn()) { ODDS = null; return null; }
      ODDS = c && c.free ? c : null;
      if (!force && ODDS && ODDS.ok && Date.now() - ODDS.at < 3 * 36e5) return ODDS;
      try { const ev = await withTimeout(freeOddsEvents(), 12000); ODDS = { ok: true, free: true, at: Date.now(), left: null, events: oddsParse(ev) }; }
      catch (e) { ODDS = Object.assign({}, ODDS || { events: [] }, { ok: !!(ODDS && ODDS.ok), free: true, err: 'No answer from the free odds feed', errAt: Date.now() }); }
      try { localStorage.setItem(ODDS_CACHE, JSON.stringify(ODDS)); } catch (e) {}
      return ODDS;
    }
    if (c && c.free) force = true; // a key was just added: replace the free odds
    ODDS = c && !c.free ? c : null;
    const nx = BS && BS.events.find((e) => e.is_next); const near = nx && Date.parse(nx.deadline_time) - Date.now() < 864e5;
    if (!force && c && c.ok && Date.now() - c.at < (near ? 3 : 12) * 36e5) return c; // about 2-4 requests a day
    const url = 'https://api.the-odds-api.com/v4/sports/soccer_epl/odds/?regions=uk&markets=h2h,totals&oddsFormat=decimal&apiKey=' + encodeURIComponent(key);
    try {
      let txt, left = null;
      const d = directText();
      if (d) txt = await withTimeout(d(url), 12000);
      else { const r = await withTimeout(fetch(url, { credentials: 'omit' }), 12000); left = r.headers.get('x-requests-remaining'); txt = await r.text(); if (!r.ok) throw new Error(r.status === 401 ? 'The key was not accepted' : r.status === 429 ? 'Monthly request limit reached' : 'HTTP ' + r.status); }
      const j = JSON.parse(txt); if (!Array.isArray(j)) throw new Error((j && j.message) || 'Unexpected reply');
      ODDS = { ok: true, at: Date.now(), left, events: oddsParse(j) };
    } catch (e) { let msg = String(e && e.message || e).replace(key, '…'); if (/401/.test(msg)) msg = 'The key was not accepted'; else if (/429/.test(msg)) msg = 'Monthly request limit reached'; else if (/timeout/i.test(msg)) msg = 'No answer from the odds service'; ODDS = Object.assign({}, c || { events: [] }, { ok: !!(c && c.ok), err: msg, errAt: Date.now() }); }
    try { localStorage.setItem(ODDS_CACHE, JSON.stringify(ODDS)); } catch (e) {}
    return ODDS;
  }
  // the market line for one FPL fixture (same teams, kick-off within 36 hours)
  const oddsFor = (h, a, ko) => { if (!ODDS || !ODDS.events) return null; const t = ko ? Date.parse(ko) : 0; return ODDS.events.find((x) => x.h === h && x.a === a && (!t || Math.abs(x.t - t) < 36 * 36e5)) || null; };

  // v3.51: News keeps only stories about Premier League players.
  // A story must name a current PL player (full name, or a distinctive surname written with a capital letter) in its title,
  // or name his club in the title and him in the summary. Women's football, youth teams, other leagues and other sports are dropped.
  // International football is kept only when it is about a player's fitness (injured, withdrawn, back to his club).
  const NOT_PL = /\b(women'?s|wsl|lionesses|girls|u-?1[6-9]s?|u-?2[0-3]s?|under-?(?:1[6-9]|2[0-3])s?|academy|youth|cricket|rugby|nfl|nba|nhl|mlb|formula (?:one|1)|\bf1\b|tennis|golf|boxing|ufc|darts|snooker|cycling|athletics|quarterback|touchdown|super bowl|nfl|nba|wnba|mlb|nhl|grand slam|wimbledon|ryder cup|olympic|la liga|laliga|serie a|bundesliga|ligue 1|eredivisie|primeira liga|mls|saudi pro league|scottish premiership|spfl|championship|league one|league two|national league|efl trophy)\b/i;
  const INTL = /\b(nations league|world cup|qualif\w*|international (?:break|duty|friendly)|friendl(?:y|ies)|euro 20\d\d|afcon|africa cup|copa am[eé]rica|national team|(?:england|scotland|wales|ireland|france|spain|germany|brazil|argentina|portugal|norway|netherlands|belgium|italy|egypt|ghana|nigeria|senegal|morocco|usa|japan|south korea|denmark|sweden|croatia|uruguay|colombia) (?:squad|camp|boss|manager|coach|win|beat|lose|draw|through))\b/i;
  const FIT = /\b(injur(?!y[- ]time)\w*|withdr[ae]w\w*|pulled out|ruled out|sent (?:back|home)|returns? to (?:his )?club|back to (?:his )?club|scan|knock|hamstring|groin|knee|ankle|calf|thigh|fitness|limped|stretchered)\b/i;
  const COMMONW = new Set(['King', 'White', 'Young', 'Stones', 'Gray', 'Hall', 'Long', 'Little', 'Cash', 'Wood', 'Baker', 'Mount', 'Bell', 'Brown', 'Green', 'Rice', 'Ward', 'Day', 'James', 'Thomas', 'Mason', 'Henry', 'Rose', 'Morgan', 'Gordon', 'Scott', 'Taylor', 'Lewis', 'Robinson', 'Wilson', 'Johnson', 'Kelly', 'Murphy', 'Walker', 'Moore', 'Smith', 'Jones', 'Williams', 'Roberts', 'Turner', 'Hill', 'Burn', 'Neto', 'Pedro', 'Bruno', 'Gabriel', 'Joelinton', 'Charles', 'Richards', 'Phillips', 'Francis', 'Owen', 'George', 'Edwards', 'Harrison', 'Andrews', 'Jackson', 'Adams', 'Daniel', 'Patrick', 'Arthur', 'Max', 'Victor', 'Lucas', 'Mateus', 'Martin', 'Ryan', 'Douglas', 'Simon', 'Allan']);
  let PLM = null;
  function plPlayers() {
    if (PLM && PLM.bs === BS) return PLM;
    const reEsc = (x) => x.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'); const nf = (x) => String(x || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '');
    const pool = BS.elements.filter((e) => e.minutes > 0 || e.status !== 'a' || +e.selected_by_percent >= 0.5);
    const full = new Set(), bare = new Map(), wc = {};
    BS.elements.forEach((e) => (wc[e.web_name] = (wc[e.web_name] || 0) + 1));
    pool.forEach((e) => { full.add(nf(`${e.first_name} ${e.second_name}`)); full.add(nf(`${e.first_name.split(' ')[0]} ${e.second_name.split(' ').pop()}`));
      const w = nf(e.web_name.replace(/^.*\./, '')); if (w.length >= 4 && wc[e.web_name] === 1 && !COMMONW.has(w)) bare.set(w, { team: e.team, star: +e.selected_by_percent >= 10 }); });
    const fr = new RegExp('(?:^|[^\\p{L}])(?:' + [...full].map(reEsc).join('|') + ')(?:$|[^\\p{L}])', 'iu');
    const br = new RegExp('(?:^|[^\\p{L}])(' + [...bare.keys()].map(reEsc).join('|') + ')(?=$|[^\\p{L}])', 'gu'); // case-sensitive: "Saka", not "saka"
    // v3.52: a surname on its own only counts when the story also names his club ("Stroud" in an NFL story is not Hull's Stroud)
    const clubRe = {}; BS.teams.forEach((t) => { const ns = [t.name, ...(CLUBALIAS[t.short_name] || []), ...(({ NFO: ['forest'], AVL: ['villa'], CRY: ['palace', 'eagles'], TOT: ['spurs', 'tottenham'], WHU: ['west ham', 'hammers'], NEW: ['newcastle', 'magpies', 'toon'], WOL: ['wolves'], MUN: ['man utd', 'man united', 'red devils'], MCI: ['man city', 'citizens'], LIV: ['reds', 'anfield'], ARS: ['gunners'], CHE: ['blues'], EVE: ['toffees'], BHA: ['seagulls'], BRE: ['bees'], BOU: ['cherries'], FUL: ['cottagers'], SUN: ['black cats'], LEE: ['leeds'], BUR: ['clarets'], HUL: ['hull', 'tigers'], COV: ['coventry', 'sky blues'], IPS: ['ipswich', 'tractor boys'], SOU: ['saints', 'southampton'] })[t.short_name] || [])].map((n) => n.toLowerCase()).filter((n) => n.length > 3); clubRe[t.id] = new RegExp('\\b(' + ns.map(reEsc).join('|') + ')\\b', 'i'); });
    // ...or uses football words, or he is one of the most-owned FPL players
    const FOOT = /\b(football|footballer|premier league|fpl|fantasy|striker|winger|midfielder|defender|full-?back|cent(?:re|er)-?back|goalkeeper|keeper|forward|squad|manager|boss|head coach|gaffer|hat-?trick|clean sheet|penalty|free-?kick|loan|transfer|signing|contract|gameweek|line-?ups?|team news|fixture|derby|dressing room)\b/i;
    PLM = { bs: BS, test: (x, ctx) => { x = nf(x); if (fr.test(x)) return true; const c = nf(ctx || x); const foot = FOOT.test(c); let m; br.lastIndex = 0; while ((m = br.exec(x))) { const b = bare.get(m[1]); if (b.star || foot || clubRe[b.team].test(c)) return true; } return false; } };
    return PLM;
  }
  function plNews(it) {
    if (!BS) return true;
    const t = String(it.title || ''), body = String(it.text || '');
    if (NOT_PL.test(t)) return false;
    const P = plPlayers();
    const ctx = t + ' ' + body.slice(0, 600);
    const named = P.test(t, ctx) || (clubIn(t) && P.test(body.slice(0, 400), ctx));
    if (!named) return false;
    if (INTL.test(t) && !FIT.test(t)) return false;
    return true;
  }
  // surnames of Premier League players who have played (or are flagged) this season, matched as whole words
  function plMatcher() {
    if (!BS) return () => false;
    const reEsc = (s) => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const nm = new Set(); BS.elements.filter((e) => e.minutes > 0 || e.status !== 'a' || +e.selected_by_percent >= 1).forEach((e) => { [e.web_name, e.second_name].forEach((n) => { n = String(n || '').trim(); if (n.length >= 4) nm.add(n.normalize('NFD').replace(/[\u0300-\u036f]/g, '')); }); });
    const re = new RegExp('\\b(' + [...nm].map(reEsc).join('|') + ')\\b', 'i');
    return (s) => re.test(String(s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, ''));
  }
  const NEG_RE = /\b(injur\w*|ruled out|out for|hamstring|groin|knee|ankle|calf|thigh|knock|(?:fitness|injury|major|serious|late|big) doubt|doubt (?:for|over|ahead of)|doubtful|is a doubt|surgery|suspen\w*|red card|withdr\w*|sidelined|setback|illness|ill\b|miss(es|ed|ing)? |limp\w*|scan|blow|absent|unavailable|fitness concern|benched|dropped from|rested|rotated|left out|on the bench|won'?t start|not in the squad|missed training)/i;
  // Sudden incidents that FPL often hasn't flagged yet
  const INCIDENT_RE = /\b(accident|crash\w*|hospital\w*|collaps\w*|ill(ness)?|sick\w*|virus|bug|personal reasons|family (reasons|matter|emergency)|bereave\w*|compassionate|arrest\w*|police|charged|fitness test|late (fitness )?test|injured in training|training (injury|knock)|knock in training|limped off|stretchered|withdr[ae]w\w*|pulled out|sent home|left the (camp|squad)|ruled out|scan|setback|surgery|operation|suspen\w*|ban(ned)?|red card)\b/i;
  // v3.49: match-time phrases are not injuries ("injury-time winner", "stoppage-time equaliser"), and neither are scans/blows used figuratively in match reports
  const BENIGN = /\b(injury[- ]time|stoppage[- ]time|added[- ]time|injury[- ]hit (?:opponents|rivals)|(?:dealt|deals?) a blow to (?:\w+ )?(?:rivals|opponents)|(?:scans?|tests?) (?:shows?|showed|reveals?|revealed|confirms?|confirmed) no (?:\w+ )?(?:damage|injury|problem|issue)|no (?:serious |major |significant |long-term )?(?:damage|injury|problem)|pass(?:es|ed)? (?:a |his )?(?:late )?fitness test|not (?:seriously )?injured|miss(?:es|ed)? (?:a |the |his )?(?:penalty|pen|chance|sitter|target|opportunit\w*)|injury (?:boost|return|comeback))\b/gi;
  const benign = (s) => String(s || '').replace(BENIGN, ' ');
  const NEG = { test: (s) => NEG_RE.test(benign(s)) };
  // v3.50: words that are bad news whatever else the sentence says
  const STRONG = /\b(ruled out|out for|surgery|operation|stretchered|hospital\w*|limped off|injured in training|suspen\w*|red card|banned|sidelined|setback|will miss|to miss|not in the squad|left out of the squad)\b/i;
  const GOOD_RE = /\b(back in training|fit again|fit to (?:play|face|start)|recovered|cleared|in contention|hat-?trick|brace|scores?|scored|scoring|winner|equali[sz]er|starts?|started|starting|recalled|in the (?:starting )?(?:xi|line-?up)|named in|nailed|played (?:the )?(?:full|90)|full 90|man of the match|assists?|assisted)\b/gi;
  const countRe = (re, s) => (String(s).match(new RegExp(re.source, 'gi')) || []).length;
  // tone of one sentence: 'neg' needs a strong word, or more warning words than good-news words
  const toneOf = (s) => {
    const t = benign(s), inc = INCIDENT_RE.test(t), strong = STRONG.test(t);
    const nNeg = countRe(NEG_RE, t) + (inc ? 1 : 0), nGood = countRe(GOOD_RE, t);
    if (strong || (nNeg && nNeg > nGood)) return { t: 'neg', inc: inc && (strong || nNeg > nGood), strong };
    if (nGood) return { t: 'pos', inc: false, strong: false };
    return { t: 'neutral', inc: false, strong: false };
  };
  const INCIDENT = { test: (s) => INCIDENT_RE.test(benign(s)) };
  const GOODNEWS = /\b(back in training|returns?|returned|fit again|fit to|available|boost|recovered|back from injury|cleared|in contention|hat-?trick|brace|scores?|scored|starts?|starting|recalled|in the (starting )?(xi|line-?up)|named in|nailed)\b/i;

  $('#f').onsubmit = (e) => {
    e.preventDefault();
    const v = $('#tid').value.trim();
    if (!/^\d+$/.test(v)) { out.innerHTML = '<div class="err">A team ID is a number, for example 123456.</div>'; return; }
    try { localStorage.setItem('fplAnalystId', v); } catch (er) {}
    run(+v);
  };
  if ($('#tid').value) fastStart(+$('#tid').value);
  async function fastStart(id) {
    let have = false; try { have = cacheOk() && !!(await (await caches.open(CKEY)).match('/api/bootstrap-static/')) && !!(await (await caches.open(CKEY)).match(`/api/entry/${id}/`)); } catch (e) {}
    if (!have) return run(id);
    FAST = true; try { await run(id, { cached: true }); } finally { FAST = false; }
    const pill = document.createElement('div'); pill.className = 'updpill'; pill.textContent = 'Saved data · updating…'; const pn = R.querySelector('.panel'); if (pn) pn.appendChild(pill);
    try { await run(id, { quiet: true }); pill.textContent = 'Up to date'; } catch (e) { pill.textContent = 'Offline: showing saved data'; }
    setTimeout(() => pill.remove(), 1800);
  }
  $('#rf').onclick = () => { const v = $('#tid').value.trim(); if (/^\d+$/.test(v)) run(+v); };

  const LIVEC = {};
  // ---------- v3.5: previous seasons (2024/25, 2023/24) from the public FPL data archive on GitHub ----------
  // Matched to this season's players by FPL's permanent player code. Cached on this browser: past seasons never change.
  const PAST_SEASONS = ['2024-25', '2023-24'];
  const PAST_KEY = 'fplAnalystPast_v2';
  let PAST = null;
  const csvRows = (txt) => { const rows = []; let row = [], f = '', q = false; for (let i = 0; i < txt.length; i++) { const c = txt[i];
      if (q) { if (c === '"') { if (txt[i + 1] === '"') { f += '"'; i++; } else q = false; } else f += c; }
      else if (c === '"') q = true; else if (c === ',') { row.push(f); f = ''; } else if (c === '\n') { row.push(f); rows.push(row); row = []; f = ''; } else if (c !== '\r') f += c; }
    if (f || row.length) { row.push(f); rows.push(row); } return rows; };
  async function loadPast() {
    if (PAST) return PAST;
    try { const c = JSON.parse(localStorage.getItem(PAST_KEY) || 'null'); if (c && c.v === 2 && PAST_SEASONS.every((k) => c.s[k])) return (PAST = c); } catch (e) {}
    const res = await Promise.allSettled(PAST_SEASONS.map((k) => withTimeout(fetch(`https://raw.githubusercontent.com/vaastav/Fantasy-Premier-League/master/data/${k}/players_raw.csv`).then((r) => { if (!r.ok) throw new Error('HTTP ' + r.status); return r.text(); }), 15000)));
    const out = { v: 2, s: {} };
    res.forEach((r, i) => { if (r.status !== 'fulfilled') return; const rows = csvRows(r.value); const h = rows.shift() || []; const ix = (n) => h.indexOf(n);
      const I = { code: ix('code'), m: ix('minutes'), p: ix('total_points'), g: ix('goals_scored'), a: ix('assists'), xg: ix('expected_goals'), xa: ix('expected_assists'), st: ix('starts'), cs: ix('clean_sheets'), et: ix('element_type'), tc: ix('team_code') };
      if (I.code < 0 || I.m < 0) return; const m = {};
      rows.forEach((x) => { const mins = +x[I.m] || 0; if (!x[I.code] || mins <= 0) return; m[x[I.code]] = [mins, +x[I.p] || 0, +x[I.g] || 0, +x[I.a] || 0, +x[I.xg] || 0, +x[I.xa] || 0, +x[I.st] || 0, +x[I.cs] || 0, +x[I.et] || 0, +x[I.tc] || 0]; });
      out.s[PAST_SEASONS[i]] = m; });
    if (Object.keys(out.s).length) { PAST = out; if (PAST_SEASONS.every((k) => out.s[k])) { try { localStorage.setItem(PAST_KEY, JSON.stringify(out)); } catch (e) {} } }
    return PAST || { v: 1, s: {} };
  }
  const pastOf = (e) => PAST_SEASONS.map((k) => { const r = PAST && PAST.s[k] && PAST.s[k][e.code]; return r ? { k, m: r[0], p: r[1], g: r[2], a: r[3], xg: r[4], xa: r[5], st: r[6], cs: r[7], tc: r[9] || 0 } : null; });
  // New at his club this season: last season's archive puts him at a different club (or he wasn't in the Premier League)
  const isNewSigning = (e) => { const t = BS && BS.teams.find((x) => x.id === e.team); const p = pastOf(e)[0]; if (!PAST || !PAST.s[PAST_SEASONS[0]]) return false; return !p ? e.minutes < 2000 : !!(t && p.tc && p.tc !== t.code); };
  // ---------- v3.5: price change outlook (rule of thumb on net transfers since the last deadline) ----------
  // v3.15: snapshots of every player's price and net transfers (saved every 2 hours) give the trend and the net since his last change.
  // Threshold: about 6% of his owners for a rise (at least 60k); falls come at about 70% of that, and at half for injured players.
  const PS_KEY = 'fplAnalystPriceSnap';
  let PSNAP = null; try { PSNAP = JSON.parse(localStorage.getItem(PS_KEY) || 'null'); } catch (e) {}
  function priceSnap() {
    if (!BS) return; const now = Date.now(), gw = (BS.events.find((e) => e.is_next) || {}).id || 0;
    if (!PSNAP || PSNAP.gw !== gw) PSNAP = { gw, base: {}, s: [] };
    BS.elements.forEach((e) => { const b = PSNAP.base[e.id]; const net = e.transfers_in_event - e.transfers_out_event; if (!b || b[0] !== e.now_cost) PSNAP.base[e.id] = [e.now_cost, b ? net : (e.cost_change_event ? net : 0), now]; });
    const last = PSNAP.s[PSNAP.s.length - 1];
    if (!last || now - last.t > 2 * 36e5) { const m = {}; BS.elements.forEach((e) => (m[e.id] = e.transfers_in_event - e.transfers_out_event)); PSNAP.s.push({ t: now, m }); PSNAP.s = PSNAP.s.slice(-12); }
    try { localStorage.setItem(PS_KEY, JSON.stringify(PSNAP)); } catch (e) { PSNAP.s = PSNAP.s.slice(-4); try { localStorage.setItem(PS_KEY, JSON.stringify(PSNAP)); } catch (er) {} }
  }
  function pricePred(e) {
    if (!BS) return null;
    const net = (e.transfers_in_event || 0) - (e.transfers_out_event || 0), hurt = e.status !== 'a';
    const owners = (+e.selected_by_percent || 0) / 100 * (BS.total_players || 10e6);
    const b = PSNAP && PSNAP.base[e.id]; const since = net - (b && b[0] === e.now_cost ? b[1] : (e.cost_change_event ? Math.round(net * 0.5) : 0));
    const up = Math.max(60000, owners * 0.06), down = up * (hurt ? 0.5 : 0.7);
    const pct = since >= 0 ? (since / up) * 100 : -(-since / down) * 100;
    let rate = 0; const ss = PSNAP ? PSNAP.s : []; if (ss.length >= 2) { const a = ss.find((x) => Date.now() - x.t < 30 * 36e5) || ss[0], z = ss[ss.length - 1]; const h = (z.t - a.t) / 36e5; if (h >= 2 && a.m[e.id] != null) rate = (z.m[e.id] - a.m[e.id]) / h; }
    const need = since >= 0 ? up - since : down + since; const hrs = rate && Math.sign(rate) === Math.sign(since || rate) ? need / Math.abs(rate) : Infinity;
    // FPL updates prices once a day, at about 01:30 UK time
    const nx = new Date(); nx.setUTCHours(1, 30, 0, 0); if (nx < new Date()) nx.setUTCDate(nx.getUTCDate() + 1); const toUpd = (nx - Date.now()) / 36e5;
    const eta = Math.abs(pct) >= 100 || hrs <= toUpd ? 'tonight' : hrs <= toUpd + 24 ? 'tomorrow' : hrs < 96 ? 'this week' : '';
    return { pct: Math.max(-130, Math.min(130, pct)), since, rate, eta, d: pct >= 0 ? 'up' : 'down' };
  }
  function priceOutlook(e) {
    const p = pricePred(e); if (!p) return null; const net = (e.transfers_in_event || 0) - (e.transfers_out_event || 0);
    const a = Math.abs(p.pct);
    if (a >= 95 || (a >= 75 && p.eta === 'tonight')) return { d: p.d, lv: 'likely', net, p };
    if (a >= 60 || (a >= 45 && p.eta === 'tomorrow')) return { d: p.d, lv: 'possible', net, p };
    return null;
  }
  const kfmt = (n) => (Math.abs(n) >= 1000 ? Math.round(n / 1000) + 'k' : String(n));
  const priceB = (e) => { const o = priceOutlook(e); if (!o) return ''; return `<span class="prc ${o.d} ${o.lv}" title="${o.net > 0 ? '+' : ''}${kfmt(o.net)} net transfers since the last deadline. Rough guide: about +150k to +200k for a £0.1m rise, about −100k for a fall (sooner if injured). Prices change overnight.">${o.d === 'up' ? '▲' : '▼'} £0.1m ${o.d === 'up' ? 'rise' : 'drop'} ${o.lv}</span>`; };
  // ---------- v3.6: accuracy test ----------
  // For each finished gameweek, rebuild every player's numbers from the weeks before it only, project that week with the
  // same formula the app uses, and compare with what really happened. Run on demand; results saved on this browser.
  // v3.9 model weights, tuned on GW4-10 of 2026/27 (held-out test: rank quality +8%, top-10 picks +25%, error -3%):
  // more weight on underlying numbers (xGI, clean sheets), less on recent form; the defensive-contribution bonus is left to
  // points per 90 (it already counts those points); players who barely played in the last 2 gameweeks are cut to 35%.
  const MODEL = { wF: 0.10, wP: 0.25, wU: 0.65, dc: 0, gate: 0.35 };
  const ACC_KEY = 'fplAnalystAccuracy_v2';
  let ACC = null; try { ACC = JSON.parse(localStorage.getItem(ACC_KEY) || 'null'); } catch (e) {}
  async function runAccuracy(onProgress) {
    const done = BS.events.filter((e) => e.finished).map((e) => e.id);
    if (done.length < 4) throw new Error('Needs at least 4 finished gameweeks.');
    const lives = {}; for (let i = 0; i < done.length; i++) { lives[done[i]] = await LIVE(done[i]); if (onProgress) onProgress(Math.round(((i + 1) / done.length) * 70)); }
    const tests = done.filter((g) => g >= 4).slice(-8);
    const GI = [0, 6, 6, 5, 4], CS = [0, 4, 4, 1, 0], E = BS.elements;
    const games = {}; FX.forEach((f) => { if (!f.event) return; [f.team_h, f.team_a].forEach((t) => { const k = t + '-' + f.event; games[k] = (games[k] || 0) + 1; }); });
    const gp = (team, g) => games[team + '-' + g] || 0;
    const phi = (z) => { const t = 1 / (1 + 0.2316419 * Math.abs(z)), d = 0.3989423 * Math.exp(-z * z / 2); const p = d * t * (0.3193815 + t * (-0.3565638 + t * (1.781478 + t * (-1.821256 + t * 1.330274)))); return z > 0 ? 1 - p : p; };
    const K90 = 5;
    const rows = []; let capOurs = 0, capForm = 0, capBest = 0;
    const errs = { model: [], fpl: [], form: [], ppg: [] };
    const myId = (LASTA && LASTA.id) || CURID; const myPicks = {}; const cal = { 1: [0, 0], 2: [0, 0], 3: [0, 0], 4: [0, 0] };
    if (myId) await Promise.all(tests.map((g) => J(`/api/entry/${myId}/event/${g}/picks/`).then((x) => (myPicks[g] = x)).catch(() => null)));
    const teamRows = [], perG = [];
    tests.forEach((g, ti) => {
      // cumulative stats before g
      const prev = done.filter((x) => x < g);
      const st = {}; E.forEach((e) => (st[e.id] = { m: 0, p: 0, xgi: 0, dc: 0, cs: 0, hasDc: false, last: [] }));
      prev.forEach((x) => { const L = lives[x]; if (!L) return; E.forEach((e) => { const r = L[e.id]; const S = st[e.id]; const m = r ? r.minutes || 0 : 0; S.m += m; if (r) { S.p += r.total_points || 0; S.xgi += +r.expected_goal_involvements || 0; if (r.defensive_contribution != null) { S.dc += +r.defensive_contribution || 0; S.hasDc = true; } S.cs += r.clean_sheets || 0; } S.last.push({ g: x, m, p: r ? r.total_points || 0 : 0 }); }); });
      // league table before g
      const tb = {}; BS.teams.forEach((t) => (tb[t.id] = { id: t.id, P: 0, Pts: 0, GD: 0 }));
      FX.filter((f) => f.event && f.event < g && f.finished && f.team_h_score != null).forEach((f) => { const h = tb[f.team_h], a = tb[f.team_a]; h.P++; a.P++; h.GD += f.team_h_score - f.team_a_score; a.GD += f.team_a_score - f.team_h_score; if (f.team_h_score > f.team_a_score) h.Pts += 3; else if (f.team_h_score < f.team_a_score) a.Pts += 3; else { h.Pts++; a.Pts++; } });
      const tbl = Object.values(tb).sort((a, b) => b.Pts - a.Pts || b.GD - a.GD); tbl.forEach((r, i) => (r.pos = i + 1));
      const nT = tbl.length, playedN = Math.max(0, ...tbl.map((r) => r.P)), tW = Math.min(0.45, (playedN / 38) * 1.6);
      const teamGamesBefore = (team) => prev.reduce((a, x) => a + gp(team, x), 0);
      const reg = E.filter((e) => st[e.id].m >= 450);
      const prior = [0, 1, 2, 3, 4].map((et) => { if (!et) return null; const xs = reg.filter((e) => e.element_type === et); const n90 = xs.reduce((a, e) => a + st[e.id].m, 0) / 90 || 1; return { xgi: xs.reduce((a, e) => a + st[e.id].xgi, 0) / n90, pts: xs.reduce((a, e) => a + st[e.id].p, 0) / n90, dc: xs.reduce((a, e) => a + st[e.id].dc, 0) / n90 }; });
      const L = lives[g]; const preds = [];
      E.forEach((e) => {
        const S = st[e.id]; if (S.m < 90) return; const et = e.element_type;
        const tg = teamGamesBefore(e.team) || 1, share = Math.min(1, S.m / (90 * tg));
        const l5g = S.last.slice(-5); let m5 = 0, n5 = 0; l5g.forEach((x) => { const n = gp(e.team, x.g); if (n) { n5 += n; m5 += x.m; } });
        const l5 = n5 ? m5 / (90 * n5) : share; let m2 = 0, n2 = 0; S.last.slice(-2).forEach((x) => { const n = gp(e.team, x.g); if (n) { n2 += n; m2 += x.m; } });
        const r = Math.max(0.08, Math.min(1, (0.6 * l5 + 0.4 * share) / 0.85)) * (n2 && m2 / (90 * n2) < 0.2 ? MODEL.gate : 1);
        const pw = Math.max(0.3, 1 - S.m / 2700), W = [0.5 * pw, 0.25 * pw]; let numX = S.xgi, numP = S.p, n90 = S.m / 90;
        pastOf(e).forEach((p, i) => { if (!p) return; numX += W[i] * (p.xg + p.xa); numP += W[i] * p.p; n90 += W[i] * (p.m / 90); });
        const xgi = (numX + K90 * prior[et].xgi) / (n90 + K90), pts90 = (numP + K90 * prior[et].pts) / (n90 + K90);
        const dc90 = S.hasDc ? (S.dc + K90 * prior[et].dc) / (S.m / 90 + K90) : 0;
        const lam = dc90 * 0.95, thr = et === 2 ? 10 : 12; const dcv = et === 1 || lam <= 0 ? 0 : 2 * (1 - phi((thr - 0.5 - lam) / Math.sqrt(1.6 * lam)));
        const cs90 = S.m ? S.cs / (S.m / 90) : 0;
        const l4 = S.last.slice(-4); const fg = l4.reduce((a, x) => a + gp(e.team, x.g), 0) || 1; const form = l4.reduce((a, x) => a + x.p, 0) / fg;
        const under = (2 + xgi * GI[et] + cs90 * CS[et] + (et === 1 ? 0.6 : 0) + MODEL.dc * dcv) * r;
        const base = MODEL.wF * form + MODEL.wP * pts90 * r + MODEL.wU * under;
        const fxs = FX.filter((f) => f.event === g && (f.team_h === e.team || f.team_a === e.team));
        const mult = (w) => fxs.reduce((a, f) => { const home = f.team_h === e.team; const o = home ? f.team_a : f.team_h; const fdr = home ? f.team_h_difficulty : f.team_a_difficulty; const tblD = 1 + (4 * (nT - tb[o].pos)) / (nT - 1); const diff = (1 - w) * fdr + w * tblD; return a + (1 + (3 - diff) * 0.13 + (home ? 0.03 : -0.03)); }, 0);
        const actual = L && L[e.id] ? L[e.id].total_points || 0 : 0;
        const pB = base * mult(tW), pF = base * mult(0), pform = form * fxs.length, pppg = (S.p / tg) * fxs.length;
        preds.push({ e, et, pB, pF, pform, pppg, actual, played: !!(L && L[e.id] && L[e.id].minutes > 0) });
      });
      perG.push({ g, preds, L });
      if (onProgress) onProgress(70 + Math.round(((ti + 1) / tests.length) * 30));
    });
    // v3.60: the fixture-difficulty rating and the calibration depend only on FPL data (not on this device's earlier
    // choice), so every phone and computer ends up with the same model
    const errOf = (k) => { let sm = 0, n = 0; perG.forEach((q) => q.preds.forEach((x) => { sm += Math.abs(x[k] - x.actual); n++; })); return n ? sm / n : 0; };
    const fdrMode = errOf('pB') < errOf('pF') * 0.995 ? 'blend' : 'fpl', KM = fdrMode === 'blend' ? 'pB' : 'pF', KO = KM === 'pB' ? 'pF' : 'pB';
    perG.forEach(({ g, preds, L }) => {
      preds.forEach((x) => { x.pm = x[KM]; x.pf = x[KO]; if (x.pm >= 2 && x.played) { cal[x.et][0] += x.pm; cal[x.et][1] += x.actual; } });
      const mp = myPicks[g]; if (mp && mp.picks) { const by = {}; preds.forEach((x) => (by[x.e.id] = x.pm)); let pj = 0, ac = 0; mp.picks.forEach((q) => { const m = q.multiplier || 0; pj += (by[q.element] || 0) * m; ac += (L && L[q.element] ? L[q.element].total_points || 0 : 0) * m; }); const cap = mp.picks.find((q) => q.is_captain); const ce = cap && BS.elements.find((x) => x.id === cap.element); teamRows.push({ g, pj, ac, hit: (mp.entry_history || {}).event_transfers_cost || 0, cap: ce ? ce.web_name : '' }); }
      const mae = (k) => preds.reduce((a, x) => a + Math.abs(x[k] - x.actual), 0) / (preds.length || 1);
      const top = (k) => preds.slice().sort((a, b) => b[k] - a[k]).slice(0, 5);
      const avgA = (arr) => arr.reduce((a, x) => a + x.actual, 0) / (arr.length || 1);
      const ours = avgA(top('pm')), fm = avgA(top('pform')), best = avgA(preds.slice().sort((a, b) => b.actual - a.actual).slice(0, 5));
      capOurs += ours; capForm += fm; capBest += best;
      ['model', 'fpl', 'form', 'ppg'].forEach((k, i) => errs[k].push(mae(['pm', 'pf', 'pform', 'pppg'][i])));
      rows.push({ g, n: preds.length, mae: mae('pm'), maeF: mae('pf'), maeForm: mae('pform'), maePpg: mae('pppg'), top5: ours, top5Form: fm, top5Best: best, pick: top('pm')[0] ? top('pm')[0].e.web_name : '', pickPts: top('pm')[0] ? top('pm')[0].actual : 0 });
    });
    const avg = (a) => a.reduce((x, y) => x + y, 0) / (a.length || 1);
    const calib = {}; [1, 2, 3, 4].forEach((et) => { const [pj, ac] = cal[et]; calib[et] = pj > 20 ? Math.max(0.85, Math.min(1.18, ac / pj)) : 1; });
    const res = { v: 3, at: Date.now(), gws: tests, rows, team: teamRows, calib, mae: avg(errs.model), maeF: avg(errs.fpl), maeForm: avg(errs.form), maePpg: avg(errs.ppg), top5: capOurs / tests.length, top5Form: capForm / tests.length, top5Best: capBest / tests.length };
    // Fixture difficulty: keep FPL's rating alone only if it is clearly better (by more than 0.5%)
    let curM = 'fpl'; try { curM = localStorage.getItem('fplAnalystFdrMode2') || 'fpl'; } catch (e) {}
    // the other rating replaces the one in use only if it is clearly better (by more than 0.5%)
    res.fdr = fdrMode; res.cur = curM;
    try { localStorage.setItem('fplAnalystFdrMode2', res.fdr); localStorage.setItem(ACC_KEY, JSON.stringify(res)); } catch (e) {}
    ACC = res; return res;
  }
  function accTeamHtml(R2) {
    if (!R2.team || !R2.team.length) return '';
    const tp = R2.team.reduce((a, r) => a + r.pj, 0), ta = R2.team.reduce((a, r) => a + r.ac, 0);
    let calOn = true; try { calOn = localStorage.getItem('fplAnalystCalib') !== 'off'; } catch (e) {}
    const cl = R2.calib || {}; const pcf = (v) => `${v >= 1 ? '+' : '−'}${Math.round(Math.abs(v - 1) * 100)}%`;
    return `<h4 class="acch">Your team: projected vs actual</h4><p class="note" style="margin:0 0 6px">Your real starting XI and captain each week, projected with only what was known before that deadline (hits not included).</p>
<div class="tw"><table class="acct"><thead><tr><th>GW</th><th class="n">Projected</th><th class="n">Actual</th><th class="n">Diff</th><th>Captain</th></tr></thead><tbody>${R2.team.map((r) => `<tr><td>GW${r.g}</td><td class="n">${f1(r.pj)}</td><td class="n"><b>${r.ac}</b></td><td class="n ${r.ac - r.pj >= 0 ? 'up' : 'dn'}">${r.ac - r.pj >= 0 ? '+' : ''}${f1(r.ac - r.pj)}</td><td>${esc(r.cap || '')}</td></tr>`).join('')}<tr><td><b>Total</b></td><td class="n"><b>${f1(tp)}</b></td><td class="n"><b>${ta}</b></td><td class="n ${ta - tp >= 0 ? 'up' : 'dn'}"><b>${ta - tp >= 0 ? '+' : ''}${f1(ta - tp)}</b></td><td></td></tr></tbody></table></div>
<h4 class="acch">Tune-up</h4><p class="note" style="margin:0 0 6px">Players who played scored this much more or less than projected, by position. With tune-up on, every projection is scaled by these (limited to −15% / +18%).</p>
<div class="calrow">${[[1, 'GK'], [2, 'DEF'], [3, 'MID'], [4, 'FWD']].map(([k, l]) => `<span><small>${l}</small><b class="${(cl[k] || 1) >= 1 ? 'up' : 'dn'}">${pcf(cl[k] || 1)}</b></span>`).join('')}<div class="seg"><button type="button" class="${calOn ? 'on' : ''}" data-cal="on">Tune-up on</button><button type="button" class="${calOn ? '' : 'on'}" data-cal="off">Off</button></div></div>`;
  }
  function accHtml() {
    const R2 = ACC;
    const head = `<div class="th"><h3>How accurate are the projections?</h3><button class="lnk2" type="button" id="acc-run">${R2 ? 'Run again' : 'Run the test'}</button></div>`;
    if (!R2) return `${head}<p class="muted">Tests the projection model on this season's finished gameweeks: for each week it uses only the data from before it, then compares with the real points. Takes about 10 seconds.</p><div id="acc-prog"></div>`;
    const pc = (a, b) => Math.round((1 - a / b) * 100);
    return `${head}
<div class="kpis uni"><div class="kpi"><small>Average error per player</small><b>${R2.mae.toFixed(2)} pts</b><span>${R2.maeForm > 0 ? (R2.mae <= R2.maeForm ? pc(R2.mae, R2.maeForm) + '% better' : -pc(R2.mae, R2.maeForm) + '% worse') + ' than form alone' : 'form alone not comparable'}</span></div>
<div class="kpi"><small>Our top 5 picks scored</small><b>${R2.top5.toFixed(1)} pts</b><span>vs ${R2.top5Form.toFixed(1)} for top-5 by form · best possible ${R2.top5Best.toFixed(1)}</span></div>
<div class="kpi"><small>Fixture difficulty</small><b>${R2.fdr === 'fpl' ? "FPL's rating" : 'FPL + table'}</b><span>error ${R2.mae.toFixed(2)} with ${R2.cur === 'blend' ? 'FPL + table' : "FPL's rating"} vs ${R2.maeF.toFixed(2)} with ${R2.cur === 'blend' ? "FPL's rating" : 'FPL + table'}${R2.fdr !== R2.cur ? ': switched' : ': kept'}</span></div></div>
<div class="tw"><table class="acct"><thead><tr><th>GW</th><th class="n">Players</th><th class="n">Our error</th><th class="n">Form only</th><th class="n">Points per game</th><th class="n">Our top 5 avg</th><th class="n">Best top 5</th><th>Our #1 pick</th></tr></thead><tbody>${R2.rows.slice().reverse().map((r) => `<tr><td>${r.g}</td><td class="n">${r.n}</td><td class="n"><b>${r.mae.toFixed(2)}</b></td><td class="n">${r.maeForm.toFixed(2)}</td><td class="n">${r.maePpg.toFixed(2)}</td><td class="n">${r.top5.toFixed(1)}</td><td class="n">${r.top5Best.toFixed(1)}</td><td>${esc(r.pick)} <small class="muted">${r.pickPts} pts</small></td></tr>`).join('')}</tbody></table></div>
<p class="muted fine">Tested on GW${R2.gws[0]}–${R2.gws[R2.gws.length - 1]} (${R2.gws.length} weeks), players with 90+ minutes before each week. Lower error is better. Injury news and set-piece duties aren't known historically, so the live app should do slightly better than this. Last run ${new Date(R2.at).toLocaleString(undefined, { day: 'numeric', month: 'short', hour: '2-digit', minute: '2-digit' })}.</p>${accTeamHtml(R2)}`;
  }
  const LIVE = async (gw) => {
    const done = (BS && BS.events ? BS.events.find((x) => x.id === gw) || {} : {}).finished;
    if (LIVEC[gw] && (done || Date.now() - (LIVEC[gw].__at || 0) < 60e3)) return LIVEC[gw];
    try { const d = await J(`/api/event/${gw}/live/`); const m = {}; d.elements.forEach((x) => (m[x.id] = x.stats)); Object.defineProperty(m, '__at', { value: Date.now(), enumerable: false }); return (LIVEC[gw] = m); } catch (e) { return LIVEC[gw] || null; }
  };
  // Premier League player page: premierleague.com/en/players/{FPL code}/{name-slug}/overview
  const slug = (s) => s.replace(/[øØ]/g, 'o').replace(/[æÆ]/g, 'ae').replace(/ß/g, 'ss').replace(/[đĐ]/g, 'd').replace(/[łŁ]/g, 'l')
    .normalize('NFD').replace(/[̀-ͯ]/g, '').toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '');
  const plUrl = (e) => `https://www.premierleague.com/en/players/${e.code}/${slug(e.first_name + ' ' + e.second_name)}/overview`;

  // Exact selling price with FPL's rule: you keep half of any rise (rounded down to £0.1m), and lose all of any fall.
  async function exactSelling(id, entry, hist, picks) {
    const tr = await J(`/api/entry/${id}/transfers/`).catch(() => null);
    if (!tr) return picks;
    const fh = new Set((hist.chips || []).filter((c) => c.name === 'freehit').map((c) => c.event));
    const E = {}; BS.elements.forEach((e) => (E[e.id] = e));
    const lastIn = {};
    tr.filter((t) => !fh.has(t.event)).sort((a, b) => new Date(a.time) - new Date(b.time)).forEach((t) => (lastIn[t.element_in] = t.element_in_cost));
    const start = entry.started_event || 1;
    const need = picks.filter((p) => lastIn[p.element] == null);
    const sums = await Promise.all(need.map((p) => J(`/api/element-summary/${p.element}/`).catch(() => null)));
    const startPrice = {};
    need.forEach((p, i) => { const h = sums[i] && sums[i].history; const r = h && (h.find((x) => x.round >= start) || h[0]); startPrice[p.element] = r ? r.value : E[p.element].now_cost; });
    return picks.map((p) => {
      const now = E[p.element].now_cost, buy = lastIn[p.element] != null ? lastIn[p.element] : startPrice[p.element];
      const sell = now > buy ? buy + Math.floor((now - buy) / 2) : now;
      return Object.assign({}, p, { purchase_price: buy, selling_price: sell, sellCalc: true });
    });
  }
  // Live gameweek score straight from FPL's live endpoint (before automatic substitutions)
  // ---------- Live gameweek engine ----------
  // FPL bonus: the 3 highest BPS scores in a match get 3, 2 and 1. Tied players share the higher award and push the next one down.
  function provisionalBonus(f) {
    const st = (f.stats || []).find((x) => x.identifier === 'bps'); const out = {};
    if (!st) return out;
    const all = [...(st.h || []), ...(st.a || [])].sort((x, y) => y.value - x.value);
    all.forEach((x) => { const rank = all.filter((y) => y.value > x.value).length + 1; if (rank <= 3) out[x.element] = 4 - rank; });
    return out;
  }
  function liveScore(cur, G) {
    if (!G || !G.pkCur || !G.liveC) return null;
    const gw = cur.id, E = {}; BS.elements.forEach((e) => (E[e.id] = e));
    const games = FX.filter((f) => f.event === gw);
    const fxOf = (team) => games.filter((f) => f.team_h === team || f.team_a === team);
    const prov = {}; games.filter((f) => f.started && !f.finished).forEach((f) => Object.assign(prov, provisionalBonus(f)));
    const chip = G.pkCur.active_chip;
    const rows = G.pkCur.picks.map((x) => {
      const e = E[x.element], st = G.liveC[x.element] || {}, fs = fxOf(e.team);
      const state = !fs.length ? 'blank' : fs.every((f) => f.finished_provisional || f.finished) ? 'done' : fs.some((f) => f.started) ? 'playing' : 'waiting';
      const pb = st.bonus ? 0 : prov[x.element] || 0;   // confirmed bonus is already inside total_points
      return { x, e, st, state, fs, bonus: st.bonus || pb, provBonus: pb, pts: (st.total_points || 0) + pb, mult: x.multiplier, pos: x.position, subIn: false, subOut: false };
    });
    // Automatic substitutions (not with Bench Boost): a starter who played 0 minutes in finished games is replaced
    // by the first bench player, in bench order, who played and keeps a legal formation (1 GK, 3 DEF, 2 MID, 1 FWD).
    if (chip !== 'bboost') {
      const xi = rows.filter((r) => r.pos <= 11), bench = rows.filter((r) => r.pos > 11).sort((a, b) => a.pos - b.pos);
      const count = (t) => xi.filter((r) => !r.subOut && r.e.element_type === t).length + bench.filter((r) => r.subIn && r.e.element_type === t).length;
      const MIN = { 1: 1, 2: 3, 3: 2, 4: 1 };
      xi.filter((r) => r.state === 'done' && !r.st.minutes).forEach((out) => {
        const pick = bench.find((b) => !b.subIn && (b.st.minutes > 0) && ((out.e.element_type === 1) === (b.e.element_type === 1)) &&
          (out.e.element_type === b.e.element_type || count(out.e.element_type) - 1 >= MIN[out.e.element_type]));
        if (pick) { out.subOut = true; pick.subIn = true; pick.mult = 1; }
      });
      // Captain didn't play: the vice-captain gets the captain's multiplier
      const capR = rows.find((r) => r.x.is_captain), vcR = rows.find((r) => r.x.is_vice_captain);
      if (capR && vcR && capR.state === 'done' && !capR.st.minutes && vcR.st.minutes > 0 && !vcR.subOut) { vcR.mult = capR.x.multiplier; vcR.capFrom = true; capR.mult = 1; }
      rows.forEach((r) => { if (r.subOut) r.mult = 0; });
    }
    const counted = rows.filter((r) => r.mult > 0);
    const hit = (G.pkCur.entry_history && G.pkCur.entry_history.event_transfers_cost) || 0;
    const pts = counted.reduce((a, r) => a + r.pts * r.mult, 0) - hit;
    const benchPts = rows.filter((r) => r.mult === 0).reduce((a, r) => a + r.pts, 0);
    const provTotal = counted.reduce((a, r) => a + r.provBonus * r.mult, 0);
    const live = games.filter((f) => f.started && !f.finished_provisional && !f.finished).length;
    const done = games.filter((f) => f.finished_provisional || f.finished).length;
    return { gw, rows, pts, hit, chip, bench: benchPts, provTotal, played: counted.filter((r) => r.st.minutes > 0).length, toPlay: counted.filter((r) => r.state === 'waiting' || (r.state === 'playing' && !r.st.minutes)).length, live, done, games: games.length, fixtures: games, at: new Date() };
  }
  // ======================= v3.55: fast live feed (free, no key) =======================
  // FPL's live data often trails the real match by a minute or more. During matches Elevn also reads
  //   - ESPN's public scoreboard (every 10 s: score, match minute, scorer names, all matches in one request)
  //   - the Premier League match centre (every 20 s: goals, assists, cards and substitutions, by player)
  // Anything they show that FPL hasn't counted yet is added on top and marked ⚡; once FPL catches up, FPL's numbers take over.
  const FASTK = 'elevnFastLive';
  const fastOn = () => { try { return localStorage.getItem(FASTK) !== 'off'; } catch (e) { return true; } };
  const FD = { fx: {}, pl: null, plAt: 0, n: 0, err: '', at: 0, first: {}, lead: [], seen: new Set(), win: {} };
  let FASTT = null;
  const FMK = 'elevnFotmob', FM_API = 'https://www.fotmob.com/api/data/';
  const fmOn = () => { if (!fastOn()) return false; try { return localStorage.getItem(FMK) !== 'off'; } catch (e) { return true; } };
  const fmFold = (x) => String(x || '').normalize('NFD').replace(/[̀-ͯ]/g, '').toLowerCase().replace(/[^a-z ]/g, ' ').replace(/\s+/g, ' ').trim();
  // FotMob player -> FPL player, by name within the club (FotMob ids are not FPL ids)
  function fmPlayer(name, teams) {
    const n = fmFold(name); if (!n || !BS) return null; const pool = BS.elements.filter((e) => teams.includes(e.team));
    let h = pool.find((e) => fmFold(e.first_name + ' ' + e.second_name) === n) || pool.find((e) => fmFold(e.web_name) === n);
    if (!h) { const w = n.split(' '), last = w[w.length - 1]; const c = pool.filter((e) => fmFold(e.second_name).split(' ').includes(last) || fmFold(e.web_name) === last);
      h = c.length === 1 ? c[0] : c.find((e) => fmFold(e.first_name).split(' ')[0] === w[0]) || null; }
    return h ? h.id : null;
  }
  function fmEvents(d, f) {
    const lu = (d.content && d.content.lineup) || {}, id2e = {}, starters = new Set();
    [['homeTeam', f.team_h], ['awayTeam', f.team_a]].forEach(([k, t]) => { const T = lu[k] || {};
      (T.starters || []).forEach((p) => { const e = fmPlayer(p.name, [t]); if (e) { id2e[p.id] = e; starters.add(e); } });
      (T.subs || []).forEach((p) => { const e = fmPlayer(p.name, [t]); if (e) id2e[p.id] = e; }); });
    const who = (pid, name, side) => id2e[pid] || fmPlayer(name, side ? [side] : [f.team_h, f.team_a]);
    const ev = {}; const get = (e) => ev[e] || (ev[e] = { g: 0, a: 0, y: 0, r: 0, og: 0, on: starters.has(e) });
    ((((d.content || {}).matchFacts || {}).events || {}).events || []).forEach((x) => {
      const side = x.isHome === true ? f.team_h : x.isHome === false ? f.team_a : null;
      if (x.type === 'Goal') { if (x.ownGoal) { const e = who(x.playerId, x.nameStr, null); if (e) get(e).og++; }
        else { const e = who(x.playerId, x.nameStr, side); if (e) get(e).g++; if (x.assistPlayerId || x.assistInput) { const a = who(x.assistPlayerId, x.assistInput, side); if (a) get(a).a++; } } }
      else if (x.type === 'Card') { const e = who(x.playerId, x.nameStr, side); if (e) { const c = String(x.card || ''); if (/red/i.test(c)) { get(e).r++; get(e).y = 0; } else if (/yellow/i.test(c)) get(e).y++; } }
      else if (x.type === 'Substitution' && Array.isArray(x.swap) && x.swap.length === 2) { const [i, out] = x.swap; const ei = who(+i.id, i.name, side), eo = who(+out.id, out.name, side); if (ei) get(ei).on = true; if (eo) get(eo).on = false; }
    });
    return { ev, starters: [...starters] };
  }
  const fastMerge = (a, b, aNewer) => !a ? b : !b ? a : { g: Math.max(a.g, b.g), a: Math.max(a.a, b.a), y: Math.max(a.y, b.y), r: Math.max(a.r, b.r), og: Math.max(a.og, b.og), on: aNewer ? a.on : b.on };
  const FGOAL = [0, 10, 6, 5, 4], FCS = [0, 4, 4, 1, 0];
  async function fastGet(url) {
    try { const r = await withTimeout(fetch(url, { credentials: 'omit' }), 8000); if (!r.ok) throw new Error('HTTP ' + r.status); return await r.json(); }
    catch (e) { const d = directText(); if (!d) throw e; return JSON.parse(await withTimeout(d(url), 9000)); }
  }
  const nameTeam = (n) => oddsTeam(String(n || '').replace(/&/g, 'and'));
  // Premier League match-centre ids for this gameweek's FPL fixtures (same clubs, kick-off within 6 hours)
  async function fastPlIndex(games) {
    if (FD.pl && Date.now() - FD.plAt < 6 * 36e5 && games.every((f) => FD.pl[f.id] !== undefined)) return FD.pl;
    const season = await fastGet(PL_API_C + 'competitions/1/compseasons?page=0&pageSize=5'); const sid = season.content && season.content[0] && season.content[0].id;
    const ks = games.map((f) => Date.parse(f.kickoff_time)).filter(Number.isFinite); if (!sid || !ks.length) return (FD.pl = {});
    const qs = new URLSearchParams({ comps: '1', compSeasons: String(sid), page: '0', pageSize: '40', sort: 'asc', startDate: new Date(Math.min(...ks) - 864e5).toISOString().slice(0, 10), endDate: new Date(Math.max(...ks) + 864e5).toISOString().slice(0, 10), altIds: 'true' });
    const fl = await fastGet(PL_API_C + 'fixtures?' + qs); const list = fl.content || [];
    const map = {}; games.forEach((f) => { const k = Date.parse(f.kickoff_time); const hit = list.find((x) => { const t = x.teams || []; if (t.length < 2) return false; const h = BS.teams.find((y) => y.short_name === (t[0].team.club || {}).abbr) || { id: nameTeam(t[0].team.name) }, a = BS.teams.find((y) => y.short_name === (t[1].team.club || {}).abbr) || { id: nameTeam(t[1].team.name) }; return h.id === f.team_h && a.id === f.team_a && Math.abs((x.kickoff && x.kickoff.millis || 0) - k) < 6 * 36e5; }); map[f.id] = hit ? hit.id : null; });
    FD.plAt = Date.now(); return (FD.pl = map);
  }
  const fastLive = (games) => games.filter((f) => { const k = Date.parse(f.kickoff_time); return !f.finished && Number.isFinite(k) && Date.now() >= k - 60e3 && Date.now() < k + 3 * 36e5; });
  async function fastTick() {
    clearTimeout(FASTT); FASTT = null;
    const A = LASTA; if (!A || !A.live || !fastOn() || !document.getElementById(PID)) return;
    const games = FX.filter((f) => f.event === A.live.gw), live = fastLive(games);
    if (!live.length) { const next = games.filter((f) => !f.started && f.kickoff_time).map((f) => Date.parse(f.kickoff_time) - Date.now()).filter((x) => x > 0).sort((a, b) => a - b)[0]; if (next != null && next < 6 * 36e5) FASTT = setTimeout(fastTick, Math.max(20e3, next - 60e3)); return; }
    FD.n++; let changed = false;
    // ESPN: every tick
    try {
      const sb = await fastGet('https://site.api.espn.com/apis/site/v2/sports/soccer/eng.1/scoreboard');
      (sb.events || []).forEach((ev) => { const c = (ev.competitions || [])[0]; if (!c) return; const H = c.competitors.find((x) => x.homeAway === 'home'), Aw = c.competitors.find((x) => x.homeAway === 'away'); if (!H || !Aw) return;
        mxPut(games, ev);
        const h = nameTeam(H.team.displayName), a = nameTeam(Aw.team.displayName); const f = live.find((x) => x.team_h === h && x.team_a === a); if (!f) return;
        const st = ev.status && ev.status.type || {}; const o = FD.fx[f.id] || (FD.fx[f.id] = {});
        const hs = +H.score || 0, as = +Aw.score || 0; if (o.h !== hs || o.a !== as) changed = true;
        fastMatchAlerts(A, f, o, st.state, ev, c, H, hs, as);
        Object.assign(o, { h: Math.max(hs, o.plH || 0), a: Math.max(as, o.plA || 0), eh: hs, ea: as, clock: /HALFTIME/.test(st.name || '') ? 'HT' : st.state === 'post' ? 'FT' : /^(HT|FT)$/.test(st.shortDetail || '') ? st.shortDetail : ev.status.displayClock, state: st.state, src: 'ESPN', at: Date.now(),
          scorers: (c.details || []).filter((d) => d.scoringPlay).map((d) => ({ side: d.team && d.team.id === H.team.id ? 'h' : 'a', who: ((d.athletesInvolved || [])[0] || {}).displayName || '', min: d.clock && d.clock.displayValue, og: !!d.ownGoal, pen: !!d.penaltyKick })) });
      });
      FD.err = '';
    } catch (e) { FD.err = 'Live source 1: ' + (e.message || e); }
    // Premier League match centre: every other tick (its data refreshes every 30 s)
    if (FD.n % 2 === 1) try {
      const idx = await fastPlIndex(games); const byCode = {}; BS.elements.forEach((e) => (byCode[e.code] = e.id));
      await Promise.all(live.filter((f) => idx[f.id]).map(async (f) => {
        const d = await fastGet(PL_API_C + 'fixtures/' + idx[f.id] + '?altIds=true'); const o = FD.fx[f.id] || (FD.fx[f.id] = {});
        const p2e = {}; (d.teamLists || []).forEach((tl) => [...(tl.lineup || []), ...(tl.substitutes || [])].forEach((p) => { const c = +String((p.altIds || {}).opta || '').replace(/^p/, ''); if (byCode[c]) p2e[p.id] = byCode[c]; }));
        const starters = new Set(); (d.teamLists || []).forEach((tl) => (tl.lineup || []).forEach((p) => p2e[p.id] && starters.add(p2e[p.id])));
        const ev = {}; const add = (pid, k) => { const e = p2e[pid]; if (!e) return; (ev[e] = ev[e] || { g: 0, a: 0, y: 0, r: 0, og: 0, on: starters.has(e) })[k]++; };
        (d.events || []).forEach((x) => { if (x.type === 'G' || x.type === 'P') { add(x.personId, 'g'); if (x.assistId) add(x.assistId, 'a'); } else if (x.type === 'O') add(x.personId, 'og'); else if (x.type === 'B') add(x.personId, x.description === 'Y' ? 'y' : 'r'); else if (x.type === 'S') { const e = p2e[x.personId]; if (e) { ev[e] = ev[e] || { g: 0, a: 0, y: 0, r: 0, og: 0, on: starters.has(e) }; ev[e].on = x.description === 'ON'; } } });
        const t = d.teams || []; const ph = t[0] ? +t[0].score || 0 : 0, pa = t[1] ? +t[1].score || 0 : 0;
        if (o.plH !== ph || o.plA !== pa) changed = true;
        Object.assign(o, { plH: ph, plA: pa, h: Math.max(ph, o.eh || 0), a: Math.max(pa, o.ea || 0), clock: o.clock || (d.clock && d.clock.label), ev, plAt: Date.now(), starters: [...starters] });
      }));
    } catch (e) { FD.err = 'Live source 3: ' + (e.message || e); }
    // FotMob: scores every tick (its data is cached 10 s); match details when its score changes, otherwise every 60 s
    if (fmOn()) try {
      const days = [...new Set(live.map((f) => new Date(Date.parse(f.kickoff_time)).toISOString().slice(0, 10).replace(/-/g, '')))];
      const lists = await Promise.all(days.map((d) => fastGet(FM_API + 'matches?date=' + d)));
      const ms = []; lists.forEach((L) => (L.leagues || []).forEach((lg) => { if (lg.primaryId === 47 || lg.id === 47) ms.push(...(lg.matches || [])); }));
      await Promise.all(live.map(async (f) => {
        const k = Date.parse(f.kickoff_time); const m = ms.find((x) => x.home && x.away && nameTeam(x.home.name) === f.team_h && nameTeam(x.away.name) === f.team_a && Math.abs(Date.parse((x.status || {}).utcTime) - k) < 6 * 36e5); if (!m) return;
        const o = FD.fx[f.id] || (FD.fx[f.id] = {}); const st = m.status || {};
        const fh = +m.home.score || 0, fa = +m.away.score || 0; if (o.fmH !== fh || o.fmA !== fa) changed = true;
        o.fmH = fh; o.fmA = fa; o.fmClock = st.liveTime && st.liveTime.short; o.fmAt = Date.now();
        const sig = fh + ':' + fa; if (st.started && (o.fmSig !== sig || Date.now() - (o.fmDetAt || 0) > 60e3)) {
          const d = await fastGet(FM_API + 'matchDetails?matchId=' + m.id); const r = fmEvents(d, f);
          Object.assign(o, { fmEv: r.ev, fmStarters: r.starters, fmSig: sig, fmDetAt: Date.now() }); changed = true; }
      }));
    } catch (e) { FD.err = (FD.err ? FD.err + ' · ' : '') + 'Live source 2: ' + (e.message || e); }
    // combine the sources, and count which one showed each new goal first
    live.forEach((f) => { const o = FD.fx[f.id]; if (!o) return; o.h = Math.max(o.eh || 0, o.plH || 0, o.fmH || 0); o.a = Math.max(o.ea || 0, o.plA || 0, o.fmA || 0); o.clock = o.clock || o.fmClock;
      const tot = { 'Live source 1': o.eh != null ? o.eh + o.ea : -1, 'Live source 3': o.plH != null ? o.plH + o.plA : -1, 'Live source 2': o.fmH != null ? o.fmH + o.fmA : -1 }, best = o.h + o.a;
      if (o.best == null) o.best = best; else if (best > o.best) { o.best = best; Object.keys(tot).forEach((s) => { if (tot[s] === best) FD.win[s] = (FD.win[s] || 0) + 1; }); } });
    FD.at = Date.now();
    if (A.gwCmp && A.gwCmp.liveC) { const before = A.live.pts; A.live = liveScore(A.cur, A.gwCmp); fastApply(A, A.live); fastAlerts(A); if (changed || A.live.pts !== before) paintLiveNow(A); else { const b = R.getElementById('fastst'); if (b) b.innerHTML = fastStatus(); } }
    FASTT = setTimeout(fastTick, 10e3);
  }
  // v3.62: kick-off of your matches and every goal (yours get their own alert with points from fastAlerts)
  function fastMatchAlerts(A, f, o, state, ev, c, H, hs, as) {
    if (!ALERTS_ON) return; const T = A.T, sh = T[f.team_h].short_name, sa = T[f.team_a].short_name;
    const mine = (A.live && A.live.rows || []).filter((r) => r.e.team === f.team_h || r.e.team === f.team_a);
    if (o.state === 'pre' && state === 'in' && mine.length && alertPref('kickoff')) { const t = `▶️ Kick-off: ${sh} v ${sa}`, b = `Your players: ${mine.map((r) => r.e.web_name).join(', ')}.`; toast(t, b, 'good'); deskNotify(t, b); }
    const goals = (c.details || []).filter((d) => d.scoringPlay);
    if (o.nG != null && goals.length > o.nG) goals.slice(o.nG).forEach((d) => {
      const who = ((d.athletesInvolved || [])[0] || {}).displayName || '', fw = fmFold(who);
      const isMine = !d.ownGoal && mine.some((r) => { const full = fmFold(r.e.first_name + ' ' + r.e.second_name), last = fmFold(r.e.second_name).split(' ').pop(); return fw === full || (last.length > 2 && fw.endsWith(' ' + last)); });
      if (isMine || !(alertPref('allgoals') || mine.length)) return;
      const t = `⚽ ${sh} ${hs}–${as} ${sa}`, b = `${who}${d.ownGoal ? ' (own goal)' : d.penaltyKick ? ' (penalty)' : ''} ${(d.clock && d.clock.displayValue) || ev.status.displayClock || ''}`.trim();
      toast(t, b, ''); deskNotify(t, b); });
    o.nG = goals.length;
    // half-time and full-time of your matches
    const ph = /HALFTIME/.test((ev.status.type || {}).name || '') ? 'ht' : state === 'post' ? 'ft' : state;
    if (o.ph && o.ph !== ph && (ph === 'ht' || ph === 'ft') && mine.length && alertPref('kickoff')) {
      const t = `${ph === 'ht' ? '⏸️ Half-time' : '🏁 Full-time'}: ${sh} ${hs}–${as} ${sa}`, b = 'Your players: ' + mine.map((r) => `${r.e.web_name} ${r.pts}`).join(', ') + (ph === 'ht' ? ' pts so far.' : ' pts (bonus to come).');
      toast(t, b, ''); deskNotify(t, b); }
    o.ph = ph;
  }
  // Add what the fast feed shows and FPL hasn't counted yet (per player, never below FPL's own numbers)
  function fastApply(A, L) {
    if (!L || !fastOn()) return L; let add = 0;
    (L.fixtures || []).forEach((f) => { const o = FD.fx[f.id]; if (!o || o.h == null) return; const ahead = o.h + o.a > (f.team_h_score || 0) + (f.team_a_score || 0); f._fast = ahead ? { h: o.h, a: o.a } : null; f._clock = o.clock; f._state = o.state;
      // lead time: when the fast feed first showed this score, and when FPL did
      const key = f.id + ':' + (o.h + o.a); if (o.h + o.a > 0 && !FD.first[key]) FD.first[key] = Date.now(); const fk = f.id + ':' + ((f.team_h_score || 0) + (f.team_a_score || 0)); if (FD.first[fk] && !FD.first[fk + 'f']) { FD.first[fk + 'f'] = Date.now(); const lead = Math.round((Date.now() - FD.first[fk]) / 1000); if (lead > 0) FD.lead.push(lead); } });
    L.rows.forEach((r) => {
      r.fast = 0; const f = (L.fixtures || []).find((x) => x.team_h === r.e.team || x.team_a === r.e.team); const o = f && FD.fx[f.id]; if (!o) return;
      const st = r.st || {}, et = r.e.element_type, ev = fastMerge(o.ev && o.ev[r.e.id], o.fmEv && o.fmEv[r.e.id], (o.plAt || 0) >= (o.fmDetAt || 0));
      if (ev) { const dg = Math.max(0, ev.g - (st.goals_scored || 0)), da = Math.max(0, ev.a - (st.assists || 0)), dy = Math.max(0, ev.y - (st.yellow_cards || 0)), dr = Math.max(0, ev.r - (st.red_cards || 0)), dog = Math.max(0, ev.og - (st.own_goals || 0));
        r.fast += dg * FGOAL[et] + da * 3 - dy - 3 * dr - 2 * dog; r.fastWhat = [dg && `${dg} goal${dg > 1 ? 's' : ''}`, da && `${da} assist${da > 1 ? 's' : ''}`, dy && 'yellow', dr && 'red', dog && 'own goal'].filter(Boolean).join(', '); }
      // goals conceded that FPL hasn't counted yet (only while he is on the pitch)
      const conc = f.team_h === r.e.team ? o.a : o.h, onP = ev ? ev.on : (o.starters || o.fmStarters || []).includes(r.e.id);
      if (onP && conc > (st.goals_conceded || 0) && et <= 3) { if (st.clean_sheets && conc >= 1) { r.fast -= FCS[et]; r.fastWhat = (r.fastWhat ? r.fastWhat + ', ' : '') + 'clean sheet gone'; } if (et <= 2) r.fast -= Math.floor(conc / 2) - Math.floor((st.goals_conceded || 0) / 2); }
      if (r.fast) { r.pts += r.fast; add += r.fast * r.mult; }
    });
    L.fastAdd = add; L.pts += add; return L;
  }
  // goal alerts as soon as the fast feed sees them (FPL's own alert for the same event is then skipped)
  function fastAlerts(A) {
    if (!ALERTS_ON || !A.live) return; const T = A.T;
    A.live.rows.forEach((r) => { if (!r.fast || !r.fastWhat) return; const k = r.e.id + ':' + r.fastWhat; if (FD.seen.has(k)) return; FD.seen.add(k);
      const good = r.fast > 0, f = (A.live.fixtures || []).find((x) => x.team_h === r.e.team || x.team_a === r.e.team), o = f && FD.fx[f.id];
      const sc = f && o ? ` (${T[f.team_h].short_name} ${o.h}–${o.a} ${T[f.team_a].short_name}${o.clock ? ' ' + o.clock : ''})` : '';
      const t = `⚡ ${r.e.web_name}: ${r.fastWhat}${sc}`, b = `${good ? '+' : ''}${r.fast * Math.max(1, r.mult)} pts${r.mult > 1 ? ' as captain' : r.mult === 0 ? ' (bench)' : ''}, before FPL has it.`;
      toast(t, b, good ? 'good' : 'bad'); deskNotify(t, b); });
  }
  const fastStatus = () => { if (!fastOn()) return ''; const avg = FD.lead.length ? Math.round(FD.lead.reduce((a, x) => a + x, 0) / FD.lead.length) : null; return FD.at ? `<span class="fastdot"></span>⚡ Fast feed: ${fmOn() ? 3 : 2} live sources · checked ${Math.max(0, Math.round((Date.now() - FD.at) / 1000))} s ago${avg != null ? ` · ${avg} s ahead of FPL on average (${FD.lead.length} goal${FD.lead.length > 1 ? 's' : ''})` : ''}${Object.keys(FD.win).length ? ` · first with a goal: ${Object.entries(FD.win).sort((a, b) => b[1] - a[1]).map(([k, v]) => `${k} ${v}`).join(', ')}` : ''}${FD.err ? ` · <span class="dn">${esc(FD.err)}</span>` : ''}` : '⚡ Fast feed on: starts when a match kicks off'; };
  function paintLiveNow(A) {
    const sec = R.getElementById('s-live'); if (sec) { const tmp = document.createElement('div'); NEWSC = {}; tmp.innerHTML = liveSection(A); SCORES = Object.assign({}, SCORES, NEWSC); const ne = tmp.firstElementChild; ne.hidden = VIEW !== 'live'; sec.replaceWith(ne); }
    const tl = R.getElementById('t-live'); if (tl) { const was = +tl.textContent; tl.textContent = A.live.pts; if (A.live.pts > was) { tl.classList.remove('bump'); void tl.offsetWidth; tl.classList.add('bump'); } }
    const bar = R.getElementById('livebar'); if (bar) bar.innerHTML = liveBar(A.live);
    try { paintLeague(A); } catch (e) {}
  }
  function liveBar(L) {
    if (!L) return '';
    return `<span class="dot ${L.live ? '' : 'still'}"></span><b>GW${L.gw} ${L.live ? 'live' : L.done === L.games ? 'final' : 'so far'}: ${L.pts} pts</b><span>${L.played} played · ${L.toPlay} still to play · bench ${L.bench}${L.provTotal ? ` · includes ${L.provTotal} provisional bonus` : ''}${L.fastAdd ? ` · ⚡ ${L.fastAdd > 0 ? '+' : ''}${L.fastAdd} not in FPL yet` : ''}${L.hit ? ` · −${L.hit} hit` : ''}</span><span class="muted">${L.done}/${L.games} matches finished${L.live ? ` · ${L.live} in progress · updated ${L.at.toLocaleTimeString()}` : ''}</span>`;
  }
  // ---------- v2.7: matchweek view for the live centre ----------
  // ---------- v3.8: live score roll-up (a score that went up since the last refresh rolls in and the card flashes) ----------
  let SCORES = {}, NEWSC = {};
  // v3.65: match details from the free live score feed: clock in seconds, scorers with minutes, stadium, timeline and stats
  const ESPN_SB = 'https://site.api.espn.com/apis/site/v2/sports/soccer/eng.1/scoreboard', ESPN_SUM = 'https://site.api.espn.com/apis/site/v2/sports/soccer/eng.1/summary?event=';
  const MX = {}, MXD = {}, MXS = {}, OPENMX = new Set(), GOALFX = {};
  function mxPut(fxs, ev) {
    const c = (ev.competitions || [])[0]; if (!c) return; const H = c.competitors.find((x) => x.homeAway === 'home'), Aw = c.competitors.find((x) => x.homeAway === 'away'); if (!H || !Aw) return;
    const h = nameTeam(H.team.displayName), a = nameTeam(Aw.team.displayName); const t0 = Date.parse(ev.date);
    const f = fxs.find((x) => x.team_h === h && x.team_a === a && (!x.kickoff_time || !t0 || Math.abs(Date.parse(x.kickoff_time) - t0) < 2 * 864e5)); if (!f) return;
    const st = ev.status || {}, ty = st.type || {}, v = c.venue || {};
    // v3.67: in stoppage time the feed holds clock at 45:00 / 90:00 and puts the added minutes in displayClock ("90'+3'")
    const dm = String(st.displayClock || '').match(/(\d+)'?\s*\+\s*(\d+)/), added = dm ? +dm[2] : 0; let clk = +st.clock || 0;
    if (dm) clk = Math.max(clk, (+dm[1] + added) * 60);
    const pv = MX[f.id]; if (pv && pv.state === 'in' && ty.state === 'in' && pv.period === (+st.period || 0)) { const ext = pv.clock + (Date.now() - pv.at) / 1000; if (ext > clk && ext - clk < 150) clk = ext; }
    MX[f.id] = { eid: ev.id, venue: v.fullName || '', city: (v.address || {}).city || '', clock: clk, added, base: dm ? +dm[1] : 0, period: +st.period || 0, state: ty.state || '', name: ty.name || '', at: Date.now(), att: +c.attendance || 0,
      goals: (c.details || []).filter((d) => d.scoringPlay).map((d) => ({ side: d.team && d.team.id === H.team.id ? 'h' : 'a', who: ((d.athletesInvolved || [])[0] || {}).displayName || '', min: (d.clock && d.clock.displayValue) || '', og: !!d.ownGoal, pen: !!d.penaltyKick })) };
  }
  async function mxLoad(mw) {
    const fxs = FX.filter((f) => f.event === mw && f.kickoff_time); const days = [...new Set(fxs.map((f) => f.kickoff_time.slice(0, 10)))]; let any = false;
    for (const d of days) { const live = fxs.some((f) => f.kickoff_time.startsWith(d) && f.started && !f.finished); if (MXD[d] && Date.now() - MXD[d] < (live ? 60e3 : 36e5)) continue; MXD[d] = Date.now();
      try { const j = await fastGet(ESPN_SB + '?dates=' + d.replace(/-/g, '')); (j.events || []).forEach((ev) => mxPut(fxs, ev)); any = true; } catch (e) {} }
    try { if (await tvLoad(fxs)) any = true; } catch (e) {}
    return any;
  }
  async function mxSummary(fid) { const m = MX[fid]; if (!m) return false; const o = MXS[fid]; const live = m.state === 'in'; if (o && (o.busy || Date.now() - o.at < (live ? 30e3 : 6e5))) return false;
    MXS[fid] = Object.assign(o || {}, { busy: true }); try { MXS[fid] = { at: Date.now(), d: await fastGet(ESPN_SUM + m.eid) }; return true; } catch (e) { MXS[fid] = { at: Date.now(), err: true }; return true; } }
  const pad2 = (n) => String(Math.max(0, Math.floor(n))).padStart(2, '0');
  const clkFmt = (t, p) => { const base = p >= 4 ? 120 : p === 3 ? 105 : p === 2 ? 90 : 45, m = Math.floor(t / 60), sec = pad2(t % 60); return m >= base ? `${base}+${m - base}:${sec}` : `${m}:${sec}`; };
  const cdFmt = (ms) => { if (ms <= 0) return 'Kick-off'; const d = Math.floor(ms / 864e5), h = Math.floor((ms % 864e5) / 36e5), m = Math.floor((ms % 36e5) / 6e4), sec = Math.floor((ms % 6e4) / 1e3); return (d ? d + 'd ' : '') + `${pad2(h)}:${pad2(m)}:${pad2(sec)}`; };
  setInterval(() => { try { R.querySelectorAll('[data-clk]').forEach((el) => { el.textContent = clkFmt(+el.dataset.clk + (Date.now() - +el.dataset.at) / 1000, +el.dataset.per); }); R.querySelectorAll('[data-ko]').forEach((el) => { el.textContent = cdFmt(+el.dataset.ko - Date.now()); }); } catch (e) {} }, 1000);
  // FPL short name for a feed name (falls back to the surname)
  const fplEl = (who, tid) => { const fw = fmFold(who); return BS.elements.find((x) => x.team === tid && (fmFold(x.first_name + ' ' + x.second_name) === fw || fmFold(x.web_name) === fw)) || BS.elements.find((x) => { const l = fmFold(x.second_name).split(' ').pop(); return x.team === tid && l.length > 2 && fw.endsWith(' ' + l); }) || null; };
  // v3.67: a player's name opens his profile
  const whoLink = (who, tid) => { const e = who ? fplEl(who, tid) : null; return e ? `<a class="pn mxpn" href="#" data-pi="1" data-pid="${e.id}">${esc(e.web_name)}</a>` : esc(String(who || '').split(' ').pop()); };
  const fplWho = (who, tid) => { const fw = fmFold(who); const e = BS.elements.find((x) => x.team === tid && (fmFold(x.first_name + ' ' + x.second_name) === fw || fmFold(x.web_name) === fw)) || BS.elements.find((x) => { const l = fmFold(x.second_name).split(' ').pop(); return x.team === tid && l.length > 2 && fw.endsWith(' ' + l); }); return e ? e.web_name : String(who).split(' ').pop(); };
  // v3.68: beIN SPORTS channel numbers per match (Middle East and North Africa listing, cached on the device)
  const TVK = 'elevnTv'; let TV = {}; try { TV = JSON.parse(localStorage.getItem(TVK) || '{}') || {}; } catch (e) { TV = {}; }
  async function tvLoad(fxs) {
    const need = fxs.filter((f) => f.kickoff_time && (!TV[f.id] || (!f.finished && Date.now() - TV[f.id].at > 6 * 36e5))); if (!need.length) return false;
    const days = [...new Set(need.map((f) => new Date(Date.parse(f.kickoff_time)).toISOString().slice(0, 10).replace(/-/g, '')))]; const ms = []; let any = false;
    for (const d of days) { try { const L = await fastGet(FM_API + 'matches?date=' + d); (L.leagues || []).forEach((lg) => { if (lg.primaryId === 47 || lg.id === 47) ms.push(...(lg.matches || [])); }); } catch (e) {} }
    await Promise.all(need.map(async (f) => { const k = Date.parse(f.kickoff_time); const m = ms.find((x) => x.home && x.away && nameTeam(x.home.name) === f.team_h && nameTeam(x.away.name) === f.team_a && Math.abs(Date.parse((x.status || {}).utcTime) - k) < 6 * 36e5); if (!m) return;
      try { const t = await fastGet(FM_API + 'tvlisting?matchId=' + m.id + '&countryCode=ma'); TV[f.id] = { at: Date.now(), ch: (t.channels || []).map((c) => String(c.name || '')).filter(Boolean) }; any = true; } catch (e) {} }));
    if (any) try { localStorage.setItem(TVK, JSON.stringify(TV)); } catch (e) {}
    return any;
  }
  const tvch = (fid, full) => { const ch = (TV[fid] || {}).ch || []; const nums = [...new Set(ch.map((c) => (c.match(/^bein\s*sports?\s*(\d+)$/i) || [])[1]).filter(Boolean))];
    const extra = full ? ch.filter((c) => !/^bein\s*sports?\s*\d+$/i.test(c) && !/connect/i.test(c)).map((c) => c.replace(/^bein\s*(sports?\s*)?/i, '').trim() || c) : [];
    const lbl = nums.length ? nums.map((n) => 'beIN SPORTS ' + n).join(' / ') : 'beIN SPORTS';
    return `<span class="tvch" title="${esc(ch.length ? ch.join(', ') : 'beIN SPORTS (Middle East and North Africa)')}">📺 <b>${lbl}</b>${extra.length ? ` <small class="muted">(${esc(extra.join(', '))})</small>` : ''}</span>`; };
  function mxPanel(A, f) {
    const T = A.T, m = MX[f.id], o = MXS[f.id], ko = f.kickoff_time ? new Date(f.kickoff_time) : null;
    const info = [ko ? '📅 ' + ko.toLocaleString(undefined, { weekday: 'short', day: 'numeric', month: 'short', hour: '2-digit', minute: '2-digit' }) : '', m && m.venue ? `🏟️ ${esc(m.venue)}${m.city ? ', ' + esc(m.city) : ''}` : '', tvch(f.id, true), m && m.added ? `⏱️ +${m.added} added` : '', m && m.att ? `👥 ${m.att.toLocaleString()}` : ''].filter(Boolean).join('<span class="dotsep">·</span>');
    const up = !f.started && !(m && (m.state === 'in' || m.state === 'post'));
    let body = '';
    if (up) body = ko ? `<div class="mxcd"><small>Kick-off in</small><b data-ko="${+ko}">${cdFmt(+ko - Date.now())}</b></div>` : '';
    else if (!m) body = '<p class="muted mxmsg">Match details are not available for this match.</p>';
    else if (!o || o.busy) body = '<p class="muted mxmsg">Loading match details…</p>';
    else if (o.err) body = '<p class="muted mxmsg">Couldn\'t load match details. Tap the match again to retry.</p>';
    else {
      const d = o.d, hid = ((d.header && d.header.competitions && d.header.competitions[0].competitors) || []).find((x) => x.homeAway === 'home');
      const homeId = hid && (hid.team || {}).id; let hs = 0, as = 0;
      const rows = (d.keyEvents || []).map((k) => {
        const ty = (k.type || {}).text || '', min = ((k.clock || {}).displayValue || '').replace(/'$/, '′').replace(/'/g, '′'), side = k.team ? (k.team.id === homeId ? 'h' : 'a') : '';
        const ps = (k.participants || []).map((p) => (p.athlete || {}).displayName || '');
        if (/^Halftime/i.test(ty)) return `<div class="sep">HT ${hs} - ${as}</div>`;
        if (/^End Regular Time|^Full ?Time/i.test(ty)) return `<div class="sep">FT ${hs} - ${as}</div>`;
        let ic = '', txt = '';
        const tid = side === 'h' ? f.team_h : f.team_a;
        if (/^Goal|Penalty - Scored|Own Goal/i.test(ty)) { if (side === 'h') hs++; else if (side === 'a') as++; ic = '⚽'; txt = `<span class="tx"><span><b>${whoLink(ps[0], tid)}</b> (${hs} - ${as})${/own goal/i.test(ty) ? ' og' : /penalty/i.test(ty) ? ' pen' : ''}</span>${ps[1] ? `<small>assist ${whoLink(ps[1], tid)}</small>` : ''}</span>`; }
        else if (/Yellow Card/i.test(ty)) { ic = '<i class="cdy"></i>'; txt = `<b>${whoLink(ps[0], tid)}</b>`; }
        else if (/Red Card/i.test(ty)) { ic = '<i class="cdr"></i>'; txt = `<span class="tx"><b>${whoLink(ps[0], tid)}</b>${/second/i.test(ty) ? '<small>second yellow</small>' : ''}</span>`; }
        else if (/Substitution/i.test(ty)) { ic = '<span class="sub">⇄</span>'; txt = `<span class="tx"><span class="in">${whoLink(ps[0], tid)}</span><span class="out">${whoLink(ps[1], tid)}</span></span>`; }
        else return '';
        const cell = `<span class="ev">${side === 'h' ? txt + ic : ic + txt}</span>`;
        return side === 'h' ? `<div class="h">${cell}</div><span class="mn">${min}</span><div></div>` : `<div></div><span class="mn">${min}</span><div class="a">${cell}</div>`;
      }).filter(Boolean).reverse().join('');
      const tms = (d.boxscore && d.boxscore.teams) || []; const th = tms.find((x) => x.team && x.team.id === homeId) || tms[0], ta = tms.find((x) => x !== th);
      const sv = (t, lbl) => { const x = ((t && t.statistics) || []).find((q) => q.label === lbl || q.name === lbl); return x ? x.displayValue : null; };
      const ST = [['Possession', 'Possession', '%'], ['Shots', 'SHOTS'], ['Shots on target', 'ON GOAL'], ['Corners', 'Corner Kicks'], ['Fouls', 'Fouls'], ['Yellow cards', 'Yellow Cards'], ['Red cards', 'Red Cards'], ['Offsides', 'Offsides'], ['Saves', 'Saves'], ['Passes', 'Passes'], ['Pass accuracy', 'Pass Completion %', 'pct']];
      const stats = th && ta ? ST.map(([l, k, u]) => { let a = sv(th, k), b = sv(ta, k); if (a == null || b == null) return ''; let x = +a, y = +b; if (u === 'pct') { x = Math.round(x * 100); y = Math.round(y * 100); a = x + '%'; b = y + '%'; } else if (u === '%') { const ra = Math.round(x * 100 / ((x + y) || 1)); a = ra + '%'; b = (100 - ra) + '%'; }
        if (l === 'Red cards' && !x && !y) return ''; const tot = x + y || 1; return `<div class="r"><span class="lb">${l}</span><b>${a}</b><span class="bar"><i class="bh" style="width:${(x / tot) * 100}%"></i><i class="ba" style="width:${(y / tot) * 100}%"></i></span><b class="mxv2">${b}</b></div>`; }).join('') : '';
      body = (rows ? `<div class="mxsec"><h4>Events <small class="muted">newest first</small></h4><div class="mxtl">${rows}</div></div>` : '') + (stats ? `<div class="mxsec"><h4>Statistics</h4><div class="mxst"><div class="r hd"><b>${esc(T[f.team_h].short_name)}</b><span></span><b class="mxv2">${esc(T[f.team_a].short_name)}</b></div>${stats}</div></div>` : '') || '<p class="muted mxmsg">No events yet.</p>';
    }
    return `<div class="mxp">${info ? `<div class="mxinfo">${info}</div>` : ''}${body}</div>`;
  }
  function matchesHtml(A) {
    const L = A.live, T = A.T, cur = L.gw, total = (BS.events || []).length || 38;
    const mw = MW == null ? cur : Math.max(1, Math.min(total, MW));
    const kt = (f) => (f.kickoff_time ? Date.parse(f.kickoff_time) : 9e15);
    const MINE = (L.rows || []).filter((r) => r.e);
    const fxs = (mw === cur ? L.fixtures : FX.filter((f) => f.event === mw)).slice().sort((x, y) => kt(x) - kt(y) || x.id - y.id);
    const dFmt = { weekday: 'short', day: 'numeric', month: 'short' };
    const dated = fxs.filter((f) => f.kickoff_time);
    const range = dated.length ? (() => { const a = new Date(dated[0].kickoff_time).toLocaleDateString(undefined, dFmt), b = new Date(dated[dated.length - 1].kickoff_time).toLocaleDateString(undefined, dFmt); return a === b ? a : a + ' – ' + b; })() : 'Dates to be confirmed';
    const chev = (d) => `<svg viewBox="0 0 24 24" width="18" height="18" aria-hidden="true"><path d="${d}" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round"/></svg>`;
    const head = `<div class="mwh"><button class="mwa" type="button" data-mw="-1" aria-label="Previous matchweek" ${mw <= 1 ? 'disabled' : ''}>${chev('M15 5l-7 7 7 7')}</button><div class="mwhc"><b>Matchweek ${mw}</b><span>${range}</span>${(() => { const xi = MINE.filter((r) => r.pos <= 11), m = new Set(fxs.flatMap((f) => MINE.filter((r) => r.e.team === f.team_h || r.e.team === f.team_a).map((r) => r.e.id))); const nx = xi.filter((r) => m.has(r.e.id)).length; return MINE.length ? `<span class="mwyou">You have <b>${m.size}</b> of 15 players in these matches · <b>${nx}</b> of your XI</span>` : ''; })()}${mw !== cur ? `<button class="lnk2" type="button" data-mw="cur">Back to GW${cur}</button>` : ''}</div><button class="mwa" type="button" data-mw="1" aria-label="Next matchweek" ${mw >= total ? 'disabled' : ''}>${chev('M9 5l7 7-7 7')}</button></div>`;
    const ev = (f, side) => { const mx = MX[f.id]; if (mx && mx.goals.length) { const tid = side === 'h' ? f.team_h : f.team_a; return mx.goals.filter((g) => g.side === side).map((g) => `${g.og ? esc(String(g.who).split(' ').pop()) : whoLink(g.who, tid)} <span class="gmin">${esc(String(g.min).replace(/'/g, '′'))}</span>${g.og ? ' (og)' : g.pen ? ' (pen)' : ''}`).join(', '); }
      const st = f.stats || []; const g = (st.find((x) => x.identifier === 'goals_scored') || {})[side] || []; const og = (st.find((x) => x.identifier === 'own_goals') || {})[side === 'h' ? 'a' : 'h'] || []; const nmOf = (x) => { const e = A.E[x.element]; return e ? `<a class="pn mxpn" href="#" data-pi="1" data-pid="${e.id}">${esc(e.web_name)}</a>` : ''; }; return [...g.map((x) => nmOf(x) + (x.value > 1 ? ' ×' + x.value : '')), ...og.map((x) => nmOf(x) + ' (og)')].join(', '); };
    const row = (f) => {
      const fin = f.finished || f.finished_provisional || f._state === 'post', live = (f.started || f._state === 'in') && !fin;
      const mx = MX[f.id], ht = (mx && /HALFTIME/.test(mx.name)) || f._clock === 'HT';
      const clk = ht ? 'HT' : mx && mx.state === 'in' && mx.clock ? `<span data-clk="${mx.clock}" data-per="${mx.period}" data-at="${mx.at}">${clkFmt(mx.clock + (Date.now() - mx.at) / 1000, mx.period)}</span>` : f._clock && f._state === 'in' ? esc(f._clock) : (f.minutes || 0) + '′';
      const left = fin ? 'FT' : live ? `<span class="mwlive">${clk}${f._fast ? ' ⚡' : ''}</span>` : '';
      const hs = f._fast ? f._fast.h : f.team_h_score ?? 0, as = f._fast ? f._fast.a : f.team_a_score ?? 0, was = SCORES[f.id], hUp = was && hs > was[0], aUp = was && as > was[1]; NEWSC[f.id] = [hs, as];
      const pill = f.started || f._state === 'in' || f._state === 'post' ? `<span class="mwsc${hUp || aUp ? ' goal' : ''}"><i class="dg${hUp ? ' up' : ''}">${hs}</i> - <i class="dg${aUp ? ' up' : ''}">${as}</i></span>` : `<span class="mwsc mwv">${f.kickoff_time ? new Date(f.kickoff_time).toLocaleTimeString(undefined, { hour: '2-digit', minute: '2-digit' }) : 'TBC'}</span>`;
      const myIn = MINE.filter((r) => r.e.team === f.team_h || r.e.team === f.team_a);
      // v3.53: each of your players sits under his own club's side, with a count per side
      const chipP = (r) => `<a href="#" data-pi="1" data-pid="${r.e.id}" class="pn mwp${r.mult > 0 ? '' : ' bn'}" title="Open ${esc(r.e.web_name)}'s profile">${pface(r.e).replace('class="picon face"', 'class="picon face mwf"')}<span class="mwnm">${esc(r.e.web_name)}${r.x.is_captain ? ' <i>C</i>' : r.x.is_vice_captain ? ' <i class="v">V</i>' : ''}</span>${mw === cur && f.started ? `<b>${r.pts * Math.max(1, r.mult)}${(() => { const lb = r.provBonus || (!f.finished && r.st && r.st.bonus) || 0; return lb ? `<i class="bpb" title="Live bonus (provisional)">+${lb}</i>` : ''; })()}</b>` : '<span></span>'}</a>`;
      const sideH = (tid) => { const rs = myIn.filter((r) => r.e.team === tid); return rs.length ? rs.map(chipP).join('') : ''; };
      const cnt = (tid) => { const n = myIn.filter((r) => r.e.team === tid).length; return n ? `<span class="mycnt" title="${n} of your players">${n}</span>` : ''; };
      const mineH = myIn.length ? `<div class="mwmy2"><div class="mws2 r">${sideH(f.team_h)}</div><span></span><div class="mws2">${sideH(f.team_a)}</div></div>` : '';
      const eh = f.started ? ev(f, 'h') : '', ea = f.started ? ev(f, 'a') : '';
      const mk = !f.started ? oddsFor(f.team_h, f.team_a, f.kickoff_time) : null; const pc = (x) => Math.round(x * 100) + '%';
      const oddsH = mk ? `<div class="mwodds" title="Bookmaker odds, margin removed, average of ${mk.books} bookmakers. Clean sheet and expected goals are fitted from these prices."><span class="r">Win ${pc(mk.pH)} · CS ${pc(Math.exp(-mk.la))} · xG ${mk.lh.toFixed(1)}</span><span class="c">Draw ${pc(mk.pD)}</span><span>xG ${mk.la.toFixed(1)} · CS ${pc(Math.exp(-mk.lh))} · Win ${pc(mk.pA)}</span></div>` : '';
      const gk = hs + '-' + as; if ((hUp || aUp) && (!GOALFX[f.id] || GOALFX[f.id].k !== gk)) GOALFX[f.id] = { at: Date.now(), k: gk, side: hUp ? 'h' : 'a' };
      const gf = GOALFX[f.id], gel = gf ? Date.now() - gf.at : 1e9; let gblk = '';
      if (gel < 9000) { const gs = gf.side, tid = gs === 'h' ? f.team_h : f.team_a, lg = mx && mx.goals.filter((g) => g.side === gs).pop(); gblk = `<div class="gblk ${gs}" style="animation-delay:-${gel}ms" aria-live="polite"><span class="gball">⚽</span><b>GOAL!</b><span class="gtm">${crest(tid)}${esc(T[tid].name)}</span>${lg && lg.who ? `<small>${esc(lg.og ? String(lg.who).split(' ').pop() + ' (og)' : fplWho(lg.who, tid))} ${esc(String(lg.min).replace(/'/g, '′'))}</small>` : ''}<span class="gsc">${hs} - ${as}</span></div>`; }
      const open = OPENMX.has(f.id); if (open && mw === cur && (f.started || (mx && mx.state === 'in'))) setTimeout(() => mxSummary(f.id).then((ch) => ch && paintMatches(A)), 0);
      const venue = !open && (mx && mx.venue || !fin) ? `<div class="mwinfo">${mx && mx.venue ? `🏟️ ${esc(mx.venue)}` : ''}${!f.started && f.kickoff_time && Date.parse(f.kickoff_time) - Date.now() < 864e5 ? ` <span class="dotsep">·</span> in <b data-ko="${Date.parse(f.kickoff_time)}">${cdFmt(Date.parse(f.kickoff_time) - Date.now())}</b>` : ''}</div><div class="mwtv">${tvch(f.id)}</div>` : '';
      return `<div class="mwr tap ${live ? 'on' : ''}${myIn.length ? ' my' : ''}${open ? ' open' : ''}" data-mx="${f.id}" role="button" tabindex="0" aria-expanded="${open}">${gblk}${left ? `<div class="mws">${left}</div>` : ''}<div class="mwm"><span class="mwt h">${cnt(f.team_h)}<b>${esc(T[f.team_h].name)}</b>${crest(f.team_h)}</span>${pill}<span class="mwt a">${crest(f.team_a)}<b>${esc(T[f.team_a].name)}</b>${cnt(f.team_a)}</span></div>${venue}${oddsH}${eh || ea ? `<div class="mwev"><span class="r">${eh}</span><span></span><span>${ea}</span></div>` : ''}${mineH}${open ? mxPanel(A, f) : ''}</div>`;
    };
    const days = []; fxs.forEach((f) => { const k = f.kickoff_time ? new Date(f.kickoff_time).toLocaleDateString(undefined, dFmt) : 'Date to be confirmed'; let d = days[days.length - 1]; if (!d || d.k !== k) { d = { k, rows: [] }; days.push(d); } d.rows.push(row(f)); });
    setTimeout(() => mxLoad(mw).then((ch) => { if (ch && LASTA === A) paintMatches(A); }), 0);
    return head + (days.length ? days.map((d) => `<section class="mwday"><h3 class="mwdh">${d.k}</h3>${d.rows.join('')}</section>`).join('') : '<p class="mwnone">No matches listed for this matchweek.</p>');
  }
  function paintMatches(A) { const w = R.querySelector('#s-live .mwk'); if (w && A && A.live) w.innerHTML = matchesHtml(A); }
  function nextGwBar(L) {
    if (!L || L.live || L.done < L.games) return '';
    const nx = BS.events.find((e) => e.is_next); if (!nx) return '';
    const ks = FX.filter((f) => f.event === nx.id && f.kickoff_time).map((f) => Date.parse(f.kickoff_time)).sort((a, b) => a - b); if (!ks.length) return '';
    const ms = ks[0] - Date.now(); const d = Math.floor(ms / 864e5), h = Math.floor((ms % 864e5) / 36e5);
    return `<div class="nextgw"><span>Next up</span><b>GW${nx.id}</b> starts ${new Date(ks[0]).toLocaleString(undefined, { weekday: 'short', hour: '2-digit', minute: '2-digit' })}${ms > 0 ? ` · in ${d ? d + 'd ' : ''}${h}h` : ''}</div>`;
  }
  function liveSection(A) {
    const L = A.live; if (!L) return '';
    const T = A.T;
    const nm = (e) => `<a class="pn" href="#" data-pid="${e.id}">${esc(e.web_name)}</a>`;
    const stTag = { playing: '<span class="pill p-live">Playing</span>', done: '<span class="pill p-keep">Finished</span>', waiting: '<span class="pill p-wait">To play</span>', blank: '<span class="pill p-sell">No match</span>' };
    const order = L.rows.slice().sort((a, b) => (b.mult > 0) - (a.mult > 0) || a.pos - b.pos);
    const tr = (r) => { const s = r.st; const role = r.x.is_captain ? ' <span class="pill p-core">C</span>' : r.x.is_vice_captain ? ' <span class="pill p-keep">VC</span>' : '';
      const note = r.subIn ? ' <span class="pill p-live">Auto-sub in</span>' : r.subOut ? ' <span class="pill p-sell">Auto-sub out</span>' : r.capFrom ? ' <span class="pill p-core">Captain (C didn’t play)</span>' : '';
      return `<tr class="${r.mult > 0 ? '' : 'bench'}"><td class="pl">${nm(r.e)}<small>${POS[r.e.element_type]} · ${T[r.e.team].short_name}</small>${role}${note}</td><td>${stTag[r.state]}</td><td class="n">${s.minutes || 0}′</td><td class="n">${s.goals_scored || 0}</td><td class="n">${s.assists || 0}</td><td class="n">${s.clean_sheets || 0}</td><td class="n">${s.saves || 0}</td><td class="n">${s.bps ?? 0}</td><td class="n">${(() => { const unc = r.bonus && (r.provBonus || (r.fs || []).some((f) => f.started && !f.finished)); return r.bonus ? (unc ? `<i class="bpb" title="Live bonus (provisional): confirmed by FPL after the match">+${r.bonus}</i>` : r.bonus) : 0; })()}</td><td class="n"><b>${r.pts}</b>${r.fast ? `<small class="fastp" title="${esc(r.fastWhat || '')}: seen in the live feed, not in FPL yet">⚡${r.fast > 0 ? '+' : ''}${r.fast}</small>` : ''}</td><td class="n">${r.mult > 1 ? '×' + r.mult : r.mult === 0 ? '<small class="muted">bench</small>' : ''}</td><td class="n"><b>${r.pts * r.mult}</b></td></tr>`; };
    const tab = (k, lab) => `<button type="button" role="tab" class="${LIVETAB === k ? 'on' : ''}" aria-selected="${LIVETAB === k}" data-ltab="${k}">${lab}</button>`;
    return `<section class="s" id="s-live"><h2>GW${L.gw} live centre</h2><p class="sub">${fastOn() ? 'Fast feed every 10 s + FPL every 15 s during matches · ⚡ = seen live, not in FPL yet' : 'Updates every 15 s during matches'} · * = provisional bonus</p>${fastOn() ? `<p class="faststrip" id="fastst">${fastStatus()}</p>` : ''}
<div class="livebar" id="livebar2">${liveBar(L)}</div>${nextGwBar(L)}
<div class="seg tabs" role="tablist">${tab('results', 'Matches')}${tab('players', 'My players')}${tab('eo', 'Ownership & threats')}${tab('leagues', 'Mini-league')}${tab('rivals', 'Rival watch')}</div>
<div class="lpanel" data-lpanel="results" ${LIVETAB === 'results' ? '' : 'hidden'}><div class="mwk">${matchesHtml(A)}</div></div>
<div class="lpanel" data-lpanel="players" ${LIVETAB === 'players' ? '' : 'hidden'}>
<div class="alertctl"><button class="try" type="button" id="al-toggle" aria-pressed="${ALERTS_ON}">${ALERTS_ON ? 'Goal alerts: on' : 'Goal alerts: off'}</button>${!isExt() && window.Notification && Notification.permission !== 'granted' ? '<button class="try" type="button" id="al-desk">Allow desktop notifications</button>' : ''}<small class="muted">${isExt() ? 'Desktop notifications come from the extension while Chrome is open.' : ''}</small></div>
<div class="tw"><table><thead><tr><th>Player</th><th>Status</th><th class="n">Mins</th><th class="n">G</th><th class="n">A</th><th class="n">CS</th><th class="n">Saves</th><th class="n">BPS</th><th class="n">Bonus</th><th class="n">Pts</th><th class="n">×</th><th class="n">Counts</th></tr></thead><tbody>${order.map(tr).join('')}</tbody></table></div></div>
<div class="lpanel" data-lpanel="eo" ${LIVETAB === 'eo' ? '' : 'hidden'}><div id="eo-box">${eoHtml(A) || '<p class="muted">Effective ownership appears once your mini-league has loaded.</p>'}</div></div>
<div class="lpanel" data-lpanel="leagues" ${LIVETAB === 'leagues' ? '' : 'hidden'}><div class="lgbox" id="lg-box">${leagueHtml(A)}</div></div>
<div class="lpanel" data-lpanel="rivals" ${LIVETAB === 'rivals' ? '' : 'hidden'}><div id="rv-box">${rivalHtml(A)}</div></div></section>`;
  }
  let MIN5 = null;
  let CURID = null, AUTO = null, LASTA = null, FORM3 = [], LIVETAB = 'results', FIXTAB = 'ticker', MW = null;
  // Refresh only the live parts every 30s, so scroll position and planner changes are kept
  async function liveTick() {
    const A = LASTA; if (!A || !A.live || !document.getElementById(PID)) return;
    try {
      const gw = A.live.gw;
      delete LIVEC[gw];
      const [liveC, fxs, pkCur] = await Promise.all([LIVE(gw), J(`/api/fixtures/?event=${gw}`), J(`/api/entry/${CURID}/event/${gw}/picks/`).catch(() => null)]);
      if (!liveC) throw new Error('no live data');
      const oldL = A.gwCmp.liveC;
      FX = FX.filter((f) => f.event !== gw).concat(fxs);
      A.gwCmp.liveC = liveC; if (pkCur) A.gwCmp.pkCur = pkCur;
      A.live = liveScore(A.cur, A.gwCmp); fastApply(A, A.live);
      if (ALERTS_ON) goalEvents(A, oldL, liveC).filter(([t]) => !(fastOn() && [...FD.seen].some((k) => { const e = A.E[+k.split(':')[0]]; return e && t.includes(e.web_name); }))).forEach(([t, b, tone]) => { toast(t, b, tone); deskNotify(t, b); });
      const sec = R.getElementById('s-live'); if (sec) { const tmp = document.createElement('div'); NEWSC = {}; tmp.innerHTML = liveSection(A); SCORES = Object.assign({}, SCORES, NEWSC); const ne = tmp.firstElementChild; ne.hidden = VIEW !== 'live'; sec.replaceWith(ne); }
      const tl = R.getElementById('t-live'); if (tl) { const was = +tl.textContent; tl.textContent = A.live.pts; if (A.live.pts > was) { tl.classList.remove('bump'); void tl.offsetWidth; tl.classList.add('bump'); } }
      const bar = R.getElementById('livebar'); if (bar) bar.innerHTML = liveBar(A.live);
      paintLeague(A);
    } catch (e) {}
    scheduleAuto(A);
  }
  // v3.60: keep the model's calibration current on every device (once per finished gameweek, in the background)
  let CALIB_BUSY = false;
  function autoCalibrate(A) {
    if (CALIB_BUSY || !BS) return; const last = Math.max(0, ...BS.events.filter((e) => e.finished).map((e) => e.id));
    if (ACC && ACC.v === 3 && ACC.gws && Math.max(...ACC.gws) >= last) return;
    CALIB_BUSY = true;
    runAccuracy().then(() => { CALIB_BUSY = false; const v = A && A.id; if (v && LASTA === A) run(+v, { quiet: true }); }).catch(() => { CALIB_BUSY = false; });
  }
  function scheduleAuto(A) {
    clearTimeout(AUTO); LASTA = A;
    if (!A.live) return;
    const soon = (A.live.fixtures || []).some((f) => !f.started && f.kickoff_time && new Date(f.kickoff_time) - Date.now() < 20 * 60e3 && new Date(f.kickoff_time) - Date.now() > -3 * 36e5);
    if (A.live.live > 0) AUTO = setTimeout(liveTick, 15e3); else if (soon) AUTO = setTimeout(liveTick, 60e3);
    if (fastOn() && !FASTT) FASTT = setTimeout(fastTick, 1500);
  }

  let RUNOPT = {};
  async function run(id, opt) {
    const quiet = !!(opt && opt.quiet); RUNOPT = { quiet, top: out.scrollTop };
    if (!quiet) out.innerHTML = `<section class="s skel"><div class="sk h"></div><div class="skrow"><div class="sk c"></div><div class="sk c"></div><div class="sk c"></div><div class="sk c"></div></div><div class="sk b"></div><div class="sk b s"></div><div class="sk b"></div><p class="muted">Reading live FPL data, the league table and ${'25'} news sources…</p></section>`;
    if (!quiet) $('#nav').innerHTML = '';
    try {
      // Always reload: player prices, injuries, fixtures and scores change during the week
      [BS, FX] = await Promise.all([J('/api/bootstrap-static/'), J('/api/fixtures/'), loadPast().catch(() => null)]);
      Object.keys(LIVEC).forEach((k) => delete LIVEC[k]);
      const nx = BS.events.find((e) => e.is_next); const nearDl = nx && new Date(nx.deadline_time) - Date.now() < 864e5;
      if (!NEWS) NEWS = loadNewsCache();
      if (NEWS && NEWS.items) NEWS.items = NEWS.items.filter(plNews);
      if (!NEWS || (!(opt && opt.cached) && Date.now() - NEWS.at > (nearDl ? 3 : 10) * 60e3)) {
        const ng = (BS.events.find((e) => e.is_next) || BS.events.find((e) => e.is_current) || { id: 1 }).id;
        if (!quiet) out.innerHTML = '<p class="muted">Reading news, leaks and social media…</p>';
        const fresh = await fetchNews(ng).catch(() => ({ ok: 0, total: 0, okBy: {}, feeds: [], items: [] }));
        if (fresh.ok || !NEWS) { NEWS = fresh; NEWS.at = Date.now(); saveNewsCache(NEWS); }
      }
      await withTimeout(fetchOdds(false), 14000).catch(() => null);
      const [entry, hist] = await Promise.all([J(`/api/entry/${id}/`), J(`/api/entry/${id}/history/`)]);
      const cur = BS.events.find((e) => e.is_current);
      let my = null;
      if (meId && +meId === id) { try { my = await J(`/api/my-team/${id}/`); } catch (e) {} }
      let pk = null, gwCmp = null;
      if (cur) {
        pk = await J(`/api/entry/${id}/event/${cur.id}/picks/`).catch(() => null);
        const prevId = cur.id - 1;
        const [liveC, liveP, pkPrev, liveP2] = await Promise.all([
          LIVE(cur.id), prevId > 0 ? LIVE(prevId) : null,
          prevId > 0 ? J(`/api/entry/${id}/event/${prevId}/picks/`).catch(() => null) : null,
          prevId > 1 ? LIVE(prevId - 1) : null,
        ]);
        FORM3 = [liveP2, liveP, liveC];
        // Minutes in the last 5 completed gameweeks (game-time model)
        const lastDone = cur.finished || cur.data_checked ? cur.id : cur.id - 1;
        const g5 = []; for (let g = lastDone; g >= 1 && g5.length < 5; g--) g5.push(g);
        const L5 = await Promise.all(g5.map((g) => LIVE(g)));
        MIN5 = { gws: g5, live: L5 };
        gwCmp = { cur: cur.id, prev: prevId, liveC, liveP, pkCur: pk, pkPrev };
        if (pk && pk.active_chip === 'freehit' && cur.id > 1) {
          const p2 = await J(`/api/entry/${id}/event/${cur.id - 1}/picks/`).catch(() => null);
          if (p2) pk = Object.assign({}, p2, { fhRevert: true });
        }
      }
      let picks = my ? my.picks : pk ? pk.picks : null;
      if (!picks || !picks.length) throw new Error('this team has no squad saved for the current gameweek yet');
      if (!my) picks = await exactSelling(id, entry, hist, picks);
      const A = analyse({ id, entry, hist, my, pk, picks });
      A.gwCmp = gwCmp;
      A.form = {}; BS.elements.forEach((e) => (A.form[e.id] = FORM3.map((L) => (L && L[e.id] ? { p: L[e.id].total_points || 0, m: L[e.id].minutes || 0 } : null))));
      A.loadedAt = new Date();
      A.live = cur ? liveScore(cur, gwCmp) : null; if (A.live) fastApply(A, A.live);
      CURID = id;
      render(A);
      scheduleAuto(A);
      autoCalibrate(A);
    } catch (err) { try { console.error("Elevn run error", err && err.stack); } catch (e) {}
      if (quiet) throw err;
      const nf = /HTTP 404/.test(err.message), off = /fetch|network|Failed/i.test(err.message) && !nf;
      out.innerHTML = `<div class="errbox"><b>${nf ? `No FPL team with ID ${id}` : off ? "Can't reach FPL right now" : `Couldn't load team ${id}`}</b><p>${nf ? 'Check the number: it\'s in the address of your Points page, after /entry/. Or pick a saved team with the people button.' : off ? 'Check your connection, then press ⟳ to try again.' : 'FPL may be updating. Press ⟳ to try again in a minute.'}</p></div>`;
    }
  }

  function analyse({ id, entry, hist, my, pk, picks }) {
    const T = {}; BS.teams.forEach((t) => (T[t.id] = t));
    const E = {}; BS.elements.forEach((e) => (E[e.id] = e));
    const cur = BS.events.find((e) => e.is_current);
    const nxt = BS.events.find((e) => e.is_next);
    const startGw = nxt ? nxt.id : cur ? cur.id : 1;

    // League table from finished fixtures
    const tb = {};
    BS.teams.forEach((t) => (tb[t.id] = { id: t.id, P: 0, W: 0, D: 0, L: 0, GF: 0, GA: 0, Pts: 0, form: [] }));
    FX.filter((f) => f.finished && f.team_h_score != null)
      .sort((a, b) => new Date(a.kickoff_time) - new Date(b.kickoff_time))
      .forEach((f) => {
        const h = tb[f.team_h], a = tb[f.team_a], hs = f.team_h_score, as = f.team_a_score;
        h.P++; a.P++; h.GF += hs; h.GA += as; a.GF += as; a.GA += hs;
        if (hs > as) { h.W++; a.L++; h.Pts += 3; h.form.push('W'); a.form.push('L'); }
        else if (hs < as) { a.W++; h.L++; a.Pts += 3; a.form.push('W'); h.form.push('L'); }
        else { h.D++; a.D++; h.Pts++; a.Pts++; h.form.push('D'); a.form.push('D'); }
      });
    const table = Object.values(tb).sort((a, b) => b.Pts - a.Pts || (b.GF - b.GA) - (a.GF - a.GA) || b.GF - a.GF || T[a.id].name.localeCompare(T[b.id].name));
    table.forEach((r, i) => (r.pos = i + 1));
    const nTeams = table.length;
    const played = Math.max(0, ...table.map((r) => r.P));
    let FDRMODE = 'fpl'; try { FDRMODE = localStorage.getItem('fplAnalystFdrMode2') || 'fpl'; } catch (e) {}   // v3.9: FPL's own rating by default (it tested better on 2026/27 data)
    const tblW = FDRMODE === 'fpl' ? 0 : Math.min(0.45, (played / 38) * 1.6); // trust the table more as the season goes on (unless the accuracy test found FPL's rating alone predicts better)

    // Fixture difficulty: FPL FDR blended with opponent's league position and form
    const fxBy = {};
    FX.filter((f) => f.event && f.event >= startGw).forEach((f) => {
      [true, false].forEach((home) => {
        const t = home ? f.team_h : f.team_a, o = home ? f.team_a : f.team_h;
        const fdr = home ? f.team_h_difficulty : f.team_a_difficulty;
        const tblD = 1 + (4 * (nTeams - tb[o].pos)) / (nTeams - 1);
        const diff = (1 - tblW) * fdr + tblW * tblD;
        (fxBy[t + '-' + f.event] = fxBy[t + '-' + f.event] || []).push({ o, home, fdr, diff, ko: f.kickoff_time });
      });
    });

    // Chip windows decide how far ahead we project
    const usedChips = hist.chips || [];
    const curId = cur ? cur.id : 0;
    const chipsLeft = BS.chips.filter((c) => c.stop_event >= startGw && !usedChips.some((u) => u.name === c.name && u.event >= c.start_event && u.event <= c.stop_event));
    const firstWindow = chipsLeft.filter((c) => c.start_event <= startGw);
    const horizonEnd = Math.min(38, Math.max(startGw + 5, ...firstWindow.map((c) => Math.min(c.stop_event, startGw + 9))));
    const GWS = []; for (let g = startGw; g <= horizonEnd; g++) GWS.push(g);

    // Player model
    const GI = [0, 6, 6, 5, 4];
    const CS = [0, 4, 4, 1, 0];
    // Game time: season share of minutes mixed with the last 5 gameweeks (more weight on recent)
    const teamGames = (team, g) => FX.filter((f) => f.event === g && (f.team_h === team || f.team_a === team)).length;
    // Minutes in the last 2 gameweeks: a player who has barely played lately is probably out of the side
    const last2 = (e) => { if (!MIN5) return null; let mins = 0, games = 0; MIN5.gws.slice(0, 2).forEach((g, i) => { const n = teamGames(e.team, g); if (!n) return; games += n; const L = MIN5.live[i]; mins += (L && L[e.id] ? L[e.id].minutes : 0) || 0; }); return games ? mins / (90 * games) : null; };
    const last5 = (e) => { if (!MIN5) return null; let mins = 0, games = 0; MIN5.gws.forEach((g, i) => { const n = teamGames(e.team, g); if (!n) return; games += n; const L = MIN5.live[i]; mins += (L && L[e.id] ? L[e.id].minutes : 0) || 0; }); return games ? mins / (90 * games) : null; };
    const relC = {};
    const rel = (e) => { if (relC[e.id] != null) return relC[e.id]; const share = Math.min(1, e.minutes / (90 * Math.max(1, tb[e.team].P))); const l5 = last5(e); const mix = l5 == null ? share : 0.6 * l5 + 0.4 * share; const l2 = last2(e); return (relC[e.id] = Math.max(0.08, Math.min(1, mix / 0.85)) * (l2 != null && l2 < 0.2 ? MODEL.gate : 1)); };
    // Rates per 90, pulled toward the position average when minutes are low (this season + 2024/25 at 50% + 2023/24 at 25%; past weight fades as this season builds up)
    const K90 = 5; // equivalent of 5 full matches at the position average
    const regs = BS.elements.filter((e) => e.minutes >= 450);
    const posAvg = (et, f) => { const xs = regs.filter((e) => e.element_type === et); const m = xs.reduce((a, e) => a + e.minutes, 0); return m ? xs.reduce((a, e) => a + f(e), 0) / (m / 90) : 0; };
    const PRIOR = [0, 1, 2, 3, 4].map((et) => et ? { xgi: posAvg(et, (e) => +e.expected_goal_involvements || 0), pts: posAvg(et, (e) => e.total_points), dc: posAvg(et, (e) => +e.defensive_contribution || 0) } : null);
    const shr = (e, curTot, pastTot, prior) => {
      const pw = Math.max(0.3, 1 - e.minutes / 2700), W = [0.5 * pw, 0.25 * pw];
      let num = curTot, n90 = e.minutes / 90;
      pastOf(e).forEach((p, i) => { if (!p) return; num += W[i] * pastTot(p); n90 += W[i] * (p.m / 90); });
      return (num + K90 * prior) / (n90 + K90);
    };
    // ---------- v3.7: 0-100 ratings, percentile within the position (players with 450+ minutes) ----------
    const PX = [0, 1, 2, 3, 4].map((et) => et ? { xg: posAvg(et, (e) => +e.expected_goals || 0), xa: posAvg(et, (e) => +e.expected_assists || 0), sv: posAvg(et, (e) => +e.saves || 0) } : null);
    const RTC = {};
    const rawR = (e) => RTC[e.id] || (RTC[e.id] = {
      fin: shr(e, +e.expected_goals || 0, (p) => p.xg, PX[e.element_type].xg),
      cre: shr(e, +e.expected_assists || 0, (p) => p.xa, PX[e.element_type].xa),
      cs: shr(e, e.clean_sheets || 0, (p) => p.cs, posAvg(e.element_type, (x) => x.clean_sheets || 0)),
      sv: ((+e.saves || 0) + K90 * PX[e.element_type].sv) / (e.minutes / 90 + K90),
      dc: rate(e).dc, min: rel(e), ovr: PR[e.id] ? PR[e.id].slice(0, 5).reduce((a, b) => a + b, 0) : 0,
    });
    const POOL = {}; const pool = (et) => POOL[et] || (POOL[et] = (() => { const xs = BS.elements.filter((e) => e.element_type === et && e.minutes >= 450); return xs.length >= 10 ? xs : BS.elements.filter((e) => e.element_type === et); })());
    const SORTED = {};
    const pctl = (et, k, v) => { const key = et + k; const arr = SORTED[key] || (SORTED[key] = pool(et).map((x) => rawR(x)[k]).sort((a, b) => a - b)); if (!arr.length) return 50; let lo = 0, hi = arr.length; while (lo < hi) { const mid = (lo + hi) >> 1; if (arr[mid] < v) lo = mid + 1; else hi = mid; } return Math.round((lo / arr.length) * 100); };
    const ratings = (e) => { const r = rawR(e), et = e.element_type; const L = [['ovr', 'Overall', 'Projected points over the next 5 gameweeks']];
      L.push(['min', 'Minutes', 'Share of minutes, recent weeks weighted more']);
      if (et === 1) L.push(['cs', 'Clean sheets', 'Clean sheets per 90 minutes'], ['sv', 'Saves', 'Saves per 90 minutes']);
      if (et === 2) L.push(['cs', 'Clean sheets', 'Clean sheets per 90 minutes'], ['dc', 'Defensive actions', 'Clearances, blocks, interceptions and tackles per 90'], ['fin', 'Attack', 'Expected goals per 90']);
      if (et === 3) L.push(['fin', 'Finishing', 'Expected goals per 90'], ['cre', 'Creating', 'Expected assists per 90'], ['dc', 'Defensive actions', 'Defensive actions per 90']);
      if (et === 4) L.push(['fin', 'Finishing', 'Expected goals per 90'], ['cre', 'Creating', 'Expected assists per 90']);
      return L.map(([k, l, d]) => ({ k, l, d, v: k === 'min' ? Math.round(r.min * 100) : pctl(et, k, r[k]) })); };
    const RATE = {};
    const rate = (e) => RATE[e.id] || (RATE[e.id] = {
      xgi: shr(e, +e.expected_goal_involvements || 0, (p) => p.xg + p.xa, PRIOR[e.element_type].xgi),
      pts: shr(e, e.total_points, (p) => p.p, PRIOR[e.element_type].pts),
      dc: e.defensive_contribution != null ? ((+e.defensive_contribution || 0) + K90 * PRIOR[e.element_type].dc) / (e.minutes / 90 + K90) : 0,
    });
    // Defensive contribution (2025/26 rule): 2 pts when a defender reaches 10 CBIT, or a midfielder/forward reaches 12 CBIRT, in a match
    const phi = (z) => { const t = 1 / (1 + 0.2316419 * Math.abs(z)), d = 0.3989423 * Math.exp(-z * z / 2); const p = d * t * (0.3193815 + t * (-0.3565638 + t * (1.781478 + t * (-1.821256 + t * 1.330274)))); return z > 0 ? 1 - p : p; };
    const dcEV = (e) => { if (e.element_type === 1) return 0; const lam = rate(e).dc * 0.95; if (lam <= 0) return 0; const thr = e.element_type === 2 ? 10 : 12; return 2 * (1 - phi((thr - 0.5 - lam) / Math.sqrt(1.6 * lam))); };
    const base = (e) => {
      const r = rel(e);
      const R2 = rate(e);
      const xgi = R2.xgi;
      const cs90 = e.clean_sheets_per_90 != null ? +e.clean_sheets_per_90 : (e.minutes ? e.clean_sheets / (e.minutes / 90) : 0);
      const under = (2 + xgi * GI[e.element_type] + cs90 * CS[e.element_type] + (e.element_type === 1 ? 0.6 : 0) + MODEL.dc * dcEV(e)) * r;
      // Set pieces: past returns already reflect them, so this is a small extra for the designated taker
      const spBoost = (e.penalties_order === 1 ? 0.3 : e.penalties_order === 2 ? 0.05 : 0) + (e.direct_freekicks_order === 1 ? 0.08 : 0) + (e.corners_and_indirect_freekicks_order === 1 ? 0.1 : 0);
      return MODEL.wF * +e.form + MODEL.wP * R2.pts * r + MODEL.wU * under + spBoost * r;
    };
    // Match news headlines to players (full name, or a distinctive web name)
    const NM = {};
    const webCount = {}; BS.elements.forEach((e) => (webCount[e.web_name] = (webCount[e.web_name] || 0) + 1));
    const reEsc = (s) => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    BS.elements.filter((e) => e.minutes > 0 || e.status !== 'a').forEach((e) => {
      const keys = [`${e.first_name} ${e.second_name}`]; const lastSn = e.second_name.split(' ').pop();
      if (e.second_name.includes(' ')) keys.push(`${e.first_name.split(' ')[0]} ${lastSn}`);
      let bare = '';
      if (e.web_name.length >= 4 && webCount[e.web_name] === 1) {
        // v3.43: a bare surname does not count when it follows another player's first name ("Bruno Fernandes" is not Mateus Fernandes)
        const others = BS.elements.filter((o) => o.id !== e.id && (o.second_name.split(' ').pop() === e.web_name || o.web_name.replace(/^.*\./, '') === e.web_name)).map((o) => o.first_name.split(' ')[0]);
        bare = (others.length ? others.map((f) => `(?<!${reEsc(f)} )`).join('') : '') + reEsc(e.web_name);
      }
      const re = new RegExp('(^|[^\\p{L}])(' + keys.map(reEsc).concat(bare ? [bare] : []).join('|') + ')($|[^\\p{L}])', 'iu');
      const hits = NEWS.items.filter((it) => re.test(it.text));
      if (!hits.length) return;
      // v3.17: only the words next to his name count (long posts and lists mention many players with no full stops)
      const sentence = (it) => { const src = it.text.replace(/\s+/g, ' '); const out = []; const g = new RegExp(re.source, 'giu'); let m; let n = 0;
        while ((m = g.exec(src)) && n++ < 4) { let a = Math.max(0, m.index - 90), b = Math.min(src.length, m.index + m[0].length + 90); const pre = src.slice(a, m.index), post = src.slice(m.index, b);
          const ps = pre.search(/[.!?|•\n][^.!?|•\n]*$/); const pe = post.search(/[.!?|•\n]/); out.push((ps >= 0 ? pre.slice(ps + 1) : pre) + (pe > 0 ? post.slice(0, pe) : post)); }
        return out.join(' … ') || it.title; };
      let neg = 0, pos = 0;
      const W = { news: 1, leak: 1.2, social: 0.6 }; // leaks weigh more, community posts less
      // v3.50: a worry older than his last Premier League match does not count if he then played 60+ minutes
      const lastLive = MIN5 && MIN5.live && MIN5.live[0], lastMin = lastLive && lastLive[e.id] ? lastLive[e.id].minutes : null;
      const lastKo = MIN5 ? Math.max(0, ...FX.filter((f) => f.event === MIN5.gws[0] && (f.team_h === e.team || f.team_a === e.team) && f.kickoff_time).map((f) => +new Date(f.kickoff_time))) : 0;
      const tagged = hits.map((it) => { const s = sentence(it); const tn = toneOf(s); let t = tn.t; const inc = tn.inc; const stale = t === 'neg' && lastKo && lastMin >= 60 && !isNaN(it.date) && it.date < lastKo; if (stale) t = 'neutral'; if (t === 'neg') neg += W[it.kind] || 1; if (t === 'pos') pos += W[it.kind] || 1; const ageH = isNaN(it.date) ? 99 : (Date.now() - it.date) / 36e5; return Object.assign({}, it, { tone: t, incident: inc && t === 'neg', strong: tn.strong && t === 'neg', stale, ageH }); });
      const team = (T[e.team].name || '').toLowerCase();
      const negSrc = new Set(tagged.filter((h) => h.tone === 'neg' && h.ageH <= 72).map((h) => (h.src || h.link || '').toLowerCase())); const confirmed = e.status !== 'a' || negSrc.size >= 2 || tagged.some((h) => h.strong && h.ageH <= 72);
      NM[e.id] = { hits: tagged, neg, pos, confirmed, negSrc: negSrc.size, signal: neg > pos && neg >= 0.9 && confirmed ? 'neg' : pos > neg && pos > 0 ? 'pos' : 'neutral', team, leak: tagged.some((h) => h.kind === 'leak'), social: tagged.some((h) => h.kind === 'social') };
    });
    const newsF = (e, k) => {
      const n = NM[e.id]; if (!n || k > 1) return 1;
      if (n.signal === 'neg' && e.status === 'a') return k === 0 ? 0.75 : 0.88; // news ahead of FPL's flag
      if (n.signal === 'pos' && e.status === 'd') return 1.25;
      return 1;
    };
    const avail = (e, k) => Math.min(1, availRaw(e, k) * newsF(e, k));
    const availRaw = (e, k) => {
      if (e.status === 'a') return 1;
      if (e.status === 'u' || e.status === 'n') return 0;
      const c = e.chance_of_playing_next_round;
      if (c != null) return Math.min(1, c / 100 + 0.25 * k);
      return k < 2 ? 0 : 0.5;
    };
    const PR = {};
    let calOn = true; try { calOn = localStorage.getItem('fplAnalystCalib') !== 'off'; } catch (e) {}
    const CAL = calOn && ACC && ACC.calib ? ACC.calib : null;
    // ===== v3.45 model =====
    // (1) Team strength: Poisson attack / defence ratings fitted to this season's results (Maher / Dixon-Coles style),
    //     recent matches weighted more, pulled toward FPL's own team strength ratings early in the season.
    const RES = FX.filter((f) => f.finished && f.team_h_score != null);
    const lastEv = Math.max(1, ...RES.map((f) => f.event || 1));
    const wOf = (f) => Math.pow(0.5, (lastEv - (f.event || lastEv)) / 8);
    let sH = 0, sA = 0, sW = 0; RES.forEach((f) => { const w = wOf(f); sH += w * f.team_h_score; sA += w * f.team_a_score; sW += w; });
    const muH = sW ? sH / sW : 1.5, muA = sW ? sA / sW : 1.2, muAvg = (muH + muA) / 2;
    // prior: FPL's attack / defence strengths when published, else its 1-5 overall strength, else neutral
    const num = (x) => (Number.isFinite(+x) ? +x : 0);
    const sAtt = (t) => (num(t.strength_attack_home) + num(t.strength_attack_away)) / 2, sDef = (t) => (num(t.strength_defence_home) + num(t.strength_defence_away)) / 2, sOv = (t) => (num(t.strength_overall_home) + num(t.strength_overall_away)) / 2;
    const useAD = BS.teams.every((t) => sAtt(t) > 0 && sDef(t) > 0), useOv = BS.teams.every((t) => sOv(t) > 0);
    const mA = useAD ? BS.teams.reduce((a, t) => a + sAtt(t), 0) / BS.teams.length : 1, mD = useAD ? BS.teams.reduce((a, t) => a + sDef(t), 0) / BS.teams.length : 1, mO = useOv ? BS.teams.reduce((a, t) => a + sOv(t), 0) / BS.teams.length : 0;
    const ATT = {}, DEF = {}, ATT0 = {}, DEF0 = {};
    BS.teams.forEach((t) => { ATT0[t.id] = useAD ? Math.pow(sAtt(t) / mA, 2.5) : useOv ? Math.pow(1.15, sOv(t) - mO) : 1; DEF0[t.id] = useAD ? Math.pow(mD / sDef(t), 2.5) : useOv ? Math.pow(1.15, mO - sOv(t)) : 1; ATT[t.id] = ATT0[t.id]; DEF[t.id] = DEF0[t.id]; });
    const KP = 4; // prior = 4 matches' worth of evidence
    for (let it = 0; it < 25; it++) {
      const na = {}, da = {}, nd = {}, dd = {}; BS.teams.forEach((t) => { na[t.id] = KP * ATT0[t.id]; da[t.id] = KP; nd[t.id] = KP * DEF0[t.id]; dd[t.id] = KP; });
      RES.forEach((f) => { const w = wOf(f), h = f.team_h, a = f.team_a;
        na[h] += w * f.team_h_score; da[h] += w * muH * DEF[a]; na[a] += w * f.team_a_score; da[a] += w * muA * DEF[h];
        nd[h] += w * f.team_a_score; dd[h] += w * muA * ATT[a]; nd[a] += w * f.team_h_score; dd[a] += w * muH * ATT[h]; });
      let ma = 0, md = 0; BS.teams.forEach((t) => { ATT[t.id] = na[t.id] / da[t.id]; DEF[t.id] = nd[t.id] / dd[t.id]; ma += ATT[t.id]; md += DEF[t.id]; });
      ma /= BS.teams.length; md /= BS.teams.length; BS.teams.forEach((t) => { ATT[t.id] /= ma; DEF[t.id] /= md; });
    }
    const lam0 = (t, o, home) => (home ? muH : muA) * ATT[t] * DEF[o];
    // v3.54: where bookmaker odds exist for the match, half of the expected goals come from the market
    let oddsUsed = 0;
    const lam = (t, o, home, ko) => { const m = home ? oddsFor(t, o, ko) : oddsFor(o, t, ko); const own = lam0(t, o, home); if (!m) return own; oddsUsed++; return (1 - ODDS_W) * own + ODDS_W * (home ? m.lh : m.la); };
    const pois = (l, k) => { let p = Math.exp(-l); for (let i = 1; i <= k; i++) p *= l / i; return p; };
    const gcPen = (l) => { let s = 0; for (let k = 2; k <= 10; k++) s += Math.floor(k / 2) * pois(l, k); return s; };
    // (2)(3) Player points from underlying numbers: chance of 60+ minutes, xG and xA per 90 pulled toward the position
    //     average (with past seasons), scaled by how many goals his team should score in that fixture.
    const BON = [0, 1, 2, 3, 4].map((et) => et ? posAvg(et, (e) => e.bonus || 0) : 0);
    const SV = posAvg(1, (e) => +e.saves || 0);
    const COMP = {}, RAW = {};
    const spX = (e) => (e.penalties_order === 1 ? 0.12 : 0) + (e.direct_freekicks_order === 1 ? 0.03 : 0);
    BS.elements.forEach((e) => {
      const et = e.element_type, g90 = shr(e, +e.expected_goals || 0, (p) => p.xg, PX[et].xg) + spX(e), a90 = shr(e, +e.expected_assists || 0, (p) => p.xa, PX[et].xa);
      const b90 = ((e.bonus || 0) + K90 * BON[et]) / (e.minutes / 90 + K90), s90 = et === 1 ? ((+e.saves || 0) + K90 * SV) / (e.minutes / 90 + K90) : 0;
      const m0 = rel(e), dc = dcEV(e), tAvg = muAvg * ATT[e.team];
      const old = base(e) * (CAL ? CAL[et] || 1 : 1);
      COMP[e.id] = []; RAW[e.id] = [];
      PR[e.id] = GWS.map((g, k) => { const fs = fxBy[e.team + '-' + g] || []; const av = avail(e, k); let tot = 0, raw = 0; const cs = [];
        fs.forEach((f) => { const lf = lam(e.team, f.o, f.home, f.ko), la = lam(f.o, e.team, !f.home, f.ko), r = lf / tAvg, m = m0 * av;
          const p60 = Math.min(1, m * 1.08), psub = Math.max(0, Math.min(1, m * 1.25) - p60) * 0.6, eg = g90 * m * r, ea = a90 * m * r;
          const v = 2 * p60 + psub + eg * GI[et] + ea * 3 + p60 * Math.exp(-la) * CS[et] - (et <= 2 ? p60 * gcPen(la) : 0) + (et === 1 ? s90 * m * (la / muAvg) / 3 : 0) + dc * p60 + b90 * m * (0.7 + 0.3 * r);
          cs.push({ p60, psub, eg, ea, la, et, sv: s90 * m * (la / muAvg), dc: dc * p60, bon: b90 * m * (0.7 + 0.3 * r), key: e.team + '-' + g + '-' + f.o });
          raw += v; tot += 0.75 * v + 0.25 * old * (1 + (3 - f.diff) * 0.13 + (f.home ? 0.03 : -0.03)) * av; });
        COMP[e.id].push(cs); RAW[e.id].push(raw); return tot; });
    });
    // (7) Learning loop: every run stores this gameweek's raw projections; once a gameweek is played, the real points
    //     correct the model per position (only part of the gap, and within ±15%, so one odd week can't swing it).
    const PLOG_KEY = 'fplAnalystProjLog'; let PLOG = {}; try { PLOG = JSON.parse(localStorage.getItem(PLOG_KEY) || '{}') || {}; } catch (e) {}
    if (!PLOG[startGw]) { const pp = {}; BS.elements.forEach((e) => { const v = RAW[e.id][0]; if (v >= 1) pp[e.id] = Math.round(v * 10); }); PLOG[startGw] = pp; const ks = Object.keys(PLOG).map(Number).sort((a, b) => b - a); ks.slice(10).forEach((k) => delete PLOG[k]); try { localStorage.setItem(PLOG_KEY, JSON.stringify(PLOG)); } catch (e) {} }
    const CAL4 = [0, 1, 1, 1, 1], CALN = [0, 0, 0, 0, 0];
    if (MIN5) MIN5.gws.forEach((g, i) => { const L = MIN5.live[i], lg = PLOG[g]; if (!L || !lg) return; const sp = [0, 0, 0, 0, 0], sa = [0, 0, 0, 0, 0];
      Object.entries(lg).forEach(([id, v]) => { const e = E[id], st = L[id]; if (!e || !st) return; sp[e.element_type] += v / 10; sa[e.element_type] += st.total_points || 0; });
      [1, 2, 3, 4].forEach((t) => { if (sp[t] > 20) { CAL4[t] *= Math.pow(sa[t] / sp[t], 0.35); CALN[t]++; } }); });
    [1, 2, 3, 4].forEach((t) => { CAL4[t] = Math.max(0.85, Math.min(1.15, CAL4[t])); });
    BS.elements.forEach((e) => { const c = CAL4[e.element_type]; if (c !== 1) PR[e.id] = PR[e.id].map((v) => v * c); });
    // (6) Monte Carlo: play the gameweek many times. Goals against are shared by team-mates, so clean sheets move together.
    const rP = (l) => { if (l <= 0) return 0; let L = Math.exp(-l), k = 0, p = 1; do { k++; p *= Math.random(); } while (p > L && k < 12); return k - 1; };
    const simulate = (ids, capId, g, opt) => { opt = opt || {}; const k = g - startGw, N = opt.n || 2500, mult = opt.tc ? 3 : 2; const out = new Float64Array(N);
      const parts = ids.map((id) => ({ id, cs: (COMP[id] && COMP[id][k]) || [], c: CAL4[(E[id] || {}).element_type || 3] }));
      for (let n = 0; n < N; n++) { const GA = {}; let tot = 0;
        parts.forEach((pl) => { let pts = 0; pl.cs.forEach((c) => { const u = Math.random(); const s60 = u < c.p60, sub = !s60 && u < c.p60 + c.psub; if (!s60 && !sub) return;
          const pr = c.p60 + c.psub * 0.35 || 1; pts += s60 ? 2 : 1; pts += rP(c.eg / pr) * GI[c.et] + rP(c.ea / pr) * 3;
          if (GA[c.key] == null) GA[c.key] = rP(c.la); const ga = GA[c.key];
          if (s60) { if (ga === 0) pts += CS[c.et]; if (c.et <= 2) pts -= Math.floor(ga / 2); if (c.et !== 1 && Math.random() < c.dc / 2 / Math.max(.05, c.p60)) pts += 2; if (c.et === 1) pts += Math.floor(rP(c.sv / Math.max(.05, c.p60)) / 3); }
          pts += Math.min(3, rP(c.bon / pr)); });
          pts *= pl.c; tot += pl.id === capId ? pts * mult : pts; });
        out[n] = tot; }
      const s = Array.from(out).sort((a, b) => a - b), q = (x) => s[Math.min(N - 1, Math.floor(x * N))];
      return { mean: s.reduce((a, b) => a + b, 0) / N, p10: q(0.1), p50: q(0.5), p90: q(0.9) }; };
    const MODEL4 = { ATT, DEF, muH, muA, CAL4, CALN, simulate, COMP };
    const P = (e, g) => PR[e.id][g - startGw] || 0;
    const S5 = (e) => PR[e.id].slice(0, 5).reduce((a, b) => a + b, 0);

    // Positional percentile on 5-GW projection
    const pct = {};
    [1, 2, 3, 4].forEach((t) => {
      const arr = BS.elements.filter((e) => e.element_type === t && e.minutes > 0).map(S5).sort((a, b) => b - a);
      pct[t] = arr[Math.floor(arr.length * 0.08)] || 99;
    });

    // Squad
    const sq = picks.map((p) => ({ e: E[p.element], p, sell: p.selling_price != null ? p.selling_price : E[p.element].now_cost }));
    const inSq = new Set(sq.map((s) => s.e.id));
    const club = {}; sq.forEach((s) => (club[s.e.team] = (club[s.e.team] || 0) + 1));
    const eh = pk ? pk.entry_history : null;
    const bank = my ? my.transfers.bank : eh ? eh.bank : entry.last_deadline_bank || 0;
    const sellCalc = !my && picks.some((p) => p.sellCalc);
    const value = my ? my.transfers.value : sellCalc ? picks.reduce((a, p) => a + p.selling_price, 0) : eh ? eh.value - eh.bank : entry.last_deadline_value;

    // Free transfers
    let ft, ftExact = false;
    if (my && my.transfers && my.transfers.limit != null) { ft = Math.max(0, my.transfers.limit - my.transfers.made); ftExact = true; }
    else {
      ft = 1;
      const hc = hist.current || [];
      // FPL rules: +1 free transfer per gameweek (max 1 + max_extra_free_transfers). A Wildcard or Free Hit week
      // keeps the saved transfers but adds no new one. Any points hit means every free transfer was used.
      const cap = 1 + ((BS.game_settings && BS.game_settings.max_extra_free_transfers) || 4);
      for (let g = (entry.started_event || 1) + 1; g <= curId; g++) {
        const h = hc.find((x) => x.event === g); const chip = usedChips.find((c) => c.event === g);
        if (chip && (chip.name === 'wildcard' || chip.name === 'freehit')) continue;
        ft = h && h.event_transfers_cost > 0 ? 0 : Math.max(0, ft - (h ? h.event_transfers : 0));
        ft = Math.min(cap, ft + 1);
      }
    }

    // Best legal XI (1 GK, 3+ DEF, 2+ MID, 1+ FWD) from any list of {e} for gameweek g
    const bestXIof = (list, g) => {
      const by = (t) => list.filter((s) => s.e.element_type === t).sort((a, b) => P(b.e, g) - P(a.e, g));
      const gk = by(1), d = by(2), m = by(3), f = by(4);
      const xi = [gk[0], ...d.slice(0, 3), ...m.slice(0, 2), ...f.slice(0, 1)].filter(Boolean);
      const rest = [...d.slice(3), ...m.slice(2), ...f.slice(1)].sort((a, b) => P(b.e, g) - P(a.e, g));
      xi.push(...rest.slice(0, Math.max(0, 11 - xi.length)));
      const benchOut = [...gk.slice(1), ...rest.filter((s) => !xi.includes(s))].filter(Boolean);
      const sum = xi.reduce((a, s) => a + P(s.e, g), 0);
      const cap = xi.reduce((a, s) => Math.max(a, P(s.e, g)), 0);
      return { xi, bench: benchOut, sum, cap, benchSum: benchOut.reduce((a, s) => a + P(s.e, g), 0) };
    };
    const bestXI = (g) => bestXIof(sq, g);
    // Projected points of a squad over the next 5 GWs (best XI each week + captain)
    const squad5 = (list) => GWS.slice(0, 5).reduce((a, g) => { const b = bestXIof(list, g); return a + b.sum + b.cap; }, 0);
    const now = bestXI(startGw);
    const starters = new Set(now.xi.map((s) => s.e.id));

    const CONV = 2.5; // minimum projected gain over 5 GWs before a transfer is advised
    // Transfer search: up to 8 candidates per player, then give each suggestion its own target
    const moves = sq.map((s) => {
      const budget = s.sell + bank;
      const cands = BS.elements
        .filter((c) => c.element_type === s.e.element_type && !inSq.has(c.id) && c.now_cost <= budget && (c.team === s.e.team || (club[c.team] || 0) < 3) && avail(c, 0) > 0.8)
        .map((c) => ({ c, v: S5(c) }))
        .sort((a, b) => b.v - a.v)
        .slice(0, 8);
      const mine = S5(s.e);
      const gain = cands.length ? cands[0].v - mine : 0;
      const w = starters.has(s.e.id) || avail(s.e, 0) < 0.5 ? 1 : 0.45;
      return { s, cands, mine, gain, w, score: gain * w, rawScore: gain * w };
    }).sort((a, b) => b.score - a.score);
    const usedT = new Set();
    moves.forEach((m) => {
      const pool = m.cands.filter((c) => !usedT.has(c.c.id));
      m.cands = pool.slice(0, 3);
      if (pool.length) usedT.add(pool[0].c.id);
      m.gain = m.cands.length ? m.cands[0].v - m.mine : 0;
      m.score = m.gain * m.w;
    });
    moves.sort((a, b) => b.score - a.score);
    const moveOf = {}; moves.forEach((m) => (moveOf[m.s.e.id] = m));

    // Differentials: owned by under 10% of managers, nailed, available, with strong next-5 projections
    const own = (e) => parseFloat(e.selected_by_percent) || 0;
    const diffs = BS.elements
      .filter((e) => own(e) < 10 && avail(e, 0) > 0.8 && rel(e) >= 0.6 && e.minutes >= 270)
      .map((e) => ({ e, v: S5(e) }))
      .sort((a, b) => b.v - a.v);
    const diffSet = new Set(diffs.slice(0, 40).map((d) => d.e.id));
    const isDiff = (e) => diffSet.has(e.id);

    const verdict = (s) => {
      const m = moveOf[s.e.id];
      if (avail(s.e, 0) === 0) return ['out', 'Out'];
      if (m.rawScore >= 5) return ['sell', 'Sell'];
      if (m.rawScore >= 2.5) return ['up', 'Upgrade'];
      if (S5(s.e) >= pct[s.e.element_type]) return ['core', 'Core'];
      return ['keep', 'Keep'];
    };

    // Captaincy
    const caps = now.xi.slice().sort((a, b) => P(b.e, startGw) - P(a.e, startGw)).slice(0, 3);

    // Chips
    const chipPlans = chipsLeft.map((c) => {
      const from = Math.max(c.start_event, startGw), to = Math.min(c.stop_event, horizonEnd);
      const locked = c.start_event > startGw;
      const rows = [];
      for (let g = from; g <= to; g++) {
        const bx = bestXI(g);
        const blanks = sq.filter((s) => !(fxBy[s.e.team + '-' + g] || []).length).length;
        const doubles = sq.filter((s) => (fxBy[s.e.team + '-' + g] || []).length > 1).length;
        let score;
        if (c.name === 'bboost') score = bx.benchSum;
        else if (c.name === '3xc') score = Math.max(...bx.xi.map((s) => P(s.e, g)));
        else if (c.name === 'freehit') score = -bx.sum + blanks * 3;
        else score = 0;
        rows.push({ g, score, bx, blanks, doubles });
      }
      const best = rows.length ? rows.slice().sort((a, b) => b.score - a.score)[0] : null;
      return { c, from, to, locked, rows, best };
    });
    const sellCount = moves.filter((m) => m.rawScore >= 4).length + sq.filter((s) => avail(s.e, 0) === 0).length;

    // v3.11: four rating axes for the player page radar (percentiles within the position)
    const radar = (e) => { const r = rawR(e), et = e.element_type; return { fin: et === 1 ? 0 : pctl(et, 'fin', r.fin), cre: et === 1 ? 0 : pctl(et, 'cre', r.cre), def: et <= 2 ? pctl(et, 'cs', r.cs) : pctl(et, 'dc', r.dc), min: Math.round(r.min * 100), ovr: pctl(et, 'ovr', r.ovr) }; };
    return { MODEL4, radar, ratings, CONV, rate, dcEV, sellCalc, bestXIof, squad5, diffs, isDiff, own, rel, NM, id, entry, hist, my, pk, cur, nxt, startGw, GWS, T, E, tb, table, fxBy, P, S5, sq, bank, value, ft, ftExact, now, caps, moves, verdict, chipPlans, sellCount, avail, club, picks };
  }

  function fixChips(A, team, n, from) {
    const out = []; const g1 = from || A.startGw;
    for (let g = g1; g < g1 + n && g <= 38; g++) {
      const fs = A.fxBy[team + '-' + g] || [];
      if (!fs.length) { out.push(`<span class="f dx" title="GW${g}: no fixture">–</span>`); continue; }
      fs.forEach((f) => {
        const nm = A.T[f.o].short_name;
        out.push(`<span class="f d${Math.max(1, Math.min(5, Math.round(f.diff)))}" title="GW${g} ${f.home ? 'home' : 'away'} vs ${esc(A.T[f.o].name)} (difficulty ${f1(f.diff)})">${nm}${ha(f.home)}</span>`);
      });
    }
    return `<span class="fx">${out.join('')}</span>`;
  }
  // Pitch card strip: opponent code on top, coloured bar with H or A underneath (colour = difficulty)
  function haStrip(A, team, n, from) {
    const out = []; const g1 = from || A.startGw;
    for (let g = g1; g < g1 + n && g <= 38; g++) {
      const fs = A.fxBy[team + '-' + g] || [];
      if (!fs.length) { out.push(`<span class="hs" title="GW${g}: no match"><b>–</b><i class="hb dx">–</i></span>`); continue; }
      fs.forEach((f) => out.push(`<span class="hs" title="GW${g}: ${f.home ? 'home' : 'away'} vs ${esc(A.T[f.o].name)} (difficulty ${f1(f.diff)})"><b>${A.T[f.o].short_name}</b><i class="hb d${Math.max(1, Math.min(5, Math.round(f.diff)))}">${f.home ? 'H' : 'A'}</i></span>`));
    }
    return out.join('');
  }

  let LAST = null;
  const drawer = $('#drawer');
  const onAct = (ev) => {
    const t = ev.target.closest ? ev.target : null; if (!t) return;
    const a = t.closest('a.pn');
    // v3.11: in the transfer planner (and Market / Head to head) a player name opens the full player page
    if (a) { ev.preventDefault(); if (a.closest('#s-planner, #sheetbody, #qa, .fx2')) openPlayerPage(+a.dataset.pid); else openProfile(+a.dataset.pid); return; }
    const vw = t.closest('[data-view]'); if (vw) { ev.preventDefault(); showView(vw.dataset.view); return; }
    const cd = t.closest('[data-card]'); if (cd && !cd.hasAttribute('data-with')) { if (PLAN && PLAN.sel) { PLAN.sel = null; renderPlanner(); return; } openQuick(+cd.dataset.card, cd); return; }
    const pr = t.closest('[data-prof]'); if (pr) { openProfile(+pr.dataset.prof); return; }
    const dot = t.closest('[data-dot]'); if (dot) { slideTo(dot.closest('[data-slider]'), +dot.dataset.dot); return; }
    const tb = t.closest('[data-tab]'); if (tb) { PLAN.tab = tb.dataset.tab; renderPlanner(); return; }
    const aps = t.closest('[data-apst]'); if (aps) { PLAN.autoStyle = aps.dataset.apst; PLAN.auto = null; renderPlanner(); return; }
    if (t.closest('#ap-run')) { PLAN.auto = { busy: true }; renderPlanner(); setTimeout(() => { try { const st0 = PLAN.autoStyle || 'steady'; PLAN.auto = autoPlan(st0); const other = autoPlan(st0 === 'steady' ? 'climber' : 'steady'); const sig = (r) => r.path.map((w) => w.moves.map((m) => m.o.id + '>' + m.i.id).join(',')).join('|'); PLAN.auto.same = sig(other) === sig(PLAN.auto); PLAN.auto.otherTotal = other.total; } catch (er) { PLAN.auto = null; PLAN.msg = 'The auto plan could not be built: ' + er.message; } renderPlanner(); }, 30); return; }
    if (t.closest('#ap-apply')) { applyAuto(); return; }
    const pf = t.closest('[data-pf]'); if (pf) { PLAN.pf = +pf.dataset.pf; renderPlanner(); return; }
    if (t.closest('#pl-best')) { planBest(); return; }
    const sel = t.closest('[data-sel]'); if (sel) { const id = +sel.dataset.sel; PLAN.sel = PLAN.sel === id ? null : id; PLAN.buying = null; PLAN.msg = ''; renderPlanner(); return; }
    const by = t.closest('[data-buy]'); if (by) { PLAN.buying = +by.dataset.buy; PLAN.sel = null; PLAN.q = ''; PLAN.msg = ''; renderPlanner(); const p = R.getElementById('pl-panel'); if (p) p.scrollIntoView({ behavior: 'smooth', block: 'nearest' }); return; }
    const sw = t.closest('[data-with]'); if (sw) { planInternal(PLAN.sel, +sw.dataset.with); return; }
    const bi = t.closest('[data-buyin]'); if (bi) { planTransfer(PLAN.buying, +bi.dataset.buyin); return; }
    const cp = t.closest('[data-cap]'); if (cp) { const [k, id] = cp.dataset.cap.split(':'); planCaptain(k, +id); return; }
    const ch = t.closest('[data-chip]'); if (ch) { planChip(ch.dataset.chip); return; }
    const wo = t.closest('[data-wcopt]'); if (wo) { applyWc(wo.dataset.wcopt); return; }
    const lk = t.closest('[data-lock]'); if (lk) { const id = +lk.dataset.lock; const W = PLAN.wc; W.locks = W.locks.includes(id) ? W.locks.filter((x) => x !== id) : [...W.locks, id]; W.bans = W.bans.filter((x) => x !== id); PLAN.wcLocks = W.locks; PLAN.wcBans = W.bans; renderPlanner(); return; }
    const bn = t.closest('[data-ban]'); if (bn) { const id = +bn.dataset.ban; const W = PLAN.wc; W.bans = W.bans.includes(id) ? W.bans.filter((x) => x !== id) : [...W.bans, id]; W.locks = W.locks.filter((x) => x !== id); PLAN.wcLocks = W.locks; PLAN.wcBans = W.bans; renderPlanner(); return; }
    if (t.closest('#wc-rebuild')) { wcSolve(); return; }
    if (t.closest('#wc-deep')) { PLAN.wc.N = 20000; wcSolve(); return; }
    if (t.closest('#al-toggle')) { ALERTS_ON = !ALERTS_ON; try { localStorage.setItem('fplAnalystAlerts', ALERTS_ON ? 'on' : 'off'); } catch (er) {} const b = R.getElementById('al-toggle'); b.textContent = ALERTS_ON ? 'Goal alerts: on' : 'Goal alerts: off'; b.setAttribute('aria-pressed', ALERTS_ON); return; }
    if (t.closest('#al-desk')) { try { Notification.requestPermission().then(() => { const b = R.getElementById('al-desk'); if (b) b.remove(); }); } catch (er) {} return; }
    const rn = t.closest('[data-rotn]'); if (rn) { ROT.n = +rn.dataset.rotn; paintRot(); return; }
    const rpz = t.closest('[data-rotpos]'); if (rpz) { ROT.pos = +rpz.dataset.rotpos; paintRot(); return; }
    const ac = t.closest('[data-act]'); if (ac) { const v = ac.dataset.act;
      if (v === 'alert') { showView('home'); const al = R.querySelector('#s-home .alerts'); if (al) al.scrollIntoView({ behavior: 'smooth', block: 'start' }); return; }
      if (PLAN.gw !== PLAN.A.startGw) { PLAN.gw = PLAN.A.startGw; }
      goPlanner();
      if (v === 'bestxi') { planBest(); return; }
      if (v.startsWith('chip:')) { PLAN.tab = 'chips'; planChip(v.slice(5)); return; }
      renderPlanner(); return; }
    const nf = t.closest('[data-nf]'); if (nf) { const f = nf.dataset.nf; R.querySelectorAll('[data-nf]').forEach((b) => { const on = b === nf; b.classList.toggle('on', on); b.setAttribute('aria-selected', on); }); NFS.k = f; nfApply(); return; }
    const lt = t.closest('[data-ltab]'); if (lt) { LIVETAB = lt.dataset.ltab; const sec = R.getElementById('s-live'); sec.querySelectorAll('[data-ltab]').forEach((b) => { const on = b.dataset.ltab === LIVETAB; b.classList.toggle('on', on); b.setAttribute('aria-selected', on); }); sec.querySelectorAll('[data-lpanel]').forEach((p) => { p.hidden = p.dataset.lpanel !== LIVETAB; }); return; }
    const ft = t.closest('[data-ftab]'); if (ft) { FIXTAB = ft.dataset.ftab; paintRot(); return; }
    const fa = t.closest('[data-fanchor]'); if (fa) { ROT.anchor = +fa.dataset.fanchor; FIXTAB = 'pairs'; SUBV.fix = 'pairs'; paintRot(); showView('fix', 'pairs'); return; }
    if (t.closest('#wc-clearlb')) { PLAN.wc.locks = []; PLAN.wc.bans = []; PLAN.wcLocks = []; PLAN.wcBans = []; renderPlanner(); return; }
    const qk = t.closest('[data-quick]'); if (qk) { quickAdd(qk); return; }
    const tr = t.closest('[data-try]'); if (tr) { const [o, i] = tr.dataset.try.split(':').map(Number); ensureWeek(o); planTransfer(o, i); goPlanner(); return; }
    const ap = t.closest('[data-addp]'); if (ap) { planFromProfile(+ap.dataset.addp); drawer.hidden = true; goPlanner(); return; }
    if (t.closest('#pl-cancel')) { PLAN.sel = null; PLAN.buying = null; renderPlanner(); return; }
    if (t.closest('#pl-undo')) { undoStep(); return; }
    if (t.closest('#pl-reset')) { pushUndo(`Reset GW${PLAN.gw}`); resetWeek(); renderPlanner(); return; }
    if (t.closest('#pl-clear')) { pushUndo('Clear plan'); PLAN.weeks = {}; loadWeek(PLAN.A.startGw); renderPlanner(); return; }
    if (t.closest('#gw-prev')) { planGo(PLAN.gw - 1); return; }
    if (t.closest('#gw-next')) { planGo(PLAN.gw + 1); return; }
    const gj = t.closest('[data-gwj]'); if (gj) { planGo(+gj.dataset.gwj); return; }
    const sg = t.closest('[data-sgw]'); if (sg) { showView('team', 'pitch'); planGo(+sg.dataset.sgw); return; }
  };
  out.addEventListener('click', onAct);
  // sub-view tabs (My Team: Pitch / List · Fixtures: Ticker / Pairs / Table)
  $('#subnav').addEventListener('click', (ev) => { const b = ev.target.closest('[data-sub]'); if (b) showView(VIEW, b.dataset.sub); });
  // player action sheet
  const sheet = $('#sheet');
  function closeSheet() { if (sheet.hidden) return; sheet.classList.add('closing'); setTimeout(() => { sheet.hidden = true; sheet.classList.remove('closing'); }, 180); }
  $('#sheetscrim').onclick = closeSheet;
  $('#sheetbody').addEventListener('click', (ev) => { if (ev.target.closest('[data-close]')) { closeSheet(); return; } if (ev.target.closest('[data-ui]')) return; const act = ev.target.closest('button,a'); if (!act) return; onAct(ev); closeSheet(); });
  document.addEventListener('keydown', (e) => { if (e.key === 'Escape' && !sheet.hidden) { e.stopImmediatePropagation(); closeSheet(); } }, true);
  // v3.22: tapping a player opens a small bar of actions that pop out from him (Wildcard mode keeps the full sheet)
  const qa = $('#qa'), qabar = $('#qabar'); let qaCard = null;
  function closeQuick() { if (qa.hidden) return; qa.hidden = true; if (qaCard) qaCard.classList.remove('qsel'); qaCard = null; }
  $('#qascrim').onclick = closeQuick;
  qabar.addEventListener('click', (ev) => { const act = ev.target.closest('button'); if (!act) return; if (act.dataset.qpp) { const pid = +act.dataset.qpp; closeQuick(); openPlayerPage(pid); return; } onAct(ev); closeQuick(); });
  document.addEventListener('keydown', (e) => { if (e.key === 'Escape' && !qa.hidden) { e.stopImmediatePropagation(); closeQuick(); } }, true);
  out.addEventListener('scroll', closeQuick, { passive: true }); window.addEventListener('resize', closeQuick);
  function openQuick(id, card) {
    if (!PLAN || !PLAN.A) return; const x = PLAN.line.find((y) => y.e.id === id); if (!x) return;
    if (PLAN.wc && PLAN.wc.opts && PLAN.wc.g === PLAN.gw && PLAN.chip === PLAN.wc.chip) { openSheet(id); return; }
    closeQuick(); const xi = inXI(x), e = x.e;
    const b = (attr, ic, lab, tip, cls) => `<button type="button" role="menuitem" class="qab ${cls || ''}" ${attr} title="${tip}" aria-label="${lab} ${esc(e.web_name)}"><span class="si">${ic}</span><small>${lab}</small></button>`;
    const items = [b(`data-sel="${id}"`, '⇄', 'Swap', 'Bench or start him, within your squad')];
    if (xi) { items.push(b(`data-cap="c:${id}"`, 'C', 'Captain', PLAN.cap === x ? 'Already your captain' : 'Double points this week', PLAN.cap === x ? 'on' : '')); items.push(b(`data-cap="v:${id}"`, 'V', 'Vice', 'Takes over if the captain doesn\'t play', PLAN.vc === x ? 'on' : '')); }
    items.push(b(`data-buy="${id}"`, '↗', 'Sell', 'Pick a replacement within your budget', 'out'));
    items.push(b(`data-qpp="${id}"`, 'i', 'Profile', 'Stats, fixtures and news'));
    qabar.innerHTML = items.join(''); qabar.querySelectorAll('.qab').forEach((el, i) => el.style.setProperty('--i', i));
    qa.hidden = false; qaCard = card; card.classList.add('qsel');
    const P = qa.getBoundingClientRect(), c = card.getBoundingClientRect(), bw = qabar.offsetWidth, bh = qabar.offsetHeight;
    const cx = c.left + c.width / 2 - P.left, cy = c.top + c.height / 2 - P.top;
    const left = Math.max(8, Math.min(P.width - bw - 8, cx - bw / 2));
    let top = c.top - P.top - bh - 6; if (top < 8) top = Math.min(P.height - bh - 8, c.bottom - P.top + 6);
    qabar.style.left = left + 'px'; qabar.style.top = top + 'px';
    qabar.querySelectorAll('.qab').forEach((el) => { el.style.setProperty('--dx', (cx - (left + el.offsetLeft + el.offsetWidth / 2)) + 'px'); el.style.setProperty('--dy', (cy - (top + el.offsetTop + el.offsetHeight / 2)) + 'px'); });
  }
  function openSheet(id) {
    if (!PLAN || !PLAN.A) return; const A = PLAN.A, T = A.T, g0 = PLAN.gw;
    const x = PLAN.line.find((y) => y.e.id === id); if (!x) return; const e = x.e;
    const xi = inXI(x), wc = PLAN.wc && PLAN.wc.opts && PLAN.wc.g === g0 && PLAN.chip === PLAN.wc.chip;
    const btn = (attr, ic, lab, sub, cls) => `<button type="button" class="sact sm ${cls || ''}" ${attr} title="${sub}"><span class="si">${ic}</span><b>${lab}</b></button>`;
    const n3 = A.GWS.filter((g) => g >= g0).slice(0, 3);
    const tip = (() => { const p3 = n3.reduce((a, g) => a + A.P(e, g), 0); const pc = PLAN.cap; if (!xi && e.now_cost <= 45 && p3 < 3) return ['', 'Bench filler: cheap 15th man, frees money for starters']; if (e.status !== 'a') return ['bad', e.news || 'Flagged by FPL']; if (xi && pc && pc !== x && A.P(e, g0) > A.P(pc.e, g0) + 0.5) return ['good', `Better captain than ${pc.e.web_name} this week`]; if (!xi && A.P(e, g0) >= 4) return ['good', 'Worth starting this week']; if (p3 < 7) return ['bad', 'Weak run: consider selling']; if (p3 >= 15) return ['good', 'Strong run: keep']; return ['', 'Hold']; })();
    $('#sheetbody').innerHTML = `<div class="shgrab" data-close></div><div class="shh2"><div class="shk2">${kitImg(T[e.team].short_name, e.element_type === 1, 110, 'shkit')}</div><div class="shi"><b>${esc(e.web_name)}</b><small>${posB(e.element_type)} ${esc(T[e.team].short_name)} · ${money(e.now_cost)} · rating <b>${A.ratings(e)[0].v}</b> · ${e.selected_by_percent}%</small><span class="shtip ${tip[0]}">${esc(tip[1])}</span></div><button type="button" class="x" data-close aria-label="Close">×</button></div>
<div class="shn3">${n3.map((g) => `<div><small>GW${g}</small>${fxCell(A, e.team, g)}<b>${f1(A.P(e, g))}</b></div>`).join('')}<div class="tot"><small>Next 3</small><b>${f1(n3.reduce((a, g) => a + A.P(e, g), 0))}</b><small>pts</small></div></div>
<div class="sgrid2">${btn(`data-sel="${id}"`, '⇄', 'Swap', 'Bench or start him, within your squad')}${xi ? btn(`data-cap="c:${id}"`, 'C', PLAN.cap === x ? 'Captain' : 'Captain', PLAN.cap === x ? 'Already your captain' : 'Double points this week', PLAN.cap === x ? 'on' : '') + btn(`data-cap="v:${id}"`, 'V', 'Vice', 'Takes over if the captain doesn\'t play', PLAN.vc === x ? 'on' : '') : ''}${btn(`data-buy="${id}"`, '↗', 'Sell', 'Pick a replacement within your budget', 'out')}<a class="pn sact sm" href="#" data-pid="${id}" title="Stats, fixtures and news"><span class="si">i</span><b>Profile</b></a></div>${wc ? `<div class="sgrid2 two">${btn(`data-lock="${id}"`, '🔒', PLAN.wc.locks.includes(id) ? 'Unlock' : 'Lock', 'Keep him in every Wildcard option', PLAN.wc.locks.includes(id) ? 'on' : '')}${btn(`data-ban="${id}"`, '⊘', PLAN.wc.bans.includes(id) ? 'Allow' : 'Exclude', 'Leave him out of every option', PLAN.wc.bans.includes(id) ? 'on' : '')}</div>` : ''}`;
    sheet.hidden = false; const f = sheet.querySelector('.sact'); if (f) f.focus();
  }
  R.addEventListener('error', (ev) => { const im = ev.target; if (!im || im.tagName !== 'IMG') return; if (im.dataset.alt) { const a = im.dataset.alt; delete im.dataset.alt; im.src = a; return; } im.classList.add('gone'); }, true);
  R.addEventListener('load', (ev) => { const im = ev.target; if (im && im.tagName === 'IMG' && (im.classList.contains('crest') || im.classList.contains('kimg')) && im.parentElement) im.parentElement.classList.add('ok'); }, true);
  // decorate player names wherever they appear (lists, tables, recommendation rows, profile, sheets)
  // v3.36: long tables show one screen of rows at a time (no vertical scrolling), with Prev / Next
  const PG = {};
  // v3.51: on phones these lists scroll inside a box that fills the rest of the screen, instead of showing a few rows per page
  const SCROLLPG = new Set(['mk', 'ps']);
  const phone = () => window.innerWidth <= 860;
  // height for a scroll box starting at el: down to the bottom bar (minus anything right under it), never less than 300px
  const fillH = (el) => { const o = out.getBoundingClientRect(), nb = (R.getElementById('nav') || out).getBoundingClientRect(); const bottom = nb.top > o.top + 120 && nb.top <= o.bottom + 1 ? nb.top : o.bottom; const top = el.getBoundingClientRect().top; return Math.max(300, Math.floor(bottom - top - 12 - (el.nextElementSibling && !el.nextElementSibling.hidden ? el.nextElementSibling.offsetHeight : 0))); };
  function fitScrollBoxes() {
    R.querySelectorAll('.cmpgrid.pick .cmpl').forEach((el) => { if (!phone() || !el.offsetParent) { el.style.height = ''; return; } const h = fillH(el); el.style.height = h + 'px'; const over = out.scrollHeight - out.clientHeight; if (over > 1 && h > 300) el.style.height = Math.max(300, h - over) + 'px'; });
  }
  function pgOne(t) {
    const key = t.dataset.pg, tb = t.tBodies[0]; if (!tb) return; const rows = [...tb.rows]; if (!rows.length) return;
    const wrap0 = t.closest('.tw, .ps-scroll') || t;
    if (SCROLLPG.has(key)) {
      rows.forEach((r) => { if (r.hidden) r.hidden = false; });
      const b0 = wrap0.nextElementSibling; if (b0 && b0.classList.contains('pgbar')) b0.hidden = true;
      wrap0.classList.add('vscroll'); let h = fillH(wrap0); wrap0.style.maxHeight = h + 'px';
      const over = out.scrollHeight - out.clientHeight; if (over > 1 && h > 300) wrap0.style.maxHeight = Math.max(300, h - over) + 'px';
      return;
    }
    wrap0.classList.remove('vscroll'); wrap0.style.maxHeight = '';
    const sig = rows.length + '|' + rows.slice(0, 3).map((r) => r.textContent.slice(0, 40)).join('|');
    const st = PG[key] || (PG[key] = { p: 0, sig: '' }); if (st.sig !== sig) { st.sig = sig; st.p = 0; }
    rows.forEach((r) => { if (r.hidden) r.hidden = false; });
    const o = out.getBoundingClientRect(), nb = (R.getElementById('nav') || out).getBoundingClientRect();
    const limit = (nb.top > o.top + 120 && nb.top <= o.bottom + 1 ? nb.top : o.bottom) - o.top;
    const headB = (t.tHead ? t.tHead.getBoundingClientRect().bottom : t.getBoundingClientRect().top) - o.top + out.scrollTop;
    const rh = Math.max(24, rows[0].getBoundingClientRect().height || 36);
    let per = Math.max(3, Math.floor((limit - headB - 64) / rh));
    const wrap = t.closest('.tw, .ps-scroll') || t; let bar = wrap.nextElementSibling;
    if (!bar || !bar.classList.contains('pgbar')) { bar = document.createElement('div'); bar.className = 'pgbar'; wrap.after(bar); }
    const paint = () => {
      const pages = Math.max(1, Math.ceil(rows.length / per)); st.p = Math.min(st.p, pages - 1);
      rows.forEach((r, i) => { const h = i < st.p * per || i >= (st.p + 1) * per; if (r.hidden !== h) r.hidden = h; });
      const html = pages < 2 ? '' : `<button type="button" data-pgk="${key}" data-pgd="-1" ${st.p ? '' : 'disabled'} aria-label="Previous page">‹ Prev</button><span>${st.p * per + 1}–${Math.min(rows.length, (st.p + 1) * per)} of ${rows.length}</span><button type="button" data-pgk="${key}" data-pgd="1" ${st.p < pages - 1 ? '' : 'disabled'} aria-label="Next page">Next ›</button>`;
      if (bar.innerHTML !== html) bar.innerHTML = html; bar.hidden = pages < 2;
    };
    paint();
    // trim rows until the page itself needs no vertical scroll (what sits under the table is measured, not guessed)
    for (let k = 0; k < 3 && per > 3; k++) { const over = out.scrollHeight - out.clientHeight; if (over <= 1) break; per = Math.max(3, per - Math.ceil(over / rh)); paint(); }
  }
  const pgAll = () => { R.querySelectorAll('table.pgd').forEach(pgOne); fitScrollBoxes(); };
  R.addEventListener('click', (ev) => { const b = ev.target.closest && ev.target.closest('[data-pgk]'); if (!b) return; const st = PG[b.dataset.pgk]; if (!st) return; st.p = Math.max(0, st.p + +b.dataset.pgd); const t = R.querySelector(`table.pgd[data-pg="${b.dataset.pgk}"]`); if (t) { pgOne(t); const top = (t.closest('.tw, .ps-scroll') || t).getBoundingClientRect().top; if (top < out.getBoundingClientRect().top) out.scrollTop += top - out.getBoundingClientRect().top - 8; } });
  window.addEventListener('resize', () => setTimeout(pgAll, 50));
  const markTw = (root) => (root || R).querySelectorAll('.tw').forEach((w) => w.classList.toggle('more', w.scrollWidth - w.clientWidth - w.scrollLeft > 6));
  try { let dq = 0; new MutationObserver(() => { if (dq) return; dq = requestAnimationFrame(() => { dq = 0; decorateNames(R.querySelector('.panel')); markTw(); pgAll(); }); }).observe(R.querySelector('.panel'), { childList: true, subtree: true }); } catch (e) {}
  R.addEventListener('scroll', (ev) => { const w = ev.target; if (w && w.classList && w.classList.contains('tw')) w.classList.toggle('more', w.scrollWidth - w.clientWidth - w.scrollLeft > 6); }, true);
  window.addEventListener('resize', () => markTw());
  drawer.addEventListener('click', onAct);
  const NFS = { k: 'all', src: '', q: '' };
  function nfApply() {
    const cs = [...R.querySelectorAll('#ngrid .ncard')]; let shown = 0;
    R.querySelectorAll('[data-nf]').forEach((b) => { const on = b.dataset.nf === NFS.k; b.classList.toggle('on', on); b.setAttribute('aria-selected', on); });
    const qq = NFS.q.trim().toLowerCase(); cs.forEach((c) => { c.hidden = (NFS.k !== 'all' && !c.dataset.k.split(' ').includes(NFS.k)) || (NFS.src && c.dataset.src !== NFS.src) || (qq && !(c.dataset.q || '').includes(qq)); if (!c.hidden) shown++; });
    R.querySelectorAll('[data-nf]').forEach((b) => { const k = b.dataset.nf, n = cs.filter((c) => (k === 'all' || c.dataset.k.split(' ').includes(k)) && (!NFS.src || c.dataset.src === NFS.src)).length; const i = b.querySelector('.nfc'); if (i) i.textContent = n; b.classList.toggle('zero', !n); });
    const e = R.getElementById('nf-empty'); if (e) e.hidden = !cs.length || shown > 0;
  }
  out.addEventListener('change', (ev) => { if (ev.target.id === 'nf-src') { NFS.src = ev.target.value; nfApply(); return; } if (ev.target.id === 'lg-sel') { LG.lid = ev.target.value; refreshLeague(LASTA, true); return; } if (ev.target.id === 'rot-anchor') { ROT.anchor = +ev.target.value; paintRot(); return; } if (ev.target.id === 'wc-league') { PLAN.wcLid = +ev.target.value; PLAN.wc.lid = PLAN.wcLid; wcSolve(); return; } if (ev.target.id === 'pl-sort') { PLAN.psort = ev.target.value; const l = R.getElementById('pl-plist'); if (l) l.innerHTML = playerList(); } });
  out.addEventListener('input', (ev) => { if (ev.target.id === 'pl-pq') { PLAN.pq = ev.target.value; const l = R.getElementById('pl-plist'); if (l) l.innerHTML = playerList(); return; } if (ev.target.id === 'pl-q') { PLAN.q = ev.target.value; const l = R.getElementById('pl-cands'); if (l) l.innerHTML = buyList(); } });
  const goPlanner = () => showView('team', 'pitch');

  // ---------- Planner: your lineup (XI + bench), internal swaps, captaincy and optional transfers ----------
  // PLAN.line holds 15 entries in FPL position order: 0-10 starting XI, 11 bench GK, 12-14 bench outfield in order.
  let PLAN = null;
  const PKEY = 'fplAnalystPlans';
  const loadPlans = () => { try { return JSON.parse(localStorage.getItem(PKEY) || '{}') || {}; } catch (e) { return {}; } };
  // ---------- v3.7: Auto plan ----------
  // Beam search over the next 6 gameweeks. Each week: roll, or make the transfers that gain at least the 2.5-pt threshold
  // over the weeks left. Steady never takes a hit; Climber may take up to 2 hits a week when the extra move gains 4 + 2.5 pts.
  function autoPlan(style) {
    const A = PLAN.A, P = A.P, CONV = A.CONV || 2.5;
    const W = A.GWS.slice(0, Math.min(6, A.GWS.length)); const H = W.length;
    const o = origLine();
    const V = (e, k) => { let v = 0; for (let j = k; j < H; j++) v += P(e, W[j]); return v; };
    const pts = (list, g) => { const b = A.bestXIof(list, g); return b.sum + b.cap; };
    const POOL = {}; [1, 2, 3, 4].forEach((et) => { POOL[et] = BS.elements.filter((c) => c.element_type === et && c.status !== 'u' && c.status !== 'n' && A.rel(c) > 0.35).map((c) => ({ c, v: V(c, 0) })).sort((a, b) => b.v - a.v).slice(0, 45).map((x) => x.c); });
    const clubsOf = (list) => { const m = {}; list.forEach((x) => (m[x.e.team] = (m[x.e.team] || 0) + 1)); return m; };
    // Steady: no hits, a move must gain 2.5+ pts, saving a free transfer is valued. Climber: up to 2 hits a week when the extra
    // move gains 4 + 1 pts, free moves from 1.5 pts, and less value on saving transfers, so it acts sooner and more often.
    const CL = style === 'climber'; const maxHits = CL ? 2 : 0, B = 36, MIN = CL ? Math.min(1.5, CONV) : CONV, HITGAIN = CL ? 5 : 4 + CONV, BANK = CL ? 0.5 : 1.2;
    const futureOf = (list, k) => { let v = 0; for (let j = k; j < H; j++) v += pts(list, W[j]); return v; };
    const key = (st) => st.list.map((x) => x.e.id).sort((a, b) => a - b).join(',') + '|' + st.ft;
    let beam = [{ list: o.list, bank: A.bank, ft: A.ft, acc: 0, path: [] }];
    for (let k = 0; k < H; k++) {
      const g = W[k], next = new Map();
      const push = (st) => { const kk = key(st); const prev = next.get(kk); if (!prev || prev.acc < st.acc) next.set(kk, st); };
      beam.forEach((st) => {
        const have = new Set(st.list.map((x) => x.e.id)), cl = clubsOf(st.list);
        // single moves worth at least the threshold over the weeks left
        const singles = [];
        st.list.forEach((x, idx) => { const vo = V(x.e, k); POOL[x.e.element_type].forEach((c) => {
          if (have.has(c.id) || c.now_cost > st.bank + x.sell) return; if (c.team !== x.e.team && (cl[c.team] || 0) >= 3) return;
          const gain = V(c, k) - vo; if (gain >= MIN) singles.push({ idx, x, c, gain }); }); });
        singles.sort((a, b) => b.gain - a.gain);
        const top = singles.slice(0, 14);
        const opts = [[]]; top.forEach((m) => opts.push([m]));
        for (let i = 0; i < Math.min(9, top.length); i++) for (let j = i + 1; j < Math.min(9, top.length); j++) { const a = top[i], b = top[j]; if (a.idx !== b.idx && a.c.id !== b.c.id) opts.push([a, b]); }
        if (maxHits >= 2) for (let i = 0; i < Math.min(5, top.length); i++) for (let j = i + 1; j < Math.min(5, top.length); j++) for (let l = j + 1; l < Math.min(5, top.length); l++) { const a = top[i], b = top[j], c2 = top[l]; if (new Set([a.idx, b.idx, c2.idx]).size === 3 && new Set([a.c.id, b.c.id, c2.c.id]).size === 3) opts.push([a, b, c2]); }
        opts.forEach((mv) => {
          const n = mv.length, hits = Math.max(0, n - st.ft); if (hits > maxHits) return;
          if (hits && mv.slice(st.ft).some((m) => m.gain < HITGAIN)) return;
          const list = st.list.slice(); let bank = st.bank; const cl2 = Object.assign({}, cl); let ok = true;
          mv.forEach((m) => { bank += m.x.sell - m.c.now_cost; cl2[m.x.e.team]--; cl2[m.c.team] = (cl2[m.c.team] || 0) + 1; list[m.idx] = { e: m.c, sell: m.c.now_cost }; });
          if (bank < 0 || mv.some((m) => cl2[m.c.team] > 3)) ok = false; if (!ok) return;
          const wp = pts(list, g) - 4 * hits;
          const ft = n === 0 ? Math.min(5, st.ft + 1) : Math.min(5, Math.max(0, st.ft - n) + 1);
          push({ list, bank, ft, acc: st.acc + wp, path: st.path.concat([{ g, moves: mv.map((m) => ({ o: m.x.e, i: m.c, gain: m.gain })), hits, pts: wp, ft: st.ft, bank }]) });
        });
      });
      // keep the best states: points so far + what the squad projects for the weeks left + a little for each free transfer kept
      beam = [...next.values()].map((st) => ({ st, h: st.acc + futureOf(st.list, k + 1) + BANK * Math.min(st.ft - 1, 3) })).sort((a, b) => b.h - a.h).slice(0, B).map((x) => x.st);
    }
    const best = beam.sort((a, b) => b.acc - a.acc)[0];
    if (!best) throw new Error('no valid path found');
    const base = W.reduce((a, g) => a + pts(o.list, g), 0);
    return { style, W, path: best.path, total: best.acc, base, gain: best.acc - base, nT: best.path.reduce((a, w) => a + w.moves.length, 0), hits: best.path.reduce((a, w) => a + w.hits, 0) };
  }
  function autoHtml(nm) {
    const R2 = PLAN.auto; const st = (PLAN.autoStyle || 'steady');
    const head = `<p class="note" style="margin:0 0 8px">Plans your transfers for the next ${Math.min(6, PLAN.A.GWS.length)} gameweeks from your real squad. ${st === 'climber' ? `<b>Climber</b> takes a move worth ${Math.min(1.5, PLAN.A.CONV || 2.5)}+ points, and up to 2 hits a week when a move gains 5+ points (more than the 4-point cost); it rolls fewer free transfers.` : `<b>Steady</b> never takes a hit, only makes a move worth ${PLAN.A.CONV || 2.5}+ points over the weeks left, and prefers to roll free transfers.`} Chips aren't planned here.</p>
<div class="aprow"><div class="seg"><button type="button" data-apst="steady" class="${st === 'steady' ? 'on' : ''}" title="Never takes a points hit">Steady</button><button type="button" data-apst="climber" class="${st === 'climber' ? 'on' : ''}" title="Up to 2 hits a week when a move clearly pays">Climber</button></div><button class="try" type="button" id="ap-run">${R2 ? 'Generate again' : 'Generate plan'}</button></div>`;
    if (!R2) return head;
    if (R2.busy) return head + '<p class="muted"><span class="spin"></span> Searching transfer paths…</p>';
    const cmpNote = R2.same ? `<p class="note" style="margin:6px 0 0">${st === 'climber' ? 'No hit pays off over these weeks, so Climber found the same plan as Steady.' : 'Climber finds the same plan here: no hit pays off over these weeks.'}</p>` : `<p class="note" style="margin:6px 0 0">${st === 'climber' ? 'Steady' : 'Climber'} would project ${f1(R2.otherTotal)} pts (${R2.otherTotal >= R2.total ? '+' : ''}${f1(R2.otherTotal - R2.total)}).</p>`;
    return `${head}${cmpNote}<div class="kpis uni apk"><div class="kpi"><small>Projected over ${R2.W.length} GWs</small><b>${f1(R2.total)}</b><span class="${R2.gain >= 0 ? 'up' : 'dn'}">${R2.gain >= 0 ? '+' : ''}${f1(R2.gain)} vs no transfers</span></div><div class="kpi"><small>Transfers</small><b>${R2.nT}</b><span>${R2.hits ? `<span class="dn">${R2.hits} hit${R2.hits > 1 ? 's' : ''} (−${4 * R2.hits})</span>` : 'no hits'}</span></div></div>
<ol class="aptl">${R2.path.map((w) => `<li><div class="apg"><b>GW${w.g}</b><small>${w.ft} free transfer${w.ft === 1 ? '' : 's'}</small></div><div class="apm">${w.moves.length ? w.moves.map((m) => `<div><span class="mv"><i class="mo">OUT</i>${nm(m.o)}</span><span class="mv"><i class="mi">IN</i>${nm(m.i)}</span> <small class="muted">${money(m.i.now_cost)}</small> <b class="up">+${f1(m.gain)}</b></div>`).join('') + (w.hits ? `<div class="dn" style="font-size:12px">−${4 * w.hits} hit</div>` : '') : '<div class="muted">Roll the free transfer</div>'}</div><div class="app">${f1(w.pts)}<small>pts</small></div></li>`).join('')}</ol>
<div class="aprow"><button class="try" type="button" id="ap-apply">Apply to planner</button><small class="muted">Replaces the transfers saved for GW${R2.W[0]}–${R2.W[R2.W.length - 1]}. You can still edit any week afterwards.</small></div>`;
  }
  function applyAuto() {
    const R2 = PLAN.auto; if (!R2 || !R2.path) return;
    pushUndo('Apply auto plan');
    R2.W.forEach((g) => { delete PLAN.weeks[g]; });
    R2.path.forEach((w) => { if (w.moves.length) PLAN.weeks[w.g] = { sw: w.moves.map((m) => [m.o.id, m.i.id]) }; });
    savePlan(); loadWeek(PLAN.A.startGw); PLAN.msg = ''; renderPlanner();
  }
  function savePlan() {
    try { const all = loadPlans(); if (Object.keys(PLAN.weeks).length) all[PLAN.A.id] = { weeks: PLAN.weeks, at: Date.now() }; else delete all[PLAN.A.id]; localStorage.setItem(PKEY, JSON.stringify(all)); } catch (e) {}
  }
  function planInit(A) {
    const keep = PLAN && PLAN.A && PLAN.A.id === A.id ? { tab: PLAN.tab, gw: PLAN.gw } : {};
    const stored = (loadPlans()[A.id] || {}).weeks || {};
    const weeks = {}; Object.keys(stored).forEach((g) => { if (+g >= A.startGw) weeks[g] = stored[g]; });   // weeks already played are dropped
    if (!keep.tab) UNDO = [];
    PLAN = { tab: keep.tab || 'do', A, weeks, gw: A.startGw, sel: null, buying: null, q: '', msg: '', hist: null, swaps: [], chipIn: [], chipOut: [] };
    const lastG = A.GWS[A.GWS.length - 1];
    loadWeek(keep.gw && keep.gw >= A.startGw && keep.gw <= lastG ? keep.gw : A.startGw);
  }
  // Your real lineup in FPL order: starting XI, bench goalkeeper, bench outfield
  function origLine() {
    const A = PLAN.A; const byEl = {}; A.sq.forEach((s) => (byEl[s.e.id] = { e: s.e, sell: s.sell }));
    const line = A.picks.slice().sort((a, b) => a.position - b.position).map((p) => byEl[p.element]);
    const xi = line.slice(0, 11), bench = line.slice(11);
    const capP = A.picks.find((p) => p.is_captain), vcP = A.picks.find((p) => p.is_vice_captain);
    return { list: [...xi, ...bench.filter((x) => x.e.element_type === 1), ...bench.filter((x) => x.e.element_type !== 1)], cap: capP ? capP.element : null, vc: vcP ? vcP.element : null };
  }
  // Apply one saved week (chip squad, transfers, lineup order, armband) to the squad entering it
  function applyWeek(st, wk) {
    const A = PLAN.A; let list = st.list.slice(), bank = st.bank, nT = 0, chipIn = [], chipOut = [], chipBank = null;
    const sellOf = (id) => { const x = st.list.find((y) => y.e.id === id); return x ? x.sell : A.E[id].now_cost; };
    if ((wk.chip === 'wildcard' || wk.chip === 'freehit') && wk.cl && wk.cl.length === 15 && wk.cl.every((id) => A.E[id])) {
      const budget = st.list.reduce((a, x) => a + x.sell, 0) + st.bank;
      const nl = wk.cl.map((id) => ({ e: A.E[id], sell: sellOf(id) }));
      const had = new Set(st.list.map((x) => x.e.id)), has = new Set(wk.cl);
      chipIn = nl.filter((x) => !had.has(x.e.id)).map((x) => x.e); chipOut = st.list.filter((x) => !has.has(x.e.id)).map((x) => x.e);
      bank = budget - nl.reduce((a, x) => a + x.sell, 0); chipBank = bank; list = nl; nT = chipIn.length;
    }
    const swaps = [];
    (wk.sw || []).forEach(([o, i]) => {
      const k = list.findIndex((x) => x.e.id === o);
      if (k < 0 || !A.E[i] || list.some((x) => x.e.id === i) || A.E[i].element_type !== list[k].e.element_type) return;   // no longer possible after earlier changes
      const ne = { e: A.E[i], sell: A.E[i].now_cost }; swaps.push({ o: list[k], i: ne }); bank += list[k].sell - ne.e.now_cost; list[k] = ne; nT++;
    });
    if (wk.order && wk.order.length === 15 && new Set(wk.order).size === 15) { const m = {}; list.forEach((x) => (m[x.e.id] = x)); if (wk.order.every((id) => m[id])) list = wk.order.map((id) => m[id]); }
    const inXi = (id) => id != null && list.slice(0, 11).some((x) => x.e.id === id);
    return { list, bank, nT, swaps, chipIn, chipOut, chipBank, cap: inXi(wk.cap) ? wk.cap : inXi(st.cap) ? st.cap : null, vc: inXi(wk.vc) ? wk.vc : inXi(st.vc) ? st.vc : null };
  }
  // Free transfers roll forward: +1 each week up to 5; a Wildcard or Free Hit week keeps what you had
  const ftNext = (ft, nT, chip) => (chip === 'wildcard' || chip === 'freehit' ? ft : Math.min(5, Math.max(0, ft - nT) + 1));
  function enterState(g) {
    const A = PLAN.A; const o = origLine(); let st = { list: o.list, bank: A.bank, cap: o.cap, vc: o.vc }, ft = A.ft;
    for (let w = A.startGw; w < g; w++) {
      const wk = PLAN.weeks[w];
      if (!wk) { ft = Math.min(5, ft + 1); continue; }
      const r = applyWeek(st, wk);
      if (wk.chip !== 'freehit') st = { list: r.list, bank: r.bank, cap: r.cap, vc: r.vc };   // a Free Hit squad lasts one week
      ft = ftNext(ft, r.nT, wk.chip);
    }
    return { st, ft };
  }
  function setWork(st, wk) {
    const r = applyWeek(st, wk);
    PLAN.line = r.list; PLAN.swaps = r.swaps; PLAN.chip = wk.chip || null; PLAN.chipBank = r.chipBank; PLAN.chipIn = r.chipIn; PLAN.chipOut = r.chipOut; PLAN.chipLine = r.chipBank != null ? wk.cl : null;
    const find = (id) => PLAN.line.find((x) => x.e.id === id);
    PLAN.cap = find(r.cap); PLAN.vc = find(r.vc); fixCaptains();
  }
  const planSig = () => [PLAN.line.map((x) => x.e.id).join(), PLAN.cap && PLAN.cap.e.id, PLAN.vc && PLAN.vc.e.id, PLAN.chip || ''].join('|');
  function loadWeek(g) {
    const A = PLAN.A; PLAN.gw = g; PLAN.hist = null;
    const { st, ft } = enterState(g);
    PLAN.enter = st.list; PLAN.bank0 = st.bank; PLAN.ft0 = ft;
    setWork(st, {}); PLAN.sig0 = planSig();
    setWork(st, PLAN.weeks[g] || {});
    PLAN.sel = null; PLAN.buying = null; PLAN.msg = '';
    const ol = origLine(); PLAN.base = ol.list.slice(0, 11).reduce((a, x) => a + A.P(x.e, g), 0) + (ol.cap ? A.P(A.E[ol.cap], g) : 0);
  }
  // Store the week being edited and save the whole plan in this browser
  function commit() {
    if (PLAN.gw < PLAN.A.startGw) return;
    if (!PLAN.swaps.length && planSig() === PLAN.sig0) delete PLAN.weeks[PLAN.gw];
    else PLAN.weeks[PLAN.gw] = { sw: PLAN.swaps.map((s) => [s.o.e.id, s.i.e.id]), order: PLAN.line.map((x) => x.e.id), cap: PLAN.cap ? PLAN.cap.e.id : null, vc: PLAN.vc ? PLAN.vc.e.id : null, chip: PLAN.chip, cl: PLAN.chipLine || null };
    savePlan();
  }
  function resetWeek() { delete PLAN.weeks[PLAN.gw]; loadWeek(PLAN.gw); }
  const dropWc = () => { if (PLAN.wc && (PLAN.wc.g !== PLAN.gw || PLAN.chip !== PLAN.wc.chip)) PLAN.wc = null; };
  // A move asked for from outside the planner applies to the next deadline unless that player is in the week on screen
  function ensureWeek(outId) { if (PLAN.gw < PLAN.A.startGw || (outId != null && !PLAN.line.some((x) => x.e.id === outId))) loadWeek(PLAN.A.startGw); }
  const inXI = (x) => PLAN.line.indexOf(x) < 11;
  const byId = (id) => PLAN.line.find((x) => x.e.id === id);
  const formationOk = (xi) => { const n = (t) => xi.filter((x) => x.e.element_type === t).length; return n(1) === 1 && n(2) >= 3 && n(3) >= 2 && n(4) >= 1; };
  function fixCaptains() {
    const xi = PLAN.line.slice(0, 11), P = PLAN.A.P, g0 = PLAN.gw;
    const best = xi.slice().sort((a, b) => P(b.e, g0) - P(a.e, g0));
    if (!xi.includes(PLAN.cap)) PLAN.cap = xi.includes(PLAN.vc) ? PLAN.vc : best[0];
    if (!xi.includes(PLAN.vc) || PLAN.vc === PLAN.cap) PLAN.vc = best.find((x) => x !== PLAN.cap);
  }
  // Valid partners for an internal swap
  function partners(x) {
    const i = PLAN.line.indexOf(x);
    return PLAN.line.filter((y, j) => {
      if (y === x) return false;
      const xGK = x.e.element_type === 1, yGK = y.e.element_type === 1;
      if (xGK !== yGK) return false;
      if ((i < 11) === (j < 11)) return i >= 11 && !xGK;          // bench outfield players can change order
      const L = PLAN.line.slice(); L[i] = y; L[j] = x; return formationOk(L.slice(0, 11));
    });
  }
  // ---------- v3.10: undo, one step at a time (each transfer, swap, armband change, chip, reset or auto plan) ----------
  let UNDO = [];
  function pushUndo(label) {
    if (!PLAN || PLAN.gw < PLAN.A.startGw) return;
    commit();
    UNDO.push({ label, gw: PLAN.gw, weeks: JSON.parse(JSON.stringify(PLAN.weeks)) });
    if (UNDO.length > 40) UNDO.shift();
  }
  function undoStep() {
    const u = UNDO.pop(); if (!u) return;
    PLAN.weeks = u.weeks; savePlan(); PLAN.wc = null; PLAN.auto = null; loadWeek(u.gw); PLAN.msg = ''; PLAN.undone = u.label; renderPlanner();
  }
  function planInternal(aId, bId) {
    const x = byId(aId), y = byId(bId); if (!x || !y) return;
    if (!partners(x).includes(y)) { PLAN.msg = 'That swap would break the formation (1 GK, 3+ DEF, 2+ MID, 1+ FWD).'; return renderPlanner(); }
    const i = PLAN.line.indexOf(x), j = PLAN.line.indexOf(y);
    pushUndo(`Swap ${x.e.web_name} ⇄ ${y.e.web_name}`);
    PLAN.line[i] = y; PLAN.line[j] = x; fixCaptains(); PLAN.sel = null; PLAN.msg = '';
    renderPlanner();
  }
  function planCaptain(kind, id) {
    const x = byId(id); if (!x || !inXI(x)) return;
    pushUndo(`${kind === 'c' ? 'Captain' : 'Vice-captain'} ${x.e.web_name}`);
    if (kind === 'c') { if (PLAN.vc === x) PLAN.vc = PLAN.cap; PLAN.cap = x; } else { if (PLAN.cap === x) PLAN.cap = PLAN.vc; PLAN.vc = x; }
    fixCaptains(); PLAN.sel = null; renderPlanner();
  }
  const planBank = () => (PLAN.chipBank != null ? PLAN.chipBank : PLAN.bank0) + PLAN.swaps.reduce((a, s) => a + s.o.sell - s.i.e.now_cost, 0);
  const planClubs = () => { const c = {}; PLAN.line.forEach((x) => (c[x.e.team] = (c[x.e.team] || 0) + 1)); return c; };
  // Transfer: the new player takes the same place (and armband) as the one leaving
  function planTransfer(outId, inId) {
    const A = PLAN.A; const k = PLAN.line.findIndex((x) => x.e.id === outId); if (k < 0) return;
    const e = A.E[inId], cur = PLAN.line[k];
    if (e.element_type !== cur.e.element_type) { PLAN.msg = `${e.web_name} plays ${POS[e.element_type]}; pick a ${POS[cur.e.element_type]}.`; return renderPlanner(); }
    if (byId(inId)) { PLAN.msg = `${e.web_name} is already in your squad.`; return renderPlanner(); }
    pushUndo(`Transfer ${cur.e.web_name} → ${e.web_name}`);
    const prev = PLAN.swaps.find((s) => s.i === cur);
    const orig = prev ? prev.o : cur;
    PLAN.swaps = PLAN.swaps.filter((s) => s !== prev);
    const x = orig.e.id === inId ? orig : { e, sell: e.now_cost };
    if (x !== orig) PLAN.swaps.push({ o: orig, i: x });
    PLAN.line[k] = x;
    if (PLAN.cap === cur) PLAN.cap = x; if (PLAN.vc === cur) PLAN.vc = x;
    PLAN.buying = null; PLAN.msg = ''; renderPlanner();
  }
  function planFromProfile(id) {
    ensureWeek(null);
    const A = PLAN.A, e = A.E[id];
    if (byId(id)) { PLAN.sel = id; PLAN.buying = null; renderPlanner(); return { ok: true, already: true, inn: e }; }
    const same = PLAN.line.filter((x) => x.e.element_type === e.element_type).sort((a, b) => A.S5(a.e) - A.S5(b.e));
    const clubs = planClubs();
    const fits = (x) => planBank() + x.sell >= e.now_cost && (x.e.team === e.team || (clubs[e.team] || 0) < 3);
    const pick = same.find(fits) || same[0]; PLAN.msg = '';
    planTransfer(pick.e.id, id);
    return PLAN.msg ? { ok: false, msg: PLAN.msg } : { ok: true, out: pick.e, inn: e };
  }
  // Clear feedback when a player is sent to the planner from any page
  function quickAdd(btn) {
    const r = planFromProfile(+btn.dataset.quick), g = PLAN.gw;
    if (!r.ok) { toast('Could not add the player', r.msg, 'bad'); return; }
    if (r.already) { toast(`${r.inn.web_name} is already in your squad`, `Selected in the GW${g} planner, ready to swap or captain.`, '', { label: 'Open planner', fn: goPlanner }); return; }
    if (btn.classList.contains('qbtn')) btn.classList.add('done');
    else if (btn.classList.contains('try')) { const o = btn.textContent; btn.textContent = '✓ Added'; btn.classList.add('done'); setTimeout(() => { btn.textContent = o; btn.classList.remove('done'); }, 3500); }
    const n = PLAN.swaps.length;
    toast(`Done: ${r.inn.web_name} in, ${r.out.web_name} out`, `GW${g} planner updated · bank ${money(planBank())} · ${n} transfer${n > 1 ? 's' : ''} planned.`, 'good', { label: 'Open planner', fn: goPlanner });
  }
  function planScore() {
    const A = PLAN.A, P = A.P, g0 = PLAN.gw, xi = PLAN.line.slice(0, 11);
    const capPts = PLAN.cap ? P(PLAN.cap.e, g0) * (PLAN.chip === '3xc' ? 2 : 1) : 0;
    const benchPts = PLAN.chip === 'bboost' ? PLAN.line.slice(11).reduce((a, x) => a + P(x.e, g0), 0) : 0;
    return xi.reduce((a, x) => a + P(x.e, g0), 0) + capPts + benchPts;
  }
  // ---- Chips: Wildcard / Free Hit build a new squad; Bench Boost / Triple Captain change scoring ----
  // Squad optimiser: for each formation, cheapest legal bench first, then repeatedly make the starter upgrade with
  // the biggest projected gain that the remaining budget and the 3-per-club rule allow. Keeps the best formation.
  // ================= Squad solver =================
  // value(e) is what the squad is optimised for (projected points, adjusted for the chosen strategy).
  // 1) For each formation: cheapest legal bench, then greedy starter upgrades.
  // 2) Local search: single swaps on any of the 15 places, and paired swaps (downgrade one starter to fund another),
  //    repeated until nothing improves. This explores far more combinations than one greedy path.
  // locks: player ids that must be in the squad; bans: ids that must not.
  function buildSquad(value, cost, budget, opt) {
    opt = opt || {};
    const A = PLAN.A, bans = new Set(opt.bans || []), locks = new Set(opt.locks || []);
    const pool = BS.elements.filter((e) => !bans.has(e.id) && (locks.has(e.id) || (e.status !== 'u' && e.minutes > 0 && A.avail(e, PLAN.gw - A.startGw) > 0.8)));
    const byT = { 1: [], 2: [], 3: [], 4: [] }; pool.forEach((e) => byT[e.element_type].push(e));
    Object.values(byT).forEach((arr) => arr.sort((a, b) => cost(a) - cost(b) || value(b) - value(a)));
    const top = {}; [1, 2, 3, 4].forEach((t) => (top[t] = byT[t].slice().sort((a, b) => value(b) - value(a)).slice(0, 70)));
    const BW = 0.1;   // a bench place is worth 10% of a starting place
    const BMIN = {}; [1, 2, 3, 4].forEach((t) => { const v = top[t].map(value).sort((a, b) => b - a); BMIN[t] = 0.4 * (v[Math.min(v.length - 1, 25)] || 0); });
    const total = (sq) => { const xi = sq.filter((x) => x.role === 'xi'); return xi.reduce((a, x) => a + value(x.e), 0) + Math.max(...xi.map((x) => value(x.e))) + BW * sq.filter((x) => x.role === 'bench').reduce((a, x) => a + value(x.e), 0); };
    let best = null;
    for (const [d, m, f] of [[3, 4, 3], [3, 5, 2], [4, 4, 2], [4, 3, 3], [4, 5, 1], [5, 3, 2], [5, 4, 1]]) {
      const need = { 1: 1, 2: d, 3: m, 4: f }, bneed = { 1: 1, 2: 5 - d, 3: 5 - m, 4: 3 - f };
      const sq = [], clubs = {}, used = new Set(); let ok = true;
      const put = (c, role) => { sq.push({ e: c, role, lock: locks.has(c.id) }); clubs[c.team] = (clubs[c.team] || 0) + 1; used.add(c.id); };
      // locked players first (as starters), then fill
      const lockedBy = { 1: 0, 2: 0, 3: 0, 4: 0 };
      pool.filter((e) => locks.has(e.id)).forEach((e) => { const t = e.element_type; if (lockedBy[t] < need[t] + bneed[t]) { put(e, lockedBy[t] < need[t] ? 'xi' : 'bench'); lockedBy[t]++; } });
      // v3.46: bench fillers must play (at least 40% of a typical starter's projection); the spare goalkeeper may be anyone
      const take = (t, role) => { const ok2 = (e) => role !== 'bench' || t === 1 || value(e) >= BMIN[t]; const c = byT[t].find((e) => !used.has(e.id) && (clubs[e.team] || 0) < 3 && ok2(e)) || byT[t].find((e) => !used.has(e.id) && (clubs[e.team] || 0) < 3); if (!c) { ok = false; return; } put(c, role); };
      [1, 2, 3, 4].forEach((t) => { const lx = Math.min(lockedBy[t], need[t]), lb = lockedBy[t] - lx; for (let k = lb; k < bneed[t]; k++) take(t, 'bench'); for (let k = lx; k < need[t]; k++) take(t, 'xi'); });
      if (!ok) continue;
      let spent = sq.reduce((a, x) => a + cost(x.e), 0); if (spent > budget) continue;
      const swapIn = (x, c) => { clubs[x.e.team]--; used.delete(x.e.id); spent += cost(c) - cost(x.e); x.e = c; clubs[c.team] = (clubs[c.team] || 0) + 1; used.add(c.id); };
      const fits = (x, c, room) => !used.has(c.id) && cost(c) <= room && (c.team === x.e.team || (clubs[c.team] || 0) < 3);
      // greedy upgrades
      for (let it = 0; it < 80; it++) {
        let sw = null;
        sq.filter((x) => x.role === 'xi' && !x.lock).forEach((x) => { const room = budget - spent + cost(x.e), sc = value(x.e);
          byT[x.e.element_type].forEach((c) => { if (!fits(x, c, room)) return; const g = value(c) - sc; if (g > 0.01 && (!sw || g > sw.g)) sw = { x, c, g }; }); });
        if (!sw) break; swapIn(sw.x, sw.c);
      }
      // local search
      for (let it = 0; it < 12; it++) {
        let improved = false;
        // single swaps on all 15 places
        for (const x of sq) { if (x.lock) continue; const w = x.role === 'xi' ? 1 : BW, room = budget - spent + cost(x.e), sc = value(x.e); let bc = null, bg = 0.01;
          for (const c of top[x.e.element_type]) { if (!fits(x, c, room)) continue; const g = (value(c) - sc) * w; if (g > bg) { bg = g; bc = c; } }
          if (bc) { swapIn(x, bc); improved = true; } }
        // paired swaps between two starters: free money in one place, spend it in another
        const xs = sq.filter((x) => x.role === 'xi' && !x.lock); let bp = null, bpg = 0.05;
        for (let i = 0; i < xs.length; i++) for (let j = i + 1; j < xs.length; j++) {
          const a = xs[i], b = xs[j], room = budget - spent + cost(a.e) + cost(b.e), base = value(a.e) + value(b.e);
          const ca = top[a.e.element_type].slice(0, 35), cb = top[b.e.element_type].slice(0, 35);
          for (const c1 of ca) { if (used.has(c1.id) && c1.id !== a.e.id) continue;
            for (const c2 of cb) { if (c2.id === c1.id || (used.has(c2.id) && c2.id !== b.e.id)) continue;
              if (cost(c1) + cost(c2) > room) continue; const g = value(c1) + value(c2) - base; if (g <= bpg) continue;
              const cl = Object.assign({}, clubs); cl[a.e.team]--; cl[b.e.team]--; cl[c1.team] = (cl[c1.team] || 0) + 1; cl[c2.team] = (cl[c2.team] || 0) + 1; if (cl[c1.team] > 3 || cl[c2.team] > 3) continue;
              bpg = g; bp = { a, b, c1, c2 }; } }
        }
        if (bp) { const { a, b, c1, c2 } = bp; clubs[a.e.team]--; clubs[b.e.team]--; used.delete(a.e.id); used.delete(b.e.id); spent += cost(c1) + cost(c2) - cost(a.e) - cost(b.e); a.e = c1; b.e = c2; [c1, c2].forEach((c) => { clubs[c.team] = (clubs[c.team] || 0) + 1; used.add(c.id); }); improved = true; }
        if (!improved) break;
      }
      const tot = total(sq);
      if (!best || tot > best.total) best = { sq: sq.map((x) => ({ e: x.e, role: x.role })), total: tot, spent };
    }
    return best;
  }

  // ================= Simulation: thousands of possible gameweek outcomes =================
  // Each player-week is drawn like real FPL scoring: does he play, goals (Poisson from xG), assists (Poisson
  // from xA), clean sheet (from his team's clean-sheet rate) and bonus that follows returns. A shared "team day"
  // factor moves a club's attack up and its clean-sheet chance down together. Each player's draws are then
  // scaled so his average matches his projection for that week. Every squad is scored on the same draws.
  async function simulate(sets, weeks, N, onProg) {
    const A = PLAN.A, P = A.P; N = N || 5000;
    const ids = new Set(); sets.forEach((s) => s.forEach((id) => ids.add(id)));
    const pl = [...ids].map((id) => A.E[id]); const idx = {}; pl.forEach((e, i) => (idx[e.id] = i));
    const plan = sets.map((s) => weeks.map((g) => { const b = A.bestXIof(s.map((id) => ({ e: A.E[id] })), g); const cap = b.xi.slice().sort((x, y) => P(y.e, g) - P(x.e, g))[0]; return { xi: b.xi.map((x) => idx[x.e.id]), cap: cap ? idx[cap.e.id] : -1 }; }));
    const GP = [0, 6, 6, 5, 4], CSP = [0, 4, 4, 1, 0];
    // per player: play chance, goal and assist rates, clean-sheet chance; per week: scale to the projection
    const prm = pl.map((e) => {
      const r = Math.min(1, A.rel(e) * 1.05), xg = +e.expected_goals_per_90 || (+e.expected_goal_involvements_per_90 || 0) * 0.6, xa = +e.expected_assists_per_90 || (+e.expected_goal_involvements_per_90 || 0) * 0.4;
      const cs = Math.min(0.6, e.clean_sheets_per_90 != null ? +e.clean_sheets_per_90 : 0.25);
      return { t: e.team, pos: e.element_type, play: Math.max(0.05, r), lg: xg * 0.9, la: xa * 0.9, cs };
    });
    const raw = (p) => 2 + p.lg * GP[p.pos] + p.la * 3 + p.cs * CSP[p.pos] + (p.lg + p.la) * 1.6 + (p.pos === 1 ? 0.6 : 0) + (p.pos <= 2 ? p.cs * 0.6 : 0);
    const scale = weeks.map((g, w) => pl.map((e, i) => { const mu = P(e, g); if (!mu) return 0; const p = prm[i]; return mu / Math.max(0.2, p.play * raw(p)); }));
    const nrm = () => { let u = 0, v = 0; while (!u) u = Math.random(); while (!v) v = Math.random(); return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v); };
    const pois = (l) => { if (l <= 0) return 0; const L = Math.exp(-l); let k = 0, p = 1; do { k++; p *= Math.random(); } while (p > L); return k - 1; };
    const out = sets.map(() => new Float64Array(N));
    const pts = new Float64Array(pl.length); const TS = 0.28, tc = Math.exp(-TS * TS / 2);
    const CH = 250;
    for (let r0 = 0; r0 < N; r0 += CH) {
      const r1 = Math.min(N, r0 + CH);
      for (let r = r0; r < r1; r++) {
        for (let w = 0; w < weeks.length; w++) {
          const tf = {}; BS.teams.forEach((t) => (tf[t.id] = Math.exp(TS * nrm()) / tc));
          for (let i = 0; i < pl.length; i++) {
            const sc = scale[w][i]; if (!sc) { pts[i] = 0; continue; }
            const p = prm[i]; if (Math.random() > p.play) { pts[i] = 0; continue; }
            const f = tf[p.t]; const g = pois(p.lg * f), a = pois(p.la * f); const cs = Math.random() < p.cs / f ? 1 : 0;
            const bonus = g * 2 + a > 0 ? Math.min(3, g * 2 + a) : p.pos <= 2 && cs && Math.random() < 0.3 ? 1 : 0;
            pts[i] = (2 + g * GP[p.pos] + a * 3 + cs * CSP[p.pos] + bonus + (p.pos === 1 ? Math.floor(Math.random() * 3) * 0.6 : 0)) * sc;
          }
          for (let s = 0; s < sets.length; s++) { const pp = plan[s][w]; let t = 0; for (const i of pp.xi) t += pts[i]; if (pp.cap >= 0) t += pts[pp.cap]; out[s][r] += t; }
        }
      }
      if (onProg) onProg(r1 / N);
      await new Promise((z) => setTimeout(z, 0));   // let the page breathe between chunks
    }
    return out;
  }
  const pctl = (arr, q) => { const a = Array.from(arr).sort((x, y) => x - y); return a[Math.min(a.length - 1, Math.floor(q * a.length))]; };

  // ================= Rivals: who your mini-league actually owns =================
  const RIVC = {};
  async function loadRivals(lid) {
    const A = PLAN.A; const key = lid + ':' + A.id; if (RIVC[key]) return RIVC[key];
    const st = await J(`/api/leagues-classic/${lid}/standings/`);
    const ents = (st.standings && st.standings.results || []).filter((r) => r.entry !== A.id).slice(0, 25);
    const gw = A.cur ? A.cur.id : A.startGw - 1;
    const picks = await Promise.all(ents.map((r) => J(`/api/entry/${r.entry}/event/${gw}/picks/`).then((p) => ({ r, p })).catch(() => null)));
    const teams = picks.filter((x) => x && x.p && x.p.picks).map((x) => ({ name: x.r.entry_name, ids: x.p.picks.map((p) => p.element) }));
    const eo = {}; teams.forEach((t) => t.ids.forEach((id) => (eo[id] = (eo[id] || 0) + 1 / teams.length)));
    return (RIVC[key] = { lid, name: (st.league || {}).name || 'League', teams, eo });
  }
  const myLeagues = () => (((LASTA || PLAN.A).entry.leagues || {}).classic || []).filter((l) => l.league_type === 'x');
  // ---------- Goal alerts: compare each live refresh with the previous one ----------
  let ALERTS_ON = true; try { ALERTS_ON = localStorage.getItem('fplAnalystAlerts') !== 'off'; } catch (e) {}
  const isExt = () => { try { return !!(typeof chrome !== 'undefined' && chrome.runtime && chrome.runtime.id); } catch (e) { return false; } };
  function deskNotify(title, body) {
    try {
      if (isExt()) { chrome.runtime.sendMessage({ type: 'fpl-notify', title, body }); return; }
      if (window.Notification && Notification.permission === 'granted') new Notification(title, { body });
    } catch (e) {}
  }
  // Update check: once a day, reads version.json from the Elevn GitHub repository and offers the right download
  const UPD_REPO = 'https://raw.githubusercontent.com/Ragxonal/elevn/main/', UPD_K = 'elevnUpd';
  const verNum = (v) => String(v || '').replace(/^v/, '').split('.').map((x) => +x || 0).reduce((a, x, i) => a + x * [1e6, 1e3, 1][i], 0);
  const updKind = () => (hasNative() ? 'apk' : extId() ? 'zip' : 'userscript');
  async function checkUpdate(force) {
    let st = {}; try { st = JSON.parse(localStorage.getItem(UPD_K) || '{}') || {}; } catch (e) {}
    if (!force && st.at && Date.now() - st.at < 864e5) return showUpdate(st);
    try {
      let txt; try { const r = await withTimeout(fetch(UPD_REPO + 'version.json?t=' + Math.floor(Date.now() / 36e5), { credentials: 'omit', cache: 'no-store' }), 8000); if (!r.ok) throw new Error('HTTP ' + r.status); txt = await r.text(); }
      catch (e) { const d = directText(); if (!d) throw e; txt = await withTimeout(d(UPD_REPO + 'version.json'), 9000); }
      const j = JSON.parse(txt); st = Object.assign(st, { at: Date.now(), latest: j.version, notes: j.notes || '', files: j.files || {} });
    } catch (e) { st.at = Date.now() - 864e5 + 36e5; } // try again in an hour
    try { localStorage.setItem(UPD_K, JSON.stringify(st)); } catch (e) {}
    showUpdate(st);
  }
  function showUpdate(st) {
    const bar = R.getElementById('updbar'); if (!bar) return;
    if (!st || !st.latest || verNum(st.latest) <= verNum(ELEVN_VER) || st.skip === st.latest) { bar.hidden = true; return; }
    const k = updKind(), file = (st.files || {})[k], url = file ? (/^https?:/.test(file) ? file : UPD_REPO + file) : 'https://github.com/Ragxonal/elevn';
    const how = k === 'apk' ? 'Download and install it over this app.' : k === 'zip' ? 'Download, unzip over your Elevn folder, then press Reload on chrome://extensions.' : 'Your Userscripts app updates it automatically, or tap Download.';
    bar.innerHTML = `<span class="updtxt"><b>Elevn v${esc(st.latest)} is available</b> (you have v${ELEVN_VER}). ${st.notes ? esc(st.notes) + ' ' : ''}${how}</span><a class="updget" href="${esc(url)}" target="_blank" rel="noopener">Download</a><button type="button" data-updskip>Not now</button>`;
    bar.hidden = false;
    bar.querySelector('[data-updskip]').onclick = () => { st.skip = st.latest; try { localStorage.setItem(UPD_K, JSON.stringify(st)); } catch (e) {} bar.hidden = true; };
  }
  function toast(title, body, tone, act) {
    const box = R.getElementById('toasts'); if (!box) return;
    const t = document.createElement('div'); t.className = 'toast ' + (tone || ''); t.setAttribute('role', 'status');
    t.innerHTML = `<b>${esc(title)}</b><span>${esc(body)}</span>`;
    if (act) { const b = document.createElement('button'); b.type = 'button'; b.className = 'toast-act'; b.textContent = act.label; b.onclick = () => { act.fn(); t.remove(); }; t.appendChild(b); }
    if (/^GOAL/i.test(title) && UI.motion !== 'calm' && !RM()) { t.classList.add('goal'); t.insertAdjacentHTML('afterbegin', '<i class="gball"></i>' + Array.from({ length: 16 }, (_, i) => { const a = (i / 16) * Math.PI * 2, d = 40 + (i % 3) * 18; return `<i class="cf" style="--x:${Math.round(Math.cos(a) * d)}px;--y:${Math.round(Math.sin(a) * d)}px;--r:${(i * 47) % 360}deg;background:${i % 3 ? '#45d08f' : '#f6c343'}"></i>`; }).join('')); }
    box.prepend(t); setTimeout(() => t.classList.add('out'), 9000); setTimeout(() => t.remove(), 9600);
    while (box.children.length > 5) box.lastChild.remove();
  }
  function goalEvents(A, oldL, newL) {
    if (!oldL || !newL || !A.live) return [];
    const T = A.T, ev = [];
    const fixOf = (e) => (A.live.fixtures || []).find((f) => f.team_h === e.team || f.team_a === e.team);
    const score = (e) => { const f = fixOf(e); return f ? ` (${T[f.team_h].short_name} ${f.team_h_score ?? 0}–${f.team_a_score ?? 0} ${T[f.team_a].short_name}${f.minutes ? ' ' + f.minutes + '′' : ''})` : ''; };
    A.live.rows.forEach((r) => {
      const o = oldL[r.e.id] || {}, n = newL[r.e.id] || {}; const m = r.mult || 0; const who = r.e.web_name;
      const d = (k) => (n[k] || 0) - (o[k] || 0);
      const pts = d('total_points') * Math.max(m, 1);
      const tail = `${m > 1 ? ` ×${m} as captain` : m === 0 ? ' (on your bench)' : ''}. ${pts >= 0 ? '+' : ''}${pts} pts.`;
      if (d('goals_scored') > 0) ev.push(['GOAL: ' + who + score(r.e), `${who} scored${tail}`, 'good']);
      if (d('assists') > 0) ev.push(['Assist: ' + who + score(r.e), `${who} got an assist${tail}`, 'good']);
      if (d('penalties_saved') > 0) ev.push(['Penalty saved: ' + who, `${who} saved a penalty${tail}`, 'good']);
      if (d('red_cards') > 0) ev.push(['Red card: ' + who, `${who} was sent off${tail}`, 'bad']);
      if (d('own_goals') > 0) ev.push(['Own goal: ' + who, `${who} scored an own goal${tail}`, 'bad']);
      if (d('penalties_missed') > 0) ev.push(['Penalty missed: ' + who, `${who} missed a penalty${tail}`, 'bad']);
      if ((o.clean_sheets || 0) > 0 && !(n.clean_sheets || 0) && r.e.element_type <= 3) ev.push(['Clean sheet lost: ' + who + score(r.e), `${T[r.e.team].short_name} conceded${tail}`, 'bad']);
      if (d('bonus') > 0) ev.push(['Bonus: ' + who, `${who} gets ${n.bonus} bonus${m > 1 ? ' ×' + m : ''}.`, 'good']);
    });
    return ev;
  }

  // ---------- Live mini-league table and effective ownership (EO) ----------
  const LG = { lid: null, data: null, busy: false, err: '' };
  // v3.11: every league and cup the manager is in: private classic, head-to-head, cups (FPL Cup and league cups), then public leagues
  function allLeagues(A) {
    const L = ((A || LASTA || PLAN.A).entry.leagues) || {}; const out = [];
    const cls = L.classic || [], h2h = L.h2h || [];
    const rk = (l) => ({ rank: l.entry_rank, last: l.entry_last_rank });
    cls.filter((l) => l.league_type === 'x').forEach((l) => out.push(Object.assign({ key: 'x' + l.id, id: l.id, kind: 'classic', name: l.name, grp: 'Leagues' }, rk(l))));
    h2h.forEach((l) => out.push(Object.assign({ key: 'h' + l.id, id: l.id, kind: 'h2h', name: l.name, grp: 'Head-to-head leagues' }, rk(l))));
    const cm = {}; [...((L.cup && L.cup.matches) || []), ...(L.cup_matches || [])].forEach((m) => { if (!m || m.league == null) return; const a = cm[m.league] || (cm[m.league] = []); if (!a.some((x) => x.id === m.id)) a.push(m); });
    const mainCup = L.cup && L.cup.cup_league;
    Object.keys(cm).forEach((lid) => { const host = [...cls, ...h2h].find((l) => l.cup_league === +lid); const nm = +lid === mainCup ? 'FPL Cup' : host ? `${host.name} Cup` : 'Cup'; out.push({ key: 'c' + lid, id: +lid, kind: 'cup', name: nm, grp: 'Cups', matches: cm[lid].sort((a, b) => b.event - a.event) }); });
    // leagues that will run a cup but have no ties yet (FPL draws cups later in the season); private leagues first
    const hasCm = (l) => l.cup_league && cm[l.cup_league];
    [...cls.filter((l) => l.league_type === 'x'), ...h2h, ...cls.filter((l) => l.league_type !== 'x')].filter((l) => l.has_cup && !hasCm(l)).forEach((l) => out.push({ key: 'p' + l.id, id: l.id, kind: 'cup', name: l.id === 314 || l.name === 'Overall' ? 'FPL Cup' : `${l.name} Cup`, grp: 'Cups', matches: [], pending: true, status: l.id === 314 || l.name === 'Overall' ? L.cup && L.cup.status : null }));
    cls.filter((l) => l.league_type !== 'x').forEach((l) => out.push(Object.assign({ key: 'x' + l.id, id: l.id, kind: 'classic', name: l.name, grp: 'Public leagues', pub: true }, rk(l))));
    return out;
  }
  async function loadLeagueLive(A, key) {
    const lg = allLeagues(A).find((l) => l.key === key) || allLeagues(A)[0]; if (!lg) throw new Error('no league');
    const ck = 'L' + key + ':' + A.id + ':' + (A.cur ? A.cur.id : 0); if (RIVC[ck]) return RIVC[ck];
    const gw = A.cur ? A.cur.id : A.startGw - 1;
    const pickOf = (entry) => J(`/api/entry/${entry}/event/${gw}/picks/`).catch(() => null);
    const team = (r, p) => ({ entry: r.entry, name: r.entry_name, player: r.player_name, rank: r.rank, lpts: r.lpts, total: p.entry_history ? p.entry_history.total_points : r.total, ev: p.entry_history ? p.entry_history.points : 0, picks: p.picks, hit: (p.entry_history && p.entry_history.event_transfers_cost) || 0, chip: p.active_chip });
    if (lg.kind === 'cup') {
      const cur = lg.matches.filter((m) => m.event === gw);
      const opp = cur.map((m) => (m.entry_1_entry === A.id ? { entry: m.entry_2_entry, entry_name: m.entry_2_name, player_name: m.entry_2_player_name } : { entry: m.entry_1_entry, entry_name: m.entry_1_name, player_name: m.entry_1_player_name })).filter((r) => r.entry);
      const ps = await Promise.all(opp.map((r) => pickOf(r.entry).then((p) => (p && p.picks ? team(r, p) : null))));
      return (RIVC[ck] = { key, kind: 'cup', name: lg.name, lg, gw, teams: ps.filter(Boolean), me: null });
    }
    const st = await J(lg.kind === 'h2h' ? `/api/leagues-h2h/${lg.id}/standings/` : `/api/leagues-classic/${lg.id}/standings/`);
    const res = ((st.standings && st.standings.results) || []).map((r) => Object.assign({}, r, { lpts: r.total }));
    const ents = res.filter((r) => r.entry !== A.id).slice(0, 25);
    const me = res.find((r) => r.entry === A.id);
    const picks = await Promise.all(ents.map((r) => pickOf(r.entry).then((p) => ({ r, p }))));
    const teams = picks.filter((x) => x && x.p && x.p.picks).map((x) => team(x.r, x.p));
    let match = null;
    if (lg.kind === 'h2h') { try { const mm = await J(`/api/leagues-h2h-matches/league/${lg.id}/?event=${gw}&page=1`); match = ((mm && mm.results) || []).find((m) => m.entry_1_entry === A.id || m.entry_2_entry === A.id) || null; } catch (e) {} }
    const full = !(st.standings && st.standings.has_next) && res.length <= ents.length + 1;
    return (RIVC[ck] = { key, kind: lg.kind, name: (st.league || {}).name || lg.name, lg, gw, teams, match, full, me: me ? { rank: me.rank, lpts: me.total } : { rank: lg.rank || null, lpts: null } });
  }
  function rivalLive(A, t) {
    const L = A.gwCmp && A.gwCmp.liveC; if (!L) return { pts: 0, left: 0, cap: null };
    const prov = {}; (A.live ? A.live.fixtures : []).filter((f) => f.started && !f.finished).forEach((f) => Object.assign(prov, provisionalBonus(f)));
    let pts = 0, left = 0, cap = null;
    t.picks.forEach((p) => {
      const st = L[p.element] || {}; const v = (st.total_points || 0) + (st.bonus ? 0 : prov[p.element] || 0);
      if (p.multiplier > 0) { pts += v * p.multiplier; const e = A.E[p.element]; const fs = (A.live ? A.live.fixtures : []).filter((f) => f.team_h === e.team || f.team_a === e.team); if (fs.some((f) => !f.finished_provisional && !f.finished)) left++; }
      if (p.is_captain) cap = { e: A.E[p.element], v: v * p.multiplier };
    });
    return { pts: pts - t.hit, left, cap };
  }
  const TOPI = ['', '👑', '🥈', '🥉', '🚀', '🔥'], TOPT = ['', 'Leader', 'Second', 'Third', 'Fourth', 'Fifth'];
  const topCls = (k) => (k >= 1 && k <= 5 ? 'lgtop lgtop' + k : '');
  const topIco = (k) => (k >= 1 && k <= 5 ? `<span class="tico t${k}" title="${TOPT[k]}" aria-label="${TOPT[k]}">${TOPI[k]}</span>` : '');
  function leagueHtml(A) {
    const lg = allLeagues(A);
    if (!lg.length) return '<p class="muted">This team is not in any league or cup yet.</p>';
    const grps = [...new Set(lg.map((l) => l.grp))];
    const cur = lg.find((l) => l.key === LG.lid) || lg[0];
    const LT = { classic: 'League', h2h: 'H2H', cup: 'Cup' };
    const sel = `<div class="lgpk"><button type="button" class="lgbtn" data-lgtog="1" aria-haspopup="listbox" aria-expanded="false"><span class="lt t-${cur.kind}">${LT[cur.kind]}</span><span class="ln">${esc(cur.name)}</span><span class="lr">${lgRank(A, cur)}</span><svg viewBox="0 0 24 24" width="16" height="16" aria-hidden="true"><path d="M6 9l6 6 6-6" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round"/></svg></button>
<div class="lgmenu" role="listbox" aria-label="League or cup" hidden>${grps.map((g) => `<div class="lgg">${esc(g)}</div>${lg.filter((l) => l.grp === g).map((l) => `<button type="button" role="option" aria-selected="${l.key === cur.key}" class="hlr${l.key === cur.key ? ' on' : ''}${l.pub ? ' pub' : ''}" data-lgopen="${l.key}"><span class="lt t-${l.kind}">${LT[l.kind]}</span><span class="ln">${esc(l.name)}</span><span class="lr">${lgRank(A, l)}</span></button>`).join('')}`).join('')}</div></div>`;
    const ttl = cur.kind === 'cup' ? 'Cup' : cur.kind === 'h2h' ? 'Head-to-head league' : 'Live mini-league';
    if (LG.busy) return `<div class="wch"><b>${ttl}</b>${sel}</div><p class="muted"><span class="spin"></span> Loading your rivals' teams…</p>`;
    if (LG.err) return `<div class="wch"><b>${ttl}</b>${sel}</div><div class="err">${esc(LG.err)}</div>`;
    const D = LG.data; if (!D) return `<div class="wch"><b>${ttl}</b>${sel}</div>`;
    const T = A.T; const L = A.live;
    const meRow = { me: true, name: A.entry.name, player: 'You', rank: D.me ? D.me.rank : null, lpts: D.me ? D.me.lpts : null, prev: A.entry.summary_overall_points - (L ? L.pts : 0), live: L ? L.pts : 0, left: L ? L.toPlay : 0, cap: L ? L.rows.find((r) => r.x.is_captain) : null };
    const rows = [meRow, ...D.teams.map((t) => { const r = rivalLive(A, t); return { entry: t.entry, name: t.name, player: t.player, rank: t.rank, lpts: t.lpts, prev: t.total - t.ev, live: r.pts, left: r.left, capE: r.cap }; })];
    rows.forEach((r) => (r.tot = r.prev + r.live));
    const capTxt = (r) => (r.me ? (r.cap ? `${esc(r.cap.e.web_name)} ${r.cap.pts * r.cap.mult}` : '–') : r.capE ? `${esc(r.capE.e.web_name)} ${r.capE.v}` : '–');
    const open = (r) => (r.me || !r.entry ? '' : `data-entry="${r.entry}" data-tname="${esc(r.name)}" tabindex="0" role="link" title="Open ${esc(r.name)}"`);
    if (D.kind === 'cup') {
      const ms = (cur.matches || []);
      const live = rows.find((r) => !r.me);
      const st = cur.status;
      const res = (m) => { const mine1 = m.entry_1_entry === A.id; const w = m.winner; return !w ? '<span class="pill p-wait">To play</span>' : w === A.id ? '<span class="pill p-core">Won</span>' : '<span class="pill p-sell">Lost</span>'; };
      return `<div class="wch"><b>${esc(cur.name)}</b>${sel}</div>
${live ? `<div class="cuplive"><div><small class="muted">GW${D.gw} live</small><b>You ${meRow.live}</b><span class="muted">vs</span><b>${live.live} ${esc(live.name)}</b></div><span class="${meRow.live > live.live ? 'up' : meRow.live < live.live ? 'dn' : 'muted'}">${meRow.live > live.live ? `Winning by ${meRow.live - live.live}` : meRow.live < live.live ? `Losing by ${live.live - meRow.live}` : 'Level'}</span></div>` : ''}
${ms.length ? `<div class="tw"><table class="lgt"><thead><tr><th>GW</th><th>Round</th><th>You</th><th></th><th>Opponent</th><th>Result</th></tr></thead><tbody>${ms.map((m) => { const me1 = m.entry_1_entry === A.id; const op = me1 ? { e: m.entry_2_entry, n: m.entry_2_name, p: m.entry_2_player_name, s: m.entry_2_points } : { e: m.entry_1_entry, n: m.entry_1_name, p: m.entry_1_player_name, s: m.entry_1_points }; const my = me1 ? m.entry_1_points : m.entry_2_points;
        return `<tr class="${op.e ? 'lgopen' : ''}" ${op.e ? `data-entry="${op.e}" data-tname="${esc(op.n)}" tabindex="0" role="link" title="Open ${esc(op.n)}"` : ''}><td>${m.event}</td><td>${esc(m.knockout_name || '')}</td><td class="n"><b>${my ?? '–'}</b></td><td class="muted">–</td><td><b>${op.s ?? '–'}</b> ${op.e ? `${esc(op.n)} <small class="muted">${esc(op.p || '')}</small>` : '<small class="muted">Bye</small>'}</td><td>${m.is_bye ? '<span class="pill p-keep">Bye</span>' : res(m)}</td></tr>`; }).join('')}</tbody></table></div>` : `<p class="muted">${st && st.qualification_event ? `The FPL Cup starts after GW${st.qualification_event}. ${st.qualification_state ? 'Status: ' + esc(String(st.qualification_state).replace(/_/g, ' ').toLowerCase()) + '.' : ''}` : 'This cup has not started yet. FPL draws the cups later in the season; once it does, every tie appears here with live scores.'}</p>`}
<p class="note">Cup ties are decided by the gameweek score. Tap an opponent to open their team.</p>`;
    }
    if (D.kind === 'h2h') {
      rows.sort((a, b) => (a.rank || 999) - (b.rank || 999));
      const m = D.match; const vs = m && (m.entry_1_entry === A.id ? { e: m.entry_2_entry, n: m.entry_2_name } : { e: m.entry_1_entry, n: m.entry_1_name });
      const vr = vs && rows.find((r) => r.entry === vs.e);
      return `<div class="wch"><b>Head-to-head · ${esc(D.name)}</b>${sel}</div>
${vs ? `<div class="cuplive"><div><small class="muted">GW${D.gw} match</small><b>You ${meRow.live}</b><span class="muted">vs</span><b>${vr ? vr.live : (m.entry_1_entry === A.id ? m.entry_2_points : m.entry_1_points)} ${esc(vs.n || 'Average')}</b></div></div>` : ''}
<div class="tw"><table class="lgt"><thead><tr><th class="n">#</th><th>Team</th><th class="n">League pts</th><th class="n">GW live</th><th class="n">FPL total</th><th>Captain</th><th class="n">To play</th></tr></thead><tbody>${rows.map((r) => `<tr class="${r.me ? 'mine me' : 'lgopen'} ${topCls(r.rank)}" ${open(r)}><td class="n"><b>${r.rank ? r.rank.toLocaleString() : '–'}</b></td><td>${topIco(r.rank)}<b>${esc(r.name)}</b> <small class="muted">${esc(r.player || '')}</small></td><td class="n"><b>${r.lpts ?? '–'}</b></td><td class="n"><b>${r.live}</b></td><td class="n">${r.tot.toLocaleString()}</td><td>${capTxt(r)}</td><td class="n">${r.left}</td></tr>`).join('')}</tbody></table></div>
<p class="note">Head-to-head table from FPL (3 points for a win, 1 for a draw). GW live scores use each team's picked lineup with provisional bonus. Tap a team to open its account.</p>`;
    }
    // v3.12: only the top of a big league is loaded, so a manager below it keeps the real league position
    const topMax = Math.max(0, ...D.teams.map((x) => x.rank || 0));
    const outside = !D.full && meRow.rank && meRow.rank > topMax;
    let gapAt = -1;
    if (outside) { const others = rows.filter((r) => !r.me).sort((a, b) => b.tot - a.tot); others.forEach((r, i) => (r.lrank = i + 1)); meRow.lrank = meRow.rank; rows.length = 0; rows.push(...others, meRow); gapAt = others.length; }
    else { rows.sort((a, b) => b.tot - a.tot); rows.forEach((r, i) => (r.lrank = i + 1)); }
    const mv = (r) => { if (!r.rank || (outside && r.me)) return ''; const d = r.rank - r.lrank; return d > 0 ? `<span class="up">▲${d}</span>` : d < 0 ? `<span class="dn">▼${-d}</span>` : '<span class="muted">–</span>'; };
    return `<div class="wch"><b>Live mini-league · ${esc(D.name)}</b>${sel}</div>
<div class="tw"><table class="lgt"><thead><tr><th class="n">#</th><th></th><th>Team</th><th class="n">GW live</th><th class="n">Total</th><th>Captain</th><th class="n">To play</th></tr></thead><tbody>${rows.map((r, i) => `${i === gapAt ? `<tr class="lggap"><td colspan="7">⋯ ${(meRow.rank - topMax - 1).toLocaleString()} more managers ⋯</td></tr>` : ''}<tr class="${r.me ? 'mine me' : 'lgopen'} ${topCls(r.lrank)}" ${r.me || !r.entry ? '' : `data-entry="${r.entry}" data-tname="${esc(r.name)}" tabindex="0" role="link" title="Open ${esc(r.name)}"`}><td class="n"><b>${r.lrank.toLocaleString()}</b></td><td>${mv(r)}</td><td>${topIco(r.lrank)}<b>${esc(r.name)}</b> <small class="muted">${esc(r.player || '')}</small></td><td class="n"><b>${r.live}</b></td><td class="n">${r.tot.toLocaleString()}</td><td>${capTxt(r)}</td><td class="n">${r.left}</td></tr>`).join('')}</tbody></table></div>
<p class="note">Top ${D.teams.length} rivals of the league plus you. Rivals' scores use their picked lineup with provisional bonus; their automatic substitutions are added by FPL after the matches. Arrows compare with the league table before this gameweek. Tap a team to open its account.</p>`;
  }
  // EO = how many points-weight the league holds in a player: owners count 1, captains 2 (triple captain 3), benched 0.
  // You gain on the league average by (your multiplier − EO) for every point he scores.
  // ======================= 7. rival watch: the managers just above and below you =======================
  const RVP = {}; let rvBusy = false;
  async function rivalPrev(A) {
    const D = LG.data; if (!D || rvBusy || D.kind === 'cup') return;
    const near = rivalsNear(A).filter((r) => !RVP[r.entry + ':' + D.gw]); if (!near.length) return;
    rvBusy = true;
    await Promise.all(near.map((r) => J(`/api/entry/${r.entry}/event/${D.gw - 1}/picks/`).then((x) => (RVP[r.entry + ':' + D.gw] = x)).catch(() => (RVP[r.entry + ':' + D.gw] = { picks: [] }))));
    rvBusy = false; const b = R.getElementById('rv-box'); if (b) b.innerHTML = rivalHtml(A);
  }
  function rivalsNear(A) {
    const D = LG.data; if (!D || !D.teams || !D.teams.length) return [];
    const L = A.live; const myTot = A.entry.summary_overall_points - (L ? L.pts : 0) + (L ? L.pts : 0);
    const rs = D.teams.map((t) => { const r = rivalLive(A, t); return { entry: t.entry, name: t.name, player: t.player, rank: t.rank, chip: t.chip, picks: t.picks, live: r.pts, tot: t.total - t.ev + r.pts }; });
    const all = rs.concat([{ me: true, tot: myTot }]).sort((a, b) => b.tot - a.tot); const i = all.findIndex((x) => x.me);
    return all.slice(Math.max(0, i - 3), i + 3).filter((x) => !x.me);
  }
  function rivalHtml(A) {
    const D = LG.data; if (!D) return '<p class="muted">Pick a league in Mini-league first.</p>';
    if (D.kind === 'cup') return '<p class="muted">Rival watch works for leagues. For a cup, your opponent is shown in Mini-league.</p>';
    const T = A.T, L = A.live, live = A.gwCmp && A.gwCmp.liveC; const myTot = A.entry.summary_overall_points;
    const mine = {}; (L ? L.rows : []).forEach((r) => (mine[r.e.id] = r.mult || 0)); if (!L) A.picks.forEach((p) => (mine[p.element] = p.multiplier || 0));
    const G = { 1: 10, 2: 6, 3: 5, 4: 4 }; const CH = { bboost: 'Bench Boost', '3xc': 'Triple Captain', freehit: 'Free Hit', wildcard: 'Wildcard', manager: 'Assistant Manager' };
    const near = rivalsNear(A); if (!near.length) return '<p class="muted">Rival watch appears once the league table has loaded.</p>';
    const nm = (id) => { const e = A.E[id]; return e ? `<a class="pn" href="#" data-pid="${id}">${esc(e.web_name)}</a>` : '?'; };
    const cards = near.map((r) => {
      const gap = r.tot - myTot; const cap = r.picks.find((q) => q.is_captain); const capE = cap && A.E[cap.element];
      const prev = RVP[r.entry + ':' + D.gw]; const was = prev && prev.picks ? new Set(prev.picks.map((q) => q.element)) : null; const now = new Set(r.picks.map((q) => q.element));
      const tin = was ? [...now].filter((id) => !was.has(id)) : null, tout = was ? [...was].filter((id) => !now.has(id)) : null;
      const danger = r.picks.filter((q) => (q.multiplier || 0) > (mine[q.element] || 0)).map((q) => { const e = A.E[q.element]; const d = (q.multiplier || 0) - (mine[q.element] || 0); const fs = (L ? L.fixtures : []).filter((f) => f.team_h === e.team || f.team_a === e.team); const left = !fs.length || fs.some((f) => !f.finished_provisional && !f.finished); return { e, d, pts: live && live[e.id] ? live[e.id].total_points || 0 : 0, left, goal: G[e.element_type] * d, p: A.P ? A.P(e, A.startGw) : 0 }; }).sort((a, b) => b.left - a.left || b.goal - a.goal).slice(0, 4);
      const top = danger.find((x) => x.left);
      const line = top ? `If <b>${esc(top.e.web_name)}</b> scores, ${esc(r.name)} gains <b>${top.goal}</b> on you${Math.abs(gap) <= top.goal + 2 ? (gap > 0 ? ' and pulls further clear.' : gap < 0 ? ` and ${gap + top.goal > 0 ? '<b>overtakes you</b>' : 'closes the gap'}.` : ' and goes ahead.') : '.'}` : 'None of their extra players has a match left.';
      return `<div class="rvc"><div class="rvh"><span class="rvr">${r.rank ? '#' + r.rank : ''}</span><div><b>${esc(r.name)}</b><small>${esc(r.player || '')}</small></div><span class="rvg ${gap > 0 ? 'dn' : 'up'}">${gap > 0 ? `${gap} ahead of you` : gap < 0 ? `${-gap} behind you` : 'level'}</span></div>
<div class="rvs"><span><small>GW live</small><b>${r.live}</b></span><span><small>Captain</small><b>${capE ? nm(capE.id) : '–'}${cap && cap.multiplier === 3 ? ' ×3' : ''}</b></span><span><small>Chip</small><b>${r.chip ? CH[r.chip] || r.chip : 'None'}</b></span></div>
<div class="rvt">${tin == null ? '<small class="muted">Loading their transfers…</small>' : tin.length ? `<span class="mv"><i class="mi">IN</i>${tin.map(nm).join(', ')}</span><span class="mv"><i class="mo">OUT</i>${tout.map(nm).join(', ')}</span>` : '<small class="muted">No transfers this week</small>'}</div>
${danger.length ? `<div class="rvd"><small>Their extra players</small>${danger.map((x) => `<span class="${x.left ? '' : 'done'}">${nm(x.e.id)}${x.d > 1 ? ' ×' + (x.d + (mine[x.e.id] || 0)) : ''} <b>${x.pts}</b></span>`).join('')}</div>` : ''}
<p class="rvl">${line}</p></div>`; }).join('');
    return `<p class="note" style="margin:0 0 8px">The managers just above and below you in <b>${esc(D.name)}</b>: their moves for GW${D.gw} (visible after the deadline), captain, chip, and the players they have that you don't.</p><div class="rvgrid">${cards}</div>`;
  }
  // v3.71: who captains whom. Mini-league: every team. Overall: 100 managers sampled evenly from the top 10,000 (cached per gameweek).
  const CAPS = {};
  async function capSample(gw) {
    const k = 'elevnCap_' + gw; if (CAPS[gw]) return CAPS[gw];
    try { const c = JSON.parse(localStorage.getItem(k) || 'null'); if (c && c.n) return (CAPS[gw] = c); } catch (e) {}
    CAPS[gw] = { busy: true };
    try {
      const pages = Array.from({ length: 10 }, (_, i) => 1 + i * 20); const ents = [];
      for (const pg of pages) { try { const st = await J(`/api/leagues-classic/314/standings/?page_standings=${pg}`); ((st.standings || {}).results || []).forEach((r, i) => { if (i % 5 === 0) ents.push(r.entry); }); } catch (e) {} }
      const out = { n: 0, cap: {}, tc: {}, own: {}, at: Date.now() }; let q = ents.slice();
      const worker = async () => { while (q.length) { const id = q.shift(); try { const p = await J(`/api/entry/${id}/event/${gw}/picks/`); if (!p || !p.picks) continue; out.n++; p.picks.forEach((x) => { out.own[x.element] = (out.own[x.element] || 0) + 1; if (x.is_captain) { out.cap[x.element] = (out.cap[x.element] || 0) + 1; if (x.multiplier === 3) out.tc[x.element] = (out.tc[x.element] || 0) + 1; } }); } catch (e) {} } };
      await Promise.all(Array.from({ length: 6 }, worker));
      if (out.n >= 20) { CAPS[gw] = out; try { localStorage.setItem(k, JSON.stringify(out)); } catch (e) {} } else CAPS[gw] = { err: true, at: Date.now() };
    } catch (e) { CAPS[gw] = { err: true, at: Date.now() }; }
    return CAPS[gw];
  }
  function capsHtml(A) {
    const gw = A.cur ? A.cur.id : null; if (!gw) return '';
    const S = CAPS[gw]; if (!S) { capSample(gw).then(() => { if (LASTA) paintLeague(LASTA); }); }
    const D = LG.data && LG.data.gw === gw ? LG.data : null; const lc = {}; let ln = 0;
    if (D) { D.teams.forEach((t) => { const c = (t.picks || []).find((x) => x.is_captain); if (c) { lc[c.element] = (lc[c.element] || 0) + 1; ln++; } }); }
    const myC = (A.live ? A.live.rows : []).find((r) => r.x && r.x.is_captain); if (D && myC) { lc[myC.e.id] = (lc[myC.e.id] || 0) + 1; ln++; }
    const ok = S && S.n; const ids = new Set([...Object.keys(lc), ...(ok ? Object.keys(S.cap) : [])].map(Number));
    const rows = [...ids].map((id) => ({ e: A.E[id], l: lc[id] || 0, s: ok ? (S.cap[id] || 0) / S.n : 0, tc: ok ? S.tc[id] || 0 : 0 })).filter((r) => r.e).sort((a, b) => b.s - a.s || b.l - a.l).slice(0, 10);
    if (!rows.length) return `<div class="capbox"><div class="wch"><b>Captains · GW${gw}</b></div><p class="muted">${S && S.busy ? 'Counting captains in the top 10k…' : S && S.err ? 'Couldn\'t load captain picks right now.' : 'Captain picks show after the deadline.'}</p></div>`;
    const top = rows[0].s || 1; const nm = (e) => `<a class="pn" href="#" data-pi="1" data-pid="${e.id}">${esc(e.web_name)}</a>`;
    return `<div class="capbox"><div class="wch"><b>Captains · GW${gw}</b><span class="muted">${ok ? `Top 10k: sample of ${S.n} managers` : S && S.busy ? 'Counting the top 10k…' : ''}${D ? ` · <bdi>${esc(D.name)}</bdi>: ${ln} teams` : ''}</span></div>
<div class="capl">${rows.map((r) => `<div class="capr${myC && myC.e.id === r.e.id ? ' mine' : ''}">${pface(r.e)}<span class="capn">${nm(r.e)}<small>${esc(A.T[r.e.team].short_name)} · owned ${r.e.selected_by_percent}%${myC && myC.e.id === r.e.id ? ' · <b>your captain</b>' : ''}</small></span><span class="capbar"><i style="width:${Math.round((r.s / top) * 100)}%"></i></span><span class="capv"><b>${ok ? Math.round(r.s * 100) + '%' : '–'}</b><small>top 10k${r.tc ? ` · ${r.tc} TC` : ''}</small></span>${D ? `<span class="capv"><b>${r.l} of ${ln}</b><small>your league</small></span>` : ''}</div>`).join('')}</div></div>`;
  }
  function eoHtml(A) {
    const D = LG.data; if (!D || !D.teams.length) return capsHtml(A);
    const T = A.T, n = D.teams.length, L = A.gwCmp && A.gwCmp.liveC;
    const eo = {}; D.teams.forEach((t) => t.picks.forEach((p) => (eo[p.element] = (eo[p.element] || 0) + (p.multiplier || 0) / n)));
    const mine = {}; (A.live ? A.live.rows : []).forEach((r) => (mine[r.e.id] = r.mult || 0));
    if (!A.live) A.picks.forEach((p) => (mine[p.element] = p.multiplier != null ? p.multiplier : p.position <= 11 ? 1 : 0));
    const ids = new Set([...Object.keys(eo).map(Number), ...Object.keys(mine).map(Number)]);
    const rows = [...ids].map((id) => { const e = A.E[id]; const pts = L && L[id] ? L[id].total_points || 0 : 0; const m = mine[id] || 0, o = eo[id] || 0; return { e, m, o, d: m - o, pts, swing: pts * (m - o) }; }).filter((r) => r.e);
    const net = rows.reduce((a, r) => a + r.swing, 0);
    const edge = rows.filter((r) => r.d > 0.05).sort((a, b) => b.d - a.d || b.swing - a.swing).slice(0, 8);
    const threat = rows.filter((r) => r.d < -0.25).sort((a, b) => a.d - b.d || a.swing - b.swing).slice(0, 8);
    const nm = (e) => `<a class="pn" href="#" data-pid="${e.id}">${esc(e.web_name)}</a>`;
    const li = (r) => `<li><span class="who"><b>${nm(r.e)}</b><small class="muted"> ${T[r.e.team].short_name}</small></span><span class="eo">you ×${r.m} · league EO ${(r.o * 100).toFixed(0)}%</span><span class="${r.swing > 0 ? 'up' : r.swing < 0 ? 'dn' : 'muted'}">${r.pts ? `${r.swing > 0 ? '+' : ''}${r.swing.toFixed(1)}` : `${r.d > 0 ? '+' : ''}${r.d.toFixed(2)}/pt`}</span></li>`;
    return `${capsHtml(A)}<div class="eobox"><div class="wch"><b>Effective ownership & threats</b><span class="${net > 0 ? 'up' : net < 0 ? 'dn' : 'muted'}">${A.live ? `Net swing this GW: ${net > 0 ? '+' : ''}${net.toFixed(1)} pts vs league average` : ''}</span></div>
<p class="note" style="margin:0 0 8px">EO counts how heavily your rivals hold a player: owned = 1, captained = 2, benched = 0. When he scores, you gain the difference between your multiplier and the league's EO for each point.</p>
<div class="grid2"><div><h3 class="h3">Your edge</h3><ul class="eol">${edge.map(li).join('') || '<li class="muted">No players where you are ahead of the league.</li>'}</ul></div>
<div><h3 class="h3">Threats (rivals have, you don't)</h3><ul class="eol">${threat.map(li).join('') || '<li class="muted">No big threats.</li>'}</ul></div></div></div>`;
  }
  async function refreshLeague(A, force) {
    const lg = allLeagues(A); if (!lg.length) return paintLeague(A);
    if (LG.lid == null) LG.lid = lgDefault(lg);
    if (LG.aid !== A.id) { LG.aid = A.id; LG.data = null; if (!lg.some((l) => l.key === LG.lid)) LG.lid = lgDefault(lg); }
    if (LG.data && LG.data.key === LG.lid && !force) return paintLeague(A);
    LG.busy = true; LG.err = ''; paintLeague(A);
    // a slower earlier load must not overwrite the league or cup chosen since
    const want = LG.lid; let d = null, err = '';
    try { d = await loadLeagueLive(A, want); } catch (e) { err = 'Could not load that league right now.'; }
    if (LG.lid !== want) return;
    LG.data = d; LG.err = err; LG.busy = false; paintLeague(A);
  }
  // Home: every league and cup with this team's rank; tap one to open its live table
  function lgRank(A, l) { if (l.kind === 'cup') { const m = (l.matches || [])[0]; if (!m) return l.status && l.status.qualification_event ? `<small class="muted">Starts after GW${l.status.qualification_event}</small>` : '<small class="muted">Not started</small>'; const w = m.winner; return `<small class="muted">GW${m.event}</small> ${!w ? '<span class="pill p-wait">To play</span>' : w === A.id ? '<span class="pill p-core">Won</span>' : '<span class="pill p-sell">Out</span>'}`; }
    const d = l.last && l.rank ? l.last - l.rank : 0; return `<b>${l.rank ? l.rank.toLocaleString() : '–'}</b>${d ? ` <span class="${d > 0 ? 'up' : 'dn'}">${d > 0 ? '▲' : '▼'}${Math.abs(d).toLocaleString()}</span>` : ''}`; }
  // first league with a live table: private leagues, then head-to-head, then public; cups only once drawn
  const lgDefault = (lg) => (lg.find((l) => l.kind !== 'cup' && !l.pub) || lg.find((l) => l.kind === 'cup' && !l.pending) || lg.find((l) => l.kind !== 'cup') || lg[0]).key;
  out.addEventListener('click', (ev) => {
    const t = ev.target; if (!t.closest) return;
    const tg = t.closest('[data-lgtog]'); const menus = R.querySelectorAll('.lgmenu');
    if (tg) { const m = tg.parentElement.querySelector('.lgmenu'); const open = m.hidden; menus.forEach((x) => (x.hidden = true)); m.hidden = !open; tg.setAttribute('aria-expanded', open); if (open) { const on = m.querySelector('.on'); if (on) on.scrollIntoView({ block: 'nearest' }); } return; }
    if (!t.closest('.lgmenu')) menus.forEach((x) => (x.hidden = true));
  });
  function homeLeagues(A) {
    const lg = allLeagues(A); const can = !!A.live;
    const tag = { classic: 'League', h2h: 'H2H', cup: 'Cup' };
    const rankTxt = (l) => lgRank(A, l);
    const rankOld = (l) => { if (l.kind === 'cup') { const m = (l.matches || [])[0]; if (!m) return l.status && l.status.qualification_event ? `<small class="muted">Starts after GW${l.status.qualification_event}</small>` : '<small class="muted">Not started</small>'; const w = m.winner; return `<small class="muted">GW${m.event}</small> ${!w ? '<span class="pill p-wait">To play</span>' : w === A.id ? '<span class="pill p-core">Won</span>' : '<span class="pill p-sell">Out</span>'}`; }
      const d = l.last && l.rank ? l.last - l.rank : 0; return `${l.rank && l.rank <= 5 ? TOPI[l.rank] + ' ' : ''}<b>${l.rank ? l.rank.toLocaleString() : '–'}</b>${d ? ` <span class="${d > 0 ? 'up' : 'dn'}">${d > 0 ? '▲' : '▼'}${Math.abs(d).toLocaleString()}</span>` : ''}`; };
    return `<div class="th"><h3>Leagues &amp; cups</h3><span class="muted">${lg.length} for ID ${A.id}</span></div>
${(() => { if (!lg.length) return '<p class="muted">Not in any league or cup.</p>'; const row = (l) => `<button type="button" class="hlr${l.pub ? ' pub' : ''}" ${can ? `data-lgopen="${l.key}"` : 'disabled'} title="${can ? 'Open the live table' : ''}"><span class="lt t-${l.kind}">${tag[l.kind]}</span><span class="ln">${esc(l.name)}</span><span class="lr">${rankTxt(l)}</span></button>`;
      const ord = lg.slice().sort((a, b) => (a.kind === 'cup' && a.pending) - (b.kind === 'cup' && b.pending)); const top = ord.slice(0, 5), rest = ord.slice(5);
      return `<div class="hlist">${top.map(row).join('')}</div>${rest.length ? `<details class="hlmore"><summary>Show all ${lg.length}</summary><div class="hlist">${rest.map(row).join('')}</div></details>` : ''}`; })()}`;
  }
  out.addEventListener('click', (ev) => { const b = ev.target.closest && ev.target.closest('[data-lgopen]'); if (!b || !LASTA) return; LG.lid = b.dataset.lgopen; LIVETAB = 'leagues'; showView('live'); const sec = R.getElementById('s-live'); if (sec) { sec.querySelectorAll('[data-ltab]').forEach((x) => { const on = x.dataset.ltab === 'leagues'; x.classList.toggle('on', on); x.setAttribute('aria-selected', on); }); sec.querySelectorAll('[data-lpanel]').forEach((p) => { p.hidden = p.dataset.lpanel !== 'leagues'; }); } refreshLeague(LASTA, true); });
  function paintLeague(A) {
    const b = R.getElementById('lg-box'); if (b) b.innerHTML = leagueHtml(A);
    const e = R.getElementById('eo-box'); if (e) e.innerHTML = eoHtml(A) || '<p class="muted">Effective ownership appears once your mini-league has loaded.</p>';
    const rv = R.getElementById('rv-box'); if (rv) rv.innerHTML = rivalHtml(A);
    rivalPrev(A);
  }

  // ---------- Fixture rotation pairs ----------
  const ROT = { n: 6, anchor: 0, pos: 1 };
  function rotHtml(A) {
    const T = A.T, lastG = Math.min(38, A.startGw + ROT.n - 1);
    const gws = []; for (let g = A.startGw; g <= lastG; g++) gws.push(g);
    const best = (team, g) => { const fs = A.fxBy[team + '-' + g] || []; if (!fs.length) return 5; const m = Math.min(...fs.map((f) => f.diff)); return fs.length > 1 ? Math.max(1, m - 0.5) : m; };
    const ids = BS.teams.map((t) => t.id);
    const pairs = [];
    for (let i = 0; i < ids.length; i++) for (let j = i + 1; j < ids.length; j++) {
      const a = ids[i], b = ids[j]; if (ROT.anchor && a !== ROT.anchor && b !== ROT.anchor) continue;
      const tiles = gws.map((g) => { const x = best(a, g), y = best(b, g); return { g, v: Math.min(x, y), both: x >= 3.6 && y >= 3.6, who: x <= y ? a : b }; });
      pairs.push({ a, b, tiles, score: tiles.reduce((s, t) => s + t.v, 0) / tiles.length, hard: tiles.filter((t) => t.both).length });
    }
    const nailed = (team, et) => BS.elements.filter((e) => e.team === team && e.element_type === et && e.status === 'a' && A.rel(e) >= 0.85).sort((x, y) => x.now_cost - y.now_cost)[0];
    // v3.12: pairs are for one position (GK or DEF): both clubs need a cheap nailed starter there; ties go to the cheaper pair
    const NL = {}; ids.forEach((id) => (NL[id] = nailed(id, ROT.pos)));
    pairs.forEach((p) => (p.cost = NL[p.a] && NL[p.b] ? NL[p.a].now_cost + NL[p.b].now_cost : 1e9));
    pairs.sort((x, y) => (x.cost === 1e9) - (y.cost === 1e9) || x.score - y.score || x.hard - y.hard || x.cost - y.cost);
    // Ticker: every club, easiest run first; owned clubs marked
    const sumD = (team) => gws.reduce((s2, g) => s2 + best(team, g), 0) / gws.length;
    const cell = (team, g) => { const fs = A.fxBy[team + '-' + g] || []; if (!fs.length) return `<td class="tk d5 blank" title="GW${g}: no match">–</td>`;
      return `<td class="tk d${Math.max(1, Math.min(5, Math.round(Math.min(...fs.map((f) => f.diff)))))}${fs.length > 1 ? ' dgw' : ''}" title="GW${g}: ${fs.map((f) => `${T[f.o].name} (${f.home ? 'home' : 'away'}), difficulty ${f.diff.toFixed(1)}`).join(' + ')}">${fs.map((f) => `${T[f.o].short_name}${ha(f.home)}`).join('<br>')}</td>`; };
    const ticker = `<div class="tw tick"><table><thead><tr><th>Club</th>${gws.map((g) => `<th class="n">GW${g}</th>`).join('')}<th class="n">Avg</th></tr></thead><tbody>${ids.slice().sort((x, y) => sumD(x) - sumD(y)).map((id) => `<tr class="${A.club[id] ? 'own' : ''}" data-fanchor="${id}" title="Show the best rotation partners for ${esc(T[id].name)}"><td class="pl"><span class="tkc">${crest(id)}<b>${T[id].short_name}</b>${A.club[id] ? `<small class="pill p-keep">${A.club[id]} owned</small>` : ''}</span></td>${gws.map((g) => cell(id, g)).join('')}<td class="n"><b>${sumD(id).toFixed(1)}</b></td></tr>`).join('')}</tbody></table></div>`;
    const cards = pairs.filter((p) => p.cost < 1e9).slice(0, 12).map((p, i) => {
      const own = [p.a, p.b].filter((id) => A.club[id]);
      const pb = (e) => `<button class="rpb" type="button" data-quick="${e.id}" title="Bring ${esc(e.web_name)} into the planner">${crest(e.team)}<span><b>${esc(e.web_name)}</b><small>${money(e.now_cost)}</small></span></button>`;
      return `<div class="rot${own.length ? ' own' : ''}"><div class="rh"><span class="rn">${i + 1}</span><span class="rt">${crest(p.a)}${crest(p.b)}</span><div class="rx"><b>${esc(T[p.a].short_name)} + ${esc(T[p.b].short_name)}</b><small>${p.hard ? `${p.hard} tough week${p.hard > 1 ? 's' : ''}` : 'No tough weeks'}${own.length ? ` · <span class="acc">you own ${own.map((id) => T[id].short_name).join(' & ')}</span>` : ''}</small></div><span class="rs"><b>${p.score.toFixed(2)}</b><small>avg</small></span></div>
<div class="rtiles" style="--n:${p.tiles.length}">${p.tiles.map((t) => `<div class="rtl d${Math.max(1, Math.min(5, Math.round(t.v)))}" title="GW${t.g}: start the ${T[t.who].short_name} player (difficulty ${t.v === 5 ? 'no match' : t.v.toFixed(1)})"><small>${t.g}</small>${crest(t.who)}<b>${t.v === 5 ? '–' : Math.round(t.v)}</b></div>`).join('')}</div>
<div class="rpl"><span class="rpk">${ROT.pos === 1 ? 'GK' : 'DEF'}</span>${pb(NL[p.a])}${pb(NL[p.b])}<span class="rpt">${money(p.cost)}</span></div></div>`; }).join('') || '<p class="muted">No pairs with a nailed starter at both clubs for this anchor team.</p>';
    // v3.11: Market, Head to head (player comparison) and Accuracy have their own full-width layouts
    if (FIXTAB === 'market') return `<section class="s fx2" id="s-fix">${marketHtml(A)}</section>`;
    if (FIXTAB === 'stats') return `<section class="s fx2" id="s-fix">${playerStatsHtml(A)}</section>`;
    if (FIXTAB === 'h2h') return `<section class="s fx2" id="s-fix">${cmpHtml(A)}</section>`;
    if (FIXTAB === 'acc') return `<section class="s fx2" id="s-fix"><div class="ptl"><h2>Projection accuracy</h2><p class="sub">Past gameweeks replayed with only what was known before each deadline</p></div><div class="card acc" id="acc-card">${accHtml()}</div></section>`;
    return `<section class="s" id="s-fix"><h2>Fixtures</h2><p class="sub">${FIXTAB === 'h2h' ? 'The players you plan to sell next to the players you plan to buy, for the gameweek on screen in the planner.' : FIXTAB === 'ticker' ? 'Easiest runs first · green easy, red hard · tap a club for its rotation partner' : 'Two cheap starters, play whichever has the easier game · lower average is better'}</p>
<div class="rotctl"><div class="seg" ${FIXTAB === 'h2h' ? 'hidden' : ''}><button type="button" class="${ROT.n === 3 ? 'on' : ''}" data-rotn="3">Next 3</button><button type="button" class="${ROT.n === 6 ? 'on' : ''}" data-rotn="6">Next 6</button><button type="button" class="${ROT.n === 10 ? 'on' : ''}" data-rotn="10">Next 10</button></div>
${FIXTAB === 'pairs' ? `<div class="seg" role="group" aria-label="Position">${[[1, 'Goalkeepers'], [2, 'Defenders']].map(([k, l]) => `<button type="button" class="${ROT.pos === k ? 'on' : ''}" data-rotpos="${k}">${l}</button>`).join('')}</div><label class="wcl">Anchor team <select id="rot-anchor" aria-label="Anchor team"><option value="0">Best pairings overall</option>${BS.teams.map((t) => `<option value="${t.id}" ${ROT.anchor === t.id ? 'selected' : ''}>${esc(t.name)}</option>`).join('')}</select></label>
` : ''}</div>
${FIXTAB === 'ticker' ? ticker : FIXTAB === 'h2h' ? h2hHtml() : `<div class="rotgrid">${cards}</div>`}</section>`;
  }
  const shirtMini = (sn) => { const s = JST[sn] || ['#8a97ab', '#8a97ab', null, '#e6ebf2']; return `<svg class="smini" viewBox="0 0 48 42" aria-hidden="true"><path d="M14 3l6 3q4 2 8 0l6-3 12 8-5 9-5-3v22H12V17l-5 3-5-9z" fill="${s[0]}" stroke="rgba(0,0,0,.45)" stroke-width="1"/>${s[2] ? `<path d="M16 8h3v31h-3zM22.5 8h3v31h-3zM29 8h3v31h-3z" fill="${s[2]}"/>` : ''}<path d="M14 3L2 11l5 9 5-3v-7zM34 3l12 8-5 9-5-3v-7z" fill="${s[1]}"/></svg>`; };

  // ================= Strategies =================
  // Safe: leans to popular players (fewer surprises). Balanced: pure projected points.
  // Differential: rewards players your rivals (or most managers) don't own, because only those gain you rank.
  const STRATS = [['safe', 'Safe', 'Popular, reliable picks. Lower risk of falling behind.'], ['balanced', 'Balanced', 'Highest projected points, ownership ignored.'], ['diff', 'Differential', 'Avoids what rivals own. More upside to climb.']];
  function stratValue(kind, base, ownF) {
    if (kind === 'safe') return (e) => base(e) * (1 + 0.25 * ownF(e));
    if (kind === 'diff') return (e) => base(e) * (1 + 0.55 * (1 - ownF(e)) - 0.2);
    return base;
  }
  async function planChip(name) {
    const A = PLAN.A, P = A.P, g0 = PLAN.gw;
    pushUndo(`${({ wildcard: 'Wildcard', freehit: 'Free Hit', bboost: 'Bench Boost', '3xc': 'Triple Captain' })[name] || name}`);
    const big = (c) => c === 'wildcard' || c === 'freehit';
    if (PLAN.chip === name) { if (big(name)) { resetWeek(); PLAN.wc = null; } else PLAN.chip = null; return renderPlanner(); }
    if (big(PLAN.chip)) resetWeek();   // one chip at a time
    if (!big(name)) {
      if (name === '3xc') { const xi = PLAN.line.slice(0, 11).sort((a, c) => P(c.e, g0) - P(a.e, g0)); if (PLAN.cap !== xi[0]) { PLAN.vc = PLAN.cap && PLAN.cap !== xi[0] ? PLAN.cap : xi[1]; PLAN.cap = xi[0]; } }
      PLAN.chip = name; PLAN.sel = null; PLAN.buying = null; PLAN.msg = ''; return renderPlanner();
    }
    resetWeek();
    const lg = myLeagues();
    PLAN.wc = { chip: name, g: g0, opts: null, busy: true, lid: PLAN.wcLid != null ? PLAN.wcLid : (lg[0] ? lg[0].id : 0), locks: PLAN.wcLocks || [], bans: PLAN.wcBans || [], pick: PLAN.wcPick || 'balanced', N: 5000 };
    PLAN.chip = name; PLAN.msg = ''; renderPlanner();
    await wcSolve();
  }
  async function wcSolve() {
    const A = PLAN.A, P = A.P, W = PLAN.wc; if (!W) return; const g0 = W.g;
    W.busy = true; renderPlanner(); await new Promise((r) => setTimeout(r, 30));
    let riv = null;
    if (W.lid) { try { riv = await loadRivals(W.lid); } catch (e) { riv = null; W.rivErr = true; } }
    const lastG = A.GWS[A.GWS.length - 1];
    const weeks = []; for (let g = g0; g < g0 + (W.chip === 'wildcard' ? 5 : 1) && g <= lastG; g++) weeks.push(g);
    const base = (e) => weeks.reduce((a, g) => a + P(e, g), 0);
    const ownF = riv && riv.teams.length ? (e) => riv.eo[e.id] || 0 : (e) => (parseFloat(e.selected_by_percent) || 0) / 100;
    const own = {}; PLAN.enter.forEach((x) => (own[x.e.id] = x.sell));
    // Cost every player at today's price, kept players included: on the FPL site a kept player you remove and re-add is charged today's price, not his selling price.
    const cost = (e) => e.now_cost;
    const budget = PLAN.enter.reduce((a, x) => a + x.sell, 0) + PLAN.bank0;
    const opts = STRATS.map(([k, lab, d]) => { const b = buildSquad(stratValue(k, base, ownF), cost, budget, { locks: W.locks, bans: W.bans }); return b ? { k, lab, d, b, ids: b.sq.map((x) => x.e.id) } : null; }).filter(Boolean);
    if (!opts.length) { W.busy = false; PLAN.msg = 'Could not build a squad within budget with those locks.'; return renderPlanner(); }
    const rivSets = riv ? riv.teams.map((t) => t.ids) : [];
    const N = W.N || 5000; W.prog = 0;
    const sim = await simulate([...opts.map((o) => o.ids), ...rivSets], weeks, N, (f) => { W.prog = f; const pe = R.getElementById('wc-prog'); if (pe) pe.style.width = Math.round(f * 100) + '%'; const pt = R.getElementById('wc-progt'); if (pt) pt.textContent = Math.round(f * 100) + '%'; });
    W.ran = N;
    opts.forEach((o, i) => {
      const s = sim[i];
      o.mean = Array.from(s).reduce((a, x) => a + x, 0) / s.length; o.p10 = pctl(s, 0.1); o.p90 = pctl(s, 0.9);
      o.ownAvg = o.ids.reduce((a, id) => a + ownF(A.E[id]), 0) / 15;
      if (rivSets.length) {
        let beatMed = 0, top = 0;
        for (let r = 0; r < s.length; r++) { const rv = rivSets.map((_, j) => sim[opts.length + j][r]).sort((x, y) => x - y); if (s[r] > rv[Math.floor(rv.length / 2)]) beatMed++; if (s[r] > rv[rv.length - 1]) top++; }
        o.beat = beatMed / s.length; o.top = top / s.length;
        o.overlap = riv.teams.reduce((a, t) => a + o.ids.filter((id) => t.ids.includes(id)).length / 15, 0) / riv.teams.length;
      }
    });
    W.opts = opts; W.riv = riv; W.weeks = weeks; W.busy = false;
    applyWc(W.pick && opts.find((o) => o.k === W.pick) ? W.pick : 'balanced');
  }
  function applyWc(k) {
    const A = PLAN.A, P = A.P, W = PLAN.wc; const o = W && W.opts && W.opts.find((x) => x.k === k); if (!o) return;
    const g0 = W.g; W.pick = k; PLAN.wcPick = k;
    const own = {}; PLAN.enter.forEach((x) => (own[x.e.id] = x.sell));
    const mk = (e) => ({ e, sell: e.now_cost, keep: own[e.id] });
    const xi = o.b.sq.filter((x) => x.role === 'xi').map((x) => mk(x.e)).sort((a, c) => a.e.element_type - c.e.element_type || P(c.e, g0) - P(a.e, g0));
    const bench = o.b.sq.filter((x) => x.role === 'bench').map((x) => mk(x.e));
    const bgk = bench.filter((x) => x.e.element_type === 1), bout = bench.filter((x) => x.e.element_type !== 1).sort((a, c) => P(c.e, g0) - P(a.e, g0));
    PLAN.line = [...xi, ...bgk, ...bout];
    const caps = xi.slice().sort((a, c) => P(c.e, g0) - P(a.e, g0)); PLAN.cap = caps[0]; PLAN.vc = caps[1];
    PLAN.chipBank = PLAN.enter.reduce((a, x) => a + x.sell, 0) + PLAN.bank0 - o.b.spent;
    const newIds = new Set(PLAN.line.map((x) => x.e.id)), oldIds = new Set(PLAN.enter.map((x) => x.e.id));
    PLAN.chipOut = PLAN.enter.filter((x) => !newIds.has(x.e.id)).map((x) => x.e); PLAN.chipIn = PLAN.line.filter((x) => !oldIds.has(x.e.id)).map((x) => x.e);
    PLAN.swaps = []; PLAN.chipLine = PLAN.line.map((x) => x.e.id); PLAN.chip = W.chip; PLAN.sel = null; PLAN.buying = null;
    renderPlanner();
  }
  function wcPanel(nm) {
    const W = PLAN.wc, A = PLAN.A; if (!W || W.g !== PLAN.gw || PLAN.chip !== W.chip) return '';
    const lg = myLeagues();
    const pc = (x) => (x * 100).toFixed(0) + '%';
    const head = `<div class="wch"><b>${W.chip === 'wildcard' ? 'Wildcard' : 'Free Hit'} builder · GW${W.g}</b>
<label class="wcl">Compare with <select id="wc-league" aria-label="Rivals to compare with"><option value="0" ${!W.lid ? 'selected' : ''}>All managers (overall ownership)</option>${lg.map((l) => `<option value="${l.id}" ${+W.lid === l.id ? 'selected' : ''}>${esc(l.name)}</option>`).join('')}</select></label></div>`;
    if (W.busy) return `<div class="wcbox">${head}<p class="muted"><span class="spin"></span> Searching squads and simulating ${(W.N || 5000).toLocaleString()} possible outcomes${W.lid ? ' against your rivals' : ''}… <span id="wc-progt">0%</span></p><div class="prog"><span id="wc-prog"></span></div></div>`;
    if (!W.opts) return '';
    const riv = W.riv;
    const best = (f) => W.opts.reduce((a, o) => (f(o) > f(a) ? o : a), W.opts[0]).k;
    const bMean = best((o) => o.mean), bUp = best((o) => o.p90), bBeat = riv ? best((o) => o.beat) : null;
    const cards = W.opts.map((o) => `<button class="wco ${W.pick === o.k ? 'on' : ''}" type="button" data-wcopt="${o.k}"><div class="wct"><b>${o.lab}</b>${W.pick === o.k ? '<span class="pill p-live">Applied</span>' : ''}</div><small class="muted">${o.d}</small>
<div class="wcs"><span>Expected</span><b class="${o.k === bMean ? 'up' : ''}">${o.mean.toFixed(0)}</b></div>
<div class="wcs"><span>Range (10–90%)</span><b>${o.p10.toFixed(0)}–<span class="${o.k === bUp ? 'up' : ''}">${o.p90.toFixed(0)}</span></b></div>
${riv ? `<div class="wcs"><span>Beat league median</span><b class="${o.k === bBeat ? 'up' : ''}">${pc(o.beat)}</b></div><div class="wcs"><span>Top all ${riv.teams.length} rivals</span><b>${pc(o.top)}</b></div><div class="wcs"><span>Same players as rivals</span><b>${pc(o.overlap)}</b></div>` : `<div class="wcs"><span>Avg ownership</span><b>${pc(o.ownAvg)}</b></div>`}
</button>`).join('');
    const rec = riv ? W.opts.reduce((a, o) => (o.beat > a.beat ? o : a), W.opts[0]) : null;
    const lockBan = W.locks.length || W.bans.length ? `<p class="note" style="margin:6px 0 0">${W.locks.length ? `Locked: ${W.locks.map((id) => esc(A.E[id].web_name)).join(', ')}. ` : ''}${W.bans.length ? `Excluded: ${W.bans.map((id) => esc(A.E[id].web_name)).join(', ')}. ` : ''}<button class="lnk" id="wc-clearlb" type="button">Clear</button></p>` : '';
    return `<div class="wcbox">${head}
<p class="note" style="margin:0 0 8px">${W.weeks.length} gameweek${W.weeks.length > 1 ? 's' : ''} simulated ${(W.ran || 5000).toLocaleString()} times with FPL-style scoring (goals, assists, clean sheets, bonus).${riv ? ` Compared with ${riv.teams.length} rivals in ${esc(riv.name)} (their current squads).` : ' Pick a mini-league to see your chances against your rivals.'}${rec ? ` <b>Best chance to beat your rivals: ${rec.lab}.</b>` : ''}</p>
<div class="wcopts">${W.opts.length ? cards : ''}</div>
<p class="note" style="margin:8px 0 0">Make it yours: press 🔒 on a player to keep him, or ⊘ to exclude him, then rebuild.</p>${lockBan}
<div class="btnrow2" style="margin-top:8px"><button class="try" id="wc-rebuild" type="button">Rebuild with my locks</button>${(W.ran || 0) < 20000 ? '<button class="try" id="wc-deep" type="button">Deep mode: 20,000 runs</button>' : '<span class="pill p-live">Deep mode</span>'}</div></div>`;
  }
  // ======================= 9. captain picker that knows who else is captaining =======================
  // Overall: ownership plus an estimated captain share (popular, high-projection players get most armbands).
  // League: from your rivals' latest teams (each rival counts 1 if he owns him, 2 if captain).
  function capHtml(g0) {
    const A = PLAN.A, T = A.T, P = (e) => A.P(e, g0);
    const xi = PLAN.line.filter((x) => inXI(x)).map((x) => x.e);
    const cands = xi.filter((e) => e.element_type > 1).sort((a, b) => P(b) - P(a)).slice(0, 6);
    if (!cands.length) return '<p class="muted">No starting XI for this week.</p>';
    const pool = BS.elements.filter((e) => +e.selected_by_percent >= 5).map((e) => ({ e, w: Math.pow(Math.max(0.1, P(e)), 3) * (+e.selected_by_percent) }));
    const W = pool.reduce((a, x) => a + x.w, 0) || 1; const capS = {}; pool.forEach((x) => (capS[x.e.id] = x.w / W));
    const D = LG.data && LG.data.teams && LG.data.teams.length ? LG.data : null; const lgEO = {};
    if (D) D.teams.forEach((tm) => tm.picks.forEach((q) => (lgEO[q.element] = (lgEO[q.element] || 0) + (q.multiplier || 0) / D.teams.length)));
    const rows = cands.map((e) => { const own = (+e.selected_by_percent || 0) / 100, eoO = own + (capS[e.id] || 0) * 0.9, eoL = D ? lgEO[e.id] || 0 : null; const eo = eoL != null ? eoL : eoO; return { e, p: P(e), eoO, eoL, eo, gain: P(e) * (2 - eo) }; });
    const best = rows.reduce((a, r) => (r.p > a.p ? r : a), rows[0]);
    const near = rows.filter((r) => r.p >= best.p - 1);
    const shield = near.reduce((a, r) => (r.eo > a.eo ? r : a), near[0]);
    const att = rows.filter((r) => r.p >= best.p * 0.85).reduce((a, r) => (r.gain > a.gain ? r : a), best);
    const me = D ? null : null; let pos = '';
    if (LG.data && LASTA) { const lr = allLeagues(LASTA).find((l) => l.key === LG.data.key); if (lr && lr.rank) pos = lr.rank <= 2 ? 'ahead' : lr.last && lr.rank > lr.last ? 'behind' : lr.rank > 3 ? 'behind' : ''; }
    const pick = pos === 'ahead' ? shield : pos === 'behind' ? att : best;
    const why = pick === best && pick === shield ? 'Highest projection and the popular choice: the safe and the best pick at once.' : pos === 'ahead' ? `You're near the top of ${esc(LG.data.name)}: copy the popular captain so a rival's haul can't overtake you.` : pos === 'behind' ? `You need to catch up in ${esc(LG.data.name)}: a less-captained pick gains you ground every time he scores.` : 'Highest projected points this week.';
    const cur = PLAN.cap && PLAN.cap.e;
    const card = (r, tag) => `<div class="capc ${r === pick ? 'rec' : ''}"><div class="ck">${kitImg(T[r.e.team].short_name, r.e.element_type === 1, 66, 'capk')}</div><div class="cm"><b>${esc(r.e.web_name)}${tag ? ` <span class="ctag">${tag}</span>` : ''}</b><small>${T[r.e.team].short_name} · ${fxCell(A, r.e.team, g0)}</small></div>
<div class="cs"><span><b>${f1(r.p)}</b><small>proj</small></span><span><b>${Math.round(r.eoO * 100)}%</b><small>EO all</small></span>${r.eoL != null ? `<span><b>${Math.round(r.eoL * 100)}%</b><small>EO league</small></span>` : ''}<span><b class="${r.gain >= best.p ? 'up' : ''}">${f1(r.gain)}</b><small>vs field</small></span></div>
${cur && cur.id === r.e.id ? '<span class="pill p-core">Captain</span>' : `<button class="try" type="button" data-cap="c:${r.e.id}">Captain</button>`}</div>`;
    const tagOf = (r) => [r === best ? 'Most points' : '', r === shield && r !== best ? 'Safe' : '', r === att && r !== best ? 'Differential' : ''].filter(Boolean).join(' · ');
    return `<div class="caprec"><small class="eyebrow">Recommended for GW${g0}</small><b>${esc(pick.e.web_name)}</b><span>${why}</span></div>
<p class="note" style="margin:6px 0 8px">EO = effective ownership: how many points the field gets when he scores (owners count once, captains twice). "vs field" = what he's worth to you as captain after removing what everyone else also gets.${D ? '' : ' Open Live › Mini-league once to add your league\'s numbers.'}</p>
<div class="stack">${rows.map((r) => card(r, tagOf(r))).join('')}</div>`;
  }
  function buyList() {
    const A = PLAN.A, T = A.T; const cur = byId(PLAN.buying); if (!cur) return '';
    const slot = (PLAN.swaps.find((s) => s.i === cur) || { o: cur }).o;
    const budget = planBank() + (cur === slot ? cur.sell : cur.e.now_cost);
    const clubs = planClubs(); clubs[cur.e.team]--;
    const q = PLAN.q.trim().toLowerCase();
    const have = new Set(PLAN.line.map((x) => x.e.id));
    const list = BS.elements.filter((c) => c.element_type === cur.e.element_type && !have.has(c.id) && c.status !== 'u' && (!q || (c.web_name + ' ' + c.first_name + ' ' + c.second_name + ' ' + T[c.team].name).toLowerCase().includes(q)))
      .map((c) => ({ c, v: A.S5(c), ok: c.now_cost <= budget && (clubs[c.team] || 0) < 3 }))
      .sort((a, b) => (b.ok - a.ok) || b.v - a.v).slice(0, q ? 30 : 15);
    const mine = A.S5(cur.e);
    return list.map(({ c, v, ok }) => { const why = c.now_cost > budget ? `needs ${money(c.now_cost - budget)} more` : (clubs[c.team] || 0) >= 3 ? `3 ${T[c.team].short_name} players already` : '';
      return `<button class="cand ${ok ? '' : 'no'}" type="button" data-buyin="${c.id}"><span class="cn"><b class="kn">${pkit(c)}${esc(c.web_name)}</b> <small>${T[c.team].short_name} · ${money(c.now_cost)} · form ${c.form} · ${c.selected_by_percent}%</small>${why ? `<small class="dn"> · ${why}</small>` : ''}</span><span class="cv"><b>${f1(v)}</b><small class="${v - mine > 0 ? 'up' : 'dn'}">${v - mine > 0 ? '+' : ''}${f1(v - mine)}</small></span></button>`; }).join('') || '<p class="muted">No player matches that search.</p>';
  }
  // v3.44 points slider: from your team as it is, to the most points the model can find for this gameweek.
  // Step 0 = your current line-up, step 1 = best 11 + captain, then one extra transfer per step,
  // each the single swap that adds the most projected points (budget and 3-per-club rules kept).
  function slidePath() {
    const A = PLAN.A, P = A.P, g = PLAN.gw, H = PLAN.slH || 1, key = g + '|' + H + '|' + PLAN.enter.map((x) => x.e.id).join(',') + '|' + PLAN.bank0;
    if (PLAN.slide && PLAN.slide.key === key) return PLAN.slide;
    const gs = A.GWS.filter((x) => x >= g).slice(0, H), W = (e) => gs.reduce((a, x, i) => a + P(e, x) * Math.pow(0.9, i), 0);
    const cur = PLAN.enter, curIds = new Set(cur.map((x) => x.e.id)), sellOf = {}; cur.forEach((x) => (sellOf[x.e.id] = x.sell != null ? x.sell : x.e.now_cost));
    const budget = PLAN.bank0 + cur.reduce((a, x) => a + sellOf[x.e.id], 0);
    const pool = new Map(cur.map((x) => [x.e.id, x.e]));
    [1, 2, 3, 4].forEach((t) => BS.elements.filter((e) => e.element_type === t && e.status !== 'u' && e.status !== 'n').sort((a, b) => W(b) - W(a)).slice(0, t === 1 ? 10 : 32).forEach((e) => pool.set(e.id, e)));
    // exact best squad, starting 11 and captain with at most n transfers (integer programming)
    const solve = (n) => { const m = { optimize: 'v', opType: 'max', constraints: { cost: { max: budget }, sq1: { equal: 2 }, sq2: { equal: 5 }, sq3: { equal: 5 }, sq4: { equal: 3 }, st: { equal: 11 }, st1: { equal: 1 }, st2: { min: 3, max: 5 }, st3: { min: 2, max: 5 }, st4: { min: 1, max: 3 }, cap: { equal: 1 }, nt: { max: n } }, variables: {}, ints: {} };
      pool.forEach((e, id) => { const v = W(e), t = e.element_type; m.constraints['t' + e.team] = { max: 3 }; m.constraints['u' + id] = { max: 1 }; m.constraints['l' + id] = { max: 0 }; m.constraints['k' + id] = { max: 0 };
        m.variables['x' + id] = { v: 0.03 * v, cost: curIds.has(id) ? sellOf[id] : e.now_cost, ['sq' + t]: 1, ['t' + e.team]: 1, ['u' + id]: 1, ['l' + id]: -1, nt: curIds.has(id) ? 0 : 1 };
        m.variables['s' + id] = { v, st: 1, ['st' + t]: 1, ['l' + id]: 1, ['k' + id]: -1 };
        m.variables['c' + id] = { v, cap: 1, ['k' + id]: 1 };
        m.ints['x' + id] = 1; m.ints['s' + id] = 1; m.ints['c' + id] = 1; });
      const r = LPS().Solve(m); if (!r.feasible) return null; const ids = [...pool.keys()].filter((id) => r['x' + id] > 0.5), xi = ids.filter((id) => r['s' + id] > 0.5), cap = ids.find((id) => r['c' + id] > 0.5);
      return { ids, xi, cap, pts: xi.reduce((a, id) => a + W(A.E[id]), 0) + W(A.E[cap]), n: ids.filter((id) => !curIds.has(id)).length }; };
    const baseV = H === 1 ? PLAN.base : (() => { const xi = cur.slice(0, 11); const c = xi.reduce((b, x) => (W(x.e) > W(b.e) ? x : b), xi[0]); return xi.reduce((a, x) => a + W(x.e), 0) + W(c.e); })();
    const steps = [{ pts: baseV, sol: null, nT: 0 }];
    let last = -1;
    for (let n = 0; n <= 15; n++) { const s = solve(n); if (!s) break; if (s.n < n && n > 0) break; if (s.pts < last + 0.1 && n > 0) break; steps.push({ pts: s.pts, sol: s, nT: s.n }); last = s.pts; }
    // chips (one gameweek only): Triple Captain and Bench Boost on top of the best squad, when you still have them
    if (H === 1) { const top = steps[steps.length - 1].sol, has = (c) => A.chipPlans.some((x) => x.c.name === c && !x.locked && x.from <= g && x.to >= g);
      if (top && has('3xc')) steps.push({ pts: top.pts + P(A.E[top.cap], g), sol: top, nT: top.n, chip: '3xc' });
      if (top && has('bboost')) { const bench = top.ids.filter((id) => !top.xi.includes(id)).reduce((a, id) => a + P(A.E[id], g), 0); steps.push({ pts: steps[steps.length - 1].pts + bench, sol: top, nT: top.n, chip: steps[steps.length - 1].chip === '3xc' ? 'both' : 'bboost' }); } }
    const free = solve(15); const has2 = (c) => A.chipPlans.some((x) => x.c.name === c && !x.locked && x.from <= g && x.to >= g);
    const alt = free ? { pts: free.pts, wc: has2('wildcard'), fh: H === 1 && has2('freehit') } : null;
    PLAN.slide = { key, steps, H, alt }; return PLAN.slide;
  }
  function slideApply(k) {
    const path = slidePath(), st = path.steps[k]; pushUndo('Points slider'); resetWeek();
    const A = PLAN.A, P = A.P, g0 = PLAN.gw;
    if (st && st.sol) { const want = new Set(st.sol.ids), outs = PLAN.line.filter((x) => !want.has(x.e.id)), ins = st.sol.ids.filter((id) => !PLAN.line.some((x) => x.e.id === id)).map((id) => A.E[id]);
      outs.forEach((o) => { const i = ins.findIndex((e) => e.element_type === o.e.element_type); if (i < 0) return; const e = ins.splice(i, 1)[0]; const ix = PLAN.line.indexOf(o); const x = { e, sell: e.now_cost }; PLAN.swaps.push({ o, i: x }); PLAN.line[ix] = x; });
      const xi = PLAN.line.filter((x) => st.sol.xi.includes(x.e.id)).sort((a, c) => a.e.element_type - c.e.element_type || P(c.e, g0) - P(a.e, g0)), bench = PLAN.line.filter((x) => !st.sol.xi.includes(x.e.id));
      const bgk = bench.filter((x) => x.e.element_type === 1), bout = bench.filter((x) => x.e.element_type !== 1).sort((a, c) => P(c.e, g0) - P(a.e, g0));
      PLAN.line = [...xi, ...bgk, ...bout]; PLAN.cap = PLAN.line.find((x) => x.e.id === st.sol.cap) || xi[0]; PLAN.vc = xi.filter((x) => x !== PLAN.cap).sort((a, c) => P(c.e, g0) - P(a.e, g0))[0];
      if (st.chip) PLAN.chip = st.chip === 'both' ? 'bboost' : st.chip; }
    PLAN.sel = null; PLAN.buying = null; PLAN.msg = ''; PLAN.slideK = k; renderPlanner(); PLAN.slideSig = planSig(); paintSlide();
  }
  let SLDRAG = false;
  function paintSlide() {
    const box = R.getElementById('pl-slide'); if (!box) return;
    if (!PLAN || !PLAN.A || PLAN.gw < PLAN.A.startGw || PLAN.chip === 'wildcard' || PLAN.chip === 'freehit') { box.innerHTML = ''; return; }
    const path = slidePath(), st = path.steps, max = st.length - 1;
    const k = PLAN.slideSig && PLAN.slideSig === planSig() ? Math.min(PLAN.slideK || 0, max) : -1;
    const lab = (i) => { const s = st[i], nT = s.nT || 0, hit = Math.max(0, nT - PLAN.ft0) * 4; return { pts: s.pts, nT, hit, net: s.pts - hit, what: i === 0 ? 'Your team as it is' : (nT ? `${nT} transfer${nT > 1 ? 's' : ''}${hit ? ` · −${hit} hit` : ' · free'}` : 'Best 11 and captain, no transfers') + (s.chip ? ` · ${s.chip === '3xc' ? '+ Triple Captain' : s.chip === 'bboost' ? '+ Bench Boost' : '+ Triple Captain + Bench Boost'}` : '') }; };
    const A = PLAN.A, P = A.P, cp = (n) => A.chipPlans.find((x) => x.c.name === n);
    const chipNote = (s) => { if (!s || !s.chip) return ''; const out = []; const bench = s.sol.ids.filter((id) => !s.sol.xi.includes(id)); 
      if (s.chip === 'bboost' || s.chip === 'both') { const now = bench.reduce((a, id) => a + P(A.E[id], PLAN.gw), 0), c = cp('bboost'); out.push(`Bench Boost +${f1(now)} now${c && c.best && c.best.g !== PLAN.gw ? ` (its best week: GW${c.best.g}, +${f1(c.best.score)})` : ''}`); }
      if (s.chip === '3xc' || s.chip === 'both') { const now = P(A.E[s.sol.cap], PLAN.gw), c = cp('3xc'); out.push(`Triple Captain +${f1(now)} now${c && c.best && c.best.g !== PLAN.gw ? ` (its best week: GW${c.best.g}, +${f1(c.best.score)})` : ''}`); }
      return out.join(' · '); };
    const flagNote = (s) => { if (!s || !s.sol) return ''; const ids = s.chip === 'bboost' || s.chip === 'both' ? s.sol.ids : s.sol.xi; const fl = ids.map((id) => A.E[id]).filter((e) => e.status !== 'a'); return fl.length ? `⚠ Flagged: ${fl.map((e) => e.web_name).join(', ')}` : ''; };
    const L = lab(Math.max(0, k)); let bn = 0; st.forEach((s, i) => { if (lab(i).net > lab(bn).net + 0.05) bn = i; }); const BN = lab(bn);
    if (SLDRAG) return;
    box.innerHTML = `<div class="psl"><div class="psl-h"><b>Points slider · ${path.H === 1 ? 'GW' + PLAN.gw : 'next ' + path.H + ' GWs'}</b><span class="psl-hz"><button type="button" class="${path.H === 1 ? 'on' : ''}" data-slh="1">1 GW</button><button type="button" class="${path.H === 5 ? 'on' : ''}" data-slh="5">5 GWs</button></span><small>Slide right to add the transfers that raise projected points most · best after hits: <button type="button" class="psl-best" data-slk="${bn}">${f1(BN.net)} pts (${bn === 0 ? 'as it is' : BN.what})</button></small></div>
<div class="psl-row"><span class="psl-end"><small>Now</small><b>${f1(st[0].pts)}</b></span><input id="pl-sl" type="range" min="0" max="${max}" step="1" value="${Math.max(0, k)}" aria-label="Projected points slider"><span class="psl-end"><small>Max</small><b>${f1(st[max].pts)}</b></span></div>
${(() => { const s = st[Math.max(0, k)], parts = [chipNote(s), flagNote(s)].filter(Boolean); return parts.length && k >= 0 ? `<div class="psl-note">${esc(parts.join(' · '))}</div>` : ''; })()}
${(() => { const alt = path.alt, maxS = st.filter((s) => !s.chip).pop() || st[0], hit = Math.max(0, (maxS.nT || 0) - PLAN.ft0) * 4; if (!alt || (!alt.wc && !alt.fh) || hit < 12) return '';
  return `<div class="psl-alt"><b>${hit} pts of hits?</b> <span>${alt.wc ? `A <b>Wildcard</b> gives ${f1(alt.pts)} ${path.H === 1 ? 'this gameweek' : 'over ' + path.H + ' GWs'} with <b>no hits</b>, and keeps your other chips` : `A <b>Free Hit</b> gives ${f1(alt.pts)} this gameweek with no hits`} (the transfers path: ${f1(maxS.pts)} − ${hit} = ${f1(maxS.pts - hit)}).</span><button type="button" class="psl-wc" data-act="chip:${alt.wc ? 'wildcard' : 'freehit'}">Open ${alt.wc ? 'Wildcard' : 'Free Hit'} builder</button></div>`; })()}
<div class="psl-out" id="pl-slo">${k < 0 ? `<span>Your own plan · slide to replace it</span>` : `<b>${f1(L.pts)} pts</b><span>${L.what}${L.hit ? ` · net ${f1(L.net)}` : ''}</span>`}${(() => { try { const A = PLAN.A, xi = PLAN.line.slice(0, 11).map((x) => x.e.id); const r = A.MODEL4.simulate(PLAN.chip === 'bboost' ? PLAN.line.map((x) => x.e.id) : xi, PLAN.cap && PLAN.cap.e.id, PLAN.gw, { tc: PLAN.chip === '3xc' }); return `<span class="psl-mc" title="Monte Carlo: this team's gameweek played 2,500 times. 8 weeks in 10 land in this range; 1 week in 10 beats ${Math.round(r.p90)}.">likely ${Math.round(r.p10)}–${Math.round(r.p90)} · ceiling ${Math.round(r.p90)}</span>`; } catch (e) { return ''; } })()}</div></div>`;
  }
  out.addEventListener('input', (ev) => { if (ev.target.id !== 'pl-sl') return; SLDRAG = true; const k = +ev.target.value; const st = slidePath().steps[k], hit = Math.max(0, (st.nT || 0) - PLAN.ft0) * 4; const o = R.getElementById('pl-slo'); if (o) o.innerHTML = `<b>${f1(st.pts)} pts</b><span>${k === 0 ? 'Your team as it is' : (st.nT ? st.nT + ' transfer' + (st.nT > 1 ? 's' : '') + (hit ? ' · −' + hit + ' hit · net ' + f1(st.pts - hit) : ' · free') : 'No transfers')}${st.chip ? ' · chip' : ''}</span>`; clearTimeout(PLAN.slT); PLAN.slT = setTimeout(() => { slideApply(k); }, 80); });
  out.addEventListener('click', (ev) => { const h = ev.target.closest && ev.target.closest('[data-slh]'); if (h) { PLAN.slH = +h.dataset.slh; PLAN.slideSig = null; paintSlide(); return; } const b = ev.target.closest && ev.target.closest('[data-slk]'); if (b) slideApply(+b.dataset.slk); });
  out.addEventListener('change', (ev) => { if (ev.target.id !== 'pl-sl') return; SLDRAG = false; slideApply(+ev.target.value); });
  out.addEventListener('pointerup', () => { if (SLDRAG) { SLDRAG = false; paintSlide(); } });
  function planBest() {
    const A = PLAN.A, P = A.P, g0 = PLAN.gw; pushUndo('Best 11 players'); const b = A.bestXIof(PLAN.line, g0);
    const xi = b.xi.slice().sort((a, c) => a.e.element_type - c.e.element_type || P(c.e, g0) - P(a.e, g0));
    const bgk = b.bench.filter((x) => x.e.element_type === 1), bout = b.bench.filter((x) => x.e.element_type !== 1).sort((a, c) => P(c.e, g0) - P(a.e, g0));
    PLAN.line = [...xi, ...bgk, ...bout];
    const caps = xi.slice().sort((a, c) => P(c.e, g0) - P(a.e, g0)); PLAN.cap = caps[0]; PLAN.vc = caps[1];
    PLAN.sel = null; PLAN.buying = null; PLAN.msg = ''; renderPlanner();
  }
  // "All players" tab: every player outside your squad, filtered and sorted
  // Weeks strip: transfers, hits and chips planned for every gameweek
  function planTimeline() {
    const A = PLAN.A; const o = origLine(); let st = { list: o.list, bank: A.bank, cap: o.cap, vc: o.vc }, ft = A.ft; const out = []; const lastG = A.GWS[A.GWS.length - 1];
    for (let w = A.startGw; w <= lastG; w++) {
      const wk = PLAN.weeks[w];
      if (!wk) { out.push({ w, nT: 0, hit: 0, ft, bank: st.bank }); ft = Math.min(5, ft + 1); continue; }
      const r = applyWeek(st, wk); const free = wk.chip === 'wildcard' || wk.chip === 'freehit';
      out.push({ w, nT: r.nT, hit: free ? 0 : Math.max(0, r.nT - ft) * 4, ft, chip: wk.chip, bank: r.bank });
      if (wk.chip !== 'freehit') st = { list: r.list, bank: r.bank, cap: r.cap, vc: r.vc };
      ft = ftNext(ft, r.nT, wk.chip);
    }
    return out;
  }
  // Compact status strip: the detail line moves into the hover text
  function tidyKpis(box) { box.querySelectorAll('.kpis.six .kpi').forEach((k) => { const sp = k.querySelector(':scope > span'); if (sp) k.title = sp.textContent.trim(); }); }
  const CHEV = (l) => `<svg viewBox="0 0 24 24" width="18" height="18" aria-hidden="true"><path d="${l ? 'M15 5l-7 7 7 7' : 'M9 5l7 7-7 7'}" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round"/></svg>`;
  function plannerNav() {
    const A = PLAN.A, g = PLAN.gw, lastG = A.GWS[A.GWS.length - 1], first = A.entry.started_event || 1;
    const tl = planTimeline(); const CH = { wildcard: 'WC', freehit: 'FH', bboost: 'BB', '3xc': 'TC' };
    const hitSum = tl.reduce((a, x) => a + x.hit, 0), nSum = tl.reduce((a, x) => a + x.nT, 0);
    return `<div class="gwnav"><button class="gwb" id="gw-prev" type="button" aria-label="Previous gameweek" ${g <= first ? 'disabled' : ''}>${CHEV(1)}</button><div class="gwt"><b>Gameweek ${g}</b><small>${g < A.startGw ? ((BS.events.find((x) => x.id === g) || {}).finished ? 'Finished · your real points' : '<span class="gwlive"></span>Live · points add up as matches are played') : g === A.startGw ? 'Next deadline · planning' : 'Future week · planning'}</small></div><button class="gwb" id="gw-next" type="button" aria-label="Next gameweek" ${g >= lastG ? 'disabled' : ''}>${CHEV(0)}</button>${nSum ? `<small class="gwsum">${nSum} transfer${nSum === 1 ? '' : 's'} planned${hitSum ? ` · −${hitSum} hits` : ''}</small>` : ''}</div>`;
  }
  // Finished gameweek: the team that played and what every player scored
  const HISTC = {};
  async function HIST(g) {
    const id = (PLAN && PLAN.A ? PLAN.A.id : CURID); const k = id + ':' + g;
    if (HISTC[k]) return HISTC[k];
    const [pk, live] = await Promise.all([J(`/api/entry/${id}/event/${g}/picks/`).catch(() => null), LIVE(g)]);
    const d = { pk, live }; if (pk && live && (BS.events.find((x) => x.id === g) || {}).finished) HISTC[k] = d; return d;
  }
  function histHtml(A, g, d) {
    if (!d || !d.pk || !d.live) return '<p class="muted">No data for this gameweek. The team may not have played it.</p>';
    const T = A.T, h = (A.hist.current || []).find((x) => x.event === g) || {}; const avg = (BS.events.find((e) => e.id === g) || {}).average_entry_score || 0;
    // v3.70: live bonus: top 3 BPS in each match not yet confirmed get 3/2/1 (FPL adds it about an hour after full time)
    const PB = {}; (FX || []).filter((f) => f.event === g && f.started && !f.finished).forEach((f) => { const ps = BS.elements.filter((e) => e.team === f.team_h || e.team === f.team_a).map((e) => ({ id: e.id, s: d.live[e.id] || {} })).filter((x) => (x.s.minutes || 0) > 0).map((x) => ({ id: x.id, b: x.s.bps || 0, cb: x.s.bonus || 0 })).sort((a, b) => b.b - a.b);
      if (ps.some((x) => x.cb)) return; ps.forEach((x) => { const rk = ps.filter((y) => y.b > x.b).length + 1; if (rk <= 3) PB[x.id] = 4 - rk; }); });
    const rows = d.pk.picks.map((x) => ({ x, e: A.E[x.element], st: d.live[x.element] || {} })).filter((r) => r.e).map((r) => { const pb = r.st.bonus ? 0 : PB[r.e.id] || 0; const unconf = (FX || []).some((f) => f.event === g && f.started && !f.finished && (f.team_h === r.e.team || f.team_a === r.e.team)); return Object.assign(r, { pb, lb: pb || (unconf ? r.st.bonus || 0 : 0), pts: (r.st.total_points || 0) + pb }); });
    const nm = (e) => `<a class="pn" href="#" data-pid="${e.id}">${esc(e.web_name)}</a>`;
    // v3.69: each player's fixture state this gameweek (not started / live / done), like the official app
    const gfx = (FX || []).filter((f) => f.event === g); const fxOf = (tid) => gfx.filter((f) => f.team_h === tid || f.team_a === tid);
    const stOf = (tid) => { const fs = fxOf(tid); if (!fs.length) return 'blank'; if (fs.some((f) => f.started && !(f.finished || f.finished_provisional))) return 'live'; if (fs.every((f) => !f.started)) return 'ns'; return fs.some((f) => !f.started) ? 'part' : 'done'; };
    const nextFx = (tid) => { const f = fxOf(tid).find((x) => !x.started); if (!f) return ''; const home = f.team_h === tid, o = T[home ? f.team_a : f.team_h]; return `${o ? o.short_name : ''} (${home ? 'H' : 'A'})${f.kickoff_time ? ' ' + new Date(f.kickoff_time).toLocaleString(undefined, { weekday: 'short', hour: '2-digit', minute: '2-digit' }) : ''}`; };
    const card = (r) => { const cnt = r.pts * (r.x.multiplier || 1); const s = r.st; const ev = [s.goals_scored ? s.goals_scored + 'G' : '', s.assists ? s.assists + 'A' : '', s.clean_sheets && r.e.element_type < 4 ? 'CS' : '', s.bonus ? '+' + s.bonus + 'b' : ''].filter(Boolean).join(' ');
      const fs = stOf(r.e.team), ns = fs === 'ns' || (fs === 'blank'), tier = ns ? 'ns' : cnt >= 10 ? 'hi' : cnt >= 4 ? 'ok' : cnt >= 2 ? 'mid' : 'lo';
      const nx = ns && fs !== 'blank' ? nextFx(r.e.team).split(' ') : [];
      const val = ns ? (fs === 'blank' ? '<b>–</b>' : `<b class="nsfx">${esc(nx.slice(0, 2).join(' '))}</b>`) : `<b>${cnt}</b>${r.lb ? `<i class="bpb" title="Live bonus: ${r.lb} provisional bonus point${r.lb > 1 ? 's' : ''} from the BPS ranking (counted in the total, confirmed by FPL after the match)">+${r.lb}</i>` : ''}`;
      const sub = fs === 'blank' ? 'No match' : ns ? esc(nx.slice(2).join(' ')) : `${fs === 'live' ? '<i class="ldot"></i>' : ''}${s.minutes || 0}′${ev ? ' · ' + ev : ''}`;
      return `<div class="chip pc ro pt-${tier}${fs === 'live' ? ' plive' : ''}" data-prof="${r.e.id}" role="button" tabindex="0">${jersey(A, r.e, { role: r.x.is_captain ? (r.x.multiplier === 3 ? '3×' : 'C') : r.x.is_vice_captain ? 'V' : '', val, sub })}</div>`; };
    const xi = rows.filter((r) => r.x.multiplier > 0), bench = rows.filter((r) => !r.x.multiplier);
    const row = (t) => xi.filter((r) => r.e.element_type === t).map(card).join('');
    const CHN = { wildcard: 'Wildcard', freehit: 'Free Hit', bboost: 'Bench Boost', '3xc': 'Triple Captain' };
    const sorted = rows.slice().sort((a, b) => b.pts * (b.x.multiplier || 0) - a.pts * (a.x.multiplier || 0) || b.pts - a.pts);
    // v3.69: points add up live from the players' scores (FPL updates the gameweek total later); final weeks use FPL's own total
    const ev = BS.events.find((x) => x.id === g) || {}, liveGw = !ev.finished, sum = xi.reduce((a, r) => a + r.pts * r.x.multiplier, 0);
    const pbSum = xi.reduce((a, r) => a + (r.lb || 0) * r.x.multiplier, 0), pts = liveGw ? sum : (h.points ?? sum), hi = ev.highest_score || 0, cost = h.event_transfers_cost || 0;
    const nf = gfx.length, nDone = gfx.filter((f) => f.finished || f.finished_provisional).length, nLive = gfx.filter((f) => f.started && !(f.finished || f.finished_provisional)).length;
    const yet = xi.filter((r) => ['ns', 'part'].includes(stOf(r.e.team))).length;
    const cell = (l, v, sub) => `<div class="hcell"><small>${l}</small><b>${v}</b>${sub ? `<em>${sub}</em>` : ''}</div>`;
    const hstat = `<div class="hst"><div class="hhero${liveGw ? ' live' : ''}"><small>${liveGw ? 'Live points' : 'Final points'}</small><b>${pts}</b><span>${liveGw ? `${nDone}/${nf} matches done${nLive ? ` · ${nLive} live` : ''}${yet ? ` · ${yet} of your XI to play` : ''}${pbSum ? `</span><span class="hhit">incl. +${pbSum} live bonus` : ''}` : avg ? `${pts >= avg ? '▲' : '▼'} ${Math.abs(pts - avg)} vs average` : `Gameweek ${g}`}</span>${cost ? `<span class="hhit">−${cost} hit · net ${pts - cost}</span>` : ''}</div><div class="hcells">${cell('Average · Highest', `${avg || '–'} <i class="hsep">/</i> ${hi || '–'}`, avg || hi ? '' : 'after the week')}${cell('GW rank', h.rank ? h.rank.toLocaleString() : '–')}${cell('Overall rank', h.overall_rank ? h.overall_rank.toLocaleString() : '–')}${cell('Transfers', h.event_transfers ?? 0, cost ? `<span class="dn">−${cost} hit</span>` : 'no hit')}${cell('Bench points', liveGw ? bench.reduce((a, r) => a + r.pts, 0) : (h.points_on_bench ?? bench.reduce((a, r) => a + r.pts, 0)))}${cell('Chip', CHN[d.pk.active_chip] || 'None')}</div></div>`;
    return `<div class="plgrid hist"><div class="plleft">
${hstat}
<div class="pitch hpitch"><div class="row">${row(1)}</div><div class="row">${row(2)}</div><div class="row">${row(3)}</div><div class="row">${row(4)}</div></div>
${bench.length ? `<div class="benchbox hpitch"><div class="ptitle">Bench</div><div class="row">${bench.map(card).join('')}</div></div>` : ''}
</div><div class="plside"><div class="ptbody"><h3 class="h3" style="margin-top:0">Points per player · GW${g}</h3><div class="tw"><table><thead><tr><th>Player</th><th class="n">Mins</th><th class="n">G</th><th class="n">A</th><th class="n">Bonus</th><th class="n">Pts</th><th class="n">Counted</th></tr></thead><tbody>${sorted.map((r) => `<tr class="${r.x.multiplier ? '' : 'bench'}"><td class="pl"><b>${nm(r.e)}</b><small>${POS[r.e.element_type]} · ${T[r.e.team].short_name}</small></td><td class="n">${r.st.minutes || 0}</td><td class="n">${r.st.goals_scored || 0}</td><td class="n">${r.st.assists || 0}</td><td class="n">${r.st.bonus || 0}</td><td class="n">${r.pts}</td><td class="n"><b>${r.x.multiplier ? r.pts * r.x.multiplier : '<small class="muted">bench</small>'}</b></td></tr>`).join('')}</tbody></table></div></div></div></div>`;
  }
  function showSeason(g) {
    const el = R.getElementById('season-detail'); if (!el || !LAST) return;
    R.querySelectorAll('[data-sgw]').forEach((x) => x.classList.toggle('on', +x.dataset.sgw === g));
    el.innerHTML = `<h3 class="h3">Gameweek ${g}</h3><p class="muted">Loading…</p>`;
    HIST(g).then((d) => { el.innerHTML = `<h3 class="h3">Gameweek ${g}: team and player points</h3>${histHtml(LAST, g, d)}`; el.scrollIntoView({ behavior: 'smooth', block: 'nearest' }); });
  }
  function planGo(g) {
    const A = PLAN.A, lastG = A.GWS[A.GWS.length - 1], first = A.entry.started_event || 1;
    g = Math.max(first, Math.min(lastG, g));
    if (g >= A.startGw) { loadWeek(g); return renderPlanner(); }
    PLAN.gw = g; PLAN.hist = null; PLAN.sel = null; PLAN.buying = null; renderPlanner();
    HIST(g).then((d) => { if (PLAN.gw === g) { PLAN.hist = d; renderPlanner(); } });
  }
  // ---------- v2.7: head to head for planned transfers (shown on the Fixtures page) ----------
  function h2hHtml() {
    if (!PLAN || !PLAN.A) return '<p class="muted">Open the planner first.</p>';
    const A = PLAN.A, g0 = PLAN.gw, P = A.P;
    if (!PLAN.swaps.length) return `<div class="h2hempty"><p class="muted" style="margin:0">No transfers planned for GW${g0} yet. Plan a transfer in the planner, or press “Bring in” on a player, and the sell-versus-buy comparison appears here.</p><button class="try" type="button" data-act="planner">Open planner</button></div>`;
    const SN = (e) => { let t = 0; for (let k = 0; k < 5; k++) t += P(e, g0 + k); return t; };
    const nm = (e) => `<a class="pn" href="#" data-pid="${e.id}">${esc(e.web_name)}</a>`;
    const sign = (v) => `<b class="${v > 0.05 ? 'up' : v < -0.05 ? 'dn' : ''}">${v > 0.05 ? '▲ +' : v < -0.05 ? '▼ ' : ''}${f1(v)}</b>`;
    const stat = (x, f) => (x ? f(x.e) : '–');
    const cmpRows = [
      ['Price', (e) => money(e.now_cost)], ['Owned by', (e) => e.selected_by_percent + '%'], ['Form', (e) => e.form], ['Points per game', (e) => e.points_per_game],
      ['Total points', (e) => e.total_points], ['xGI per 90', (e) => e.expected_goal_involvements_per_90 ?? '–'], ['Set pieces', (e) => spB(e) || '–'],
      ['GW' + g0 + ' projection', (e) => f1(P(e, g0))], ['5-week projection', (e) => f1(SN(e))], ['Next 5 fixtures', (e) => fixChips(A, e.team, 5, g0)],
    ];
    return `<h3 class="h3" style="margin-top:0">GW${g0} transfers: head to head</h3><div class="grid2">${PLAN.swaps.map(({ o, i }) => `<div class="tw"><table class="cmp"><thead><tr><th></th><th>Out: ${nm(o.e)}</th><th>In: ${nm(i.e)}</th></tr></thead><tbody>${cmpRows.map(([l, f]) => `<tr><td class="muted">${l}</td><td>${stat(o, f)}</td><td>${stat(i, f)}</td></tr>`).join('')}<tr><td class="muted">Verdict</td><td colspan="2">${(() => { const g = SN(i.e) - SN(o.e); return g > 0 ? `<b class="up">▲ ${esc(i.e.web_name)} projects +${f1(g)} pts more</b> over 5 gameweeks.` : `<b class="dn">▼ ${esc(o.e.web_name)} projects ${f1(-g)} pts more.</b> Keep him.`; })()}</td></tr></tbody></table></div>`).join('')}</div>`;
  }
  out.addEventListener('click', (ev) => {
    const t = ev.target; if (!t.closest) return;
    const mxr = t.closest('[data-mx]');
    if (mxr && !t.closest('.mxp') && !t.closest('[data-mw]') && !t.closest('a.pn') && LASTA && LASTA.live) { const fid = +mxr.dataset.mx; if (OPENMX.has(fid)) OPENMX.delete(fid); else { OPENMX.add(fid); mxSummary(fid).then((ch) => ch && paintMatches(LASTA)); } paintMatches(LASTA); return; }
    const mwb = t.closest('[data-mw]');
    if (mwb && LASTA && LASTA.live) { ev.preventDefault(); const cur = LASTA.live.gw, total = (BS.events || []).length || 38; if (mwb.dataset.mw === 'cur') MW = null; else { const n = Math.max(1, Math.min(total, (MW == null ? cur : MW) + (+mwb.dataset.mw))); MW = n === cur ? null : n; } paintMatches(LASTA); return; }
    if (t.closest('[data-h2h]')) { cmpFromSwaps(); FIXTAB = 'h2h'; showView('fix', 'h2h'); paintRot(); }
  });

  // ---------- v3.11: shared bits for Market, Head to head and the player page ----------
  const POSL = ['', 'GKP', 'DEF', 'MID', 'FWD'], POSN = ['', 'Goalkeeper', 'Defender', 'Midfielder', 'Forward'];
  const posB = (et) => `<i class="pb p${et}">${POSL[et]}</i>`;
  const sgnM = (v) => (v > 0 ? `<b class="up">+£${(v / 10).toFixed(1)}m</b>` : v < 0 ? `<b class="dn">−£${(-v / 10).toFixed(1)}m</b>` : '<span class="muted">£0.0m</span>');
  const kfmt2 = (n) => (Math.abs(n) >= 1000 ? (Math.abs(n) >= 1e6 ? (n / 1e6).toFixed(1) + 'M' : Math.round(n / 1000) + 'k') : String(n));
  const S6of = (A, e, g0) => { let s = 0; for (let k = 0; k < 6; k++) { const g = (g0 || A.startGw) + k; if (A.GWS.includes(g)) s += A.P(e, g); } return s; };
  const rtg = (A, e) => { try { return A.ratings(e)[0].v; } catch (er) { return 0; } };
  const fxCell = (A, team, g) => { const fs = A.fxBy[team + '-' + g] || []; if (!fs.length) return '<span class="fxc d5 blank">–</span>'; return fs.map((f) => `<span class="fxc d${Math.max(1, Math.min(5, Math.round(f.diff)))}" title="${esc(A.T[f.o].name)} (${f.home ? 'home' : 'away'})">${A.T[f.o].short_name} (${f.home ? 'H' : 'A'})</span>`).join(''); };
  const hdr = (eyebrow, a, b, sub, extra) => `<div class="ptl"><h2>${a} ${b}</h2><p class="sub">${sub}</p>${extra || ''}</div>`;

  // ---------- Players market: transfers and price changes for every player ----------
  const MKT = { q: '', pos: 0, view: 'in', sort: null, dir: -1 };
  const MKV = [['in', 'Most Transferred In', 'net', -1], ['out', 'Most Transferred Out', 'net', 1], ['rise', 'Biggest Risers', 'gw', -1], ['fall', 'Biggest Fallers', 'gw', 1], ['pup', 'Likely to rise', 'pred', -1], ['pdn', 'Likely to fall', 'pred', 1]];
  const MKC = [['cost', 'Cost', (e) => e.now_cost], ['gw', 'Change this GW', (e) => e.cost_change_event], ['season', 'Change this season', (e) => e.cost_change_start], ['tin', 'Transfers in', (e) => e.transfers_in_event], ['tout', 'Transfers out', (e) => e.transfers_out_event], ['net', 'Net transfers', (e) => e.transfers_in_event - e.transfers_out_event], ['own', 'Owned', (e) => +e.selected_by_percent || 0], ['pred', 'Next change', (e) => { const p = pricePred(e); return p ? p.pct : 0; }]];
  // v3.36: progress towards the NEXT price change (from this gameweek's net transfers), not the change already made
  const nextUpd = () => { const nx = new Date(); nx.setUTCHours(1, 30, 0, 0); if (nx < new Date()) nx.setUTCDate(nx.getUTCDate() + 1); return nx; };
  function predCell(e) {
    const p = pricePred(e); if (!p || Math.abs(p.pct) < 20) return '<span class="muted">–</span>';
    const a = Math.min(100, Math.abs(p.pct)), due = Math.abs(p.pct) >= 100, upw = p.d === 'up';
    const t = nextUpd().toLocaleTimeString(undefined, { hour: '2-digit', minute: '2-digit' });
    const when = p.eta === 'tonight' ? `tonight ${t}` : p.eta;
    const tip = `${kfmt(p.since)} net transfers since his last price change. ${due ? 'Past' : Math.round(a) + '% of'} the estimated threshold for a ${upw ? 'rise' : 'drop'}.${when ? ' Expected at the price update ' + when + ' (FPL changes prices once a day, about 01:30 UK time).' : ''} Price changes already made show in the Change this GW / this season columns.`;
    return `<span class="pbar2 ${p.d}" title="${tip}"><i style="width:${a}%"></i><b>${upw ? '▲' : '▼'} ${due ? (upw ? 'Rise due' : 'Drop due') : Math.round(a) + '%'}</b></span>${when ? `<small class="${upw ? 'up' : 'dn'}">${when}</small>` : ''}`;
  }
  function mkBody(A) {
    const q = MKT.q.trim().toLowerCase(), T = A.T;
    const xs = BS.elements.filter((e) => (!MKT.onlySel || SELP.has(e.id)) && (!MKT.pos || e.element_type === MKT.pos) && (!q || `${e.web_name} ${e.first_name} ${e.second_name} ${T[e.team].name} ${T[e.team].short_name}`.toLowerCase().includes(q)));
    const v = MKV.find((x) => x[0] === MKT.view) || MKV[0];
    const key = MKT.sort || v[2], dir = MKT.sort ? MKT.dir : v[3];
    const f = MKC.find((c) => c[0] === key)[2], net = MKC[5][2], ssn = MKC[2][2];
    xs.sort((a, b) => dir * (f(a) - f(b)) || (key === 'gw' ? dir * (ssn(a) - ssn(b)) : 0) || net(b) - net(a));
    const rows = xs;
    const th = (k, l) => `<th class="n sortable ${key === k ? 'on' : ''}" data-mks="${k}" title="Sort by ${l.toLowerCase()}">${key === k ? (dir < 0 ? '↓ ' : '↑ ') : ''}${l}</th>`;
    return `<div class="mkmeta"><span class="muted">Showing <b class="acc">${rows.length}</b> players${xs.length > rows.length ? ` of ${xs.length}` : ''}</span><span class="muted">Last updated ${A.loadedAt.toLocaleDateString(undefined, { day: 'numeric', month: 'short' })} ${A.loadedAt.toLocaleTimeString(undefined, { hour: '2-digit', minute: '2-digit' })}</span></div>
<div class="tw nodeco"><table class="mkt pgd" data-pg="mk"><thead><tr><th class="selc" aria-label="Select"></th><th>Player</th>${MKC.map(([k, l]) => th(k, l)).join('')}</tr></thead><tbody>${rows.map((e) => { const n = net(e); return `<tr class="${SELP.has(e.id) ? 'sel' : ''}">${selCell(e)}<td class="pl">${pface(e)}<a class="pn" href="#" data-pid="${e.id}">${esc(e.web_name)}</a> <small class="muted">${esc(T[e.team].name)}</small> ${posB(e.element_type)}${MKT.view === 'pup' || MKT.view === 'pdn' ? `<div class="pinl">${predCell(e)}</div>` : ''}</td><td class="n">${money(e.now_cost)}</td><td class="n">${sgnM(e.cost_change_event)}</td><td class="n">${sgnM(e.cost_change_start)}</td><td class="n">${kfmt2(e.transfers_in_event)}</td><td class="n">${kfmt2(e.transfers_out_event)}</td><td class="n"><b class="${n > 0 ? 'up' : n < 0 ? 'dn' : ''}">${n > 0 ? '+' : n < 0 ? '−' : ''}${kfmt2(Math.abs(n))}</b></td><td class="n">${e.selected_by_percent}%</td><td class="n">${predCell(e)}</td></tr>`; }).join('') || '<tr><td colspan="9" class="muted">No player matches that search.</td></tr>'}</tbody></table></div>`;
  }
  function marketHtml(A) {
    const gw = A.cur ? A.cur.id : A.startGw;
    return `${hdr('', 'Players', 'market', `Transfers and price changes · all players · GW${gw}`)}
<div class="mkctl"><input id="mk-q" placeholder="Search player or team…" autocomplete="off" aria-label="Search player or team" value="${esc(MKT.q)}"><div class="pseg">${[0, 1, 2, 3, 4].map((p) => `<button type="button" class="${MKT.pos === p ? 'on' : ''}" data-mkpos="${p}">${p ? POSL[p] : 'All'}</button>`).join('')}</div></div>${selBar('mk')}
<div class="mkviews">${MKV.map(([k, l]) => `<button type="button" class="${MKT.view === k && !MKT.sort ? 'on' : ''}" data-mkv="${k}">${l}</button>`).join('')}</div>
<div id="mk-body">${mkBody(A)}</div>`;
  }

  // ---------- Full-season player stats: PL event metrics joined to FPL identity/prices ----------
  const PST = { q: '', pos: 0, sort: 'mins', dir: -1, mode: 'season', rangeLabel: '', data: null, xData: {}, loaded: [], errors: [], failedCodes: [], seasonData: null, seasonId: null, seasonLabel: '', updated: 0, busy: false, error: '' };
  const PS_KEYS = ['apps', 'mins', 'goals', 'goalsIn', 'goalsOut', 'goalsHead', 'shots', 'shotsIn', 'shotsOut', 'shotsHead', 'shotsOn', 'bigScored', 'bigMissed'];
  const PS_X_KEYS = ['xg', 'xa', 'xgi', 'xgc', 'xg90', 'xa90', 'xgi90', 'xgc90'];
  // v3.40: defensive stats (FPL data). dch = matches where defensive contribution earned the +2 bonus.
  const PS_D_KEYS = ['cbi', 'tkl', 'rec', 'dc', 'dc90', 'dch', 'cs', 'sv'];
  const PS_D_SRC = { cbi: 'clearances_blocks_interceptions', tkl: 'tackles', rec: 'recoveries', dc: 'defensive_contribution', cs: 'clean_sheets', sv: 'saves' };
  const psDValue = (e, k) => {
    if (PST.mode === 'season') {
      if (k === 'dch') return PST.dcHits ? (PST.dcHits[e.id] || 0) : null;
      if (k === 'dc90') { const m = Number(e.minutes) || 0; return m > 0 ? (Number(e.defensive_contribution) || 0) * 90 / m : null; }
      const v = Number(e[PS_D_SRC[k]]); return Number.isFinite(v) ? v : null;
    }
    const x = PST.xData && PST.xData[e.id]; if (!x) return null;
    if (k === 'dc90') return x.mins > 0 ? (x.dc || 0) * 90 / x.mins : null;
    const v = Number(x[k]); return Number.isFinite(v) ? v : 0;
  };
  // season count of +2 defensive-contribution returns, read from each finished gameweek's explain data
  async function psLoadDcHits() {
    if (PST.dcHits || PST.dcBusy) return; PST.dcBusy = true;
    try {
      const last = psLatestFinishedGw(), hits = {}; const gws = Array.from({ length: last }, (_, i) => i + 1);
      let i = 0; await Promise.all(Array.from({ length: 4 }, async () => { while (i < gws.length) { const g = gws[i++]; try { const lv = await J(`/api/event/${g}/live/`); (lv.elements || []).forEach((el) => { (el.explain || []).forEach((fx) => (fx.stats || []).forEach((s) => { if (s.identifier === 'defensive_contribution' && s.points > 0) hits[el.id] = (hits[el.id] || 0) + 1; })); }); } catch (e) {} } }));
      PST.dcHits = hits;
    } finally { PST.dcBusy = false; const b = R.getElementById('ps-table-wrap'); if (b && LASTA && PST.data && FIXTAB === 'stats') b.innerHTML = psTable(LASTA); }
  }
  const PS_X_SOURCE = { xg: 'expected_goals', xa: 'expected_assists', xgi: 'expected_goal_involvements', xgc: 'expected_goals_conceded' };
  const psXValue = (e, key) => {
    const source = PS_X_SOURCE[key.replace(/90$/, '')];
    if (!source) return null;
    let total;
    if (PST.mode === 'season') total = Number(e[source]);
    else total = Number(PST.xData && PST.xData[e.id] && PST.xData[e.id][key.replace(/90$/, '')]);
    if (!Number.isFinite(total)) return null;
    if (!key.endsWith('90')) return total;
    const mins = PST.mode === 'season' ? Number(e.minutes) : Number(PST.xData && PST.xData[e.id] && PST.xData[e.id].mins);
    return mins > 0 ? total * 90 / mins : null;
  };
  const psFailed = (e) => !!(PST.failedCodes && e.opta_code && PST.failedCodes.includes(e.opta_code));
  const psNumber = (e, k) => { const p = PST.data && e.opta_code ? PST.data[e.opta_code] : null; return p && Number.isFinite(+p[k]) ? +p[k] : 0; };
  const psAvailable = (k) => PST.loaded.includes(k);
  const psField = (e, k) => {
    if (k === 'team') return e.team;
    if (k === 'cost') return e.now_cost;
    if (k === 'mGoal') return psNumber(e, 'goals') ? psNumber(e, 'mins') / psNumber(e, 'goals') : 0;
    if (k === 'mShot') return psNumber(e, 'shots') ? psNumber(e, 'mins') / psNumber(e, 'shots') : 0;
    if (k === 'big') return psNumber(e, 'bigScored') + psNumber(e, 'bigMissed');
    return psNumber(e, k);
  };
  const psMetricFor = { apps: 'apps', mins: 'mins', goals: 'goals', goalsIn: 'goalsIn', goalsOut: 'goalsOut', goalsHead: 'goalsHead', shots: 'shots', shotsIn: 'shotsIn', shotsOut: 'shotsOut', shotsHead: 'shotsHead', shotsOn: 'shotsOn', big: 'bigScored' };
  function psValue(e, key) {
    if (PS_D_KEYS.includes(key)) return psDValue(e, key);
    if (!['name', 'team', 'cost'].includes(key) && !PS_X_KEYS.includes(key) && psFailed(e)) return null;
    const metric = psMetricFor[key];
    if (key === 'name') return e.web_name;
    if (key === 'team' || key === 'cost') return psField(e, key);
    if (PS_X_KEYS.includes(key)) return psXValue(e, key);
    if (key === 'mGoal') return psAvailable('mins') && psAvailable('goals') ? psField(e, key) : null;
    if (key === 'mShot') return psAvailable('mins') && psAvailable('shots') ? psField(e, key) : null;
    if (key === 'big') return psAvailable('bigScored') && psAvailable('bigMissed') ? psField(e, key) : null;
    return psAvailable(metric) ? psField(e, key) : null;
  }
  function psTable(A) {
    const T = A.T, q = PST.q.trim().toLowerCase();
    const ranked = [...BS.elements].sort((a, b) => {
      const score = (e) => { const mins = Number(e.minutes) || 0; const xgi = Number(e.expected_goal_involvements) || 0; const points = Number(e.total_points) || 0; const recent = Number(e.form) || 0; const starts = Number(e.starts) || 0; return (Math.min(mins / 900, 1) * 30) + (Math.min(starts / 10, 1) * 20) + (Math.min(points / 80, 1) * 20) + (Math.min(xgi / 8, 1) * 20) + (Math.min(recent / 8, 1) * 10); }; return score(b) - score(a); });
    const shortlist = ranked;
    const players = shortlist.filter((e) => (!PST.onlySel || SELP.has(e.id)) && (!PST.pos || e.element_type === PST.pos) && (!q || `${e.web_name} ${e.first_name} ${e.second_name} ${T[e.team].name} ${T[e.team].short_name}`.toLowerCase().includes(q)));
    const sortVal = (e) => psValue(e, PST.sort);
    players.sort((a, b) => { const x = sortVal(a), y = sortVal(b); if (x == null && y != null) return 1; if (y == null && x != null) return -1; const cmp = typeof x === 'string' ? x.localeCompare(y) : (x || 0) - (y || 0); return PST.dir * cmp || a.web_name.localeCompare(b.web_name); });
    const PSG = { goals: 'g1', goalsIn: 'g1', goalsOut: 'g1', goalsHead: 'g1', mGoal: 'g1', shots: 'g2', shotsIn: 'g2', shotsOut: 'g2', shotsHead: 'g2 g2x', shotsOn: 'g2', mShot: 'g2', big: 'g3', xg: 'g4', xa: 'g4', xgi: 'g4', xgc: 'g4', xg90: 'g6', xa90: 'g6', xgi90: 'g6', xgc90: 'g6', cbi: 'g7', tkl: 'g7', rec: 'g7', dc: 'g7', dc90: 'g7 g7x', dch: 'g7', cs: 'g7 g7x', sv: 'g7 g7x' };
    const th = (k, label, title) => { const on = PST.sort === k; return `<th class="ps-sort ${PSG[k] || ''} ${on ? 'on' : ''}" data-psort="${k}" title="${title || `Sort by ${label}`}" aria-sort="${on ? (PST.dir < 0 ? 'descending' : 'ascending') : 'none'}">${label}${on ? `<span class="ps-sortmark">${PST.dir < 0 ? '↓' : '↑'}</span>` : ''}</th>`; };
    const fmt = (e, k, decimals) => { const v = psValue(e, k); if (v == null) return '<span class="muted">–</span>'; if ((k === 'mGoal' || k === 'mShot') && !v) return '<span class="muted">–</span>'; return decimals ? Number(v).toFixed(decimals === true ? 1 : decimals) : Math.round(Number(v)).toLocaleString(); };
    const rows = players.map((e) => {
      const bc = psValue(e, 'big');
      return `<tr class="${SELP.has(e.id) ? 'sel' : ''}">${selCell(e)}<td class="ps-name">${pface(e)}<a class="pn" href="#" data-pid="${e.id}">${esc(e.web_name)}</a> <i class="pb p${e.element_type}">${POSL[e.element_type]}</i></td><td class="ps-team pbs" title="${esc(T[e.team].name)}">${esc(T[e.team].short_name)}</td><td class="pbs">${(e.now_cost / 10).toFixed(1)}</td><td class="pbs">${fmt(e, 'apps')}</td><td>${fmt(e, 'mins')}</td><td class="g1">${fmt(e, 'goals')}</td><td class="g1">${fmt(e, 'goalsIn')}</td><td class="g1">${fmt(e, 'goalsOut')}</td><td class="g1">${fmt(e, 'goalsHead')}</td><td class="g1">${fmt(e, 'mGoal')}</td><td class="g2">${fmt(e, 'shots')}</td><td class="g2">${fmt(e, 'shotsIn')}</td><td class="g2">${fmt(e, 'shotsOut')}</td><td class="g2 g2x">${fmt(e, 'shotsHead')}</td><td class="g2">${fmt(e, 'shotsOn')}</td><td class="g2">${fmt(e, 'mShot')}</td><td class="g3">${bc == null ? '<span class="muted">–</span>' : `<span title="${psNumber(e, 'bigScored')} scored + ${psNumber(e, 'bigMissed')} missed">${Math.round(bc)}</span>`}</td>${PS_X_KEYS.map((k) => `<td class="${/90$/.test(k) ? 'g6' : 'g4'}">${fmt(e, k, /90$/.test(k) ? 2 : 1)}</td>`).join('')}${PS_D_KEYS.map((k) => `<td class="g7${['dc90', 'cs', 'sv'].includes(k) ? ' g7x' : ''}">${fmt(e, k, k === 'dc90' ? 1 : 0)}</td>`).join('')}<td class="g5">${(() => { const n = (Number(e.transfers_in_event) || 0) - (Number(e.transfers_out_event) || 0); return (n > 0 ? '+' : n < 0 ? '−' : '') + kfmt(Math.abs(n)); })()}</td></tr>`;
    }).join('');
    const loadedCount = players.length;
    const baseHdr = (key, label, cls) => `<th rowspan="2" class="ps-base ps-sort ${cls || ''} ${PST.sort === key ? 'on' : ''}" data-psort="${key}">${label}${PST.sort === key ? `<span class="ps-sortmark">${PST.dir < 0 ? '↓' : '↑'}</span>` : ''}</th>`;
    const baseCols = `<th rowspan="2" class="selc" aria-label="Select"></th>${baseHdr('name', 'Player', 'ps-name')}${baseHdr('team', 'Team', 'pbs')}${baseHdr('cost', '£m', 'pbs')}${baseHdr('apps', 'App', 'pbs')}${baseHdr('mins', 'Mins')}`;
    return `<div class="ps-scroll nodeco" data-g="${PST.grp || 'att'}"><table class="pstats pgd" data-pg="ps"><thead><tr>${baseCols}<th colspan="5" class="ps-group g1">GOALS</th><th colspan="6" class="ps-group g2">SHOTS</th><th colspan="1" class="ps-group g3" title="Big chances: scored + missed">BIG</th><th colspan="4" class="ps-group g4">EXPECTED</th><th colspan="4" class="ps-group g6">PER 90</th><th colspan="8" class="ps-group g7 g7w">DEFENCE</th><th colspan="5" class="ps-group g7n">DEFENCE</th><th rowspan="2" class="ps-base g5" title="Net transfers this gameweek">NET</th></tr><tr>${th('goals', 'Tot', 'Total goals')}${th('goalsIn', 'In', 'Goals from inside the box')}${th('goalsOut', 'Out', 'Goals from outside the box')}${th('goalsHead', 'H', 'Headed goals')}${th('mGoal', 'M/G', 'Minutes per goal')}${th('shots', 'Tot', 'Total shots')}${th('shotsIn', 'In', 'Shots inside the box')}${th('shotsOut', 'Out', 'Shots outside the box')}${th('shotsHead', 'H', 'Headed shots')}${th('shotsOn', 'On', 'Shots on target')}${th('mShot', 'M/S', 'Minutes per shot')}${th('big', 'Tot', 'Big chances scored + missed')}${PS_X_KEYS.map((k) => th(k, ({ xg: 'xG', xa: 'xA', xgi: 'xGI', xgc: 'xGC', xg90: 'xG/90', xa90: 'xA/90', xgi90: 'xGI/90', xgc90: 'xGC/90' })[k], `FPL expected metric ${k}`)).join('')}${PS_D_KEYS.map((k) => th(k, ({ cbi: 'CBI', tkl: 'Tkl', rec: 'Rec', dc: 'DC', dc90: 'DC/90', dch: 'DC+2', cs: 'CS', sv: 'Sv' })[k], ({ cbi: 'Clearances, blocks and interceptions', tkl: 'Tackles', rec: 'Recoveries', dc: 'Defensive contribution (the count FPL uses for its +2 bonus)', dc90: 'Defensive contribution per 90 minutes', dch: 'Matches where defensive contribution earned +2 FPL points', cs: 'Clean sheets', sv: 'Saves' })[k])).join('')}</tr></thead><tbody>${rows || `<tr><td colspan="34" class="muted">No players match that search.</td></tr>`}</tbody></table></div><div class="ps-meta"><span><b class="acc">${loadedCount}</b> players · M/G minutes per goal · M/S minutes per shot · xG from FPL</span><span>${PST.mode === 'season' ? 'Full season' : PST.rangeLabel}${PST.updated ? ` · Updated ${new Date(PST.updated).toLocaleString()}` : ''}</span></div>`;
  }
  const PSG_D = { att: 'att', g1: 'att', g2: 'att', g3: 'att', exp: 'exp', g4: 'exp', g6: 'exp', def: 'def', g7: 'def' }, PSG_M = { att: 'g1', exp: 'g4', def: 'g7' };
  const psgOn = (k) => { const g = PST.grp || 'att'; return ['att', 'exp', 'def'].includes(k) ? PSG_D[g] === k : (PSG_M[g] || g) === k; };
  // v3.43: pick several players in Player stats or Market; show only them, or compare them in Head to head
  const SELP = new Set();
  const selBar = (which) => `<div class="selbar ${SELP.size ? 'on' : ''}" data-selbar="${which}"><span><b>${SELP.size}</b> selected${SELP.size ? `: ${[...SELP].slice(0, 4).map((id) => esc((BS.elements.find((x) => x.id === id) || {}).web_name || '')).join(', ')}${SELP.size > 4 ? '…' : ''}` : ' · tick players to compare them'}</span>${SELP.size ? `<button type="button" class="${(which === 'ps' ? PST.onlySel : MKT.onlySel) ? 'on' : ''}" data-selonly="${which}">Only selected</button><button type="button" data-selcmp="1" ${SELP.size < 2 ? 'disabled' : ''}>Compare ${SELP.size}</button><button type="button" class="ghost" data-selclr="${which}">Clear</button>` : ''}</div>`;
  const selCell = (e) => `<td class="selc"><button type="button" class="pck ${SELP.has(e.id) ? 'on' : ''}" data-pck="${e.id}" aria-pressed="${SELP.has(e.id)}" aria-label="Select ${esc(e.web_name)}"></button></td>`;
  function playerStatsHtml(A) {
    const status = PST.error ? `<div class="errbox"><b>Player stats could not be loaded</b><p>${esc(PST.error)}</p><button type="button" class="mbtn" data-ps-retry="1">Retry</button></div>`
      : PST.busy ? `<div class="ps-info ps-status">${PST.mode === 'season' ? 'Loading full-season Premier League stats…' : `Loading player stats for ${esc(PST.rangeLabel)}… This may take a short while.`}</div>`
      : PST.errors.length ? `<div class="ps-info ps-status ps-partial">Some stats could not be refreshed (${PST.errors.length}); unavailable values show –. <button type="button" class="mbtn ghost" data-ps-retry="1">Retry</button></div>`
      : '';
    const info = `<div class="ps-info">${PST.mode === 'season' ? 'All-season totals' : esc(PST.rangeLabel)} · M/G: minutes per goal · M/S: minutes per shot · xG metrics from FPL data.</div>`;
    const modes = [['season', 'All Season'], ['last5', 'Last 5 GWs']].map(([k, label]) => `<button type="button" class="${PST.mode === k ? 'on' : ''}" data-psmode="${k}" ${PST.busy ? 'disabled' : ''}>${label}</button>`).join('');
    return `${hdr('', 'Player', 'stats', 'Compare full-season performance with recent gameweeks')}
${status}<div class="pstool"><div class="ps-modes" role="group" aria-label="Stats period">${modes}</div><span class="pslab">Stats</span><div class="pseg psgrp" role="group" aria-label="Stats columns">${[['att', 'Attack', 'd'], ['exp', 'Expected', 'd'], ['def', 'DefCon', 'd'], ['g1', 'Goals', 'm'], ['g2', 'Shots', 'm'], ['g4', 'xG', 'm'], ['g6', 'Per 90', 'm'], ['g7', 'DefCon', 'm']].map(([k, l, s]) => `<button type="button" class="psg-${s} ${psgOn(k) ? 'on' : ''}" data-psg="${k}">${l}</button>`).join('')}</div><input id="ps-q" placeholder="Search player or team…" autocomplete="off" aria-label="Search player or team" value="${esc(PST.q)}"><span class="pslab">Position</span><div class="pseg pspos" role="group" aria-label="Position">${[0, 1, 2, 3, 4].map((p) => `<button type="button" class="${PST.pos === p ? 'on' : ''}" data-pspos="${p}">${p ? POSL[p] : 'All'}</button>`).join('')}</div></div>
${selBar('ps')}<div id="ps-table-wrap">${PST.data ? psTable(A) : `<div class="ps-info">${PST.busy ? 'Collecting player stats…' : 'Stats load automatically the first time you open this tab.'}</div>`}</div>`;
  }
  const psSeasonYear = () => { const d = BS && BS.events && BS.events[0] ? new Date(BS.events[0].deadline_time) : new Date(); return d.getUTCFullYear() - (d.getUTCMonth() < 6 ? 1 : 0); };
  const psCacheKey = () => `fplAnalystPlayerStats-v2-${psSeasonYear()}`;
  // v3.36: Android (native fetch) and iPhone (userscript GM fetch) read the Premier League stats feed directly
  const PL_API_C = 'https://footballapi.pulselive.com/football/';
  const PL_MET = { apps: 'appearances', mins: 'mins_played', goals: 'goals', goalsIn: 'att_ibox_goal', goalsOut: 'att_obox_goal', goalsHead: 'att_hd_goal', shots: 'total_scoring_att', shotsIn: 'attempts_ibox', shotsOut: 'attempts_obox', shotsHead: 'att_hd_total', shotsOn: 'ontarget_scoring_att', bigScored: 'big_chance_scored', bigMissed: 'big_chance_missed' };
  const plGet = (path) => { const d = directText(); if (!d) return Promise.reject(new Error('Player stats need the Chrome extension, the Android app or the iPhone script.')); return withTimeout(d(PL_API_C + path), 20000).then((t) => JSON.parse(t)); };
  async function plSeason() { const s = await plGet('competitions/1/compseasons?page=0&pageSize=100'); const x = (s.content || [])[0]; if (!x || !x.id) throw new Error('Could not identify the current Premier League season.'); return x; }
  const plPool = async (items, n, fn) => { let i = 0; await Promise.all(Array.from({ length: n }, async () => { while (i < items.length) { const it = items[i++]; await fn(it); } })); };
  async function plStatsDirect() {
    const season = await plSeason(); const output = {}, errors = [], loaded = [];
    await plPool(Object.entries(PL_MET), 4, async ([key, metric]) => {
      try {
        let rows = [], page = 0, pages = 1;
        do { const qs = new URLSearchParams({ comp: '1', compSeasons: String(season.id), altIds: 'true', page: String(page), pageSize: '1000' }); const r = await plGet(`stats/ranked/players/${encodeURIComponent(metric)}?${qs}`); const st = r.stats || {}; rows = rows.concat(st.content || []); pages = Math.min(5, Number(st.pageInfo && st.pageInfo.numPages) || 1); page++; } while (page < pages);
        rows.forEach((row) => { const code = row && row.owner && row.owner.altIds && row.owner.altIds.opta; if (!code) return; const o = output[code] || (output[code] = {}); o[key] = Number(row.value) || 0; if (row.owner.id) o._plId = Number(row.owner.id); });
        loaded.push(key);
      } catch (e) { errors.push({ key, message: String(e && e.message || e) }); }
    });
    return { seasonId: season.id, seasonLabel: season.label || '', fetchedAt: Date.now(), data: output, loaded, errors };
  }
  async function plWindowDirect(fromGw, toGw, players) {
    const season = await plSeason();
    const qs = new URLSearchParams({ comp: '1', compSeasons: String(season.id), page: '0', pageSize: '1000' });
    const fx = await plGet(`fixtures?${qs}`); const fr = Array.isArray(fx) ? fx : (fx.content || []);
    const ids = fr.filter((f) => f && f.status === 'C' && Number(f.gameweek && f.gameweek.gameweek) >= fromGw && Number(f.gameweek && f.gameweek.gameweek) <= toGw).map((f) => Number(f.id)).filter(Number.isFinite);
    if (!ids.length) throw new Error(`No completed Premier League fixtures found for GW${fromGw}–GW${toGw}.`);
    const data = {}, failed = [];
    await plPool(players, 6, async (p) => { try { const r = await plGet(`stats/player/${Number(p.playerId)}?fixtures=${ids.join(',')}`); const row = {}; (r.stats || []).forEach((s) => { const k = Object.keys(PL_MET).find((x) => PL_MET[x] === s.name); if (k) row[k] = Number(s.value) || 0; }); data[p.code] = row; } catch (e) { failed.push(p.code); } });
    return { seasonId: season.id, seasonLabel: season.label || '', fromGw, toGw, fixtureCount: ids.length, fetchedAt: Date.now(), data, loaded: Object.keys(PL_MET), failedCodes: failed, errors: failed.length ? [{ message: `${failed.length} players could not be refreshed.` }] : [] };
  }
  function requestPlStats() { if (!extId()) return plStatsDirect(); return new Promise((resolve, reject) => { try { chrome.runtime.sendMessage({ type: 'fpl-pl-player-stats' }, (r) => { const er = chrome.runtime.lastError; if (er || !r || !r.ok) reject(new Error((er && er.message) || (r && r.error) || 'Premier League stats request failed.')); else resolve(r.data); }); } catch (e) { reject(e); } }); }
  function requestPlWindow(fromGw, toGw, players) { if (!extId()) return plWindowDirect(fromGw, toGw, players); return new Promise((resolve, reject) => { try { chrome.runtime.sendMessage({ type: 'fpl-pl-player-window-stats', fromGw, toGw, players }, (r) => { const er = chrome.runtime.lastError; if (er || !r || !r.ok) reject(new Error((er && er.message) || (r && r.error) || 'Premier League gameweek stats request failed.')); else resolve(r.data); }); } catch (e) { reject(e); } }); }
  function psLatestFinishedGw() { return Math.max(0, ...(BS.events || []).filter((g) => g.finished).map((g) => Number(g.id) || 0)); }
  async function loadPlayerWindow(force, mode) {
    const toGw = psLatestFinishedGw();
    if (!toGw) throw new Error('No completed gameweek is available yet.');
    const span = 5, fromGw = Math.max(1, toGw - span + 1), label = `Last 5 GWs · GW${fromGw}–GW${toGw}`;
    PST.rangeLabel = label;
    const cacheKey = `${psCacheKey()}-${mode}-GW${fromGw}-${toGw}`;
    if (!force) { try { const c = JSON.parse(localStorage.getItem(cacheKey) || 'null'); if (c && c.data && Date.now() - c.fetchedAt < 3 * 3600e3) { return { ...c, rangeLabel: label }; } } catch (e) {} }
    if (!PST.seasonData) {
      let c = null; try { c = JSON.parse(localStorage.getItem(psCacheKey()) || 'null'); } catch (e) {}
      if (c && c.data && c.data[Object.keys(c.data)[0]] && c.data[Object.keys(c.data)[0]]._plId) PST.seasonData = c;
      else PST.seasonData = await requestPlStats();
      PST.seasonId = PST.seasonData.seasonId; PST.seasonLabel = PST.seasonData.seasonLabel || '';
      try { localStorage.setItem(psCacheKey(), JSON.stringify(PST.seasonData)); } catch (e) {}
    }
    const played = new Set(), xData = {};
    for (let gw = fromGw; gw <= toGw; gw++) {
      const live = await J(`/api/event/${gw}/live/`);
      for (const el of (live.elements || [])) {
        const id = Number(el.id), stats = el.stats || {};
        if (Number(stats.minutes) > 0) played.add(id);
        const x = xData[id] || (xData[id] = { xg: 0, xa: 0, xgi: 0, xgc: 0, mins: 0, cbi: 0, tkl: 0, rec: 0, dc: 0, dch: 0, cs: 0, sv: 0 });
        x.cbi += Number(stats.clearances_blocks_interceptions) || 0; x.tkl += Number(stats.tackles) || 0; x.rec += Number(stats.recoveries) || 0; x.dc += Number(stats.defensive_contribution) || 0; x.cs += Number(stats.clean_sheets) || 0; x.sv += Number(stats.saves) || 0;
        (el.explain || []).forEach((fx) => (fx.stats || []).forEach((s) => { if (s.identifier === 'defensive_contribution' && s.points > 0) x.dch++; }));
        x.mins += Number(stats.minutes) || 0;
        x.xg += Number(stats.expected_goals) || 0; x.xa += Number(stats.expected_assists) || 0;
        x.xgi += Number(stats.expected_goal_involvements) || 0; x.xgc += Number(stats.expected_goals_conceded) || 0;
      }
    }
    for (const e of BS.elements) if (!xData[e.id]) xData[e.id] = { xg: 0, xa: 0, xgi: 0, xgc: 0, mins: 0, cbi: 0, tkl: 0, rec: 0, dc: 0, dch: 0, cs: 0, sv: 0 };
    const players = BS.elements.filter((e) => played.has(e.id) && e.opta_code && PST.seasonData.data[e.opta_code] && PST.seasonData.data[e.opta_code]._plId).map((e) => ({ code: e.opta_code, playerId: PST.seasonData.data[e.opta_code]._plId }));
    const result = await requestPlWindow(fromGw, toGw, players);
    const value = { ...result, xData, rangeLabel: label };
    try { localStorage.setItem(cacheKey, JSON.stringify(value)); } catch (e) {}
    return value;
  }
  async function loadPlayerStats(force) {
    if (PST.busy) return;
    const mode = PST.mode;
    if (!force && PST.data && Date.now() - PST.updated < 3 * 3600e3) return;
    PST.error = ''; PST.errors = []; PST.failedCodes = [];
    PST.busy = true; paintRot();
    try {
      let result;
      if (mode === 'season') {
        result = await requestPlStats();
        if (!result.loaded || !result.loaded.length) throw new Error(result.errors && result.errors[0] ? `Premier League feed error: ${result.errors[0].message}` : 'No player statistics were returned.');
        PST.seasonData = result;
        try { localStorage.setItem(psCacheKey(), JSON.stringify(result)); } catch (e) {}
        setTimeout(psLoadDcHits, 0);
      } else result = await loadPlayerWindow(force, mode);
      PST.data = result.data || {}; PST.xData = result.xData || {}; PST.loaded = result.loaded || []; PST.errors = result.errors || []; PST.failedCodes = result.failedCodes || []; PST.seasonId = result.seasonId; PST.seasonLabel = result.seasonLabel || ''; PST.rangeLabel = result.rangeLabel || PST.rangeLabel; PST.updated = result.fetchedAt || Date.now();
    } catch (e) { PST.error = String(e && e.message || e); }
    finally { PST.busy = false; if (FIXTAB === 'stats' || FIXTAB === 'market') paintRot(); }
  }

  // ---------- Head to head: compare up to 10 players side by side ----------
  const CMP = { ids: [], q: '', pos: 0, col: 'gw', mode: 'weeks' };
  function cmpFromSwaps() { if (PLAN && PLAN.swaps && PLAN.swaps.length) CMP.ids = PLAN.swaps.flatMap((s) => [s.o.e.id, s.i.e.id]).filter((v, i, a) => a.indexOf(v) === i).slice(0, 10); }
  function cmpList(A) {
    const q = CMP.q.trim().toLowerCase(), T = A.T, g0 = A.startGw;
    const val = (e) => (CMP.col === 'gw' ? A.P(e, g0) : S6of(A, e, g0));
    const xs = BS.elements.filter((e) => (e.minutes > 0 || CMP.ids.includes(e.id)) && (!CMP.pos || e.element_type === CMP.pos) && (!q || `${e.web_name} ${e.first_name} ${e.second_name} ${T[e.team].name} ${T[e.team].short_name}`.toLowerCase().includes(q)))
      .map((e) => ({ e, v: val(e) })).sort((a, b) => b.v - a.v);
    return xs.slice(0, 250).map(({ e, v }) => `<button type="button" class="crow ${CMP.ids.includes(e.id) ? 'on' : ''}" data-cmpadd="${e.id}" aria-pressed="${CMP.ids.includes(e.id)}"><span class="cn">${pface(e).replace('class="picon face"', 'class="picon face fsm"')}<b>${esc(e.web_name)}</b><small>${posB(e.element_type)} ${esc(T[e.team].short_name)}</small></span><span class="cp">${money(e.now_cost)}</span><span class="cr">${rtg(A, e)}</span><span class="cv">${f1(v)}</span></button>`).join('') || '<p class="muted" style="padding:8px">No players match.</p>';
  }
  function cmpHtml(A) {
    const T = A.T, g0 = A.startGw;
    const gws = A.GWS.filter((g) => g >= g0).slice(0, 6), gEnd = gws[gws.length - 1];
    const sel = CMP.ids.map((id) => A.E[id]).filter(Boolean);
    const nPool = BS.elements.filter((e) => e.minutes > 0).length;
    const left = `<aside class="cmpl"><h3>Add players <small class="muted">${sel.length}/10</small></h3><div class="cmpq"><input id="cmp-q" placeholder="Search name or club" autocomplete="off" aria-label="Search name or club" value="${esc(CMP.q)}"></div>
<div class="pseg full">${[0, 1, 2, 3, 4].map((p) => `<button type="button" class="${CMP.pos === p ? 'on' : ''}" data-cmppos="${p}">${p ? POSL[p] : 'All'}</button>`).join('')}</div>
<div class="clh"><span>Name <small>${nPool} players</small></span><span>£</span><span>Rtg</span><span class="cseg"><button type="button" class="${CMP.col === 'gw' ? 'on' : ''}" data-cmpc="gw">GW${g0}</button><button type="button" class="${CMP.col === '6' ? 'on' : ''}" data-cmpc="6">6 GW</button></span></div>
<div class="clist" id="cmp-list">${cmpList(A)}</div></aside>`;
    const swaps = PLAN && PLAN.swaps && PLAN.swaps.length ? `<div class="cmpswap"><span class="muted">Planned GW${PLAN.gw}:</span> ${PLAN.swaps.map((s) => `<span class="mv"><i class="mo">OUT</i>${esc(s.o.e.web_name)}</span><span class="mv"><i class="mi">IN</i>${esc(s.i.e.web_name)}</span>`).join(' ')}<button class="lnk2" type="button" data-cmpswap="1">Compare these</button></div>` : '';
    const chips = `<div class="cmpsel nodeco">${sel.map((e) => `<span class="cchip">${pface(e).replace('class="picon face"', 'class="picon face fsm"')}${posB(e.element_type)}<a class="pn" href="#" data-pid="${e.id}">${esc(e.web_name)}</a><small>${T[e.team].short_name}</small><button type="button" class="cx" data-cmpx="${e.id}" aria-label="Remove ${esc(e.web_name)}">×</button></span>`).join('')}<button type="button" class="mbtn cadd" data-cmppick="1" aria-expanded="${!!CMP.pick}">${CMP.pick ? '✓ Done' : '＋ Add players'}</button>${sel.length ? '<button class="lnk2" type="button" data-cmpclear="1">Clear</button>' : ''}</div>`;
    let right;
    if (!sel.length) right = `${swaps}<div class="cmpempty"><span class="cico">⇄</span><p>Pick up to 10 players to compare.</p></div>`;
    else {
      const best = (vals, hi) => { const m = hi === false ? Math.min(...vals) : Math.max(...vals); return (v) => (sel.length > 1 && v === m ? 'best' : ''); };
      const kpi = (e) => (CMP.mode === 'weeks' ? gws.reduce((a, g) => a + A.P(e, g), 0) : e.total_points); const kTop = Math.max(...sel.map(kpi));
      const head = `<thead><tr><th class="cmk"></th>${sel.map((e) => { const k = kpi(e), kc = (JST[T[e.team].short_name] || ['#33507e'])[0]; return `<th class="cph"><div class="pcard ${sel.length > 1 && k === kTop ? 'lead' : ''}" style="--kc:${kc}"><button type="button" class="cx" data-cmpx="${e.id}" aria-label="Remove ${esc(e.web_name)}">×</button>${pface(e).replace('class="picon face"', 'class="picon face fbig"')}<a class="pn" href="#" data-pid="${e.id}">${esc(e.web_name)}</a><small>${posB(e.element_type)} ${T[e.team].short_name} · ${money(e.now_cost)}</small><span class="pkpi"><b>${CMP.mode === 'weeks' ? f1(k) : k}</b><small>${CMP.mode === 'weeks' ? `pts next ${gws.length}` : 'season pts'}</small></span></div></th>`; }).join('')}</tr></thead>`;
      const rowF = (lab, vals, fmt, hi, extra) => { const B = best(vals, hi); const mx = Math.max(...vals.map((v) => Math.abs(v)), 1e-9), mn = Math.min(...vals); return `<tr><th class="cmk">${lab}</th>${vals.map((v, k) => { const w = hi === false ? (v > 0 ? mn / v : 0) : Math.abs(v) / mx; return `<td class="${B(v) ? 'win' : ''}">${extra ? extra(sel[k]) : ''}<b class="${B(v)}">${fmt(v)}</b><span class="cbar"><i style="width:${Math.round(Math.max(4, w * 100))}%"></i></span></td>`; }).join('')}</tr>`; };
      let body;
      if (CMP.mode === 'weeks') {
        body = rowF(`Next ${gws.length} GWs`, sel.map((e) => gws.reduce((a, g) => a + A.P(e, g), 0)), f1) +
          gws.map((g, i) => rowF(`GW${g}`, sel.map((e) => A.P(e, g)), f1, true, (e) => `<div class="cfx">${fxCell(A, e.team, g)}</div>`)).join('') +
          rowF('Rating', sel.map((e) => +rtg(A, e) || 0), (v) => v) + rowF('Price', sel.map((e) => e.now_cost), money, false) + rowF('Form', sel.map((e) => +e.form || 0), (v) => v.toFixed(1)) + rowF('Owned', sel.map((e) => +e.selected_by_percent || 0), (v) => v.toFixed(1) + '%');
      } else {
        const team = (e) => Math.max(1, (A.tb[e.team] || {}).P || 1);
        const C = [['Points', (e) => e.total_points, 0], ['Goals', (e) => e.goals_scored, 0], ['Assists', (e) => e.assists, 0], ['xG/90', (e) => +e.expected_goals_per_90 || 0, 2], ['xA/90', (e) => +e.expected_assists_per_90 || 0, 2], ['Clean sheets', (e) => e.clean_sheets, 0], ['Def actions', (e) => +e.defensive_contribution || 0, 0], ['Bonus', (e) => e.bonus, 0], ['Mins / match', (e) => Math.round(e.minutes / team(e)), 0], ['Starts', (e) => e.starts || 0, 0], ['Owned', (e) => +e.selected_by_percent || 0, 1, '%']];
        body = C.map(([l, f, d, u]) => rowF(l, sel.map(f), (v) => v.toFixed(d) + (u || ''))).join('');
      }
      right = `${swaps}<div class="cmpbar"><span class="cseg"><button type="button" class="${CMP.mode === 'weeks' ? 'on' : ''}" data-cmpm="weeks">Weeks ahead</button><button type="button" class="${CMP.mode === 'season' ? 'on' : ''}" data-cmpm="season">Season stats</button></span><small class="muted">${CMP.mode === 'weeks' ? `Projected points GW${g0}–GW${gEnd}` : 'This season so far'} · best in green</small></div>
<div class="tw nodeco cmpw"><table class="cmpv">${head}<tbody>${body}</tbody></table></div>`;
    }
    return `<div class="cmptop"><div><small class="eyebrow">Head to head</small><h3>Compare players</h3></div><div class="cmpact"><button type="button" class="mbtn ghost cadd" data-cmppick="1" aria-expanded="${!!CMP.pick}">${CMP.pick ? '✓ Done' : '＋ Add players'}</button>${sel.length ? '<button class="mbtn ghost" type="button" data-cmpclear="1">Clear</button>' : ''}<button class="mbtn" type="button" data-act="planner">✎ Planner</button></div></div><div class="cmpgrid${CMP.pick || !sel.length ? ' pick' : ''}">${left}<div class="cmpr">${right}</div></div>`;
  }
  function paintFix2(part) {
    const A = LASTA; if (!A) return;
    if (part === 'mk') { const b = R.getElementById('mk-body'); if (b) b.innerHTML = mkBody(A); return; }
    if (part === 'cmplist') { const l = R.getElementById('cmp-list'); if (l) l.innerHTML = cmpList(A); return; }
    const sc = R.querySelector('#s-fix .clist'); const keep = sc ? sc.scrollTop : 0; paintRot(); const sc2 = R.querySelector('#s-fix .clist'); if (sc2) sc2.scrollTop = keep;
  }
  out.addEventListener('input', (ev) => {
    if (ev.target.id === 'mk-q') { MKT.q = ev.target.value; paintFix2('mk'); }
    if (ev.target.id === 'cmp-q') { CMP.q = ev.target.value; paintFix2('cmplist'); }
    if (ev.target.id === 'nf-q') { NFS.q = ev.target.value; nfApply(); return; }
    if (ev.target.id === 'ps-q') { PST.q = ev.target.value; const b = R.getElementById('ps-table-wrap'); if (b && LASTA && PST.data) b.innerHTML = psTable(LASTA); }
  });
  out.addEventListener('click', (ev) => {
    const t = ev.target; if (!t.closest || t.closest('a.pn')) return;
    const pm = t.closest('[data-psmode]'); if (pm) { if (PST.busy) return; PST.mode = pm.dataset.psmode; PST.data = null; PST.loaded = []; PST.errors = []; PST.failedCodes = []; PST.updated = 0; PST.error = ''; paintRot(); loadPlayerStats(false); return; }
    const pg = t.closest('[data-psg]'); if (pg) { PST.grp = pg.dataset.psg; R.querySelectorAll('[data-psg]').forEach((b) => b.classList.toggle('on', psgOn(b.dataset.psg))); const w = R.querySelector('#s-fix .ps-scroll'); if (w) w.dataset.g = PST.grp; pgAll(); return; }
    const pk = t.closest('[data-pck]'); if (pk) { ev.preventDefault(); const id = +pk.dataset.pck; if (SELP.has(id)) SELP.delete(id); else if (SELP.size < 10) SELP.add(id); else toast('Up to 10 players', 'Head to head compares at most 10.'); pk.classList.toggle('on', SELP.has(id)); pk.setAttribute('aria-pressed', SELP.has(id)); const tr = pk.closest('tr'); if (tr) tr.classList.toggle('sel', SELP.has(id)); R.querySelectorAll('[data-selbar]').forEach((b) => { b.outerHTML = selBar(b.dataset.selbar); }); return; }
    const so = t.closest('[data-selonly]'); if (so) { if (so.dataset.selonly === 'ps') PST.onlySel = !PST.onlySel; else MKT.onlySel = !MKT.onlySel; paintRot(); return; }
    const sc = t.closest('[data-selclr]'); if (sc) { SELP.clear(); PST.onlySel = false; MKT.onlySel = false; paintRot(); return; }
    if (t.closest('[data-selcmp]')) { CMP.ids = [...SELP].slice(0, 10); CMP.pick = false; showView('fix', 'h2h'); return; }
    const pp = t.closest('[data-pspos]'); if (pp) { PST.pos = +pp.dataset.pspos; paintRot(); return; }
    const pso = t.closest('[data-psort]'); if (pso) { const k = pso.dataset.psort; if (PST.sort === k) PST.dir = -PST.dir; else { PST.sort = k; PST.dir = -1; } const b = R.getElementById('ps-table-wrap'); if (b && LASTA && PST.data) b.innerHTML = psTable(LASTA); else paintRot(); return; }
    if (t.closest('[data-ps-retry]')) { loadPlayerStats(true); return; }
    const mp = t.closest('[data-mkpos]'); if (mp) { MKT.pos = +mp.dataset.mkpos; paintRot(); return; }
    const mv = t.closest('[data-mkv]'); if (mv) { MKT.view = mv.dataset.mkv; MKT.sort = null; paintRot(); return; }
    const ms = t.closest('[data-mks]'); if (ms) { const k = ms.dataset.mks; if (MKT.sort === k) MKT.dir = -MKT.dir; else { MKT.sort = k; MKT.dir = -1; } paintRot(); return; }
    const ca = t.closest('[data-cmpadd]'); if (ca) { const id = +ca.dataset.cmpadd; if (CMP.ids.includes(id)) CMP.ids = CMP.ids.filter((x) => x !== id); else if (CMP.ids.length < 10) CMP.ids.push(id); else toast('Up to 10 players', 'Remove one to add another.', ''); paintFix2(); return; }
    const cx = t.closest('[data-cmpx]'); if (cx) { CMP.ids = CMP.ids.filter((x) => x !== +cx.dataset.cmpx); paintFix2(); return; }
    const cp = t.closest('[data-cmppos]'); if (cp) { CMP.pos = +cp.dataset.cmppos; paintFix2(); return; }
    const cc = t.closest('[data-cmpc]'); if (cc) { CMP.col = cc.dataset.cmpc; paintFix2(); return; }
    const cm = t.closest('[data-cmpm]'); if (cm) { CMP.mode = cm.dataset.cmpm; paintFix2(); return; }
    if (t.closest('[data-cmpclear]')) { CMP.ids = []; paintFix2(); return; }
    if (t.closest('[data-cmppick]')) { CMP.pick = !CMP.pick; paintFix2(); if (!CMP.pick) { const w = R.querySelector('.cmpw'); if (w) w.scrollIntoView({ block: 'nearest' }); } return; }
    if (t.closest('[data-cmpswap]')) { cmpFromSwaps(); paintFix2(); return; }
  });

  // ---------- Full player page (opened from the transfer planner, Market and Head to head) ----------
  async function openPlayerPage(pid) {
    const A = LAST; if (!A || !A.E[pid]) return;
    const e = A.E[pid], T = A.T, g0 = A.startGw, et = e.element_type;
    const pg = $('#ppage'), body = $('#ppbody');
    pg.hidden = false; drawer.hidden = true;
    body.innerHTML = `<div class="pp2"><div class="pph${flagUrl(e) ? ' fl' : ''}${REGION[e.region] && REGION[e.region][0] === 'eg' ? ' egy' : ''}"${flagSt(e)}>${flagUrl(e) ? `<i class="pflag l" aria-hidden="true"></i><i class="pflag r" aria-hidden="true"></i><i class="pflag c wv" aria-hidden="true">${FLAGW}</i><i class="pflag t" aria-hidden="true"></i>` : ''}<div class="ppt"><h1>${esc(e.web_name)}</h1><span class="ppfull">Loading…</span></div><button type="button" class="x ppx" data-ppclose="1" aria-label="Close">×</button></div></div>`;
    let sum = null; try { sum = await J(`/api/element-summary/${pid}/`); } catch (er) {}
    if (pg.hidden) return;
    const H = sum ? sum.history : [];
    const byRound = {}; H.forEach((h) => { const r = byRound[h.round] || (byRound[h.round] = { round: h.round, pts: 0, mins: 0, opp: [] }); r.pts += h.total_points; r.mins += h.minutes; r.opp.push(`${T[h.opponent_team].short_name} (${h.was_home ? 'H' : 'A'})`); });
    const rounds = Object.values(byRound).sort((a, b) => a.round - b.round);
    const played = H.filter((h) => h.minutes > 0);
    const matches = played.length, mins = e.minutes;
    const last5 = played.slice(-5); const form5 = last5.length ? last5.reduce((a, h) => a + h.total_points, 0) / last5.length : 0;
    const Pg = (g) => (A.GWS.includes(g) ? A.P(e, g) : 0);
    const oppTxt = (g) => (A.fxBy[e.team + '-' + g] || []).map((f) => `${esc(T[f.o].name)} (${f.home ? 'H' : 'A'})`).join(' + ') || 'no match';
    const next3 = Pg(g0) + Pg(g0 + 1) + Pg(g0 + 2), s6 = S6of(A, e, g0);
    const rd = A.radar(e), ovr = rd.ovr;
    // points chart: last 3 banked, next 6 projected
    const past = rounds.slice(-3), fut = A.GWS.filter((g) => g >= g0).slice(0, 6);
    const maxV = Math.max(4, ...past.map((r) => r.pts), ...fut.map(Pg));
    const bar = (v, cls, top, chip, gl, sub) => `<div class="pbar ${cls}"><b>${top}</b><div class="pbw"><i style="height:${Math.max(4, Math.round((Math.max(0, v) / maxV) * 100))}%"></i></div>${chip}<small>${gl}</small><small class="m">${sub}</small></div>`;
    const bars = past.map((r) => bar(r.pts, 'bank', r.pts, `<span class="fxc past">${r.opp.join(' ')}</span>`, 'GW' + r.round, r.mins + '′')).join('') + fut.map((g) => bar(Pg(g), 'proj', f1(Pg(g)), fxCell(A, e.team, g), 'GW' + g, 'proj')).join('');
    // radar
    const RX = 100, RY = 92, RAD = 70; const ax = [[0, -1, rd.fin], [1, 0, rd.cre], [0, 1, rd.def], [-1, 0, rd.min]];
    const ring = (k) => ax.map(([x, y]) => `${RX + x * RAD * k},${RY + y * RAD * k}`).join(' ');
    const poly = ax.map(([x, y, v]) => `${RX + (x * RAD * v) / 100},${RY + (y * RAD * v) / 100}`).join(' ');
    const radar = `<svg class="radar" viewBox="0 0 200 184" role="img" aria-label="Fantasy rating ${ovr}"><polygon points="${ring(1)}" class="rg"/><polygon points="${ring(0.66)}" class="rg"/><polygon points="${ring(0.33)}" class="rg"/><polygon points="${poly}" class="rp"/>${ax.map(([x, y, v]) => `<circle cx="${RX + (x * RAD * v) / 100}" cy="${RY + (y * RAD * v) / 100}" r="2.6" class="rd"/>`).join('')}<text x="${RX}" y="${RY + 6}" class="rc">${ovr}</text></svg>`;
    const rLab = (l, v, pos) => `<span class="rl ${pos}"><small>${l}</small><b class="${v >= 70 ? 'up' : v < 40 ? 'dn' : ''}">${v}</b></span>`;
    // transfer signal
    const pool = BS.elements.filter((x) => x.element_type === et && x.minutes >= 270 && x.status !== 'u');
    const s6s = pool.map((x) => S6of(A, x, g0)).sort((a, b) => a - b);
    const pc = s6s.length ? Math.round((s6s.filter((v) => v < s6).length / s6s.length) * 100) : 50;
    const sig = e.status === 'i' || e.status === 's' || e.status === 'u' ? ['Sell', 'sell'] : pc >= 92 ? ['Strong Buy', 'sbuy'] : pc >= 72 ? ['Buy', 'buy'] : pc >= 40 ? ['Hold', 'hold'] : ['Sell', 'sell'];
    const cheaper = pool.filter((x) => x.id !== e.id && x.now_cost < e.now_cost && x.now_cost >= e.now_cost - 15).map((x) => ({ x, v: S6of(A, x, g0) })).sort((a, b) => b.v - a.v)[0];
    const pricier = pool.filter((x) => x.id !== e.id && x.now_cost > e.now_cost && x.now_cost <= e.now_cost + 15).map((x) => ({ x, v: S6of(A, x, g0) })).sort((a, b) => b.v - a.v)[0];
    const reasons = [];
    if (cheaper) { const d = s6 - cheaper.v, dm = e.now_cost - cheaper.x.now_cost; reasons.push(d >= 0 ? ['good', 'Worth the extra money', `${f1(d)} more points than ${esc(cheaper.x.web_name)} for ${money(dm)} more over the next 6 gameweeks.`] : ['bad', 'A cheaper player projects more', `${esc(cheaper.x.web_name)} projects ${f1(-d)} more points for ${money(dm)} less over the next 6 gameweeks.`]); }
    if (pricier && pricier.v > s6 + 3) reasons.push(['warn', 'Upgrade option', `${esc(pricier.x.web_name)} projects ${f1(pricier.v - s6)} more points for ${money(pricier.x.now_cost - e.now_cost)} more.`]);
    const topAll = BS.elements.filter((x) => x.id !== e.id && x.minutes > 0).map((x) => ({ x, v: S6of(A, x, g0) })).sort((a, b) => b.v - a.v)[0];
    if (topAll) { const gap = topAll.v - s6; const topW = fut.filter((g) => BS.elements.every((x) => x.id === e.id || !A.GWS.includes(g) || A.P(x, g) <= Pg(g) + 0.3)); reasons.push(gap <= 0 ? ['good', 'Top captain pick', `Highest projection of any player over the next 6 gameweeks.`] : gap < 3 ? ['good', 'Viable captain', `${f1(gap)} points behind ${esc(topAll.x.web_name)} over the next 6 gameweeks${topW.length ? `; highest projection in ${topW.map((g) => 'GW' + g).join(', ')}` : ''}.`] : ['muted', 'Not a captain pick', `${f1(gap)} points behind ${esc(topAll.x.web_name)} over the next 6 gameweeks.`]); }
    if (e.news) reasons.unshift(['bad', 'Availability', esc(e.news)]);
    const tf = ((A.tb[e.team] || {}).form || []).slice(-5);
    // similar players: same position, closest rating, then price
    const similar = pool.filter((x) => x.id !== e.id).map((x) => ({ x, r: rtg(A, x) })).sort((a, b) => Math.abs(a.r - ovr) + Math.abs(a.x.now_cost - e.now_cost) / 10 - (Math.abs(b.r - ovr) + Math.abs(b.x.now_cost - e.now_cost) / 10)).slice(0, 5).sort((a, b) => b.r - a.r);
    const spT = (v) => (v === 1 ? '1st choice' : v === 2 ? '2nd choice' : v === 3 ? '3rd choice' : v ? v + 'th choice' : 'No');
    const thr = et === 2 ? 10 : 12; const dcm = et === 1 ? 0 : H.filter((h) => (+h.defensive_contribution || 0) >= thr).length;
    const ps = pastOf(e).filter(Boolean); const n = A.NM[pid];
    const owned = A.sq.some((s) => s.e.id === pid);
    const kc = JST[T[e.team].short_name] || ['#33507e', '#1a2a45'];
    const chg = (v, l) => `<span class="${v > 0 ? 'up' : v < 0 ? 'dn' : 'muted'}">${v > 0 ? '▲' : v < 0 ? '▼' : '•'}${money(Math.abs(v))} ${l}</span>`;
    const stat = (l, v) => `<div><b>${v}</b><small>${l}</small></div>`;
    body.innerHTML = `<div class="pp2">
<div class="pph${flagUrl(e) ? ' fl' : ''}${REGION[e.region] && REGION[e.region][0] === 'eg' ? ' egy' : ''}" style="--k1:${kc[0]};--k2:${kc[1]}${flagUrl(e) ? `;--flag:url('${flagUrl(e)}');--flagb:url('${flagPng(REGION[e.region][0])}')` : ''}">${flagUrl(e) ? `<i class="pflag l" aria-hidden="true"></i><i class="pflag r" aria-hidden="true"></i><i class="pflag c wv" aria-hidden="true">${FLAGW}</i><i class="pflag t" aria-hidden="true"></i>` : ''}
<div class="ppimg">${kitImg(T[e.team].short_name, et === 1, 110, 'ppk')}<img class="ppface" src="https://resources.premierleague.com/premierleague25/photos/players/110x140/${e.code}.png" data-alt="https://resources.premierleague.com/premierleague/photos/players/110x140/p${e.code}.png" alt="${esc(e.web_name)}" loading="lazy" referrerpolicy="no-referrer"></div>
<div class="ppt"><small>${posB(et)} ${esc(T[e.team].name)}${isNewSigning(e) ? ' · <span class="newpill">New signing</span>' : ''}</small><h1>${esc(e.web_name)}</h1><span class="ppfull">${esc(e.first_name)} ${esc(e.second_name)}${country(e) ? ' · ' + esc(country(e)) : ''}</span>
<div class="ppchips"><b class="ppp">${money(e.now_cost)}</b>${chg(e.cost_change_event, 'wk')}${chg(e.cost_change_start, 'season')}<span class="sigchip ${sig[1]}">${sig[0]}</span></div>
${e.status === 'a' ? '' : `<span class="ppst2"><i class="dot warn"></i>${esc(e.news || 'Flagged')}</span>`}</div>
<button type="button" class="x ppx" data-ppclose="1" aria-label="Close">×</button></div>
<div class="ppk4"><div><small>Next GW</small><b class="acc">${f1(Pg(g0))}</b><span>${fxCell(A, e.team, g0)}</span></div><div><small>Next 3</small><b class="acc">${f1(next3)}</b><span>pts</span></div><div><small>Rating</small><b>${ovr}</b><span>${pc}th pct</span></div><div><small>Owned</small><b>${e.selected_by_percent}%</b><span>${owned ? 'in your team' : 'of managers'}</span></div></div>
<div class="pchart"><div class="pch"><b>Points</b><small class="muted">last ${past.length} · next ${fut.length} projected</small></div><div class="pbars">${bars}</div></div>
<div class="ppr2"><div class="radw">${radar}${rLab('Finisher', rd.fin, 't')}${rLab('Playmaker', rd.cre, 'r')}${rLab(et <= 2 ? 'Defender' : 'Defending', rd.def, 'b')}${rLab('Game time', rd.min, 'l')}</div>
<div class="ppsg">${stat('Points', e.total_points)}${stat('Per game', e.points_per_game)}${stat('Form', f1(form5))}${et === 1 ? stat('Saves', e.saves) : stat('Goals', e.goals_scored)}${et === 1 ? stat('Clean sh.', e.clean_sheets) : stat('Assists', e.assists)}${et <= 2 ? (et === 1 ? stat('Conceded', e.goals_conceded) : stat('Clean sh.', e.clean_sheets)) : stat('xGI/90', (+e.expected_goal_involvements_per_90 || 0).toFixed(2))}${stat('Mins/game', matches ? Math.round(mins / matches) : '–')}${stat('Pens', spT(e.penalties_order).replace(' choice', ''))}${stat('Starts', e.starts || matches)}</div></div>
<div class="ppacts"><button class="mbtn" type="button" data-addp="${pid}">✎ ${owned ? 'Plan around him' : 'Bring in'}</button><button class="mbtn ghost" type="button" data-cmpwith="${pid}">⇄ Compare</button><a class="mbtn ghost" href="${plUrl(e)}" target="_blank" rel="noopener">↗ PL page</a></div>
<details class="ppmore"><summary>Why ${sig[0].toLowerCase()} · set pieces · similar players${n && n.hits.length ? ' · news' : ''}${ps.length ? ' · past seasons' : ''}</summary>
<p class="ppwhy">${esc(e.web_name)} is in the ${pc}th percentile of ${POSN[et].toLowerCase()}s for projected points over the next ${fut.length} gameweeks (${f1(s6)} pts).</p>
${reasons.map(([c, h, tx]) => `<div class="why ${c}"><b>${h}</b><small>${tx}</small></div>`).join('')}
<div class="sprows"><div><span>Penalties</span><b>${spT(e.penalties_order)}</b></div><div><span>Corners</span><b>${spT(e.corners_and_indirect_freekicks_order)}</b></div><div><span>Free kicks</span><b>${spT(e.direct_freekicks_order)}</b></div></div>
${similar.length ? `<h3 class="psh">Similar players</h3><div class="simg">${similar.map(({ x, r }) => `<a class="simc pn" href="#" data-pid="${x.id}"><b>${esc(x.web_name)}</b><small class="muted">${esc(T[x.team].short_name)} · ${money(x.now_cost)}</small><span><b class="acc">${r}</b></span></a>`).join('')}</div>` : ''}
${n && n.hits.length ? `<h3 class="psh">In the news</h3>${n.hits.slice(0, 4).map((it) => `<div class="alt" style="margin-bottom:6px"><a href="${esc(it.link)}" target="_blank" rel="noopener">${esc(it.title)}</a> <small class="muted">${esc(it.src)}</small></div>`).join('')}` : ''}
${ps.length ? `<h3 class="psh">Previous seasons</h3><div class="tw"><table><thead><tr><th>Season</th><th class="n">Pts</th><th class="n">Mins</th><th class="n">G</th><th class="n">A</th><th class="n">Pts/90</th></tr></thead><tbody>${ps.map((q) => `<tr><td>${q.k.replace('-', '/')}</td><td class="n"><b>${q.p}</b></td><td class="n">${q.m}</td><td class="n">${q.g}</td><td class="n">${q.a}</td><td class="n">${q.m ? (q.p / (q.m / 90)).toFixed(1) : '–'}</td></tr>`).join('')}</tbody></table></div>` : ''}
</details></div>`;
    body.scrollTop = 0; pg.scrollTop = 0;
  }
  function closePlayerPage() { const pg = $('#ppage'); if (pg) pg.hidden = true; }
  $('#ppage').addEventListener('click', (ev) => {
    if (ev.target === ev.currentTarget) { closePlayerPage(); return; }
    const t = ev.target; if (!t.closest) return;
    if (t.closest('[data-ppclose]')) { closePlayerPage(); return; }
    const a = t.closest('a.pn'); if (a) { ev.preventDefault(); openPlayerPage(+a.dataset.pid); return; }
    const cw = t.closest('[data-cmpwith]'); if (cw) { const id = +cw.dataset.cmpwith; if (!CMP.ids.includes(id)) CMP.ids = [id, ...CMP.ids].slice(0, 10); closePlayerPage(); FIXTAB = 'h2h'; showView('fix', 'h2h'); paintRot(); return; }
    const go = t.closest('[data-ppgo]'); if (go) { closePlayerPage(); if (go.dataset.ppgo === 'market') { FIXTAB = 'market'; showView('fix', 'market'); paintRot(); } else showView('team', 'pitch'); return; }
    if (t.closest('[data-addp], [data-act]')) { onAct(ev); closePlayerPage(); }
  });
  document.addEventListener('keydown', (ev) => { if (ev.key === 'Escape') { const pg = R.getElementById('ppage'); if (pg && !pg.hidden) { ev.stopImmediatePropagation(); closePlayerPage(); } } }, true);

  // ---------- v3.3: choose how much information the player cards show (remembered) ----------
  const CI_KEY = 'fplAnalystCardInfo';
  const CI_PRESETS = { full: { price: true, fx: 3, badge: true, star: true, code: true }, compact: { price: true, fx: 1, badge: true, star: false, code: true }, minimal: { price: false, fx: 0, badge: false, star: false, code: true } };
  // v3.11: official FPL kits are the default player art ('real'); the choice is stored as art2 so older saved settings don't override it
  let CI = Object.assign({ open: false, art: 'real' }, CI_PRESETS.full);
  const CI_FIXED = () => Object.assign(CI, CI_PRESETS.full, { open: false, art: 'real' });
  try { const sv = JSON.parse(localStorage.getItem(CI_KEY) || '{}'); ['price', 'badge', 'star', 'code'].forEach((k) => { if (typeof sv[k] === 'boolean') CI[k] = sv[k]; }); if ([0, 1, 2, 3].includes(sv.fx)) CI.fx = sv.fx; if (['real', 'kit', 'player'].includes(sv.art2)) CI.art = sv.art2; } catch (e) {}
  const saveCI = () => { try { localStorage.setItem(CI_KEY, JSON.stringify({ price: CI.price, fx: CI.fx, badge: CI.badge, star: CI.star, code: CI.code, art2: CI.art })); } catch (e) {} };
  const ciPreset = () => Object.keys(CI_PRESETS).find((k) => { const q = CI_PRESETS[k]; return q.price === CI.price && q.fx === CI.fx && q.badge === CI.badge && q.star === CI.star && q.code === CI.code; }) || '';
  const CI_ITEMS = [['price', 'Price'], ['badge', 'Penalty / set-piece'], ['star', 'In-form star'], ['code', 'Club code']];
  // An inline bar (it pushes the pitch down instead of floating over it) with a live preview card
  function infoBar() {
    let prev = '';
    try {
      const x = PLAN.cap || (PLAN.line && PLAN.line[0]);
      if (x) prev = `<div class="iprev" aria-hidden="true"><div class="chip pc">${jersey(PLAN.A, x.e, { role: 'C', val: `£${(x.e.now_cost / 10).toFixed(1)}m`, sp: spB(x.e), sub: haStrip(PLAN.A, x.e.team, 3, PLAN.gw), strip: 1 })}</div><small>Preview</small></div>`;
    } catch (e) {}
    const pills = (arr, attr) => arr.map(([k, l]) => `<button type="button" class="ipill" ${attr}="${k}">${l}</button>`).join('');
    return `<div class="infobar" id="pl-infopop" hidden>${prev}<div class="ictl">
<div class="ig"><span>Player art</span><div class="irow">${pills([['real', 'FPL kit'], ['kit', 'Drawn shirt'], ['player', 'Illustrated player']], 'data-ciart')}</div></div>
<div class="ig"><span>Quick style</span><div class="irow">${pills([['full', 'Full'], ['compact', 'Compact'], ['minimal', 'Minimal']], 'data-cipre')}</div></div>
<div class="ig"><span>Show on each player</span><div class="irow">${pills(CI_ITEMS, 'data-ci')}</div></div>
<div class="ig"><span>Next fixtures</span><div class="irow">${pills([[0, 'Off'], [1, '1'], [2, '2'], [3, '3']], 'data-cifx')}</div></div>
</div><button class="ix" type="button" id="pl-infox">Done</button></div>`;
  }
  function applyCI() {
    const box = R.getElementById('planner'); if (!box) return;
    box.classList.toggle('ci-noprice', !CI.price); box.classList.toggle('ci-nofx', CI.fx === 0); box.classList.toggle('ci-nobadge', !CI.badge); box.classList.toggle('ci-nostar', !CI.star); box.classList.toggle('ci-nocode', !CI.code);
    box.dataset.fx = CI.fx; box.classList.toggle('art-player', CI.art === 'player');
    const bar = box.querySelector('#pl-infopop');
    if (bar) {
      bar.hidden = !CI.open;
      bar.querySelectorAll('[data-ci]').forEach((b) => { const on = !!CI[b.dataset.ci]; b.classList.toggle('on', on); b.setAttribute('aria-pressed', String(on)); });
      bar.querySelectorAll('[data-cifx]').forEach((b) => b.classList.toggle('on', +b.dataset.cifx === CI.fx));
      bar.querySelectorAll('[data-ciart]').forEach((b) => b.classList.toggle('on', b.dataset.ciart === CI.art));
      const cp = ciPreset(); bar.querySelectorAll('[data-cipre]').forEach((b) => b.classList.toggle('on', b.dataset.cipre === cp));
    }
    const bt = box.querySelector('#pl-info'); if (bt) { bt.setAttribute('aria-expanded', String(CI.open)); bt.classList.toggle('on', CI.open); }
  }
  out.addEventListener('click', (ev) => {
    const t = ev.target; if (!t.closest) return;
    if (t.closest('#pl-info')) { CI.open = !CI.open; applyCI(); requestAnimationFrame(applyPV); return; }
    if (t.closest('#pl-infox')) { CI.open = false; applyCI(); return; }
    const tg = t.closest('[data-ci]'); if (tg) { CI[tg.dataset.ci] = !CI[tg.dataset.ci]; saveCI(); applyCI(); return; }
    const fx = t.closest('[data-cifx]'); if (fx) { CI.fx = +fx.dataset.cifx; saveCI(); applyCI(); return; }
    const cb = t.closest('[data-cal]'); if (cb) { try { localStorage.setItem('fplAnalystCalib', cb.dataset.cal); } catch (er) {} const card = R.getElementById('acc-card'); if (card) card.innerHTML = accHtml(); toast(cb.dataset.cal === 'on' ? 'Tune-up on' : 'Tune-up off', 'Projections update on the next refresh (⟳).', ''); return; }
    if (t.closest('#acc-run')) { const card = R.getElementById('acc-card'); const b = t.closest('#acc-run'); b.disabled = true; b.textContent = 'Testing…';
      const pr = R.getElementById('acc-prog') || (card.insertAdjacentHTML('beforeend', '<div id="acc-prog"></div>'), R.getElementById('acc-prog'));
      runAccuracy((p) => { pr.innerHTML = `<div class="accbar"><i style="width:${p}%"></i></div><small class="muted">${p < 70 ? 'Reading past gameweeks…' : 'Projecting each week…'} ${p}%</small>`; })
        .then(() => { card.innerHTML = accHtml(); }).catch((er) => { pr.innerHTML = `<p class="err">${esc(er.message || 'The test could not run.')}</p>`; b.disabled = false; b.textContent = 'Run the test'; });
      return; }
    const ca = t.closest('[data-ciart]'); if (ca) { CI.art = ca.dataset.ciart; saveCI(); renderPlanner(); return; }
    const pr = t.closest('[data-cipre]'); if (pr) { Object.assign(CI, CI_PRESETS[pr.dataset.cipre]); saveCI(); applyCI(); }
  });
  R.addEventListener('keydown', (ev) => { if (ev.key === 'Escape' && CI.open) { CI.open = false; applyCI(); } });

  // ---------- v3.4: open any manager (mini-league row) and fill the Team ID ----------
  async function openTeam(id, name) {
    const inp = $('#tid'); if (inp) inp.value = String(id);
    toast(name ? `Opening ${name}` : 'Opening your team', `Team ID ${id}`, '');
    await run(id); showView('home');
  }
  out.addEventListener('click', (ev) => {
    const t = ev.target; if (!t.closest || t.closest('a')) return;
    const tr = t.closest('tr[data-entry]'); if (tr) { openTeam(+tr.dataset.entry, tr.dataset.tname); return; }
    if (t.closest('[data-back]') && MYID) openTeam(MYID, MYNAME || 'your team');
  });
  out.addEventListener('keydown', (ev) => { if (ev.key !== 'Enter' && ev.key !== ' ') return; const tr = ev.target.closest && ev.target.closest('tr[data-entry]'); if (tr) { ev.preventDefault(); openTeam(+tr.dataset.entry, tr.dataset.tname); } });

  // ---------- v2.6: planner view (player size, split position), remembered between visits ----------
  const PV_KEY = 'fplAnalystPlanView';
  let PV = { auto: true, scale: 1, lw: null };
  try { const sv = JSON.parse(localStorage.getItem(PV_KEY) || '{}'); if (sv && typeof sv === 'object') { if (typeof sv.auto === 'boolean') PV.auto = sv.auto; if (+sv.scale >= .6 && +sv.scale <= 1.6) PV.scale = +sv.scale; if (+sv.lw > 0) PV.lw = +sv.lw; } } catch (e) {}
  const savePV = () => { try { localStorage.setItem(PV_KEY, JSON.stringify(PV)); } catch (e) {} };
  let PVRO = null, PVEL = null, PVBUSY = false;
  // v3.29: on wide screens the Targets / Differentials / Chips panel is exactly as tall as the pitch column
  function fitSide(box) {
    const grid = box.querySelector('.plgrid'), left = box.querySelector('.plleft'), body = box.querySelector('.plside .ptbody');
    if (!grid || !left || !body) return;
    const wide = grid.clientWidth > 860 && getComputedStyle(grid).gridTemplateColumns.split(' ').length > 1;
    const all = box.dataset.all === PLAN.tab || PLAN.tab === 'chips';
    // v3.53: the Chips panel (Wildcard builder, chip notes) scrolls inside the side panel instead of stretching the page
    const scr = PLAN.tab === 'chips' || PLAN.tab === 'do';
    box.classList.toggle('sidefit', wide && (!all || scr)); box.classList.toggle('sidescroll', scr);
    if (wide && scr) { const cs0 = left.querySelectorAll('.chip.pc[data-card]'), l0 = cs0[cs0.length - 1]; const bt = l0 ? l0.getBoundingClientRect().bottom + 8 : left.getBoundingClientRect().bottom; box.style.setProperty('--plh', Math.max(360, Math.round(bt - box.querySelector('.plside').getBoundingClientRect().top)) + 'px'); return; }
    if (!wide && scr) { box.style.removeProperty('--plh'); return; }
    if (!wide || all) { box.style.removeProperty('--plh'); body.querySelectorAll('.stack > [hidden]').forEach((c) => (c.hidden = false)); const m = body.querySelector('.tmore'); if (m) m.remove(); return; }
    const cs = left.querySelectorAll('.chip.pc[data-card]'), lc = cs[cs.length - 1];
    const benchBox = lc ? (lc.closest('.bench, .bnch, .benchrow') || lc.parentElement) : null;
    const bottom = benchBox ? Math.max(benchBox.getBoundingClientRect().bottom, lc.getBoundingClientRect().bottom) : left.getBoundingClientRect().bottom;
    box.style.setProperty('--plh', Math.max(320, Math.round(bottom - box.querySelector('.plside').getBoundingClientRect().top)) + 'px');
    const cards = [...body.querySelectorAll('.stack > *')]; cards.forEach((c) => (c.hidden = false));
    let m = body.querySelector('.tmore'); if (m) m.remove();
    const lim = body.getBoundingClientRect().bottom - 12; let n = 0;
    cards.forEach((c) => { if (n || c.getBoundingClientRect().bottom > lim - 40) { c.hidden = true; n++; } });
    if (n) { m = document.createElement('button'); m.type = 'button'; m.className = 'tmore'; m.dataset.more = PLAN.tab; m.textContent = `Show ${n} more`; body.appendChild(m); }
  }
  out.addEventListener('click', (ev) => { const b = ev.target.closest && ev.target.closest('.tmore'); if (!b) return; const box = R.getElementById('planner'); box.dataset.all = b.dataset.more; applyPV(); });
  function applyPV() {
    const box = R.getElementById('planner'); if (!box) return;
    if (box !== PVEL) { if (PVRO) PVRO.disconnect(); PVEL = box; if (typeof ResizeObserver === 'function') { PVRO = new ResizeObserver(() => { if (PVBUSY) return; PVBUSY = true; requestAnimationFrame(() => { PVBUSY = false; applyPV(); }); }); PVRO.observe(box); } }
    const grid = box.querySelector('.plgrid'), pitch = box.querySelector('.pitch');
    if (!grid || !pitch || !pitch.clientWidth) return;
    // split position: keep both columns usable
    if (PV.lw && grid.clientWidth > 860) { const lw = Math.max(340, Math.min(PV.lw, grid.clientWidth - 12 - 300)); box.style.setProperty('--lw', lw + 'px'); } else box.style.removeProperty('--lw');
    // size: auto-fit so the widest row (up to 5 players) fills the pitch evenly, or the manual slider value
    const widest = Math.max(3, ...[...pitch.querySelectorAll('.row')].map((r) => r.children.length));
    const avail = out.clientHeight - (pitch.getBoundingClientRect().top - out.getBoundingClientRect().top) - 24;
    const fitW = (Math.min(pitch.clientWidth, (box.querySelector('.plleft') || pitch).clientWidth) - 16) / (widest * 96), fitH = avail > 200 ? avail / 690 : 1.5;
    const fit = Math.round(Math.max(.6, Math.min(1.35, fitW, fitH)) * 100) / 100;
    let sc = fit;
    box.style.setProperty('--ps', sc); box.style.setProperty('--pb', Math.round(sc * .88 * 100) / 100);
    // v3.28: measure pitch + bench and shrink until the last bench card sits above the bottom bar (no scrolling to drag)
    if (PV.auto) for (let k = 0; k < 3; k++) {
      const cs = box.querySelectorAll('.chip.pc[data-card]'); if (!cs.length) break;
      const orr = out.getBoundingClientRect(), nb = (R.getElementById('nav') || out).getBoundingClientRect();
      const limit = (nb.top > orr.top + 120 && nb.top <= orr.bottom + 1 ? nb.top : orr.bottom) - 8;
      const pTop = pitch.getBoundingClientRect().top + out.scrollTop; // position with the page scrolled to the top
      const need = cs[cs.length - 1].getBoundingClientRect().bottom - pitch.getBoundingClientRect().top, room = limit - pTop;
      if (need <= room + 2 || need <= 0 || room < 150) break;
      sc = Math.max(.42, Math.round(sc * Math.max(.5, room / need) * 100) / 100); box.style.setProperty('--ps', sc); box.style.setProperty('--pb', Math.round(sc * .88 * 100) / 100);
      if (sc <= .42) break;
    }
    fitSide(box);
    const z = box.querySelector('#pl-zoom'), o = box.querySelector('#pl-zoomv'), f = box.querySelector('#pl-fit');
    if (z) z.value = Math.round(sc * 100); if (o) o.textContent = Math.round(sc * 100) + '%'; if (f) f.classList.toggle('on', PV.auto);
  }
  out.addEventListener('input', (ev) => { if (ev.target.id === 'pl-zoom') { PV.auto = false; PV.scale = Math.max(.6, Math.min(1.6, +ev.target.value / 100)); applyPV(); savePV(); } });
  out.addEventListener('click', (ev) => { if (ev.target.closest && ev.target.closest('#pl-fit')) { PV.auto = true; applyPV(); savePV(); } });
  out.addEventListener('dblclick', (ev) => { if (ev.target.closest && ev.target.closest('#pl-split')) { PV.lw = null; applyPV(); savePV(); } });
  out.addEventListener('pointerdown', (ev) => {
    const sp = ev.target.closest && ev.target.closest('#pl-split'); if (!sp) return;
    ev.preventDefault(); const left = sp.parentElement.getBoundingClientRect().left;
    try { sp.setPointerCapture(ev.pointerId); } catch (e) {}
    sp.classList.add('drag');
    const mv = (e) => { PV.lw = Math.round(e.clientX - left - 6); applyPV(); };
    const up = () => { sp.classList.remove('drag'); sp.removeEventListener('pointermove', mv); sp.removeEventListener('pointerup', up); sp.removeEventListener('pointercancel', up); savePV(); };
    sp.addEventListener('pointermove', mv); sp.addEventListener('pointerup', up); sp.addEventListener('pointercancel', up);
  });
  out.addEventListener('keydown', (ev) => {
    if (ev.target.id !== 'pl-split') return;
    const k = ev.key; if (k !== 'ArrowLeft' && k !== 'ArrowRight' && k !== 'Home') return;
    ev.preventDefault();
    if (k === 'Home') PV.lw = null; else { const cur = PV.lw || R.querySelector('#planner .plleft').getBoundingClientRect().width; PV.lw = Math.round(cur + (k === 'ArrowRight' ? 24 : -24)); }
    applyPV(); savePV();
  });

  function renderPlanner() {
    const box = R.getElementById('planner'); if (!box || !PLAN) return;
    const A = PLAN.A, g0 = PLAN.gw, P = A.P, T = A.T;
    if (g0 < A.startGw) { box.innerHTML = plannerNav() + (PLAN.hist ? histHtml(A, g0, PLAN.hist) : '<p class="muted">Loading gameweek…</p>'); tidyKpis(box); return; }
    commit(); dropWc();
    const lastG = A.GWS[A.GWS.length - 1], kOff = g0 - A.startGw;
    const nm = (e) => `<a class="pn" href="#" data-pid="${e.id}">${esc(e.web_name)}</a>`;
    const SN = (e) => { let s = 0; for (let k = 0; k < 5; k++) s += P(e, g0 + k); return s; };
    const sqN = (list) => { let s = 0; for (let k = 0; k < 5 && g0 + k <= lastG; k++) { const b = A.bestXIof(list, g0 + k); s += b.sum + b.cap; } return s; };
    const bank = planBank();
    const free = PLAN.chip === 'wildcard' || PLAN.chip === 'freehit';
    const nT = PLAN.swaps.length + (free ? PLAN.chipIn.length : 0), hits = free ? 0 : Math.max(0, nT - PLAN.ft0) * 4;
    const new1 = planScore(), d1 = new1 - PLAN.base - hits;
    const draft = PLAN.line;
    const bestNow = (() => { const b = A.bestXIof(draft, g0); return b.sum + b.cap * (PLAN.chip === '3xc' ? 2 : 1) + (PLAN.chip === 'bboost' ? b.benchSum : 0); })();
    const new5 = sqN(draft), base5 = sqN(A.sq), d5 = new5 - base5 - hits;
    const clubs = planClubs();
    const warns = [];
    if (bank < 0) warns.push(`Over budget by ${money(-bank)}.`);
    Object.entries(clubs).filter(([, n]) => n > 3).forEach(([t, n]) => warns.push(`${n} players from ${esc(T[t].name)} (the limit is 3).`));
    const selX = PLAN.sel != null ? byId(PLAN.sel) : null;
    const okSet = new Set(selX ? partners(selX) : []);
    const wcOpen = PLAN.wc && PLAN.wc.opts && PLAN.wc.g === g0 && PLAN.chip === PLAN.wc.chip && PLAN.tab === 'chips';
    const chip = (x) => {
      const role = '';
      const jr = PLAN.cap === x ? (PLAN.chip === '3xc' ? '3×' : 'C') : PLAN.vc === x ? 'V' : '';
      const cls = [PLAN.swaps.some((s) => s.i === x) || PLAN.chipIn.includes(x.e) ? 'new' : '', selX === x ? 'sel' : '', okSet.has(x) ? 'okw' : '', selX && !okSet.has(x) && selX !== x ? 'dim' : '', x.e.status !== 'a' ? 'flag' : ''].join(' ');
      return `<div class="chip pc ${cls}" title="${esc(x.e.web_name)}: ${f1(P(x.e, g0))} projected pts in GW${g0}" data-card="${x.e.id}" role="button" tabindex="0" ${okSet.has(x) ? `data-with="${x.e.id}"` : ''}>
${role}${jersey(A, x.e, { role: jr, val: `£${(x.e.now_cost / 10).toFixed(1)}m`, sp: spB(x.e), sub: haStrip(A, x.e.team, 3, g0), strip: 1 })}</div>`; };
    const xi = draft.slice(0, 11), bench = draft.slice(11);
    const row = (t) => xi.filter((x) => x.e.element_type === t).map(chip).join('');
    const formation = [2, 3, 4].map((t) => xi.filter((x) => x.e.element_type === t).length).join('-');
    const sign = (v) => `<b class="${v > 0.05 ? 'up' : v < -0.05 ? 'dn' : ''}">${v > 0.05 ? '▲ +' : v < -0.05 ? '▼ ' : ''}${f1(v)}</b>`;
    let panel = '';
    if (selX) {
      const ps = partners(selX);
      panel = `<div class="swappanel" id="pl-panel"><div class="h"><b>Swap ${esc(selX.e.web_name)} with…</b><button class="x" id="pl-cancel" type="button" style="font-size:13px">Cancel</button></div>
${ps.length ? ps.map((y) => `<button class="cand" type="button" data-with="${y.e.id}"><span class="cn"><b>${esc(y.e.web_name)}</b> <small>${POS[y.e.element_type]} · ${inXI(y) ? 'starting' : 'bench'}</small></span><span class="cv"><b>${f1(P(y.e, g0))}</b><small>GW${g0} xP</small></span></button>`).join('') : '<p class="muted">No swap keeps a legal formation for this player.</p>'}
${inXI(selX) ? `<div class="btnrow2"><button class="try" type="button" data-cap="c:${selX.e.id}">Make captain</button><button class="try" type="button" data-cap="v:${selX.e.id}">Make vice-captain</button></div>` : ''}
<p class="note" style="margin:0">You can also click a highlighted player on the pitch.</p></div>`;
    } else if (PLAN.buying != null && byId(PLAN.buying)) {
      const bx = byId(PLAN.buying);
      panel = `<div class="swappanel" id="pl-panel"><div class="h"><b>Replace ${esc(bx.e.web_name)} in GW${g0}</b><button class="x" id="pl-cancel" type="button" style="font-size:13px">Cancel</button></div>
<p class="note" style="margin:0">${POS[bx.e.element_type]}s you can afford come first, ranked by projected points.</p>
<input id="pl-q" placeholder="Search by name or club…" autocomplete="off" aria-label="Search replacements" value="${esc(PLAN.q)}">
<div class="cands" id="pl-cands">${buyList()}</div></div>`;
    }
    // Targets and differentials are recalculated for this gameweek and this planned squad
    const have = new Set(draft.map((x) => x.e.id)); const xiSet = new Set(xi);
    const usedT = new Set();
    const tgs = draft.map((x) => { const budget = bank + x.sell, mine = SN(x.e);
      const c = BS.elements.filter((c) => c.element_type === x.e.element_type && !have.has(c.id) && c.now_cost <= budget && (c.team === x.e.team || (clubs[c.team] || 0) < 3) && A.avail(c, kOff) > 0.8).map((c) => ({ c, v: SN(c) })).sort((a, b) => b.v - a.v).slice(0, 8);
      return { x, c, mine, w: xiSet.has(x) || A.avail(x.e, kOff) < 0.5 ? 1 : 0.45 }; })
      .sort((a, b) => ((b.c[0] ? b.c[0].v - b.mine : 0) * b.w) - ((a.c[0] ? a.c[0].v - a.mine : 0) * a.w));
    tgs.forEach((t) => { t.c = t.c.filter((c) => !usedT.has(c.c.id)).slice(0, 3); if (t.c[0]) usedT.add(t.c[0].c.id); t.gain = t.c[0] ? t.c[0].v - t.mine : 0; });
    const moveCards = tgs.filter((t) => t.c.length && t.gain > 0.5).sort((a, b) => b.gain * b.w - a.gain * a.w).slice(0, 6).map((t) => { const o = t.x.e, c = t.c[0].c; return `<div class="move mv2 ${t.gain < A.CONV ? 'marginal' : ''}">${t.gain < A.CONV ? `<div class="mgn">Below the ${A.CONV}-pt threshold: usually better to roll</div>` : ''}<div class="h"><span class="mvx2">${shirt(T[o.team].short_name, o.element_type === 1)}<b>${nm(o)}</b><i aria-label="replaced by">→</i>${shirt(T[c.team].short_name, c.element_type === 1)}<b>${nm(c)}</b>${spB(c)}${priceB(c)}${A.isDiff(c) ? '<span class="pill p-diff">Diff</span>' : ''}</span><span class="gain">+${f1(t.gain)}</span></div>
<small class="muted mvm">${T[o.team].short_name} ${money(t.x.sell)} → ${T[c.team].short_name} ${money(c.now_cost)} · form ${c.form} · ${c.selected_by_percent}% owned</small>
<div class="mvf">${fixChips(A, c.team, 5, g0)}<button class="try" type="button" data-try="${o.id}:${c.id}">Transfer</button></div>
${t.c.slice(1).length ? `<div class="alt">Or: ${t.c.slice(1).map((x) => `${nm(x.c)} <small class="muted">${money(x.c.now_cost)}, +${f1(x.v - t.mine)}</small>`).join(' · ')}</div>` : ''}</div>`; }).join('') || '<p class="muted">No transfer improves this squad by more than half a point.</p>';
    const diffCards = A.diffs.filter((d) => !have.has(d.e.id) && A.avail(d.e, kOff) > 0.8).map((d) => ({ e: d.e, v: SN(d.e) })).sort((a, b) => b.v - a.v).slice(0, 10).map((d) => `<div class="move diffc"><div class="h"><span class="who">${shirt(T[d.e.team].short_name, d.e.element_type === 1)}<span><b>${nm(d.e)}</b>${spB(d.e)} <small class="muted">${POS[d.e.element_type]} · ${T[d.e.team].short_name} · ${money(d.e.now_cost)}</small></span></span><span class="pill p-diff">${d.e.selected_by_percent}% owned</span></div>
<div class="alt">Form ${d.e.form} · ${d.e.points_per_game} pts/game · 5-week projection <b>${f1(d.v)}</b></div><div>${fixChips(A, d.e.team, 5, g0)}</div><div><button class="try" type="button" data-quick="${d.e.id}">Bring in for GW${g0}</button></div></div>`).join('') || '<p class="muted">No strong differentials for this week.</p>';
    const CHIPN = [['wildcard', 'Wildcard', 'Best 15 for the next 5 GWs'], ['freehit', 'Free Hit', `Best squad for GW${g0} only`], ['bboost', 'Bench Boost', 'Bench points count too'], ['3xc', 'Triple Captain', 'Captain scores ×3']];
    const usedC = (A.hist && A.hist.chips) || [];
    const chipBtns = CHIPN.map(([k, lab, d]) => {
      const win = BS.chips.filter((c) => c.name === k).find((c) => g0 >= c.start_event && g0 <= c.stop_event);
      const usedNow = win && usedC.find((u) => u.name === k && u.event >= win.start_event && u.event <= win.stop_event);
      const cp = A.chipPlans.find((c) => c.c.name === k && c.from <= g0 && c.to >= g0 && !usedNow);
      const nextWin = BS.chips.filter((c) => c.name === k && c.start_event > g0).sort((a, b) => a.start_event - b.start_event)[0];
      const ok = !!cp;
      const st = PLAN.chip === k ? `<em class="ok">Planned for GW${g0}</em>` : ok ? `<em>Available to GW${cp.c.stop_event}</em>` : usedNow ? `<em class="no">Used GW${usedNow.event}</em>` : `<em class="no">Not available</em>`;
      const best = ok && cp.best && k !== 'wildcard' ? `<span>Best: <b>GW${cp.best.g}</b>${k === 'bboost' ? ` · bench ${f1(cp.best.score)}` : k === '3xc' ? ` · ${f1(cp.best.score)} pts` : ''}</span>` : !ok && nextWin ? `<span>Next one from GW${nextWin.start_event}</span>` : `<span>${d}</span>`;
      return `<button class="chipt ${PLAN.chip === k ? 'on' : ok ? '' : 'na'}" type="button" data-chip="${k}" aria-pressed="${PLAN.chip === k}" title="${ok ? 'Plan it for GW' + g0 : 'Not available this week: preview only'}"><b>${lab}</b>${st}${best}</button>`; }).join('');
    const chipNote = free ? `<div class="chipnote"><b>${PLAN.chip === 'wildcard' ? 'Wildcard' : 'Free Hit'} squad for GW${g0}</b> built within your budget of ${money(PLAN.enter.reduce((a, x) => a + x.sell, 0) + PLAN.bank0)} (selling value + bank), every player at today's price, ${money(PLAN.chipBank || 0)} left, max 3 per club.${(() => { const k = PLAN.line.filter((x) => x.keep != null && x.keep < x.e.now_cost); return k.length ? ` <span style="color:var(--gold)">Kept at a lower selling price: ${k.map((x) => `${esc(x.e.web_name)} ${money(x.keep)}`).join(', ')}. The squad fits even if you remove and re-add them on the FPL site.</span>` : ''; })()}${PLAN.chip === 'freehit' ? ' Your normal squad returns the week after.' : ' Later weeks start from this squad.'}<br><span class="dn">Out (${PLAN.chipOut.length}):</span> ${PLAN.chipOut.map((e) => esc(e.web_name)).join(', ') || '–'}<br><span class="up">In (${PLAN.chipIn.length}):</span> ${PLAN.chipIn.map((e) => nm(e)).join(', ') || '–'}</div>` : PLAN.chip === 'bboost' ? `<div class="chipnote"><b>Bench Boost in GW${g0}:</b> your 4 bench players add ${f1(draft.slice(11).reduce((a, x) => a + P(x.e, g0), 0))} projected pts.</div>` : PLAN.chip === '3xc' ? `<div class="chipnote"><b>Triple Captain in GW${g0}:</b> ${PLAN.cap ? nm(PLAN.cap.e) : '–'} scores ×3, worth +${f1(PLAN.cap ? P(PLAN.cap.e, g0) : 0)} extra projected pts.</div>` : '';
    const H = A.html || {};
    const TABS = [['do', 'Do this now'], ['targets', 'Targets'], ['diffs', 'Differentials'], ['chips', 'Chips']];
    if (!TABS.some(([k]) => k === PLAN.tab)) PLAN.tab = 'do';
    let body;
    if (PLAN.tab === 'auto') body = autoHtml(nm);
    else if (PLAN.tab === 'cap') body = capHtml(g0);
    else if (PLAN.tab === 'do') body = H.doNow || '<p class="muted">Open Home once to build this week\'s actions.</p>';
    else if (PLAN.tab === 'diffs') body = `<p class="note" style="margin:0 0 8px">Owned by under 10% of managers, playing regularly, ranked by projected points from GW${g0}.</p><div class="stack">${diffCards}</div>`;
    else if (PLAN.tab === 'chips') body = `<div class="chipbox"><div class="chiphd"><b>Chips for GW${g0}</b><small>Tap to plan · tap again to remove · red = not available this week</small></div><div class="chipgrid">${chipBtns}</div></div>${wcPanel(nm)}${chipNote}`;
    else body = `<p class="note tn">Best replacement within ${money(bank)} and 3 per club · gain over 5 GWs</p><div class="stack tgt">${moveCards}</div>`;
    box.innerHTML = `<div class="plgrid">
  <div class="plleft">
    <div class="pltools2"><button class="tbtn ico" id="pl-undo" type="button" ${UNDO.length ? '' : 'disabled'} title="${UNDO.length ? 'Undo: ' + esc(UNDO[UNDO.length - 1].label) : 'Nothing to undo'} (Ctrl+Z)" aria-label="Undo"><svg viewBox="0 0 24 24" width="16" height="16" aria-hidden="true"><path d="M9 14L4 9l5-5M4 9h11a5 5 0 0 1 0 10h-3" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round"/></svg></button><button class="tbtn" id="pl-best" type="button" title="Start the 11 players with the highest projections">★ Best 11 players</button><button class="tbtn" id="pl-reset" type="button" title="Undo every change for GW${g0}">↺ Reset GW${g0}</button>${Object.keys(PLAN.weeks).length ? '<button class="tbtn warn" id="pl-clear" type="button" title="Remove every planned transfer and chip">✕ Clear plan</button>' : ''}</div>
    ${plannerNav()}
    ${PLAN.msg ? `<div class="err">${esc(PLAN.msg)}</div>` : ''}${warns.length ? `<ul class="warns">${warns.map((w) => `<li>${w}</li>`).join('')}</ul>` : ''}
    <div class="pitch"><div class="ppills l"><div class="ppill" title="Projected points for GW${g0} with this team, captain included. ${d1 >= 0 ? '+' : ''}${f1(d1)} vs your current team."><b>${f1(new1)}</b><small>GW</small>${Math.abs(d1) > 0.05 ? `<i class="pd ${d1 > 0 ? 'up' : 'dn'}">${d1 > 0 ? '▲+' : '▼'}${f1(d1)}</i>` : ''}</div><div class="ppill" title="Projected points over the next 5 gameweeks. ${d5 >= 0 ? '+' : ''}${f1(d5)} vs your current team."><b>${f1(new5)}</b><small>5 GW</small>${Math.abs(d5) > 0.05 ? `<i class="pd ${d5 > 0 ? 'up' : 'dn'}">${d5 > 0 ? '▲+' : '▼'}${f1(d5)}</i>` : ''}</div></div><div class="ppills r"><div class="ppill" title="Money left to spend after these transfers. ${money(PLAN.bank0)} at the start of GW${g0}."><b class="${bank < 0 ? 'dn' : ''}">${money(bank)}</b><small>Bank</small></div><div class="ppill" title="${free ? 'Unlimited with this chip' : 'Transfers made / free this week'}"><b class="${hits ? 'dn' : ''}">${nT}/${free ? '∞' : PLAN.ft0}${hits ? ` <i>−${hits}</i>` : ''}</b><small>FT</small></div></div><div class="fmpill" title="Formation of the starting XI${PLAN.chip ? ' and the chip planned for this week' : ''}"><b>${formation}</b>${PLAN.chip ? `<small>${({ wildcard: 'Wildcard', freehit: 'Free Hit', bboost: 'Bench Boost', '3xc': 'Triple Captain' })[PLAN.chip]}</small>` : ''}</div><div class="row">${row(1)}</div><div class="row">${row(2)}</div><div class="row">${row(3)}</div><div class="row">${row(4)}</div></div>
    <div class="benchbox"><div class="ptitle">Bench</div><div class="row">${bench.map(chip).join('')}</div></div>
    <p class="legend"><span>Drag a player onto another to swap · tap for captain, transfer or profile</span><span><i class="sp">P</i> penalties · <i class="sp">SP</i> free kicks / corners</span><span><i class="hb d2">H</i> home · <i class="hb d4">A</i> away</span></p>
  </div>
  <div class="splitter" id="pl-split" role="separator" aria-orientation="vertical" aria-label="Resize pitch and side panel" tabindex="0" title="Drag to resize · double-click to reset"></div>
  <div class="plside">
    ${panel}
    <div class="ptabs" role="tablist">${TABS.map(([k, l]) => `<button class="ptab ${PLAN.tab === k ? 'on' : ''}" type="button" role="tab" aria-selected="${PLAN.tab === k}" data-tab="${k}">${l}</button>`).join('')}</div>
    <div class="ptbody">${body}</div>
  </div>
</div>${PLAN.swaps.length ? `<p class="h2hnote"><span class="muted">Head to head for your ${PLAN.swaps.length} planned transfer${PLAN.swaps.length > 1 ? 's' : ''} is on the Fixtures page.</span><button class="try" type="button" data-h2h="1">Open head to head</button></p>` : ''}`;
    box.classList.toggle('sidescroll', PLAN.tab === 'chips' || PLAN.tab === 'do');
    { const pb = box.querySelector('.ptbody'); if (pb) { const narrow = window.innerWidth <= 860 && (PLAN.tab === 'chips' || PLAN.tab === 'do'); pb.style.maxHeight = narrow ? Math.round(window.innerHeight * 0.72) + 'px' : ''; pb.style.overflowY = narrow ? 'auto' : ''; pb.style.overscrollBehavior = narrow ? 'contain' : ''; } }
    tidyKpis(box); CI_FIXED(); applyCI(); paintSlide(); applyPV();
    if (FIXTAB === 'h2h') paintRot();
    const qi = R.getElementById('pl-q'); if (qi && PLAN.q) { qi.focus(); qi.setSelectionRange(qi.value.length, qi.value.length); }
  }

  // ---------- v3.9: drag a player onto another to swap them (mouse and touch) ----------
  // Dragging lights up the players he can legally swap with (formation rules); dropping on one swaps them.
  // A plain tap still opens the action sheet; dropping anywhere else cancels.
  let DRAG = null;
  out.addEventListener('pointerdown', (ev) => {
    if (ev.button !== 0 || !PLAN || PLAN.gw < PLAN.A.startGw) return;
    const card = ev.target.closest && ev.target.closest('#planner .chip.pc[data-card]'); if (!card) return;
    const x = byId(+card.dataset.card); if (!x) return;
    DRAG = { card, x, id: x.e.id, sx: ev.clientX, sy: ev.clientY, cx: ev.clientX, cy: ev.clientY, on: false, pid: ev.pointerId, ghost: null, over: null, ok: new Set(partners(x).map((y) => y.e.id)) };
  });
  // v3.12: the whole card (jersey included) drags; the list scrolls when the finger nears the top or bottom; moves are drawn once per frame
  out.addEventListener('dragstart', (ev) => { if (ev.target.closest && ev.target.closest('#planner')) ev.preventDefault(); });
  out.addEventListener('contextmenu', (ev) => { if (ev.target.closest && ev.target.closest('#planner .chip.pc')) ev.preventDefault(); });
  let DRAF = 0, DRAS = 0;
  function dragFrame() {
    DRAF = 0; const d = DRAG; if (!d || !d.on) return;
    const pr = d.pr; d.ghost.style.transform = `translate3d(${d.cx - pr.left - d.dx}px,${d.cy - pr.top - d.dy}px,0)`;
    const under = R.elementFromPoint(d.cx, d.cy); const tgt = under && under.closest && under.closest('#planner .chip.pc.droppable');
    if (tgt !== d.over) { if (d.over) d.over.classList.remove('dropover'); if (tgt) tgt.classList.add('dropover'); d.over = tgt; }
  }
  function dragScroll() {
    const d = DRAG; if (!d || !d.on) { DRAS = 0; return; }
    const r = out.getBoundingClientRect(), nb = (R.getElementById('nav') || out).getBoundingClientRect();
    const top = r.top, bot = nb.top > r.top + 120 && nb.top < r.bottom ? nb.top : r.bottom, edge = Math.min(80, (bot - top) / 5);
    let v = d.cy > bot - edge ? (d.cy - (bot - edge)) / edge : d.cy < top + edge ? -((top + edge) - d.cy) / edge : 0;
    v = Math.max(-1, Math.min(1, v));
    // stay on the pitch: stop once the bench (last card) or the first row is fully in view
    const cs = R.querySelectorAll('#planner .chip.pc[data-card]');
    if (cs.length) { if (v > 0 && cs[cs.length - 1].getBoundingClientRect().bottom < bot - 8) v = 0; if (v < 0 && cs[0].getBoundingClientRect().top > top + 8) v = 0; }
    if (v) { out.scrollTop += Math.round(v * v * 12 * Math.sign(v)) || Math.sign(v); if (!DRAF) DRAF = requestAnimationFrame(dragFrame); }
    DRAS = requestAnimationFrame(dragScroll);
  }
  out.addEventListener('pointermove', (ev) => {
    if (!DRAG || ev.pointerId !== DRAG.pid) return;
    if (DRAG.on) { ev.preventDefault(); DRAG.cx = ev.clientX; DRAG.cy = ev.clientY; if (!DRAF) DRAF = requestAnimationFrame(dragFrame); return; }
    if (!DRAG.on) {
      if (Math.hypot(ev.clientX - DRAG.sx, ev.clientY - DRAG.sy) < 8) return;
      DRAG.on = true;
      const r = DRAG.card.getBoundingClientRect(); DRAG.dx = DRAG.sx - r.left; DRAG.dy = DRAG.sy - r.top;
      const g = DRAG.card.cloneNode(true); g.classList.add('dragghost'); g.removeAttribute('data-card'); g.style.width = r.width + 'px';
      R.querySelector('.panel').appendChild(g); DRAG.ghost = g; DRAG.card.classList.add('dragsrc');
      R.querySelectorAll('#planner .chip.pc[data-card]').forEach((c) => { if (DRAG.ok.has(+c.dataset.card)) c.classList.add('droppable'); else if (c !== DRAG.card) c.classList.add('dim'); });
      try { DRAG.card.setPointerCapture(ev.pointerId); } catch (e) {}
      DRAG.pr = R.querySelector('.panel').getBoundingClientRect(); if (navigator.vibrate) try { navigator.vibrate(12); } catch (e) {}
      out.style.overflowY = 'hidden';
    }
    ev.preventDefault(); DRAG.cx = ev.clientX; DRAG.cy = ev.clientY; if (!DRAF) DRAF = requestAnimationFrame(dragFrame);
  });
  const endDrag = (ev, cancel) => {
    if (!DRAG || (ev && ev.pointerId !== DRAG.pid)) return;
    const d = DRAG; DRAG = null; if (!d.on) return;
    out.style.overflowY = '';
    if (DRAF) cancelAnimationFrame(DRAF); if (DRAS) cancelAnimationFrame(DRAS); DRAF = DRAS = 0;
    let target = null;
    if (!cancel && ev) { const under = R.elementFromPoint(ev.clientX, ev.clientY); const t = under && under.closest && under.closest('#planner .chip.pc.droppable'); if (t) target = +t.dataset.card; }
    if (d.ghost) d.ghost.remove();
    R.querySelectorAll('#planner .chip.pc').forEach((c) => c.classList.remove('droppable', 'dropover', 'dragsrc', 'dim'));
    // swallow the click that follows a drag so the action sheet doesn't open
    const stop = (e) => { e.stopPropagation(); e.preventDefault(); out.removeEventListener('click', stop, true); };
    out.addEventListener('click', stop, true); setTimeout(() => out.removeEventListener('click', stop, true), 0);
    if (target) { PLAN.sel = null; planInternal(d.id, target); }
  };
  out.addEventListener('pointerup', (ev) => endDrag(ev, false));
  out.addEventListener('pointercancel', (ev) => endDrag(ev, true));
  document.addEventListener('keydown', (ev) => { if (ev.key === 'Escape' && DRAG && DRAG.on) endDrag(null, true); });
  document.addEventListener('keydown', (ev) => {
    if (!(ev.ctrlKey || ev.metaKey) || ev.key.toLowerCase() !== 'z' || ev.shiftKey) return;
    if (!document.getElementById(PID) || VIEW !== 'team' || !UNDO.length) return;
    const a = R.activeElement; if (a && /^(INPUT|TEXTAREA|SELECT)$/.test(a.tagName)) return;
    ev.preventDefault(); undoStep();
  });
  // ---------- Views: dashboard home + one section at a time ----------
  let VIEW = 'home';
  const VIEWS = [['home', 'Home'], ['team', 'My Team'], ['live', 'Live'], ['fix', 'Fixtures'], ['news', 'News']];
  const SUBS = { team: [['pitch', 'Pitch', 's-planner'], ['list', 'List', 's-squad']], fix: [['ticker', 'Ticker', 's-fix'], ['pairs', 'Pairs', 's-fix'], ['market', 'Market', 's-fix'], ['stats', 'Player stats', 's-fix'], ['h2h', 'Head to head', 's-fix'], ['acc', 'Accuracy', 's-fix'], ['table', 'Table', 's-table']] };
  const SUBV = { team: 'pitch', fix: 'ticker' };
  const ALIAS = { plan: ['home'], planner: ['team', 'pitch'], squad: ['team', 'list'], table: ['fix', 'table'], gw: ['home'], season: ['home'] };
  function paintRot() { const sec = R.getElementById('s-fix'); if (!sec || !LASTA) return; const tmp = document.createElement('div'); tmp.innerHTML = rotHtml(LASTA); const ne = tmp.firstElementChild; ne.hidden = !(VIEW === 'fix' && SUBV.fix !== 'table'); sec.replaceWith(ne); }
  const secOf = (v) => { if (!SUBS[v]) return 's-' + v; const s = SUBS[v].find(([k]) => k === SUBV[v]) || SUBS[v][0]; return s[2]; };
  function moveInk() {
    const nav = R.getElementById('nav'), ink = nav && nav.querySelector('.nink'), on = nav && nav.querySelector('a.on'); if (!ink) return;
    if (!on) { ink.style.opacity = 0; return; }
    ink.style.opacity = 1; ink.style.transform = `translate(${on.offsetLeft}px,${on.offsetTop}px)`; ink.style.width = on.offsetWidth + 'px'; ink.style.height = on.offsetHeight + 'px';
  }
  function countUps(root) {
    if (UI.motion === 'calm' || RM()) return;
    root.querySelectorAll('[data-count]').forEach((el) => { const to = +el.dataset.count; if (!isFinite(to)) return; const t0 = performance.now(), dur = 850; const fmt = (v) => Math.round(v).toLocaleString();
      const step = (t) => { const k = Math.min(1, (t - t0) / dur), e2 = 1 - Math.pow(1 - k, 3); el.textContent = fmt(to * e2); if (k < 1) requestAnimationFrame(step); }; requestAnimationFrame(step); });
  }
  function playWipe() {
    if (UI.motion === 'calm' || RM() || window.innerWidth < 700) return false;
    const w = R.getElementById('wipe'), m = R.getElementById('out'); if (!w || !m) return false;
    w.style.top = m.offsetTop + 'px'; w.classList.remove('go'); void w.offsetWidth; w.classList.add('go'); clearTimeout(w.__t); w.__t = setTimeout(() => w.classList.remove('go'), 700 * (UI.motion === 'calm' ? 1.4 : UI.motion === 'lively' ? 0.8 : 1)); return true;
  }
  function showView(v, sub) {
    { const pg = R.getElementById('ppage'); if (pg && !pg.hidden) pg.hidden = true; }
    if (ALIAS[v]) { const [m, s2] = ALIAS[v]; v = m; if (s2) sub = s2; }
    if (!VIEWS.some(([k]) => k === v) || !R.getElementById(secOf(v))) v = 'home';
    if (v === 'news') setTimeout(nfApply, 0);
    if (v === 'fix' && (sub === 'stats' || sub === 'market')) setTimeout(() => loadPlayerStats(false), 0);
    if (sub && SUBS[v]) SUBV[v] = sub;
    if (v === 'fix' && SUBV.fix !== 'table' && FIXTAB !== SUBV.fix) { FIXTAB = SUBV.fix; paintRot(); }
    const prev = VIEW; VIEW = v;
    const id = secOf(v);
    const order = (k) => VIEWS.findIndex(([x]) => x === k);
    const mainChange = prev !== v;
    const wiped = mainChange && playWipe();
    out.querySelectorAll(':scope > section.s').forEach((s) => { const on = s.id === id; const was = !s.hidden; s.hidden = !on;
      if (on && (!was || mainChange)) { s.classList.remove('vin-r', 'vin-l', 'vin-f'); void s.offsetWidth; s.classList.add(wiped ? 'vin-f' : mainChange ? (order(v) >= order(prev) ? 'vin-r' : 'vin-l') : 'vin-f'); countUps(s); } });
    R.querySelectorAll('nav a').forEach((a) => a.classList.toggle('on', a.dataset.t === v));
    const ns = R.getElementById('navsub'); if (ns) ns.innerHTML = SUBS[v] ? `<div class="seg" role="tablist">${SUBS[v].map(([k, l]) => `<button type="button" role="tab" data-sub="${k}" class="${SUBV[v] === k ? 'on' : ''}" aria-selected="${SUBV[v] === k}">${l}</button>`).join('')}</div>` : '';
    const sn = R.getElementById('subnav');
    if (sn) { if (SUBS[v]) { sn.hidden = false; sn.innerHTML = `<div class="seg" role="tablist">${SUBS[v].map(([k, l]) => `<button type="button" role="tab" data-sub="${k}" class="${SUBV[v] === k ? 'on' : ''}" aria-selected="${SUBV[v] === k}">${l}</button>`).join('')}</div>`; } else { sn.hidden = true; sn.innerHTML = ''; } }
    moveInk(); fitHome();
    out.scrollTop = 0;
    if (v === 'team' && SUBV.team === 'pitch' && typeof applyPV === 'function') requestAnimationFrame(applyPV);
  }
  // v3.11: Home always fits the panel height on desktop (cards scroll inside themselves)
  function fitHome() { out.style.setProperty('--oh', out.clientHeight + 'px'); }
  window.addEventListener('resize', () => { moveInk(); fitHome(); });
  // News slider: one story at a time, sliding vertically, with dots
  let SLT = null;
  function sliderHtml(slides) {
    if (!slides.length) return '<p class="muted">No headlines could be read right now.</p>';
    return `<div class="slider" data-slider data-i="0"><div class="strack">${slides.map((s) => `<div class="slide"><div class="sph nph">${newsPic(s.it, s.who)}</div><div class="stx"><div><span class="kind k-${s.it.kind}">${{ news: 'News', leak: 'Leak', social: 'Social' }[s.it.kind] || 'News'}</span>${s.who ? `<span class="pill ${s.tone === 'neg' ? 'p-sell' : s.tone === 'pos' ? 'p-live' : 'p-keep'}">${esc(s.who.web_name)}</span>` : ''}</div><a class="stitle" href="${esc(s.it.link)}" target="_blank" rel="noopener">${esc(s.it.title)}</a><small class="muted">${esc(s.it.src)}${s.ago ? ' · ' + s.ago : ''}</small></div></div>`).join('')}</div><div class="sdots">${slides.map((_, i) => `<button type="button" class="${i ? '' : 'on'}" data-dot="${i}" aria-label="Story ${i + 1}"></button>`).join('')}</div></div>`;
  }
  function slideTo(sl, i) {
    const n = sl.querySelectorAll('.slide').length; if (!n) return;
    i = ((i % n) + n) % n; sl.dataset.i = i;
    sl.querySelector('.strack').style.transform = `translateY(-${i * 100}%)`;
    sl.querySelectorAll('.sdots button').forEach((b, k) => b.classList.toggle('on', k === i));
  }
  function initSliders() {
    clearInterval(SLT);
    if (window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches) return;
    SLT = setInterval(() => { if (!document.getElementById(PID)) return clearInterval(SLT); R.querySelectorAll('[data-slider]').forEach((sl) => { if (!sl.matches(':hover') && !sl.contains(R.activeElement)) slideTo(sl, +sl.dataset.i + 1); }); }, 5000);
  }

  // ---------- This gameweek vs last ----------
  function gwSection(A) {
    const hc = A.hist.current || []; let c = hc[hc.length - 1]; const p = hc[hc.length - 2];
    if (!c) return '';
    // v3.71: a gameweek still being played shows the live total (FPL's own total stays 0 until it updates)
    if (A.live && A.live.gw === c.event && !((BS.events.find((x) => x.id === c.event) || {}).finished)) c = Object.assign({}, c, { points: A.live.pts + (c.event_transfers_cost || 0), points_on_bench: A.live.bench != null ? A.live.bench : c.points_on_bench });
    const T = A.T, G = A.gwCmp || {};
    const nm = (e) => `<a class="pn" href="#" data-pid="${e.id}">${esc(e.web_name)}</a>`;
    const avg = (g) => (BS.events.find((e) => e.id === g) || {}).average_entry_score || 0;
    // unit: 'rank' (lower is better, shown as places), 'pts', 'bench' (fewer wasted points is better), 'money'
    const chg = (now, was, unit) => {
      if (was == null || now == null) return '<span class="muted">no previous week</span>';
      const better = unit === 'rank' || unit === 'bench' ? was - now : now - was;
      if (!better) return '<span class="muted">no change</span>';
      const amt = Math.abs(now - was);
      const txt = unit === 'rank' ? `${amt.toLocaleString()} places ${better > 0 ? 'up' : 'down'}` : unit === 'money' ? `${now > was ? '+' : '−'}${money(amt)}` : `${now > was ? '+' : '−'}${amt} pts`;
      return `<span class="${better > 0 ? 'up' : 'dn'}">${better > 0 ? '▲' : '▼'} ${txt}</span>`;
    };
    const k = (lab, now, was, unit, fmt) => `<div class="kpi"><small>${lab}</small><b>${fmt ? fmt(now) : (now ?? 0).toLocaleString()}</b><span>${chg(now, was, unit)}</span><span class="was">GW${p ? p.event : '–'}: ${p ? (fmt ? fmt(was) : (was ?? 0).toLocaleString()) : '–'}</span></div>`;
    return `<h3 class="h3">GW${c.event} vs GW${p ? p.event : '–'} <span class="muted" style="text-transform:none;letter-spacing:0">· you scored ${c.points}, average ${avg(c.event)} (${c.points >= avg(c.event) ? `<span class="up">▲ ${c.points - avg(c.event)}</span>` : `<span class="dn">▼ ${avg(c.event) - c.points}</span>`})${c.event_transfers_cost ? ` · hit <span class="dn">−${c.event_transfers_cost}</span>` : ''}</span></h3>
<div class="kpis uni">
  ${k('GW points', c.points, p && p.points, 'pts')}
  ${k('Overall rank', c.overall_rank, p && p.overall_rank, 'rank')}
  ${k('Gameweek rank', c.rank, p && p.rank, 'rank')}
  ${k('Total points', c.total_points, p && p.total_points, 'pts')}
  ${k('Points on bench', c.points_on_bench, p && p.points_on_bench, 'bench')}
  ${k('Team value', c.value, p && p.value, 'money', (v) => money(v || 0))}
</div>`;
  }
  $('#dx').onclick = () => { drawer.hidden = true; };

  async function openProfile(pid) {
    return openPlayerPage(pid);
    const A = LAST; if (!A) return;
    const e = A.E[pid]; const T = A.T;
    const full = `${e.first_name} ${e.second_name}`;
    const body = $('#dbody');
    drawer.hidden = false;
    body.innerHTML = `<p class="muted">Loading ${esc(full)}…</p>`;
    let sum = null;
    try { sum = await J(`/api/element-summary/${pid}/`); } catch (er) {}
    const n = A.NM[pid];
    const tone = (t) => (t === 'neg' ? '<span class="pill p-sell">Concern</span>' : t === 'pos' ? '<span class="pill p-core">Positive</span>' : '');
    const kindLab = { news: 'News', leak: 'Leak', social: 'Social' };
    const hist = sum ? sum.history.slice(-6).reverse() : [];
    const nextF = sum ? sum.fixtures.slice(0, 6) : [];
    const q = encodeURIComponent(full);
    body.innerHTML = `
<div class="ph"><div><h2 style="margin:0">${esc(full)}${isNewSigning(e) ? ' <span class="newpill" title="Not at this club last season">New signing</span>' : ''}</h2><p class="sub" style="margin:2px 0 0">${POS[e.element_type]} · ${esc(T[e.team].name)} · ${money(e.now_cost)} · owned ${e.selected_by_percent}%</p>${spList(e).length ? `<p class="sub" style="margin:4px 0 0">Set pieces: ${spList(e).map(([l, v]) => `${SPN[l].toLowerCase()} (${v === 1 ? '1st' : '2nd'} choice)`).join(', ')}</p>` : ''}</div>${kitImg(T[e.team].short_name, e.element_type === 1, 110, 'big')}</div>
${e.news ? `<div class="err" style="margin-top:10px">${esc(e.news)}</div>` : ''}
<div class="kpis" style="margin-top:12px">
  <div class="kpi"><small>Total</small><b>${e.total_points}</b><span>${e.points_per_game} per game</span></div>
  <div class="kpi"><small>Form</small><b>${e.form}</b><span>last 30 days</span></div>
  <div class="kpi"><small>xGI / 90</small><b>${e.expected_goal_involvements_per_90 ?? '–'}</b><span>${e.goals_scored} G · ${e.assists} A</span></div>
  <div class="kpi"><small>Next 5 projection</small><b>${f1(A.S5(e))}</b><span>GW${A.startGw}: ${f1(A.P(e, A.startGw))}</span></div>
</div>
${(() => { const rt = A.ratings(e); return `<h3 class="h3">Ratings <small class="muted" style="text-transform:none;letter-spacing:0;font-weight:500">0–100 vs other ${POS[e.element_type]}s</small></h3><div class="rtg">${rt.map((x) => `<div class="rt" title="${esc(x.d)}"><span>${x.l}</span><i><b style="width:${x.v}%;background:${x.v >= 80 ? 'var(--acc)' : x.v >= 55 ? '#8bd3b8' : x.v >= 30 ? '#c9a54a' : '#d9706a'}"></b></i><em>${x.v}</em></div>`).join('')}</div>`; })()}
${(() => { const R2 = A.rate(e), ps = pastOf(e); const dc = A.dcEV(e); return `<h3 class="h3">How the projection is built</h3><div class="kpis mdl">
  <div class="kpi"><small>Game time</small><b>${Math.round(A.rel(e) * 100)}%</b><span>last 5 GWs and season minutes</span></div>
  <div class="kpi"><small>xGI / 90 (adjusted)</small><b>${R2.xgi.toFixed(2)}</b><span>this season ${(+e.expected_goal_involvements_per_90 || 0).toFixed(2)}${ps.some(Boolean) ? ' + past seasons' : ''}</span></div>
  <div class="kpi"><small>Points / 90 (adjusted)</small><b>${R2.pts.toFixed(1)}</b><span>pulled toward the ${POS[e.element_type]} average</span></div>
  ${e.element_type > 1 ? `<div class="kpi"><small>Defensive contribution</small><b>+${dc.toFixed(2)}</b><span>expected bonus per match · ${R2.dc.toFixed(1)} actions / 90 · already counted in points per 90</span></div>` : ''}
</div>${ps.some(Boolean) ? `<h3 class="h3">Previous seasons</h3><div class="tw"><table><thead><tr><th>Season</th><th class="n">Pts</th><th class="n">Mins</th><th class="n">Starts</th><th class="n">G</th><th class="n">A</th><th class="n">xGI / 90</th><th class="n">Pts / 90</th></tr></thead><tbody>${ps.filter(Boolean).map((p) => `<tr><td>${p.k.replace('-', '/')}</td><td class="n"><b>${p.p}</b></td><td class="n">${p.m}</td><td class="n">${p.st}</td><td class="n">${p.g}</td><td class="n">${p.a}</td><td class="n">${((p.xg + p.xa) / (p.m / 90)).toFixed(2)}</td><td class="n">${(p.p / (p.m / 90)).toFixed(1)}</td></tr>`).join('')}</tbody></table></div>` : '<p class="muted" style="font-size:13px">No Premier League minutes in 2024/25 or 2023/24, so this season and the position average carry the projection.</p>'}`; })()}
<h3 class="h3">Upcoming</h3>${fixChips(A, e.team, 6)}
${hist.length ? `<h3 class="h3">Last ${hist.length} matches</h3><div class="tw"><table><thead><tr><th>GW</th><th>Opponent</th><th class="n">Mins</th><th class="n">G</th><th class="n">A</th><th class="n">CS</th><th class="n">Bonus</th><th class="n">xGI</th><th class="n">Pts</th></tr></thead><tbody>${hist.map((h) => `<tr><td>${h.round}</td><td>${T[h.opponent_team].short_name}${ha(h.was_home)} ${h.team_h_score != null ? `<small class="muted">${h.team_h_score}-${h.team_a_score}</small>` : ''}</td><td class="n">${h.minutes}</td><td class="n">${h.goals_scored}</td><td class="n">${h.assists}</td><td class="n">${h.clean_sheets}</td><td class="n">${h.bonus}</td><td class="n">${h.expected_goal_involvements ?? '–'}</td><td class="n"><b>${h.total_points}</b></td></tr>`).join('')}</tbody></table></div>` : ''}
<h3 class="h3">News, leaks and social mentions</h3>
${n ? n.hits.slice(0, 8).map((it) => `<div class="alt" style="margin-bottom:6px"><span class="pill p-keep">${kindLab[it.kind] || 'News'}</span> ${tone(it.tone)} <a href="${esc(it.link)}" target="_blank" rel="noopener">${esc(it.title)}</a> <small class="muted">${esc(it.src)}</small></div>`).join('') : '<p class="muted">No mentions in the last 12 days.</p>'}
<div style="margin-top:14px"><button class="go" type="button" data-addp="${pid}">${A.sq.some((s) => s.e.id === pid) ? 'Remove in transfer planner' : 'Try in transfer planner'}</button></div>
<h3 class="h3">Open elsewhere</h3>
<div class="links">
<a href="https://fantasy.premierleague.com/statistics" target="_blank" rel="noopener">FPL statistics</a>
<a href="${plUrl(e)}" target="_blank" rel="noopener">Premier League player page</a>
<a href="https://news.google.com/search?q=${q}" target="_blank" rel="noopener">Latest news</a>
<a href="https://x.com/search?q=${q}&f=live" target="_blank" rel="noopener">Live posts on X</a>
<a href="https://www.reddit.com/r/FantasyPL/search/?q=${q}&sort=new" target="_blank" rel="noopener">r/FantasyPL</a>
</div>`;
    body.scrollTop = 0;
  }

  function render(A) {
    const { entry, hist, cur, nxt, T, P, S5, sq, now, caps, moves, chipPlans } = A;
    const g0 = A.startGw;
    const hc = hist.current || [];
    const last = hc[hc.length - 1];
    const avgOf = (g) => (BS.events.find((e) => e.id === g) || {}).average_entry_score || 0;
    const name = (e) => `<a class="pn" href="#" data-pid="${e.id}" title="Open ${esc(e.first_name)} ${esc(e.second_name)}'s profile">${esc(e.web_name)}</a>`;
    const tm = (e) => T[e.team].short_name;
    LAST = A; LASTA = A;
    { const tp = R.querySelector('.panel>.top'), rg = null; if (tp) { tp.classList.toggle('fl', !!rg); tp.classList.toggle('egy', !!rg && rg[0] === 'eg'); if (rg) tp.style.setProperty('--flagt', `url('${flagPng(rg[0])}')`); else tp.style.removeProperty('--flagt'); if (rg && !tp.querySelector('.tfl')) tp.insertAdjacentHTML('afterbegin', '<span class="tfl" aria-hidden="true"><i class="l"></i><i class="r"></i><i class="c"></i><i class="t"></i></span>'); if (!rg) { const x = tp.querySelector('.tfl'); if (x) x.remove(); } tp.title = rg ? entry.player_region_name || '' : ''; } }

    // ACTION PLAN: each item is [tag, text, { lab, attr } action]
    const plan = [];
    const mvH = (o, i) => `<span class="mvx">${o}<i aria-label="replaced by">→</i>${i}</span>`;
    const good = moves.filter((m) => m.cands.length && m.gain >= A.CONV && m.score >= 2);
    if (good.length && A.ft >= 1) {
      const used = new Set();
      const picked = [];
      for (const m of good) {
        if (picked.length >= Math.max(1, Math.min(A.ft, 2))) break;
        if (used.has(m.cands[0].c.id)) continue;
        used.add(m.cands[0].c.id); picked.push(m);
      }
      picked.forEach((m) => plan.push(['Transfer', `${mvH(name(m.s.e), name(m.cands[0].c))}<br><b class="up">+${f1(m.gain)} pts</b> <small class="muted">over 5 GWs · ${tm(m.cands[0].c)} · ${money(m.cands[0].c.now_cost)}</small>`, { lab: 'Make transfer', attr: `data-try="${m.s.e.id}:${m.cands[0].c.id}"` }]));
    } else if (good.length && A.ft === 0 && good[0].gain >= 4 + A.CONV && good[0].score >= 4 + A.CONV) {
      plan.push(['Transfer', `Worth a −4 hit: ${mvH(name(good[0].s.e), name(good[0].cands[0].c))} <b class="up">+${f1(good[0].gain)} pts</b> <small class="muted">over 5 GWs</small>`, { lab: 'Make transfer', attr: `data-try="${good[0].s.e.id}:${good[0].cands[0].c.id}"` }]);
    } else {
      plan.push(['Transfer', `No move gains ${A.CONV} pts or more over 5 GWs. <b>Roll the free transfer</b> (${Math.min(5, A.ft + 1)} next week).`, { lab: 'Open planner', attr: 'data-act="planner"' }]);
    }
    if (caps[0]) plan.push(['Captain', `<b>${name(caps[0].e)}</b> <small class="muted">${f1(P(caps[0].e, g0))} pts projected</small>${caps[1] ? ` · vice <b>${name(caps[1].e)}</b>` : ''}`, { lab: 'Set armband', attr: 'data-act="bestxi"' }]);
    const currentXI = new Set(A.picks.filter((p) => p.position <= 11).map((p) => p.element));
    const ins = now.xi.filter((s) => !currentXI.has(s.e.id));
    const outs = A.picks.filter((p) => p.position <= 11 && !now.xi.some((s) => s.e.id === p.element)).map((p) => A.E[p.element]);
    if (ins.length) plan.push(['Lineup', `Start ${ins.map((s) => `<b>${name(s.e)}</b>`).join(', ')}, bench ${outs.map((e) => `<b>${name(e)}</b>`).join(', ')}`, { lab: 'Best 11 players', attr: 'data-act="bestxi"' }]);
    else plan.push(['Lineup', 'Your starting XI is already the projected best XI.', { lab: 'View lineup', attr: 'data-act="planner"' }]);
    const newsBad = sq.filter((s) => A.NM[s.e.id] && A.NM[s.e.id].signal === 'neg');
    if (false && newsBad.length) plan.push(['News', `Reports raise doubts over ${newsBad.map((s) => `<b>${name(s.e)}</b>`).join(', ')}. Check press conferences before the deadline.`, { lab: 'Read news', attr: 'data-view="news"' }]);
    const flagged = sq.filter((s) => s.e.status !== 'a');
    if (false && flagged.length) plan.push(['Injuries', flagged.map((s) => `<b>${name(s.e)}</b> <small class="muted">${esc(s.e.news || s.e.status)}</small>`).join(' · '), { lab: 'See squad', attr: 'data-view="squad"' }]);
    chipPlans.filter((c) => !c.locked && c.best && c.c.name !== 'wildcard').forEach((c) => {
      const nowGw = c.best.g === g0;
      const lastCall = c.c.stop_event - g0 <= 2;
      if (nowGw || lastCall) plan.push(['Chip', `${nowGw ? 'Play' : 'Plan'} <b>${CHIP[c.c.name] || c.c.name}</b> in GW${c.best.g} <small class="muted">expires after GW${c.c.stop_event}</small>`, { lab: nowGw ? 'Try chip' : 'Plan chip', attr: `data-act="chip:${c.c.name}"` }]);
    });
    const wc = chipPlans.find((c) => c.c.name === 'wildcard' && !c.locked);
    if (wc && A.sellCount >= 4) plan.push(['Chip', `${A.sellCount} players need replacing. A <b>Wildcard</b> is worth considering.`, { lab: 'Build wildcard', attr: 'data-act="chip:wildcard"' }]);
    const falling = sq.filter((s) => { const o = priceOutlook(s.e); return o && o.d === 'down'; });
    const sellNow = falling.filter((s) => good.some((m) => m.s === s));
    if (falling.length) plan.push(['Prices', `${falling.map((s) => `${name(s.e)} <small class="muted">${priceOutlook(s.e).lv}</small>`).join(', ')}: price may drop tonight${sellNow.length ? '. You plan to sell ' + sellNow.map((s) => name(s.e)).join(', ') + ', so do it before the drop.' : ''}`, { lab: 'See squad', attr: 'data-view="squad"' }]);
    const rising = good.map((m) => m.cands[0] && m.cands[0].c).filter((c) => { const o = c && priceOutlook(c); return o && o.d === 'up'; });
    if (rising.length) plan.push(['Prices', `${rising.map((c) => name(c)).join(', ')} may rise £0.1m tonight. If you're buying, buy before the deadline-day rush.`, { lab: 'Open planner', attr: 'data-act="planner"' }]);

    const rankMove = hc.length > 1 ? hc[hc.length - 2].overall_rank - last.overall_rank : 0;

    // Squad rows
    const sorted = sq.slice().sort((a, b) => (A.picks.indexOf(a.p) - A.picks.indexOf(b.p)));
    const squadRows = sorted.map((s) => {
      const e = s.e; const [cls, lab] = A.verdict(s);
      const share = Math.min(100, Math.round((100 * e.minutes) / (90 * Math.max(1, A.tb[e.team].P))));
      const net = e.transfers_in_event - e.transfers_out_event;
      const bench = s.p.position > 11;
      return `<tr class="${bench ? 'bench' : ''}"><td class="pl"><b>${name(e)}</b><small>${POS[e.element_type]} · ${tm(e)}</small>${spB(e)}${priceB(e)}${A.isDiff(e) ? ' <span class="pill p-diff">Diff</span>' : ''}${s.p.is_captain ? ' <span class="pill p-core">C</span>' : s.p.is_vice_captain ? ' <span class="pill p-keep">VC</span>' : ''}</td>
<td class="n">${money(e.now_cost)}${s.p.selling_price != null && s.p.selling_price !== e.now_cost ? `<br><small class="muted">sell ${money(s.p.selling_price)}</small>` : ''}</td>
<td class="n">${e.form}</td><td class="n">${e.points_per_game}</td><td class="n">${e.total_points}</td><td class="n">${e.expected_goal_involvements_per_90 ?? '–'}</td><td class="n">${share}%</td>
<td>${fixChips(A, e.team, 5)}</td><td class="n"><b>${f1(P(e, g0))}</b></td><td class="n">${f1(S5(e))}</td>
<td class="n ${net > 0 ? 'up' : net < 0 ? 'dn' : ''}">${net > 0 ? '▲' : net < 0 ? '▼' : ''}${Math.abs(net) >= 1000 ? Math.round(Math.abs(net) / 1000) + 'k' : Math.abs(net)}</td>
<td><span class="pill p-${cls}">${lab}</span>${e.news ? `<div class="news">${esc(e.news)}</div>` : ''}</td></tr>`;
    }).join('');

    // Transfers
    const moveCards = moves.filter((m) => m.cands.length && m.gain > 0.5).slice(0, 6).map((m) => `<div class="move"><div class="h"><span>Sell <b>${name(m.s.e)}</b> <small class="muted">${tm(m.s.e)} · ${money(m.s.sell)}</small></span><span class="gain">+${f1(m.gain)} pts</span></div>
<div>Buy <b>${name(m.cands[0].c)}</b> ${A.isDiff(m.cands[0].c) ? '<span class="pill p-diff">Differential</span> ' : ''}<small class="muted">${tm(m.cands[0].c)} · ${money(m.cands[0].c.now_cost)} · form ${m.cands[0].c.form} · owned ${m.cands[0].c.selected_by_percent}%</small></div>
<div>${fixChips(A, m.cands[0].c.team, 5)}</div>
${m.cands.slice(1).length ? `<div class="alt">Alternatives: ${m.cands.slice(1).map((c) => `${name(c.c)} (${T[c.c.team].short_name}, ${money(c.c.now_cost)}, +${f1(c.v - m.mine)})`).join(' · ')}</div>` : ''}
<div><button class="try" type="button" data-try="${m.s.e.id}:${m.cands[0].c.id}">Make this transfer</button></div></div>`).join('') || '<p class="muted">No transfer improves your projected score by more than half a point.</p>';

    // Lineup pitch
    const rowOf = (t) => now.xi.filter((s) => s.e.element_type === t).map((s) => `<div class="chip ${caps[0] && s === caps[0] ? 'c' : ''}"><b>${name(s.e)}${caps[0] && s === caps[0] ? ' (C)' : caps[1] && s === caps[1] ? ' (V)' : ''}</b><span>${tm(s.e)} · ${f1(P(s.e, g0))} pts</span></div>`).join('');
    const formation = [2, 3, 4].map((t) => now.xi.filter((s) => s.e.element_type === t).length).join('-');
    const benchHtml = now.bench.map((s, i) => `<div class="chip"><b>${i === 0 ? 'GK · ' : i + '. '}${name(s.e)}</b><span>${tm(s.e)} · ${f1(P(s.e, g0))} pts</span></div>`).join('');

    // Chips
    const chipCards = chipPlans.map((c) => {
      const label = CHIP[c.c.name] || c.c.name;
      if (c.locked) return `<div class="move"><div class="h"><b>${label}</b><span class="pill p-keep">Unlocks GW${c.c.start_event}</span></div><div class="alt">Second-half chip, usable GW${c.c.start_event}–${c.c.stop_event}.</div></div>`;
      if (c.c.name === 'wildcard') return `<div class="move"><div class="h"><b>${label}</b><span class="pill ${A.sellCount >= 4 ? 'p-up' : 'p-keep'}">${A.sellCount >= 4 ? 'Consider now' : 'Hold'}</span></div><div class="alt">${A.sellCount} squad player(s) flagged to sell or injured. Expires after GW${c.c.stop_event}.</div></div>`;
      const mx = Math.max(1, ...c.rows.map((r) => Math.abs(r.score)));
      const mn = Math.min(...c.rows.map((r) => r.score));
      const bars = c.rows.map((r) => { const h = c.c.name === 'freehit' ? (r.score - mn + 1) / (Math.max(...c.rows.map((x) => x.score)) - mn + 1) : r.score / mx; return `<div class="${r === c.best ? 'best' : ''}" title="GW${r.g}"><i style="height:${Math.max(4, Math.round(h * 52))}px"></i>${r.g}</div>`; }).join('');
      const why = c.c.name === 'bboost' ? `Your bench projects ${f1(c.best.score)} pts that week` : c.c.name === '3xc' ? `${name(c.best.bx.xi.slice().sort((a, b) => P(b.e, c.best.g) - P(a.e, c.best.g))[0].e)} projects ${f1(c.best.score)} pts` : `Your XI projects lowest that week (${f1(c.best.bx.sum)} pts${c.best.blanks ? `, ${c.best.blanks} blanking` : ''})`;
      return `<div class="move"><div class="h"><b>${label}</b><span class="pill p-core">Best: GW${c.best.g}</span></div><div class="alt">${why}. Expires after GW${c.c.stop_event}.</div><div class="bars">${bars}</div></div>`;
    }).join('') || '<p class="muted">No chips left in the current window.</p>';

    // News
    const ago = (d) => { if (!d || isNaN(d)) return ''; const h = Math.round((Date.now() - d) / 36e5); return h < 24 ? h + 'h ago' : Math.round(h / 24) + 'd ago'; };
    const link = (it) => `<span class="kind k-${it.kind}">${{ news: 'News', leak: 'Leak', social: 'Social' }[it.kind] || 'News'}</span><a href="${esc(it.link)}" target="_blank" rel="noopener">${esc(it.title)}</a> <small class="muted">${esc(it.src)} · ${ago(it.date)}</small>`;
    const mineSet = new Set(sq.map((s) => s.e.id));
    const watch = [...sq.map((s) => s.e), ...moves.slice(0, 6).flatMap((m) => m.cands.slice(0, 1).map((c) => c.c))].filter((e, i, a) => a.indexOf(e) === i && A.NM[e.id]);
    const newsRows = watch.map((e) => { const n = A.NM[e.id]; const lab = n.signal === 'neg' ? ['sell', 'Concern'] : n.signal === 'pos' ? ['core', 'Positive'] : ['keep', 'Mentioned']; return `<div class="move"><div class="h"><b>${name(e)} <small class="muted">${tm(e)}${A.sq.some((s) => s.e === e) ? '' : ' · transfer target'}</small></b><span class="pill p-${lab[0]}">${lab[1]}</span></div>${n.hits.slice(0, 3).map((it) => `<div class="alt">${link(it)}</div>`).join('')}${n.signal === 'neg' && e.status === 'a' ? '<div class="alt"><b>Effect:</b> FPL has no flag yet, so projections for the next two gameweeks are reduced.</div>' : n.signal === 'pos' && e.status === 'd' ? '<div class="alt"><b>Effect:</b> positive return news, so the chance of playing is raised.</div>' : ''}</div>`; }).join('');
    const whoBy = {}, whoAll = {}; Object.entries(A.NM).forEach(([id, n]) => n.hits.forEach((h) => { const e = A.E[id]; (whoAll[h.title] = whoAll[h.title] || []).push(e); if (!whoBy[h.title] || (mineSet.has(e.id) && !mineSet.has(whoBy[h.title].id))) whoBy[h.title] = e; }));
    const mineIds = new Set(sq.map((s) => s.e.id));
    const KN = { news: 'News', leak: 'Leak', social: 'Social' };
    const ncards = NEWS.items.slice(0, 160).map((it) => { const who = whoBy[it.title], all = whoAll[it.title] || []; const qtxt = (it.title + ' ' + it.src + ' ' + all.map((e) => `${e.web_name} ${e.first_name} ${e.second_name} ${T[e.team].name} ${T[e.team].short_name}`).join(' ')).toLowerCase(); const inj = NEG.test(it.title) || INCIDENT.test(it.title);
      const k = [it.kind, all.some((e) => mineIds.has(e.id)) ? 'mine' : '', inj ? 'inj' : '', it.excl ? 'excl' : ''].filter(Boolean).join(' ');
      return `<a class="ncard" data-k="${k}" data-src="${esc(it.src)}" data-q="${esc(qtxt)}" href="${esc(it.link)}" target="_blank" rel="noopener"><div class="nph">${newsPic(it, who)}</div><div class="nb"><div class="nt">${it.excl ? '<span class="kind k-excl">Exclusive</span>' : `<span class="kind k-${it.kind}">${KN[it.kind] || 'News'}</span>`}${all.slice(0, 3).map((e) => `<span class="pill ${inj ? 'p-sell' : mineIds.has(e.id) ? 'p-core' : 'p-keep'}" title="${esc(T[e.team].name)}${mineIds.has(e.id) ? ' · in your squad' : ''}">${esc(e.web_name)} <small>${T[e.team].short_name}</small></span>`).join('')}${all.length > 3 ? `<span class="pill p-keep">+${all.length - 3}</span>` : ''}</div><b>${esc(it.title)}</b><small class="muted">${esc(it.src)}${it.date && !isNaN(it.date) ? ' · ' + ago(it.date) : ''}</small></div></a>`; }).join('');
    const NF = [['all', 'All'], ['excl', 'Exclusives'], ['mine', 'Your players'], ['inj', 'Injuries'], ['leak', 'Leaks & line-ups'], ['social', 'Journalists & social']];
    const colOf = (k, n) => NEWS.items.filter((it) => it.kind === k).slice(0, n).map((it) => `<li class="nli">${it.img ? `<img src="${esc(it.img)}" alt="" loading="lazy" referrerpolicy="no-referrer">` : '<span class="noimg sm"></span>'}<span>${link(it)}</span></li>`).join('') || '<li class="muted">Nothing from these sources right now.</li>';
    const srcChips = (NEWS.feeds || []).map(([k, src]) => `<span class="${NEWS.okBy[src] ? 'on' : ''}" title="${NEWS.okBy[src] ? 'Read OK' : 'Could not be read this time'}">${NEWS.okBy[src] ? '✓' : '✕'} ${esc(src)}</span>`).join('');
    const leakFlags = watch.filter((e) => A.NM[e.id].leak);

    // Differentials
    const inSqIds = new Set(sq.map((s) => s.e.id));
    const maxBudget = {}; sq.forEach((s) => { const t = s.e.element_type; maxBudget[t] = Math.max(maxBudget[t] || 0, s.sell + A.bank); });
    const dList = A.diffs.filter((d) => !inSqIds.has(d.e.id)).slice(0, 12);
    const myDiffs = sq.filter((s) => A.isDiff(s.e));
    const diffCards = dList.map((d) => { const e = d.e; const n = A.NM[e.id]; const net = e.transfers_in_event - e.transfers_out_event; const ok = e.now_cost <= (maxBudget[e.element_type] || 0);
      return `<div class="move diffc"><div class="h"><span><b>${name(e)}</b> <small class="muted">${POS[e.element_type]} · ${tm(e)} · ${money(e.now_cost)}</small></span><span class="pill p-diff">${e.selected_by_percent}% owned</span></div>
<div class="alt">Form ${e.form} · ${e.points_per_game} pts/game · xGI/90 ${e.expected_goal_involvements_per_90 ?? '–'} · next 5: <b>${f1(d.v)}</b> pts${net > 2000 ? ` · <span class="up">▲ ${Math.round(net / 1000)}k buying</span>` : ''}</div>
<div>${fixChips(A, e.team, 5)}</div>
${n && n.signal !== 'neutral' ? `<div class="alt">${n.signal === 'neg' ? '<span class="dn">News concern:</span> ' : '<span class="up">Positive news:</span> '}${esc(n.hits[0].title)}</div>` : ''}
<div class="alt">${ok ? 'Affordable with one of your current players.' : '<span class="muted">Needs more budget than one swap frees.</span>'}</div><div><button class="try" type="button" data-quick="${e.id}">Bring in</button></div></div>`; }).join('');

    // Deadline emergency alerts: squad players FPL flags, or that news/leaks say may not play
    const dl = nxt ? new Date(nxt.deadline_time) : null;
    const msLeft = dl ? dl - Date.now() : 0;
    const left = msLeft > 0 ? (msLeft > 864e5 ? `${Math.floor(msLeft / 864e5)}d ${Math.floor((msLeft % 864e5) / 36e5)}h` : `${Math.floor(msLeft / 36e5)}h ${Math.floor((msLeft % 36e5) / 6e4)}m`) : '';
    const xiNow = new Set(A.picks.filter((p) => p.position <= 11).map((p) => p.element));
    // Deadline alerts. Priority: sudden new incidents in the last 72h (often before FPL flags them),
    // then fresh doubts from news/leaks; injuries FPL already flags are listed separately as known.
    const agoH = (h) => (h < 1 ? 'just now' : h < 24 ? `${Math.round(h)}h ago` : `${Math.round(h / 24)}d ago`);
    const srcLab = (h) => (h.kind === 'leak' ? 'Leak' : h.kind === 'social' ? 'Social media' : 'News');
    const hl = (h) => `<span class="kind k-${h.kind}">${srcLab(h)}</span><a href="${esc(h.link)}" target="_blank" rel="noopener">${esc(h.title)}</a> <small class="muted">${esc(h.src)} · ${agoH(h.ageH)}</small>`;
    const alerts = sq.map((s) => {
      const e = s.e, n = A.NM[e.id], c = e.chance_of_playing_next_round;
      const flagged = ['i', 's', 'u', 'n', 'd'].includes(e.status);
      const LISTY = /calendar|megathread|rate my team|\brmt\b|team reveal|\bpicks?\b.*\bgw\d|fixture (?:ticker|run|swing)|wildcard (?:draft|team)|daily discussion|price changes?/i;
      const fresh0 = n ? n.hits.filter((h) => h.tone === 'neg' && h.ageH <= 72 && !LISTY.test(h.title)).sort((x, y) => x.ageH - y.ageH) : [];
      const fresh = fresh0.some((h) => h.kind !== 'social') || fresh0.filter((h) => h.kind === 'social').length >= 2 ? fresh0 : [];
      const incidents = fresh.filter((h) => h.incident);
      let level = null, heads = [];
      const conf = flagged || (n && n.confirmed);
      if (incidents.length && conf) { level = 'breaking'; heads = incidents.slice(0, 2); }
      else if (fresh.length && !flagged && conf) { level = 'doubt'; heads = fresh.slice(0, 2); }
      else if (fresh.length && !flagged) { level = 'check'; heads = fresh.slice(0, 1); }
      else if (flagged) level = 'known';
      if (!level) return null;
      const starter = xiNow.has(e.id), cap = s.p.is_captain, vc = s.p.is_vice_captain;
      const acts = [];
      if (level === 'check') return { s, e, level, heads, fpl: 'Only one source so far and FPL has not flagged him. No change suggested yet.', starter, cap, vc, acts, prio: 0.5 * (cap ? 3 : starter ? 2 : 0.5) };
      if (cap || vc) { const alt = now.xi.filter((x) => x.e.id !== e.id).sort((a, b) => P(b.e, g0) - P(a.e, g0))[0]; if (alt) acts.push(`${cap ? 'Captain' : 'Vice-captain'}: switch to <b>${name(alt.e)}</b> <small class="muted">${f1(P(alt.e, g0))} pts projected vs ${f1(P(e, g0))} if he plays</small>`); }
      if (starter) { const bx = A.bestXIof(sq.filter((x) => x !== s), g0); const ins = bx.xi.filter((x) => !xiNow.has(x.e.id)); if (ins.length) acts.push(`Bench him and start <b>${ins.map((x) => name(x.e)).join(', ')}</b>`); }
      const mv = moves.find((m) => m.s === s);
      if (mv && mv.cands.length) acts.push(`${A.ft > 0 ? 'Free transfer' : 'Transfer (−4)'}: <b>${name(mv.cands[0].c)}</b> <small class="muted">${tm(mv.cands[0].c)} · ${money(mv.cands[0].c.now_cost)}</small> <button class="try" type="button" data-try="${e.id}:${mv.cands[0].c.id}">Try it</button>`);
      const fpl = flagged ? `FPL: ${esc(e.news || (c != null ? c + '% chance of playing' : 'flagged'))}` : 'FPL has not flagged him yet';
      return { s, e, level, heads, fpl, starter, cap, vc, acts, prio: ({ breaking: 3, doubt: 2, known: 1, check: 0.5 })[level] * (cap ? 3 : starter ? 2 : 0.5) };
    }).filter(Boolean).sort((a, b) => b.prio - a.prio);
    const liveAl = alerts.filter((a) => a.level !== 'known' && a.level !== 'check');
    const checks = alerts.filter((a) => a.level === 'check');
    const known = alerts.filter((a) => a.level === 'known');
    const urgent = liveAl.filter((a) => a.starter || a.cap || a.vc);
    const breaking = liveAl.some((a) => a.level === 'breaking');
    const role = (a) => (a.cap ? 'your captain' : a.vc ? 'your vice-captain' : a.starter ? 'in your starting XI' : 'on your bench');
    const knownXI = known.filter((a) => a.starter || a.cap || a.vc);
    const alertsHtml = alerts.length ? `<div class="alerts ${liveAl.length || knownXI.length ? '' : 'calm'} ${msLeft > 0 && msLeft < 3 * 36e5 && (urgent.length || knownXI.length) ? 'hot' : ''}"><div class="ah"><b>${breaking ? '⚠ Breaking: deadline alerts' : liveAl.length ? '⚠ Deadline alerts' : knownXI.length ? `⚠ Deadline check: ${knownXI.length} flagged player${knownXI.length > 1 ? 's' : ''} in your XI` : 'Deadline check'}</b>${left ? `<span>GW${g0} deadline in <b>${left}</b></span>` : ''}</div>
${liveAl.length ? liveAl.map((a) => `<div class="al ${a.starter || a.cap || a.vc ? '' : 'low'}"><div><span class="pill ${a.level === 'breaking' ? 'p-sell' : 'p-up'}">${a.level === 'breaking' ? 'New incident' : 'Doubt'}</span> <b>${name(a.e)}</b> <small class="muted">${POS[a.e.element_type]} · ${tm(a.e)} · ${role(a)}</small></div>
${a.heads.map((h) => `<div class="alt">${hl(h)}</div>`).join('')}<div class="alt"><small>${a.fpl}</small></div>
${a.starter || a.cap || a.vc ? `<ul class="acts">${a.acts.map((x) => `<li>${x}</li>`).join('')}</ul>` : '<div class="alt">On your bench, so no action is needed unless you planned to start him.</div>'}</div>`).join('') : '<div class="alt">No new incidents or doubts about your players in the last 72 hours.</div>'}
${checks.length ? `<div class="known"><b>Check the news:</b> ${checks.map((a) => `${name(a.e)} <small class="muted">(${a.heads.map((h) => `<a href="${esc(h.link)}" target="_blank" rel="noopener">${esc(h.title.length > 70 ? h.title.slice(0, 68) + '…' : h.title)}</a> · ${esc(h.src)}`).join('')}; one source, FPL hasn't flagged him, no change suggested)</small>`).join(' · ')}</div>` : ''}
${known.length ? `<div class="known"><b>Already known:</b> ${known.map((a) => `${name(a.e)} <small class="muted">(${esc(a.e.news || a.e.status)}${a.starter ? ', starting' : ''})</small>`).join(' · ')}</div>` : ''}
${urgent.length || knownXI.length ? '<p class="note" style="margin:6px 0 0">Re-check right before the deadline with ⟳: news, leaks and FPL flags are re-read each time.</p>' : ''}</div>` : `<div class="alerts clear"><div class="ah"><b>✓ Deadline check: all clear</b>${left ? `<span>GW${g0} deadline in <b>${left}</b></span>` : ''}</div><div class="alt">No injury flags on your players and no worrying news or leaks in the last 72 hours. Re-check with ⟳ before the deadline.</div></div>`;

    if (false && urgent.length) plan.unshift(['Urgent', `${urgent.map((a) => `<b>${name(a.e)}</b>`).join(', ')}: ${breaking ? 'new incident reported' : 'fresh doubt'}`, { lab: 'See alert', attr: 'data-act="alert"' }]);

    // v3.37 Season chart: bars = points above / below the gameweek average (diverging from a centre line);
    // gold line = overall rank (higher on the chart = better rank). Click a column for that week's team.
    const W = 440, H = 306, PADT = 16, PH = 166, AX = PADT + PH + 26, RT = AX + 34, RH = 40, bw = W / Math.max(1, hc.length);
    const dif = hc.map((h) => h.points - avgOf(h.event));
    const mUp = Math.max(6, ...dif), mDn = Math.max(6, ...dif.map((d) => -d)), s = PH / (mUp + mDn), y0 = PADT + mUp * s;
    const rks = hc.map((h) => h.overall_rank).filter((r) => r > 0), lr = (r) => Math.log10(Math.max(1, r));
    const rMin = rks.length ? Math.min(...rks) : 1, rMax = rks.length ? Math.max(...rks) : 10, rSpan = Math.max(.05, lr(rMax) - lr(rMin));
    const yR = (r) => RT + 4 + ((lr(r) - lr(rMin)) / rSpan) * (RH - 8);
    const kr = (r) => (r >= 1e6 ? (r / 1e6).toFixed(1) + 'M' : r >= 1e3 ? Math.round(r / 1e3) + 'k' : String(r));
    const bars = hc.map((h, i) => { const d = dif[i], bwi = Math.max(5, Math.min(24, bw * .6)), x = i * bw + (bw - bwi) / 2, hh = Math.max(2, Math.abs(d) * s), y = d >= 0 ? y0 - hh : y0, cx = i * bw + bw / 2;
      return `<rect x="${x}" y="${y}" width="${bwi}" height="${hh}" rx="${Math.min(4, bwi / 2)}" class="bar" style="animation-delay:${i * 30}ms" fill="${d >= 0 ? 'url(#sgUp)' : 'url(#sgDn)'}"></rect><text x="${cx}" y="${d >= 0 ? y - 5 : y + hh + 12}" text-anchor="middle" class="lbl ${d >= 0 ? 'hi' : 'lo'}">${d > 0 ? '+' : ''}${d}</text><text x="${cx}" y="${AX + 4}" text-anchor="middle" class="ax">${bw >= 34 ? 'GW' : ''}${h.event}</text><text x="${cx}" y="${AX + 16}" text-anchor="middle" class="rk">${h.points} pts</text><rect class="hit" data-sgw="${h.event}" x="${i * bw}" y="0" width="${bw}" height="${H}" fill="transparent"><title>GW${h.event}: ${h.points} pts, average ${avgOf(h.event)} (${d >= 0 ? '+' : ''}${d})${h.overall_rank ? `, overall rank ${h.overall_rank.toLocaleString()}` : ''}. Click to see the team.</title></rect>`; }).join('');
    const rPts = hc.map((h, i) => (h.overall_rank ? [i * bw + bw / 2, yR(h.overall_rank), h.overall_rank] : null)).filter(Boolean);
    const rLine = rPts.length > 1 ? `<polyline points="${rPts.map((p) => p[0] + ',' + p[1]).join(' ')}" class="rline"/>${rPts.map((p, k) => `<circle cx="${p[0]}" cy="${p[1]}" r="${k === rPts.length - 1 ? 3.6 : 2.4}" class="rdot"/>`).join('')}<text x="${W - 2}" y="${rPts[rPts.length - 1][1] + 4}" text-anchor="end" class="rlab">${kr(rPts[rPts.length - 1][2])}</text><text x="${Math.max(2, rPts[0][0] - bw / 2 + 2)}" y="${RT - 4}" class="rlab dim">Overall rank · ${kr(rPts[0][2])} → ${kr(rPts[rPts.length - 1][2])}</text>` : '';
    const seasonChart = `<svg class="schart sdiv" viewBox="0 0 ${W} ${H}" width="100%" role="img" aria-label="Points above or below the gameweek average, with overall rank"><defs><linearGradient id="sgUp" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#6fe0a8"/><stop offset="1" stop-color="#2f9a68"/></linearGradient><linearGradient id="sgDn" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#e2566a"/><stop offset="1" stop-color="#ff8a8a"/></linearGradient></defs><line x1="0" x2="${W}" y1="${y0}" y2="${y0}" class="base"/><rect x="0" y="${RT - 1}" width="${W}" height="${RH + 2}" rx="6" class="rband"/>${bars}${rLine}</svg>`;

    // League table
    const myClubs = A.club;
    const tableRows = A.table.map((r) => `<tr class="${myClubs[r.id] ? 'mine' : ''}"><td class="n">${r.pos}</td><td><span class="tkc">${crest(r.id)}<b>${esc(T[r.id].name)}</b>${myClubs[r.id] ? ` <small class="muted">(${myClubs[r.id]} of yours)</small>` : ''}</span></td><td class="n">${r.P}</td><td class="n">${r.W}</td><td class="n">${r.D}</td><td class="n">${r.L}</td><td class="n">${r.GF - r.GA > 0 ? '+' : ''}${r.GF - r.GA}</td><td class="n"><b>${r.Pts}</b></td><td><span class="form">${r.form.slice(-5).map((x) => `<i class="f${x}">${x}</i>`).join('')}</span></td><td>${fixChips(A, r.id, 5)}</td></tr>`).join('');
    const runs = A.table.map((r) => { let s = 0, n = 0; for (let g = g0; g < g0 + 5; g++) (A.fxBy[r.id + '-' + g] || []).forEach((f) => { s += f.diff; n++; }); return { r, avg: n ? s / n : 9, n }; }).sort((a, b) => a.avg - b.avg);

    const NAVI = { home: '<path d="M4 11l8-7 8 7v9h-5v-6H9v6H4z"/>', team: '<path d="M8 3l2 1.5q2 1 4 0L16 3l6 4-2.5 4.5L17 10v11H7V10l-2.5 1.5L2 7z"/>', live: '<circle cx="12" cy="12" r="3.5"/><path d="M5.6 5.6a9 9 0 0 0 0 12.8M18.4 5.6a9 9 0 0 1 0 12.8" fill="none" stroke="currentColor" stroke-width="2"/>', fix: '<path d="M4 5h16v15H4zM4 9h16M9 3v4M15 3v4" fill="none" stroke="currentColor" stroke-width="2"/>', news: '<path d="M4 5h13v14H6a2 2 0 0 1-2-2zM17 9h3v8a2 2 0 0 1-2 2M7 9h7M7 13h7" fill="none" stroke="currentColor" stroke-width="2"/>' };
    $('#nav').innerHTML = '<span class="nink" aria-hidden="true"></span>' + VIEWS.filter(([id]) => id !== 'live' || A.live).map(([id, l]) => `<a href="#" data-t="${id}"><svg viewBox="0 0 24 24" aria-hidden="true" fill="currentColor">${NAVI[id]}</svg><span>${l}</span></a>`).join('') + '<span class="navsub" id="navsub"></span>';
    $('#navsub').onclick = (ev) => { const b = ev.target.closest('[data-sub]'); if (b) { ev.preventDefault(); showView(VIEW, b.dataset.sub); } };
    R.querySelectorAll('nav a').forEach((a) => (a.onclick = (ev) => { ev.preventDefault(); showView(a.dataset.t); }));
    // Dashboard pieces
    const strip = (h) => h.replace(/<button[\s\S]*?<\/button>/g, '').replace(/<[^>]+>/g, '');
    const shortH = (h) => h.replace(/<a [^>]*>/g, '').replace(/<\/a>/g, '');
    const slides = []; const seenT = new Set();
    NEWS.items.filter((it) => it.img).concat(NEWS.items.filter((it) => !it.img)).forEach((it) => { if (slides.length < 10 && !seenT.has(it.title)) { seenT.add(it.title); slides.push({ it, who: whoBy[it.title], ago: ago(it.date) }); } });
    const newsSlider = slides.length ? `<div class="hnl">${slides.slice(0, 4).map((s) => `<a class="hni" href="${esc(s.it.link)}" target="_blank" rel="noopener"><span class="hnp nph">${newsPic(s.it, s.who)}</span><span class="hnt"><b>${esc(s.it.title)}</b><small>${s.it.excl ? '<i class="ex">Exclusive</i>' : ''}${s.who ? `<i class="${s.tone === 'neg' ? 'neg' : s.tone === 'pos' ? 'pos' : ''}">${esc(s.who.web_name)}</i>` : ''}${esc(s.it.src)}${s.ago ? ' · ' + s.ago : ''}</small></span></a>`).join('')}</div>` : '<p class="muted">No headlines could be read right now.</p>';
    const flaggedN = sq.filter((s) => s.e.status !== 'a').length;
    const verd = sq.map((s) => A.verdict(s)[0]); const nUp = verd.filter((v) => v === 'sell' || v === 'up').length;
    const topMove = moves.find((m) => m.cands.length && m.gain >= A.CONV);
    const cHist = hc[hc.length - 1], pHist = hc[hc.length - 2];
    const dPts = cHist && pHist ? cHist.points - pHist.points : 0;
    const proj = now.sum + (caps[0] ? P(caps[0].e, g0) : 0);
    const rmv = hc.length > 1 ? hc[hc.length - 2].overall_rank - last.overall_rank : 0;
    const homeHtml = `<section class="s home" id="s-home">
${MYID && MYID !== A.id ? `<div class="viewing"><span>Viewing <b>${esc(entry.name)}</b> · ${esc(entry.player_first_name)} ${esc(entry.player_last_name)} · ID ${A.id}</span><button class="try" type="button" data-back="1">Back to my team</button></div>` : ''}
${(() => { const rg = REGION[entry.player_region_id], code = rg ? rg[0] : '', ini = (entry.name || '?').replace(/[^\p{L}\p{N} ]/gu, '').split(/\s+/).filter(Boolean).map((w) => w[0]).join('').slice(0, 3).toUpperCase() || '?';
  return `<div class="pph hbn${rg ? ' fl' : ''}${code === 'eg' ? ' egy' : ''}"${rg ? ` style="--flagb:url('${flagPng(code)}')"` : ''}>${rg ? `<i class="pflag l" aria-hidden="true"></i><i class="pflag r" aria-hidden="true"></i><i class="pflag c wv" aria-hidden="true">${FLAGW}</i><i class="pflag t" aria-hidden="true"></i>` : ''}
<div class="hbav" aria-hidden="true"><i class="hblion"></i>${rg ? `<img class="hbfl" src="https://flagcdn.com/w80/${code}.png" alt="">` : ''}</div>
<div class="hbtx"><small class="eyebrow">${nxt ? `GW${g0} deadline` : 'Season complete'}</small><h2>${esc(entry.name)}</h2><span class="hbsub">${esc(entry.player_first_name)} ${esc(entry.player_last_name)}${rg ? ' · ' + esc(entry.player_region_name || rg[1]) : ''} · ID ${A.id}</span></div>
<div class="hbkp"><div><small>Overall rank</small><b>${(entry.summary_overall_rank || 0).toLocaleString()}</b></div><div><small>Points</small><b>${entry.summary_overall_points}</b></div>${left ? `<span class="cdpill ${msLeft < 864e5 ? 'dn' : ''}" data-dl="${+dl}">${cdTxt(msLeft)} left</span>` : ''}</div></div>`; })()}
<div class="hero hero2"><div class="hl deadline-head"><small class="eyebrow">${nxt ? `GW${g0} DEADLINE` : 'SEASON COMPLETE'}</small></div>
<div class="herok"><div><small>Total points</small><b data-count="${entry.summary_overall_points}">${entry.summary_overall_points}</b><span class="hs2">${last && last.event ? `GW${last.event}: ${last.points} pts` : ''}</span></div><div><small>Overall rank</small><b data-count="${entry.summary_overall_rank || 0}">${(entry.summary_overall_rank || 0).toLocaleString()}</b><span class="hs2 ${rmv > 0 ? 'up' : rmv < 0 ? 'dn' : ''}">${rmv > 0 ? '▲' : rmv < 0 ? '▼' : '–'} ${Math.abs(rmv).toLocaleString()} places</span></div><div><small>Projected GW${g0}</small><b>${f1(proj)}</b><span class="hs2">${caps[0] ? 'Captain ' + esc(caps[0].e.web_name) : ''}</span></div><div><small>Bank</small><b>${money(A.bank)}</b><span class="hs2">to spend</span></div><div title="${A.ftExact ? 'Taken from your FPL account.' : 'Estimated from this manager’s transfer history. Log in to FPL as this manager for the exact number.'}"><small>Free transfers</small><b>${A.ft}</b><span class="hs2">${A.ftExact ? 'confirmed by FPL' : 'estimated'} · −4 per extra</span></div></div></div>
${A.live && (A.live.live || !A.cur.finished) ? `<button class="livestrip" type="button" data-view="live"><span id="livebar" class="lsx">${liveBar(A.live)}</span></button>` : ''}
<div class="hgrid">
<div class="card hc alc">${alertsHtml}</div>
<div class="card hc do"><div class="th"><h3>Do this now</h3><span class="muted">${plan.length} action${plan.length === 1 ? '' : 's'} for GW${g0}</span></div>
<div class="arows">${plan.slice(0, 3).map(([t, h, a]) => `<div class="arow t-${t.toLowerCase()}"><span class="tag">${t}</span><span class="atx">${h}</span>${a ? `<button class="cta" type="button" ${a.attr}>${a.lab}</button>` : ''}</div>`).join('')}</div>
${plan.length > 3 ? `<details class="more"><summary>${plan.length - 3} more</summary><div class="arows">${plan.slice(3).map(([t, h, a]) => `<div class="arow t-${t.toLowerCase()}"><span class="tag">${t}</span><span class="atx">${h}</span>${a ? `<button class="cta" type="button" ${a.attr}>${a.lab}</button>` : ''}</div>`).join('')}${A.diffs && A.diffs[0] ? `<div class="arow t-diff"><span class="tag">Differential</span><span class="atx"><b>${name(A.diffs[0].e)}</b> <small class="muted">${T[A.diffs[0].e.team].short_name} · ${money(A.diffs[0].e.now_cost)} · ${A.diffs[0].e.selected_by_percent}% owned</small></span><button class="cta" type="button" data-quick="${A.diffs[0].e.id}">Bring in</button></div>` : ''}</div></details>` : ''}</div>
<div class="card hc lgc" id="hl-box">${homeLeagues(A)}</div>
<div class="card hc gwc">${gwSection(A) || '<div class="th"><h3>This gameweek</h3></div><p class="muted">No finished gameweek yet.</p>'}</div>
<div class="card hc seast"><div class="th"><h3>Season so far</h3><div class="slg"><span><i style="background:#45d08f"></i>Above avg</span><span><i style="background:#e2566a"></i>Below avg</span><span><i style="background:#f6c343;height:3px;border-radius:2px"></i>Overall rank</span></div></div>
${seasonChart}<p class="muted fine">Click a bar to open that week's team.</p></div>
<div class="card hc newst"><div class="th"><h3>Latest news</h3><button class="lnk2" type="button" data-view="news">All news</button></div>${newsSlider}</div>
</div>
</section>`;
    const doRow = ([t, h, a]) => `<div class="arow t-${t.toLowerCase()}"><span class="tag">${t}</span><span class="atx">${h}</span>${a ? `<button class="cta" type="button" ${a.attr}>${a.lab}</button>` : ''}</div>`;
    const doNow = `<p class="note tn">${plan.length} action${plan.length === 1 ? '' : 's'} for GW${g0}, most important first</p><div class="arows dotab">${plan.map(doRow).join('')}${A.diffs && A.diffs[0] ? doRow(['Differential', `<b>${name(A.diffs[0].e)}</b> <small class="muted">${T[A.diffs[0].e.team].short_name} · ${money(A.diffs[0].e.now_cost)} · ${A.diffs[0].e.selected_by_percent}% owned</small>`, { attr: `data-quick="${A.diffs[0].e.id}"`, lab: 'Bring in' }]) : ''}</div>`;
    A.html = { moveCards, diffCards, chipCards, doNow };
    const gp = R.getElementById('gwpill'); if (gp) { const tickGw = () => { const ms = nxt ? new Date(nxt.deadline_time) - Date.now() : 0; const d = Math.floor(ms / 864e5), h = Math.floor(ms % 864e5 / 36e5), m = Math.floor(ms % 36e5 / 6e4); gp.innerHTML = nxt ? `<b>GW${g0}</b> <span class="cdt">${ms > 0 ? cdTxt(ms).replace(ms >= 864e5 ? / (\d\dm \d\ds)$/ : / (\d\ds)$/, '<i class="cs"> $1</i>') : 'deadline passed'}</span>` : 'Season complete'; gp.classList.toggle('hot', ms > 0 && ms < 864e5); }; tickGw(); gp.hidden = false; clearInterval(window.__fplGwT); window.__fplGwT = setInterval(() => { if (!document.getElementById(PID)) return clearInterval(window.__fplGwT); tickGw(); R.querySelectorAll('[data-dl]').forEach((x) => { const ms = +x.dataset.dl - Date.now(); x.textContent = ms > 0 ? cdTxt(ms) + ' left' : 'Deadline passed'; x.classList.toggle('dn', ms < 864e5); }); }, 1000); }
    try { const cap = caps[0] && caps[0].e; const k = cap && JST[T[cap.team].short_name]; const rt = R.querySelector('.root'); if (k && rt) { rt.style.setProperty('--c1', k[0]); rt.style.setProperty('--c2', k[3] && k[3] !== k[0] ? k[3] : k[1]); } } catch (e) {}
    $('#sub').textContent = `${entry.name} · ${entry.player_first_name} ${entry.player_last_name} · live data ${A.loadedAt.toLocaleTimeString()}${A.live && A.live.live ? ' · live points refresh every 15 seconds' : ''}`;

    out.innerHTML = `${homeHtml}
${(() => { NEWSC = {}; const h = liveSection(A); SCORES = Object.assign({}, SCORES, NEWSC); return h; })()}
<section class="s" id="s-squad"><h2>Squad status</h2><p class="sub">Next 5 fixtures by difficulty (green easy, red hard) · H home, A away.</p>
<div class="tw"><table><thead><tr><th>Player</th><th class="n">Price</th><th class="n">Form</th><th class="n">PPG</th><th class="n">Pts</th><th class="n">xGI/90</th><th class="n">Mins</th><th>Next 5</th><th class="n">GW${g0}</th><th class="n">Next 5</th><th class="n">Net tr.</th><th>Verdict</th></tr></thead><tbody>${squadRows}</tbody></table></div><div class="vleg"><b>Verdict</b><span><span class="pill p-core">Core</span>top 8% of his position for the next 5 GWs: keep</span><span><span class="pill p-keep">Keep</span>fine for now, no clearly better buy</span><span><span class="pill p-up">Upgrade</span>a replacement you can afford gains 2.5–5 pts over 5 GWs</span><span><span class="pill p-sell">Sell</span>a replacement gains 5+ pts over 5 GWs</span><span><span class="pill p-out">Out</span>injured, suspended or not expected to play</span></div></section>
<section class="s plan3" id="s-planner"><div id="pl-slide"></div><div id="planner"></div></section>
<section class="s" id="s-news"><h2>News</h2><p class="sub">Premier League only · last 48 h · ${NEWS.ok} of ${NEWS.total} sources read</p>
<div class="nfq"><input id="nf-q" placeholder="Search any player or club…" autocomplete="off" aria-label="Search news by player or club"></div><div class="nfbar"><div class="seg tabs nfilt" role="tablist">${NF.map(([k, l], i) => `<button type="button" role="tab" class="${i ? '' : 'on'}" aria-selected="${!i}" data-nf="${k}">${l}<i class="nfc"></i></button>`).join('')}</div><label class="wcl">Source <select id="nf-src" aria-label="Source"><option value="">All sources</option>${[...new Set(NEWS.items.map((it) => it.src))].sort().map((s) => `<option value="${esc(s)}">${esc(s)} (${NEWS.items.filter((it) => it.src === s).length})</option>`).join('')}</select></label></div>
<details class="srcd top"><summary>Sources · ${NEWS.ok} of ${NEWS.total} read</summary><div class="srcs">${srcChips}<span class="${PAST && PAST.s['2024-25'] ? 'on' : ''}" title="Season totals used by the projection model">${PAST && PAST.s['2024-25'] ? '✓' : '✕'} Past seasons 2024/25 · 2023/24 (FPL data archive, GitHub)</span></div><div class="links"><a href="https://x.com/FabrizioRomano" target="_blank" rel="noopener">Fabrizio Romano on X</a><a href="https://x.com/David_Ornstein" target="_blank" rel="noopener">David Ornstein on X</a><a href="https://x.com/OfficialFPL" target="_blank" rel="noopener">Official FPL on X</a></div></details>
${NEWS.ok === 0 ? '<div class="err">No news source could be reached, so recommendations use FPL data only. Try again in a few minutes.</div>' : ''}
<div class="ngrid" id="ngrid">${ncards || '<p class="muted">No Premier League stories in the last 48 hours.</p>'}</div><p class="muted nfempty" id="nf-empty" hidden>No stories in this filter from the last 48 hours. Try All, or check again closer to the deadline.</p>
${newsRows ? `<h3 class="h3">Affecting your team</h3><div class="grid2">${newsRows}</div>` : ''}
<details class="srcd" hidden><summary>Sources · ${NEWS.ok} of ${NEWS.total} read</summary><div class="srcs">${srcChips}<span class="${PAST && PAST.s['2024-25'] ? 'on' : ''}" title="Season totals used by the projection model">${PAST && PAST.s['2024-25'] ? '✓' : '✕'} Past seasons 2024/25 · 2023/24 (FPL data archive, GitHub)</span></div><div class="links"><a href="https://x.com/FabrizioRomano" target="_blank" rel="noopener">Fabrizio Romano on X</a><a href="https://x.com/David_Ornstein" target="_blank" rel="noopener">David Ornstein on X</a><a href="https://x.com/OfficialFPL" target="_blank" rel="noopener">Official FPL on X</a></div></details>
</section>
${rotHtml(A)}
<section class="s" id="s-table"><h2>Premier League table & fixture runs</h2><p class="sub">Calculated from finished matches. Rows marked on the left are clubs you own. Easiest next-5 runs: ${runs.slice(0, 5).map((x) => `<b>${T[x.r.id].short_name}</b> ${f1(x.avg)}`).join(' · ')}. Hardest: ${runs.slice(-3).map((x) => `${T[x.r.id].short_name} ${f1(x.avg)}`).join(' · ')}.</p>
<div class="tw"><table><thead><tr><th class="n">#</th><th>Club</th><th class="n">P</th><th class="n">W</th><th class="n">D</th><th class="n">L</th><th class="n">GD</th><th class="n">Pts</th><th>Last 5</th><th>Next 5</th></tr></thead><tbody>${tableRows}</tbody></table></div>
<p class="note">Projections are estimates from public FPL data, not guarantees. Run the analyst again after each gameweek: everything reloads live.</p></section>`;
    planInit(A); renderPlanner();
    showView(VIEW); initSliders();
    LASTA = A; idsLoaded(A); refreshLeague(A);
    if (RUNOPT.quiet) out.scrollTop = RUNOPT.top;
    try { priceSnap(); } catch (e) {}
    try { androidSync(A); } catch (e) {}
  }
};

chrome.runtime.onMessage.addListener((m) => { if (m && m.type === 'fpl-analyst-toggle') runFplAnalyst(); });

// Floating launcher button on every FPL page
(() => {
  if (document.getElementById('fpl-analyst-launcher')) return;
  const h = document.createElement('div');
  h.id = 'fpl-analyst-launcher';
  h.style.cssText = 'position:fixed;right:18px;bottom:18px;z-index:2147483000;';
  const r = h.attachShadow({ mode: 'open' });
  r.innerHTML = `<style>button{font:600 14px/1 Inter,system-ui,sans-serif;display:flex;align-items:center;gap:8px;background:#2b0f45;color:#fff;border:1px solid #45d08f;border-radius:999px;padding:8px 16px 8px 8px;cursor:pointer;box-shadow:0 6px 20px rgba(0,0,0,.25)}button:hover{background:#3a1760}button:focus-visible{outline:2px solid #5cc8ad;outline-offset:2px}svg{width:16px;height:16px}</style><button type="button" aria-label="Open Elevn"><svg style="width:22px;height:22px" viewBox="0 0 100 100" aria-hidden="true"><rect width="100" height="100" rx="24" fill="#2b0f45"/><g fill="#45d08f"><circle cx="50" cy="16" r="5.5"/><circle cx="40" cy="30" r="5.5"/><circle cx="60" cy="30" r="5.5"/><circle cx="30" cy="44" r="5.5"/><circle cx="50" cy="44" r="5.5"/><circle cx="70" cy="44" r="5.5"/><circle cx="20" cy="58" r="5.5"/><circle cx="50" cy="58" r="5.5"/><circle cx="80" cy="58" r="5.5"/><circle cx="50" cy="72" r="5.5"/></g><circle cx="50" cy="86" r="5.5" fill="#f6c343"/></svg>Elevn</button>`;
  r.querySelector('button').onclick = () => runFplAnalyst();
  document.documentElement.appendChild(h);
})();

})();
