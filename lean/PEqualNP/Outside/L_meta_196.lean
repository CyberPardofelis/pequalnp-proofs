import Mathlib
import PEqualNP.Defs

namespace LiftGate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma getElem?_nil' {α : Type} (i : ℕ) : ([] : List α)[i]? = none := by
  exact List.getElem?_nil

private lemma getElem?_cons_zero' {α : Type} (a : α) (l : List α) : (a :: l)[0]? = some a := by
  exact List.getElem?_cons_zero

private lemma getElem?_cons_succ' {α : Type} (a : α) (l : List α) (i : ℕ) :
    (a :: l)[Nat.succ i]? = l[i]? := by
  exact List.getElem?_cons_succ

private lemma set_zero' {α : Type} (a b : α) (l : List α) : (a :: l).set 0 b = b :: l := rfl

private lemma set_succ' {α : Type} (a b : α) (l : List α) (i : ℕ) :
    (a :: l).set (Nat.succ i) b = a :: (l.set i b) := rfl

private lemma or_eval (x y : Bool) : GateOp.eval GateOp.or [x, y] = (x || y) := by
  cases x <;> cases y <;> rfl

private lemma or_eval1 (x : Bool) : GateOp.eval GateOp.or [x] = x := by
  cases x <;> rfl

private lemma or_eval_false (x : Bool) : GateOp.eval GateOp.or [x, false] = x := by
  cases x <;> rfl

private lemma step_or (w : List Bool) (p q : ℕ) :
    step w ⟨GateOp.or, [p, q]⟩ = w ++ [w.getD p false || w.getD q false] := by
  show w ++ [GateOp.eval GateOp.or [w.getD p false, w.getD q false]]
      = w ++ [w.getD p false || w.getD q false]
  exact congrArg (fun z : Bool => w ++ [z]) (or_eval _ _)

private lemma step_or1 (w : List Bool) (p : ℕ) :
    step w ⟨GateOp.or, [p]⟩ = w ++ [w.getD p false] := by
  show w ++ [GateOp.eval GateOp.or [w.getD p false]] = w ++ [w.getD p false]
  exact congrArg (fun z : Bool => w ++ [z]) (or_eval1 _)

private lemma foldl_append_single : ∀ (l : List Gate) (g : Gate) (init : List Bool),
    (l ++ [g]).foldl step init = step (l.foldl step init) g := by
  intro l
  induction l with
  | nil => intro g init; rfl
  | cons a l ih =>
    intro g init
    have h1 : ((a :: l) ++ [g]).foldl step init = (l ++ [g]).foldl step (step init a) := by
      show (a :: (l ++ [g])).foldl step init = _
      rw [List.foldl_cons]
    rw [h1, ih, List.foldl_cons]

private lemma foldl_step_append : ∀ (gs : List Gate) (w : List Bool),
    ∃ r : List Bool, gs.foldl step w = w ++ r := by
  intro gs
  induction gs with
  | nil => intro w; exact ⟨[], by rw [List.foldl_nil]; exact (List.append_nil w).symm⟩
  | cons g gs ih =>
    intro w
    obtain ⟨r, hr⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: r, ?_⟩
    rw [List.foldl_cons, hr]
    simp only [step, List.append_assoc]
    rfl

private lemma foldl_step_length : ∀ (gs : List Gate) (w : List Bool),
    (gs.foldl step w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma getD_append_lt {α : Type} : ∀ (l₁ l₂ : List α) (i : ℕ) (d : α),
    i < l₁.length → (l₁ ++ l₂).getD i d = l₁.getD i d := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ i d h
    exact absurd h (by simp only [List.length_nil]; omega)
  | cons a l₁ ih =>
    intro l₂ i d h
    simp only [List.length_cons] at h
    cases i with
    | zero => simp
    | succ i =>
      have h' : i < l₁.length := by omega
      have h2 : (a :: (l₁ ++ l₂)).getD (Nat.succ i) d = (a :: l₁).getD (Nat.succ i) d := by
        simpa only [Nat.succ_eq_add_one, List.getD_cons_succ] using (ih l₂ i d h')
      exact h2

private lemma getD_snoc {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  induction l with
  | nil =>
    show List.getD [a] 0 d = a
    rw [List.getD_cons_zero]
  | cons b l ih =>
    simp only [List.length_cons, List.getD_cons_succ]
    exact ih

private lemma getD_foldl_step : ∀ (gs : List Gate) (w : List Bool) (h : ℕ),
    h < w.length → (gs.foldl step w).getD h false = w.getD h false := by
  intro gs
  induction gs with
  | nil => intro w h _; rfl
  | cons g gs ih =>
    intro w h hw
    rw [List.foldl_cons]
    obtain ⟨r, hr⟩ := foldl_step_append gs (step w g)
    rw [hr]
    have hlt : h < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [getD_append_lt (step w g) r h false hlt]
    simp only [step]
    exact getD_append_lt w _ h false hw

private lemma foldl_mod_eq : ∀ (gs : List Gate) (x : List Bool) (j a h : ℕ),
    gs[j]? = some ⟨GateOp.or, [a, h]⟩ → h < x.length + j →
    (gs.foldl step x).getD h false = false →
    (gs.set j ⟨GateOp.or, [a]⟩).foldl step x = gs.foldl step x := by
  intro gs
  induction gs with
  | nil =>
    intro x j a h hj hh hval
    simp only [getElem?_nil'] at hj
  | cons g gs ih =>
    intro x j a h hj hh hval
    cases j with
    | zero =>
      have hg : g = ⟨GateOp.or, [a, h]⟩ := by
        simp only [getElem?_cons_zero'] at hj
        exact Option.some.inj hj
      have hx : h < x.length := by omega
      have hxh : x.getD h false = false := by
        have h1 : (gs.foldl step (step x g)).getD h false = false := hval
        obtain ⟨r, hr⟩ := foldl_step_append gs (step x g)
        rw [hr] at h1
        have hlt : h < (step x g).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        rw [getD_append_lt (step x g) r h false hlt] at h1
        have h2 : (step x g).getD h false = x.getD h false := by
          simp only [step]
          exact getD_append_lt x _ h false hx
        rw [h2] at h1
        exact h1
      have hstep_eq : step x g = step x ⟨GateOp.or, [a]⟩ := by
        rw [hg]
        show x ++ [GateOp.eval GateOp.or [x.getD a false, x.getD h false]]
            = x ++ [GateOp.eval GateOp.or [x.getD a false]]
        rw [hxh]
        exact congrArg (fun z : Bool => x ++ [z]) ((or_eval_false _).trans (or_eval1 _).symm)
      rw [set_zero']
      simp only [List.foldl_cons]
      exact congrArg (fun w : List Bool => List.foldl step w gs) hstep_eq.symm
    | succ j =>
      have hj' : gs[j]? = some ⟨GateOp.or, [a, h]⟩ := by
        simp only [getElem?_cons_succ'] at hj
        exact hj
      have hh' : h < (step x g).length + j := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      have hval' : (gs.foldl step (step x g)).getD h false = false := hval
      have hrec := ih (step x g) j a h hj' hh' hval'
      rw [set_succ']
      simp only [List.foldl_cons]
      exact hrec

private lemma foldl_mod_getD : ∀ (gs : List Gate) (x : List Bool) (j a h : ℕ),
    gs[j]? = some ⟨GateOp.or, [a, h]⟩ → h < x.length + j →
    ((gs.set j ⟨GateOp.or, [a]⟩).foldl step x).getD h false = (gs.foldl step x).getD h false := by
  intro gs
  induction gs with
  | nil =>
    intro x j a h hj hh
    simp only [getElem?_nil'] at hj
  | cons g gs ih =>
    intro x j a h hj hh
    cases j with
    | zero =>
      have hx : h < x.length := by omega
      have hlt1 : h < (step x g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      have hlt2 : h < (step x ⟨GateOp.or, [a]⟩).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [set_zero']
      simp only [List.foldl_cons]
      rw [getD_foldl_step gs (step x ⟨GateOp.or, [a]⟩) h hlt2]
      rw [getD_foldl_step gs (step x g) h hlt1]
      have e1 : (step x ⟨GateOp.or, [a]⟩).getD h false = x.getD h false := by
        simp only [step]
        exact getD_append_lt x _ h false hx
      have e2 : (step x g).getD h false = x.getD h false := by
        simp only [step]
        exact getD_append_lt x _ h false hx
      rw [e1, e2]
    | succ j =>
      have hj' : gs[j]? = some ⟨GateOp.or, [a, h]⟩ := by
        simp only [getElem?_cons_succ'] at hj
        exact hj
      have hh' : h < (step x g).length + j := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [set_succ']
      simp only [List.foldl_cons]
      exact ih (step x g) j a h hj' hh'

private lemma lift_eval (C : Circuit) (x : List Bool) (m : ℕ) (hm : x.length = m) (j a h : ℕ) :
    (Circuit.mk (C.gates.set j ⟨GateOp.or, [a]⟩ ++ [(⟨GateOp.or, [C.output, h]⟩ : Gate)])
      (m + C.size)).eval x
      = (((C.gates.set j ⟨GateOp.or, [a]⟩).foldl step x).getD C.output false
        || ((C.gates.set j ⟨GateOp.or, [a]⟩).foldl step x).getD h false) := by
  have hlen : ((C.gates.set j ⟨GateOp.or, [a]⟩).foldl step x).length = m + C.size := by
    rw [foldl_step_length (C.gates.set j ⟨GateOp.or, [a]⟩) x, List.length_set, hm]
    rfl
  have hW : ((C.gates.set j ⟨GateOp.or, [a]⟩).foldl step x)
      = (C.gates.set j ⟨GateOp.or, [a]⟩).foldl step x := rfl
  have hw : (Circuit.mk (C.gates.set j ⟨GateOp.or, [a]⟩ ++ [(⟨GateOp.or, [C.output, h]⟩ : Gate)])
      (m + C.size)).wires x
      = ((C.gates.set j ⟨GateOp.or, [a]⟩).foldl step x) ++
        [((C.gates.set j ⟨GateOp.or, [a]⟩).foldl step x).getD C.output false
          || ((C.gates.set j ⟨GateOp.or, [a]⟩).foldl step x).getD h false] := by
    have h1 : (Circuit.mk (C.gates.set j ⟨GateOp.or, [a]⟩ ++ [(⟨GateOp.or, [C.output, h]⟩ : Gate)])
        (m + C.size)).wires x
        = (C.gates.set j ⟨GateOp.or, [a]⟩ ++ [(⟨GateOp.or, [C.output, h]⟩ : Gate)]).foldl step x := rfl
    exact h1.trans ((foldl_append_single (C.gates.set j ⟨GateOp.or, [a]⟩)
      ⟨GateOp.or, [C.output, h]⟩ x).trans (step_or _ _ _))
  have hEval : (Circuit.mk (C.gates.set j ⟨GateOp.or, [a]⟩ ++ [(⟨GateOp.or, [C.output, h]⟩ : Gate)])
      (m + C.size)).eval x
      = ((Circuit.mk (C.gates.set j ⟨GateOp.or, [a]⟩ ++ [(⟨GateOp.or, [C.output, h]⟩ : Gate)])
        (m + C.size)).wires x).getD (m + C.size) false := rfl
  have hSnoc : (((C.gates.set j ⟨GateOp.or, [a]⟩).foldl step x) ++
      [((C.gates.set j ⟨GateOp.or, [a]⟩).foldl step x).getD C.output false
        || ((C.gates.set j ⟨GateOp.or, [a]⟩).foldl step x).getD h false]).getD (m + C.size) false
      = (((C.gates.set j ⟨GateOp.or, [a]⟩).foldl step x).getD C.output false
        || ((C.gates.set j ⟨GateOp.or, [a]⟩).foldl step x).getD h false) := by
    rw [← hlen]
    exact getD_snoc _ _ _
  exact hEval.trans (hw ▸ hSnoc)

end LiftGate

open LiftGate PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_196 :
    ∀ (n j a h : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool),
      C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, h]⟩ →
      h < n + j →
      ∀ x : Fin n → Bool,
        PEqualNP.MetaComplexity.circuitFun n
          { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++
              [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩],
            output := n + C.size } x ≠ f x →
        PEqualNP.MetaComplexity.circuitFun n C x ≠ f x ∨
          ((C.wires (List.ofFn x)).getD h false = true ∧ f x = false) := by
  intro n j a h C f hj hh x hx
  have hlen : (List.ofFn x).length = n := List.length_ofFn x
  have hW : C.wires (List.ofFn x) = C.gates.foldl step (List.ofFn x) := rfl
  by_cases hv : (C.wires (List.ofFn x)).getD h false = false
  · have hmain : (C.gates.set j ⟨GateOp.or, [a]⟩).foldl step (List.ofFn x)
        = C.gates.foldl step (List.ofFn x) := by
      apply foldl_mod_eq C.gates (List.ofFn x) j a h hj
      · rw [hlen]
        exact hh
      · rw [← hW]
        exact hv
    have hEq : (C.gates.set j ⟨GateOp.or, [a]⟩).foldl step (List.ofFn x)
        = C.wires (List.ofFn x) := by
      rw [hmain, ← hW]
    have hfalse : ((C.gates.set j ⟨GateOp.or, [a]⟩).foldl step (List.ofFn x)).getD h false = false := by
      have hW2h : ((C.gates.set j ⟨GateOp.or, [a]⟩).foldl step (List.ofFn x)).getD h false
          = (C.wires (List.ofFn x)).getD h false := by
        apply foldl_mod_getD C.gates (List.ofFn x) j a h hj
        rw [hlen]
        exact hh
      rw [hW2h]
      exact hv
    have hLiftEq : (PEqualNP.CircuitLowerBounds.Circuit.mk
          (C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++
            [(⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩ :
              PEqualNP.CircuitLowerBounds.Gate)])
          (n + C.size)).eval (List.ofFn x)
        = C.eval (List.ofFn x) := by
      have h := lift_eval C (List.ofFn x) n hlen j a h
      rw [h]
      rw [hfalse, hEq, Bool.or_false]
      rfl
    have hNe : (PEqualNP.CircuitLowerBounds.Circuit.mk
          (C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++
            [(⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩ :
              PEqualNP.CircuitLowerBounds.Gate)])
          (n + C.size)).eval (List.ofFn x) ≠ f x := hx
    left
    simp only [circuitFun]
    intro heq
    exact hNe (by rw [hLiftEq, heq])
  · have hhtrue : (C.wires (List.ofFn x)).getD h false = true := by
      cases hb : (C.wires (List.ofFn x)).getD h false with
      | false => exact (hv hb).elim
      | true => rfl
    have hW2h : ((C.gates.set j ⟨GateOp.or, [a]⟩).foldl step (List.ofFn x)).getD h false
        = (C.wires (List.ofFn x)).getD h false := by
      apply foldl_mod_getD C.gates (List.ofFn x) j a h hj
      rw [hlen]
      exact hh
    have hLiftTrue : (PEqualNP.CircuitLowerBounds.Circuit.mk
          (C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++
            [(⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩ :
              PEqualNP.CircuitLowerBounds.Gate)])
          (n + C.size)).eval (List.ofFn x) = true := by
      have h := lift_eval C (List.ofFn x) n hlen j a h
      rw [h, hW2h, hhtrue]
      simp only [Bool.or_true]
    have hNe : (PEqualNP.CircuitLowerBounds.Circuit.mk
          (C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++
            [(⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩ :
              PEqualNP.CircuitLowerBounds.Gate)])
          (n + C.size)).eval (List.ofFn x) ≠ f x := hx
    right
    have hf : f x = false := by
      have hne := hNe
      rw [hLiftTrue] at hne
      cases hfx : f x with
      | false => rfl
      | true => exact (hne hfx.symm).elim
    exact ⟨hhtrue, hf⟩


