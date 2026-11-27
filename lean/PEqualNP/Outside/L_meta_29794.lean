import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29794_aux
open PEqualNP.CircuitLowerBounds

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def state (b : Bool) (more : List Bool) : List Bool :=
  b :: true :: false :: true :: false :: false :: false :: more

def value (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)

lemma sameGate (g : Gate) (ok : 0 ∈ g.inputs → g.op = .or ∧ 3 ∈ g.inputs)
    (more : List Bool) : value g (state false more) = value g (state true more) := by
  by_cases h : 0 ∈ g.inputs
  · obtain ⟨op,three⟩ := ok h
    have on (b : Bool) : value g (state b more) = true := by
      unfold value
      rw [op]
      change (_ : List Bool).any id = true
      apply List.any_eq_true.mpr
      exact ⟨true, List.mem_map.mpr ⟨3,three,rfl⟩,rfl⟩
    rw [on,on]
  · unfold value
    congr 1
    apply List.map_congr_left
    intro k hk
    cases k with
    | zero => exact (h hk).elim
    | succ k => rfl

lemma coupled (gs : List Gate)
    (ok : ∀ g ∈ gs, 0 ∈ g.inputs → g.op = .or ∧ 3 ∈ g.inputs)
    (more : List Bool) :
    ∃ rest, ∀ b : Bool, gs.foldl (fun w g => w ++ [value g w]) (state b more) = state b rest := by
  induction gs generalizing more with
  | nil => exact ⟨more,fun _ => rfl⟩
  | cons g gs ih =>
    have same := sameGate g (ok g (by simp)) more
    obtain ⟨rest, hr⟩ := ih (fun d hd => ok d (by simp [hd])) (more ++ [value g (state true more)])
    refine ⟨rest,?_⟩
    intro b
    simp only [List.foldl_cons]
    have step : state b more ++ [value g (state b more)] =
        state b (more ++ [value g (state true more)]) := by
      cases b
      · rw [same]; rfl
      · rfl
    rw [step,hr]

end PEqualNP.Outside.L_meta_29794_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_29794_aux
theorem PEqualNP.Outside.L_meta_29794 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 1 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 3 ∈ (C.gates.get i).inputs ∧ 3 ≠ 0 ∧ 3 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 3 false = true)) := by
  rintro ⟨C,i,k,_,_,_,correct,_,unique,op,_,_,_,three,_⟩
  have ok : ∀ g ∈ C.gates, 0 ∈ g.inputs → g.op = .or ∧ 3 ∈ g.inputs := by
    intro g hg read
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hg
    subst g
    have eq := unique j read
    subst j
    exact ⟨op,three⟩
  have hn : C.output ≠ 0 := by
    intro h
    have test := correct ![true,false,false,false,false,false,false]
    change (C.wires [true,false,false,false,false,false,false]).getD C.output false = false at test
    unfold Circuit.wires at test
    rw [h,foldl_wires_getD_lt _ _ _ (by decide)] at test
    contradiction
  obtain ⟨rest,hr⟩ := coupled C.gates ok []
  have eval (b : Bool) : C.eval (state b []) = (state b rest).getD C.output false := by
    unfold Circuit.eval Circuit.wires
    change (C.gates.foldl (fun w g => w ++ [value g w]) _).getD _ _ = _
    rw [hr]
  have eq : C.eval (state false []) = C.eval (state true []) := by
    rw [eval,eval]
    cases ho : C.output with
    | zero => exact (hn ho).elim
    | succ n => rfl
  have off := correct ![false,true,false,true,false,false,false]
  have on := correct ![true,true,false,true,false,false,false]
  change C.eval (state false []) = false at off
  change C.eval (state true []) = true at on
  rw [off,on] at eq
  contradiction
