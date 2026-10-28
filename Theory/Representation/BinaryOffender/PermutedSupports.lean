module
public import Theory.Representation.BinaryOffender.Homogeneous.Basic
public import Theory.Representation.BinaryOffender.FixedMovedComplement
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration
public import Mathlib.GroupTheory.PGroup

/-!
# Fixed vectors generate distinct odd supports

Suppose the module is a direct sum of supports with odd actors, distinct
supports fix each other's actors, and every invariant subspace either contains
a support or is fixed by its actor. A two-group permuting the supports generates
the entire module from its fixed vectors under the normal odd actor.

The proof takes the sum of the supports missing from that orbit span. This is
a stable complement. A nonzero complement would have a nonzero fixed vector,
which already belongs to the orbit span. This avoids choosing orbit sums or
coset representatives. It is the seed-generation step in Aschbacher--Smith
15.1.2, printed p.1085.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender.PermutedSupports
variable {G V ι : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Finite ι]
  (ρ : Representation (ZMod 2) G V)

omit [Finite G] in
 theorem exists_nonzero_fixed (S : Subgroup G) (hS : IsPGroup 2 S)
    (W : Submodule (ZMod 2) V) (hne : W ≠ ⊥)
    (hW : S ≤ subspaceStabilizer ρ W) :
    ∃ v : V, v ∈ W ∧ v ≠ 0 ∧ v ∈ fixedSpace ρ S := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
  let : MulAction S W := {
    smul s w := ⟨ρ s w, (hW s.property w).2 w.property⟩
    one_smul w := by apply Subtype.ext; exact congrArg (fun f => f (w : V)) (map_one ρ)
    mul_smul s t w := by apply Subtype.ext; exact congrArg (fun f => f (w : V)) (map_mul ρ (s : G) (t : G)) }
  have hcard : 2 ∣ Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card, ZMod.card]
    exact dvd_pow_self 2 (Nat.ne_of_gt (Module.finrank_pos (R := ZMod 2) (M := W)))
  have hz : (0 : W) ∈ MulAction.fixedPoints S W := by
    apply MulAction.mem_fixedPoints.mpr
    intro s
    apply Subtype.ext
    exact map_zero (ρ s)
  obtain ⟨v,hv,hvne⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := W) hcard hz
  exact ⟨v,v.property,(fun he => hvne (Subtype.ext he).symm),
    fun s => congrArg Subtype.val (MulAction.mem_fixedPoints.mp hv s)⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
 theorem orbitSpan_fixed_invariant (P S : Subgroup G) [P.Normal] :
    S ≤ subspaceStabilizer ρ (Homogeneous.orbitSpan ρ P (fixedSpace ρ S)) := by
  apply le_subspaceStabilizer
  intro s hs v hv
  change v ∈ ⨆ p : P, (fixedSpace ρ S).map (ρ p) at hv
  refine Submodule.iSup_induction (fun p : P => (fixedSpace ρ S).map (ρ p))
    (motive := fun v => ρ s v ∈ Homogeneous.orbitSpan ρ P (fixedSpace ρ S)) hv ?_ ?_ ?_
  · rintro p _ ⟨z,hz,rfl⟩
    let p' : P := ⟨s * p * s⁻¹, (inferInstance : P.Normal).conj_mem _ p.property s⟩
    apply le_iSup (fun p : P => (fixedSpace ρ S).map (ρ p)) p'
    refine ⟨z,hz,?_⟩
    change ρ (s * p * s⁻¹) z = ρ s (ρ p z)
    have hzfix : ρ s⁻¹ z = z := hz ⟨s⁻¹,S.inv_mem hs⟩
    rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,hzfix]
  · simp
  · intro x y hx hy
    simpa only [map_add] using (Homogeneous.orbitSpan ρ P (fixedSpace ρ S)).add_mem hx hy

omit [Finite G] in
 theorem fixed_generates (P S : Subgroup G) [P.Normal] (hS : IsPGroup 2 S)
    (X : ι → Subgroup G) (U : ι → Submodule (ZMod 2) V)
    (hc : ∀ i, IsCompl (U i) (fixedSpace ρ (X i)))
    (hcross : ∀ i j, i ≠ j → U i ≤ fixedSpace ρ (X j))
    (hfull : (⨆ i, U i) = ⊤)
    (hirr : ∀ (C : Submodule (ZMod 2) V), P ≤ subspaceStabilizer ρ C →
      ∀ i, U i ≤ C ∨ C ≤ fixedSpace ρ (X i))
    (hperm : ∀ s ∈ S, ∀ i, ∃ j, (U i).map (ρ s) = U j) :
    Homogeneous.orbitSpan ρ P (fixedSpace ρ S) = ⊤ := by
  classical
  let C := Homogeneous.orbitSpan ρ P (fixedSpace ρ S)
  have hCP : P ≤ subspaceStabilizer ρ C := Homogeneous.orbitSpan_invariant ρ P _
  have hCS : S ≤ subspaceStabilizer ρ C := orbitSpan_fixed_invariant ρ P S
  let J := {i : ι // ¬ U i ≤ C}
  let W : Submodule (ZMod 2) V := ⨆ j : J, U j.val
  have hCW : Disjoint W C := by
    have hh : IsCompl W (⨅ j : J, fixedSpace ρ (X j.val)) :=
      Submodule.isCompl_iSup_iInf_of_cross_le
      (fun j : J => U j.val) (fun j : J => fixedSpace ρ (X j.val))
      (fun j => hc j.val) (fun i j hij => hcross i.val j.val
        (fun he => hij (Subtype.ext he)))
    have hCf : C ≤ ⨅ j : J, fixedSpace ρ (X j.val) := by
      refine le_iInf (fun j : J => ?_)
      exact (hirr C hCP j.val).resolve_left j.property
    exact hh.disjoint.mono_right hCf
  have hspan : C ⊔ W = ⊤ := by
    apply top_unique
    rw [← hfull]
    refine iSup_le (fun i => ?_)
    by_cases hi : U i ≤ C
    · exact hi.trans le_sup_left
    · exact (le_iSup (fun j : J => U j.val) ⟨i,hi⟩).trans le_sup_right
  have hWS : S ≤ subspaceStabilizer ρ W := by
    apply le_subspaceStabilizer
    intro s hs v hv
    change v ∈ ⨆ j : J, U j.val at hv
    refine Submodule.iSup_induction (fun j : J => U j.val)
      (motive := fun v => ρ s v ∈ W) hv ?_ ?_ ?_
    · intro i v hv
      obtain ⟨j,hj⟩ := hperm s hs i.val
      have hjn : ¬ U j ≤ C := by
        intro hjC
        apply i.property
        intro w hw
        have hh := hjC (hj ▸ (Submodule.mem_map_of_mem (f := ρ s) hw))
        have hh' := (hCS (S.inv_mem hs) (ρ s w)).2 hh
        simpa using hh'
      exact (le_iSup (fun j : J => U j.val) ⟨j,hjn⟩)
        (hj ▸ Submodule.mem_map_of_mem (f := ρ s) hv)
    · simp
    · intro x y hx hy
      simpa only [map_add] using W.add_mem hx hy
  have hW : W = ⊥ := by
    by_contra hne
    obtain ⟨v,hv,hv0,hvf⟩ := exists_nonzero_fixed ρ S hS W hne hWS
    exact hv0 (Submodule.disjoint_def.mp hCW v hv (Homogeneous.le_orbitSpan ρ P _ hvf))
  simpa only [hW,sup_bot_eq] using hspan
end Representation.BinaryOffender.PermutedSupports
