module

public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.SpecificGroups.SL2.Affine.Action
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
/-!
# Line root groups in SL₂

For a field line in the natural plane, its pointwise fixer is a conjugate
of the upper unipotent group, and its setwise stabilizer is the corresponding
Borel. Over a finite field of characteristic two the fixer is a Sylow
two-subgroup of order the field cardinality, and the Borel acts irreducibly
on it as a group. Two root groups attached to distinct lines generate SL₂.

Send the first coordinate vector to a nonzero vector of the given line and
transport the standard matrix calculations. For generation, a proper
overgroup would lie in the Borel; a two-subgroup in that Borel lies in its
normal Sylow subgroup, forcing the two roots and hence the lines to agree.
The conjugated root is written explicitly with the right-conjugation
convention, g⁻¹ R g.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.3(1–2), printed p.333, PDF p.344.
-/

@[expose] public section

open Matrix Subgroup
open scoped MatrixGroups Pointwise
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F]
private def firstLine : Submodule F (Fin 2 → F) := Submodule.span F {![1,0]}
private theorem mem_firstLine (v : Fin 2 → F) : v ∈ firstLine ↔ v 1 = 0 := by
  change v ∈ Submodule.span F {![1,0]} ↔ _
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, rfl⟩; simp
  · intro h
    refine ⟨v 0, ?_⟩
    ext i; fin_cases i <;> simp [h]
private theorem fixing_firstLine :
    fixingSubgroup SL(2,F) (firstLine (F := F) : Set (Fin 2 → F)) = upperUnipotent F := by
  ext g
  rw [mem_fixingSubgroup_iff, mem_upperUnipotent]
  constructor
  · intro hg
    have hh := hg ![1,0] ((mem_firstLine _).mpr (by simp))
    have h00 : g.val 0 0 = 1 := by
      simpa [SpecialLinearGroup.smul_def, mulVec, dotProduct, Fin.sum_univ_two] using congrFun hh 0
    have h10 : g.val 1 0 = 0 := by
      simpa [SpecialLinearGroup.smul_def, mulVec, dotProduct, Fin.sum_univ_two] using congrFun hh 1
    have h11 : g.val 1 1 = 1 := by
      simpa only [det_fin_two, h00, h10, one_mul, mul_zero, sub_zero] using g.property
    refine ⟨g.val 0 1, ?_⟩
    apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp [transvection_coe, h00, h10, h11]
  · rintro ⟨t, rfl⟩ v hv
    have hv1 := (mem_firstLine v).mp hv
    ext i; fin_cases i <;>
      simp [SpecialLinearGroup.smul_def, transvection_coe, mulVec, dotProduct, Fin.sum_univ_two, hv1]
private theorem stabilizer_firstLine [Finite F] :
    MulAction.stabilizer SL(2,F) (firstLine (F := F) : Set (Fin 2 → F)) = rankOneBorel F := by
  ext g
  rw [MulAction.mem_stabilizer_set' (Set.toFinite _), mem_rankOneBorel_iff]
  constructor
  · intro hg
    have hh := (mem_firstLine _).mp (hg ((mem_firstLine ![1,0]).mpr (by simp)))
    simpa [SpecialLinearGroup.smul_def, mulVec, dotProduct, Fin.sum_univ_two] using hh
  · intro hg v hv
    apply (mem_firstLine _).mpr
    have hv1 := (mem_firstLine v).mp hv
    simp [SpecialLinearGroup.smul_def, mulVec, dotProduct, Fin.sum_univ_two, hg, hv1]
private theorem exists_firstLine_transport (P : Submodule F (Fin 2 → F))
    (hP : Module.finrank F P = 1) :
    ∃ a : SL(2,F), a • (firstLine (F := F) : Set (Fin 2 → F)) = (P : Set (Fin 2 → F)) := by
  have hne : P ≠ ⊥ := (Submodule.isAtom_iff_finrank_eq_one.mpr hP).ne_bot
  obtain ⟨v, hv, hv0⟩ := P.ne_bot_iff.mp hne
  obtain ⟨a, ha⟩ := Matrix.SL2.exists_mulVec_eq F ![1,0] v (by simp) hv0
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hP hv hv0
  refine ⟨a, ?_⟩
  ext w
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change a.val *ᵥ (t • ![1,0]) ∈ P
    rw [mulVec_smul, ha]
    exact P.smul_mem t hv
  · intro hw
    change w ∈ P at hw
    rw [hspan, Submodule.mem_span_singleton] at hw
    obtain ⟨t, rfl⟩ := hw
    refine ⟨t • ![1,0], (firstLine (F := F)).smul_mem t (Submodule.subset_span (by simp)), ?_⟩
    change a.val *ᵥ (t • ![1,0]) = _
    rw [mulVec_smul, ha]

/-- Simultaneous coordinates for a line root and its full Borel. -/
theorem exists_lineRoot_coordinates [Finite F] (P : Submodule F (Fin 2 → F))
    (hP : Module.finrank F P = 1) : ∃ a : SL(2,F),
    fixingSubgroup SL(2,F) (P : Set (Fin 2 → F)) =
      (upperUnipotent F).map (MulAut.conj a).toMonoidHom ∧
    MulAction.stabilizer SL(2,F) (P : Set (Fin 2 → F)) =
      (rankOneBorel F).map (MulAut.conj a).toMonoidHom := by
  obtain ⟨a, ha⟩ := exists_firstLine_transport P hP
  refine ⟨a, ?_, ?_⟩
  · rw [← ha, SubMulAction.fixingSubgroup_smul_eq_fixingSubgroup_map_conj, fixing_firstLine]
  · rw [← ha, MulAction.stabilizer_smul_eq_stabilizer_map_conj, stabilizer_firstLine]

variable [Finite F]

/-- The normalizer of a line root group is its full setwise stabilizer. -/
theorem normalizer_fixing_line (P : Submodule F (Fin 2 → F))
    (hP : Module.finrank F P = 1) :
    normalizer (fixingSubgroup SL(2,F) (P : Set (Fin 2 → F)) : Set SL(2,F)) =
      MulAction.stabilizer SL(2,F) (P : Set (Fin 2 → F)) := by
  obtain ⟨a, hR, hB⟩ := exists_lineRoot_coordinates P hP
  rw [hR, ← map_equiv_normalizer_eq, hB]

/-- A pointwise line fixer has the order of the field. -/
theorem card_fixing_line (P : Submodule F (Fin 2 → F))
    (hP : Module.finrank F P = 1) :
    Nat.card (fixingSubgroup SL(2,F) (P : Set (Fin 2 → F))) = Nat.card F := by
  obtain ⟨a, hR, _⟩ := exists_lineRoot_coordinates P hP
  rw [hR]
  exact (Nat.card_congr ((upperUnipotent F).equivMapOfInjective
    (MulAut.conj a).toMonoidHom (MulAut.conj a).injective).toEquiv).symm.trans
    (card_upperUnipotent F)

/-- A proper overgroup of a line root group preserves that line. -/
theorem overgroup_fixing_line_le_stabilizer (P : Submodule F (Fin 2 → F))
    (hP : Module.finrank F P = 1) {K : Subgroup SL(2,F)}
    (hRK : fixingSubgroup SL(2,F) (P : Set (Fin 2 → F)) ≤ K) (hK : K ≠ ⊤) :
    K ≤ MulAction.stabilizer SL(2,F) (P : Set (Fin 2 → F)) := by
  obtain ⟨a, hR, hB⟩ := exists_lineRoot_coordinates P hP
  let e := MulAut.conj a
  have hUK : upperUnipotent F ≤ K.comap e.toMonoidHom := by
    intro x hx
    exact hRK (hR ▸ mem_map_of_mem e.toMonoidHom hx)
  have hproper : K.comap e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hK
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := e.surjective x
    exact (show y ∈ K.comap e.toMonoidHom from he ▸ mem_top y)
  have hle := overgroup_le_rankOneBorel hUK hproper
  intro x hx
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [hB]
  exact mem_map_of_mem e.toMonoidHom (hle hx)

variable [CharP F 2]

/-- The line fixer is a Sylow two-subgroup, with no group-order assumption. -/
theorem exists_sylow_fixing_line (P : Submodule F (Fin 2 → F))
    (hP : Module.finrank F P = 1) :
    ∃ S : Sylow 2 SL(2,F), (S : Subgroup SL(2,F)) =
      fixingSubgroup SL(2,F) (P : Set (Fin 2 → F)) := by
  obtain ⟨a, hR, _⟩ := exists_lineRoot_coordinates P hP
  exact ⟨(upperUnipotentSylow F 2).mapSurjective (MulAut.conj a).surjective, hR.symm⟩

/-- The line Borel is irreducible on its root group over the prime field. -/
theorem eq_fixing_line_of_normalized (P : Submodule F (Fin 2 → F))
    (hP : Module.finrank F P = 1) (A : Subgroup SL(2,F))
    (hAR : A ≤ fixingSubgroup SL(2,F) (P : Set (Fin 2 → F))) (hne : A ≠ ⊥)
    (hn : MulAction.stabilizer SL(2,F) (P : Set (Fin 2 → F)) ≤ normalizer (A : Set SL(2,F))) :
    A = fixingSubgroup SL(2,F) (P : Set (Fin 2 → F)) := by
  obtain ⟨a, hR, hB⟩ := exists_lineRoot_coordinates P hP
  let e := MulAut.conj a
  have hmap : (A.comap e.toMonoidHom).map e.toMonoidHom = A :=
    map_comap_eq_self (by intro x _; exact e.surjective x)
  have hAU : A.comap e.toMonoidHom ≤ upperUnipotent F := by
    intro x hx
    have hh := hAR hx
    rw [hR, mem_map_equiv] at hh
    simpa [e, mul_assoc] using hh
  have hne' : A.comap e.toMonoidHom ≠ ⊥ := by
    intro he
    apply hne
    rw [← hmap, he, Subgroup.map_bot]
  have hn' : rankOneBorel F ≤ normalizer (A.comap e.toMonoidHom : Set SL(2,F)) := by
    intro b hb
    apply le_normalizer_comap e.toMonoidHom
    exact hn (hB ▸ mem_map_of_mem e.toMonoidHom hb)
  rw [← hmap, eq_upperUnipotent_of_normalized _ hAU hne' hn']
  exact hR.symm

/-- Two line root groups generate SL₂ when their lines are distinct.
The second root uses right conjugation, `g⁻¹ R g`. -/
theorem fixing_line_sup_right_conjugate (P : Submodule F (Fin 2 → F))
    (hP : Module.finrank F P = 1) (g : SL(2,F))
    (hg : g ∉ MulAction.stabilizer SL(2,F) (P : Set (Fin 2 → F))) :
    fixingSubgroup SL(2,F) (P : Set (Fin 2 → F)) ⊔
      (fixingSubgroup SL(2,F) (P : Set (Fin 2 → F))).map
        (MulAut.conj g⁻¹).toMonoidHom = ⊤ := by
  obtain ⟨S, hS⟩ := exists_sylow_fixing_line P hP
  let Q : Sylow 2 SL(2,F) := S.mapSurjective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).surjective
  have hQ : (Q : Subgroup SL(2,F)) =
      (fixingSubgroup SL(2,F) (P : Set (Fin 2 → F))).map
        (MulAut.conj g⁻¹).toMonoidHom := by
    change (S : Subgroup SL(2,F)).map (MulAut.conj g⁻¹).toMonoidHom = _
    rw [hS]
  by_contra hproper
  have hle := overgroup_fixing_line_le_stabilizer P hP le_sup_left hproper
  have hQN : (Q : Subgroup SL(2,F)) ≤ normalizer (S : Set SL(2,F)) := by
    rw [← S.coe_coe, hS, normalizer_fixing_line P hP, hQ]
    exact le_sup_right.trans hle
  have hQS : (Q : Subgroup SL(2,F)) ≤ S := by
    calc
      (Q : Subgroup SL(2,F)) = (Q : Subgroup SL(2,F)) ⊓ normalizer (S : Set SL(2,F)) := (inf_eq_left.mpr hQN).symm
      _ = (Q : Subgroup SL(2,F)) ⊓ (S : Subgroup SL(2,F)) := Q.isPGroup'.inf_normalizer_sylow S
      _ ≤ S := inf_le_right
  have he : (S : Subgroup SL(2,F)) = Q := Q.is_maximal' S.isPGroup' hQS
  have hn : g⁻¹ ∈ normalizer (fixingSubgroup SL(2,F) (P : Set (Fin 2 → F)) : Set SL(2,F)) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hQ.symm.trans (he.symm.trans hS)
  apply hg
  rw [← normalizer_fixing_line P hP]
  simpa only [inv_inv] using (normalizer _).inv_mem hn

end Matrix.SpecialLinearGroup
