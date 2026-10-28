module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Generation
public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import Theory.Representation.BinaryOffender.FixedCodimTransport
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
/-!
# Descent on the original module in the B.5.13 product case

The source product decomposition lives modulo the global fixed space.
When a factor is perfect, its action on the opposite prescribed space has
central displacements and hence is trivial. Two perfect factors therefore
act on opposite spaces. The same conclusion holds for an ordinary perfect
factor by commuting its displacements with those of the other factor.

The actual B.5.3 hypotheses then descend to the full original representation
restricted to that factor. Offender generation first descends to its faithful
subspace and lifts back using equality of all fixed codimensions. Deleting
the other nontrivial factor strictly reduces group order. The final consumers
use only the corresponding smaller-order numerical bound, to be supplied by
the B.5.13 induction; no quotient-module dual is substituted for the original.

Source: Aschbacher–Smith B.5.6(3) and B.5.13, printed pp.105 and 110.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceB513
open SourceInduction QuasisimpleSource
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
 {σ : Representation (ZMod 2) D V}

/-- Every source factor space contains all displacements of its actual actor. -/
theorem factor_moved_le {A : Subgroup D} {U : Subrepresentation σ}
    (h : SourceFactorCase σ A U) : moved σ A ≤ U.toSubmodule := by
  cases h with
  | natural hm _ => exact hm.ge
  | doubleNatural _ _ hm _ => exact hm.ge
  | exceptional hm _ => exact hm

/-- The literal quotient decomposition gives a spanning sum with globally fixed vectors. -/
theorem quotient_span (c : SourceTwoFactorCase σ) :
    c.firstSpace.toSubmodule ⊔ c.secondSpace.toSubmodule ⊔ σ.invariants = ⊤ := by
  apply top_unique
  intro v _
  have hv : σ.invariants.mkQ v ∈
      ((fixed σ).quotientImage c.firstSpace).toSubmodule ⊔
        ((fixed σ).quotientImage c.secondSpace).toSubmodule := by
    rw [c.decomposition.sup_eq_top]; trivial
  change σ.invariants.mkQ v ∈ c.firstSpace.toSubmodule.map σ.invariants.mkQ ⊔
    c.secondSpace.toSubmodule.map σ.invariants.mkQ at hv
  obtain ⟨u,⟨x,hx,rfl⟩,w,⟨y,hy,rfl⟩,he⟩ := Submodule.mem_sup.mp hv
  have hz : v - (x+y) ∈ σ.invariants := by
    apply (Submodule.Quotient.mk_eq_zero σ.invariants).mp
    change σ.invariants.mkQ (v-(x+y)) = 0
    rw [map_sub,map_add,he,sub_self]
  have hv' : (x+y)+(v-(x+y)) ∈ c.firstSpace.toSubmodule ⊔
      c.secondSpace.toSubmodule ⊔ σ.invariants :=
    Submodule.mem_sup.mpr ⟨x+y,Submodule.mem_sup.mpr ⟨x,hx,y,hy,rfl⟩,
      v-(x+y),hz,rfl⟩
  simpa only [add_sub_cancel] using hv'

/-- A perfect factor fixes the opposite prescribed space before taking a quotient. -/
theorem opposite_fixed_of_perfect (A : Subgroup D) [Group.IsPerfect A]
    (U W : Subrepresentation σ) (hm : moved σ A ≤ U.toSubmodule)
    (hd : Disjoint ((fixed σ).quotientImage U).toSubmodule
      ((fixed σ).quotientImage W).toSubmodule) :
    W.toSubmodule ≤ fixedSpace σ A := by
  apply le_fixedSpace_of_commutator_le_fixedSpace σ A W.toSubmodule
    (le_subspaceStabilizer σ _ (fun a _ v hv => W.apply_mem_toSubmodule a hv))
  have hcent : subspaceCommutator σ W.toSubmodule A ≤ σ.invariants := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,hv,rfl⟩
    apply (Submodule.Quotient.mk_eq_zero σ.invariants).mp
    apply Submodule.disjoint_def.mp hd
    · exact ⟨σ a v-v,hm (Submodule.subset_span ⟨a,ha,v,Submodule.mem_top,rfl⟩),rfl⟩
    · exact ⟨σ a v-v,W.toSubmodule.sub_mem (W.apply_mem_toSubmodule a hv) hv,rfl⟩
  exact hcent.trans (fun v hv a => hv a)

/-- Cross fixation transfers B.5.3 to the full original action of the second factor. -/
theorem product_restriction_of_cross_fixed [Finite D] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass} (h : FFHypothesis K σ) (c : SourceTwoFactorCase σ)
    (hU : c.firstSpace.toSubmodule ≤ fixedSpace σ c.second)
    (hW : c.secondSpace.toSubmodule ≤ fixedSpace σ c.first) :
    FFHypothesis K (σ.comp c.second.subtype) := by
  let U : Subrepresentation σ := c.firstSpace ⊔ fixed σ
  have hspan : U.toSubmodule ⊔ c.secondSpace.toSubmodule = ⊤ := by
    change (c.firstSpace.toSubmodule ⊔ σ.invariants) ⊔ c.secondSpace.toSubmodule = ⊤
    simpa only [sup_assoc,sup_comm,sup_left_comm] using quotient_span c
  have hUc : U.toSubmodule ≤ fixedSpace σ c.second :=
    sup_le hU (fun v hv a => hv a)
  have hf := faithful_on_supplement σ h.faithful c.second U c.secondSpace hspan hUc
  have hj := second_generated σ c.product c.secondSpace hW hf h.generated
  let W : Subrepresentation (σ.comp c.second.subtype) :=
    ⟨c.secondSpace.toSubmodule, fun a v hv => c.secondSpace.apply_mem_toSubmodule a hv⟩
  have hfix (A : Subgroup c.second) :
      fixedCodim W.toRepresentation A = fixedCodim (σ.comp c.second.subtype) A := by
    apply (fixedCodim_subrepresentation_eq_iff _ W A).mpr
    apply top_unique
    rw [← hspan]
    apply sup_le _ le_sup_left
    intro v hv
    apply Submodule.mem_sup_right
    intro a
    exact hUc hv a.val
  have hgen : offenderSubgroup (σ.comp c.second.subtype) = ⊤ := by
    apply top_unique
    rw [← hj]
    apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA,_⟩
    have hB := hA.map_of_fixedCodim W.toRepresentation (σ.comp c.second.subtype)
      (MonoidHom.id c.second) Function.injective_id (by simpa only [Subgroup.map_id] using hfix)
    have hB' : IsBestOffender (σ.comp c.second.subtype) A := by
      simpa only [Subgroup.map_id] using hB
    exact le_iSup_of_le A (le_iSup_of_le ⟨hB',le_top⟩ le_rfl)
  refine ⟨inferInstance,h.faithful.comp c.second.subtype_injective,
    c.product.second_twoCore h.twoCore,hgen,?_⟩
  obtain ⟨q⟩ := h.quotient
  exact ⟨q.subgroup c.second⟩
/-- Both perfect factors supply the original cross-fixation premises. -/
theorem perfect_product_restriction [Finite D] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass} (h : FFHypothesis K σ) (c : SourceTwoFactorCase σ)
    [Group.IsPerfect c.first] [Group.IsPerfect c.second] :
    FFHypothesis K (σ.comp c.second.subtype) :=
  product_restriction_of_cross_fixed h c
    (opposite_fixed_of_perfect c.second c.secondSpace c.firstSpace
      (factor_moved_le c.secondCase) c.decomposition.disjoint.symm)
    (opposite_fixed_of_perfect c.first c.firstSpace c.secondSpace
      (factor_moved_le c.firstCase) c.decomposition.disjoint)

private theorem product_commutes {A B : Subgroup D} (p : InternalProduct A B)
    (a : A) (b : B) : (a : D) * (b : D) = (b : D) * (a : D) := by
  have he : p.equiv ((a,1) * (1,b)) = p.equiv ((1,b) * (a,1)) := by simp
  rw [map_mul,map_mul] at he
  simpa only [p.apply_eq,OneMemClass.coe_one,mul_one,one_mul] using he

/-- Commuting actors exchange the condition that one moved space is fixed by the other. -/
theorem opposite_moved_fixed {A B : Subgroup D} (p : InternalProduct A B)
    (hfix : moved σ A ≤ fixedSpace σ B) : moved σ B ≤ fixedSpace σ A := by
  apply Submodule.span_le.mpr
  rintro _ ⟨b,hb,v,_,rfl⟩ a
  have he := hfix (Submodule.subset_span ⟨a,a.property,v,Submodule.mem_top,rfl⟩) ⟨b,hb⟩
  change σ b (σ (a : D) v-v) = σ (a : D) v-v at he
  rw [map_sub] at he
  have hcomm : σ b (σ (a : D) v) = σ (a : D) (σ b v) := by
    rw [← Module.End.mul_apply,← map_mul,
      ← product_commutes p a ⟨b,hb⟩,map_mul,Module.End.mul_apply]
  rw [hcomm] at he
  change σ (a : D) (σ b v-v) = σ b v-v
  rw [map_sub]
  apply sub_eq_sub_iff_add_eq_add.mpr
  exact (sub_eq_sub_iff_add_eq_add.mp he).trans (add_comm _ _)

/-- An ordinary perfect factor suffices even when the opposite factor is not perfect. -/
theorem ordinary_perfect_product_restriction [Finite D] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass} (h : FFHypothesis K σ) (c : SourceTwoFactorCase σ)
    [Group.IsPerfect c.second]
    (hm : c.secondSpace.toSubmodule = moved σ c.second) :
    FFHypothesis K (σ.comp c.second.subtype) := by
  have hU := opposite_fixed_of_perfect c.second c.secondSpace c.firstSpace
    (factor_moved_le c.secondCase) c.decomposition.disjoint.symm
  apply product_restriction_of_cross_fixed h c hU
  rw [hm]
  exact opposite_moved_fixed c.product ((factor_moved_le c.firstCase).trans hU)

private theorem sl_nontrivial (F : BinaryField) (n : ℕ) (hn : 2 ≤ n) :
    Nontrivial (Matrix.SpecialLinearGroup (Fin n) F.Carrier) := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp only [i,j] at this; omega
  refine ⟨⟨Matrix.SpecialLinearGroup.transvection hij (1 : F.Carrier), 1, ?_⟩⟩
  intro he
  have hh := congrArg (fun m : Matrix.SpecialLinearGroup (Fin n) F.Carrier => m.val i j) he
  simp only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply,
    Matrix.single_apply_same, Matrix.one_apply_ne hij, zero_add,
    Matrix.SpecialLinearGroup.coe_one] at hh
  exact one_ne_zero hh

private theorem factor_nontrivial {A : Subgroup D} {U : Subrepresentation σ}
    (h : SourceFactorCase σ A U) : Nontrivial A := by
  cases h with
  | natural _ hn =>
    cases hn with
    | linearTwo F hn =>
      let := sl_nontrivial F 2 (by decide)
      obtain ⟨e⟩ := hn; exact e.groupEquiv.symm.injective.nontrivial
    | symmetricFive hn => obtain ⟨e⟩ := hn; exact e.groupEquiv.symm.injective.nontrivial
    | linearThree F _ hn =>
      let := sl_nontrivial F 3 (by decide)
      obtain ⟨e⟩ := hn; exact e.groupEquiv.symm.injective.nontrivial
  | doubleNatural F _ _ hn =>
    let := sl_nontrivial F 3 (by decide)
    obtain ⟨e⟩ := hn; exact e.groupEquiv.symm.injective.nontrivial
  | exceptional _ hn =>
    let := sl_nontrivial BinaryField.two 3 (by decide)
    exact hn.natural.groupEquiv.symm.injective.nontrivial

/-- Both literal source factors are nontrivial, so deleting the first strictly lowers order. -/
theorem product_second_card_lt [Finite D] (c : SourceTwoFactorCase σ) :
    Nat.card c.second < Nat.card D := by
  let : Nontrivial c.first := factor_nontrivial c.firstCase
  exact c.product.second_card_lt ((Subgroup.nontrivial_iff_ne_bot c.first).mp inferInstance)

/-- The two-perfect-factor branch uses the smaller-order bound on the same full module. -/
theorem perfect_product_bound [Finite D] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {K : GroupClass}
    (h : FFHypothesis K ρ.dual) (c : SourceTwoFactorCase ρ.dual)
    [Group.IsPerfect c.first] [Group.IsPerfect c.second]
    (hb : Nat.card c.second < Nat.card D →
      FFHypothesis K (Representation.dual (ρ.comp c.second.subtype)) →
      quadraticRatio (ρ.comp c.second.subtype) ≤ 2) :
    quadraticRatio ρ ≤ 2 := by
  have hf : FFHypothesis K (Representation.dual (ρ.comp c.second.subtype)) :=
    perfect_product_restriction h c
  have ht := quadraticRatio_le_of_injective_equivariant (ρ.comp c.second.subtype) ρ
    c.second.subtype c.second.subtype_injective (LinearEquiv.refl (ZMod 2) V) (fun _ _ => rfl)
  exact ht.trans (hb (product_second_card_lt c) hf)

/-- The ordinary-perfect-factor branch uses the same smaller-order numerical induction. -/
theorem ordinary_perfect_product_bound [Finite D] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {K : GroupClass}
    (h : FFHypothesis K ρ.dual) (c : SourceTwoFactorCase ρ.dual)
    [Group.IsPerfect c.second]
    (hm : c.secondSpace.toSubmodule = moved ρ.dual c.second)
    (hb : Nat.card c.second < Nat.card D →
      FFHypothesis K (Representation.dual (ρ.comp c.second.subtype)) →
      quadraticRatio (ρ.comp c.second.subtype) ≤ 2) :
    quadraticRatio ρ ≤ 2 := by
  have hf : FFHypothesis K (Representation.dual (ρ.comp c.second.subtype)) :=
    ordinary_perfect_product_restriction h c hm
  have ht := quadraticRatio_le_of_injective_equivariant (ρ.comp c.second.subtype) ρ
    c.second.subtype c.second.subtype_injective (LinearEquiv.refl (ZMod 2) V) (fun _ _ => rfl)
  exact ht.trans (hb (product_second_card_lt c) hf)

end CFSG.Quasithin.ChapterB.SourceB513
