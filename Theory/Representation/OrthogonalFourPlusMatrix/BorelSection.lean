module
public import Theory.Representation.OrthogonalFourPlusMatrix.SylowSingularLine
public import Theory.Representation.OrthogonalFourPlusMatrix.SylowLineCubic
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import Theory.GroupTheory.PCoreProduct
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.ElementaryAbelian.Injective

/-!
# The Borel section of the determinant tensor

The normalizer of a Sylow two-subgroup of SL₂(4) × SL₂(4) has elementary
quotient of order nine. Its common fixed space is a field line, while the
full Borel fixes no nonzero vector. The quotient coordinates retain the
literal Sylow normalizer and its intrinsic two-core.

These facts supply the Cartan section in the tensor branch of
Aschbacher–Smith 14.3.6(3) and 14.3.15, printed pp.991–994.
-/

public noncomputable section
open Matrix Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

private theorem upper_normalizer : normalizer (upperPairSylow : Set G) =
    (SpecialLinearGroup.rankOneBorel F).prod (SpecialLinearGroup.rankOneBorel F) := by
  ext x
  constructor
  · intro hx
    constructor
    · apply mem_normalizer_iff.mpr
      intro a
      have hh := mem_normalizer_iff.mp hx (a,1)
      change (a ∈ _ ∧ (1 : SL2FourNatural.SL) ∈ _) ↔
        (x.1*a*x.1⁻¹ ∈ _ ∧ x.2*1*x.2⁻¹ ∈ _) at hh
      constructor
      · intro ha; exact (hh.mp ⟨ha,one_mem _⟩).1
      · intro ha; exact (hh.mpr ⟨ha,by simp⟩).1
    · apply mem_normalizer_iff.mpr
      intro a
      have hh := mem_normalizer_iff.mp hx (1,a)
      change ((1 : SL2FourNatural.SL) ∈ _ ∧ a ∈ _) ↔
        (x.1*1*x.1⁻¹ ∈ _ ∧ x.2*a*x.2⁻¹ ∈ _) at hh
      constructor
      · intro ha; exact (hh.mp ⟨one_mem _,ha⟩).2
      · intro ha; exact (hh.mpr ⟨by simp,ha⟩).2
  · intro hx
    apply mem_normalizer_iff.mpr
    intro a
    exact and_congr (mem_normalizer_iff.mp hx.1 a.1) (mem_normalizer_iff.mp hx.2 a.2)

private def upperNormalizerEquiv : normalizer (upperPairSylow : Set G) ≃*
    (Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F ×
      Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F) :=
  ((MulEquiv.subgroupCongr upper_normalizer).trans (Subgroup.prodEquiv _ _)).trans
    (MulEquiv.prodCongr
      (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.rankOneBorelEquiv F)
      (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.rankOneBorelEquiv F))

private theorem field_card_four : Nat.card F = 2^2 := by
  rw [Nat.card_eq_fintype_card]
  exact SL2FourNatural.card_field

private def upperQuotientEquiv :
    (normalizer (upperPairSylow : Set G) ⧸ pCore 2 (normalizer (upperPairSylow : Set G))) ≃*
      Fˣ × Fˣ :=
  (upperNormalizerEquiv.toMonoidHom.pCoreQuotientEquiv (p := 2)
    upperNormalizerEquiv.surjective (IsPGroup.ker_isPGroup_of_injective upperNormalizerEquiv.injective)).trans
    ((QuotientGroup.quotientMulEquivOfEq (pCore_prod 2)).trans
      ((QuotientGroup.prodMulEquiv _ _).trans
        (MulEquiv.prodCongr
          (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.quotientTorusEquiv F field_card_four)
          (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.quotientTorusEquiv F field_card_four))))

/-- The Borel quotient of the exact determinant tensor has two independent cubic factors. -/
def sylowNormalizerQuotientEquiv (P : Sylow 2 G) :
    (normalizer (P : Set G) ⧸ pCore 2 (normalizer (P : Set G))) ≃* Fˣ × Fˣ := by
  let g := Classical.choose (MulAction.exists_smul_eq G P upperPairSylow)
  have hg := Classical.choose_spec (MulAction.exists_smul_eq G P upperPairSylow)
  have he : (P : Subgroup G).map (MulAut.conj g).toMonoidHom = upperPairSylow :=
    congrArg Sylow.toSubgroup hg
  have hn : (normalizer (P : Set G)).map (MulAut.conj g).toMonoidHom =
      normalizer (upperPairSylow : Set G) := by
    change (normalizer ((P : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom = _
    rw [map_equiv_normalizer_eq,he]
    rfl
  let e := ((normalizer (P : Set G)).equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hn)
  exact (e.toMonoidHom.pCoreQuotientEquiv (p := 2) e.surjective
    (IsPGroup.ker_isPGroup_of_injective e.injective)).trans upperQuotientEquiv

theorem sylowNormalizer_quotient_elementary (P : Sylow 2 G) :
    IsElementaryAbelian 3 (normalizer (P : Set G) ⧸ pCore 2 (normalizer (P : Set G))) := by
  let : IsElementaryAbelian 3 (Fˣ × Fˣ) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      apply Prod.ext <;> apply Units.ext <;>
        have h : ∀ u : Fˣ, u^3=1 := by decide +kernel
      · exact congrArg Units.val (h x.1)
      · exact congrArg Units.val (h x.2)) }
  exact IsElementaryAbelian.of_injective (p := 3)
    (sylowNormalizerQuotientEquiv P).toMonoidHom (sylowNormalizerQuotientEquiv P).injective

theorem sylowNormalizer_quotient_card (P : Sylow 2 G) :
    Nat.card (normalizer (P : Set G) ⧸ pCore 2 (normalizer (P : Set G))) = 9 := by
  rw [Nat.card_congr (sylowNormalizerQuotientEquiv P).toEquiv,Nat.card_prod,
    Nat.card_units,field_card_four]
  norm_num

/-- The full Borel fixes no vector in the binary determinant tensor. -/
theorem sylowNormalizer_fixedSpace (P : Sylow 2 G) :
    fixedSpace action (normalizer (P : Set G)) = ⊥ := by
  let g := Classical.choose (MulAction.exists_smul_eq G P upperPairSylow)
  have hg := Classical.choose_spec (MulAction.exists_smul_eq G P upperPairSylow)
  have he : (P : Subgroup G).map (MulAut.conj g).toMonoidHom = upperPairSylow :=
    congrArg Sylow.toSubgroup hg
  have hn : (normalizer (P : Set G)).map (MulAut.conj g).toMonoidHom =
      normalizer (upperPairSylow : Set G) := by
    change (normalizer ((P : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom = _
    rw [map_equiv_normalizer_eq,he]
    rfl
  have hu : fixedSpace action (normalizer (upperPairSylow : Set G)) = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    have hp : v ∈ point := fixedSpace_upperPair ▸ (fun p => hv ⟨p,(upperPairSylow : Subgroup G).le_normalizer p.property⟩)
    obtain ⟨b,rfl⟩ := hp
    let c := SL2FourNatural.PointCommutator.cubic
    have hc : (c,1) ∈ normalizer (upperPairSylow : Set G) := by
      rw [upper_normalizer]
      exact ⟨(SpecialLinearGroup.mem_rankOneBorel_iff _).mpr rfl,one_mem _⟩
    have hf := hv ⟨(c,1),hc⟩
    have hentry := congrArg (fun v : V => v 0 1) hf
    have heq : QuadraticAlgebra.omega * b = b := by
      simpa [action_apply,c,SL2FourNatural.PointCommutator.cubic,pointMap,
        Matrix.mul_apply,Fin.sum_univ_two] using hentry
    have hb : b = 0 := by
      have hw : (QuadraticAlgebra.omega : F) ≠ 1 := by decide +kernel
      by_contra hb
      exact hw (mul_right_cancel₀ hb (heq.trans (one_mul b).symm))
    simp only [hb,map_zero]
  let e := fixedSpaceConjEquiv action (normalizer (P : Set G)) g
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have hh : e ⟨v,hv⟩ = 0 := by
    apply Subtype.ext
    exact (Submodule.mem_bot (R := ZMod 2)).mp (by
      have h := (e ⟨v,hv⟩).property
      simpa only [hn,hu] using h)
  exact congrArg Subtype.val (e.injective (hh.trans e.map_zero.symm))
end ClassicalOrthogonal.FourPlusMatrix.Binary
