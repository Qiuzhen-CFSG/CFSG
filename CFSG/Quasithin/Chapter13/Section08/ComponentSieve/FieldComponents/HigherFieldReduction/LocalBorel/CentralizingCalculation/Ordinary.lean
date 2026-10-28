module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.SourceData
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.NaturalImage
public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals.Recognition

/-!
# Obstruction to the literal ordinary Borel identities

The actual natural-line residual L₁ has permutation image A₄, of order
twelve. An element of L₁ centralizing L/O₂(L) has trivial permutation
image, since A₆ has trivial centralizer in S₆. Consequently the literal
B_C = O²(C_{BL₁}(L/O₂(L))) has index at least twelve in BL₁.

Every two-core lies in the three-residual. Thus the simultaneous claims
B_C = O³(B) and |BL₁ : B_C O₂(B)| = 3 contradict the genuine ordinary
natural setup. The final theorem records this obstruction for the published
SourceContext without changing any of its fields or quotient conventions.
This is not a counterexample to the global exclusion in 13.8.20: its full
standing counterexample assumptions may be inconsistent. It prevents
presenting the requested pair as a compatible intrinsic local calculation;
a different source interpretation or an independent exclusion is needed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1, p.877; proof of 13.8.20, p.954/PDF p.971. Both displayed
formulas were checked against the PDF, including the superscript in O³.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u v
variable {G : Type*} [Group G] [Finite G] {L T V V₁ : Subgroup G}

omit [Finite G] in
/-- The two-core is always contained in the three-residual. -/
private theorem twoCore_le_threeResidual (B : Subgroup G) : B.pCoreIn 2 ≤ residualIn 3 B := by
  rintro _ ⟨b, hb, rfl⟩
  refine ⟨b, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
  have hc := (pCore_isPGroup (p := 2) (G := B)).orderOf_coprime
    (by decide : Nat.Coprime 2 3) (⟨b, hb⟩ : pCore 2 B)
  rw [← Subgroup.orderOf_coe] at hc
  exact hc.symm

omit [Finite G] in
/-- A member of L₁ centralizing L/O₂(L) has trivial six-letter image. -/
theorem onePermutation_eq_one_of_quotient_centralizing
    (d : NaturalSetup L T V V₁) (x : one L T V₁)
    (hx : ∀ l ∈ L, ⁅x.val, l⁆ ∈ L.pCoreIn 2) :
    NaturalImage.onePermutation d x = 1 := by
  have hc : NaturalImage.onePermutation d x ∈
      centralizer (alternatingGroup (Fin 6) : Set (Equiv.Perm (Fin 6))) := by
    apply mem_centralizer_iff.mpr
    intro a ha
    obtain ⟨q, hq⟩ := d.model.surjective ⟨a, ha⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    have hl : d.permutation (inclusion le_sup_left l) = a :=
      (d.model_compatible l).trans (congrArg Subtype.val hq)
    let y : (L ⊔ T : Subgroup G) := inclusion ((one_le L T V₁).trans inf_le_left) x
    let z : (L ⊔ T : Subgroup G) := inclusion le_sup_left l
    obtain ⟨c, hc, he⟩ := hx l.val l.property
    have he' : inclusion le_sup_left c = ⁅y, z⁆ := Subtype.ext he
    have hm : d.permutation (inclusion le_sup_left c) = 1 := by
      have hq : QuotientGroup.mk' (pCore 2 L) c = 1 :=
        (QuotientGroup.eq_one_iff c).mpr hc
      rw [d.model_compatible c, hq, map_one]
      rfl
    rw [he'] at hm
    have hcomm : ⁅NaturalImage.onePermutation d x, a⁆ = 1 := by
      simpa only [commutatorElement_def, map_mul, map_inv, z, hl, y,
        NaturalImage.onePermutation, MonoidHom.comp_apply] using hm
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm
  rw [Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals.centralizer_alternating] at hc
  exact hc

/-- The literal quotient-centralizer residual has index at least twelve
in BL₁: its intersection with L₁ kills the entire A₄ permutation image. -/
theorem twelve_le_centralizingResidual_index
    (d : NaturalSetup L T V V₁) (B : Subgroup G)
    (hJL : B ⊔ one L T V₁ ≤ normalizer (L : Set G)) :
    12 ≤ (centralizingResidual B (one L T V₁) L).relIndex (B ⊔ one L T V₁) := by
  let C := centralizingResidual B (one L T V₁) L
  let f := NaturalImage.onePermutation d
  have hc : C.subgroupOf (one L T V₁) ≤ f.ker := by
    intro x hx
    apply onePermutation_eq_one_of_quotient_centralizing d x
    intro l hl
    exact centralizingResidual_commutator_le B (one L T V₁) L
      (hJL.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
      (commutator_mem_commutator hx hl)
  have hlow : 12 ≤ C.relIndex (one L T V₁) := by
    change 12 ≤ (C.subgroupOf (one L T V₁)).index
    rw [← NaturalImage.onePermutation_range_card d, ← index_ker]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero index_ne_zero_of_finite) (index_dvd_of_le hc)
  exact hlow.trans (relIndex_le_of_le_right le_sup_right (show C.relIndex (B ⊔ one L T V₁) ≠ 0 from index_ne_zero_of_finite))

/-- The requested residual identity and index three cannot hold together
for the genuine ordinary natural setup with the literal residual conventions. -/
theorem not_residual_identity_and_cubic_index
    (d : NaturalSetup L T V V₁) (B : Subgroup G)
    (hJL : B ⊔ one L T V₁ ≤ normalizer (L : Set G)) :
    ¬ (centralizingResidual B (one L T V₁) L = residualIn 3 B ∧
      (centralizingResidual B (one L T V₁) L ⊔ B.pCoreIn 2).relIndex
        (B ⊔ one L T V₁) = 3) := by
  rintro ⟨he, hi⟩
  have hc : B.pCoreIn 2 ≤ centralizingResidual B (one L T V₁) L := by
    rw [he]
    exact twoCore_le_threeResidual B
  rw [sup_eq_left.mpr hc] at hi
  have hlow := twelve_le_centralizingResidual_index d B hJL
  omega

/-- Specialization to the exact published source context. The literal ordinary
residual identity and index assertion cannot both be established without
also excluding this context. -/
theorem source_residual_index_obstruction
    {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
    [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
    (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)
    (a : NaturalSetup L (T : Subgroup G) V V₁) :
    ¬ (centralizingResidual d.B (one L (T : Subgroup G) V₁) L = residualIn 3 d.B ∧
      (centralizingResidual d.B (one L (T : Subgroup G) V₁) L ⊔ d.B.pCoreIn 2).relIndex
        (d.B ⊔ one L (T : Subgroup G) V₁) = 3) :=
  not_residual_identity_and_cubic_index a d.B d.product_normalizes_L

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary
