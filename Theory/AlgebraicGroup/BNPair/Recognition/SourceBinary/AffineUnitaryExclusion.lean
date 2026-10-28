module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryCartanFixed
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.AffineExclusion

/-!
# Excluding affine hexagons opposite either nonbinary unitary cover

The actual affine Cartan-fixed panel kernel admits a faithful action of
the root-panel image of order 72. Root separation and primitivity prove
faithfulness, and the Frattini automorphism-kernel theorem preserves it.
The regular normal ternary plane and its freely acting stabilizer of order
eight force binary degree at least eight. This gives the unconditional
lower bound 256 on that kernel, with no assumption on the opposite actor.

If the full Cartan has no fixed points on the opposite root family, unique
five-root coordinates put its entire remainder centralizer in a product
of two roots of order eight. Hence the kernel has order at most 64, which
contradicts the lower bound. UnitaryCartanFixed discharges precisely this
premise for both SU3 and PSU3 at every q greater than two, retaining their
actual scalar projection and both endpoint orientations.

Source: Fong--Seitz I (4D), (5E), (5I), pp.21--23,27,31--35. The original
factor and both original core identifications are supplied by the source
consumer BinaryAffineUnitaryExclusion. This does not prove the other even
Weyl branches, minimality, or the exhaustive seven-row classification.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates UnitarySource MulAction
open scoped Pointwise IsMulCommutative
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The affine actor forces at least eight dimensions on its actual Cartan-fixed kernel. -/
theorem affine_hexagon_fixed_section_lower_bound
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    256 ≤ Nat.card (affineFixedSection Q split j hs hp hg).numerator := by
  let d := affineFixedSection Q split j hs hp hg
  let f := rootImageProjection Q split j
  have hf : Function.Surjective f :=
    (panelAction Q j _ (rankOne_le_parabolic Q split j)).rangeRestrict_surjective
  have hk : f.ker ≤ d.numeratorAction.ker := by
    change ((panelAction Q j _ (rankOne_le_parabolic Q split j)).rangeRestrict).ker ≤ _
    rw [MonoidHom.ker_rangeRestrict,panelAction_ker]
    rw [←rankOneAction_ker]
    exact affine_fixed_panel_kernel Q split j hs hp hg
  let α : rootPanelImage Q split j →* MulAut d.numerator :=
    f.liftOfSurjective hf ⟨d.numeratorAction,hk⟩
  have ha (r : rankOne Q split j) : α (f r) = d.numeratorAction r :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have harange : α.range = d.numeratorAction.range := by
    have he : α.comp f = d.numeratorAction := MonoidHom.ext ha
    rw [←he,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hf,←MonoidHom.range_eq_map]
  have hnon : ¬ IsPGroup 2 α.range := by
    rw [harange]
    exact affine_fixed_action_not_two Q split hm i j hij (actorReflection Q split j) hs hp hg
  obtain ⟨hsol,hcard,hfree⟩ := affine_root_image_structure Q split j hs hp hg
  let := hsol
  have hα : Function.Injective α := BinaryPanel.injective_of_non_two_image
    (rootPanelImage_two_pretransitive Q split j) hp hcard (panelBase Q j) α hnon
  let β := (quotientAut (frattini d.numerator)).comp α
  have hkβ : IsPGroup 2 β.ker :=
    (isPGroup_quotientAut_frattini_kernel d.isTwo).comap_of_injective α hα
  have hβ : Function.Injective β := BinaryPanel.injective_of_two_kernel
    (rootPanelImage_two_pretransitive Q split j) hp (panelBase Q j) β hkβ
  let : Fact (IsPGroup 2 d.numerator) := ⟨d.isTwo⟩
  let : IsElementaryAbelian 2 (d.numerator ⧸ frattini d.numerator) :=
    isElementaryAbelian_quotient_frattini
  let ρ := Representation.FrattiniAction.ofAutomorphismHom β
  have hρ : Function.Injective ρ := by
    intro r t he
    apply hβ
    ext x
    exact Additive.ofMul.injective (congrArg
      (fun a : Module.End (ZMod 2) (Additive (d.numerator ⧸ frattini d.numerator)) =>
        a (Additive.ofMul x)) he)
  have hdim := BinaryPanel.frobenius_nine_degree
    (rootPanelImage_two_pretransitive Q split j) hp hcard (panelBase Q j) hfree ρ hρ
  have hlow : 256 ≤ Nat.card (d.numerator ⧸ frattini d.numerator) := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hdim
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive (d.numerator ⧸ frattini d.numerator))
    simp only [Nat.card_zmod] at he
    rw [←he] at hh
    exact hh
  have hup := Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (frattini d.numerator))
  exact hlow.trans hup

/-- Trivial Cartan fixed points on the opposite root family exclude the affine hexagon. -/
theorem no_affine_hexagon_of_cartan_fixedFree
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hfree : ∀ w, rootAt Q split i w ⊓
      centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) = ⊥)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) : False := by
  let C := simpleRemainder Q split j ⊓
    centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D))
  have hprod := radical_centralizer_product Q split hm i j hij
    (Q.tits.B ⊓ Q.tits.N) le_rfl hfree (affine_cartan_centralizes_all_roots Q split j hs hp hg)
  change (C : Set (X ⧸ Q.D)) = _ at hprod
  let A := rootAt Q split j (Q.simple i)
  let B := rootAt Q split j (Q.simple i*Q.simple j)
  let f : A × B → C := fun z => ⟨(z.1 : X ⧸ Q.D)*z.2, by
    rw [← SetLike.mem_coe,hprod]
    exact ⟨_,z.1.property,_,z.2.property,rfl⟩⟩
  have hf : Function.Surjective f := by
    intro x
    have hx := x.property
    rw [← SetLike.mem_coe,hprod] at hx
    obtain ⟨a,ha,b,hb,he⟩ := hx
    exact ⟨(⟨a,ha⟩,⟨b,hb⟩),Subtype.ext he⟩
  have hr : Nat.card (simpleRoot Q split j) = 8 := by
    have hh := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at hh
    omega
  have hc := Nat.card_le_card_of_surjective f hf
  change Nat.card C ≤ Nat.card (A × B) at hc
  simp only [Nat.card_prod,A,B,rootAt,card_rightConjugate,hr] at hc
  have hMC : (affineFixedSection Q split j hs hp hg).numerator ≤ C :=
    inf_le_inf_right _ (unipotent_inf_kernel_le_remainder Q split j)
  have hu := Nat.card_le_card_of_injective (inclusion hMC) (inclusion_injective hMC)
  have hl := affine_hexagon_fixed_section_lower_bound Q split hm i j hij hs hp hg
  omega

open BenderSuzuki.MatrixGroups
/-- The affine alternative is impossible opposite a nonbinary projective-unitary actor. -/
theorem no_affine_hexagon_of_projective_unitary
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : rankOne Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hroot : Nat.card (simpleRoot Q split i) = (2^n)^3)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) : False :=
  no_affine_hexagon_of_cartan_fixedFree Q split hm i j hij
    (unitary_cartan_all_roots_fixedFree J Q split hn hcard hconj i hKi μ hroot
      (actorReflection Q split i)) hs hp hg
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates BenderSuzuki.MatrixGroups
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
/-- The full special-unitary actor gives the same global affine contradiction. -/
theorem no_affine_hexagon_of_special_unitary
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : rankOne Q split i ≃* J.specialSubgroup)
    (hroot : Nat.card (simpleRoot Q split i) = (2^n)^3)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) : False :=
  no_affine_hexagon_of_cartan_fixedFree Q split hm i j hij
    (special_unitary_cartan_all_roots_fixedFree J Q split hn hcard hconj i hKi μ hroot
      (UnitarySource.actorReflection Q split i)) hs hp hg
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
