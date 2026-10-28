module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.MarkedMovedSection
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Saturated
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import Theory.Representation.BinaryConjugationSection.CentralImage
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.NormalizedSectionFixer

/-!
# HS exclusion for the original natural binary-three section

The literal central-quotient images of L and [V,L] give a Sylow-normalized
subgroup whose order is divisible by 168 and an elementary section of order
at least eight. The concrete HS normalizer calculation makes each involution
fixing this subgroup trivial. Faithful descent gives common centralization
and contradicts the original moved-normalizer bound. The fixed kernel is
retained throughout, with no splitting assumption.

Source: Aschbacher--Smith 10.2.9, printed pp.750--751. Quasisimple.Source
uses this comparison for the actual natural and dual binary-three sections.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

theorem higmanSims_quotient_fixer_of_large_section [Group.IsPerfect I]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) L W}
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) ρ)
    (hc : 8 ≤ Nat.card W) (h168 : 168 ∣ Nat.card (L ⧸ pCore 2 L)) (e : (I ⧸ center I) ≃* Sporadic.LeechRelated.HS.Carrier) :
    let B := (L.subgroupOf I).map (e.toMonoidHom.comp (QuotientGroup.mk' (center I)))
    ∀ a : MulAut Sporadic.LeechRelated.HS.Carrier, a^2=1 → (∀ x ∈ B, a x=x) → a=1 := by
  obtain ⟨S,_,_,hSB,hSE,_,_,hE,_,_,_⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map (e.toMonoidHom.comp q)
  let E := ((⁅D.fullModule,L⁆).subgroupOf I).map (e.toMonoidHom.comp q)
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  let P := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPB : (P : Subgroup Sporadic.LeechRelated.HS.Carrier) ≤ normalizer (B : Set Sporadic.LeechRelated.HS.Carrier) := by
    change ((R : Subgroup (I ⧸ center I)).map e.toMonoidHom) ≤ _
    change _ ≤ normalizer (↑((L.subgroupOf I).map (e.toMonoidHom.comp q)) : Set Sporadic.LeechRelated.HS.Carrier)
    rw [←Subgroup.map_map]
    exact
      (map_mono (f := e.toMonoidHom) hSB).trans (le_normalizer_map e.toMonoidHom)
  have hPE : (P : Subgroup Sporadic.LeechRelated.HS.Carrier) ≤ normalizer (E : Set Sporadic.LeechRelated.HS.Carrier) := by
    change ((R : Subgroup (I ⧸ center I)).map e.toMonoidHom) ≤ _
    change _ ≤ normalizer (↑(((⁅D.fullModule,L⁆).subgroupOf I).map (e.toMonoidHom.comp q)) : Set Sporadic.LeechRelated.HS.Carrier)
    rw [←Subgroup.map_map]
    exact
      (map_mono (f := e.toMonoidHom) hSE).trans (le_normalizer_map e.toMonoidHom)
  have hEp : IsElementaryAbelian 2 E := by
    let := hE
    change IsElementaryAbelian 2 (((⁅D.fullModule,L⁆).subgroupOf I).map (e.toMonoidHom.comp q))
    rw [←Subgroup.map_map]
    exact IsElementaryAbelian.map (p := 2) (A := ((⁅D.fullModule,L⁆).subgroupOf I).map q) e.toMonoidHom
  have hcard : 8 ≤ Nat.card E := by
    have hh := d.card_le_central_image I c.strict.le
      ((source_full_moved_le_component D).trans c.strict.le) le_rfl
    have he : Nat.card E = Nat.card (((⁅D.fullModule,L⁆).subgroupOf I).map q) := by
      dsimp only [E]
      rw [←Subgroup.map_map,card_map_of_injective e.injective]
    exact hc.trans (he.symm ▸ hh)
  have hBE : B ≤ normalizer (E : Set Sporadic.LeechRelated.HS.Carrier) := by
    have hn : L.subgroupOf I ≤ normalizer ((⁅D.fullModule,L⁆).subgroupOf I : Set I) := by
      rw [←subgroupOf_normalizer_eq ((source_full_moved_le_component D).trans c.strict.le)]
      exact comap_mono (normalizer_commutator_ge_right _ _)
    exact (map_mono hn).trans (le_normalizer_map _)
  have h168B : 168 ∣ Nat.card B := by
    have hh := Nat.card_congr (markedCoreQuotientEquiv D c.strict.le e).toEquiv
    exact (hh ▸ h168).trans (card_quotient_dvd_card (pCore 2 B))
  exact Sporadic.LeechRelated.HS.eq_one_of_fixes_normalized_large_section
    P B E hPB hPE hBE hEp hcard h168B

theorem higmanSims_common_centralizer_of_large_section [IsQuasisimple I]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) L W}
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) ρ)
    (hc : 8 ≤ Nat.card W) (h168 : 168 ∣ Nat.card (L ⧸ pCore 2 L)) (e : (I ⧸ center I) ≃* Sporadic.LeechRelated.HS.Carrier) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (I : Set G) := by
  let B := (L.subgroupOf I).map (e.toMonoidHom.comp (QuotientGroup.mk' (center I)))
  have hfixer := higmanSims_quotient_fixer_of_large_section D c d hc h168 e
  let U := (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
  let := source_original_full_moved_elementary D
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  intro u hu
  let a : MulAut I := I.normalizerMonoidHom ⟨u,partner_normalizes D c hu⟩
  have ha2 : a ^ 2 = 1 := by
    change (I.normalizerMonoidHom ⟨u,partner_normalizes D c hu⟩) ^ 2 = 1
    rw [←map_pow]
    have he : (⟨u,partner_normalizes D c hu⟩ : normalizer (I : Set G)) ^ 2 = 1 :=
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := U) u hu)
    rw [he,map_one]
  have hfix : ∀ x ∈ B, MulAut.centralQuotientAction e a x = x := by
    intro x hx
    obtain ⟨l,hl⟩ := markedLocalHom_surjective c.strict.le e ⟨x,hx⟩
    have hxval := congrArg Subtype.val hl
    change e (QuotientGroup.mk' (center I) (inclusion c.strict.le l)) = x at hxval
    rw [←hxval,MulAut.centralQuotientAction_apply]
    have hal : a (inclusion c.strict.le l) = inclusion c.strict.le l := by
      apply Subtype.ext
      change u*l.val*u⁻¹=l.val
      exact mul_inv_eq_iff_eq_mul.mpr (c.crossed hu l.val l.property).symm
    rw [hal]
  have hqa : MulAut.centralQuotientAction e a = 1 :=
    hfixer _
      (by rw [←map_pow,ha2,map_one]) hfix
  have ha : a = 1 := MulAut.centralQuotientAction_injective e
    (hqa.trans (map_one _).symm)
  intro i hi
  have hh := congrArg (fun b : MulAut I => (b ⟨i,hi⟩ : G)) ha
  change u*i*u⁻¹=i at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

theorem not_higmanSims_of_large_section [IsQuasisimple I]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) L W}
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) ρ)
    (hc : 8 ≤ Nat.card W) (h168 : 168 ∣ Nat.card (L ⧸ pCore 2 L)) (e : (I ⧸ center I) ≃* Sporadic.LeechRelated.HS.Carrier) : False :=
  source_a5_point_component_common_centralizer_impossible D c.t_mem c.moved_normalizer
    I c.escapes (higmanSims_common_centralizer_of_large_section D c d hc h168 e)

theorem not_higmanSims_of_natural_binary_three [IsQuasisimple I]
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      ((specialLinearNatural (k := ZMod 2) 3).comp
        (dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (e : (I ⧸ center I) ≃* Sporadic.LeechRelated.HS.Carrier) : False := by
  exact not_higmanSims_of_large_section D c d (by
    simp only [Nat.card_fun,Nat.card_fin,Nat.card_zmod]; decide) (by
    rw [Nat.card_congr dL.toEquiv,Matrix.PSL3Two.card_SL]) e
/-- The dual marking gives the same exclusion, with its literal fixed kernel. -/
theorem not_higmanSims_of_dual_binary_three [IsQuasisimple I]
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      ((specialLinearNatural (k := ZMod 2) 3).dual.comp
        (dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (e : (I ⧸ center I) ≃* Sporadic.LeechRelated.HS.Carrier) : False := by
  apply not_higmanSims_of_large_section D c d _ (by
    rw [Nat.card_congr dL.toEquiv,Matrix.PSL3Two.card_SL]) e
  rw [Nat.card_congr (Pi.basisFun (ZMod 2) (Fin 3)).dualBasis.equivFun.toEquiv,
    Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  decide

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
