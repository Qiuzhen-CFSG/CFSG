module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.MarkedNaturalDual
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.JankoNatural
public import Theory.SpecificGroups.Janko4.Model.TrivialCommutantCentralizer

/-!
# J₄ exclusion for the literal binary natural-plus-dual section

The marked quotient action has trivial invertible commutant. The native
J₄ two-core comparison makes the centralizer of the original component
image odd. The opposite elementary moved factor then acts trivially on
J₄; faithful descent through I/Z(I) gives common centralization and the
source moved-normalizer contradiction.

This completes the final containing carrier for the natural-plus-dual row,
with all fixed vectors and nonsplit extensions retained. Quasisimple.Source
assembles the full row. Source: Aschbacher--Smith 10.2.9, pp.750--751.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c
theorem jankoFour_centralizer_odd_of_natural_dual [Group.IsPerfect I]
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (BinaryLinearThree.NaturalDual.action.comp
        (dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) (e : (I ⧸ center I) ≃* Janko4.Model) :
    let B := (L.subgroupOf I).map (e.toMonoidHom.comp (QuotientGroup.mk' (center I)))
    ¬ 2 ∣ Nat.card (centralizer (B : Set Janko4.Model)) := by
  obtain ⟨S,_,_,hSB,hSE,_,_,hE,hEB,_,hmove⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map (e.toMonoidHom.comp q)
  let E := ((⁅D.fullModule,L⁆).subgroupOf I).map (e.toMonoidHom.comp q)
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  let P := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPB : (P : Subgroup Janko4.Model) ≤ normalizer (B : Set Janko4.Model) := by
    change ((R : Subgroup (I ⧸ center I)).map e.toMonoidHom) ≤ _
    change _ ≤ normalizer (↑((L.subgroupOf I).map (e.toMonoidHom.comp q)) : Set Janko4.Model)
    rw [←Subgroup.map_map]
    exact
      (map_mono (f := e.toMonoidHom) hSB).trans (le_normalizer_map e.toMonoidHom)
  have hPE : (P : Subgroup Janko4.Model) ≤ normalizer (E : Set Janko4.Model) := by
    change ((R : Subgroup (I ⧸ center I)).map e.toMonoidHom) ≤ _
    change _ ≤ normalizer (↑(((⁅D.fullModule,L⁆).subgroupOf I).map (e.toMonoidHom.comp q)) : Set Janko4.Model)
    rw [←Subgroup.map_map]
    exact
      (map_mono (f := e.toMonoidHom) hSE).trans (le_normalizer_map e.toMonoidHom)
  have hEp : IsElementaryAbelian 2 E := by
    let := hE
    change IsElementaryAbelian 2 (((⁅D.fullModule,L⁆).subgroupOf I).map (e.toMonoidHom.comp q))
    rw [←Subgroup.map_map]
    exact IsElementaryAbelian.map (p := 2) (A := ((⁅D.fullModule,L⁆).subgroupOf I).map q) e.toMonoidHom
  have hEB' : E ≤ B := map_mono (comap_mono (source_full_moved_le_component D))
  have hcard : 2 < Nat.card E := by
    have hh := d.card_le_central_image I c.strict.le
      ((source_full_moved_le_component D).trans c.strict.le) le_rfl
    have he : Nat.card E = Nat.card (((⁅D.fullModule,L⁆).subgroupOf I).map q) := by
      dsimp only [E]
      rw [←Subgroup.map_map,card_map_of_injective e.injective]
    have hc : 2 < Nat.card BinaryLinearThree.NaturalDual.Space := by
      have hd : Nat.card (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) = 8 := by
        rw [Nat.card_congr (Pi.basisFun (ZMod 2) (Fin 3)).dualBasis.equivFun.toEquiv,
          Nat.card_fun,Nat.card_fin,Nat.card_zmod]
        decide
      simp only [BinaryLinearThree.NaturalDual.Space,BinaryLinearThree.Vector,
        Nat.card_prod,Nat.card_fun,Nat.card_fin,Nat.card_zmod,hd]
      decide
    exact hc.trans_le (he.symm ▸ hh)
  have hmov : ⁅E,B⁆ = E := by
    simpa only [E,B,map_commutator,map_map] using congrArg (map e.toMonoidHom) hmove
  let := hEp
  let π := dL.toMonoidHom.comp ((markedCoreQuotientEquiv D c.strict.le e).symm.toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 B)))
  obtain ⟨dB⟩ := marked_natural_dual_section D c.strict.le e dL d
  apply Janko4.centralizer_odd_of_trivial_commutant_section P B E dB _ hPB hPE hcard
    (marked_moved_core_centralizes D c.strict.le e) hmov
  intro f hf
  apply BinaryLinearThree.NaturalDual.centralizer_eq_one f
  intro g w
  obtain ⟨b,rfl⟩ := (dL.surjective.comp
    ((markedCoreQuotientEquiv D c.strict.le e).symm.surjective.comp
      (QuotientGroup.mk'_surjective (pCore 2 B)))) g
  exact hf b w

theorem jankoFour_common_centralizer_of_natural_dual [IsQuasisimple I]
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (BinaryLinearThree.NaturalDual.action.comp
        (dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) (e : (I ⧸ center I) ≃* Janko4.Model) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (I : Set G) := by
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  let : IsSimpleGroup Janko4.Model := e.symm.isSimpleGroup
  let : Group.IsPerfect Janko4.Model := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom.comp (QuotientGroup.mk' (center I)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  let B := (L.subgroupOf I).map (e.toMonoidHom.comp (QuotientGroup.mk' (center I)))
  have hodd := jankoFour_centralizer_odd_of_natural_dual D c dL d e
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
    Janko4.eq_one_of_fixes_odd_centralizer center_eq_bot_of_simple_perfect B hodd _
      (by rw [←map_pow,ha2,map_one]) hfix
  have ha : a = 1 := MulAut.centralQuotientAction_injective e
    (hqa.trans (map_one _).symm)
  intro i hi
  have hh := congrArg (fun b : MulAut I => (b ⟨i,hi⟩ : G)) ha
  change u*i*u⁻¹=i at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

theorem not_jankoFour_of_natural_dual [IsQuasisimple I]
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (BinaryLinearThree.NaturalDual.action.comp
        (dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) (e : (I ⧸ center I) ≃* Janko4.Model) : False :=
  source_a5_point_component_common_centralizer_impossible D c.t_mem c.moved_normalizer
    I c.escapes (jankoFour_common_centralizer_of_natural_dual D c dL d e)

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
