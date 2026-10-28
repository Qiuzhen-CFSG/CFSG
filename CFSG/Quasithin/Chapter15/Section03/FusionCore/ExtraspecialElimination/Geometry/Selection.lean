module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.Sections

/-!
# The selected endpoint and its actual quadratic offenders

F.9.16(4) selects the positive rank inequality between U_gamma/D_gamma and
U_H/D_H. The section-action kernel calculation identifies the first rank
with that of the actual star image. The image of D_H modulo Z is fixed by
V_gamma by cross-centralization. Counting its quotient therefore supplies
the precise input to RankComparison.offenders_of_crossCentralization_rank.
F.9.13(3) supplies quadratic action for V_gamma and hence U_gamma.

This proves ordinary offending only. B.1.2 best-offender status requires
all subgroup weight comparisons, which are not consequences of the single
selected rank inequality. No FF-star claim is made by this module.

Explicit earlier input: F.9.16(4)'s selected positive rank comparison.
The parent must supply the endpoint, together with the F.9.13 commutator
bound and the cross-centralizations proved in Geometry.Local.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
F.9.16(4), printed pp.323–324; 15.3.49(h), printed p.1143.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem sectionCentralizer_mono_left {X Y U Z : Subgroup G} (hXY : X ≤ Y) (hXZ : X ≤ normalizer (Z : Set G)) :
    sectionCentralizer X U Z ≤ sectionCentralizer Y U Z := by
  exact le_commutatorPreimage ((commutatorPreimage_le X U Z).trans hXY)
    (commutator_commutatorPreimage_le X U Z hXZ)

/-- The concrete rank comparison, fixed subspace, and quadratic ordinary offenders at a selected endpoint. -/
theorem selected_rank_and_quadratic_offenders
    (V ZS Z H Ug Vg Zg : Subgroup G)
    [IsElementaryAbelian 2 (localSpan ZS H)]
    [IsElementaryAbelian 2 Ug] [IsElementaryAbelian 2 Vg]
    (action : SectionAction H (localSpan ZS H) Z)
    (hZS : ZS ≤ V) (hUV : Ug ≤ Vg) (hVgH : Vg ≤ H)
    (hHZ : H ≤ centralizer (Z : Set G))
    (hUHZg : localSpan ZS H ≤ normalizer (Zg : Set G))
    (hcross : sectionCentralizer (localSpan V H) Ug Zg ≤ centralizer (Vg : Set G))
    (hcomm : ⁅localSpan ZS H, Vg⁆ ≤ Vg)
    (hselected : 0 < Nat.log 2 ((sectionCentralizer Ug (localSpan ZS H) Z).relIndex Ug) ∧
      Nat.log 2 ((sectionCentralizer (localSpan ZS H) Ug Zg).relIndex (localSpan ZS H)) ≤
        Nat.log 2 ((sectionCentralizer Ug (localSpan ZS H) Z).relIndex Ug)) :
    let D := sectionImage (localSpan ZS H) Z (sectionCentralizer (localSpan ZS H) Ug Zg)
    D ≤ fixedSpace action.representation (starImage H Vg) ∧
      Module.finrank (ZMod 2) (Additive (localSpan ZS H ⧸ Z.subgroupOf (localSpan ZS H)) ⧸ D) ≤
        rank (starImage H Ug) ∧
      IsOffender action.representation (starImage H Ug) ∧
      IsOffender action.representation (starImage H Vg) ∧
      IsQuadratic action.representation (starImage H Ug) ∧
      IsQuadratic action.representation (starImage H Vg) := by
  dsimp only
  let U := localSpan ZS H
  let DH := sectionCentralizer U Ug Zg
  let Dg := sectionCentralizer Ug U Z
  have hUgH := hUV.trans hVgH
  have hDg : Dg = Ug ⊓ localTwoCore H :=
    sectionCentralizer_eq_core_intersection H U Z Ug action hUgH
  have hrank : rank (starImage H Ug) = Nat.log 2 (Dg.relIndex Ug) :=
    starImage_rank H Ug Dg hUgH hDg
  have hZD : Z ≤ DH := by
    apply le_commutatorPreimage action.layer_le
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hUgH.trans hHZ))).le.trans bot_le
  have hDU : DH ≤ U := commutatorPreimage_le _ _ _
  have hDcross : DH ≤ centralizer (Vg : Set G) :=
    (sectionCentralizer_mono_left (conjugateSpanBy_mono hZS le_rfl) hUHZg).trans hcross
  have hfixed : sectionImage U Z DH ≤ fixedSpace action.representation (starImage H Vg) :=
    (sectionImage_le_fixedSpace_iff H U Z DH Vg action hDU hVgH).mpr
      ((commutator_eq_bot_iff_le_centralizer.mpr hDcross).le.trans bot_le)
  have hdim : Module.finrank (ZMod 2) (Additive (U ⧸ Z.subgroupOf U) ⧸ sectionImage U Z DH) ≤
      rank (starImage H Ug) := by
    rw [sectionImage_quotient_finrank U Z DH hZD, hrank]
    exact hselected.2
  have hstar : starImage H Ug ≤ starImage H Vg := map_mono (fun _ hx => hUV hx)
  have hUgne : starImage H Ug ≠ ⊥ := by
    intro he
    have hz := hselected.1
    rw [← hrank, he, Representation.BinaryOffender.rank_bot] at hz
    exact (Nat.lt_irrefl 0) hz
  have hVgne : starImage H Vg ≠ ⊥ := fun he => hUgne (le_bot_iff.mp (hstar.trans_eq he))
  have hUg : IsElementaryTwo (starImage H Ug) := by
    let := IsElementaryAbelian.subgroupOf (p := 2) hUgH
    exact ⟨hUgne, IsElementaryAbelian.map _⟩
  have hVg : IsElementaryTwo (starImage H Vg) := by
    let := IsElementaryAbelian.subgroupOf (p := 2) hVgH
    exact ⟨hVgne, IsElementaryAbelian.map _⟩
  obtain ⟨hoU, hoV⟩ := offenders_of_crossCentralization_rank action.representation
    (sectionImage U Z DH) (starImage H Ug) (starImage H Vg) hUg hVg hstar hfixed hdim
  have hquadV := quadratic_of_commutator_le H U Z Vg action hVgH hcomm
  have hquadU : IsQuadratic action.representation (starImage H Ug) :=
    fun a ha b hb v => hquadV a (hstar ha) b (hstar hb) v
  exact ⟨hfixed, hdim, hoU, hoV, hquadU, hquadV⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry
