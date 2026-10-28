module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.Applicability
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Assembly

/-!
# The actual source quotient in the terminal configuration

F.6.18 requires a quotient of an SQTK group by O_{3'}, not an arbitrary
quotient by O₂. The terminal configuration supplies equality of those
intrinsic cores. Its induced quotient equivalence commutes with the literal
quotient maps. The local groups descend as a genuine Goldschmidt triple.

The image of X_E is nonzero because X_E is outside M, whereas the kernel
O₂(H) is contained in T_E ≤ T ≤ M. Thus the supplied offender-image
containment gives a nontrivial offender actor satisfying every B.5.3
hypothesis. No centrality or common-local-core bound is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, F.6.18,
pp.309–310, and 15.3.67(3), 15.3.68(4),(5), pp.1153–1155.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u v

/-- The exact quotient condition in F.6.18, retaining the actual cover and map.
This is source input data, not a classification assertion. -/
structure ThreePrimeSQTKQuotient (K : GroupClass.{u}) (D : Type u) [Group D] where
  Cover : Type u
  [coverGroup : Group Cover]
  [coverFinite : Finite Cover]
  sqtk : IsSQTK K Cover
  equiv : (Cover ⧸ pPrimeCore 3 Cover) ≃* D

variable {H : Type u} [Group H] [Finite H]

/-- Equality of the source cores provides the genuine O_{3'} quotient witness. -/
noncomputable def threePrimeSQTKQuotient_of_core_eq {K : GroupClass.{u}}
    (hH : IsSQTK K H) (hc : pPrimeCore 3 H = pCore 2 H) :
    ThreePrimeSQTKQuotient K (H ⧸ pCore 2 H) where
  Cover := H
  sqtk := hH
  equiv := QuotientGroup.quotientMulEquivOfEq hc

/-- The quotient witness uses the original quotient maps, literally. -/
theorem threePrimeSQTKQuotient_of_core_eq_mk {K : GroupClass.{u}}
    (hH : IsSQTK K H) (hc : pPrimeCore 3 H = pCore 2 H) (h : H) :
    (threePrimeSQTKQuotient_of_core_eq hH hc).equiv
      (QuotientGroup.mk' (pPrimeCore 3 H) h) = QuotientGroup.mk' (pCore 2 H) h := by
  exact QuotientGroup.quotientMulEquivOfEq_mk hc h

variable {G : Type u} [Group G] [Finite G]

/-- The earlier source escape gives a nonzero image of X_E in H/O₂(H). -/
theorem terminal_X_image_ne_bot (T : Sylow 2 G) (M Y V E F : Subgroup G)
    (d : OrthogonalFourBinary.NaturalAction V M)
    (c : TerminalConfiguration T M Y V E F d) (hTM : (T : Subgroup G) ≤ M)
    (hX : ¬ lineX E ≤ M) :
    ((lineX E).subgroupOf (amalgamGroup Y T E F)).map
      (QuotientGroup.mk' (pCore 2 (amalgamGroup Y T E F))) ≠ ⊥ := by
  let H := amalgamGroup Y T E F
  have hXH : lineX E ≤ H := le_sup_left.trans le_sup_right
  have hQM : (pCore 2 H).map H.subtype ≤ M := by
    obtain ⟨S, hS, _⟩ := c.extension
    calc
      (pCore 2 H).map H.subtype ≤ (S : Subgroup H).map H.subtype :=
        map_mono (pCore_isPGroup.le_sylow_of_normal S)
      _ = lineT T E := hS
      _ ≤ M := inf_le_left.trans hTM
  intro hz
  have hle : (lineX E).subgroupOf H ≤ pCore 2 H := by
    exact (Subgroup.map_eq_bot_iff _).mp hz |>.trans (QuotientGroup.ker_mk' _).le
  apply hX
  rw [← map_subgroupOf_eq_of_le hXH]
  exact (map_mono hle).trans hQM

/-- Both source classifications apply at the literal quotient and offender
actor. The conclusion keeps the complete B.5.3 record, the actual O_{3'}
cover, the local triple, and the nonzero offender image separate. -/
theorem terminal_classification_applicability {K : GroupClass.{u}}
    (T : Sylow 2 G) (M Y V E F : Subgroup G)
    (d : OrthogonalFourBinary.NaturalAction V M)
    (c : TerminalConfiguration T M Y V E F d)
    (hH : IsSQTK K (amalgamGroup Y T E F)) (hTM : (T : Subgroup G) ≤ M)
    (hX : ¬ lineX E ≤ M)
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (ρ : Representation (ZMod 2)
      (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) W)
    (hfaith : Function.Injective ρ)
    (hXI : ((lineX E).subgroupOf (amalgamGroup Y T E F)).map
      (QuotientGroup.mk' (pCore 2 (amalgamGroup Y T E F))) ≤ offenderSubgroup ρ) :
    Nonempty (ThreePrimeSQTKQuotient K
      (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F))) ∧
    ChapterF.IsGoldschmidtTriple
      (((firstAmalgamGroup Y T E F).subgroupOf (amalgamGroup Y T E F)).map
        (QuotientGroup.mk' (pCore 2 (amalgamGroup Y T E F))))
      (((secondAmalgamGroup T E).subgroupOf (amalgamGroup Y T E F)).map
        (QuotientGroup.mk' (pCore 2 (amalgamGroup Y T E F)))) ∧
    FFHypothesis K (ρ.comp (offenderSubgroup ρ).subtype) ∧ offenderSubgroup ρ ≠ ⊥ := by
  have hcore := CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.coreQuotient_twoCore
    (H := amalgamGroup Y T E F)
  exact ⟨⟨threePrimeSQTKQuotient_of_core_eq hH c.core_eq⟩,
    goldschmidt_twoCore_quotient _ _ c.goldschmidt,
    offender_source_hypothesis hH (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      hcore ρ hfaith,
    fun hz => terminal_X_image_ne_bot T M Y V E F d c hTM hX
      (le_bot_iff.mp (hz ▸ hXI))⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
