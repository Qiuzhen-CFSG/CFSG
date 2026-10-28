module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear.Doubled
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.RadicalInitial

/-!
# The original point centralizer from the initial moved module

The chosen seed lies in the initial moved subgroup [Omega1 Z(O2(LR1)),L].
The intrinsic initial module is natural or doubled natural. In the natural
case its order identifies it with V. In the doubled case, the two coordinate
projections show that fixing the original point fixes every Sylow-fixed
vector. The genuine initial Sylow splitting therefore computes
C_LR1(Omega1 Z(S')) = C_L(V1) R1, where S' is the actual T intersect LR1.
Its two-core is R1. The intrinsic doubled-initial radical inequality then
excludes that case, so the initial moved subgroup is exactly V.

These results need no model of the whole commutator core or its center,
and retain every nonbinary field, including field four. The final Sylow
splitting keeps the full central attachment. Source.lean applies the core
identity to the original point-recognition consumer of RadicalAssembly.
The remaining whole-core classification belongs to
qt-c134-nonbinary-linear-three-source; it is not inferred from the initial
subgroup equality. Final 11.1.5 assembly stays with the normalizer owner.
Source: Aschbacher--Smith C.1.34, pp.136--137, and 11.1.5, pp.765--766.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear
open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource
open PointCohomology.PointGeometry.SL3Core
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
  (f : InvariantFlag (.sl3 m))
local notation "J" => (L ⊔ f.Ri 0 : Subgroup G)
local notation "P" => (((T : Subgroup G) ⊓ J) : Subgroup G)
local notation "U" => initialMoved L (f.Ri 0)
local notation "ρ" => specialLinearNatural (k := S.field.Carrier) 3

/-- The original chosen seed lies in the actual initial moved subgroup. -/
theorem seed_le_initialMoved : V ≤ U := by
  have hV : V ≤ initialOmega L (f.Ri 0) := by
    rw [initialOmega_eq]
    intro v hv
    refine (mem_omegaCenterIn_iff _ _).mpr ⟨seed_le_pointCore D S f hv,?_,?_⟩
    · intro x hx
      exact (D.core_centralizes (pointCore_le_core D S f hx) v hv).symm
    · let := D.elementary
      exact elemPow_eq_one_of_isElementaryAbelian v hv
  exact D.eq_commutator.le.trans (commutator_mono hV le_rfl)

private theorem initial_eq_seed_of_natural
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (hm : HasSectionModel L U ⊥ (linearThreeActor e) ρ) : U = V := by
  apply (Subgroup.eq_of_le_of_card_ge (seed_le_initialMoved D S m f) ?_).symm
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,a,_⟩ := hm
  let := hn
  have hc : Nat.card U = Nat.card (Fin 3 → S.field.Carrier) :=
    Nat.card_congr (QuotientGroup.quotientBot.symm.trans a).toEquiv
  rw [hc,seed_card D S m]

private theorem seed_sylow_fixed_le_point :
    V ⊓ centralizer (P : Set G) ≤ f.Vi 0 := by
  rw [←local_core_fixed D S m f]
  apply inf_le_inf_left _ (centralizer_le ?_)
  apply le_trans _ (radical_le_pointSylow D S f)
  exact pCoreIn_mono_of_normalizes le_sup_left
    (sup_le (f.Li 0).le_normalizer (f.sylow_normalizes_Li 0))

/-- The initial module suffices to compute the whole Sylow-omega centralizer
at the original point, before any whole-core classification. -/
theorem point_sylowOmega_centralizer
    (hm : NonbinaryMSPair S.field L (f.Ri 0)) :
    J ⊓ centralizer (Subgroup.omegaCenterIn P : Set G) =
      (L ⊓ centralizer (f.Vi 0 : Set G)) ⊔ f.Ri 0 := by
  have hi := point_linearThreeMSPair D S m f hm
  have hfix : L ⊓ centralizer (f.Vi 0 : Set G) ≤
      centralizer ((U ⊓ centralizer (P : Set G) : Subgroup G) : Set G) := by
    obtain ⟨e,he⟩ := initialMoved_section_models hi S.nonbinary
    rcases he with hn | hd
    · rw [initial_eq_seed_of_natural D S m f e hn]
      exact inf_le_right.trans (centralizer_le (seed_sylow_fixed_le_point D S m f))
    · apply (point_fixer_centralizes_doubled_fixed D S m f
        (seed_le_initialMoved D S m f) e hd).trans
      apply centralizer_le
      have hLP : (T : Subgroup G) ⊓ L ≤ P := inf_le_inf_left _ le_sup_left
      exact inf_le_inf_left _ (centralizer_le hLP)
  rw [omega_centralizer_join D S m f]
  congr 1
  apply le_antisymm (omega_fixer_le_point_fixer D S m f)
  change L ⊓ centralizer (f.Vi 0 : Set G) ≤
    L ⊓ centralizer (SourceInterface.omegaCenterIn P : Set G)
  rw [SylowInitial.component_centralizer hi S.nonbinary (pointSylow_isSylowIn D S f)]
  exact le_inf inf_le_left hfix

/-- The literal radical is the two-core of the original Sylow-omega
centralizer, with no whole-center or whole-core model premise. -/
theorem point_sylowOmega_centralizer_core
    (hm : NonbinaryMSPair S.field L (f.Ri 0)) :
    (J ⊓ centralizer (Subgroup.omegaCenterIn P : Set G)).pCoreIn 2 = f.Ri 0 := by
  rw [point_sylowOmega_centralizer D S m f hm,point_fixer_core D S m f]

/-- The nonblock radical inequality is impossible at the original point,
independently of the still-open intrinsic module classification. -/
theorem point_not_MSNotCentralizerCore
    (hm : NonbinaryMSPair S.field L (f.Ri 0)) :
    ¬ MSNotCentralizerCore L (f.Ri 0) P := by
  intro h
  exact h (point_sylowOmega_centralizer_core D S m f hm).symm

/-- The actual point's initial moved subgroup is exactly the original V,
including at field four. This makes no assertion about the whole MS core. -/
theorem point_initialMoved_eq_seed
    (hm : NonbinaryMSPair S.field L (f.Ri 0)) : U = V := by
  have hi := point_linearThreeMSPair D S m f hm
  obtain ⟨e,he⟩ := initialMoved_section_models hi S.nonbinary
  rcases he with hn | hd
  · exact initial_eq_seed_of_natural D S m f e hn
  · exact (point_not_MSNotCentralizerCore D S m f hm
      (RadicalInitial.notCentralizerCore_of_initial_doubled hi S.nonbinary e hd
        (pointSylow_isSylowIn D S f) (radical_le_pointSylow D S f))).elim

/-- The actual Sylow omega splits over the original seed's fixed subgroup
and the center of LR₁; this retains the full central attachment. -/
theorem point_sylowOmega_split
    (hm : NonbinaryMSPair S.field L (f.Ri 0)) :
    SourceInterface.omegaCenterIn P =
      (V ⊓ centralizer (P : Set G)) ⊔ SourceInterface.omegaCenterIn J ∧
    (V ⊓ centralizer (P : Set G)) ⊓ SourceInterface.omegaCenterIn J = ⊥ := by
  have hs := SylowInitial.sylowOmega_split_center
    (point_linearThreeMSPair D S m f hm) S.nonbinary
    (pointSylow_isSylowIn D S f) (radical_le_pointSylow D S f)
  simpa only [point_initialMoved_eq_seed D S m f hm] using hs

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear
