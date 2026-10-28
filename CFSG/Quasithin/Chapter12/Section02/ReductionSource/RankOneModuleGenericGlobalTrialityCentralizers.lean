module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCentralizers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialityMaximal

/-!
# Central-involution control for the original triality completion

The genuine triality torus scales the highest-root parameter by arbitrary
nonzero base-field elements. The actual parabolic comparison transports
this orbit to the center of the original right residual. Right maximality
and a Sylow-central involution then give its full ambient centralizer bound.
Together with original left uniqueness this discharges both factor-center
bounds used in 5.3.3, with the literal whole overlap and source Sylow retained.

The original uniqueness in Preparation and the compatible comparison remain
explicit. Exhaustive F.1.12 comparison and concrete and ambient completion
recognition remain with the generic-global owner; no GlobalExit is claimed.
Source: Aschbacher–Smith 5.3.1–3, printed pp.658–659, and the Chapter12
application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal full-normalizer conditions and both central-involution
centralizer bounds for the original triality pair. -/
theorem rankOne_global_triality_normalizer_centralizer_conditions
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse)) :
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∧
    ∀ i : Fin 2, ∀ z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype,
      orderOf z = 2 → centralizer ({z} : Set G) ≤ normalizer (![L,residual H] i : Set G) := by
  exact ⟨D.rankOne_global_triality_normalizer_local_conditions h hmany hn hpsl hH d hp m hm he,
    d.triality_central_involution_centralizers
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
