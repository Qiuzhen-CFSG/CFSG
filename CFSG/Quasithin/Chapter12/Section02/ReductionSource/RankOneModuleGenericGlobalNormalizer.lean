module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalNormalizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalCompletion

/-!
# Normalizer geometry for the original Chapter12 pair

The common Sylow after the convention in 5.2.7 is T ∩ L = T ∩ K,
where K = O²(H). It need not equal the original sourceS in the degree-two
unitary extension. From the earlier core identities for GᵢT and the
nonexceptional conclusion K ∈ L*, the full normalizers have precisely
this Sylow normalizer as their intersection and supplement their local
factors by that intersection. Their generated subgroup has trivial two-core.

The application retains the actual chosen module and prepared whole-residual
pair. The common-Sylow and core identities from 5.2.7, right maximality
from 5.2.8, exhaustive F.1.12 comparison, and ambient recognition still
require their source proofs. In particular this is not DGS Theorem A or
GlobalExit. Original uniqueness remains in the prepared pair, with its
independent producer qt-d-1222-rankone-global-uniqueness.

Source: Aschbacher–Smith 5.3.1–2, printed pp.658–659, and the Chapter12
application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal normalizer pair satisfies the local conditions used in 5.3.2,
once the preceding common-Sylow, core and right-maximality conclusions are
supplied. The products retain the whole normalizer intersection. -/
theorem rankOne_global_normalizer_local_conditions
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hs : (T : Subgroup G) ⊓ L = (T : Subgroup G) ⊓ residual H)
    (hc : ∀ i : Fin 2,
      (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i ⊔
        (T : Subgroup G)).pCoreIn 2 = (![L,residual H] i).pCoreIn 2) :
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) :=
  d.normalizer_local_conditions (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hK rfl hs hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
