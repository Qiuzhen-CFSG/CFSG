module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.GroupTheory.InvariantLocalPairCover
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.LocalGeneration

/-!+# The concrete rank-two local cover for HS and its two-extensions

Transport the proved HS generating pair to the normal subgroup `L`, aligning
the marked Sylow with the actual intersection `T ∩ L`. Each transported local
is normalized by `T`, so adjoining `T` gives two Sylow overgroups generating
`L T = G`. The literal quotient of each overgroup by its intrinsic two-core
embeds in the automorphism group of S₅ or SL₃(2), respectively. Both full
automorphism groups have two-rank at most two.

Thus outer two-extensions are included without identifying their local
quotients with the simple-case quotients. The construction needs only a normal
HS copy and the supplied Sylow supplement. The source-facing theorem retains
the SQTK, generalized-Fitting, simplicity and actual-model hypotheses.

Source: Aschbacher–Smith E.1.14(5), printed p.214, citing Asc82a Lemma 4.9;
the local descriptions are A.3.12(18), p.47, and I.4.8, p.418. This supplies
the local-cover input to E.1.12. E-generation existence and the final
E-generation assertion remain with the parent Higman–Sims assembly.
-/

public section
namespace CFSG.Quasithin.ChapterE.HigmanSims

open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.HS

universe u
variable {G : Type u} [Group G] [Finite G]

/-- A normal copy of the exact HS carrier and any Sylow two-supplement admit
the required generating cover, including all outer two-extensions. -/
theorem exists_local_cover_of_normal_hs
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (hLT : L ⊔ (T : Subgroup G) = ⊤) (e : L ≃* Carrier) :
    ∃ Δ : Set (Subgroup G), sSup Δ = ⊤ ∧
      ∀ H ∈ Δ, (T : Subgroup G) ≤ H ∧ primeRank 2 (H ⧸ pCore 2 H) ≤ 2 :=
  exists_rankTwo_cover_of_invariant_pair L T e hLT BlockNormalizer.baseSylow
    LocalGeneration.member LocalGeneration.members_sup_eq_top
    LocalGeneration.member_invariant LocalGeneration.quotient_center
    LocalGeneration.quotient_automorphism_rank

/-- The concrete local-cover input for the HS clause of E.1.14(5), under
exactly the source hypotheses and with no generation or local-rank premise. -/
theorem exists_local_cover {K : GroupClass.{u}}
    (_hG : IsSQTK K G) (_hL : IsSimpleGroup (generalizedFitting G))
    (T : Sylow 2 G) (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (e : generalizedFitting G ≃* Carrier) :
    ∃ Δ : Set (Subgroup G), sSup Δ = ⊤ ∧
      ∀ H ∈ Δ, (T : Subgroup G) ≤ H ∧ primeRank 2 (H ⧸ pCore 2 H) ≤ 2 :=
  exists_local_cover_of_normal_hs (generalizedFitting G) T hLT e

end CFSG.Quasithin.ChapterE.HigmanSims
