module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.LocalCover
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.HSOrders
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.HigmanSims

/-!
# Higman–Sims has no full Sylow pair at five

The product has a nontrivial two-core by its full Sylow order and its small
odd complement. The intrinsic normal-elementary Sylow catalogue identifies
the maximal two-local overgroup with one of the three concrete normalizers;
their five-parts exclude the original complement.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511;
GLS3 Table 5.3m for the actual HS local normalizers.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates

theorem higmanSims_no_five_pair (B : Subgroup Carrier) (S : Sylow 2 Carrier)
    (hB : XiOddQuotient 5 B)
    (hperm : (B : Set Carrier) * (S : Set Carrier) = (S : Set Carrier) * (B : Set Carrier)) :
    False := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨T,hT,hcover⟩ :=
    InvariantThree.SporadicRemaining.HigmanSims.exists_sylow_local_cover_of_catalogue
      subgroup_card normal_elementary_catalogue
  apply no_exceptional_pair_of_local_cover (Or.inl rfl) T (by rw [hT]; norm_num) _ B S hB hperm
  intro M hM hTM
  obtain ⟨i,rfl⟩ := hcover M hM hTM
  by_cases hi : i = 0
  · subst i; exact hs_central_local_twentyfive_not_dvd
  · exact hs_large_local_twentyfive_not_dvd i hi

variable {κ : GroupClass} {J : Type*} [Group J] [Finite J]
    {D B : Subgroup J} {S : Sylow 2 J}

theorem not_higmanSims
    (hA : OddCartan.AmbientInput κ D B S 5)
    (hB : SourceTransport.PairAction 5 (S : Subgroup J) B)
    (e : D ≃* Carrier) : False := by
  let : D.Normal := hA.normal
  obtain ⟨U,_,hU,hperm⟩ := exists_model_sylow_pair S hA.inside hB.oddComplement hA.permutes e
  exact higmanSims_no_five_pair _ U hU hperm
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
