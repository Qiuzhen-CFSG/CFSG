module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SpecialUnitaryEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallSuzukiEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.DihedralApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.ActorData

/-!
# The exhaustive enlargement split with small unitary cases retained

The original five rank-one rows give an actual model of the enlarged
core quotient unless the original quotient is PSU₃(2) or SU₃(2). The
linear and all-parameter Suzuki cases preserve the starred subgroup;
the dihedral branch retains its genuine D₁₀-or-Sz(2) alternative. Both
unitary forms preserve the starred subgroup for every degree at least two.
No scalar center, local core, or original quotient marking is replaced.

The reduced F1.11 application preserves the two small original quotient
alternatives literally. When those alternatives are excluded, original
conjugation supplies actual actor models at every vertex and discharges
that exact premise in the Chapter 7 consumer. Small-model exclusion and
the general 6.5 obstruction remain explicit there; full source assembly
must discharge them. This does not establish unconditional 6.1 or 6.5.

Source: DGS, Groups and Graphs (1985), Hypothesis A p.94, reduction p.95,
6.1 and its remark pp.118--119, and 7.1--7.5 pp.126--131.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P B : Subgroup G}

/-- Every original rank-one row now supplies the actual enlarged quotient
model, except for the two explicitly retained unitary models of fixed-field order two. -/
theorem localEnlargement_rankOne_or_small_unitary (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B) :
    IsRankOneModel (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ∨
      ClassicalGroup.IsPSU (d.Pstar ⧸ pCore 2 d.Pstar) 3 2 ∨
        IsSU (d.Pstar ⧸ pCore 2 d.Pstar) 3 2 := by
  have heq (he : localEnlargement d = d.Pstar) :
      IsRankOneModel (localEnlargement d ⧸ pCore 2 (localEnlargement d)) := by
    let e := MulEquiv.subgroupCongr he
    exact d.quotient.of_equiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  cases d.quotient with
  | linear n hn hm =>
    obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    let := hF
    let := hfin
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact Or.inl (heq (localEnlargement_eq_star_of_linear d hB e))
  | suzuki m he =>
    exact Or.inl (heq (localEnlargement_eq_star_of_suzuki_all d m he.some))
  | projective_unitary n hn hm =>
    by_cases hl : 2 ≤ n
    · exact Or.inl (heq (localEnlargement_eq_star_of_isPSU d hB hl hm))
    · have he : n = 1 := by omega
      subst n
      exact Or.inr (Or.inl (by simpa only [pow_one] using hm))
  | special_unitary n hn hm =>
    by_cases hl : 2 ≤ n
    · exact Or.inl (heq (localEnlargement_eq_star_of_isSU d hB hl hm))
    · have he : n = 1 := by omega
      subst n
      exact Or.inr (Or.inr (by simpa only [pow_one] using hm))
  | dihedral he =>
    rcases localEnlargement_dihedral_alternatives d he.some with hh | hh
    · exact Or.inl (heq hh)
    · exact Or.inl (.suzuki 0 hh)

namespace Reduction
open Subgroup.CosetGeometry.RankTwo
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The exhaustive source split for the original enlarged endpoint. The
remaining alternatives keep the original degree-one unitary quotient markings. -/
theorem reduced_enlargement_rankOne_or_small_unitary (h : HypothesisF11 L S) (i : Fin 2) :
    IsRankOneModel (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) ∨
      ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2 ∨ IsSU (L i ⧸ pCore 2 (L i)) 3 2 := by
  let hh := SuzukiContainment.reduced_hypothesis h
  have hb : ∃ T : Sylow 2 (commonBorel L (SuzukiContainment.reducedSylow L S)),
      (T : Subgroup (commonBorel L (SuzukiContainment.reducedSylow L S))) =
        pCore 2 (commonBorel L (SuzukiContainment.reducedSylow L S)) := by
    apply f11_borel_core_sylow hh
    exact (normal_subgroupOf_iff_le_normalizer
      (show SuzukiContainment.reducedSylow L S ≤ commonBorel L (SuzukiContainment.reducedSylow L S)
        from le_sup_right)).mp (SuzukiContainment.reduced_sylow_normal h)
  rcases localEnlargement_rankOne_or_small_unitary (hh.starredLocalRankOneData i) hb with hm | hp | hs
  · left
    rwa [reduced_localEnlargement_eq h i] at hm
  · right; left
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hp
    exact ⟨F,hF,hfin,J,hcard,hconj,⟨(hh.starredQuotientEquiv i).trans e⟩⟩
  · right; right
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hs
    exact ⟨F,hF,hfin,J,hcard,hconj,⟨(hh.starredQuotientEquiv i).trans e⟩⟩

/-- Away from the two explicit small original unitary quotients, all five
source families supply genuine enlarged models at every graph vertex. -/
theorem reduced_actor_models_of_no_small_unitary (h : HypothesisF11 L S)
    (hsmall : ∀ i : Fin 2, ¬ ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2 ∧
      ¬ IsSU (L i ⧸ pCore 2 (L i)) 3 2)
    (v : Vertex (reducedFamily L S)) :
    IsRankOneModel (graphLocalGroup (reducedFamily L S) v ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) v)) := by
  have hi (i : Fin 2) : IsRankOneModel (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) := by
    rcases reduced_enlargement_rankOne_or_small_unitary h i with hh | hp | hs
    · exact hh
    · exact ((hsmall i).1 hp).elim
    · exact ((hsmall i).2 hs).elim
  have hb (i : Bool) : IsRankOneModel (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i))) := by
    apply IsRankOneModel.of_equiv ?_ (reduced_graphEnlargementQuotient h i)
    cases i
    · exact hi 0
    · exact hi 1
  let F := reducedFamily L S
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  let A := graphLocalGroup F (base F v.type)
  have heq : A.map (MulAut.conj g).toMonoidHom = graphLocalGroup F v :=
    (graphLocalGroup_conjugate (reduced_triple h) g (base F v.type)).symm.trans
      (congrArg (graphLocalGroup F) hg)
  let a : A ≃* graphLocalGroup F v :=
    (A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr heq)
  exact (hb v.type).of_equiv (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm

/-- The literal Chapter 7 consumer now needs only the retained small-model
exclusions and the general 6.5 adjacent-core obstruction. -/
theorem reduced_noncommuting_distance_bound_of_no_small_unitary (h : HypothesisF11 L S)
    (hsmall : ∀ i : Fin 2, ¬ ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2 ∧
      ¬ IsSU (L i ⧸ pCore 2 (L i)) 3 2)
    (hob : ∀ x y, (graph (reducedFamily L S)).Adj x y →
      ¬ stabilizer (reducedFamily L S) y ≤ normalizer
        ((Q (reducedFamily L S) x ⊓ Q (reducedFamily L S) y : Subgroup (G₀ L S)) : Set (G₀ L S)))
    {v w : Vertex (reducedFamily L S)} (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v,Z (reducedFamily L S) w⁆ ≠ ⊥) :
    (b (reducedFamily L S) = 1 ∨ b (reducedFamily L S) = 2) ∧
    Noncommuting.HasNaturalCenter (graphLocalGroup (reducedFamily L S) v)
      (Z (reducedFamily L S) v) (Q (reducedFamily L S) v) ∧
    Noncommuting.HasNaturalCenter (graphLocalGroup (reducedFamily L S) w)
      (Z (reducedFamily L S) w) (Q (reducedFamily L S) w) :=
  Noncommuting.Reduction.reduced_distance_bound_of_actor_models h
    (reduced_actor_models_of_no_small_unitary h hsmall) hob hc hne

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
