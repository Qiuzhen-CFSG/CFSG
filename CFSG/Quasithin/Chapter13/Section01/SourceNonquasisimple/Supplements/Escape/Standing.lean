module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Source
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.GuardedPositiveStar

/-!
# The standing normalizers in the supplement argument

For a supported canonical radical X=Ξ_p(L), the original normalizer
calculation identifies N_G(X) with N_G(L). The guarded positive-star
theorem then identifies the unique maximal two-local over C_G(Ω₁Z(T));
the starred normalizer theorem identifies the unique overgroup of XT.
The multiple-overgroup assumption supplies the actual standing guard.

Canonical starred membership remains an explicit earlier obligation,
owned by the specialized radical-star construction. Neither the universal
A.3.12/C.2.7 inputs nor an unguarded 3.1.8 assertion are used here.
Source: Aschbacher--Smith 13.1.4--6 and (+), printed pp.867--868.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape
open Chapter1 Chapter1.Section02 Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The specialized earlier radical-star obligation, only for the faithful
maximal nonquasisimple components actually used in this argument. -/
def CanonicalStars (T : Sylow 2 G) : Prop :=
  ∀ K : Subgroup G, FaithfulMaximalLocal T K → ¬ IsQuasisimple (XiQuotient K) →
    ∀ p : ℕ, p.Prime → Odd p → p ∣ Nat.card (fittingSubgroup (XiQuotient K)) →
      XiP p K ∈ XiStar G (T : Subgroup G)

/-- The literal (+) assertions for any supported canonical radical.
The only undischarged earlier premise is this radical's starred membership. -/
theorem canonical_standing_of_star
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hs : XiP p L ∈ XiStar G (T : Subgroup G)) :
    normalizer (XiP p L : Set G) = normalizer (L : Set G) ∧
      IsMaximalTwoLocal (normalizer (L : Set G)) ∧
      XiP p L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      (∀ H : Subgroup G, IsMaximalTwoLocal H → XiP p L ⊔ (T : Subgroup G) ≤ H →
        H = normalizer (L : Set G)) ∧
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) ∧
      (∀ H : Subgroup G, IsMaximalTwoLocal H →
        centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ H →
        H = normalizer (L : Set G)) := by
  have hx := XiP_mem_XiPlus_source h.simpleQTKE T hL.1.1 hn ho hd
  obtain ⟨_,he,hm⟩ := RadicalConjugateRigidity.maximal_radical_structure
    h.simpleQTKE T hL.1 hn ho hd
  obtain ⟨_,hu⟩ := XiEmbedding.normalizer_unique_of_XiStar_knownSimple h.simpleQTKE T hs
  have hc := GuardedPositiveStar.positive_star_centralizer_unique h.simpleQTKE
    (Chapter3.source_guardedTheorem318One h.simpleQTKE) T
    (Chapter3.hasMaximalOutside_of_many T hmany) ⟨hx,hs⟩
  rw [he] at hc hu
  refine ⟨he,hm,?_,?_,hc.2.1,hc.2.2⟩
  · rw [← he]
    exact sup_le (XiP p L).le_normalizer hx.1.invariant
  · intro H hH hXH
    have hmH : H ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ XiP p L ⊔ (T : Subgroup G) ≤ N} :=
      ⟨hH,hXH⟩
    rw [hu] at hmH
    exact Set.mem_singleton_iff.mp hmH

/-- Every maximal faithful nonquasisimple component has the same centralizer
overgroup. Prime selection is provided by the actual maximal-counterexample
construction, not by an additional nonempty-radical assumption. -/
theorem nonquasisimple_centralizer_unique_of_stars
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    IsMaximalTwoLocal (normalizer (L : Set G)) ∧
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) ∧
      ∀ H : Subgroup G, IsMaximalTwoLocal H →
        centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ H →
        H = normalizer (L : Set G) := by
  have hf : L ∈ nonquasisimpleFaithful T :=
    ⟨(Adequate.mem_faithfulLocalComponents_iff T L).mpr ⟨hL.1.1,hL.2⟩,hn⟩
  obtain ⟨K,hK,hLK,_,_,_,_,_,p,hp,ho,_,hd,_⟩ := h.maximal_counterexample_of_many hmany hf
  have he : K = L := hL.1.2 K hK.1 hLK
  subst K
  let : Fact p.Prime := ⟨hp⟩
  have hc := canonical_standing_of_star h hmany hL hn ho hd (hs L hL hn p hp ho hd)
  exact ⟨hc.2.1,hc.2.2.2.2⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape
