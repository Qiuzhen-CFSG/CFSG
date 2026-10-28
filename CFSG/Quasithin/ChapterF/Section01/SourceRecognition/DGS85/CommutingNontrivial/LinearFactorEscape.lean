module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.FactorComparison

/-!
# Reciprocal escape with a linear starting quotient

The ending factor discharges the numerical premise of the starting-center
recognition argument. This proves full reciprocal escape for two linear
endpoints, and excludes reverse containment for all Suzuki, D₁₀ and
large-unitary ending quotients. Any remaining reverse containment with
linear starting quotient has an actual SU₃(2) or PSU₃(2) ending quotient.

The critical pair may have either orientation. All models, conjugation
actions, cores, spans and Borel data belong to the original F1.11 reduction.
The two small-unitary factor cases, non-linear starting cases and 8.3--8.7
remain Chapter 8 obligations; this is not a distance-three conclusion.
Source: DGS, Groups and Graphs (1985), 8.2, printed pp.134--135.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G] {J : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Full 8.2 for two supplied linear endpoint quotients: the factor bound,
fixed generation and natural-case contradiction are all discharged. -/
theorem reduced_reciprocal_escape_of_linear_endpoints
    (h : HypothesisF11 J S)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S),
      (graph (Reduction.reducedFamily J S)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S) w ⊓ Q (Reduction.reducedFamily J S) v :
          Subgroup (Reduction.G₀ J S)) : Set (Reduction.G₀ J S)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S) a a')
    (hab : (graph (Reduction.reducedFamily J S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S)).dist beta a' + 1 = b (Reduction.reducedFamily J S))
    (hb : 1 < b (Reduction.reducedFamily J S))
    (hcomm : ⁅Z (Reduction.reducedFamily J S) a,Z (Reduction.reducedFamily J S) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S) beta 1 ⊓ Q (Reduction.reducedFamily J S) a',
      V (Reduction.reducedFamily J S) a' 1⁆ ≠ ⊥)
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily J S) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) a)) ≃* SL(2,K))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (e' : (graphLocalGroup (Reduction.reducedFamily J S) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) a')) ≃* SL(2,F)) :
    ¬ V (Reduction.reducedFamily J S) a' 1 ≤ Q (Reduction.reducedFamily J S) beta := by
  exact source_reciprocal_linear_escape_of_factor_bound (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reducedEarlierLocalTheorems h hob)
    hc hab hd hb hcomm models hne hn hK e
    (reduced_ending_linear_constituent_bound h hc hab hd hb hcomm hm hF e')

/-- In the full source catalogue, reverse containment with a linear
starting quotient can only have a field-two unitary ending quotient.
Every other ending factor is excluded on the original reduced action. -/
theorem reduced_linear_reverse_endpoint_unitary_two
    (h : HypothesisF11 J S)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S),
      (graph (Reduction.reducedFamily J S)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S) w ⊓ Q (Reduction.reducedFamily J S) v :
          Subgroup (Reduction.G₀ J S)) : Set (Reduction.G₀ J S)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S) a a')
    (hab : (graph (Reduction.reducedFamily J S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S)).dist beta a' + 1 = b (Reduction.reducedFamily J S))
    (hb : 1 < b (Reduction.reducedFamily J S))
    (hcomm : ⁅Z (Reduction.reducedFamily J S) a,Z (Reduction.reducedFamily J S) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S) beta 1 ⊓ Q (Reduction.reducedFamily J S) a',
      V (Reduction.reducedFamily J S) a' 1⁆ ≠ ⊥)
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily J S) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) a)) ≃* SL(2,K))
    (hreverse : V (Reduction.reducedFamily J S) a' 1 ≤ Q (Reduction.reducedFamily J S) beta) :
    let D := graphLocalGroup (Reduction.reducedFamily J S) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) a')
    ClassicalGroup.IsPSU D 3 2 ∨ IsSU D 3 2 := by
  let Γ := Reduction.reducedFamily J S
  have hno (hh : (Q Γ a').relIndex (Z Γ a) ≤
      (centralizer (Z Γ a : Set (Reduction.G₀ J S))).relIndex (V Γ a' 1)) : False :=
    source_reciprocal_linear_escape_of_factor_bound (Reduction.reduced_triple h)
      (Reduction.reduced_borel_core_sylow h) (Reduction.reducedEarlierLocalTheorems h hob)
      hc hab hd hb hcomm models hne hn hK e hh hreverse
  have hsquare (hh : ((Q Γ a').relIndex (Z Γ a))^2 ≤
      (centralizer (Z Γ a : Set (Reduction.G₀ J S))).relIndex (V Γ a' 1)) : False :=
    hno ((Nat.le_self_pow (by decide : 2 ≠ 0) _).trans hh)
  cases models a' with
  | linear m hm hi =>
    obtain ⟨F,_,_,hF,⟨e'⟩⟩ := hi
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let f := e'.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
    exact (hno (reduced_ending_linear_constituent_bound h hc hab hd hb hcomm hm hF f)).elim
  | suzuki m hi =>
    exact (hsquare (reduced_ending_suzuki_constituent_bound h hc hab hd hb hcomm m hi.some)).elim
  | projective_unitary m hm hi =>
    by_cases hm2 : 2 ≤ m
    · obtain ⟨F,_,_,T,hF,hconj,⟨f⟩⟩ := hi
      exact (hsquare (reduced_ending_projective_unitary_constituent_bound h hc hab hd hb hcomm
        T hm2 hF hconj f)).elim
    · have he : m = 1 := by omega
      exact Or.inl (by simpa only [he,pow_one] using hi)
  | special_unitary m hm hi =>
    by_cases hm2 : 2 ≤ m
    · obtain ⟨F,_,_,T,hF,hconj,⟨f⟩⟩ := hi
      exact (hsquare (reduced_ending_special_unitary_constituent_bound h hc hab hd hb hcomm
        T hm2 hF hconj f)).elim
    · have he : m = 1 := by omega
      exact Or.inr (by simpa only [he,pow_one] using hi)
  | dihedral hi =>
    exact (hsquare (reduced_ending_dihedral_constituent_bound h hc hab hd hb hcomm hi.some)).elim

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
