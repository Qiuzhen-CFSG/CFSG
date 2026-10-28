module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.AlphaSelection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.Parameters

/-!
# Initial beta recognition followed by strict alpha selection

The initial Chapter 9 consumer constructs the literal beta quotient and its
whole natural residual section in both small-neighbor and reciprocal branches.
This extension applies the normalized strict-square comparison to exactly that
constructed section and returns the corresponding literal alpha quotient model.
The strict comparison remains an explicit source premise; no quotient tag or
legacy encoding is promoted to an alpha recognition theorem.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The quotient omega-center of any original Sylow has the defining-field
order once the literal quotient is marked by `SL₂`. -/
theorem linear_marking_quotient_sylow_omega_card
    {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
    (e : (H ⧸ pCore 2 H) ≃* SL(2,F)) (R : Sylow 2 H) :
    Nat.card (omegaCenterIn
      ((R : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)))) = Nat.card F := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let T : Sylow 2 (H ⧸ pCore 2 H) :=
    R.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hT : (T : Subgroup (H ⧸ pCore 2 H)) = (R : Subgroup H).map q := by
    change (R : Subgroup H).map q = (R : Subgroup H).map q
    rfl
  rw [← hT]
  exact CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.quotient_sylow_omega_card e T

/-- The literal initial section and the normalized strict comparison together
select an actual alpha `SL₂` quotient.  The strictness premise is quantified
over the same field, quotient map and whole residual section returned by the
initial source theorem, so the consumer cannot silently switch to a supplied
or unconnected model.
-/
theorem reduced_critical_initial_alpha_model_of_normalized_strict
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓
      Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (h8 : ∀ z : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj z a' →
      IsCriticalPair (Reduction.reducedFamily L S₀) z beta →
      ⁅Z (Reduction.reducedFamily L S₀) z,
        Z (Reduction.reducedFamily L S₀) beta⁆ = ⊥ →
      ⁅V (Reduction.reducedFamily L S₀) a' 1 ⊓
        Q (Reduction.reducedFamily L S₀) beta,
        V (Reduction.reducedFamily L S₀) beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b (Reduction.reducedFamily L S₀) = 3 ∧
          Nonempty ((graphLocalGroup (Reduction.reducedFamily L S₀) z ⧸
            pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) z)) ≃*
              SL(2,F)))
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓
          Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (Mα : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (Mβ : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)))
    (Mα' : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')))
    (Mαsource : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (hstrict : ∀ {F : Type u} [Field F] [Finite F] [CharP F 2]
      {n : ℕ}, 0 < n → Nat.card F = 2^n →
      (eβ : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F)) →
      NaturalResidualSection h beta eβ n →
      ∀ (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)),
        (R : Subgroup (graphLocalGroup (Reduction.reducedFamily L S₀) a)).map
            (graphLocalGroup (Reduction.reducedFamily L S₀) a).subtype =
          (stabilizer (Reduction.reducedFamily L S₀) a ⊓
            stabilizer (Reduction.reducedFamily L S₀) beta).pCoreIn 2 →
        Nat.card F < Nat.card (omegaCenterIn
          ((R : Subgroup (graphLocalGroup (Reduction.reducedFamily L S₀) a)).map
            (QuotientGroup.mk' (pCore 2
              (graphLocalGroup (Reduction.reducedFamily L S₀) a))))) ^ 2) :
    let Γ := Reduction.reducedFamily L S₀
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧
      ∃ eβ : (graphLocalGroup Γ beta ⧸
        pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F),
        NaturalResidualSection h beta eβ n ∧
        ∃ (K : Type u) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (m : ℕ),
          0 < m ∧ Nat.card K = 2^m ∧
          Nonempty ((graphLocalGroup Γ a ⧸
            pCore 2 (graphLocalGroup Γ a)) ≃* SL(2,K)) := by
  let Γ := Reduction.reducedFamily L S₀
  obtain ⟨F, instF, finF, charF, n, hn, hF, eβ, _, _, _, hres⟩ :=
    reduced_critical_recognized_initial_section h hc hab hd hb hcomm htriv h8 hob
      Mα Mβ Mα'
  let := instF
  let := finF
  let := charF
  obtain ⟨K, instK, finK, charK, m, hm, hK, heα⟩ :=
    reduced_critical_alpha_model_of_normalized_strict h hob hc hab hd hb hcomm
      Mα Mαsource hn hF eβ hres (hstrict hn hF eβ hres)
  exact ⟨F, instF, finF, charF, n, hn, hF, eβ, hres,
    K, instK, finK, charK, m, hm, hK, heα⟩

/-- In the small-neighbor branch the two already-recognized linear markings
make the normalized strict comparison automatic.  The quotient omega-card
calculation is performed on the literal alpha Sylow and the literal quotient
map, then fed back into the strict alpha selector. -/
theorem reduced_critical_small_neighbor_alpha_model
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓
      Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (hs : V (Reduction.reducedFamily L S₀) a' 1 ≤
      Q (Reduction.reducedFamily L S₀) beta)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓
          Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (Mα : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (Mα' : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')))
    (Mαsource : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a))) :
    let Γ := Reduction.reducedFamily L S₀
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧
      ∃ eβ : (graphLocalGroup Γ beta ⧸
        pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F),
        NaturalResidualSection h beta eβ n ∧
        ∃ (K : Type u) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (m : ℕ),
          0 < m ∧ Nat.card K = 2^m ∧
          Nonempty ((graphLocalGroup Γ a ⧸
            pCore 2 (graphLocalGroup Γ a)) ≃* SL(2,K)) := by
  let Γ := Reduction.reducedFamily L S₀
  obtain ⟨F, instF, finF, charF, K, instK, finK, charK, n, m, hn, hF, hm,
      hK, eα, eβ, _, _, hres⟩ :=
    reduced_small_neighbor_recognized_sections h hc hab hd hb hcomm htriv hs hob Mα Mα'
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  obtain ⟨hFK, _, _, _, _, _, _⟩ :=
    reduced_small_neighbor_linear_recognition h hc hab hd hb hcomm htriv hs hob
      hn hF hm hK eα eβ
  let H := graphLocalGroup Γ a
  let : ∀ i, Finite (Γ i) := finite_endpoints (Reduction.reduced_triple h)
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _))
    (inclusion_injective _)
  have hstrict : ∀ (R : Sylow 2 H),
      (R : Subgroup H).map H.subtype =
        (stabilizer Γ a ⊓ stabilizer Γ beta).pCoreIn 2 →
      Nat.card K < Nat.card (omegaCenterIn
        ((R : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)))) ^ 2 := by
    intro R hR
    have hω : Nat.card (omegaCenterIn
        ((R : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)))) = Nat.card F :=
      linear_marking_quotient_sylow_omega_card eα R
    have hpos : 1 < Nat.card F := by
      rw [hF]
      exact Nat.one_lt_pow (by omega) (by decide)
    rw [hω]
    rw [← hFK]
    nlinarith
  obtain ⟨K', instK', finK', charK', m', hm', hK', heα'⟩ :=
    reduced_critical_alpha_model_of_normalized_strict h
      (fun v w hvw => hob v w hvw) hc hab hd hb hcomm Mα Mαsource hm hK eβ hres hstrict
  exact ⟨K, instK, finK, charK, m, hm, hK, eβ, hres,
    K', instK', finK', charK', m', hm', hK', heα'⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
