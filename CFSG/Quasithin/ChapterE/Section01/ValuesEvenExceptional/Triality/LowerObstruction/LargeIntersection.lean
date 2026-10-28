module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.LowerObstruction.ModelTransport
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.LowerObstruction.HeadCounterexample

/-!
# Transport of the two proposed triality normalizer alternatives

The automorphism group used here is the actual conjugation image of G = LT:
the join of the inner automorphisms and the image of T. Stabilizer containment
there transports to either the actor normalizer or the central full parabolic
overgroup in G. No splitting or faithful outer action is assumed.

The model stabilizer alternative remains an explicit premise.
`HeadCounterexample.head_normalizer_criterion_counterexample` disproves the
proposed universal head-intersection criterion at every positive exponent.
These transport results therefore do not prove E.1.14(2).
The source setting is Aschbacher--Smith E.1.14(2), printed p.214.
-/

public section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction
open Subgroup
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics

variable {G : Type*} [Group G] {f : ℕ} {hf : 0 < f}

private theorem normalizer_le_of_model_action (L : Subgroup G) [L.Normal]
    (e : L ≃* BinaryCarrier f hf) (Q B : Subgroup (BinaryCarrier f hf))
    (h : ∀ β ∈ (modelAction L e).range,
      Q.map β.toMonoidHom = Q → B.map β.toMonoidHom = B) :
    normalizer (Q.map (modelEmbedding L e) : Set G) ≤
      normalizer (B.map (modelEmbedding L e) : Set G) := by
  intro g hg
  apply (modelAction_stabilizes_iff L e B g).mp
  exact h (modelAction L e g) ⟨g, rfl⟩
    ((modelAction_stabilizes_iff L e Q g).mpr hg)

/-- Both alternatives transport from the actual inner-by-two action image.
The model geometry is an explicit premise, not an asserted source theorem. -/
theorem normalizer_alternative_of_model_action [Finite G]
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf))
    (hLT : L ⊔ (T : Subgroup G) = ⊤)
    (Q A : Subgroup (BinaryCarrier f hf))
    (h : (∀ β ∈ (MulAut.conj : BinaryCarrier f hf →* MulAut (BinaryCarrier f hf)).range ⊔
          (T : Subgroup G).map (modelAction L e),
        Q.map β.toMonoidHom = Q → A.map β.toMonoidHom = A) ∨
      (∀ β ∈ (MulAut.conj : BinaryCarrier f hf →* MulAut (BinaryCarrier f hf)).range ⊔
          (T : Subgroup G).map (modelAction L e),
        Q.map β.toMonoidHom = Q →
          (parabolic (binaryParameters f hf) .central).map β.toMonoidHom =
            parabolic (binaryParameters f hf) .central)) :
    normalizer (Q.map (modelEmbedding L e) : Set G) ≤
        normalizer (A.map (modelEmbedding L e) : Set G) ∨
      normalizer (Q.map (modelEmbedding L e) : Set G) ≤
        parabolicOvergroup L T e .central := by
  rw [← modelAction_range_of_join L (T : Subgroup G) e hLT] at h
  rcases h with h | h
  · exact Or.inl (normalizer_le_of_model_action L e Q A h)
  · right
    rw [← normalizer_ambientParabolic L T e he hLT .central]
    exact normalizer_le_of_model_action L e Q (parabolic (binaryParameters f hf) .central) h

/-- Pointwise fixers in the actual image of T normalize the model Q whenever
the literal ambient tau does. This supplies the action premise without
identifying tau with a centralizer or discarding the ambient two-core. -/
theorem model_fixer_normalizes_of_tau (L T : Subgroup G) [L.Normal]
    (e : L ≃* BinaryCarrier f hf) (Q A : Subgroup (BinaryCarrier f hf))
    (hτ : tau T (A.map (modelEmbedding L e)) ≤
      normalizer (Q.map (modelEmbedding L e) : Set G))
    (β : MulAut (BinaryCarrier f hf)) (hβ : β ∈ T.map (modelAction L e))
    (hfix : ∀ x ∈ A, β x = x) : Q.map β.toMonoidHom = Q := by
  obtain ⟨t, ht, rfl⟩ := modelAction_fixer_lifts_to_tau L T e A β hβ hfix
  exact (modelAction_stabilizes_iff L e Q t).mpr (hτ ht)

/-- The literal ambient criterion already fails in the trivial outer extension
L = G, with the actual top-subgroup model equivalence and positive Sylow.
Thus the missing geometry cannot be supplied uniformly for this head family. -/
theorem not_head_geometry_for_trivial_extension (f : ℕ) (hf : 0 < f) :
    let T := unipotentSylow (binaryParameters f hf) (binaryParameters_prime f hf)
    let e : (⊤ : Subgroup (BinaryCarrier f hf)) ≃* BinaryCarrier f hf := Subgroup.topEquiv
    ¬ (∀ A ∈ ambientHeadFamily ⊤ e, A ≤ (T : Subgroup (BinaryCarrier f hf)) →
      ∀ Q : Subgroup (BinaryCarrier f hf), Q ≤ (T : Subgroup (BinaryCarrier f hf)) ⊓ ⊤ →
        IsPGroup 2 Q →
        A ≤ normalizer (Q : Set (BinaryCarrier f hf)) →
        tau (T : Subgroup (BinaryCarrier f hf)) A ≤
          normalizer (Q : Set (BinaryCarrier f hf)) →
        2 ^ (2 * f) < Nat.card (Q ⊓ A : Subgroup (BinaryCarrier f hf)) → ¬ A ≤ Q →
        normalizer (Q : Set (BinaryCarrier f hf)) ≤
            normalizer (A : Set (BinaryCarrier f hf)) ∨
          normalizer (Q : Set (BinaryCarrier f hf)) ≤
            parabolicOvergroup ⊤ T e .central) := by
  dsimp only
  intro h
  have hι : modelEmbedding (⊤ : Subgroup (BinaryCarrier f hf)) Subgroup.topEquiv =
      MonoidHom.id (BinaryCarrier f hf) := by ext x; rfl
  have hP : parabolicOvergroup (⊤ : Subgroup (BinaryCarrier f hf))
      (unipotentSylow (binaryParameters f hf) (binaryParameters_prime f hf))
      Subgroup.topEquiv .central =
        parabolic (binaryParameters f hf) .central := by
    rw [parabolicOvergroup, ambientParabolic, hι, Subgroup.map_id, coe_unipotentSylow]
    exact sup_eq_left.mpr
      ((unipotent_le_borel _).trans (borel_le_parabolic _ .central))
  obtain ⟨A, Q, hA, hAU, hQU, hQtwo, hAN, hτ, hlarge, hnot, hbad⟩ :=
    HeadCounterexample.head_normalizer_criterion_counterexample f hf
  have hAm : A ∈ ambientHeadFamily (⊤ : Subgroup (BinaryCarrier f hf))
      Subgroup.topEquiv := by
    refine ⟨A, hA, ?_⟩
    rw [hι, Subgroup.map_id]
  have hh := h A hAm hAU Q (le_inf hQU le_top) hQtwo hAN hτ hlarge hnot
  rw [hP] at hh
  exact hbad hh

end CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction
