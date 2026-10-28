module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalPrime
public import Theory.GroupAction.ElementaryThreeChiefSylow
public import Theory.GroupTheory.TwoPerfectCyclicQuotient
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection

/-!
# The original cubic-chief action

The selected chief image in H/O₂(H) is irreducible under the image of the
actual Sylow subgroup T. This follows from the four-line action of an
elementary nine-group. When its order is three, the two-perfect point
residual L₁ centralizes the intrinsic quotient K/O₂(K), because its
automorphism group has order two. Both conclusions retain the literal
subgroup inclusion and quotient maps used by the odd-chief endgame.

The exclusion of order nine still requires the original Thompson-section
and rank argument; it is not asserted by these reductions.

Source: Aschbacher--Smith 13.7.4(1), printed pp.937--938.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₃ M H : Subgroup G}

/-- The original point residual centralizes an actual cubic primitive quotient. -/
theorem source_primitive_cubic_centralized
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (J : Subgroup H)
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (hcard : Nat.card (J ⧸ pCore 2 J) = 3) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let K := J.map H.subtype
    ⁅K,F.L₁⁆ ≤ K.pCoreIn 2 := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let e := J.equivMapOfInjective H.subtype H.subtype_injective
  have hc : Nat.card (K ⧸ pCore 2 K) = 3 := by
    rw [← Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
    exact hcard
  change ⁅K,F.L₁⁆ ≤ K.pCoreIn 2
  rw [commutator_comm]
  exact commutator_le_pCoreIn_of_twoPerfect_of_normalizes_of_quotient_card_three K F.L₁
    (isPPerfect_embedded_pResidual 2 _) ((le_sup_left.trans h.local_le).trans hJn) hc


/-- Chief minimality makes the actual star image irreducible under the actual Sylow image. -/
theorem source_primitive_three_chief_sylow_irreducible
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (J : Subgroup H)
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (hchief : ChiefFactor.IsChief (J.map (QuotientGroup.mk' (pCore 2 H))) ⊥)
    (hE : IsElementaryAbelian 3 (J ⧸ pCore 2 J))
    (hcard : Nat.card (J ⧸ pCore 2 J) = 3 ∨ Nat.card (J ⧸ pCore 2 J) = 9) :
    let S := (T.subtype (show (T : Subgroup G) ≤ H from h.T_le_H)).mapSurjective
      (QuotientGroup.mk'_surjective (pCore 2 H))
    ∀ A : Subgroup (H ⧸ pCore 2 H), A ≤ J.map (QuotientGroup.mk' (pCore 2 H)) →
      (S : Subgroup (H ⧸ pCore 2 H)) ≤ normalizer (A : Set _) →
      A = ⊥ ∨ A = J.map (QuotientGroup.mk' (pCore 2 H)) := by
  let K := J.map H.subtype
  have hsub : K.subgroupOf H = J := comap_map_eq_self_of_injective H.subtype_injective J
  have hn : J.Normal := hsub ▸ normal_subgroupOf_of_le_normalizer hJn
  let e := hn.isSubnormal.quotientCoreImageEquiv 2
  let : IsElementaryAbelian 3 (J.map (QuotientGroup.mk' (pCore 2 H))) :=
    hE.of_injective e.symm.toMonoidHom e.symm.injective
  have hc : Nat.card (J.map (QuotientGroup.mk' (pCore 2 H))) = 3 ∨
      Nat.card (J.map (QuotientGroup.mk' (pCore 2 H))) = 9 := by
    rw [← Nat.card_congr e.toEquiv]
    exact hcard
  dsimp only
  intro A hA hTA
  exact chief_elementary_three_sylow_irreducible _ hchief hc _ A hA hTA

end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
