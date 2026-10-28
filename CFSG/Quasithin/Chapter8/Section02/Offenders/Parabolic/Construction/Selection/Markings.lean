module
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Selection.Sources
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# Model markings on the selected quotient

The canonical quotient equivalence transports the literal embedded center
and the action of M on the quotient Sylow. Sylow normalizer and center-order
facts in the actual dihedral, PSL₂ and Suzuki models then identify the Borel
normalizer and compute binary rank. All model inputs are universal facts
in `SelectionModelSources`; no family label is used as an isomorphism.

Source: Aschbacher–Smith, E.2.11(3), E.2.14(2), and the deduction of
Proposition 8.2.2(6), combined manuscript pp.224, 226–227 and 715.
-/

public section
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
open Subgroup ChapterE Representation.BinaryOffender
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups

/-- The same isomorphism transports the specified Sylow, its normalizer,
and its intrinsic center order. -/
private theorem transport_sylow_marking {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (N : Subgroup X) (S : Sylow 2 X) (R : Sylow 2 Y)
    (hR : (R : Subgroup Y) = (S : Subgroup X).map e.toMonoidHom) (k : ℕ)
    (h : N.map e.toMonoidHom = normalizer ((R : Subgroup Y) : Set Y) ∧
      Nat.card (center R) = 2 ^ k) :
    N = normalizer ((S : Subgroup X) : Set X) ∧ Nat.card (center S) = 2 ^ k := by
  refine ⟨?_, ?_⟩
  · apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_equiv_normalizer_eq, ← hR]
    exact h.1
  · let eR : S ≃* R := ((S : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hR.symm)
    exact (Nat.card_congr (centerCongr eR).toEquiv).trans h.2

/-- The actual nonsymplectic alternatives give the Borel normalizer and
center order of the specified quotient Sylow. In the dihedral branch,
normalization and Sylow containment force the Borel to equal that Sylow. -/
theorem RankOneAlternative.sylow_marking (models : SelectionModelSources)
    {X : Type*} [Group X] [Finite X] {N : Subgroup X} {k : ℕ}
    (h : RankOneAlternative X N k) (S : Sylow 2 X)
    (hSN : (S : Subgroup X) ≤ N) (hNS : N ≤ normalizer ((S : Subgroup X) : Set X)) :
    N = normalizer ((S : Subgroup X) : Set X) ∧ Nat.card (center S) = 2 ^ k := by
  rcases h with ⟨hk, e, he⟩ | ⟨m, hm, hk, e, he⟩ | ⟨hk, p, a, hp, ho, ha, ⟨e⟩⟩
  · let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
    have hR : (R : Subgroup _) = (S : Subgroup X).map e.toMonoidHom :=
      Sylow.coe_mapSurjective _ _
    have hRN : (R : Subgroup _) ≤ PBorel (BinaryGaloisField k) := by
      rw [hR, ← he]
      exact map_mono hSN
    have hm := models.psl2 k hk R hRN
    apply transport_sylow_marking e N S R hR k
    exact ⟨he.trans hm.1, hm.2⟩
  · let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
    have hR : (R : Subgroup _) = (S : Subgroup X).map e.toMonoidHom :=
      Sylow.coe_mapSurjective _ _
    have hRN : (R : Subgroup _) ≤ SuzukiBorelSubgroup m := by
      rw [hR, ← he]
      exact map_mono hSN
    have hb := models.suzuki m hm R hRN
    apply transport_sylow_marking e N S R hR k
    exact ⟨he.trans hb.1, hb.2.trans (congrArg (fun n : ℕ => 2 ^ n) hk.symm)⟩
  · let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
    have hR : (R : Subgroup _) = (S : Subgroup X).map e.toMonoidHom :=
      Sylow.coe_mapSurjective _ _
    obtain ⟨hnR, hc⟩ := models.dihedral p a hp ho ha R
    have heq : normalizer ((S : Subgroup X) : Set X) = (S : Subgroup X) := by
      apply map_injective (f := e.toMonoidHom) e.injective
      rw [map_equiv_normalizer_eq, ← hR]
      exact hnR
    apply transport_sylow_marking e N S R hR k
    refine ⟨?_, ?_⟩
    · have hN : N = (S : Subgroup X) := le_antisymm (heq ▸ hNS) hSN
      rw [hN, ← hR]
      exact hnR.symm
    · exact hc.trans (by rw [hk, pow_one])

/-- Change the quotient kernel while preserving the embedded center and
the normalizing action of M. -/
theorem core_markings_of_star {G : Type*} [Group G]
    (M I T V : Subgroup G) (hc : localCore M I = pCore 2 I)
    (hz : starImage M I V = embeddedCenter (starImage M I T))
    (hn : starImage M I M ≤ normalizer (starImage M I T : Set (Star M I))) :
    coreImage I V = embeddedCenter (coreImage I T) ∧
      coreImage I M ≤ normalizer (coreImage I T : Set (I ⧸ pCore 2 I)) := by
  let e := coreQuotientEquiv M I hc
  have hz' := congrArg (Subgroup.map e.toMonoidHom) hz
  have hn' := map_mono (f := e.toMonoidHom) hn
  rw [map_equiv_normalizer_eq, starImage_map_coreQuotientEquiv,
    starImage_map_coreQuotientEquiv] at hn'
  refine ⟨?_, hn'⟩
  change (starImage M I V).map e.toMonoidHom =
    ((center (starImage M I T)).map (starImage M I T).subtype).map e.toMonoidHom at hz'
  rw [map_embeddedCenter _ _ e.injective, starImage_map_coreQuotientEquiv,
    starImage_map_coreQuotientEquiv] at hz'
  exact hz'

private theorem rank_eq_of_center_order {X : Type*} [Group X]
    (U S : Subgroup X) (k : ℕ) (hU : U = embeddedCenter S)
    (hc : Nat.card (center S) = 2 ^ k) : rank U = k := by
  rw [hU]
  change Nat.log 2 (Nat.card ((center S).map S.subtype)) = k
  rw [card_map_of_injective S.subtype_injective, hc, Nat.log_pow (by decide)]

/-- The quotient images and center rank are literal: the quotient Sylow is
the surjective image of the selected Sylow of I. -/
theorem selected_model_markings {G : Type*} [Group G] [Finite G]
    (models : SelectionModelSources) (M I T V : Subgroup G) (k : ℕ)
    (S : Sylow 2 I) (hS : (S : Subgroup I) = T.subgroupOf I)
    (hTM : T ≤ M)
    (hr : RankOneAlternative (I ⧸ pCore 2 I) (coreImage I M) k)
    (hz : coreImage I V = embeddedCenter (coreImage I T))
    (hn : coreImage I M ≤ normalizer (coreImage I T : Set (I ⧸ pCore 2 I))) :
    coreImage I M = normalizer (coreImage I T : Set (I ⧸ pCore 2 I)) ∧
      rank (coreImage I V) = k := by
  let q : I →* I ⧸ pCore 2 I := QuotientGroup.mk' (pCore 2 I)
  let R : Sylow 2 (I ⧸ pCore 2 I) := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective (pCore 2 I))
  have hR : (R : Subgroup (I ⧸ pCore 2 I)) = coreImage I T := by
    change (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 I)) : Subgroup (I ⧸ pCore 2 I)) = _
    rw [Sylow.coe_mapSurjective, hS]
    rfl
  have hRM : (R : Subgroup (I ⧸ pCore 2 I)) ≤ coreImage I M := by
    rw [hR]
    exact map_mono (comap_mono hTM)
  have hnorm : coreImage I M ≤ normalizer ((R : Subgroup (I ⧸ pCore 2 I)) : Set (I ⧸ pCore 2 I)) := by
    rw [hR]
    exact hn
  obtain ⟨hN, hcard⟩ := hr.sylow_marking models R hRM hnorm
  rw [hR] at hN
  have hc : Nat.card (center (coreImage I T)) = 2 ^ k := by
    change Nat.card (center (R : Subgroup (I ⧸ pCore 2 I))) = 2 ^ k at hcard
    rwa [hR] at hcard
  exact ⟨hN, rank_eq_of_center_order _ _ k hz hc⟩

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
