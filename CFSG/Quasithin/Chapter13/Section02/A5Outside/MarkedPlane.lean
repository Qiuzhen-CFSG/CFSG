module
public import Theory.Representation.BinaryPermutation.FiveSylowPlane
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.FixedPlane

/-!
# Identifying the original alpha plane

The actual local action is onto S₅ in the center-free outside branch.
Transporting the unique Sylow-invariant plane of its five-point core shows
that E=Ω₁Z(J(T)) is exactly the original chosen flag plane V₂. Hence the
original Baumann subgroup is C_T(V₂). The comparison preserves the original
module embedding and both subgroup inclusions.

The last theorem applies these identities to the literal contrary core-free
join H∨O²(N_L(T∩L)). It removes the previously missing E=V₂ marking; the
earlier Baumann-normalizer, solvability and [Z,L₁]=1 premises stay explicit.
Source: Aschbacher–Smith13.2.11(3),(4) and13.2.12, printed pp.881–882.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

theorem invariant_plane_unique (hfull : Function.Surjective d.localActor)
    (W₁ W₂ : Subgroup G) (hle₁ : W₁ ≤ V) (hle₂ : W₂ ≤ V)
    (hc₁ : Nat.card W₁ = 4) (hc₂ : Nat.card W₂ = 4)
    (hn₁ : (T : Subgroup G) ≤ normalizer (W₁ : Set G))
    (hn₂ : (T : Subgroup G) ≤ normalizer (W₂ : Set G)) : W₁ = W₂ := by
  let S := T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)
  let P := S.mapSurjective hfull
  have invariant (W : Subgroup G) (hn : (T : Subgroup G) ≤ normalizer (W : Set G)) :
      ∀ p ∈ (P : Subgroup (Equiv.Perm (Fin 5))), ∀ x ∈ d.flag.preimage W,
        BinaryPermutation.FivePairFixedSpaces.actionHom p x ∈ d.flag.preimage W := by
    rintro p ⟨t, ht, rfl⟩ x hx
    change d.flag.module.map (Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5) (d.localActor t) x.toAdd)) ∈ W
    change d.flag.module.map (Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5) (d.flag.normalizerAction ⟨t,_⟩) x.toAdd)) ∈ W
    rw [← d.flag.normalizer_equivariant]
    exact (mem_normalizer_iff.mp (hn ht) _).mp hx
  have he := BinaryPermutation.FiveSylowPlane.invariant_plane_eq P
    (d.flag.preimage W₁) (d.flag.preimage W₂)
    ((d.flag.preimage_card W₁ hle₁).trans hc₁)
    ((d.flag.preimage_card W₂ hle₂).trans hc₂)
    (invariant W₁ hn₁) (invariant W₂ hn₂)
  have hh := congrArg (map d.flag.module.map) he
  rwa [d.flag.preimage_map W₁ hle₁, d.flag.preimage_map W₂ hle₂] at hh

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context

namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

theorem source_alpha_eq_flag_plane
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    ChapterB.thompsonAlpha (T : Subgroup G) = V₂ := by
  have hn : (T : Subgroup G) ≤ normalizer (ChapterB.thompsonAlpha (T : Subgroup G) : Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (omegaOneCenterAmbient (elementaryAbelianMaxJ (T : Subgroup G))).map
      (MulAut.conj t).toMonoidHom = _
    have hT : (T : Subgroup G).map (MulAut.conj t).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)
    rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj t).injective,
      ← elementaryAbelianMaxJ_map_equiv, hT]
    rfl
  exact d.invariant_plane_unique (source_centerfree_localActor_surjective d hH hB hZ hs hz)
    _ _ ((source_alpha_eq_local_fixed_plane d hH hB hZ hs hz).le.trans inf_le_left)
    d.flag.two_le_V (source_alpha_card_four d hH hB hZ hs hz) d.flag.two_card hn d.flag.two_invariant

theorem source_baumann_eq_flag_plane_centralizer
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    ChapterB.baumann (T : Subgroup G) = (T : Subgroup G) ⊓ centralizer (V₂ : Set G) := by
  change (T : Subgroup G) ⊓ centralizer (ChapterB.thompsonAlpha (T : Subgroup G) : Set G) = _
  rw [source_alpha_eq_flag_plane d hH hB hZ hs hz]

theorem source_coreFree_borel_join_marked_plane
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hL₁Z : borelResidual T L ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 = ⊥) :
    ChapterB.thompsonAlpha (T : Subgroup G) = V₂ ∧
      ChapterB.baumann (T : Subgroup G) = (T : Subgroup G) ⊓ centralizer (V₂ : Set G) := by
  have hz := source_center_eq_bot_of_borel_join_core_eq_bot d hH hL₁Z hcore
  exact ⟨source_alpha_eq_flag_plane d hH hB hZ hs hz,
    source_baumann_eq_flag_plane_centralizer d hH hB hZ hs hz⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside
