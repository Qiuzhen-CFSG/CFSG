module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.QuotientGeometry

/-!
# Transport for the concrete linear Sylow calculation

The five intrinsic Borel conclusions transport along an actual group
isomorphism. Sylow conjugacy then reduces arbitrary Sylow subgroups to the
standard upper unipotents. The two-core clause is supplied by the general
Sylow-normalizer theorem, so no quotient or residual convention is changed.

This is an assembly helper for Aschbacher–Smith F.1.3(1), printed p.260.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.Source.Linear

variable {G H : Type*} [Group G] [Group H]

set_option backward.isDefEq.respectTransparency false in
theorem transport (e : G ≃* H) (S : Sylow 2 G) (T : Sylow 2 H)
    (hST : (S : Subgroup G).map (e : G →* H) = (T : Subgroup H))
    (h : RankOneSylowFacts S) : RankOneSylowFacts T := by
  have hn : (Subgroup.normalizer (S : Set G)).map (e : G →* H) =
      Subgroup.normalizer (T : Set H) := by
    change (Subgroup.normalizer ((S : Subgroup G) : Set G)).map (e : G →* H) =
      Subgroup.normalizer ((T : Subgroup H) : Set H)
    rw [← MulEquiv.toMonoidHom_eq_coe, Subgroup.map_equiv_normalizer_eq]
    simp only [MulEquiv.toMonoidHom_eq_coe, hST]
  refine ⟨?_, ?_, twoCore_sylow_normalizer T, ?_, ?_⟩
  · apply lt_top_iff_ne_top.mpr
    intro ht
    apply h.proper.ne
    apply Subgroup.map_injective (f := (e : G →* H)) e.injective
    rw [hn, ht, Subgroup.map_equiv_top]
  · intro M hTM hM
    have hpre : M.comap (e : G →* H) < ⊤ := by
      apply lt_top_iff_ne_top.mpr
      intro ht
      apply hM.ne
      have := congrArg (Subgroup.map (e : G →* H)) ht
      simpa [Subgroup.map_comap_eq_self_of_surjective (f := (e : G →* H)) e.surjective] using this
    have hs : (S : Subgroup G) ≤ M.comap (e : G →* H) :=
      Subgroup.map_le_iff_le_comap.mp (hST ▸ hTM)
    have := Subgroup.map_mono (f := (e : G →* H)) (h.unique_maximal _ hs hpre)
    simpa [hn, Subgroup.map_comap_eq_self_of_surjective (f := (e : G →* H)) e.surjective] using this
  · let := h.solvable
    rw [← hn]
    exact Group.isSolvable_of_surjective (f := (e.subgroupMap (Subgroup.normalizer (S : Set G))).toMonoidHom)
      (e.subgroupMap (Subgroup.normalizer (S : Set G))).surjective
  · obtain ⟨D, hDn, hodd, hcomm, hdisj, hsup⟩ := h.abelian_odd_complement
    let := hcomm
    refine ⟨D.map (e : G →* H), ?_, ?_, inferInstance, ?_, ?_⟩
    · rw [← hn]
      exact Subgroup.map_mono hDn
    · rwa [← Nat.card_congr (e.subgroupMap D).toEquiv]
    · rw [disjoint_iff, ← hST, ← Subgroup.map_inf _ _ _ e.injective,
        disjoint_iff.mp hdisj, Subgroup.map_bot]
    · rw [← hST, ← Subgroup.map_sup, hsup, hn]

set_option backward.isDefEq.respectTransparency false in
theorem all_sylows [Finite G] (S : Sylow 2 G) (h : RankOneSylowFacts S)
    (T : Sylow 2 G) : RankOneSylowFacts T := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  apply transport (MulAut.conj g) S T _ h
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  rfl

end CFSG.Quasithin.ChapterF.Source.Linear
