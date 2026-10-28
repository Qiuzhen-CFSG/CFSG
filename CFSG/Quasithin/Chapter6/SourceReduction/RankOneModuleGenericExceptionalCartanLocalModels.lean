module

public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.ContainingQuotients
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.SylowActors
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalQuotient

/-!
# Containing-model exclusions and the full cyclic-actor setup

The original universal Input constructs the seed and its containing component.
Its literal two-core image is proper, excluding all Bender, even SU₃ and
small alternating containers. No normalization of the seed by T is imposed.

The normal containing orbit supports the original quotient action. The
escaping odd cyclic Cartan image permutes with a full Sylow of the induced
action group and generates a solvable group with it. Both Hall conditions,
the right-Hall normalization and the escaping residual image are retained.

The other model rows, escaping cubic, A₇ contradiction and module recognition
remain to be proved; this module does not assert LocalCartanSieve.
Source: Aschbacher--Smith 5.1.12--13, printed pp.635--638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The original seed embeds properly after removing the actual local two-core.
All Bender, even SU₃, and small alternating containing rows are excluded. -/
theorem localCartan_escape_containing_quotient_restrictions
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (_c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ ClassificationModels.IsBenderModel (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m)) ∧
        ¬ (IsAlternating (C ⧸ pCore 2 C) 5 ∨ IsAlternating (C ⧸ pCore 2 C) 6 ∨
          IsAlternatingCover (C ⧸ pCore 2 C) 6) := by
  obtain ⟨K,hKH,hK,hq,hg,hl,ho,C,hC,_⟩ := LocalSieve.exists_escape_seed_embedding
    h.qtke h.sylow_normalizes hH hgen hY hescape
  exact ⟨K,hKH,hK,hq,hg,hl,ho,C,hC.1,hC.2.1,hC.2.2.1,hC.2.2.2,
    LocalSieve.seed_image_lt_container h.qtke hKH hH.1.1.2 hl ho hY hescape C hC.1 hC.2.1,
    LocalSieve.not_bender_container h.qtke hKH hH.1.1.2 hl ho hY hescape C hC.1 hC.2.1,
    LocalSieve.not_binary_su3_container h.qtke hKH hH.1.1.2 hl ho hY hescape C hC.1 hC.2.1,
    LocalSieve.not_small_alternating_container h.qtke hKH hH.1.1.2 hl ho hY hescape C hC.1 hC.2.1⟩

/-- The actual odd cyclic actor permutes with the original full Sylow image
in the induced automorphism group, while still escaping the residual image. -/
theorem localCartan_exists_escaping_sylow_action
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ C : Subgroup Y, C.IsCComponent ∧
      residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
      ∃ hn : ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal,
        let J := (componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y
        letI : J.Normal := hn
        let f := normalQuotientAction J (pCore 2 J)
        let Dbar := (A.subgroupOf Y).map f
        let Bbar := (B.subgroupOf Y).map f
        let Tbar := ((T : Subgroup G).subgroupOf Y).map f
        Chapter1.IsSylowIn 2 Tbar f.range ∧
          (Dbar : Set (MulAut (J ⧸ pCore 2 J))) * (Tbar : Set _) =
            (Tbar : Set _) * (Dbar : Set _) ∧
          Group.IsSolvable (Dbar ⊔ Tbar : Subgroup _) ∧
          IsCyclic Dbar ∧ Odd (Nat.card Dbar) ∧
          Bbar ≤ normalizer (Dbar : Set (MulAut (J ⧸ pCore 2 J))) ∧
          ¬ Dbar ≤ normalizer (((residual H).subgroupOf Y).map f : Set _) ∧
          Dbar ≠ ⊥ ∧ ¬ Dbar ≤ Bbar := by
  obtain ⟨C,hC,hlt,hn,haction⟩ :=
    localCartan_exists_escaping_component_action h hH hgen c hY hescape
  refine ⟨C,hC,hlt,hn,?_⟩
  let J := (componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y
  let : J.Normal := hn
  let f := normalQuotientAction J (pCore 2 J)
  have hTY := hH.1.1.2.trans hY.2
  refine ⟨?_,c.image_intersection_permutes_sylow h.sylow_normalizes hTY f,
    h.cartan_sylow_action_isSolvable c hTY f,haction⟩
  let S := (T.subtype hTY).mapSurjective f.rangeRestrict_surjective
  refine ⟨S,?_⟩
  change (((T : Subgroup G).subgroupOf Y).map f.rangeRestrict).map f.range.subtype = _
  rw [Subgroup.map_map]
  rfl

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
