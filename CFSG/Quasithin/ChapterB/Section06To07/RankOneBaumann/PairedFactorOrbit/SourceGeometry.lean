module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.Residuals
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.LayerGeometry
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedLayerSource
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
/-!
# The same original marked pair at the Baumann source boundary

The source marked product supplies its actual quotient map and exact
residual-fixed kernel. Its chosen Sylow exchange gives the paired action,
Thompson and Baumann images, fixed-space lift, and global alpha identity.
These are derived inputs for the per-factor argument; the source consumer
retains the same d and does not import Chapter E.
Source: Aschbacher–Smith B.6.9–10, printed pp.115–117.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
open QuasisimpleSource SourceInduction CFSG.Quasithin.ChapterB
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
theorem source_global_baumann_and_alpha
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (pResidual 2 G ⊔ baumann (T : Subgroup G)) ∧
      thompsonAlpha (T : Subgroup G) =
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ⊔
          (U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [← pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T:Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hff,_,_,_⟩ := lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  apply RankOneBaumann.paired_layer_baumann_sylow_and_alpha T hP U hU hJ q hq hker
    Y c.action.groupEquiv c.quotientMap c.quotientMap_surjective
    (fun g v => c.quotientMap_action g v) ?_ le_rfl ?_
  · rw [map_pResidual_of_surjective 2 q hq]
    exact source_offender_pair_linear_kernel α (T.mapSurjective hq) hp hff hcore F c
  · obtain ⟨t,h₁,h₂⟩ := hexchange
    have ht : (t:H) ∈ (T:Subgroup G).map q := t.property
    obtain ⟨g,hg,he⟩ := ht
    have hm₁ := congrArg (map Y.subtype) h₁
    have hm₂ := congrArg (map Y.subtype) h₂
    have hc : Y.subtype.comp (MulAut.conjNormal (t:H)).toMonoidHom =
        (MulAut.conj (t:H)).toMonoidHom.comp Y.subtype := by ext; rfl
    rw [map_map,hc,← map_map] at hm₁ hm₂
    refine ⟨g,hg,?_,?_⟩
    · rw [← map_map,c.first_eq,← map_map,c.second_eq,he]
      exact hm₁
    · rw [← map_map,c.second_eq,← map_map,c.first_eq,he]
      exact hm₂

theorem source_images_and_fixedSpace
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
    let V := Fin 2 → F.Carrier
    ∃ ρ : Representation (ZMod 2) H (V × V), Function.Injective ρ ∧
      (∀ (g : Y) v, ρ (g : H) v = SL2NaturalOffenders.naturalPair (F := F.Carrier)
        (c.action.groupEquiv g) v) ∧
      (∀ g v, c.quotientMap (NormalElementaryQuotient.representation U q hq hker g v) = ρ g (c.quotientMap v)) ∧
      ((elementaryAbelianMaxJ (T : Subgroup G)).map q = (T : Subgroup G).map q ⊓ Y ∧
        (baumann (T : Subgroup G)).map q = (T : Subgroup G).map q ⊓ Y) ∧
      fixedSpace (NormalElementaryQuotient.representation U q hq hker)
        ((elementaryAbelianMaxJ (T : Subgroup G)).map q) =
        (fixedSpace ρ ((elementaryAbelianMaxJ (T : Subgroup G)).map q)).comap c.quotientMap := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [← pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T:Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hff,_,_,_⟩ := lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  apply RankOneBaumann.paired_layer_action_and_fixedSpace T hP U hU hJ q hq hker
    Y c.action.groupEquiv c.quotientMap c.quotientMap_surjective
    (fun g v => c.quotientMap_action g v) ?_ le_rfl ?_
  · rw [map_pResidual_of_surjective 2 q hq]
    exact source_offender_pair_linear_kernel α (T.mapSurjective hq) hp hff hcore F c
  · obtain ⟨t,h₁,h₂⟩ := hexchange
    have ht : (t:H) ∈ (T:Subgroup G).map q := t.property
    obtain ⟨g,hg,he⟩ := ht
    have hm₁ := congrArg (map Y.subtype) h₁
    have hm₂ := congrArg (map Y.subtype) h₂
    have hc : Y.subtype.comp (MulAut.conjNormal (t:H)).toMonoidHom =
        (MulAut.conj (t:H)).toMonoidHom.comp Y.subtype := by ext; rfl
    rw [map_map,hc,← map_map] at hm₁ hm₂
    refine ⟨g,hg,?_,?_⟩
    · rw [← map_map,c.first_eq,← map_map,c.second_eq,he]
      exact hm₁
    · rw [← map_map,c.second_eq,← map_map,c.first_eq,he]
      exact hm₂

theorem source_residual_normalizers_and_sylows
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
    let B := baumann (T : Subgroup G)
    let K₁ := factorResidual q Y d.first
    let K₂ := factorResidual q Y d.second
    Chapter1.IsSylowIn 2 B (pResidual 2 G ⊔ B) ∧
      (B ≤ normalizer (K₁ : Set G) ∧ Chapter1.IsSylowIn 2 B (K₁ ⊔ B)) ∧
      (B ≤ normalizer (K₂ : Set G) ∧ Chapter1.IsSylowIn 2 B (K₂ ⊔ B)) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let B := baumann (T : Subgroup G)
  let := d.product.first_normal
  let := d.product.second_normal
  have hs := (source_global_baumann_and_alpha T hP U hU hJ q hq hker d F c hexchange).1
  obtain ⟨ρ,hρ,hnat,he,⟨hJq,hBq⟩,hfix⟩ :=
    source_images_and_fixedSpace T hP U hU hJ q hq hker d F c hexchange
  have hBY : B ≤ Y.comap q := map_le_iff_le_comap.mp (hBq.le.trans inf_le_right)
  refine ⟨hs,⟨hBY.trans (factorResidual_normalized q Y d.first),?_⟩,
    ⟨hBY.trans (factorResidual_normalized q Y d.second),?_⟩⟩
  · exact Chapter1.IsSylowIn.restrict hs le_sup_right
      (sup_le_sup_right (factorResidual_le_residual q Y d.first) B)
  · exact Chapter1.IsSylowIn.restrict hs le_sup_right
      (sup_le_sup_right (factorResidual_le_residual q Y d.second) B)
end CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
