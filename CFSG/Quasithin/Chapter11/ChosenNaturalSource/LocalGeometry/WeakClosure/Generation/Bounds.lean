module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Hall
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Transport

/-!
# The generation deduction from the literal automizer

Restrict the constructed Cartan witness to H intersect J, where J contains
the prescribed Sylow and the full Hall actor. Embed it into that same J,
then map to its actual action on U. Faithfulness on V implies faithfulness
on any U containing V. Thus n(H) ≤ f ≤ n'(Aut_J(U)), with the source model
bounds on the last term kept separate.

Source: Aschbacher--Smith, E.3.38 and 11.2.1, printed pp.240,767.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterB
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- E.3.38's faithful-Cartan deduction for the actual H-star witness. -/
theorem parameter_le_automizer {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hP : IsMinimalParabolicOver (T.subtype hTH) ⊤) {f : ℕ}
    (d : IntrinsicHallCartanData (T.subtype hTH) hP f)
    (hf : generationParameter H ≤ f)
    (hfaith : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) = ⊥)
    (J U : Subgroup G) (hTJ : (T : Subgroup G) ≤ J)
    (hBJ : d.witness.abelianGroup.map H.subtype ≤ J)
    (hJU : J ≤ normalizer (U : Set G)) (hVU : V ≤ U) :
    generationParameter H ≤ nPrime (inducedAutomizer U J) := by
  let K := J.subgroupOf H
  have hBK : d.witness.abelianGroup ≤ K := map_le_iff_le_comap.mp hBJ
  have hSK : (d.witness.sylow : Subgroup H) ≤ K := by
    rw [d.sylow_eq]
    exact comap_mono hTJ
  let wK := MarkedModels.restrictWitness d.witness K hBK hSK
  let emb : K →* J := (H.subtype.comp K.subtype).codRestrict J (fun x => x.property)
  have hi : Function.Injective emb := by
    intro x y he
    have he' : ((x : H) : G) = ((y : H) : G) :=
      congrArg (fun z : J => (z : G)) he
    exact Subtype.ext (Subtype.ext he')
  let R := T.subtype hTJ
  have hR : (wK.sylow : Subgroup K).map emb = R := by
    apply map_injective J.subtype_injective
    rw [map_map]
    change (((d.witness.sylow : Subgroup H).subgroupOf K).map
      (H.subtype.comp K.subtype)) = ((T : Subgroup G).subgroupOf J).map J.subtype
    rw [← map_map, map_subgroupOf_eq_of_le hSK, d.sylow_eq]
    change ((T : Subgroup G).subgroupOf H).map H.subtype =
      ((T : Subgroup G).subgroupOf J).map J.subtype
    rw [map_subgroupOf_eq_of_le hTH, map_subgroupOf_eq_of_le hTJ]
  let w := MarkedModels.embedWitness wK emb hi R hR
  have hw : w.cyclicGroup.map J.subtype = d.witness.cyclicGroup.map H.subtype := by
    change ((d.witness.cyclicGroup.subgroupOf K).map emb).map J.subtype = _
    rw [map_map]
    change (d.witness.cyclicGroup.subgroupOf K).map (H.subtype.comp K.subtype) = _
    rw [← map_map, map_subgroupOf_eq_of_le (d.witness.cyclic_le.trans hBK)]
  apply hf.trans (faithful_cartan_bound hJU w ?_)
  rw [hw]
  apply le_bot_iff.mp
  exact (inf_le_inf (map_mono d.witness.cyclic_le) (centralizer_le hVU)).trans hfaith.le

/-- If the faithful Hall actor preserves the seed, the single-module
model bound gives the first alternative of 11.2.1. -/
theorem parameter_le_degree_of_normalizes
    (hbounds : AutomizerBounds D S)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) {f : ℕ}
    (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hf : generationParameter H ≤ f)
    (hfaith : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) = ⊥)
    (hn : d.witness.abelianGroup.map H.subtype ≤ normalizer (V : Set G)) :
    generationParameter H ≤ S.field.degree := by
  apply (parameter_le_automizer hH.1.1.2 hP d hf hfaith
    (normalizer (L : Set G) ⊓ normalizer (V : Set G)) V
    (le_inf D.sylow_normalizes_component S.sylow_normalizes)
    (le_inf (map_le_iff_le_comap.mpr (d.hall_le.trans hm.le)) hn) inf_le_right le_rfl).trans
  exact hbounds.1

/-- In the doubled branch the same faithful Hall actor acts on the full
normalizer orbit. Its model bound gives n(H) ≤ 2n. -/
theorem parameter_le_twice_degree
    (hbounds : AutomizerBounds D S) (hdouble : DoubledNatural D S)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) {f : ℕ}
    (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hf : generationParameter H ≤ f)
    (hfaith : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) = ⊥) :
    generationParameter H ≤ 2 * S.field.degree := by
  apply (parameter_le_automizer hH.1.1.2 hP d hf hfaith
    (normalizer (L : Set G)) (Source.conjugateSpan (normalizer (L : Set G)) V)
    D.sylow_normalizes_component (map_le_iff_le_comap.mpr (d.hall_le.trans hm.le))
    (le_normalizer_componentOrbit V _) (le_componentOrbit V _)).trans
  exact hbounds.2 hdouble

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation
