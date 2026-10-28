module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFiveNormalAction
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.Representation.BinaryAlternatingFiveBorel.PointNormalizedTwoSubgroup
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups
public import CFSG.Quasithin.ChapterB.Section03.Offenders.OddConjugation
public import Theory.GroupTheory.PGroup.NormalSupplementCore

/-!
# The Thompson subgroup on an actual A₅ constituent

A normal A₅ block has its genuine five-point action on the entire binary
core. If its Sylow Borel normalizes the two-group Q containing the module,
Q acts evenly. B.3.2(4) then excludes every nontrivial maximal elementary
action image, putting J(Q) in the two-core of XQ.

The statement is relative to the displayed normal overgroup. It applies
separately to either constituent of an exchanged orbit once Q is shown to
preserve that constituent. No embedding of a paired actor into S₅ is used.

Source: Aschbacher--Smith B.3.2(4) and preliminary15.2.23, pp.83,1115.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

theorem IsAlternatingBlock.normal_thompson_le_core (X Q : Subgroup G) [X.Normal]
    (hb : IsAlternatingBlock X 5) (hQ : IsPGroup 2 Q)
    (hWQ : (blockU X).map X.subtype ≤ Q)
    (P : Sylow 2 X)
    (hBQ : (normalizer (P : Set X)).map X.subtype ≤ normalizer (Q : Set G)) :
    elementaryAbelianMaxJ Q ≤ (X ⊔ Q).pCoreIn 2 := by
  obtain ⟨q,E,f,hf,hE,_himage,hker,hC⟩ := hb.five_normal_action X
  let a := q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have ha : Function.Surjective a := q.surjective.comp (QuotientGroup.mk'_surjective _)
  let R := P.mapSurjective ha
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer R
  let B := (normalizer (P : Set X)).map X.subtype
  have hBimage : B.map f = alternatingGroup (Fin 5) ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 5)) i := by
    have he : f.comp X.subtype = (alternatingGroup (Fin 5)).subtype.comp a :=
      MonoidHom.ext hf
    rw [map_map,he,←map_map,P.normalizer_map_surjective a ha]
    change (normalizer (R : Set (alternatingGroup (Fin 5)))).map _ = _
    rw [hi]
    ext x
    exact ⟨fun ⟨y,hy,he⟩ => he ▸ ⟨y.property,hy⟩,fun ⟨hy,hf⟩ => ⟨⟨x,hy⟩,hf,rfl⟩⟩
  have heven : Q.map f ≤ alternatingGroup (Fin 5) := by
    apply BinaryPermutation.AlternatingFiveBorel.even_point_stabilizer_normalizes_twoSubgroup
      _ (hQ.map f) i
    rw [←hBimage]
    exact (map_mono hBQ).trans (le_normalizer_map f)
  let W := (blockU X).map X.subtype
  let : W.Normal := inferInstance
  let : IsElementaryAbelian 2 (blockU X) := hb.2.1.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map X.subtype
  let j : blockU X ≃* W := (blockU X).equivMapOfInjective X.subtype X.subtype_injective
  let F : W ≃* Multiplicative (BinaryPermutation.core (Fin 5)) := j.symm.trans E
  have hF (g : G) (w : W) : (F (MulAut.conjNormal g w)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 5) (f g) (F w).toAdd := by
    have hh : j.symm (MulAut.conjNormal g w) =
        MulAut.characteristic (blockU X) (MulAut.conjNormal g) (j.symm w) := by
      apply j.injective
      rw [j.apply_symm_apply]
      apply Subtype.ext
      change g * (w : G) * g⁻¹ = g * (((j.symm w : blockU X) : X) : G) * g⁻¹
      congr 2
      exact (congrArg Subtype.val (j.apply_symm_apply w)).symm
    change (E (j.symm _)).toAdd = _
    rw [hh]
    exact hE g (j.symm w)
  have hJ := ChapterB.Offenders.thompson_le_kernel_of_even_core_action (Or.inl rfl) W Q hWQ f
    hC F hF heven
  have hk : IsPGroup 2 (f.comp X.subtype).ker := by
    rw [hker]
    exact pCore_isPGroup
  exact (le_inf ((sSup_le fun _ hA => hA.1).trans le_sup_right) hJ).trans
    (inf_ker_le_core_of_two_supplement f X Q le_normalizer_of_normal hQ hk)

end CFSG.Quasithin.ChapterC
