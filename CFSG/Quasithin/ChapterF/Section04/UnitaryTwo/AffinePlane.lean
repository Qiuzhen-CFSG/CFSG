module
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.BinaryOrders
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.AlternatingFive.Intertwining
public import Theory.Representation.BinaryAlternatingFiveExtension.Automorphism
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ModelClasses
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# The marked affine model of the binary unitary plane

The deleted permutation module on five letters is equivariantly isomorphic
to the binary Hermitian plane radical. The A₅ extension theorem identifies
the full affine group with the literal U₄(2) plane parabolic. Relabelling
the five singular vectors sends the marked weight-four vector to the
long-root element, so its centralizer becomes the literal flag overlap.

This supplies the ordinary plane endpoint required by the normal A₅ branch
of Aschbacher–Smith 13.5.17. The model coordinates and long-root centralizer
are those of F.4.27 and F.4.43, printed pp.287 and 296.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.AffinePlane
open GreenBook.LieModels.UnitaryFour
open Representation.OrthogonalFourMinus
open BinaryPermutation
local notation "hn" => Nat.le_refl 1
local notation "L" => L2 1 hn
local notation "P" => planeParabolic 1 hn
local notation "A" => AlternatingFiveExtension.AlternatingModel
local notation "V" => Multiplicative (core (Fin 5))

private theorem core_equivariant (g : AlternatingFive.Group) (v : core (Fin 5)) :
    AlternatingFive.coreEquiv (coreRepresentation (Fin 5) (AlternatingFive.groupEquiv g).val v) =
      FiniteModel.action 1 g (AlternatingFive.coreEquiv v) := by
  rw [AlternatingFive.groupEquiv_coe]
  change AlternatingFive.combination (representation (Fin 5) (AlternatingFive.permutation g) v.val) =
    FiniteModel.action 1 g (AlternatingFive.combination v.val)
  exact AlternatingFive.combination_equivariant g v.val

private theorem local_marked_equiv : ∃ E : L ≃* A,
    ∀ v : V, E (L2RadicalEquiv 1 hn
      (Multiplicative.ofAdd (AlternatingFive.coreEquiv v.toAdd))) = SemidirectProduct.inl v := by
  let q := AlternatingFive.groupEquiv.toMonoidHom.comp
    ((planeSL2Equiv 1).toMonoidHom.comp (L2Restriction 1 hn))
  have hq : Function.Surjective q := AlternatingFive.groupEquiv.surjective.comp
    ((planeSL2Equiv 1).surjective.comp (L2Restriction_surjective 1 hn))
  have hk : q.ker = L2Radical 1 hn := by
    ext x
    change AlternatingFive.groupEquiv (planeSL2Equiv 1 (L2Restriction 1 hn x)) = 1 ↔
      L2Restriction 1 hn x = 1
    exact (AlternatingFive.groupEquiv.map_eq_one_iff).trans ((planeSL2Equiv 1).map_eq_one_iff)
  let e := (MulEquiv.subgroupCongr hk).trans ((L2RadicalEquiv 1 hn).symm.trans
    AlternatingFive.coreEquiv.toAddEquiv.symm.toMultiplicative)
  have he (g : L) (v : q.ker) : e (MulAut.conjNormal g v) =
      Multiplicative.ofAdd (coreRepresentation (Fin 5) (q g).val (e v).toAdd) := by
    change Multiplicative.ofAdd (AlternatingFive.coreEquiv.symm
      ((L2RadicalEquiv 1 hn).symm (MulAut.conjNormal g ⟨v.val,hk.le v.property⟩)).toAdd) = _
    rw [L2RadicalEquiv_symm_conj]
    change AlternatingFive.coreEquiv.symm
      (FiniteModel.action 1 (planeSL2Equiv 1 (L2Restriction 1 hn g))
        ((L2RadicalEquiv 1 hn).symm ⟨v.val,hk.le v.property⟩).toAdd) =
      coreRepresentation (Fin 5) (q g).val (e v).toAdd
    apply AlternatingFive.coreEquiv.injective
    rw [AlternatingFive.coreEquiv.apply_symm_apply]
    change FiniteModel.action 1 (planeSL2Equiv 1 (L2Restriction 1 hn g))
      ((L2RadicalEquiv 1 hn).symm ⟨v.val,hk.le v.property⟩).toAdd =
      AlternatingFive.coreEquiv (coreRepresentation (Fin 5)
        (AlternatingFive.groupEquiv (planeSL2Equiv 1 (L2Restriction 1 hn g))).val
        (AlternatingFive.coreEquiv.symm ((L2RadicalEquiv 1 hn).symm ⟨v.val,hk.le v.property⟩).toAdd))
    rw [core_equivariant,AlternatingFive.coreEquiv.apply_symm_apply]
  obtain ⟨E,_,hEe⟩ := AlternatingFiveExtension.exists_marked_equiv q hq e he
  refine ⟨E,fun v => ?_⟩
  have hi : (e.symm v : L) = L2RadicalEquiv 1 hn
      (Multiplicative.ofAdd (AlternatingFive.coreEquiv v.toAdd)) := rfl
  rw [←hi,hEe,e.apply_symm_apply]

private def relabel : Equiv.Perm (Fin 5) :=
  Equiv.swap 4 (AlternatingFive.label (AlternatingFive.parametrize none))

private theorem relabel_z : AlternatingFive.coreEquiv
    (coreRepresentation (Fin 5) relabel FiveCentralizerGeometry.z) =
      AlternatingFive.pointVector none := by
  have hz : coreRepresentation (Fin 5) relabel FiveCentralizerGeometry.z =
      (⟨(allOne (Fin 5)) - Pi.single (relabel 4) 1, by
        change augmentation (Fin 5) _ = 0
        norm_num [augmentation,allOne]
        decide⟩ : core (Fin 5)) := by
    apply Subtype.ext
    funext i
    change FiveCentralizerGeometry.z.val (relabel⁻¹ i) = _
    have hv : FiveCentralizerGeometry.z.val = allOne (Fin 5) - Pi.single (4 : Fin 5) 1 := by decide +kernel
    rw [hv]
    simp only [Pi.sub_apply,allOne]
    congr 1
    simp only [Pi.single_apply]
    congr 1
    exact propext (Equiv.symm_apply_eq relabel)
  change AlternatingFive.combination ((coreRepresentation (Fin 5) relabel FiveCentralizerGeometry.z).val) = _
  rw [hz]
  change AlternatingFive.combination (allOne (Fin 5) - Pi.single (relabel 4) 1) = _
  rw [map_sub,AlternatingFive.combination_allOne]
  have hs : AlternatingFive.combination (Pi.single (relabel 4) 1) = AlternatingFive.vector (relabel 4) := by
    simp [AlternatingFive.combination,Fintype.linearCombination_apply]
  rw [hs,zero_sub]
  have hneg (X : FiniteModel.Space 1) : -X=X := by
    apply Subtype.ext
    ext i j
    exact CharTwo.neg_eq _
  rw [hneg]
  change (AlternatingFive.label.symm (relabel 4)).val = _
  rw [relabel,Equiv.swap_apply_left,AlternatingFive.label.symm_apply_apply]
  rfl

private theorem radical_infinity :
    (L2RadicalEquiv 1 hn (Multiplicative.ofAdd (AlternatingFive.pointVector none)) : L) =
      L2ProjectIso 1 hn (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot.longLocal
        (MatrixField 1) (fieldConj 1) (fieldConj_involutive 1 hn)) := by
  rw [L2RadicalEquiv_project]
  apply congrArg (L2ProjectIso 1 hn)
  have hm : (planeHermitianEquiv 1).symm (AlternatingFive.pointVector none) =
      Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot.longParameter
        (MatrixField 1) (fieldConj 1) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [planeHermitianEquiv,AlternatingFive.pointVector,FiniteModel.coordinates_symm_val,
        Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot.longParameter,Matrix.map_apply]
  change (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical.radicalEquiv
    (MatrixField 1) (fieldConj 1) (fieldConj_involutive 1 hn)
      (Multiplicative.ofAdd ((planeHermitianEquiv 1).symm (AlternatingFive.pointVector none)))).val = _
  rw [hm]
  rfl

/-- The binary affine A₅ plane is the literal unitary-four plane parabolic,
with its marked singular vector and its centralizer identified simultaneously. -/
theorem exists_marked_plane_equiv : ∃ E : A ≃* P,
    E (SemidirectProduct.inl (Multiplicative.ofAdd FiveCentralizerGeometry.z)) =
      ModelClasses.longRight ∧
    (SemidirectProduct.inl : V →* A).range.map E.toMonoidHom = pCore 2 P ∧
    (centralizer ({SemidirectProduct.inl (Multiplicative.ofAdd FiveCentralizerGeometry.z)} : Set A)).map
      E.toMonoidHom = (overlap 1 hn).subgroupOf P := by
  obtain ⟨e,he⟩ := local_marked_equiv
  let c : L ≃* P := MulEquiv.subgroupCongr BinaryCompletion.plane_eq_local.symm
  let E : A ≃* P := (AlternatingFiveExtension.standardAction relabel).trans (e.symm.trans c)
  have hi (v : V) : E (SemidirectProduct.inl v) =
      c (L2RadicalEquiv 1 hn (Multiplicative.ofAdd
        (AlternatingFive.coreEquiv (coreRepresentation (Fin 5) relabel v.toAdd)))) := by
    change c (e.symm (AlternatingFiveExtension.standardAction relabel (SemidirectProduct.inl v))) = _
    rw [AlternatingFiveExtension.standardAction_inl]
    have hh := congrArg e.symm (he (AlternatingFiveExtension.coreAction relabel v))
    rw [e.symm_apply_apply] at hh
    exact congrArg c hh.symm
  have hz : E (SemidirectProduct.inl (Multiplicative.ofAdd FiveCentralizerGeometry.z)) =
      ModelClasses.longRight := by
    rw [hi]
    exact (congrArg (fun X : FiniteModel.Space 1 =>
      c (L2RadicalEquiv 1 hn (Multiplicative.ofAdd X))) relabel_z).trans
        (congrArg c radical_infinity)
  refine ⟨E,hz,?_,?_⟩
  · have hrange : (SemidirectProduct.inl : V →* A).range.map E.toMonoidHom =
        (L2Radical 1 hn).map c.toMonoidHom := by
      ext y
      constructor
      · rintro ⟨_,⟨v,rfl⟩,rfl⟩
        change E (SemidirectProduct.inl v) ∈ (L2Radical 1 hn).map c.toMonoidHom
        rw [hi]
        exact mem_map_of_mem _ (L2RadicalEquiv 1 hn _).property
      · rintro ⟨x,hx,rfl⟩
        let X := (L2RadicalEquiv 1 hn).symm ⟨x,hx⟩
        let v : V := (AlternatingFiveExtension.coreAction relabel).symm
          (Multiplicative.ofAdd (AlternatingFive.coreEquiv.symm X.toAdd))
        refine ⟨SemidirectProduct.inl v,⟨v,rfl⟩,?_⟩
        change E (SemidirectProduct.inl v) = c x
        rw [hi]
        apply congrArg c
        change (L2RadicalEquiv 1 hn
          (Multiplicative.ofAdd (AlternatingFive.coreEquiv
            ((AlternatingFiveExtension.coreAction relabel) v).toAdd))).val = x
        rw [MulEquiv.apply_symm_apply]
        exact (congrArg (fun Y : FiniteModel.Space 1 =>
          (L2RadicalEquiv 1 hn (Multiplicative.ofAdd Y)).val)
            (AlternatingFive.coreEquiv.apply_symm_apply X.toAdd)).trans
          (congrArg Subtype.val ((L2RadicalEquiv 1 hn).apply_symm_apply ⟨x,hx⟩))
    rw [hrange,L2Radical_eq_twoCore,pCore_map_iso]
  · have hmap : (centralizer ({SemidirectProduct.inl (Multiplicative.ofAdd FiveCentralizerGeometry.z)} : Set A)).map
        E.toMonoidHom = centralizer ({ModelClasses.longRight} : Set P) := by
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩
        rw [←hz,mem_centralizer_singleton_iff]
        exact (map_mul E _ _).symm.trans
          ((congrArg E (mem_centralizer_singleton_iff.mp hx)).trans (map_mul E _ _))
      · intro hy
        refine ⟨E.symm y,?_,E.apply_symm_apply y⟩
        apply mem_centralizer_singleton_iff.mpr
        apply E.injective
        rw [map_mul,map_mul,E.apply_symm_apply,hz]
        exact mem_centralizer_singleton_iff.mp hy
    rw [hmap,ModelClasses.right_long_centralizer]
    rw [←exact_overlap,inf_subgroupOf_right]

end CFSG.Quasithin.ChapterF.UnitaryTwo.AffinePlane
