module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.LargerFieldThree.Reduction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeCommonActors
public import Theory.Representation.BinaryOffender.Embedding
public import Theory.Representation.ConjugateRep

/-!
# The FF obstruction from the two natural SL₃ types

For two natural SL₃ representations of the same component, the first
coordinate and the literal quotient of their product form the B.4.9
extension. That theorem forces equal module types if the product is FF.
An equivariant embedding of disjoint constituents transfers the offender
budget, excluding FF on any invariant subspace containing two distinct
natural types. Conjugation transports the actual natural action.

The Chapter12 application constructs this pair from the original seed and
its moved Sylow conjugate. Source: Aschbacher--Smith B.4.9(2), D.3.9(1)
and D.3.13, printed pp.92--94,199--202. The local first-coordinate and
quotient constructions follow SourceCompletion/CommonActors.
-/

public noncomputable section
open Representation Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB.QuasisimpleSource
namespace LinearThreePair
variable {H X Y : Type*} [Group H]
  [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
  (ρ : Representation (ZMod 2) H X) (σ : Representation (ZMod 2) H Y)
private def first : Subrepresentation (ρ.prod σ) where
  toSubmodule := LinearMap.ker (LinearMap.snd (ZMod 2) X Y)
  apply_mem_toSubmodule g v hv := by
    change σ g v.2 = 0
    rw [show v.2 = 0 from hv,map_zero]
private def firstEquiv : (first ρ σ).toRepresentation.Equiv ρ where
  toFun v := v.val.1
  invFun v := ⟨(v,0),rfl⟩
  left_inv v := by apply Subtype.ext; exact Prod.ext rfl v.property.symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' _ := rfl
private def quotientEquiv : (first ρ σ).quotientRepresentation.Equiv σ :=
  .mk ((LinearMap.snd (ZMod 2) X Y).quotKerEquivOfSurjective LinearMap.snd_surjective) (by
    intro g
    apply LinearMap.ext
    intro v
    refine Submodule.Quotient.induction_on _ v ?_
    intro w
    rfl)

/-- Two actual natural SL₃ modules whose product is FF have the same
unchanged-actor module type. The literal quotient is used in B.4.9. -/
theorem same_of_ff [FiniteDimensional (ZMod 2) X] [FiniteDimensional (ZMod 2) Y]
    (F : BinaryField) (a : ActionEquiv ρ (linearNatural F 3))
    (b : ActionEquiv σ (linearNatural F 3)) (hff : IsFFModule (ρ.prod σ)) :
    Nonempty (ρ.Equiv σ) := by
  let e := firstEquiv ρ σ
  let q := quotientEquiv ρ σ
  let an : ActionEquiv (first ρ σ).toRepresentation (linearNatural F 3) :=
    ⟨a.groupEquiv,e.toLinearEquiv.trans a.linearEquiv,by
      intro g v
      exact a.intertwines g v.val.1⟩
  let bn : ActionEquiv (first ρ σ).quotientRepresentation (linearNatural F 3) :=
    ⟨b.groupEquiv,q.toLinearEquiv.trans b.linearEquiv,by
      intro g v
      exact (congrArg b.linearEquiv (LinearMap.congr_fun (q.isIntertwining' g) v)).trans
        (b.intertwines g (q v))⟩
  let d : ChapterB.NaturalExtensions.DoubleNatural F 3 (ρ.prod σ) :=
    { faithful := by
        intro g h he
        apply a.groupEquiv.injective
        apply specialLinearNatural_injective 3
        apply LinearMap.ext
        intro v
        obtain ⟨w,rfl⟩ := a.linearEquiv.surjective v
        exact (a.intertwines g w).symm.trans
          ((congrArg a.linearEquiv (congrArg Prod.fst (LinearMap.congr_fun he (w,0)))).trans
            (a.intertwines h w))
      space := first ρ σ
      natural := an
      quotient := ChapterB.QuasisimpleSource.SourceCompletion.linearThree_naturals_same_or_dual
        _ _ F F ⟨bn⟩ ⟨an⟩ }
  obtain ⟨c⟩ := d.three_same_orientation hff
  exact ⟨e.symm.trans (c.symm.trans q)⟩
end LinearThreePair

/-- Disjoint nonisomorphic natural SL₃ constituents exclude an FF offender
for the original component on any module containing both. -/
theorem no_ff_of_disjoint_natural_linearThree
    {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) (I J : Subrepresentation ρ)
    (hd : Disjoint I.toSubmodule J.toSubmodule) (F : BinaryField)
    (a : ActionEquiv I.toRepresentation (linearNatural F 3))
    (b : ActionEquiv J.toRepresentation (linearNatural F 3))
    (hne : ¬ Nonempty (I.toRepresentation.Equiv J.toRepresentation)) :
    ¬ IsFFModule ρ := by
  rintro ⟨A,hA⟩
  apply hne
  apply LinearThreePair.same_of_ff _ _ F a b
  refine ⟨A,hA.1,le_trans ?_ hA.2⟩
  let f := I.toSubmodule.subtype.coprod J.toSubmodule.subtype
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro v hv
    change v.1.val + v.2.val = 0 at hv
    have hu : v.1.val ∈ J.toSubmodule := by
      rw [eq_neg_of_add_eq_zero_left hv]
      exact J.toSubmodule.neg_mem v.2.property
    have hz := (Submodule.disjoint_def.mp hd) v.1.val v.1.property hu
    have hw : v.2.val = 0 := by simpa only [hz,zero_add] using hv
    exact Prod.ext (Subtype.ext hz) (Subtype.ext hw)
  simpa only [Subgroup.map_id] using fixedCodim_map_le_of_embedding ρ
    (I.toRepresentation.prod J.toRepresentation) (MonoidHom.id H) f hf
    (fun g v => map_add (ρ g) v.1.val v.2.val) A

/-- Conjugating the actual constituent preserves its natural model,
including the original component as the acting carrier. -/
def conjugate_linearThree_action
    {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) (K : Subgroup H) [K.Normal]
    (I : Subrepresentation (ρ.comp K.subtype)) (F : BinaryField)
    (a : ActionEquiv I.toRepresentation (linearNatural F 3)) (g : H) :
    ActionEquiv (conjugateSubrepresentationOrderIso ρ K g I).toRepresentation
      (linearNatural F 3) := by
  let c := conjugateSubrepresentationEquiv ρ K I g⁻¹
  refine ⟨(MulAut.conjNormal g⁻¹).trans a.groupEquiv,
    c.toLinearEquiv.trans a.linearEquiv,?_⟩
  intro k v
  exact (congrArg a.linearEquiv (c.isIntertwining k v)).trans
    (a.intertwines ((MulAut.conjNormal g⁻¹) k) (c v))

/-- The exclusion applies to the actual containing subspace, not only to
the whole ambient representation. -/
theorem no_ff_on_subspace_of_disjoint_natural_linearThree
    {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) (I J W : Subrepresentation ρ)
    (hIW : I ≤ W) (hJW : J ≤ W)
    (hd : Disjoint I.toSubmodule J.toSubmodule) (F : BinaryField)
    (a : ActionEquiv I.toRepresentation (linearNatural F 3))
    (b : ActionEquiv J.toRepresentation (linearNatural F 3))
    (hne : ¬ Nonempty (I.toRepresentation.Equiv J.toRepresentation)) :
    ¬ IsFFModule W.toRepresentation := by
  let I' := sectionLower ρ I W
  let J' := sectionLower ρ J W
  let e : I'.toRepresentation.Equiv I.toRepresentation :=
    .mk (sectionLowerEquiv ρ hIW) (by intro g; rfl)
  let f : J'.toRepresentation.Equiv J.toRepresentation :=
    .mk (sectionLowerEquiv ρ hJW) (by intro g; rfl)
  have hd' : Disjoint I'.toSubmodule J'.toSubmodule := by
    apply Submodule.disjoint_def.mpr
    intro v hi hj
    exact Subtype.ext ((Submodule.disjoint_def.mp hd) v.val hi hj)
  let a' : ActionEquiv I'.toRepresentation (linearNatural F 3) :=
    ⟨a.groupEquiv,e.toLinearEquiv.trans a.linearEquiv,by intro g v; exact a.intertwines g (e v)⟩
  let b' : ActionEquiv J'.toRepresentation (linearNatural F 3) :=
    ⟨b.groupEquiv,f.toLinearEquiv.trans b.linearEquiv,by intro g v; exact b.intertwines g (f v)⟩
  apply no_ff_of_disjoint_natural_linearThree W.toRepresentation I' J' hd' F a' b'
  rintro ⟨c⟩
  exact hne ⟨e.symm.trans (c.trans f)⟩
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
