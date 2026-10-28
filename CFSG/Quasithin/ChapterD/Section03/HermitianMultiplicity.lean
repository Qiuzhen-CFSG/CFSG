module
public import Theory.Representation.SL2.HermitianImage
public import Theory.Representation.OrthogonalFourMinusRankOne.NormalizerRank
public import Theory.Representation.BinaryOffender.NormalizerImage
public import Theory.Representation.BinaryOffender.NormalizerNonStrong
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.CubicBudget
public import Theory.Representation.BinaryOffender.GeneratedCore
public import CFSG.Quasithin.ChapterD.Section03.EvenConstituent
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.Assembly

/-!
# Hermitian constituents cannot repeat under a faithful small actor

The full binary normalizer of the Hermitian SL₂(2^(2s)) module is non-FF for
s>1. To prove this without assuming SQTK for that whole normalizer, adjoin a
putative cubic offender to its actual component image and apply the proved
Chapter K orthogonal calculation there. Only the component's SQTK is used.

Hermitian type is invariant under the full compatible normalizer. If its
isotypic restriction were reducible, two invariant sections would each cost
strictly more than the rank of the same quotient-faithful elementary actor.
This contradicts the two-rank budget. The image formulation descends the
original quotient action and does not require an elementary lift.

Source: Aschbacher--Smith D.3.9(1) and K.3.1.2, pp.199--200,454.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped MatrixGroups MonoidAlgebra
namespace CFSG.Quasithin.ChapterD
open Representation.OrthogonalFourMinus.FiniteModel Representation.OrthogonalFourMinus.RankOne
variable (s : ℕ) [NeZero s]
local instance : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

theorem hermitian_normalizer_not_ff
    [IsQuasisimple SL(2,Field s)]
    (hS : IsSQTK KnownSimple.IsKnownSimple SL(2,Field s)) (hs : 1 < s) :
    ¬ IsFFModule (normalizerRepresentation (SL2.BinarySmall.hermitian s)) := by
  let μ := SL2.BinarySmall.hermitian s
  let : Finite (Module.End (ZMod 2) (Space s)) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) (Space s) => (f : Space s → Space s))
      DFunLike.coe_injective
  let : Finite (Module.End (ZMod 2) (Space s))ˣ :=
    Finite.of_injective Units.val Units.val_injective
  let Q := linearNormalizer μ
  let K := (actionImage μ).subgroupOf Q
  have hle : actionImage μ ≤ Q := (actionImage μ).le_normalizer
  let : K.Normal := (normal_subgroupOf_iff_le_normalizer hle).mpr le_rfl
  let e0 := MonoidHom.ofInjective (show Function.Injective μ.asGroupHom from by
    intro g h he
    exact hermitian_injective s (congrArg Units.val he))
  let e : K ≃* SL(2,Field s) := (subgroupOfEquivOfLe hle).trans e0.symm
  let ρ := normalizerRepresentation μ
  have he (g : K) (v : Space s) : ρ (g : Q) v = μ (e g) v := by
    exact congrArg (fun z : actionImage μ => z.val.val v)
      (e0.apply_symm_apply (subgroupOfEquivOfLe hle g)).symm
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv e.symm
  have hK : IsSQTK KnownSimple.IsKnownSimple K := hS.knownSimple_of_equiv e.symm
  have hirr : IsIrreducible (ρ.comp K.subtype) := by
    have hrep : ρ.comp K.subtype = μ.comp e.toMonoidHom := by
      apply MonoidHom.ext
      intro g
      apply LinearMap.ext
      exact he g
    rw [hrep]
    exact (irreducible_comp_surjective_iff e.toMonoidHom e.surjective μ).mpr
      (SL2.BinarySmall.hermitian_irreducible s)
  intro hff
  obtain ⟨A,hA,hc,hr⟩ := (cubicRatio_le_iff ρ (by simp)).mp
    ((isFFModule_iff_cubicRatio_le_one ρ).mp hff)
  have hsrc := normal_component_actor_source ρ (normalizerRepresentation_injective μ)
    K hK hirr A hA hc (hr.trans (by norm_num))
  let H := K ⊔ A
  let B := K.subgroupOf H
  let eB := subgroupOfEquivOfLe (show K ≤ H from le_sup_left)
  let M : ChapterK.RankOne.OrthogonalModel s (ρ.comp H.subtype) B := {
    groupEquiv := eB.trans e
    coordinates := LinearEquiv.refl _ _
    intertwines g v := he (eB g) v }
  apply hsrc.orthogonal_not_ff M hs
  let P := A.subgroupOf H
  have hP : IsElementaryTwo P := by
    let : IsElementaryAbelian 2 A := hA.2
    refine ⟨?_,IsElementaryAbelian.subgroupOf (show A ≤ H from le_sup_right)⟩
    intro hp
    change A.subgroupOf H = ⊥ at hp
    apply hA.1
    rw [←map_subgroupOf_eq_of_le (show A ≤ H from le_sup_right),hp,Subgroup.map_bot]
  refine ⟨P,hP,?_⟩
  change fixedCodim (ρ.comp H.subtype) (A.subgroupOf H) ≤ rank (A.subgroupOf H)
  rw [fixedCodim_subgroupOf ρ (show A ≤ H from le_sup_right),
    rank_subgroupOf (show A ≤ H from le_sup_right)]
  exact (actionRatio_le_one_iff ρ hA).mp hr

universe u v
variable {G : Type u} [Group G] {V : Type v}
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem hermitian_irreducible_of_faithful_actor
    [IsQuasisimple SL(2,Field s)]
    (hS : IsSQTK KnownSimple.IsKnownSimple SL(2,Field s)) (hs : 1 < s)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (K : Subgroup G) [K.Normal]
    (q : K →* SL(2,Field s)) (hq : Function.Surjective q)
    (α : G →* MulAut SL(2,Field s))
    (hα : ∀ (a : G) (k : K), q (MulAut.conjNormal a k) = α a (q k))
    (I : Subrepresentation (ρ.comp K.subtype)) (hI : I.toRepresentation.IsIrreducible)
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ k v, E (SL2.BinarySmall.hermitian s (q k) v) = I.toRepresentation k (E v))
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hf : Function.Injective (α.comp A.subtype))
    (hb : fixedCodim ρ A ≤ 2 * rank A) :
    IsIrreducible (ρ.comp K.subtype) := by
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  let : Nontrivial V := (inferInstance : IsSimpleModule (ZMod 2)[G] ρ.asModule).nontrivial
  let : IsSemisimpleModule (ZMod 2)[K] (Representation.asModule (ρ.comp K.subtype)) :=
    NormalConstituentDisplacement.restriction_semisimple ρ inferInstance K
  have ht : (normalTypeAction ρ K).inertia I = ⊤ := by
    apply top_unique
    intro a _
    exact SL2Hermitian.sameModule_conjugate s ρ K q α hα I E hE a
  have htype := restriction_isotypic_of_typeInertia_top ρ K I hI ht
  by_contra hred
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨U,W,_hU,_hW,heU,heW⟩ := exists_two_restricted_sections_of_isotypic
    ρ K I htype A (IsElementaryAbelian.isPGroup 2 A) hred
  let H := K ⊔ A
  let B := K.subgroupOf H
  let P := A.subgroupOf H
  let e := subgroupOfEquivOfLe (show K ≤ H from le_sup_left)
  let eA := subgroupOfEquivOfLe (show A ≤ H from le_sup_right)
  let I' := I.compActors e.toMonoidHom
  let q' := q.comp e.toMonoidHom
  let α' := α.comp H.subtype
  have hα' (a : H) (k : B) : q' (MulAut.conjNormal a k) = α' a (q' k) :=
    hα a.val (e k)
  have hf' : Function.Injective (α'.comp P.subtype) := by
    intro a b hab
    apply eA.injective
    exact hf hab
  have hsection {Y : Type v} [AddCommGroup Y] [Module (ZMod 2) Y]
      (τ : Representation (ZMod 2) H Y) (X : Subrepresentation τ)
      (hX : Nonempty ((X.compActors B.subtype).asSubmodule ≃ₗ[(ZMod 2)[B]] I'.asSubmodule)) :
      (∀ a ∈ P, (∀ v, X.toRepresentation a v = v) → a = 1) ∧
        ¬ IsFFModule (imageRepresentation X.toRepresentation) := by
    let er := equiv_of_asSubmodule_equiv (τ.comp B.subtype)
      ((ρ.comp K.subtype).comp e.toMonoidHom) (X.compActors B.subtype) I' hX.some
    let E' : Space s ≃ₗ[ZMod 2] I'.toSubmodule := E
    have hE' (k : B) (v : Space s) :
        E' (SL2.BinarySmall.hermitian s (q' k) v) = I'.toRepresentation k (E' v) := hE (e k) v
    let b : Representation.Equiv (X.compActors B.subtype).toRepresentation
        ((SL2.BinarySmall.hermitian s).comp q') := {
      __ := er.toLinearEquiv.trans E'.symm
      isIntertwining' k := by
        apply LinearMap.ext
        intro v
        change E'.symm (er.toLinearEquiv ((X.compActors B.subtype).toRepresentation k v)) =
          SL2.BinarySmall.hermitian s (q' k) (E'.symm (er.toLinearEquiv v))
        apply E'.injective
        rw [E'.apply_symm_apply,hE',E'.apply_symm_apply]
        exact LinearMap.congr_fun (er.isIntertwining' k) v }
    have hfaith := faithful_actor_of_marked_normal_action X.toRepresentation B
      (SL2.BinarySmall.hermitian s) (hermitian_injective s) q' (hq.comp e.surjective)
      α' hα' b P hf'
    have hi : B.subtype.range = B := Subgroup.range_subtype B
    let : B.subtype.range.Normal := hi.symm ▸ (inferInstance : B.Normal)
    exact ⟨hfaith,not_isFFModule_image_of_marked_normal_range X.toRepresentation B.subtype
      (SL2.BinarySmall.hermitian s) q' (hq.comp e.surjective) b
      (hermitian_normalizer_not_ff s hS hs)⟩
  obtain ⟨hfU,hnU⟩ := hsection (ρ.comp H.subtype) U heU
  obtain ⟨hfW,hnW⟩ := hsection U.quotientRepresentation W heW
  exact (not_lt_of_ge hb)
    (twice_rank_lt_fixedCodim_of_restricted_nonFF_submodule_sections ρ
      hA le_sup_right U W hfU hfW hnU hnW)
/-- The Hermitian multiplicity exclusion uses the literal faithful image actor and its unchanged module. -/
theorem hermitian_irreducible_of_faithful_image_actor
    [IsQuasisimple SL(2,Field s)]
    (hS : IsSQTK KnownSimple.IsKnownSimple SL(2,Field s)) (hs : 1 < s)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (K : Subgroup G) [K.Normal]
    (q : K →* SL(2,Field s)) (hq : Function.Surjective q)
    (α : G →* MulAut (SL(2,Field s)))
    (hα : ∀ (a : G) (k : K), q (MulAut.conjNormal a k) = α a (q k))
    (I : Subrepresentation (ρ.comp K.subtype)) (hI : I.toRepresentation.IsIrreducible)
    (E : (Space s) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ k v, E (SL2.BinarySmall.hermitian s (q k) v) = I.toRepresentation k (E v))
    (A : Subgroup (actionImage ρ)) (hA : IsElementaryTwo A)
    (hf : Function.Injective ((SL2Hermitian.hermitianImageQuotientAction s ρ K q hq α hα I E hE).comp A.subtype))
    (hb : fixedCodim (imageRepresentation ρ) A ≤ 2 * rank A) :
    IsIrreducible (ρ.comp K.subtype) := by
  let σ := imageRepresentation ρ
  let f0 := (actionHom ρ).comp K.subtype
  let B := f0.range
  have hB : B = K.map (actionHom ρ) := by
    change ((actionHom ρ).comp K.subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let : B.Normal := hB ▸ Subgroup.Normal.map inferInstance (actionHom ρ)
    ρ.asGroupHom.rangeRestrict_surjective
  let f : K →* B := f0.rangeRestrict
  have hf0 : Function.Surjective f := f0.rangeRestrict_surjective
  have hk : f.ker ≤ q.ker := by
    intro k hk
    apply SL2Hermitian.hermitian_constituent_detects_component_kernel s ρ K q I E hE
    exact congrArg (fun b : B => (b : actionImage ρ)) hk
  let qb : B →* SL(2,Field s) := f.liftOfSurjective hf0 ⟨q,hk⟩
  have hqb (k : K) : qb (f k) = q k := f.liftOfRightInverse_comp_apply _ _ _ k
  have hqb_surj : Function.Surjective qb := by
    intro g
    obtain ⟨k,rfl⟩ := hq g
    exact ⟨f k,hqb k⟩
  let αb := SL2Hermitian.hermitianImageQuotientAction s ρ K q hq α hα I E hE
  have hαb (a : actionImage ρ) (b : B) :
      qb (MulAut.conjNormal a b) = αb a (qb b) := by
    obtain ⟨g,rfl⟩ := ρ.asGroupHom.rangeRestrict_surjective a
    obtain ⟨k,rfl⟩ := hf0 b
    have hc : MulAut.conjNormal (actionHom ρ g) (f k) = f (MulAut.conjNormal g k) := by
      apply Subtype.ext
      change actionHom ρ g * actionHom ρ (k : G) * (actionHom ρ g)⁻¹ =
        actionHom ρ (g * (k : G) * g⁻¹)
      simp only [map_mul,map_inv]
    change qb (MulAut.conjNormal (actionHom ρ g) (f k)) = αb (actionHom ρ g) (qb (f k))
    rw [hc,hqb,hqb]
    exact (hα g k).trans (congrArg (fun z : MulAut (SL(2,Field s)) => z (q k))
      (SL2Hermitian.hermitianImageQuotientAction_apply s ρ K q hq α hα I E hE g).symm)
  let J : Subrepresentation (σ.comp B.subtype) := {
    toSubmodule := I.toSubmodule
    apply_mem_toSubmodule b v hv := by
      obtain ⟨k,rfl⟩ := hf0 b
      exact I.apply_mem_toSubmodule k hv }
  have hJ : J.toRepresentation.IsIrreducible :=
    (irreducible_comp_surjective_iff f hf0 J.toRepresentation).mp hI
  let E' : (Space s) ≃ₗ[ZMod 2] J.toSubmodule := E
  have hE' (b : B) v : E' (SL2.BinarySmall.hermitian s (qb b) v) = J.toRepresentation b (E' v) := by
    obtain ⟨k,rfl⟩ := hf0 b
    rw [hqb]
    exact hE k v
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective σ).mp (inferInstance : ρ.IsIrreducible)
  have hirr := hermitian_irreducible_of_faithful_actor s hS hs σ B qb hqb_surj αb hαb
    J hJ E' hE' A hA hf hb
  exact (irreducible_comp_surjective_iff f hf0 (σ.comp B.subtype)).mpr hirr

end CFSG.Quasithin.ChapterD
