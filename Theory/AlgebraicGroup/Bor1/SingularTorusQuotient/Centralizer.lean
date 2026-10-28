module
public import Theory.AlgebraicGroup.Bor1.SingularTorusQuotient.RankOne
public import Theory.AlgebraicGroup.Bor1.GeometricCertificates
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.TorusRigidity.FiniteBorels

/-!
# The radical quotient of a singular codimension-one centralizer

The original ambient torus and subtorus are embedded by their actual
inclusions into `C_G(S)`. Maximality and dimension are preserved, and `S`
is central in that carrier. Quotienting by its constructed solvable radical
therefore gives a semisimple group with a one-dimensional maximal torus.

Nonsolvability may be given directly, or obtained from the infinite family
of Borels containing `S` by the proved Borel-restriction theorem. The stored
certificate retains the actual quotient morphism, its point-surjectivity,
and its exact closed radical kernel. No rank-one classification, separability,
or conclusion about the Borel curve is presumed.

Source: Borel, *Linear Algebraic Groups*, IV, 13.11.
-/

set_option backward.isDefEq.respectTransparency false

public section
namespace Theory.AlgebraicGroup.Bor1.SingularTorusQuotient
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
open SemisimpleCenterContainment
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

private theorem image_dimension_eq_of_injective
    {H Q : Variety k} [AlgebraicGroup H] [AlgebraicGroup Q]
    (f : AlgebraicGroup.Morphism H Q) (hf : Function.Injective f.onPoints) :
    Variety.dimension f.imageClosedSubgroup.carrierVariety = Variety.dimension H := by
  let : Subsingleton f.kernelClosedSubgroup.toSubgroup := by
    constructor
    intro x y
    apply Subtype.ext
    apply hf
    exact x.property.trans y.property.symm
  let : Subsingleton (Variety.Point f.kernelClosedSubgroup.carrierVariety) :=
    f.kernelClosedSubgroup.pointEquiv.subsingleton
  have hzero : Variety.dimension f.kernelClosedSubgroup.carrierVariety = 0 :=
    (dimension_zero_iff_finite_points _).2 inferInstance
  have heq := morphism_dimension_eq_kernel_add_image f
  rw [hzero,zero_add] at heq
  exact heq.symm

private theorem internal_maximal {T C : ClosedSubgroup G}
    (hT : IsMaximalTorus T) (hTC : T ≤ C) :
    IsMaximalTorus (T.inclusion.codRestrictClosedSubgroup C
      (fun x => hTC (T.pointEquiv x).property)).imageClosedSubgroup := by
  let j := T.inclusion.codRestrictClosedSubgroup C
    (fun x => hTC (T.pointEquiv x).property)
  let A := j.imageClosedSubgroup
  have hj (x : Variety.Point T.carrierVariety) :
      C.inclusion.onPoints (j.onPoints x) = T.inclusion.onPoints x :=
    Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _
  have hAmem (x : Variety.Point C.carrierVariety) : x ∈ A ↔ C.inclusion.onPoints x ∈ T := by
    constructor
    · rintro ⟨t,rfl⟩
      rw [hj]
      exact (T.pointEquiv t).property
    · intro hx
      refine ⟨T.pointEquiv.symm ⟨C.inclusion.onPoints x,hx⟩,C.inclusion_injective ?_⟩
      rw [hj]
      rfl
  refine ⟨morphism_image_isTorus j hT.1, ?_⟩
  intro R hR hAR
  let : AlgebraicGroup R.carrierVariety := R.carrierAlgebraicGroup
  let f := C.inclusion.comp R.inclusion
  have hTf : T ≤ f.imageClosedSubgroup := by
    intro t ht
    let c := C.pointEquiv.symm ⟨t,hTC ht⟩
    have hc : c ∈ R := hAR ((hAmem c).mpr ht)
    exact ⟨R.pointEquiv.symm ⟨c,hc⟩,rfl⟩
  have hfT := hT.2 _ (morphism_image_isTorus f hR) hTf
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · intro r hr
    apply (hAmem r).mpr
    rw [← hfT]
    exact ⟨R.pointEquiv.symm ⟨r,hr⟩,rfl⟩
  · exact hAR

private theorem internal_dim {T C : ClosedSubgroup G} (hTC : T ≤ C) :
    Variety.dimension (T.inclusion.codRestrictClosedSubgroup C
      (fun x => hTC (T.pointEquiv x).property)).imageClosedSubgroup.carrierVariety =
      Variety.dimension T.carrierVariety := by
  apply image_dimension_eq_of_injective
  intro x y hxy
  apply T.inclusion_injective
  simpa only [Morphism.codRestrictClosedSubgroup_inclusion_apply] using
    congrArg C.inclusion.onPoints hxy

private def certificate_of_quotient
    (C : ClosedSubgroup G) (R : ClosedSubgroup C.carrierVariety)
    (hR : IsRadicalSubgroup R) (q : Bor1.Theorem112BQuotientData R)
    : letI : AlgebraicGroup q.quotient := q.quotientAlgebraicGroup
      ∀ (A : ClosedSubgroup q.quotient), IsSemisimpleAlgebraicGroup q.quotient →
        IsMaximalTorus A → Variety.dimension A.carrierVariety = 1 →
        SemisimpleRankOneQuotientCertificate C := by
  let _ : AlgebraicGroup q.quotient := q.quotientAlgebraicGroup
  intro A hq hA hdim
  have hk : q.projection.kernelClosedSubgroup = R := by
    apply SetLike.coe_injective
    ext x
    change x ∈ q.projection.kernel ↔ x ∈ R.toSubgroup
    rw [q.kernel_eq]
  exact @SemisimpleRankOneQuotientCertificate.mk k _ G _ C
    q.quotient q.quotientAlgebraicGroup q.projection q.pointSurjective R hR hk hq A hA hdim

private theorem certificate_of_internal
    (C : ClosedSubgroup G) (hc : Variety.IsConnected C.carrierVariety)
    (hns : ¬ Group.IsSolvable (Variety.Point C.carrierVariety))
    {D A : ClosedSubgroup C.carrierVariety} (hD : IsSubtorus D) (hA : IsMaximalTorus A)
    (hDA : D ≤ A) (hDc : D.toSubgroup ≤ Subgroup.center (Variety.Point C.carrierVariety))
    (hdim : Variety.dimension D.carrierVariety + 1 = Variety.dimension A.carrierVariety) :
    Nonempty (SemisimpleRankOneQuotientCertificate C) := by
  obtain ⟨R,hR,q,hq,hAq,hdimq⟩ :=
    exists_rankOne_radical_quotient_of_central_codimension_one hc hns hD hA hDA hDc hdim
  exact ⟨certificate_of_quotient C R hR q _ hq hAq hdimq⟩

/-- The literal singular subtorus centralizer has a semisimple radical
quotient whose maximal torus has dimension one (Bor1 IV, 13.11). -/
theorem centralizer_rankOne_quotient_of_not_solvable
    (hG : Variety.IsConnected G) {S T : ClosedSubgroup G}
    (hS : IsSubtorus S) (hT : IsMaximalTorus T) (hST : S ≤ T)
    (hcodim : Variety.dimension S.carrierVariety + 1 = Variety.dimension T.carrierVariety)
    (hns : ¬ Group.IsSolvable (Variety.Point S.centralizer.carrierVariety)) :
    Nonempty (SemisimpleRankOneQuotientCertificate S.centralizer) := by
  let C := S.centralizer
  have hTC : T ≤ C := by
    intro t ht
    apply Subgroup.mem_centralizer_iff.mpr
    intro s hs
    exact Subgroup.mem_centralizer_iff.mp (maximalTorus_le_centralizer hT ht) s (hST hs)
  have hSC : S ≤ C := fun _ hs => hTC (hST hs)
  let j := T.inclusion.codRestrictClosedSubgroup C
    (fun x => hTC (T.pointEquiv x).property)
  let i := S.inclusion.codRestrictClosedSubgroup C
    (fun x => hSC (S.pointEquiv x).property)
  let A := j.imageClosedSubgroup
  let D := i.imageClosedSubgroup
  have hj (x : Variety.Point T.carrierVariety) :
      C.inclusion.onPoints (j.onPoints x) = T.inclusion.onPoints x :=
    Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _
  have hi (x : Variety.Point S.carrierVariety) :
      C.inclusion.onPoints (i.onPoints x) = S.inclusion.onPoints x :=
    Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _
  have hAmem (x : Variety.Point C.carrierVariety) : x ∈ A ↔ C.inclusion.onPoints x ∈ T := by
    constructor
    · rintro ⟨t,rfl⟩
      rw [hj]
      exact (T.pointEquiv t).property
    · intro hx
      refine ⟨T.pointEquiv.symm ⟨C.inclusion.onPoints x,hx⟩,C.inclusion_injective ?_⟩
      rw [hj]
      rfl
  have hA : IsMaximalTorus A := internal_maximal hT hTC
  have hD : IsSubtorus D := morphism_image_isTorus i hS
  have hDA : D ≤ A := by
    rintro x ⟨s,rfl⟩
    apply (hAmem _).mpr
    rw [hi]
    exact hST (S.pointEquiv s).property
  have hDc : D.toSubgroup ≤ Subgroup.center (Variety.Point C.carrierVariety) := by
    rintro d ⟨s,rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro c
    apply C.inclusion_injective
    rw [map_mul,map_mul,hi]
    exact (Subgroup.mem_centralizer_iff.mp (C.pointEquiv c).property
      _ (S.pointEquiv s).property).symm
  have hdim : Variety.dimension D.carrierVariety + 1 = Variety.dimension A.carrierVariety := by
    rw [internal_dim hSC,internal_dim hTC]
    exact hcodim
  exact certificate_of_internal C
    (CartanGeometry.subtorus_centralizer_isConnected hG hS)
    hns
    hD hA hDA hDc hdim

/-- Bor1 13.11 in the literal infinite-family formulation of singularity. -/
theorem singular_centralizer_rankOne_quotient
    (hG : Variety.IsConnected G) {S T : ClosedSubgroup G}
    (hS : IsSubtorus S) (hT : IsMaximalTorus T) (hST : S ≤ T)
    (hcodim : Variety.dimension S.carrierVariety + 1 = Variety.dimension T.carrierVariety)
    (hsing : Infinite (BorelContainingIndex S)) :
    Nonempty (SemisimpleRankOneQuotientCertificate S.centralizer) :=
  centralizer_rankOne_quotient_of_not_solvable hG hS hT hST hcodim
    (RadicalGeometry.BorelRestriction.centralizer_not_solvable_of_infinite_borels hG hS hsing)

end Theory.AlgebraicGroup.Bor1.SingularTorusQuotient
