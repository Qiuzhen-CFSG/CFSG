module

public import Theory.AlgebraicGroup.Tori.Character.Duality
public import Theory.AlgebraicGroup.Dimension.Torus
public import Theory.AlgebraicGroup.ClosedSubgroup.Conjugation
/-!
# The normalizer action of a one-dimensional torus

A regular endomorphism of the one-dimensional torus is an integral power map.
For an algebraic automorphism its inverse gives an inverse integral exponent,
so the exponent is one or minus one. Transport through an actual diagonal
isomorphism proves the same result for every dimension-one torus. Restricting
ambient conjugation and its inverse gives the literal normalizer action.

This is the upper Weyl-group bound in Borel, *Linear Algebraic Groups*,
§13.11(1), used again in §13.13. No root-system or rank-one classification
is assumed, and the proof applies in every characteristic.
-/

public section
namespace Theory.AlgebraicGroup.Bor1.RankOneGeometry
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
open Theory.AlgebraicGroup

private def kMultCoordinate : Variety.Point (KMult k) →* kˣ where
  toFun x := dPointEquiv 1 x 0
  map_one' := by rw [dPointEquiv_one]; rfl
  map_mul' x y := congrFun (dPointEquiv_mul 1 x y) 0

omit [IsAlgClosed k] in
private theorem kMultCoordinate_injective : Function.Injective (kMultCoordinate (k := k)) := by
  intro x y h
  apply (dPointEquiv 1).injective
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact h

private theorem kMult_morphism_power (f : AlgebraicGroup.Morphism (KMult k) (KMult k)) :
    ∃ n : ℤ, ∀ x, f.onPoints x = x ^ n := by
  obtain ⟨z,hz⟩ := dLaurentCharacter_surjective 1 f
  refine ⟨z 0,fun x => ?_⟩
  rw [←hz]
  apply kMultCoordinate_injective
  rw [map_zpow]
  change dPointEquiv 1 ((dLaurentCharacter 1 z).onPoints x) 0 = _
  rw [dLaurentCharacter_apply]
  simp [kMultCoordinate]

theorem kMult_iso_identity_or_inverse (e : AlgebraicGroup.Iso (KMult k) (KMult k)) :
    (∀ x, e.hom.onPoints x = x) ∨ (∀ x, e.hom.onPoints x = x⁻¹) := by
  obtain ⟨n,hn⟩ := kMult_morphism_power e.hom
  obtain ⟨m,hm⟩ := kMult_morphism_power e.inv
  have hnm : n * m = 1 := by
    by_contra hh
    have he : n*m-1 ≠ 0 := sub_ne_zero.mpr hh
    obtain ⟨a,ha⟩ := exists_unit_zpow_ne_one (k := k) he
    let x : Variety.Point (KMult k) := (dPointEquiv 1).symm (fun _ => a)
    have hx := e.hom_inv_id x
    rw [hm,hn,←zpow_mul] at hx
    have hx' := congrArg (kMultCoordinate (k := k)) hx
    rw [map_zpow] at hx'
    apply ha
    rw [zpow_sub,zpow_one,mul_inv_eq_one]
    simpa [x,kMultCoordinate] using hx'
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hnm with h | h
  · left; intro x; simpa [h] using hn x
  · right; intro x; simpa [h] using hn x



theorem torus_dim_one_iso_identity_or_inverse
    {T : Variety k} [AlgebraicGroup T] (hT : IsTorus T)
    (hdim : Variety.dimension T = 1) (a : AlgebraicGroup.Iso T T) :
    (∀ x, a.hom.onPoints x = x) ∨ (∀ x, a.hom.onPoints x = x⁻¹) := by
  obtain ⟨n,⟨e⟩⟩ := hT
  have hn : n = 1 := by
    have h := algebraicGroupIso_dimension_eq e
    rw [dVariety_dimension_eq,hdim] at h
    exact_mod_cast h
  subst n
  let b := e.symm.comp (a.comp e)
  rcases kMult_iso_identity_or_inverse b with h | h
  · left
    intro x
    have hh := congrArg e.hom.onPoints (h (e.inv.onPoints x))
    change e.hom.onPoints (e.inv.onPoints (a.hom.onPoints
      (e.hom.onPoints (e.inv.onPoints x)))) = e.hom.onPoints (e.inv.onPoints x) at hh
    simpa only [e.inv_hom_id] using hh
  · right
    intro x
    have hh := congrArg e.hom.onPoints (h (e.inv.onPoints x))
    change e.hom.onPoints (e.inv.onPoints (a.hom.onPoints
      (e.hom.onPoints (e.inv.onPoints x)))) = e.hom.onPoints ((e.inv.onPoints x)⁻¹) at hh
    simpa only [e.inv_hom_id,map_inv] using hh


variable {G : Variety k} [AlgebraicGroup G]

omit [IsAlgClosed k] in
private theorem exists_normalizerTorusIso (T : ClosedSubgroup G) (n : Variety.Point G)
    (hn : n ∈ T.normalizer.toSubgroup) : ∃ e : AlgebraicGroup.Iso T.carrierVariety T.carrierVariety,
      ∀ x, T.inclusion.onPoints (e.hom.onPoints x) = n * T.inclusion.onPoints x * n⁻¹ := by
  let c (g : Variety.Point G) : AlgebraicGroup.Morphism G G :=
    { toVariety := AlgebraicGroup.conjugationByMorphism G g
      map_one := by simp [AlgebraicGroup.conjugationByMorphism_apply]
      map_mul := by
        intro x y
        simp only [AlgebraicGroup.conjugationByMorphism_apply]
        group }
  have hmap (g : Variety.Point G) (hg : g ∈ T.normalizer.toSubgroup)
      (x : Variety.Point T.carrierVariety) :
      ((c g).comp T.inclusion).onPoints x ∈ T.toSubgroup :=
    (Subgroup.mem_normalizer_iff.mp hg _).mp (T.pointEquiv x).property
  let f := ((c n).comp T.inclusion).codRestrictClosedSubgroup T (hmap n hn)
  let b := ((c n⁻¹).comp T.inclusion).codRestrictClosedSubgroup T
    (hmap n⁻¹ (T.normalizer.toSubgroup.inv_mem hn))
  have hf (x) : T.inclusion.onPoints (f.onPoints x) = n * T.inclusion.onPoints x * n⁻¹ := by
    rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
    rfl
  have hb (x) : T.inclusion.onPoints (b.onPoints x) = n⁻¹ * T.inclusion.onPoints x * n := by
    rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
    change n⁻¹ * T.inclusion.onPoints x * (n⁻¹)⁻¹ = _
    rw [inv_inv]
  exact ⟨{ hom := f,inv := b
           hom_inv_id := fun x => T.inclusion_injective (by rw [hb,hf]; group)
           inv_hom_id := fun x => T.inclusion_injective (by rw [hf,hb]; group) },hf⟩

/-- Every actual normalizer point acts on a dimension-one torus as identity or inversion. -/
theorem normalizer_dim_one_torus_identity_or_inverse
    (T : ClosedSubgroup G) (hT : IsSubtorus T)
    (hdim : Variety.dimension T.carrierVariety = 1)
    (n : Variety.Point G) (hn : n ∈ T.normalizer.toSubgroup) :
    (∀ x ∈ T.toSubgroup, n*x*n⁻¹ = x) ∨
      (∀ x ∈ T.toSubgroup, n*x*n⁻¹ = x⁻¹) := by
  obtain ⟨a,ha⟩ := exists_normalizerTorusIso T n hn
  rcases torus_dim_one_iso_identity_or_inverse hT hdim a with h | h
  · left
    intro x hx
    let t := T.pointEquiv.symm ⟨x,hx⟩
    have ht : T.inclusion.onPoints t = x := congrArg Subtype.val (T.pointEquiv.apply_symm_apply _)
    have hh := congrArg T.inclusion.onPoints (h t)
    rwa [ha,ht] at hh
  · right
    intro x hx
    let t := T.pointEquiv.symm ⟨x,hx⟩
    have ht : T.inclusion.onPoints t = x := congrArg Subtype.val (T.pointEquiv.apply_symm_apply _)
    have hh := congrArg T.inclusion.onPoints (h t)
    rwa [ha,map_inv,ht] at hh
end Theory.AlgebraicGroup.Bor1.RankOneGeometry
