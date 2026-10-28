module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.NormalizerCubicCentralizer
public import Theory.SpecificGroups.SymmetricSix.CubicEvenReflection
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors

/-!
# A chosen endpoint reflection on the original normalizer cubic centralizer

The same endpoint quotient makes its reflection even in the retained six-letter
quotient. The full normalizer cubic centralizer maps isomorphically to the
native cubic centralizer, intertwining the actual reflection action. Its fixed
subgroup has order two.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} [IsElementaryAbelian 2 A]

omit [Finite G] in
private theorem endpoint_even (d : NaturalEndpointData A)
    (f : normalizer (A : Set G) →* Equiv.Perm (Fin 6))
    (hk : f.ker = A.subgroupOf (normalizer (A : Set G))) (r : d.carrier) :
    Equiv.Perm.sign (f (inclusion d.normalizes r)) = 1 := by
  let g := Equiv.Perm.sign.comp (f.comp (inclusion d.normalizes))
  have hkg : d.quotient.ker ≤ g.ker := by
    intro x hx
    have hxA : (x : G) ∈ A := by
      have hh : x ∈ A.subgroupOf d.carrier := d.quotient_kernel ▸ hx
      exact hh
    have hxf : inclusion d.normalizes x ∈ f.ker := hk.symm ▸ hxA
    change Equiv.Perm.sign (f (inclusion d.normalizes x)) = 1
    rw [show f (inclusion d.normalizes x) = 1 from hxf, map_one]
  let k := d.quotient.liftOfSurjective d.quotient_surjective ⟨g,hkg⟩
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect Representation.SL2FourNatural.SL :=
    Group.IsPerfect.ofSurjective
      (f := Representation.SL2FourNatural.alternatingFiveEquiv.symm.toMonoidHom)
      Representation.SL2FourNatural.alternatingFiveEquiv.symm.surjective
  have he : k (d.quotient r) = 1 :=
    Abelianization.commutator_subset_ker k Group.IsPerfect.mem_commutator
  simpa only [k,MonoidHom.liftOfSurjective,MonoidHom.liftOfRightInverse_comp_apply,
    g,MonoidHom.comp_apply] using he

/-- The actual endpoint reflection normalizes the full normalizer cubic
centralizer. Its fixed subgroup has order two, with the same quotient map
and the reflection conjugation formula retained explicitly. -/
theorem NaturalEndpointData.cubic_reflection_action (d : NaturalEndpointData A)
    (t r : G) (ht : t ∈ d.carrier) (ht3 : orderOf t = 3)
    (hr : r ∈ d.carrier) (hr2 : orderOf r = 2) (hinv : r * t * r⁻¹ = t⁻¹) :
    let N := normalizer (A : Set G)
    let E := N ⊓ centralizer ({t} : Set G)
    ∃ hrE : r ∈ normalizer (E : Set G),
      Nat.card (E ⊓ centralizer ({r} : Set G) : Subgroup G) = 2 ∧
      ∃ f : N →* Equiv.Perm (Fin 6), Function.Surjective f ∧
        f.ker = A.subgroupOf N ∧
        orderOf (f ⟨t,d.normalizes ht⟩) = 3 ∧
        orderOf (f ⟨r,d.normalizes hr⟩) = 2 ∧
        Equiv.Perm.sign (f ⟨r,d.normalizes hr⟩) = 1 ∧
        ∃ e : E ≃* centralizer ({f ⟨t,d.normalizes ht⟩} : Set (Equiv.Perm (Fin 6))),
          (∀ x, (e x : Equiv.Perm (Fin 6)) = f ⟨x,x.property.1⟩) ∧
          ∀ x, (e (E.normalizerMonoidHom ⟨r,hrE⟩ x) : Equiv.Perm (Fin 6)) =
            f ⟨r,d.normalizes hr⟩ * (e x : Equiv.Perm (Fin 6)) *
              (f ⟨r,d.normalizes hr⟩)⁻¹ := by
  let N := normalizer (A : Set G)
  let E := N ⊓ centralizer ({t} : Set G)
  let T : N := ⟨t,d.normalizes ht⟩
  let R : N := ⟨r,d.normalizes hr⟩
  have hrC : r ∈ normalizer (centralizer ({t} : Set G) : Set G) := by
    have hh : r ∈ normalizer (zpowers t : Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      rw [MonoidHom.map_zpowers]
      change zpowers (r*t*r⁻¹) = zpowers t
      rw [hinv,zpowers_inv]
    simpa only [zpowers_eq_closure,centralizer_closure] using
      normalizer_le_normalizer_centralizer (zpowers t) hh
  have hrE : r ∈ normalizer (E : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨N.le_normalizer (d.normalizes hr),hrC⟩
  obtain ⟨_,f,hf,hk,hfT,e,he⟩ := d.cubic_full_normalizer_centralizer t ht ht3
  have hfinv : f R * f T * (f R)⁻¹ = (f T)⁻¹ := by
    rw [←map_inv,←map_mul,←map_mul,←map_inv]
    exact congrArg f (Subtype.ext hinv)
  have hfr1 : f R ≠ 1 := by
    intro hh
    have heq : f T = (f T)⁻¹ := by simpa only [hh,one_mul,inv_one,mul_one] using hfinv
    have hp : (f T)^2 = 1 := by
      rw [pow_two]
      nth_rw 1 [heq]
      exact inv_mul_cancel (f T)
    have hd := orderOf_dvd_of_pow_eq_one hp
    rw [hfT] at hd
    norm_num at hd
  have hfR : orderOf (f R) = 2 := orderOf_eq_prime (by
    rw [←map_pow]
    have hh : R^2=1 := Subtype.ext (by simpa [hr2] using pow_orderOf_eq_one r)
    rw [hh,map_one]) hfr1
  have hfe : Equiv.Perm.sign (f R) = 1 := endpoint_even d f hk ⟨r,hr⟩
  have hnative := (Theory.SpecificGroups.SymmetricSix.cubic_even_reflection_centralizer
    (f T) (f R) hfT hfR hfe hfinv).2
  have heconj (x : E) :
      (e (E.normalizerMonoidHom ⟨r,hrE⟩ x) : Equiv.Perm (Fin 6)) =
        f R * (e x : Equiv.Perm (Fin 6)) * (f R)⁻¹ := by
    rw [he,he,←map_inv,←map_mul,←map_mul]
    rfl
  let K := E ⊓ centralizer ({r} : Set G)
  let J := centralizer ({f T} : Set (Equiv.Perm (Fin 6))) ⊓
    centralizer ({f R} : Set (Equiv.Perm (Fin 6)))
  let j : K →* J := {
    toFun x := ⟨e ⟨x,x.property.1⟩,⟨(e ⟨x,x.property.1⟩).property,
      mem_centralizer_singleton_iff.mpr (by
        rw [he,←map_mul,←map_mul]
        exact congrArg f (Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2)))⟩⟩
    map_one' := by
      apply Subtype.ext
      change (e (1 : E) : Equiv.Perm (Fin 6)) = 1
      exact congrArg Subtype.val e.map_one
    map_mul' x y := by
      apply Subtype.ext
      change (e ((⟨x,x.property.1⟩ : E) * ⟨y,y.property.1⟩) : Equiv.Perm (Fin 6)) =
        (e ⟨x,x.property.1⟩ : Equiv.Perm (Fin 6)) * e ⟨y,y.property.1⟩
      exact congrArg Subtype.val (e.map_mul _ _) }
  have hji : Function.Injective j := by
    intro x y hh
    have hv : (e ⟨x,x.property.1⟩ : Equiv.Perm (Fin 6)) = e ⟨y,y.property.1⟩ :=
      congrArg (fun k : J => (k : Equiv.Perm (Fin 6))) hh
    have hh' : (⟨x,x.property.1⟩ : E) = ⟨y,y.property.1⟩ := e.injective (Subtype.ext hv)
    exact Subtype.ext (congrArg (fun k : E => (k : G)) hh')
  have hjs : Function.Surjective j := by
    intro y
    obtain ⟨x,hxy⟩ := e.surjective ⟨y,y.property.1⟩
    have hxfix : E.normalizerMonoidHom ⟨r,hrE⟩ x = x := by
      apply e.injective
      apply Subtype.ext
      rw [heconj,hxy]
      change f R * (y : Equiv.Perm (Fin 6)) * (f R)⁻¹ = y
      rw [←mem_centralizer_singleton_iff.mp y.property.2,mul_inv_cancel_right]
    have hxC : (x : G) ∈ centralizer ({r} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      have hh : r * (x : G) * r⁻¹ = x := congrArg Subtype.val hxfix
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    refine ⟨⟨x,⟨x.property,hxC⟩⟩,?_⟩
    apply Subtype.ext
    change (e x : Equiv.Perm (Fin 6)) = (y : Equiv.Perm (Fin 6))
    exact congrArg (fun k : centralizer ({f T} : Set (Equiv.Perm (Fin 6))) =>
      (k : Equiv.Perm (Fin 6))) hxy
  have hK2 : Nat.card K = 2 :=
    (Nat.card_congr (MulEquiv.ofBijective j ⟨hji,hjs⟩).toEquiv).trans hnative
  exact ⟨hrE,hK2,f,hf,hk,hfT,hfR,hfe,e,he,heconj⟩

end CFSG.Quasithin.HigmanSims
