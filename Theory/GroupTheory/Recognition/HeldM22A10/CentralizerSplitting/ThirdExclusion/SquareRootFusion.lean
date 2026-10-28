module

public import Theory.GroupTheory.CharacteristicSylowCentralizerFusion

/-!
# Square-root counts and weak closure of a central involution

Automorphisms preserve square-root counts. If these counts single out a
central involution inside each proper involution centralizer of a Sylow
two-subgroup, the corresponding ambient normalizers fix that involution.
The maximal-centralizer argument then proves its weak closure.

The numerical rigidity conditions are explicit inputs here; they are certified
for the third Held candidate in `Geometry`. This module proves only the
general counting and fusion implications.

The fusion argument is the characteristic-centralizer method of
Janko--Thompson (1970), §4, p.392, in the imported module. Its use here is
for Huppert--Blackburn III, XII.1.18(b), p.314.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.ThirdExclusion

@[expose] public noncomputable def squareRootCount {H : Type*} [Group H] (t w : H) : ℕ :=
  Nat.card {x : H // x * t = t * x ∧ x * x = w}

public theorem squareRootCount_equiv {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) (t w : H) : squareRootCount (e t) (e w) = squareRootCount t w := by
  symm
  apply Nat.card_congr (Equiv.subtypeEquiv e.toEquiv _)
  intro x
  change (x * t = t * x ∧ x * x = w) ↔
    (e x * e t = e t * e x ∧ e x * e x = e w)
  simp only [← map_mul, e.injective.eq_iff]

private theorem squareRootCount_subtype {H : Type*} [Group H] (t : H)
    (w : centralizer ({t} : Set H)) :
    squareRootCount t (w : H) = Nat.card {x : centralizer ({t} : Set H) // x * x = w} := by
  apply Nat.card_congr
  exact {
    toFun := fun x => ⟨⟨x, mem_centralizer_singleton_iff.mpr x.property.1⟩,
      Subtype.ext x.property.2⟩
    invFun := fun x => ⟨x.val, mem_centralizer_singleton_iff.mp x.val.property,
      congrArg Subtype.val x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

private theorem squareRootCount_aut {H : Type*} [Group H] (t : H)
    (a : MulAut (centralizer ({t} : Set H))) (w : centralizer ({t} : Set H)) :
    squareRootCount t (a w : H) = squareRootCount t (w : H) := by
  rw [squareRootCount_subtype, squareRootCount_subtype]
  symm
  apply Nat.card_congr (Equiv.subtypeEquiv a.toEquiv _)
  intro x
  change x * x = w ↔ a x * a x = a w
  simp only [← map_mul, a.injective.eq_iff]

/-- A central involution singled out by its square-root count is fixed by
all automorphisms of the involution centralizer. -/
public theorem centralizer_aut_fix {H : Type*} [Group H]
    (z t : H) (hzC : z ∈ center H) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hrigid : ∀ w : H, w ≠ 1 → w * w = 1 →
      (∀ x : H, x * t = t * x → w * x = x * w) →
      squareRootCount t w = squareRootCount t z → w = z)
    (a : MulAut (centralizer ({t} : Set H))) :
    (a ⟨z, mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hzC t).symm⟩ : H) = z := by
  let zC : centralizer ({t} : Set H) :=
    ⟨z, mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hzC t).symm⟩
  have hzCC : zC ∈ center (centralizer ({t} : Set H)) := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_center_iff.mp hzC x)
  have hazC : a zC ∈ center (centralizer ({t} : Set H)) :=
    characteristic_iff_le_comap.mp inferInstance a hzCC
  apply hrigid
  · intro he
    have h : a zC = 1 := Subtype.ext he
    have h' : zC = 1 := a.injective (h.trans a.map_one.symm)
    exact hz1 (congrArg Subtype.val h')
  · have h : zC * zC = 1 := Subtype.ext hz2
    exact congrArg Subtype.val (show a zC * a zC = 1 by rw [← map_mul, h, map_one])
  · intro x hx
    exact (congrArg Subtype.val
      (mem_center_iff.mp hazC ⟨x, mem_centralizer_singleton_iff.mpr hx⟩)).symm
  · exact squareRootCount_aut t a zC

/-- Intrinsic fixed points give normalizer control on the actual ambient image. -/
public theorem normalizer_le_of_aut_fix {G : Type*} [Group G]
    (S : Subgroup G) (C : Subgroup S) (z : C)
    (hfix : ∀ a : MulAut C, a z = z) :
    normalizer (C.map S.subtype : Set G) ≤ centralizer ({((z : S) : G)} : Set G) := by
  let K := C.map S.subtype
  let e : C ≃* K := C.equivMapOfInjective S.subtype S.subtype_injective
  intro g hg
  let a := K.normalizerMonoidHom ⟨g, hg⟩
  have he : a (e z) = e z := by
    have h := congrArg e (hfix ((e.trans a).trans e.symm))
    simpa using h
  have h : g * ((z : S) : G) * g⁻¹ = ((z : S) : G) :=
    congrArg Subtype.val he
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h)

/-- Square counts in every noncentral involution centralizer imply weak closure.
The centralizer-maximality argument supplies the needed saturation. -/
public theorem eq_of_isConj_of_squareRootCount {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (z : S) (hzC : z ∈ center S) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hunique : ∀ w : S, w ∈ center S → w * w = 1 → w ≠ 1 → w = z)
    (hrigid : ∀ t : S, t * t = 1 → t ≠ 1 → t ≠ z →
      ∀ w : S, w ≠ 1 → w * w = 1 →
      (∀ x : S, x * t = t * x → w * x = x * w) →
      squareRootCount t w = squareRootCount t z → w = z)
    (t : S) (hconj : IsConj (z : G) (t : G)) : t = z := by
  by_contra htz
  let X : Set S := {w | w * w = 1 ∧ w ≠ 1 ∧ w ≠ z}
  have ht2 : t * t = 1 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    apply Subtype.ext
    have h := congrArg (MulAut.conj g)
      (show (z : G) * (z : G) = 1 from congrArg Subtype.val hz2)
    have hg' : (MulAut.conj g) (z : G) = (t : G) := hg
    change (t : G) * (t : G) = 1
    simpa only [map_mul, map_one, hg'] using h
  have ht1 : t ≠ 1 := by
    intro ht
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    apply hz1
    apply Subtype.ext
    apply (MulAut.conj g).injective
    exact hg.trans ((congrArg Subtype.val ht).trans (map_one _).symm)
  apply S.not_isConj_of_stable_centralizer_normalizers z hzC X _ _ _ t ⟨ht2, ht1, htz⟩ hconj
  · intro w hw g hg u hu
    have hgz : (MulAut.conj g) (z : G) = (z : G) :=
      mul_inv_eq_iff_eq_mul.mpr hg.eq
    refine ⟨?_, ?_, ?_⟩
    · apply Subtype.ext
      have h := congrArg (MulAut.conj g) (congrArg Subtype.val hw.1)
      simpa only [Subgroup.coe_mul, Subgroup.coe_one, map_mul, map_one, hu] using h
    · intro he
      apply hw.2.1
      apply Subtype.ext
      apply (MulAut.conj g).injective
      rw [hu, he]
      exact (map_one _).symm
    · intro he
      apply hw.2.2
      apply Subtype.ext
      apply (MulAut.conj g).injective
      rw [hu, he, hgz]
  · intro w hw _ he
    apply hw.2.2
    apply hunique w _ hw.1 hw.2.1
    apply mem_center_iff.mpr
    intro x
    exact mem_centralizer_singleton_iff.mp (show x ∈ centralizer ({w} : Set S) by rw [he]; trivial)
  · intro w hw _
    let zC : centralizer ({w} : Set S) :=
      ⟨z, mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hzC w).symm⟩
    apply normalizer_le_of_aut_fix (S : Subgroup G) _ zC
    intro a
    apply Subtype.ext
    exact centralizer_aut_fix z w hzC hz1 hz2 (hrigid w hw.1 hw.2.1 hw.2.2) a

end Theory.GroupTheory.HeldM22A10.ThirdExclusion
