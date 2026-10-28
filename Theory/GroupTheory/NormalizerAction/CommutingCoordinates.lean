module
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.NormalizerAction

/-!
# Conjugation coordinates on a direct product of ambient subgroups

Multiplication identifies two disjoint commuting subgroups with their join.
The retained factor formulas identify conjugation by an actor centralizing the
second factor with the first factor action extended by the identity. Preserving
either coordinate factor is equivalent to normalizing that ambient subgroup.

This is the product-coordinate step for the enlarged elementary subgroup in
Aschbacher–Smith, proof of 14.4.4, printed p.1007. No existence of an ambient
normalizing actor is assumed or deduced by these transport lemmas.
-/

@[expose] public section
open Subgroup
namespace Subgroup.NormalizerAction
variable {G X Y : Type*} [Group G] [Group X] [Group Y]

/-- Coordinates on the actual product, retaining multiplication of the factors. -/
structure ProductCoordinates (A D : Subgroup G) (a : A ≃* X) (d : D ≃* Y) where
  equiv : (A ⊔ D : Subgroup G) ≃* X × Y
  apply_mul : ∀ (x : A) (y : D),
    equiv ⟨(x : G) * y, mul_mem_sup x.property y.property⟩ = (a x,d y)

theorem productCoordinates_nonempty (A D : Subgroup G) (a : A ≃* X) (d : D ≃* Y)
    (hd : Disjoint A D) (hc : A ≤ centralizer (D : Set G)) :
    Nonempty (ProductCoordinates A D a d) := by
  obtain ⟨m,hm⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A D hd hc
  refine ⟨⟨m.symm.trans (a.prodCongr d),?_⟩⟩
  intro x y
  have he : (⟨(x : G)*y,mul_mem_sup x.property y.property⟩ : (A ⊔ D : Subgroup G)) =
      m (x,y) := Subtype.ext (hm x y).symm
  rw [he]
  change (a.prodCongr d) (m.symm (m (x,y))) = _
  rw [m.symm_apply_apply]
  rfl

variable {A D : Subgroup G} {a : A ≃* X} {d : D ≃* Y}
variable (e : ProductCoordinates A D a d)

theorem ProductCoordinates.apply_left (x : A) :
    e.equiv (inclusion le_sup_left x) = (a x,1) := by
  calc
    _ = e.equiv ⟨(x:G)*(1:D),mul_mem_sup x.property (D.one_mem)⟩ := by
      apply congrArg e.equiv
      apply Subtype.ext
      exact (mul_one (x:G)).symm
    _ = (a x,d 1) := e.apply_mul x 1
    _ = _ := by rw [map_one]

theorem ProductCoordinates.apply_right (y : D) :
    e.equiv (inclusion le_sup_right y) = (1,d y) := by
  calc
    _ = e.equiv ⟨((1:A):G)*y,mul_mem_sup (A.one_mem) y.property⟩ := by
      apply congrArg e.equiv
      apply Subtype.ext
      exact (one_mul (y:G)).symm
    _ = (a 1,d y) := e.apply_mul 1 y
    _ = _ := by rw [map_one]

/-- Conjugation by an actor centralizing the second factor extends its first
factor action by the identity, in these same product coordinates. -/
theorem ProductCoordinates.action_eq (n : G)
    (hnA : n ∈ normalizer (A : Set G)) (hnD : n ∈ centralizer (D : Set G))
    (hnB : n ∈ normalizer ((A ⊔ D : Subgroup G) : Set G)) :
    MulAut.congr e.equiv ((A ⊔ D).normalizerMonoidHom ⟨n,hnB⟩) =
      (MulAut.congr a (A.normalizerMonoidHom ⟨n,hnA⟩)).prodCongr (MulEquiv.refl Y) := by
  apply MulEquiv.ext
  rintro ⟨x,y⟩
  obtain ⟨v,rfl⟩ := a.surjective x
  obtain ⟨w,rfl⟩ := d.surjective y
  have he := e.apply_mul v w
  change e.equiv ((A ⊔ D).normalizerMonoidHom ⟨n,hnB⟩ (e.equiv.symm (a v,d w))) = _
  rw [←he,e.equiv.symm_apply_apply]
  have hc : n*(w:G)*n⁻¹=w := mul_inv_eq_iff_eq_mul.mpr (hnD w w.property).symm
  have hmul : (A ⊔ D).normalizerMonoidHom ⟨n,hnB⟩
      ⟨(v:G)*w,mul_mem_sup v.property w.property⟩ =
      ⟨((A.normalizerMonoidHom ⟨n,hnA⟩ v):G)*(w:G),
        mul_mem_sup (A.normalizerMonoidHom ⟨n,hnA⟩ v).property w.property⟩ := by
    apply Subtype.ext
    change n*((v:G)*w)*n⁻¹ = (n*(v:G)*n⁻¹)*w
    calc
      _ = (n*(v:G)*n⁻¹)*(n*(w:G)*n⁻¹) := by group
      _ = _ := by rw [hc]
  rw [hmul,e.apply_mul,he]
  change (a (A.normalizerMonoidHom ⟨n,hnA⟩ v), d w) =
    (a (A.normalizerMonoidHom ⟨n,hnA⟩ (a.symm (a v))), d w)
  rw [a.symm_apply_apply]

theorem ProductCoordinates.mem_left (x : (A ⊔ D : Subgroup G)) :
    (e.equiv x).2 = 1 ↔ (x:G) ∈ A := by
  constructor
  · intro hx
    obtain ⟨v,hv⟩ := a.surjective (e.equiv x).1
    have he : e.equiv (inclusion le_sup_left v) = e.equiv x := by
      rw [e.apply_left,hv]
      exact Prod.ext rfl hx.symm
    have he' := congrArg (fun z : (A ⊔ D : Subgroup G) => (z:G)) (e.equiv.injective he)
    exact he' ▸ v.property
  · intro hx
    exact congrArg Prod.snd (e.apply_left ⟨x,hx⟩)

theorem ProductCoordinates.mem_right (x : (A ⊔ D : Subgroup G)) :
    (e.equiv x).1 = 1 ↔ (x:G) ∈ D := by
  constructor
  · intro hx
    obtain ⟨v,hv⟩ := d.surjective (e.equiv x).2
    have he : e.equiv (inclusion le_sup_right v) = e.equiv x := by
      rw [e.apply_right,hv]
      exact Prod.ext hx.symm rfl
    have he' := congrArg (fun z : (A ⊔ D : Subgroup G) => (z:G)) (e.equiv.injective he)
    exact he' ▸ v.property
  · intro hx
    exact congrArg Prod.fst (e.apply_right ⟨x,hx⟩)
/-- Failure to preserve either coordinate factor is exactly failure to
normalize its original ambient subgroup. -/
theorem ProductCoordinates.left_map_eq_iff [Finite G] (n : normalizer ((A ⊔ D : Subgroup G) : Set G)) :
    ((⊤ : Subgroup X).prod (⊥ : Subgroup Y)).map
      (MulAut.congr e.equiv ((A ⊔ D).normalizerMonoidHom n)).toMonoidHom =
      (⊤ : Subgroup X).prod (⊥ : Subgroup Y) ↔
    (n:G) ∈ normalizer (A : Set G) := by
  let : Finite (X × Y) := Finite.of_equiv (A ⊔ D : Subgroup G) e.equiv.toEquiv
  let f := MulAut.congr e.equiv ((A ⊔ D).normalizerMonoidHom n)
  have heval (x : (A ⊔ D : Subgroup G)) :
      f (e.equiv x) = e.equiv ((A ⊔ D).normalizerMonoidHom n x) := by
    change e.equiv ((A ⊔ D).normalizerMonoidHom n (e.equiv.symm (e.equiv x))) = _
    rw [e.equiv.symm_apply_apply]
  constructor
  · intro h
    rw [mem_normalizer_iff_map_conj_eq]
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      have hp : e.equiv (inclusion le_sup_left (⟨x,hx⟩ : A)) ∈
          (⊤ : Subgroup X).prod (⊥ : Subgroup Y) := by
        exact ⟨mem_top _,(e.mem_left _).mpr hx⟩
      have hm := h.le (mem_map.mpr ⟨_,hp,rfl⟩)
      have hm := hm.2
      change (f (e.equiv (inclusion le_sup_left (⟨x,hx⟩ : A)))).2 = 1 at hm
      rw [heval] at hm
      exact (e.mem_left _).mp hm
    · rw [card_map_of_injective (MulAut.conj (n:G)).injective]
  · intro h
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      have hxA : (e.equiv.symm x:G) ∈ A := (e.mem_left _).mp (by
        rw [e.equiv.apply_symm_apply]
        exact hx.2)
      refine ⟨mem_top _,?_⟩
      change (f x).2=1
      rw [←e.equiv.apply_symm_apply x,heval]
      exact (e.mem_left _).mpr ((mem_normalizer_iff.mp h _).mp hxA)
    · rw [card_map_of_injective f.injective]

theorem ProductCoordinates.right_map_eq_iff [Finite G] (n : normalizer ((A ⊔ D : Subgroup G) : Set G)) :
    ((⊥ : Subgroup X).prod (⊤ : Subgroup Y)).map
      (MulAut.congr e.equiv ((A ⊔ D).normalizerMonoidHom n)).toMonoidHom =
      (⊥ : Subgroup X).prod (⊤ : Subgroup Y) ↔
    (n:G) ∈ normalizer (D : Set G) := by
  let : Finite (X × Y) := Finite.of_equiv (A ⊔ D : Subgroup G) e.equiv.toEquiv
  let f := MulAut.congr e.equiv ((A ⊔ D).normalizerMonoidHom n)
  have heval (x : (A ⊔ D : Subgroup G)) :
      f (e.equiv x) = e.equiv ((A ⊔ D).normalizerMonoidHom n x) := by
    change e.equiv ((A ⊔ D).normalizerMonoidHom n (e.equiv.symm (e.equiv x))) = _
    rw [e.equiv.symm_apply_apply]
  constructor
  · intro h
    rw [mem_normalizer_iff_map_conj_eq]
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      have hp : e.equiv (inclusion le_sup_right (⟨x,hx⟩ : D)) ∈
          (⊥ : Subgroup X).prod (⊤ : Subgroup Y) := by
        exact ⟨(e.mem_right _).mpr hx,mem_top _⟩
      have hm := h.le (mem_map.mpr ⟨_,hp,rfl⟩)
      have hm := hm.1
      change (f (e.equiv (inclusion le_sup_right (⟨x,hx⟩ : D)))).1 = 1 at hm
      rw [heval] at hm
      exact (e.mem_right _).mp hm
    · rw [card_map_of_injective (MulAut.conj (n:G)).injective]
  · intro h
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      have hxD : (e.equiv.symm x:G) ∈ D := (e.mem_right _).mp (by
        rw [e.equiv.apply_symm_apply]
        exact hx.1)
      refine ⟨?_,mem_top _⟩
      change (f x).1=1
      rw [←e.equiv.apply_symm_apply x,heval]
      exact (e.mem_right _).mpr ((mem_normalizer_iff.mp h _).mp hxD)
    · rw [card_map_of_injective f.injective]
end Subgroup.NormalizerAction
