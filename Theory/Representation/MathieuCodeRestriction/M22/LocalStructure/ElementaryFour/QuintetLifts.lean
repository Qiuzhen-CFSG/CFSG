module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.ElementaryFour.Quotient
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Involution lifts and centralizers over an elementary kernel

In an extension with elementary abelian two-kernel, two involutory lifts of
one quotient element differ by an element of its kernel centralizer. This
identifies lifts inside an elementary subgroup when that subgroup contains
the kernel centralizer. For an order-two image, a cardinality comparison
constructs the supplement using a specified involution. An intertwiner then
identifies the actual restricted fixed space, without assuming its dimension.

These are the group and linear-algebra steps of Aschbacher--Smith H.15.5,
combined manuscript (1 March 2004), printed p.401.
-/

@[expose] public section

open Representation.BinaryOffender
namespace MathieuCode.M22ElementaryFour.QuintetLifts
variable {G D : Type*} [Group G] [Group D]

abbrev kernelCentralizer (q : G →* D) (a : G) : Subgroup G :=
  q.ker ⊓ Subgroup.centralizer ({a} : Set G)

theorem commute_of_mem_elementary (Q : Subgroup G) [IsElementaryAbelian 2 Q]
    {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) : Commute a b :=
  congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Q) ⟨b, hb⟩)

theorem intersection_le_kernelCentralizer (q : G →* D) (Q : Subgroup G)
    [IsElementaryAbelian 2 Q] {a : G} (ha : a ∈ Q) :
    Q ⊓ q.ker ≤ kernelCentralizer q a := by
  intro b hb
  exact ⟨hb.2, Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_of_mem_elementary Q hb.1 ha).eq⟩

theorem kernelCentralizer_card_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (q : G →* D) (ρ : Representation (ZMod 2) D V) (e : q.ker ≃ V)
    (he : ∀ (a : G) (k : q.ker), Commute a k.val → ρ (q a) (e k) = e k)
    [Finite V] (a : G) :
    Nat.card (kernelCentralizer q a) ≤ Nat.card (fixedSpace ρ (Subgroup.zpowers (q a))) := by
  let f : kernelCentralizer q a → fixedSpace ρ (Subgroup.zpowers (q a)) :=
    fun k => ⟨e ⟨k.val, k.property.1⟩, (mem_fixedSpace_zpowers_iff _ _ _).mpr
      (he a ⟨k.val, k.property.1⟩
        (Subgroup.mem_centralizer_singleton_iff.mp k.property.2).symm)⟩
  apply Nat.card_le_card_of_injective f
  intro x y h
  apply Subtype.ext
  exact congrArg (fun k : q.ker => (k : G)) (e.injective (congrArg Subtype.val h))

theorem kernelCentralizer_le_of_card [Finite G] (q : G →* D) (Q : Subgroup G)
    [IsElementaryAbelian 2 Q] {a : G} (ha : a ∈ Q)
    (hc : Nat.card (kernelCentralizer q a) ≤ Nat.card (Q ⊓ q.ker : Subgroup G)) :
    kernelCentralizer q a ≤ Q := by
  have he := Subgroup.eq_of_le_of_card_ge (intersection_le_kernelCentralizer q Q ha) hc
  exact he ▸ inf_le_left

theorem involution_difference_mem_kernelCentralizer (q : G →* D)
    [IsElementaryAbelian 2 q.ker] {a x : G}
    (ha : a ^ 2 = 1) (hx : x ^ 2 = 1) (he : q a = q x) :
    a * x⁻¹ ∈ kernelCentralizer q x := by
  have hk : a * x⁻¹ ∈ q.ker := by simp [MonoidHom.mem_ker, he]
  have hk2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (a * x⁻¹) hk
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hx)
  have hki : (a * x⁻¹)⁻¹ = a * x⁻¹ :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hk2)
  refine ⟨hk, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have hax : x * a = a * x := by simpa [hai, hxi] using hki
  simp only [hxi]
  calc
    a * x * x = a := by rw [mul_assoc, ← pow_two, hx, mul_one]
    _ = x * (a * x) := by rw [← hax, ← mul_assoc, ← pow_two, hx, one_mul]

theorem involution_mem_of_same_image (q : G →* D) (Q : Subgroup G)
    [IsElementaryAbelian 2 q.ker] [IsElementaryAbelian 2 Q] {a x : G}
    (ha : a ^ 2 = 1) (hx : x ∈ Q) (he : q a = q x)
    (hc : kernelCentralizer q x ≤ Q) : a ∈ Q := by
  have hk := hc (involution_difference_mem_kernelCentralizer q ha
    (elemPow_eq_one_of_isElementaryAbelian x hx) he)
  simpa using Q.mul_mem hk hx

theorem centralizer_in_preimage_le (q : G →* D) (Q : Subgroup G)
    [IsElementaryAbelian 2 Q] {a : G} (ha : a ∈ Q)
    (hc : kernelCentralizer q a ≤ Q) :
    (Q.map q).comap q ⊓ Subgroup.centralizer ({a} : Set G) ≤ Q := by
  intro b hb
  obtain ⟨x, hx, he⟩ := hb.1
  have hk : b * x⁻¹ ∈ kernelCentralizer q a := by
    refine ⟨by simp [he], ?_⟩
    have hba : Commute b a := Subgroup.mem_centralizer_singleton_iff.mp hb.2
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (hba.mul_left (commute_of_mem_elementary Q (Q.inv_mem hx) ha)).eq
  simpa using Q.mul_mem (hc hk) hx

theorem supplement_of_image_card_two (q : G →* D) (A : Subgroup G)
    (hc : Nat.card (A.map q) = 2) {a : G} (ha : a ∈ A) (hne : q a ≠ 1) :
    A = (A ⊓ q.ker) ⊔ Subgroup.zpowers a := by
  obtain ⟨s, hs, hu⟩ := (Nat.card_eq_two_iff' (1 : A.map q)).mp hc
  have huniq {b c : A.map q} (hb : b ≠ 1) (hc : c ≠ 1) : b = c :=
    (hu b hb).trans (hu c hc).symm
  apply le_antisymm
  · intro b hb
    by_cases hb1 : q b = 1
    · exact (le_sup_left : A ⊓ q.ker ≤ (A ⊓ q.ker) ⊔ Subgroup.zpowers a) ⟨hb, hb1⟩
    · have hba : q b = q a := congrArg Subtype.val
        (huniq (b := ⟨q b, Subgroup.mem_map_of_mem q hb⟩)
          (c := ⟨q a, Subgroup.mem_map_of_mem q ha⟩)
          (fun h => hb1 (congrArg Subtype.val h))
          (fun h => hne (congrArg Subtype.val h)))
      have hk : b * a⁻¹ ∈ A ⊓ q.ker :=
        ⟨A.mul_mem hb (A.inv_mem ha), by simp [hba]⟩
      simpa using ((A ⊓ q.ker) ⊔ Subgroup.zpowers a).mul_mem
        ((le_sup_left : A ⊓ q.ker ≤ (A ⊓ q.ker) ⊔ Subgroup.zpowers a) hk)
        ((le_sup_right : Subgroup.zpowers a ≤ (A ⊓ q.ker) ⊔ Subgroup.zpowers a) (Subgroup.mem_zpowers a))
  · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr ha)

theorem elementary_kernel_of_coordinates {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (q : G →* D) (e : q.ker ≃ V) (hm : ∀ a b, e (a * b) = e a + e b) :
    IsElementaryAbelian 2 q.ker := by
  have h0 : e 1 = 0 := by
    have h := hm 1 1
    simpa only [one_mul, left_eq_add] using h
  refine {
    toIsMulCommutative := ⟨⟨?_⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  · intro a b
    apply e.injective
    rw [hm, hm, add_comm]
  · intro a
    apply e.injective
    rw [pow_two, hm, h0, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]

theorem supplement_at_involution [Finite G] (q : G →* D) (A : Subgroup G)
    [IsElementaryAbelian 2 q.ker] [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 16) (himage : Nat.card (A.map q) = 2)
    (x : G) (hx : x ^ 2 = 1) (hximage : q x ∈ A.map q) (hx1 : q x ≠ 1)
    (hcentral : Nat.card (kernelCentralizer q x) ≤ 8) :
    x ∈ A ∧ A = (A ⊓ q.ker) ⊔ Subgroup.zpowers x := by
  obtain ⟨a, ha, hax⟩ := hximage
  have hdiff : a * x⁻¹ ∈ q.ker := by simp [hax]
  have hle : A ⊓ q.ker ≤ kernelCentralizer q x := by
    intro b hb
    refine ⟨hb.2, ?_⟩
    have hba := commute_of_mem_elementary A hb.1 ha
    have hbd := commute_of_mem_elementary q.ker hb.2 hdiff
    have hh := hbd.inv_right.mul_right hba
    have he : (a * x⁻¹)⁻¹ * a = x := by group
    rw [he] at hh
    exact Subgroup.mem_centralizer_singleton_iff.mpr hh.eq
  have hc := card_intersection_of_card_image_two q A hcard himage
  have heq : A ⊓ q.ker = kernelCentralizer q x :=
    Subgroup.eq_of_le_of_card_ge hle (by omega)
  have hd : a * x⁻¹ ∈ A ⊓ q.ker := heq ▸
    involution_difference_mem_kernelCentralizer q
      (elemPow_eq_one_of_isElementaryAbelian a ha) hx hax
  have hxA : x ∈ A := by
    have hh := A.mul_mem (A.inv_mem hd.1) ha
    have he : (a * x⁻¹)⁻¹ * a = x := by group
    rwa [he] at hh
  exact ⟨hxA, supplement_of_image_card_two q A himage hxA hx1⟩

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]
  [Module (ZMod 2) V] [Module (ZMod 2) W]

/-- An actual intertwiner identifies the fixed space inside a subspace. -/
def restrictedFixedEquiv (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) D W) (U : Submodule (ZMod 2) V)
    (i : G) (s : D) (e : U ≃ₗ[ZMod 2] W)
    (he : ∀ w, ρ i (e.symm w : V) = (e.symm (σ s w) : V)) :
    (U ⊓ fixedSpace ρ (Subgroup.zpowers i) : Submodule (ZMod 2) V) ≃ₗ[ZMod 2]
      fixedSpace σ (Subgroup.zpowers s) where
  toFun v := ⟨e ⟨v.val, v.property.1⟩, by
    apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
    apply e.symm.injective
    apply Subtype.ext
    rw [← he]
    simpa using (mem_fixedSpace_zpowers_iff ρ i v.val).mp v.property.2⟩
  invFun w := ⟨e.symm w.val, (e.symm w.val).property, by
    apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
    rw [he, (mem_fixedSpace_zpowers_iff σ s w.val).mp w.property]⟩
  left_inv v := by apply Subtype.ext; simp
  right_inv w := by apply Subtype.ext; simp
  map_add' v w := by
    apply Subtype.ext
    exact e.map_add (⟨v.val, v.property.1⟩ : U) (⟨w.val, w.property.1⟩ : U)
  map_smul' c v := by
    apply Subtype.ext
    exact e.map_smul c (⟨v.val, v.property.1⟩ : U)

/-- Conjugation preserves the codimension of the actual span of element
fixed spaces, for any value of that codimension. -/
theorem fixedSpaceSpan_codim_conj (ρ : Representation (ZMod 2) G V)
    (A : Subgroup G) (g : G) :
    Module.finrank (ZMod 2) (V ⧸ fixedSpaceSpan ρ A) =
      Module.finrank (ZMod 2) (V ⧸ fixedSpaceSpan ρ (A.map (MulAut.conj g).toMonoidHom)) := by
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)
  apply fixedSpaceSpan_codim_map_equivariant ρ ρ (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective e
  intro a v
  change ρ g (ρ a v) = ρ (g * a * g⁻¹) (ρ g v)
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

end MathieuCode.M22ElementaryFour.QuintetLifts
