module
public import Theory.GroupTheory.QuaternionCentralProductNineAction.FactorSwap
public import Theory.GroupTheory.QuaternionCentralProductIndependentCubics
public import Mathlib.GroupTheory.IndexNormal

/-!
# Cardinalities and normality for the order-nine outer image

The stabilizer of either quaternion factor has index two when a factor swap
exists. In a quotient of order 36 its image has order 18. A subgroup of order
nine is normal in that image; Sylow counting then makes it normal in the whole
quotient. The image of an elementary sixteen meeting the kernel in order eight
is cyclic of order two.

Source: Aschbacher–Smith, §5.3.7, printed p.661 (PDF p.678).
-/

namespace Subgroup

/-- A factor interchange makes each intrinsic quaternion factor stabilizer
have index two in the ambient normalizer. -/
public theorem quaternion_factor_normalizer_index_two_of_swap
    {G : Type*} [Group G] [Finite G] (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hn : normalizer ((B ⊔ C : Subgroup G) : Set G) = ⊤)
    (s : G) (hBC : B.map (MulAut.conj s).toMonoidHom = C)
    (hCB : C.map (MulAut.conj s).toMonoidHom = B) :
    (normalizer (B : Set G)).index = 2 := by
  have hne : B ≠ C := by
    intro hh
    have hc : Nat.card B = 8 := by
      rw [Nat.card_congr hB.some.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [← hh, inf_idem, hc] at hinter
    omega
  apply index_eq_two_iff_exists_notMem_and'.mpr
  refine ⟨s, fun hs => hne ((mem_normalizer_iff_map_conj_eq.mp hs).symm.trans hBC), ?_⟩
  intro g
  have hg : (B ⊔ C).map (MulAut.conj g).toMonoidHom = B ⊔ C :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [hn]; trivial)
  have him := quaternion_subgroup_eq_factor B C
    (B.map (MulAut.conj g).toMonoidHom) hB hC hinter hcomm
    ⟨(B.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.trans hB.some⟩
    ((map_mono le_sup_left).trans_eq hg)
  rcases him with hBB | hBC'
  · exact Or.inr (mem_normalizer_iff_map_conj_eq.mpr hBB)
  · apply Or.inl
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hcomp : (MulAut.conj (s*g)).toMonoidHom =
        (MulAut.conj s).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
      ext x
      change (s*g)*x*(s*g)⁻¹ = s*(g*x*g⁻¹)*s⁻¹
      group
    change B.map (MulAut.conj (s*g)).toMonoidHom = B
    rw [hcomp, ← map_map, hBC', hCB]

/-- In order 36, a subgroup of order nine contained in an index-two subgroup
is normal in the whole group. -/
public theorem normal_nine_of_le_index_two_in_order_thirty_six
    {K : Type*} [Group K] [Finite K] (hK : Nat.card K = 36)
    (E N : Subgroup K) (hE : Nat.card E = 9) (hN : N.index = 2)
    (hle : E ≤ N) : E.Normal := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNc : Nat.card N = 18 := by
    have h := N.card_mul_index
    rw [hN, hK] at h
    omega
  have hEc : Nat.card (E.subgroupOf N) = 9 :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans hE
  have hEi : (E.subgroupOf N).index = 2 := by
    have h := (E.subgroupOf N).card_mul_index
    rw [hNc, hEc] at h
    omega
  have hnorm : N ≤ normalizer (E : Set K) :=
    (normal_subgroupOf_iff_le_normalizer hle).mp (normal_of_index_eq_two hEi)
  let P : Sylow 3 K := Sylow.ofCard E (by rw [hE, hK]; decide +kernel)
  have hcount : Nat.card (Sylow 3 K) ≤ 2 := by
    rw [Sylow.card_eq_index_normalizer P]
    change (normalizer (E : Set K)).index ≤ 2
    exact Nat.le_of_dvd (by decide) (hN ▸ index_dvd_of_le hnorm)
  have hmod := card_sylow_modEq_one 3 K
  have hone : Nat.card (Sylow 3 K) = 1 := by
    change Nat.card (Sylow 3 K) % 3 = 1 % 3 at hmod
    omega
  let : Subsingleton (Sylow 3 K) := (Nat.card_eq_one_iff_unique.mp hone).1
  exact P.normal_of_subsingleton

/-- Restricting a quotient map with kernel of order 32 to an order-nine
subgroup is injective. -/
public theorem injective_nine_restriction_of_kernel_thirty_two
    {G K : Type*} [Group G] [Finite G] [Group K]
    (A : Subgroup G) (hA : Nat.card A = 9)
    (f : G →* K) (hker : Nat.card f.ker = 32) :
    Function.Injective (f.comp A.subtype) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  have ha9 : (a : G) ^ 9 = 1 := by
    have h := pow_card_eq_one' (x := a)
    rw [hA] at h
    exact congrArg Subtype.val h
  have ha32 : (a : G) ^ 32 = 1 := by
    have h := pow_card_eq_one' (x := (⟨a, ha⟩ : f.ker))
    rw [hker] at h
    exact congrArg Subtype.val h
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha9) (orderOf_dvd_of_pow_eq_one ha32)
  exact Subtype.ext (orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by simpa using hd)))

/-- The image has order two when a subgroup of order sixteen meets the
kernel in a subgroup of order eight. -/
public theorem card_image_two_of_sixteen_inf_kernel_eight
    {G K : Type*} [Group G] [Finite G] [Group K]
    (V : Subgroup G) (f : G →* K) (hV : Nat.card V = 16)
    (hinter : Nat.card (V ⊓ f.ker : Subgroup G) = 8) :
    Nat.card (V.map f) = 2 := by
  let g := f.comp V.subtype
  let e : g.ker ≃* (V ⊓ f.ker : Subgroup G) := {
    toFun := fun x => ⟨x.val, x.val.property, x.property⟩
    invFun := fun x => ⟨⟨x, x.property.1⟩, x.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  have hk : Nat.card g.ker = 8 := (Nat.card_congr e.toEquiv).trans hinter
  have hr : g.range = V.map f := by rw [MonoidHom.range_comp, V.range_subtype]
  have h := g.ker.card_mul_index
  rw [index_ker, hk, hr, hV] at h
  omega

/-- Any nonidentity image generates a subgroup image of order two. -/
public theorem image_eq_zpowers_of_card_two
    {G K : Type*} [Group G] [Group K] (V : Subgroup G) (f : G →* K)
    (hcard : Nat.card (V.map f) = 2) (s : G) (hs : s ∈ V) (hne : f s ≠ 1) :
    V.map f = zpowers (f s) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · intro x hx
    let t : V.map f := ⟨f s, mem_map_of_mem f hs⟩
    have ht : t ≠ 1 := fun h => hne (congrArg Subtype.val h)
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp
      (mem_zpowers_of_prime_card hcard ht (g' := (⟨x, hx⟩ : V.map f)))
    exact mem_zpowers_iff.mpr ⟨n, congrArg Subtype.val hn⟩
  · exact zpowers_le.mpr (mem_map_of_mem f hs)

end Subgroup
