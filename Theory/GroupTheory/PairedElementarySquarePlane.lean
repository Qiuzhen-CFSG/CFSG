module

public import Theory.GroupTheory.PairedElementarySupports
public import Theory.GroupAction.MaximalCosetOrbit
public import Theory.ElementaryAbelian.Basic
public import Theory.ElementaryAbelian.Injective
public import Mathlib.Tactic.Group

/-!
# Squares on the distinguished plane of a paired elementary product

The two index-two denominators commute into different point lines. A
commutator between elements outside both denominators cannot lie in their
plane: otherwise relative generation would put every cross commutator in
that plane. Consequently the squares in the plane lie in the two point
lines. This is intrinsic to the product, without choosing coordinate bases.
-/

namespace Subgroup
open scoped commutatorElement IsMulCommutative Pointwise

private theorem involution_zpowers_cases {G : Type*} [Group G] [Finite G]
    {x y : G} (hx : x ^ 2 = 1) (hy : y ∈ zpowers x) : y = 1 ∨ y = x := by
  classical
  by_cases hx1 : x = 1
  · simpa only [hx1, zpowers_one_eq_bot, mem_bot] using Or.inl hy
  have ho : orderOf x = 2 := orderOf_eq_prime hx hx1
  rw [mem_zpowers_iff_mem_range_orderOf, ho] at hy
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
  have hn' : n < 2 := Finset.mem_range.mp hn
  interval_cases n <;> simp

private theorem commutator_involutions_le {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) {u v : G} (hu : u ^ 2 = 1) (hv : v ^ 2 = 1)
    (hcomm : ⁅u,v⁆ ∈ A) : ⁅zpowers u,zpowers v⁆ ≤ A := by
  apply commutator_le.mpr
  intro x hx y hy
  rcases involution_zpowers_cases hu hx with rfl | rfl <;>
    rcases involution_zpowers_cases hv hy with rfl | rfl
  all_goals simp_all

/-- A cross commutator outside both index-two denominators escapes the plane. -/
public theorem paired_outer_commutator_not_mem
    {G : Type*} [Group G] [Finite G]
    (U V E F A : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
    (hEU : E ≤ U) (hFV : F ≤ V)
    (hEi : E.relIndex U = 2) (hFi : F.relIndex V = 2)
    (hAU : A ≤ U) (hAV : A ≤ V)
    (hEV : ⁅E,V⁆ ≤ A) (hUF : ⁅U,F⁆ ≤ A) (hnot : ¬ ⁅U,V⁆ ≤ A)
    (u v : G) (hu : u ∈ U) (huE : u ∉ E) (hv : v ∈ V) (hvF : v ∉ F) :
    ⁅u,v⁆ ∉ A := by
  intro hc
  have hNU : U ⊔ V ≤ normalizer (A : Set G) := by
    apply sup_le
    · exact ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (centralizer_le hAU)).trans (centralizer_le_normalizer _)
    · exact ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (centralizer_le hAV)).trans (centralizer_le_normalizer _)
  have huU : zpowers u ≤ U := zpowers_le.mpr hu
  have hvV : zpowers v ≤ V := zpowers_le.mpr hv
  have hgenU := sup_zpowers_eq_of_relIndex_prime hEU Nat.prime_two hEi hu huE
  have hgenV := sup_zpowers_eq_of_relIndex_prime hFV Nat.prime_two hFi hv hvF
  have huv : ⁅zpowers u,zpowers v⁆ ≤ A := commutator_involutions_le A
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hu)
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hv) hc
  have huf : ⁅zpowers u,F⁆ ≤ A := (commutator_mono huU le_rfl).trans hUF
  have huV : ⁅zpowers u,V⁆ ≤ A := by
    rw [commutator_comm, ← hgenV]
    apply commutator_sup_le_of_relative_normal (U ⊔ V) F (zpowers v) (zpowers u) A
      hNU (hFV.trans le_sup_right) (hvV.trans le_sup_right)
    · rwa [commutator_comm]
    · rwa [commutator_comm]
  apply hnot
  rw [← hgenU]
  exact commutator_sup_le_of_relative_normal (U ⊔ V) E (zpowers u) V A
    hNU (hEU.trans le_sup_left) (huU.trans le_sup_left) hEV huV

/-- Every square in the distinguished plane lies on one of its two point lines. -/
public theorem square_mem_point_union_of_paired_denominators
    {G : Type*} [Group G] [Finite G]
    (U V E F Z Z' : Subgroup G)
    [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
    (hVU : V ≤ normalizer (U : Set G))
    (hEU : E ≤ U) (hFV : F ≤ V)
    (hEi : E.relIndex U = 2) (hFi : F.relIndex V = 2)
    (hAU : Z ⊔ Z' ≤ U) (hAV : Z ⊔ Z' ≤ V)
    (hEV : ⁅E,V⁆ ≤ Z') (hUF : ⁅U,F⁆ ≤ Z)
    (hnot : ¬ ⁅U,V⁆ ≤ Z ⊔ Z')
    (x : G) (hx : x ∈ U ⊔ V) (hxs : x ^ 2 ∈ Z ⊔ Z') :
    x ^ 2 ∈ Z ∨ x ^ 2 ∈ Z' := by
  have hxprod : x ∈ (U : Set G) * (V : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left U V hVU]
    exact hx
  obtain ⟨u,hu,v,hv,rfl⟩ := hxprod
  have hs : (u*v)^2 = ⁅u,v⁆ := by
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right
      (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hu)
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right
      (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hv)
    simp only [pow_two,commutatorElement_def,hui,hvi,mul_assoc]
  rw [hs] at hxs ⊢
  by_cases huE : u ∈ E
  · exact Or.inr (hEV (commutator_mem_commutator huE hv))
  by_cases hvF : v ∈ F
  · exact Or.inl (hUF (commutator_mem_commutator hu hvF))
  exact (paired_outer_commutator_not_mem U V E F (Z ⊔ Z') hEU hFV hEi hFi
    hAU hAV (hEV.trans le_sup_right) (hUF.trans le_sup_left) hnot u v hu huE hv hvF hxs).elim

private theorem point_commutator_square
    {G : Type*} [Group G] [Finite G]
    (U V Z : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
    (hcomm : ⁅U,V⁆ = Z) (hZ : Nat.card Z = 2) (z : G) (hz : z ∈ Z) :
    ∃ x ∈ U ⊔ V, x ^ 2 = z := by
  classical
  by_cases hz1 : z = 1
  · exact ⟨1, one_mem _, by simp [hz1]⟩
  have hex : ∃ u ∈ U, ∃ v ∈ V, ⁅u,v⁆ ≠ 1 := by
    by_contra! hall
    have hh : ⁅U,V⁆ = ⊥ := by
      apply bot_unique
      exact commutator_le.mpr (fun u hu v hv => mem_bot.mpr (hall u hu v hv))
    rw [hcomm] at hh
    rw [hh,card_bot] at hZ
    omega
  obtain ⟨u,hu,v,hv,hne⟩ := hex
  have hc : ⁅u,v⁆ ∈ Z := hcomm ▸ commutator_mem_commutator hu hv
  obtain ⟨t,_,ht⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
  have he : ⁅u,v⁆ = z := by
    have hc1 : (⟨⁅u,v⁆,hc⟩ : Z) ≠ 1 := fun hh => hne (congrArg Subtype.val hh)
    have hz1' : (⟨z,hz⟩ : Z) ≠ 1 := fun hh => hz1 (congrArg Subtype.val hh)
    exact congrArg Subtype.val ((ht _ hc1).trans (ht _ hz1').symm)
  refine ⟨u*v, (U ⊔ V).mul_mem (mem_sup_left hu) (mem_sup_right hv), ?_⟩
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hu)
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hv)
  simpa only [commutatorElement_def,hui,hvi,pow_two,mul_assoc] using he

/-- The two actual commutator points give exactly the squares on their plane. -/
public theorem paired_square_plane_iff
    {G : Type*} [Group G] [Finite G]
    (U V E F Z Z' : Subgroup G)
    [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
    (hVU : V ≤ normalizer (U : Set G))
    (hEU : E ≤ U) (hFV : F ≤ V)
    (hEi : E.relIndex U = 2) (hFi : F.relIndex V = 2)
    (hAU : Z ⊔ Z' ≤ U) (hAV : Z ⊔ Z' ≤ V)
    (hEV : ⁅E,V⁆ = Z') (hUF : ⁅U,F⁆ = Z)
    (hZ : Nat.card Z = 2) (hZ' : Nat.card Z' = 2)
    (hnot : ¬ ⁅U,V⁆ ≤ Z ⊔ Z') (z : G) (hz : z ∈ Z ⊔ Z') :
    (∃ x ∈ U ⊔ V, x ^ 2 = z) ↔ z ∈ Z ∨ z ∈ Z' := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact square_mem_point_union_of_paired_denominators U V E F Z Z' hVU hEU hFV
      hEi hFi hAU hAV hEV.le hUF.le hnot x hx hz
  · intro hz
    let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective
      (inclusion hEU) (inclusion_injective hEU)
    let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_injective
      (inclusion hFV) (inclusion_injective hFV)
    rcases hz with hz | hz
    · obtain ⟨x,hx,hx2⟩ := point_commutator_square U F Z hUF hZ z hz
      exact ⟨x,(sup_le_sup_left hFV U) hx,hx2⟩
    · obtain ⟨x,hx,hx2⟩ := point_commutator_square E V Z' hEV hZ' z hz
      exact ⟨x,(sup_le_sup_right hEU V) hx,hx2⟩

/-- Any automorphism preserving the product and its distinguished plane
preserves the union of the two point lines. Preservation of the individual
elementary factors is not required. -/
public theorem paired_square_plane_automorphism
    {G : Type*} [Group G]
    (P Z Z' : Subgroup G)
    (hsquare : ∀ z ∈ Z ⊔ Z',
      (∃ x ∈ P, x ^ 2 = z) ↔ z ∈ Z ∨ z ∈ Z')
    (a : MulAut G) (hP : P.map a.toMonoidHom = P)
    (hA : (Z ⊔ Z').map a.toMonoidHom = Z ⊔ Z')
    (z : G) (hz : z ∈ Z ∨ z ∈ Z') : a z ∈ Z ∨ a z ∈ Z' := by
  have hzA : z ∈ Z ⊔ Z' := hz.elim mem_sup_left mem_sup_right
  have hazA : a z ∈ Z ⊔ Z' := hA ▸ mem_map_of_mem a.toMonoidHom hzA
  obtain ⟨x,hx,hxz⟩ := (hsquare z hzA).mpr hz
  apply (hsquare (a z) hazA).mp
  exact ⟨a x,hP ▸ mem_map_of_mem a.toMonoidHom hx,by rw [← map_pow,hxz]⟩

end Subgroup
