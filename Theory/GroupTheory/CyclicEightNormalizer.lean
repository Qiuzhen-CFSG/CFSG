module
public import Theory.GroupTheory.PPrimeCorePGroupQuotient
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic

/-!
# Normalizers of cyclic subgroups of order eight

Suppose an involution x acts on an element f of order eight by f ↦ f⁵,
and f² is not conjugate to its inverse. Then the normalizer of ⟨f⟩ is
C(f)⟨x⟩, with C(f) of index two. If C(f)/O₂′(C(f)) has order eight,
the normalizer modulo its odd core has order sixteen, and that odd core
centralizes f.

Conjugation can send f only to an odd power. The nonreal square excludes
powers three and seven; multiplication by x reduces the remaining action
to the identity. The characteristic odd core of the index-two centralizer
is then a normal Hall odd subgroup of the normalizer.

Source: P. Fong, Some Sylow subgroups of order 32 and a characterization
of U(3,3), J. Algebra 6 (1967), printed p. 72, first paragraph.
-/

namespace Subgroup
variable {G : Type*} [Group G] (f x : G)
  (hf : orderOf f = 8) (hx : x ^ 2 = 1) (hxf : x * f * x⁻¹ = f ^ 5)

include hf in
private theorem fifth_fifth : (f ^ 5) ^ 5 = f := by
  rw [← pow_mul, ← pow_mod_orderOf, hf]
  norm_num

include hf hxf in
private theorem x_mem_normalizer : x ∈ normalizer (zpowers f : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change zpowers (x * f * x⁻¹) = zpowers f
  rw [hxf]
  apply le_antisymm
  · exact zpowers_le.mpr ((zpowers f).pow_mem (mem_zpowers f) 5)
  · apply zpowers_le.mpr
    have hm := (zpowers (f ^ 5)).pow_mem (mem_zpowers _) 5
    rwa [fifth_fifth f hf] at hm

include hf hxf in
private theorem x_not_centralizer : x ∉ centralizer ({f} : Set G) := by
  intro hc
  have he : f ^ 5 = f ^ 1 := by
    rw [pow_one, ← hxf]
    exact (mul_inv_eq_iff_eq_mul).mpr (mem_centralizer_singleton_iff.mp hc)
  have hh := pow_inj_mod.mp he
  norm_num [hf] at hh

private theorem centralizer_le_cyclic_normalizer :
    centralizer ({f} : Set G) ≤ normalizer (zpowers f : Set G) := by
  simpa only [zpowers_eq_closure, centralizer_closure] using
    centralizer_le_normalizer (zpowers f : Set G)

variable [Finite G] (hn : ¬ IsConj (f ^ 2) (f ^ 2)⁻¹)

include hf hn in
private theorem conjugate_eq_or_fifth {g : G}
    (hg : g ∈ normalizer (zpowers f : Set G)) :
    g * f * g⁻¹ = f ∨ g * f * g⁻¹ = f ^ 5 := by
  classical
  have hm := (mem_normalizer_iff.mp hg f).mp (mem_zpowers f)
  have hfin : IsOfFinOrder f := isOfFinOrder_of_finite f
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at hm
  obtain ⟨k, hk, he⟩ := hm
  have hk8 : k < 8 := by simpa only [Finset.mem_range, hf] using hk
  have hord : orderOf (f ^ k) = orderOf f := by
    rw [he]
    exact (MulAut.conj g).orderOf_eq f
  rw [orderOf_pow, hf] at hord
  have hs : IsConj (f ^ 2) ((f ^ k) ^ 2) :=
    (isConj_iff.mpr ⟨g, he.symm⟩).pow 2
  have hi (n : ℕ) (h : (n * 2 + 2) % 8 = 0) : (f ^ n) ^ 2 = (f ^ 2)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_mul, ← pow_add, ← pow_mod_orderOf, hf, h, pow_zero]
  interval_cases k
  all_goals norm_num at hord
  · exact Or.inl (by simpa using he.symm)
  · exact (hn (by simpa only [hi 3 (by decide)] using hs)).elim
  · exact Or.inr he.symm
  · exact (hn (by simpa only [hi 7 (by decide)] using hs)).elim

include hf hxf hn in
private theorem two_cosets {g : G} (hg : g ∈ normalizer (zpowers f : Set G)) :
    g ∈ centralizer ({f} : Set G) ∨ x * g ∈ centralizer ({f} : Set G) := by
  rcases conjugate_eq_or_fifth f hf hn hg with h | h
  · exact Or.inl (mem_centralizer_singleton_iff.mpr ((mul_inv_eq_iff_eq_mul).mp h))
  · right
    apply mem_centralizer_singleton_iff.mpr
    apply (mul_inv_eq_iff_eq_mul).mp
    calc
      (x * g) * f * (x * g)⁻¹ = x * (g * f * g⁻¹) * x⁻¹ := by group
      _ = x * f ^ 5 * x⁻¹ := by rw [h]
      _ = (x * f * x⁻¹) ^ 5 := map_pow (MulAut.conj x) f 5
      _ = (f ^ 5) ^ 5 := by rw [hxf]
      _ = f := fifth_fifth f hf

include hf hx hxf hn in
public theorem normalizer_zpowers_eq_centralizer_sup :
    normalizer (zpowers f : Set G) = centralizer ({f} : Set G) ⊔ zpowers x := by
  apply le_antisymm
  · intro g hg
    rcases two_cosets f x hf hxf hn hg with h | h
    · exact (show centralizer ({f} : Set G) ≤ _ from le_sup_left) h
    · have hxmem : x ∈ centralizer ({f} : Set G) ⊔ zpowers x := (show zpowers x ≤ _ from le_sup_right) (mem_zpowers x)
      have hh := (centralizer ({f} : Set G) ⊔ zpowers x).mul_mem hxmem ((show centralizer ({f} : Set G) ≤ _ from le_sup_left) h)
      have hs : x * x = 1 := by simpa only [pow_two] using hx
      simpa only [← mul_assoc, hs, one_mul] using hh
  · exact sup_le (centralizer_le_cyclic_normalizer f) (zpowers_le.mpr (x_mem_normalizer f x hf hxf))

include hf hxf hn in
public theorem centralizer_relIndex_normalizer_eq_two :
    (centralizer ({f} : Set G)).relIndex (normalizer (zpowers f : Set G)) = 2 := by
  apply relIndex_eq_two_iff_exists_notMem_and'.mpr
  exact ⟨x, x_mem_normalizer f x hf hxf, x_not_centralizer f x hf hxf,
    fun _ hg => (two_cosets f x hf hxf hn hg).symm⟩


include hf hxf hn in
public theorem normalizer_oddCore_contract
    (hC : Nat.card ((centralizer ({f} : Set G)) ⧸
      pPrimeCore 2 (centralizer ({f} : Set G))) = 8) :
    let H := normalizer (zpowers f : Set G)
    Nat.card (H ⧸ pPrimeCore 2 H) = 16 ∧
      pPrimeCore 2 H ≤ (centralizer ({f} : Set G)).subgroupOf H := by
  let H := normalizer (zpowers f : Set G)
  let C := (centralizer ({f} : Set G)).subgroupOf H
  have hidx : C.index = 2 := centralizer_relIndex_normalizer_eq_two f x hf hxf hn
  let : C.Normal := C.normal_of_index_eq_two hidx
  let e : C ≃* centralizer ({f} : Set G) :=
    subgroupOfEquivOfLe (centralizer_le_cyclic_normalizer f)
  let eqt := QuotientGroup.congr (pPrimeCore 2 C)
    (pPrimeCore 2 (centralizer ({f} : Set G))) e (pPrimeCore_map_iso 2 e)
  have hCidx : (pPrimeCore 2 C).index = 8 :=
    (Nat.card_congr eqt.toEquiv).trans hC
  let U := (pPrimeCore 2 C).map C.subtype
  have hUi : U.index = 16 := by
    rw [show U = (pPrimeCore 2 C).map C.subtype from rfl,
      index_map_subtype, hCidx, hidx]
  have hUc : Nat.Coprime 2 (Nat.card U) := by
    rw [show U = (pPrimeCore 2 C).map C.subtype from rfl,
      card_map_of_injective C.subtype_injective]
    exact pPrimeCore_coprime_card
  let : U.Normal := inferInstance
  have hUeq : U = pPrimeCore 2 H := by
    apply le_antisymm
    · exact le_sSup ⟨inferInstance, hUc⟩
    · apply pPrimeCore_le_of_isPGroup_quotient 2 U
      exact IsPGroup.of_card (n := 4) hUi
  constructor
  · change (pPrimeCore 2 H).index = 16
    rw [← hUeq]
    exact hUi
  · rw [← hUeq]
    exact map_subtype_le _

end Subgroup
