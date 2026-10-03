module
public import ABG.ChapterII.Section1.OrderFourClasses
public import ABG.ChapterII.Section1.QuaternionRepresentative

/-!
# Quaternion subgroups of a quasi-dihedral group

Every quaternion subgroup of order eight is conjugate to the subgroup generated
by the quarter-order rotation and the first odd outer element. The representative
contains its centralizer and has index two in its normalizer; these local
properties are imported from the explicit representative calculation.

For conjugacy, take images of the two standard quaternion generators. Both
and their product have order four, and the generators do not commute. Ambient
normal forms therefore yield a cyclic element of order four and an outer
element of order four in the subgroup. The cyclic classification supplies
the quarter-order rotation, while the outer conjugacy calculation supplies
a conjugate of the canonical outer generator. Conjugates of the rotation
remain in its cyclic subgroup, so inclusion and cardinality eight identify
the two subgroups.

This is the quaternion branch of ABG Chapter II, §1, Lemma 1(ii), article
page 9 in `refs/latex/alperin-brauer-gorenstein.tex`. The SmallSubgroups
assembly transfers the representative's local properties to every quaternion
subgroup and identifies the ambient centralizer with its embedded center.
-/

namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]
private theorem quaternion_pair (T : Subgroup G) (e : T ≃* QuaternionGroup 2) :
    ∃ x y : G, x ∈ T ∧ y ∈ T ∧ orderOf x = 4 ∧ orderOf y = 4 ∧
      orderOf (x*y) = 4 ∧ ¬ Commute x y := by
  let f := T.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := T.subtype_injective.comp e.symm.injective
  refine ⟨f (QuaternionGroup.a 1), f (QuaternionGroup.xa 0), (e.symm _).property, (e.symm _).property, ?_, ?_, ?_, ?_⟩
  · rw [orderOf_injective f hf, QuaternionGroup.orderOf_a_one]
  · rw [orderOf_injective f hf, QuaternionGroup.orderOf_xa]
  · rw [← map_mul, orderOf_injective f hf, QuaternionGroup.a_mul_xa, QuaternionGroup.orderOf_xa]
  · intro h
    have hh : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
        QuaternionGroup.xa 0 * QuaternionGroup.a 1 := hf (by simpa only [map_mul] using h.eq)
    have hn : ¬ ((QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
        QuaternionGroup.xa 0 * QuaternionGroup.a 1) := by decide
    exact hn hh

private theorem quaternion_has_cyclic_outer (T : Subgroup G) (e : T ≃* QuaternionGroup 2)
    (a b : G) (k : ℕ) (hb : b^2=1) (hconj : b*a*b⁻¹=a^k)
    (hnf : ∀ x:G, ∃ i:ℕ, x=a^i ∨ x=a^i*b) :
    ∃ i j : ℕ, a^i ∈ T ∧ a^j*b ∈ T ∧ orderOf (a^i)=4 ∧ orderOf (a^j*b)=4 := by
  obtain ⟨x,y,hx,hy,hx4,hy4,hxy4,hnc⟩ := quaternion_pair T e
  obtain ⟨i,rfl|rfl⟩ := hnf x <;> obtain ⟨j,rfl|rfl⟩ := hnf y
  · exact False.elim (hnc (Commute.pow_pow_self a i j))
  · exact ⟨i,j,hx,hy,hx4,hy4⟩
  · exact ⟨j,i,hy,hx,hy4,hx4⟩
  · have hm : (a^i*b)*(a^j*b)=a^(i+k*j) := by
      rw [mul_assoc, ← mul_assoc b, move_pow a b k hconj j]
      simpa only [mul_assoc, ← pow_two, hb, mul_one] using (pow_add a i (k*j)).symm
    exact ⟨i+k*j,i,hm ▸ T.mul_mem hx hy,hx,hm ▸ hxy4,hx4⟩

private theorem conjugate_power_mem (a b : G) (k q : ℕ)
    (hconj : b*a*b⁻¹=a^k)
    (hnf : ∀ x:G, ∃ i:ℕ, x=a^i ∨ x=a^i*b) (g:G) :
    g*a^q*g⁻¹ ∈ Subgroup.zpowers (a^q) := by
  obtain ⟨i,rfl|rfl⟩ := hnf g
  · have he : a^i*a^q*(a^i)⁻¹=a^q := by
      rw [(Commute.pow_pow_self a i q).eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [he]; exact Subgroup.mem_zpowers _
  · have he : (a^i*b)*a^q*(a^i*b)⁻¹=(a^q)^k := by
      have hh := congrArg (fun x:G => x^q) hconj
      rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply] at hh
      calc
        _ = a^i*(b*a^q*b⁻¹)*(a^i)⁻¹ := by group
        _ = a^i*(a^k)^q*(a^i)⁻¹ := by rw [hh]
        _ = (a^q)^k := by
          rw [← pow_mul, (Commute.pow_pow_self a i (k*q)).eq, mul_assoc,
            mul_inv_cancel, mul_one, Nat.mul_comm k q, pow_mul]
    rw [he]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

private theorem quaternion_conjugacy_of_local {n : ℕ} (hn : 4≤n) (a b : G)
    (ha : orderOf a=2^(n-1)) (hb : orderOf b=2)
    (hconj : b*a*b⁻¹=a^(2^(n-2)-1))
    (hnf : ∀ x:G, ∃ i:ℕ, i<2^(n-1) ∧ (x=a^i ∨ x=a^i*b))
    (hU : Nat.card (Subgroup.closure ({a^(2^(n-3)),a*b}:Set G))=8)
    (T : Subgroup G) (e:T ≃* QuaternionGroup 2) :
    ∃ g:G, (Subgroup.closure ({a^(2^(n-3)),a*b}:Set G)).map (MulAut.conj g).toMonoidHom=T := by
  have he : 2^(n-1)=4*2^(n-3) := by
    rw [show n-1=n-3+2 by omega, pow_add]
    ring
  have hcyc (i:ℕ) (hi:i<2^(n-1)) (hi4:orderOf (a^i)=4) :
      a^i=a^(2^(n-3)) ∨ a^i=(a^(2^(n-3)))⁻¹ := by
    exact cyclic_order_four_eq_or_inv a (2^(n-3)) i (by positivity)
      (ha.trans he) (he ▸ hi) hi4
  have hout (j:ℕ) (hj:orderOf (a^j*b)=4) : IsConj (a^j*b) (a*b) := by
    apply outer_order_four_isConj a b (2^(n-2)) j
    · rw [ha, show n-1=n-2+1 by omega, pow_succ, Nat.mul_comm]
    · exact outer_square hn a b hb hconj
    · exact outer_even_shift_isConj hn a b ha hconj
    · exact hj
  have hnf' (x:G) : ∃ i:ℕ, x=a^i ∨ x=a^i*b := by
    obtain ⟨i,_,hi⟩ := hnf x
    exact ⟨i,hi⟩
  obtain ⟨i,j,hi,hj,hi4,hj4⟩ := quaternion_has_cyclic_outer T e a b _
    (by rw [← hb]; exact pow_orderOf_eq_one _) hconj hnf'
  have hc : a^(2^(n-3)) ∈ T := by
    have hp : a^(i % orderOf a)=a^i := pow_mod_orderOf a i
    have hi' : i % orderOf a < 2^(n-1) := by rw [ha]; exact Nat.mod_lt _ (by positivity)
    rcases hcyc (i % orderOf a) hi' (hp.symm ▸ hi4) with hh|hh
    · exact hh ▸ (hp.symm ▸ hi)
    · have ht : (a^(2^(n-3)))⁻¹ ∈ T := hh ▸ (hp.symm ▸ hi)
      simpa only [inv_inv] using T.inv_mem ht
  let : Finite T := Finite.of_equiv (QuaternionGroup 2) e.symm.toEquiv
  obtain ⟨g,hg⟩ := isConj_iff.mp (hout j hj4).symm
  refine ⟨g, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · apply (Subgroup.map_le_iff_le_comap).mpr
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl|hx
    · change g*a^(2^(n-3))*g⁻¹ ∈ T
      exact (Subgroup.zpowers_le.mpr hc) (conjugate_power_mem a b _ _ hconj hnf' g)
    · have hx' : x=a*b := Set.mem_singleton_iff.mp hx
      subst x
      change g*(a*b)*g⁻¹ ∈ T
      rwa [hg]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hU]
    have ht : Nat.card T=8 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    omega
end ABG.QuasiDihedral

namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]
/-- The single quaternion subgroup class, with representative centralizer and normalizer
properties (ABG II.1.1(ii)). -/
public theorem quaternion_subgroups (hG : Stellmacher.IsSemidihedralGroup G) :
    ∃ U : Subgroup G, Nonempty (U ≃* QuaternionGroup 2) ∧
      (∀ T : Subgroup G, Nonempty (T ≃* QuaternionGroup 2) →
        ∃ g : G, U.map (MulAut.conj g).toMonoidHom = T) ∧
      Subgroup.centralizer (U : Set G) ≤ U ∧
      U.relIndex (Subgroup.normalizer (U : Set G)) = 2 := by
  obtain ⟨n, hn, hcard, a, b, ha, hb, hconj, hgen⟩ := hG
  obtain ⟨hU, hC, hN⟩ := quaternion_representative_local hn a b hcard ha hb hconj hgen
  refine ⟨Subgroup.closure ({a^(2^(n-3)),a*b}:Set G), hU, ?_, hC, hN⟩
  intro T ⟨e⟩
  have hu : Nat.card (Subgroup.closure ({a^(2^(n-3)),a*b}:Set G)) = 8 := by
    obtain ⟨f⟩ := hU
    rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  exact quaternion_conjugacy_of_local hn a b ha hb hconj
    (normal_form a b _ _ (by positivity) ha (by rw [← hb]; exact pow_orderOf_eq_one _)
      hconj hgen) hu T e
end ABG.QuasiDihedral
