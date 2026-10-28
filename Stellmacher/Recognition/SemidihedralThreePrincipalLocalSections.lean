module
public import ABG.ChapterIII.Section7.ThreePrincipalPairing
public import ABG.ChapterII.Section2.SimpleQD
public import Theory.SpecificGroups.GL2.ThreeInvolutionPairs
public import Theory.SpecificGroups.GL2.ThreeLargeSubgroupCenter
public import Theory.GroupTheory.PrimePowerDecomposition
public import Theory.PPrimeCore

/-!
# Principal-character values on local involution products

For supplied characteristic-three principal data, the root-supported
function on a product of two involutions of C_G(x) is four exactly when
the quotient product in GL₂(3) squares to the scalar involution; otherwise
it is zero. The odd core is retained. The general theorem only requires
an odd kernel and fusion of order-four elements to the supplied generator
squared. Simple groups with semidihedral Sylow subgroups supply this fusion,
so no N₂ hypothesis is needed once the surjective quotient map is given.

Decompose the product into commuting two-power and odd-order parts inside
its cyclic subgroup. The odd kernel preserves the order of the two-part.
In the order-four quotient branch the odd part has trivial image and the
two-part squares to x; global order-four fusion gives the value four. In
the sixth-power branch the two-part has order at most two. Root support
then identifies it with x, where the involution-section formula vanishes.

Source: Alperin–Brauer–Gorenstein III.7, equation (8), article pp.103–104.
-/

open Subgroup Matrix Matrix.GeneralLinearGroup
open Theory.Character
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable

private theorem two_power_order_coprime {G : Type*} [Group G]
    {a : G} (ha : ∃ k : ℕ, a ^ (2 ^ k) = 1) {m : ℕ}
    (hm : Nat.Coprime 2 m) : Nat.Coprime (orderOf a) m := by
  obtain ⟨k, hk⟩ := ha
  exact (hm.pow_left k).of_dvd_left (orderOf_dvd_of_pow_eq_one hk)

private theorem decomp_image_order {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hker : Nat.Coprime 2 (Nat.card f.ker))
    (a b : G) (ha : ∃ k : ℕ, a ^ (2 ^ k) = 1)
    (hb : Nat.Coprime 2 (orderOf b)) (hab : Commute a b) :
    orderOf (f (a * b)) = orderOf a * orderOf (f b) := by
  rw [map_mul, (hab.map f).orderOf_mul_eq_mul_orderOf_of_coprime,
    f.orderOf_eq_of_prime_power_of_coprime_ker hker a ha]
  exact (two_power_order_coprime ha hb).of_dvd_left (orderOf_map_dvd f a)
    |>.of_dvd_right (orderOf_map_dvd f b)

private theorem central_image {G : Type*} [Group G] [Finite G]
    {x : G} (hx : orderOf x = 2)
    (f : centralizer ({x} : Set G) →* GL (Fin 2) (ZMod 3))
    (hf : Function.Surjective f) (hker : Nat.Coprime 2 (Nat.card f.ker)) :
    f ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩ = threeCentral := by
  let z : centralizer ({x} : Set G) := ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩
  have hz : orderOf z = 2 := (Subgroup.orderOf_coe z).symm.trans hx
  have ho : orderOf (f z) = 2 :=
    (f.orderOf_eq_of_prime_power_of_coprime_ker hker z
      ⟨1, by simpa only [pow_one, hz] using pow_orderOf_eq_one z⟩).trans hz
  have hc : f z ∈ center (GL (Fin 2) (ZMod 3)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨a, rfl⟩ := hf y
    simpa only [← map_mul] using congrArg f
      (show a * z = z * a from Subtype.ext (mem_centralizer_singleton_iff.mp a.property))
  have hcard : Nat.card (⊤ : Subgroup (GL (Fin 2) (ZMod 3))) = 48 := by
    rw [Subgroup.card_top, Matrix.card_GL_field]
    decide
  have hc' : (⟨f z, mem_top _⟩ : (⊤ : Subgroup (GL (Fin 2) (ZMod 3)))) ∈
      center (⊤ : Subgroup (GL (Fin 2) (ZMod 3))) := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp hc y)
  rcases (three_large_subgroup_center ⊤ (Or.inr hcard)).2 _ |>.mp hc' with h | h
  · change f z = 1 at h
    simp [h] at ho
  · exact h

private theorem order_four_of_square_central (w : GL (Fin 2) (ZMod 3))
    (hw : w ^ 2 = threeCentral) : orderOf w = 4 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide : 0 < 4)
  · rw [show 4 = 2 * 2 from rfl, pow_mul, hw]
    decide +kernel
  · intro p hp hpd
    have hp2 : p = 2 := by
      have hd : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from hpd)
      exact (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one
    subst p
    norm_num only [Nat.reduceDiv]
    rw [hw]
    decide +kernel

private theorem four_section_value {G : Type*} [Group G] [Finite G]
    {x : G} (c : ABG.ThreePrincipalData G x)
    (hfuse : ∀ a : G, orderOf a = 4 → IsConj a (c.generator ^ (2 : ℤ)))
    (a b : G) (ha : orderOf a = 4) (hb : Odd (orderOf b)) (hab : Commute a b) :
    c.orderFunction (a * b) = 4 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (hfuse a ha)
  let e := MulAut.conj g
  have he : e a = c.generator ^ (2 : ℤ) := hg
  have hc : e b ∈ centralizer ({c.generator ^ (2 : ℤ)} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← he]
    exact (hab.map e.toMonoidHom).symm.eq
  let r : centralizer ({c.generator ^ (2 : ℤ)} : Set G) := ⟨e b, hc⟩
  have hr : Odd (orderOf r) := by
    rw [← Subgroup.orderOf_coe, e.orderOf_eq]
    exact hb
  have hv := c.orderFunction_order_four_section r hr
  have hf := c.orderFunction_isClassFunction (a * b) g
  change c.orderFunction (e (a * b)) = c.orderFunction (a * b) at hf
  rw [map_mul, he] at hf
  exact hf.symm.trans hv

private theorem square_eq_central_lift {G : Type*} [Group G] [Finite G]
    {x : G} (hx : orderOf x = 2)
    (f : centralizer ({x} : Set G) →* GL (Fin 2) (ZMod 3))
    (hf : Function.Surjective f) (hker : Nat.Coprime 2 (Nat.card f.ker))
    (a : centralizer ({x} : Set G)) (ha : orderOf a = 4)
    (hfaa : (f a) ^ 2 = threeCentral) : (a : G) ^ 2 = x := by
  let z : centralizer ({x} : Set G) := ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩
  have hcomm : Commute a z := Subtype.ext (mem_centralizer_singleton_iff.mp a.property)
  have hpow : (a ^ 2 * z⁻¹) ^ 2 = 1 := by
    rw [hcomm.pow_left 2 |>.inv_right |>.mul_pow, ← pow_mul,
      show 2 * 2 = 4 from rfl, ← ha, pow_orderOf_eq_one, one_mul, inv_pow]
    have hz : z ^ 2 = 1 := Subtype.ext (hx ▸ pow_orderOf_eq_one x)
    rw [hz, inv_one]
  have him : f (a ^ 2 * z⁻¹) = 1 := by
    rw [map_mul, map_pow, map_inv, hfaa, central_image hx f hf hker, mul_inv_cancel]
  have ho := f.orderOf_eq_of_prime_power_of_coprime_ker hker
    (a ^ 2 * z⁻¹) ⟨1, by simpa using hpow⟩
  have he : a ^ 2 * z⁻¹ = 1 := orderOf_eq_one_iff.mp (by simpa only [him, orderOf_one] using ho.symm)
  exact congrArg Subtype.val (mul_inv_eq_one.mp he)

private theorem local_value_four {G : Type*} [Group G] [Finite G]
    {x : G} (hx : orderOf x = 2) (c : ABG.ThreePrincipalData G x)
    (hfuse : ∀ a : G, orderOf a = 4 → IsConj a (c.generator ^ (2 : ℤ)))
    (f : centralizer ({x} : Set G) →* GL (Fin 2) (ZMod 3))
    (hf : Function.Surjective f) (hker : Nat.Coprime 2 (Nat.card f.ker))
    (w : centralizer ({x} : Set G)) (hw : (f w) ^ 2 = threeCentral) :
    c.localOrderFunction w = 4 := by
  obtain ⟨a, b, ha, hb, hab, he, ham, _⟩ :=
    exists_prime_power_decomposition 2 Nat.prime_two w
  have ho : orderOf (f w) = 4 := order_four_of_square_central (f w) hw
  have hprod := decomp_image_order f hker a b ha hb hab
  rw [he, ho] at hprod
  have hfbdiv : orderOf (f b) ∣ 4 := by
    rw [hprod]
    exact dvd_mul_left _ _
  have hfb1 : orderOf (f b) = 1 := Nat.eq_one_of_dvd_coprimes
    ((hb.of_dvd_right (orderOf_map_dvd f b)).pow_left 2) hfbdiv dvd_rfl
  have hfb : f b = 1 := orderOf_eq_one_iff.mp hfb1
  have ha4 : orderOf a = 4 := by simpa only [hfb1, mul_one] using hprod.symm
  have hfaa : (f a) ^ 2 = threeCentral := by
    simpa only [← he, map_mul, hfb, mul_one] using hw
  have hax : (a : G) ^ 2 = x := square_eq_central_lift hx f hf hker a ha4 hfaa
  have haG : (a : G) ∈ zpowers (w : G) := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp ham
    exact mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩
  have hroot : x ∈ zpowers (w : G) := by
    simpa only [hax] using (zpowers (w : G)).pow_mem haG 2
  have hval := four_section_value c hfuse (a : G) (b : G)
    ((Subgroup.orderOf_coe a).trans ha4)
    (by rw [Subgroup.orderOf_coe]; exact Nat.coprime_two_left.mp hb)
    (hab.map (centralizer ({x} : Set G)).subtype)
  change (if x ∈ zpowers (w : G) then c.orderFunction (w : G) else 0) = 4
  rw [if_pos hroot]
  have heG : (a : G) * (b : G) = (w : G) := congrArg Subtype.val he
  rwa [heG] at hval

private theorem local_value_six {G : Type*} [Group G] [Finite G]
    {x : G} (hx : orderOf x = 2) (c : ABG.ThreePrincipalData G x)
    (f : centralizer ({x} : Set G) →* GL (Fin 2) (ZMod 3))
    (hker : Nat.Coprime 2 (Nat.card f.ker))
    (w : centralizer ({x} : Set G)) (hw : (f w) ^ 6 = 1) :
    c.localOrderFunction w = 0 := by
  by_cases hroot : x ∈ zpowers (w : G)
  · change (if x ∈ zpowers (w : G) then c.orderFunction (w : G) else 0) = 0
    rw [if_pos hroot]
    obtain ⟨a, b, ha, hb, hab, he, ham, _⟩ :=
      exists_prime_power_decomposition 2 Nat.prime_two w
    have hprod := decomp_image_order f hker a b ha hb hab
    rw [he] at hprod
    have hadiv : orderOf a ∣ 6 :=
      (show orderOf a ∣ orderOf (f w) by rw [hprod]; exact dvd_mul_right _ _).trans
        (orderOf_dvd_of_pow_eq_one hw)
    have hacop : Nat.Coprime (orderOf a) 3 := two_power_order_coprime ha (by decide)
    have ha2div : orderOf a ∣ 2 := hacop.dvd_mul_right.mp hadiv
    rcases (Nat.dvd_prime Nat.prime_two).mp ha2div with ha1 | ha2
    · have haone : a = 1 := orderOf_eq_one_iff.mp ha1
      have he' : b = w := by simpa [haone] using he
      have hd := orderOf_dvd_of_mem_zpowers hroot
      rw [hx, Subgroup.orderOf_coe, ← he'] at hd
      exact False.elim ((Nat.coprime_two_left.mp hb).not_two_dvd_nat hd)
    · have haG : (a : G) ∈ zpowers (w : G) := by
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp ham
        exact mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩
      have hax : (a : G) = x := congrArg Subtype.val
        (IsCyclic.eq_of_orderOf_eq_two
          (x := (⟨(a : G), haG⟩ : zpowers (w : G)))
          (y := (⟨x, hroot⟩ : zpowers (w : G)))
          (by simpa only [← Subgroup.orderOf_coe] using ha2)
          (by simpa only [← Subgroup.orderOf_coe] using hx))
      have hval := c.orderFunction_involution_section b (Nat.coprime_two_left.mp hb)
      have heG : (a : G) * (b : G) = (w : G) := congrArg Subtype.val he
      rw [hax] at heG
      rwa [heG] at hval
  · exact involutionRootRestriction_supported x c.orderFunction w hroot

namespace Stellmacher.Recognition

/-- The local root-section evaluation only needs order-four fusion and an odd kernel. -/
public theorem threePrincipal_localOrderFunction_mul_of_order_four_fusion
    {G : Type*} [Group G] [Finite G] {x : G}
    (hx : orderOf x = 2) (c : ABG.ThreePrincipalData G x)
    (hfuse : ∀ a : G, orderOf a = 4 → IsConj a (c.generator ^ (2 : ℤ)))
    (f : centralizer ({x} : Set G) →* GL (Fin 2) (ZMod 3))
    (hf : Function.Surjective f) (hker : Nat.Coprime 2 (Nat.card f.ker))
    (u v : centralizer ({x} : Set G)) (hu : orderOf u = 2) (hv : orderOf v = 2) :
    c.localOrderFunction (u * v) =
      if (f u * f v) ^ 2 = threeCentral then 4 else 0 := by
  have image_order (a : centralizer ({x} : Set G)) (ha : orderOf a = 2) :
      orderOf (f a) = 2 :=
    (f.orderOf_eq_of_prime_power_of_coprime_ker hker a
      ⟨1, by simpa only [pow_one, ha] using pow_orderOf_eq_one a⟩).trans ha
  by_cases hfour : (f u * f v) ^ 2 = threeCentral
  · rw [if_pos hfour]
    exact local_value_four hx c hfuse f hf hker (u * v) (by rwa [map_mul])
  · rw [if_neg hfour]
    have hsix := (three_involution_product_six_or_square_central (f u) (f v)
      (image_order u hu) (image_order v hv)).resolve_right hfour
    exact local_value_six hx c f hker (u * v) (by rwa [map_mul])

/-- Every supplied principal datum has the required local values in the semidihedral simple case.
No N₂ hypothesis or triviality of the odd core is needed once the quotient map is supplied. -/
public theorem threePrincipal_localOrderFunction_mul_of_semidihedral
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (x : G) (hx : orderOf x = 2) (c : ABG.ThreePrincipalData G x)
    (f : centralizer ({x} : Set G) →* GL (Fin 2) (ZMod 3))
    (hf : Function.Surjective f)
    (hfker : f.ker = pPrimeCore 2 (centralizer ({x} : Set G)))
    (u v : centralizer ({x} : Set G)) (hu : orderOf u = 2) (hv : orderOf v = 2) :
    c.localOrderFunction (u * v) =
      if (f u * f v) ^ 2 = threeCentral then 4 else 0 := by
  apply threePrincipal_localOrderFunction_mul_of_order_four_fusion hx c ?_ f hf
    (by rw [hfker]; exact pPrimeCore_coprime_card) u v hu hv
  obtain ⟨T, Q, hframe⟩ := ABG.exists_quasiDihedralFusionFrame S hS
  obtain ⟨r, _, _, hcov⟩ :=
    (ABG.quasiDihedral_qdPattern_of_simple S T Q hframe).2.2.1
  have hgen : orderOf (c.generator ^ (2 : ℤ)) = 4 := by
    rw [zpow_ofNat, orderOf_pow, c.generator_order]
    norm_num
  intro a ha
  obtain ⟨i, hi⟩ := hcov a ha
  obtain ⟨j, hj⟩ := hcov (c.generator ^ (2 : ℤ)) hgen
  have he : i = j := Subsingleton.elim _ _
  exact hi.trans (he ▸ hj.symm)

end Stellmacher.Recognition
