module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Dichotomy
public import Theory.GroupTheory.PrimeSubgroupInvolution

/-!
# The lifted central factor and its cubic correction

In the split normalizer alternative, lift the nonidentity central C₂ factor
to an involution of the original normalizer. It inverts B and commutes with
C_G(B) modulo B. Cubic correction then factors every x in C_G(B) as b y with
b in B and y commuting with the lift. Elements of order coprime to three
already commute with it, since their central commutator has both orders.

This retains the B-conjugates of the lifted involution; it makes no singleton
fusion assertion.

Source: Aschbacher–Smith J.2.7(3), printed p.436 (PDF p.447).
-/

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

private lemma normalizer_involution_lift (x : c.NormalizerQuotient) (hx : orderOf x = 2) :
    ∃ y : c.NB, orderOf y = 2 ∧ c.normalizerQuotientMap y = x := by
  obtain ⟨y, rfl⟩ := c.normalizerQuotientMap_surjective x
  have hx2 : (c.normalizerQuotientMap y)^2 = 1 := hx ▸ pow_orderOf_eq_one _
  have hk : y^2 ∈ c.normalizerKernel := by
    rw [← c.normalizerQuotientMap_ker]
    exact (map_pow c.normalizerQuotientMap y 2).trans hx2
  have hcard : Nat.card c.normalizerKernel = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe (le_normalizer : c.B ≤ c.NB)).toEquiv).trans
      (SourceCompletion.B_card c)
  have hy6 : (y^3)^2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨y^2, hk⟩ : c.normalizerKernel))
    rw [hcard] at hh
    have hh' := congrArg Subtype.val hh
    change (y^2)^3 = 1 at hh'
    simpa only [← pow_mul] using hh'
  have hmap : c.normalizerQuotientMap (y^3) = c.normalizerQuotientMap y := by
    rw [map_pow, show 3 = 2+1 from rfl, pow_succ, hx2, one_mul]
  refine ⟨y^3, orderOf_eq_prime hy6 ?_, hmap⟩
  intro he
  have hone : c.normalizerQuotientMap y = 1 := by rw [← hmap, he, map_one]
  simp [hone] at hx

/-- Lift the central factor of the marked split quotient in the original group. -/
public theorem exists_central_quotient_inverter_of_split
    (e : c.NormalizerQuotient ≃* (Multiplicative (ZMod 2) × AlternatingSix.M10.extension))
    (hM : c.centralizerImage.map e.toMonoidHom =
      (⊥ : Subgroup (Multiplicative (ZMod 2))).prod ⊤) :
    ∃ u : G, orderOf u = 2 ∧ c.InvertsB u ∧
      ∀ x ∈ c.GB, ⁅u,x⁆ ∈ c.B := by
  let a : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1
  have ha2 : a ^ 2 = 1 := by decide
  have hane : a ≠ 1 := by decide
  let v := e.symm (a, 1)
  have hv2 : v ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    change (e (e.symm (a,1))) ^ 2 = 1
    rw [e.apply_symm_apply]
    exact Prod.ext ha2 (one_pow 2)
  have hvne : v ≠ 1 := by
    intro h
    have he := congrArg (fun x => (e x).1) h
    exact hane (by simpa only [v, e.apply_symm_apply, map_one, Prod.fst_one] using he)
  have hvM : v ∉ c.centralizerImage := by
    intro h
    have he := mem_map_of_mem e.toMonoidHom h
    rw [hM] at he
    change (e (e.symm (a,1))) ∈ (⊥ : Subgroup (Multiplicative (ZMod 2))).prod ⊤ at he
    rw [e.apply_symm_apply] at he
    exact hane he.1
  have hvcentral : v ∈ center c.NormalizerQuotient := by
    apply mem_center_iff.mpr
    intro x
    apply e.injective
    simp only [map_mul]
    change e x * e (e.symm (a,1)) = e (e.symm (a,1)) * e x
    rw [e.apply_symm_apply]
    apply Prod.ext
    · exact mul_comm _ _
    · exact (mul_one _).trans (one_mul _).symm
  obtain ⟨u, hu2, hu⟩ := c.normalizer_involution_lift v (orderOf_eq_prime hv2 hvne)
  have huGB : (u : G) ∉ c.GB := by
    intro h
    exact hvM (hu ▸ mem_map_of_mem c.normalizerQuotientMap h)
  have hui : c.InvertsB (u : G) := by
    rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one c.B
      (by rw [SourceCompletion.B_card c]; decide) (u : G)
      (congrArg Subtype.val (hu2 ▸ pow_orderOf_eq_one u)) u.property with hc | hi
    · exact (huGB (fun b hb => (hc b hb).symm)).elim
    · exact hi
  refine ⟨u, (Subgroup.orderOf_coe u).trans hu2, hui, ?_⟩
  intro x hx
  let xN : c.NB := ⟨x, c.GB_le_NB hx⟩
  have hm : ⁅u,xN⁆ ∈ c.normalizerQuotientMap.ker := by
    change c.normalizerQuotientMap ⁅u,xN⁆ = 1
    simp only [commutatorElement_def, map_mul, map_inv, hu]
    rw [← mem_center_iff.mp hvcentral (c.normalizerQuotientMap xN)]
    group
  rw [c.normalizerQuotientMap_ker] at hm
  exact hm


/-- Correct an element of the original cubic centralizer by a cubic element. -/
public theorem cubic_factor_of_modular_inverter (u : G) (hui : c.InvertsB u)
    (hmod : ∀ x ∈ c.GB, ⁅u,x⁆ ∈ c.B) (x : G) (hx : x ∈ c.GB) :
    ∃ b ∈ c.B, ∃ y ∈ c.GB, Commute u y ∧ x = b*y := by
  let b := ⁅u,x⁆
  have hb : b ∈ c.B := hmod x hx
  have hb3 : b^3 = 1 := by
    have h := pow_card_eq_one' (x := (⟨b,hb⟩ : c.B))
    rw [SourceCompletion.B_card c] at h
    exact congrArg Subtype.val h
  have hbi : b⁻¹ = b^2 := by
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ, hb3]
  have hux : u*x*u⁻¹ = b*x := by dsimp [b, commutatorElement_def]; group
  let y := b^2*x
  have hy : y ∈ c.GB := c.GB.mul_mem
    (c.GB.pow_mem ((c.B_le_GB_of_card (SourceCompletion.B_card c)) hb) 2) hx
  have huy : u*y*u⁻¹ = y := by
    calc
      u*y*u⁻¹ = (u*b*u⁻¹)^2*(u*x*u⁻¹) := by dsimp [y]; rw [conj_pow]; group
      _ = (b⁻¹)^2*(b*x) := by rw [hui b hb, hux]
      _ = b⁻¹*x := by group
      _ = y := by rw [hbi]
  refine ⟨b,hb,y,hy,mul_inv_eq_iff_eq_mul.mp huy,?_⟩
  calc
    x = b^3*x := by rw [hb3, one_mul]
    _ = b*y := by dsimp [y]; group

/-- Coprime-order elements have trivial central cubic displacement. -/
public theorem commute_of_modular_cubic_of_coprime_power (u : G)
    (hmod : ∀ x ∈ c.GB, ⁅u,x⁆ ∈ c.B)
    (x : G) (hx : x ∈ c.GB) (n : ℕ) (hn : Nat.Coprime 3 n) (hxn : x^n=1) :
    Commute u x := by
  let b := ⁅u,x⁆
  have hb : b ∈ c.B := hmod x hx
  have hb3 : b^3 = 1 := by
    have h := pow_card_eq_one' (x := (⟨b,hb⟩ : c.B))
    rw [SourceCompletion.B_card c] at h
    exact congrArg Subtype.val h
  have hux : u*x*u⁻¹ = b*x := by dsimp [b, commutatorElement_def]; group
  have hbx : Commute b x := hx b hb
  have hbn : b^n=1 := by
    have h : (b*x)^n=1 := by
      rw [← hux, conj_pow, hxn]
      group
    rwa [hbx.mul_pow, hxn, mul_one] at h
  have hb1 : b=1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hn (orderOf_dvd_of_pow_eq_one hb3)
      (orderOf_dvd_of_pow_eq_one hbn))
  apply mul_inv_eq_iff_eq_mul.mp
  simpa only [hb1, one_mul] using hux

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
