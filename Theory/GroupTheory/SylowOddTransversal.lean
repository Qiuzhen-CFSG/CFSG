module
public import BenderSuzuki.PFchapter1section1.proposition_2_a
public import Theory.GroupTheory.Involution.Dihedral
public import Mathlib.GroupTheory.Sylow
public import Theory.GroupTheory.OddElementLift
public import Theory.GroupTheory.Hall.OddSylowComplement

/-!
# Odd representatives of Sylow-normalizer cosets

For a nontrivial TI Sylow two-subgroup, involutions in distinct Sylows
have odd-order product. Its cyclic conjugator gives an odd representative
of each normalizer coset. Regularity of a Sylow away from its fixed point
supplies the TI property. Odd representatives lift through a surjection
whose normalizer preimage is marked, including central quotients.

Source: the dihedral argument in DGS, Groups and Graphs (1985), 6.5,
printed p.122. The solvable case uses a complementary odd Hall subgroup.
-/

public noncomputable section
open Subgroup BenderSuzuki.PFAppendixIII
open scoped Pointwise
namespace Sylow
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem ti_normalizer_of_commute (T : Sylow 2 G)
    (hti : ∀ P Q : Sylow 2 G, (P : Subgroup G) ⊓ (Q : Subgroup G) ≠ ⊥ → P = Q)
    {t x : G} (ht : t ∈ T) (ht1 : t ≠ 1) (hc : Commute x t) :
    x ∈ normalizer (T : Set G) := by
  have he : T = x • T := hti T (x • T) (by
    intro hb
    have hm : t ∈ (T : Subgroup G) ⊓ (x • T : Sylow 2 G) :=
      ⟨ht, ⟨t, ht, by simp [MulAut.conj_apply, hc.eq, mul_assoc]⟩⟩
    rw [hb] at hm
    exact ht1 hm)
  exact Sylow.smul_eq_iff_mem_normalizer.mp he.symm

/-- Every normalizer coset of a nontrivial TI Sylow two-subgroup has an odd representative. -/
theorem exists_odd_normalizer_coset_of_ti (T : Sylow 2 G)
    (hti : ∀ P Q : Sylow 2 G, (P : Subgroup G) ⊓ (Q : Subgroup G) ≠ ⊥ → P = Q)
    (hne : (T : Subgroup G) ≠ ⊥) (g : G) :
    ∃ x : G, Odd (orderOf x) ∧ g⁻¹ * x ∈ normalizer (T : Set G) := by
  by_cases hg : g ∈ normalizer (T : Set G)
  · exact ⟨1, by simp, by simpa using (normalizer (T : Set G)).inv_mem hg⟩
  let : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hd : 2 ∣ Nat.card T := T.isPGroup'.card_eq_or_dvd.resolve_left
    (by have := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial T); omega)
  obtain ⟨t, ht2⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 hd
  have ht : IsInvolution (t : G) := by
    have hh : orderOf (t : G) = 2 := by rwa [Subgroup.orderOf_coe]
    exact ⟨(orderOf_eq_prime_iff.mp hh).2, (orderOf_eq_prime_iff.mp hh).1⟩
  let u := (MulAut.conj g) (t : G)
  have hu : IsInvolution u := ⟨by simpa [u] using ht.ne_one,
    by change ((MulAut.conj g) (t : G))^2 = 1; rw [←map_pow,ht.sq_eq_one,map_one]⟩
  have huT : u ∈ (g • T : Sylow 2 G) := ⟨t,t.property,rfl⟩
  have htu : (t : G) ≠ u := by
    intro he
    have hc : Commute g (t : G) := by
      change g * (t : G) = (t : G) * g
      have hh := congrArg (fun a : G => a*g) he.symm
      simpa [u,MulAut.conj_apply,mul_assoc] using hh
    exact hg (ti_normalizer_of_commute T hti t.property ht.ne_one hc)
  have ho : Odd (orderOf ((t : G)*u)) := by
    rw [←Nat.not_even_iff_odd]
    rintro ⟨m,hm⟩
    have hm' : orderOf ((t : G)*u) = 2*m := by omega
    obtain ⟨hz,hzt,hzu⟩ :=
      BenderSuzuki.External.Suzuki.V.suzuki_ch5_proposition_1_2_iii ht hu htu hm'
    let z := ((t : G)*u)^m
    have hzT := ti_normalizer_of_commute T hti t.property ht.ne_one hzt
    have hzU := ti_normalizer_of_commute (g • T) hti huT hu.ne_one hzu
    have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers,orderOf_eq_prime hz.sq_eq_one hz.ne_one]; rfl)
    have htmem : z ∈ (T : Subgroup G) := by
      have hh : z ∈ zpowers z ⊓ normalizer (T : Set G) := ⟨mem_zpowers z,hzT⟩
      rw [hp.inf_normalizer_sylow T] at hh
      exact hh.2
    have humem : z ∈ (g • T : Sylow 2 G) := by
      have hh : z ∈ zpowers z ⊓ normalizer ((g • T : Sylow 2 G) : Set G) := ⟨mem_zpowers z,hzU⟩
      rw [hp.inf_normalizer_sylow (g • T)] at hh
      exact hh.2
    have he := hti T (g • T) (by
      intro hb
      have hh : z ∈ (T : Subgroup G) ⊓ (g • T : Sylow 2 G) := ⟨htmem,humem⟩
      rw [hb] at hh
      exact hz.ne_one hh)
    exact hg (Sylow.smul_eq_iff_mem_normalizer.mp he.symm)
  obtain ⟨y,hy,he⟩ := BenderSuzuki.PFchapter1section1.exists_zpowers_conjugator_of_odd_product ht hu ho
  have hyodd : Odd (orderOf y) := by
    exact ho.of_dvd_nat (orderOf_dvd_of_mem_zpowers hy)
  refine ⟨y⁻¹,by simpa using hyodd,?_⟩
  have hc : Commute (g⁻¹*y⁻¹) (t : G) := by
    change (g⁻¹*y⁻¹)*(t : G) = (t : G)*(g⁻¹*y⁻¹)
    change y⁻¹*(t : G)*y = g*(t : G)*g⁻¹ at he
    have hh := congrArg (fun a : G => g⁻¹*a*y⁻¹) he
    simpa [mul_assoc] using hh
  exact ti_normalizer_of_commute T hti t.property ht.ne_one hc

/-- A Sylow subgroup regular off its unique fixed point has trivial intersections with distinct Sylows. -/
theorem eq_of_inf_ne_bot_of_regular_compl {Ω : Type*} [MulAction G Ω]
    (S : Sylow 2 G) (o : Ω)
    (hN : normalizer (S : Set G) = MulAction.stabilizer G o)
    (hreg : ∀ a b : Ω, a ≠ o → b ≠ o → ∃! s : S, (s : G) • a = b)
    (P Q : Sylow 2 G) (hi : (P : Subgroup G) ⊓ (Q : Subgroup G) ≠ ⊥) : P = Q := by
  have hs (R : Sylow 2 G) (hr : (S : Subgroup G) ⊓ (R : Subgroup G) ≠ ⊥) : S = R := by
    obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq G S R
    obtain ⟨x,hx,hx1⟩ := ((S : Subgroup G) ⊓ (g • S : Sylow 2 G)).bot_or_exists_ne_one.resolve_left hr
    obtain ⟨y,hy,hye⟩ := hx.2
    have hyo : y • o = o := MulAction.mem_stabilizer_iff.mp
      (hN ▸ (S : Subgroup G).le_normalizer hy)
    have hxgo : x • (g • o) = g • o := by
      rw [←hye]
      change (g*y*g⁻¹) • (g • o) = g • o
      simpa only [MulAut.conj_apply,mul_smul,inv_smul_smul] using congrArg (g • ·) hyo
    have hgo : g • o = o := by
      by_contra hh
      obtain ⟨s,_,hs⟩ := hreg (g • o) (g • o) hh hh
      have he : (⟨x,hx.1⟩ : S) = 1 := (hs _ hxgo).trans (hs 1 (one_smul _ _)).symm
      exact hx1 (congrArg Subtype.val he)
    exact (Sylow.smul_eq_iff_mem_normalizer.mpr (hN ▸ hgo)).symm
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P S
  have hm : (g • P : Sylow 2 G).toSubgroup ⊓ (g • Q : Sylow 2 G).toSubgroup ≠ ⊥ := by
    change (P : Subgroup G).map (MulAut.conj g).toMonoidHom ⊓
      (Q : Subgroup G).map (MulAut.conj g).toMonoidHom ≠ ⊥
    rw [←Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    exact fun hh => hi ((map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp hh)
  rw [hg] at hm
  exact smul_left_cancel g (hg.trans (hs _ hm))
/-- Complementary odd Hall subgroups give odd representatives in the solvable case. -/
theorem exists_odd_normalizer_coset_of_solvable (T : Sylow 2 G)
    (hsol : Group.IsSolvable G) (g : G) :
    ∃ x : G, Odd (orderOf x) ∧ g⁻¹ * x ∈ normalizer (T : Set G) := by
  obtain ⟨D,hodd,hcompl⟩ := Subgroup.exists_odd_complement_sylow_two hsol T
  let z := hcompl.symm.equiv g
  have he : (z.1 : G) * z.2 = g := hcompl.symm.equiv_fst_mul_equiv_snd g
  refine ⟨z.1,?_,?_⟩
  · have hh := hodd.of_dvd_nat (orderOf_dvd_natCard z.1)
    simpa only [Subgroup.orderOf_coe] using hh
  · rw [←he,mul_inv_rev,mul_assoc,inv_mul_cancel,mul_one]
    exact (T : Subgroup G).le_normalizer ((T : Subgroup G).inv_mem z.2.property)
end Sylow

namespace MonoidHom
/-- Odd coset representatives lift through a surjection with the literal subgroup preimage. -/
theorem exists_odd_coset_of_comap {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (N : Subgroup G) (M : Subgroup H)
    (hNM : M.comap f = N)
    (hm : ∀ g : H, ∃ x : H, Odd (orderOf x) ∧ g⁻¹*x ∈ M) (g : G) :
    ∃ x : G, Odd (orderOf x) ∧ g⁻¹*x ∈ N := by
  obtain ⟨a,ha,ham⟩ := hm (f g)
  obtain ⟨b,hb⟩ := hf a
  obtain ⟨x,_,hx,hfx⟩ := f.exists_odd_power_with_image b (hb ▸ ha)
  refine ⟨x,hx,?_⟩
  rw [←hNM]
  change f (g⁻¹*x) ∈ M
  rwa [map_mul,map_inv,hfx,hb]
end MonoidHom
