module

public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.Basic
import GorensteinWalter.DihedralCore
import Theory.GroupTheory.PGroup.CyclicInvolution
import Mathlib.Tactic

/-!
# Brauer–Suzuki–Wall data from a dihedral involution centralizer

Under the exact hypotheses of Aschbacher–Smith, *The Classification of
Quasithin Groups*, I.4.1 (printed p. 415), the rotation subgroup and a
reflection supply the configuration in Bender's Brauer–Suzuki–Wall theorem
(`refs/latex/bender-bsw.tex`, hypotheses (i)–(iv)).

Choose the unique involution of the cyclic rotation subgroup, and conjugate
the entire dihedral embedding so that this involution becomes the specified
`z`. Its image centralizes `z` and has the same order as `C_G(z)`, hence is
that centralizer. This also covers the Klein-four case without asserting
uniqueness of central involutions in the whole dihedral group.

The fixed subgroup follows from inversion and uniqueness of the involution
in a cyclic group. For TI, a nontrivial intersection with a conjugate contains
the cyclic two-group's involution; uniqueness in the conjugate then forces
the conjugating element to centralize `z`.
-/

open GorensteinWalter
namespace CFSG.Quasithin.DihedralInvolutionCentralizerHypotheses

private theorem cyclic_two_ti {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [IsCyclic K] (hK : IsPGroup 2 K)
    {z : G} (hzK : z ∈ K) (hz : IsInvolution z) :
    ∀ g : G, g ∉ Subgroup.centralizer ({z} : Set G) → Disjoint K (K.conjBy g) := by
  intro g hg
  rw [Subgroup.disjoint_def]
  intro x hx hxg
  by_contra hne
  have hmeet : (K.conjBy g).subgroupOf K ≠ ⊥ := by
    intro he
    have hm : (⟨x, hx⟩ : K) ∈ (K.conjBy g).subgroupOf K := hxg
    rw [he, Subgroup.mem_bot] at hm
    exact hne (congrArg Subtype.val hm)
  have hzo : orderOf (⟨z, hzK⟩ : K) = 2 := by
    simpa using (orderOf_eq_prime hz.2 hz.1 : orderOf z = 2)
  have hzg : z ∈ K.conjBy g := hK.involution_mem_subgroup_of_ne_bot hzo _ hmeet
  let e := K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  let : IsCyclic (K.map (MulAut.conj g).toMonoidHom) := e.isCyclic.mp inferInstance
  have he : e ⟨z, hzK⟩ = (⟨z, hzg⟩ : K.conjBy g) :=
    IsCyclic.eq_of_orderOf_eq_two ((e.orderOf_eq _).trans hzo) (by
      exact (Subgroup.orderOf_coe (⟨z, hzg⟩ : K.conjBy g)).symm.trans
        (orderOf_eq_prime hz.2 hz.1))
  have hconj : g * z * g⁻¹ = z := congrArg Subtype.val he
  apply hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc
    g * z = (g * z * g⁻¹) * g := by group
    _ = z * g := by rw [hconj]

private theorem aligned_embedding {G : Type*} [Group G] [Finite G] {n : ℕ}
    (h : DihedralInvolutionCentralizerHypotheses G n) :
    ∃ f : DihedralGroup (2 ^ (n - 1)) →* G, Function.Injective f ∧
      (⊤ : Subgroup (DihedralGroup (2 ^ (n - 1)))).map f =
        Subgroup.centralizer ({h.z} : Set G) ∧
      h.z ∈ (Subgroup.zpowers (DihedralGroup.r 1)).map f := by
  classical
  let D := DihedralGroup (2 ^ (n - 1))
  let R : Subgroup D := Subgroup.zpowers (DihedralGroup.r 1)
  have hRcard : Nat.card R = 2 ^ (n - 1) := by
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  obtain ⟨u, huo⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 (by
    rw [hRcard]
    exact dvd_pow_self 2 (by have := h.two_le; omega))
  have hu2 : (u : D) ^ 2 = 1 := by
    have hu := pow_orderOf_eq_one u
    rw [huo] at hu
    exact congrArg Subtype.val hu
  have hune : (u : D) ≠ 1 := by
    intro he
    have hu : u = 1 := Subtype.ext he
    rw [hu, orderOf_one] at huo
    omega
  have huc : ∀ x : D, x * u = u * x := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp u.2
    have huform : (u : D) = DihedralGroup.r (k : ZMod (2 ^ (n - 1))) := by
      rw [← hk, DihedralGroup.r_one_zpow]
    have hneg : -(k : ZMod (2 ^ (n - 1))) = k := by
      have hinv : (u : D)⁻¹ = u := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hu2)
      rw [huform, DihedralGroup.inv_r] at hinv
      exact DihedralGroup.r.inj hinv
    intro x
    rw [huform]
    rcases dihedralGroup_cases x with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · change DihedralGroup.r i * DihedralGroup.r _ = DihedralGroup.r _ * DihedralGroup.r i
      rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
    · change DihedralGroup.sr i * DihedralGroup.r _ = DihedralGroup.r _ * DihedralGroup.sr i
      rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, sub_eq_add_neg, hneg]
  let e := h.centralizer_equiv.some
  let f₀ : D →* G := (Subgroup.centralizer ({h.z} : Set G)).subtype.comp e.symm.toMonoidHom
  have hf₀ : Function.Injective f₀ := Subtype.val_injective.comp e.symm.injective
  have huI : IsInvolution (f₀ u) := by
    refine ⟨?_, ?_⟩
    · intro he
      apply hune
      apply hf₀
      simpa using he
    · rw [← map_pow, hu2, map_one]
  obtain ⟨g, hg⟩ := h.involutions_conjugate (f₀ u) huI
  let f := (MulAut.conj g).toMonoidHom.comp f₀
  have hf : Function.Injective f := (MulAut.conj g).injective.comp hf₀
  have hfu : f u = h.z := hg
  have hle : (⊤ : Subgroup D).map f ≤ Subgroup.centralizer ({h.z} : Set G) := by
    rintro x ⟨y, _, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hfu, ← map_mul, ← map_mul, huc]
  refine ⟨f, hf, Subgroup.eq_of_le_of_card_ge hle ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hf, Subgroup.card_top, h.centralizer_card,
      DihedralGroup.nat_card]
    have he : n - 1 + 1 = n := by have := h.two_le; omega
    rw [mul_comm, ← pow_succ, he]
  · exact Subgroup.mem_map.mpr ⟨u, u.2, hfu⟩

/-- The Brauer–Suzuki–Wall configuration associated to the I.4.1 hypotheses. -/
public theorem exists_brauerSuzukiWallHypotheses
    {G : Type*} [Group G] [Finite G] {n : ℕ}
    (h : DihedralInvolutionCentralizerHypotheses G n) :
    ∃ b : BrauerSuzukiWallHypotheses G,
      b.t = h.z ∧ b.H = Subgroup.centralizer ({h.z} : Set G) ∧
      Nat.card b.K = 2 ^ (n - 1) := by
  classical
  obtain ⟨f, hf, hH, hzK⟩ := aligned_embedding h
  let R : Subgroup (DihedralGroup (2 ^ (n - 1))) := Subgroup.zpowers (DihedralGroup.r 1)
  let K := R.map f
  let s := f (DihedralGroup.sr 0)
  have hKcyc : IsCyclic K := by
    change IsCyclic ((Subgroup.zpowers (DihedralGroup.r 1)).map f)
    rw [MonoidHom.map_zpowers]
    infer_instance
  let := hKcyc
  have hKcard : Nat.card K = 2 ^ (n - 1) := by
    rw [Subgroup.card_map_of_injective hf, Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hKle : K ≤ Subgroup.centralizer ({h.z} : Set G) := by
    rw [← hH]
    exact Subgroup.map_mono le_top
  have hsH : s ∈ Subgroup.centralizer ({h.z} : Set G) := by
    rw [← hH]
    exact Subgroup.mem_map.mpr ⟨DihedralGroup.sr 0, Subgroup.mem_top _, rfl⟩
  have hsI : IsInvolution s := by
    constructor
    · intro he
      have hs1 : (DihedralGroup.sr 0 : DihedralGroup (2 ^ (n - 1))) = 1 :=
        hf (by simpa [s] using he)
      have ho := DihedralGroup.orderOf_sr (0 : ZMod (2 ^ (n - 1)))
      rw [hs1, orderOf_one] at ho
      omega
    · dsimp [s]
      rw [← map_pow]
      have ho := pow_orderOf_eq_one (DihedralGroup.sr (0 : ZMod (2 ^ (n - 1))))
      rw [DihedralGroup.orderOf_sr] at ho
      rw [ho, map_one]
  have hsnot : s ∉ K := by
    rintro ⟨x, hx, he⟩
    exact sr_not_mem_zpowers_r_one 0 (hf he ▸ hx)
  have hInv : ∀ x : G, x ∈ K → s * x * s⁻¹ = x⁻¹ := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    dsimp [s]
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv,
      DihedralGroup.r_one_zpow, DihedralGroup.inv_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_r]
    simp
  have hjoin : Subgroup.centralizer ({h.z} : Set G) = K ⊔ Subgroup.zpowers s := by
    apply le_antisymm
    · rw [← hH]
      rintro x ⟨y, _, rfl⟩
      rcases dihedralGroup_cases y with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact Subgroup.mem_sup_left (Subgroup.mem_map.mpr ⟨_, r_mem_zpowers_r_one i, rfl⟩)
      · have he : DihedralGroup.sr i = DihedralGroup.sr 0 * DihedralGroup.r i := by simp
        rw [he, map_mul]
        exact (K ⊔ Subgroup.zpowers s).mul_mem
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
          (Subgroup.mem_sup_left (Subgroup.mem_map.mpr ⟨_, r_mem_zpowers_r_one i, rfl⟩))
    · exact sup_le hKle (Subgroup.zpowers_le.mpr hsH)
  have hfixed : K ⊓ Subgroup.centralizer ({s} : Set G) = Subgroup.zpowers h.z := by
    apply le_antisymm
    · intro x hx
      have he : x = x⁻¹ := by
        calc
          x = s * x * s⁻¹ := by
            rw [← Subgroup.mem_centralizer_singleton_iff.mp hx.2]
            group
          _ = x⁻¹ := hInv x hx.1
      by_cases hx1 : x = 1
      · simp [hx1]
      have hx2 : x ^ 2 = 1 := by
        rw [pow_two]
        nth_rw 1 [he]
        exact inv_mul_cancel x
      have heq : (⟨x, hx.1⟩ : K) = ⟨h.z, hzK⟩ :=
        IsCyclic.eq_of_orderOf_eq_two (by simpa using (orderOf_eq_prime hx2 hx1 : orderOf x = 2))
          (by simpa using (orderOf_eq_prime h.involution.2 h.involution.1 : orderOf h.z = 2))
      have hxz : x = h.z := congrArg Subtype.val heq
      rw [hxz]
      exact Subgroup.mem_zpowers h.z
    · apply Subgroup.zpowers_le.mpr
      refine ⟨hzK, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hsH).symm
  let b : BrauerSuzukiWallHypotheses G := {
    t := h.z
    K := K
    H := Subgroup.centralizer ({h.z} : Set G)
    s := s
    t_involution := h.involution
    t_mem_K := hzK
    H_eq_centralizer := rfl
    K_commutative := inferInstance
    s_involution := hsI
    s_not_mem_K := hsnot
    H_eq_join := hjoin
    fixed_subgroup_eq := hfixed
    s_inverts_K := hInv
    conjugate_disjoint := cyclic_two_ti K (IsPGroup.of_card hKcard) hzK h.involution
    involutions_conjugate := h.involutions_conjugate
  }
  exact ⟨b, rfl, rfl, hKcard⟩

end CFSG.Quasithin.DihedralInvolutionCentralizerHypotheses
