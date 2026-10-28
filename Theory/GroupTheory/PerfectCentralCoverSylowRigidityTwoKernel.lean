module

public import Theory.GroupTheory.PerfectCentralCoverSylowRigidity
public import Theory.GroupTheory.CoveringComparisonKernelCard

/-!
# Sylow rigidity for central two-group kernels

Pointwise Sylow rigidity for perfect central double covers of a fixed base
implies the same conclusion for every nontrivial central two-group kernel.
Choose a subgroup of index two in the actual kernel and quotient by its
ambient image. The original automorphism fixes this subgroup pointwise, so
it descends and fixes the actual Sylow image. Double-cover rigidity makes
the descended action trivial; uniqueness of maps from a perfect group
through a central quotient then recovers the original action.

The double-cover implication remains an explicit earlier theorem. The source
consumer is the Bender-family branch of Aschbacher--Smith 1.1.5(3), printed
pp.501--503, using the Sylow rigidity in GLS4, Chapter 4, Lemma 2.8(c).
-/

public section
open Subgroup
namespace PerfectCentralCovering
universe u v

/-- The precise earlier implication for double covers of one fixed base.
This definition makes no assertion that the implication has been proved. -/
@[expose] def DoubleCoverSylowRigidityAt (B : Type v) [Group B] : Prop :=
  ∀ (E₀ : Type u) [Group E₀] [Finite E₀] (f : Cover E₀ B),
    Nat.card f.toMonoidHom.ker = 2 → ∀ (P : Sylow 2 E₀) (α : MulAut E₀),
      (∀ x : P, α (x : E₀) = x) → α = 1

variable {E : Type u} {B : Type v} [Group E] [Finite E] [Group B]

private theorem exists_kernel_half (f : Cover E B)
    (hp : IsPGroup 2 f.toMonoidHom.ker) (hne : f.toMonoidHom.ker ≠ ⊥) :
    ∃ N : Subgroup E, N ≤ f.toMonoidHom.ker ∧ N.Normal ∧
      Nat.card f.toMonoidHom.ker = 2 * Nat.card N := by
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hnpos : 0 < n := by
    have hcard := (Subgroup.one_lt_card_iff_ne_bot (H := f.toMonoidHom.ker)).mpr hne
    change 1 < Nat.card f.toMonoidHom.ker at hcard
    by_contra h
    have hzero : n = 0 := by omega
    rw [hn, hzero] at hcard
    norm_num at hcard
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  obtain ⟨R, hR⟩ := Sylow.exists_subgroup_card_pow_prime (G := f.toMonoidHom.ker) 2
    (n := k) (by rw [hn, pow_succ]; exact dvd_mul_right _ _)
  let N := R.map f.toMonoidHom.ker.subtype
  have hNA : N ≤ f.toMonoidHom.ker := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hNc : N ≤ center E := hNA.trans f.ker_le_center
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [mem_center_iff.mp (hNc hn) g, mul_inv_cancel_right]
    exact hn⟩
  refine ⟨N, hNA, hNn, ?_⟩
  have hNc : Nat.card N = Nat.card R :=
    Subgroup.card_map_of_injective f.toMonoidHom.ker.subtype_injective
  rw [hNc, hR, hn, pow_succ, Nat.mul_comm]

/-- The double-cover theorem suffices for a nontrivial two-group kernel,
retaining the original cover, Sylow subgroup and automorphism. -/
theorem Cover.fixingSylow_eq_one_of_nontrivial_twoKernel
    (f : Cover E B) (rigidity : DoubleCoverSylowRigidityAt.{u, v} B)
    (hp : IsPGroup 2 f.toMonoidHom.ker) (hne : f.toMonoidHom.ker ≠ ⊥)
    (P : Sylow 2 E) (α : MulAut E) (hfix : ∀ x : P, α (x : E) = x) :
    α = 1 := by
  classical
  let : Group.IsPerfect E := f.isPerfect
  let : Finite B := Finite.of_surjective f.toMonoidHom f.surjective
  obtain ⟨N, hNA, hNn, hcard⟩ := exists_kernel_half f hp hne
  let : N.Normal := hNn
  have hNc : N ≤ center E := hNA.trans f.ker_le_center
  let q := QuotientGroup.mk' N
  let c : Cover (E ⧸ N) B := {
    toMonoidHom := QuotientGroup.lift N f.toMonoidHom hNA
    surjective := by
      intro b
      obtain ⟨e, he⟩ := f.surjective b
      exact ⟨q e, he⟩
    isPerfect := inferInstance
    ker_le_center := by
      intro x hx
      obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective N x
      have he : e ∈ f.toMonoidHom.ker := hx
      rw [mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective N y
      exact congrArg q (mem_center_iff.mp (f.ker_le_center he) z) }
  have hcomp : c.toMonoidHom.comp q = f.toMonoidHom := by ext x; rfl
  have hc : Nat.card c.toMonoidHom.ker = 2 := by
    have hh := Theory.GroupTheory.kernel_card_eq_mul_of_surjective_factor
      f.toMonoidHom c.toMonoidHom q c.surjective (QuotientGroup.mk'_surjective N) hcomp
    rw [QuotientGroup.ker_mk'] at hh
    have hpos : 0 < Nat.card N := Nat.card_pos
    nlinarith
  have hAP : f.toMonoidHom.ker ≤ P := hp.le_sylow_of_normal P
  have hmap : N.map (α : E →* E) = N := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change α y ∈ N
      rw [hfix ⟨y, hAP (hNA hy)⟩]
      exact hy
    · intro hx
      exact ⟨x, hx, hfix ⟨x, hAP (hNA hx)⟩⟩
  let β : MulAut (E ⧸ N) := QuotientGroup.congr N N α hmap
  have hβq (x : E) : β (q x) = q (α x) := rfl
  let Q := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  have hβfix : ∀ x : Q, β (x : E ⧸ N) = x := by
    rintro ⟨x, hx⟩
    change x ∈ (P : Subgroup E).map q at hx
    obtain ⟨p, hp, rfl⟩ := hx
    change β (q p) = q p
    rw [hβq]
    exact congrArg q (hfix ⟨p, hp⟩)
  have hβ : β = 1 := rigidity (E ⧸ N) c hc Q β hβfix
  have he : q.comp α.toMonoidHom = q.comp (MonoidHom.id E) := by
    ext x
    have hh := congrArg (fun a : MulAut (E ⧸ N) => a (q x)) hβ
    change β (q x) = q x at hh
    change q (α x) = q x
    rwa [hβq] at hh
  have ha : α.toMonoidHom = MonoidHom.id E :=
    monoidHom_eq_of_isPerfect_of_comp_eq q
      (by simpa only [q, QuotientGroup.ker_mk'] using hNc)
      α.toMonoidHom (MonoidHom.id E) he
  exact MulEquiv.ext (fun x => DFunLike.congr_fun ha x)

end PerfectCentralCovering
