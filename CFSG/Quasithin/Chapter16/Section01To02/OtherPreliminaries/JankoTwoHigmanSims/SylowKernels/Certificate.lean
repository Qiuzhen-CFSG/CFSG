module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Conventions
public import Theory.GroupTheory.WordSubgroup

/-!
# Certificates for the two sporadic Sylow restriction kernels

A commuting permutation preserves the fixed-point pattern of every word in
the generators. Once its images on orbit representatives are known, words
transport those images to every point. The finite certificates use these two
facts to exhaust the restriction kernel, without enumerating automorphisms or
restricting their orders. Sylow conjugacy then transports innerness.

Source: Aschbacher–Smith, combined manuscript, 16.1.6, printed p.1172.
-/

public section
namespace CFSG.Quasithin.SylowKernelCertificate
open Theory.GroupTheory

theorem commute_word {X : Type*} {m : ℕ} (gen : Fin m → Equiv.Perm X)
    (p : Equiv.Perm X) (hp : ∀ i, Commute p (gen i)) (w : List (Fin m)) :
    Commute p (evalWord gen w) := by
  induction w with
  | nil => exact Commute.one_right p
  | cons i w ih => exact (hp i).mul_right ih

theorem fixed_word_iff {X : Type*} {m : ℕ} (gen : Fin m → Equiv.Perm X)
    (p : Equiv.Perm X) (hp : ∀ i, Commute p (gen i)) (w : List (Fin m)) (x : X) :
    evalWord gen w (p x) = p x ↔ evalWord gen w x = x := by
  have he := congrArg (fun q : Equiv.Perm X => q x) (commute_word gen p hp w).eq
  change p (evalWord gen w x) = evalWord gen w (p x) at he
  rw [← he, p.injective.eq_iff]

theorem eq_of_orbit_images {X I : Type*} {m k : ℕ}
    (gen : Fin m → Equiv.Perm X) (base : Fin k → X)
    (orbit : X → Fin k) (word : X → List (Fin m))
    (hword : ∀ x, evalWord gen (word x) (base (orbit x)) = x)
    (candidate : I → Equiv.Perm X) (target : I → Fin k → X)
    (hcandidate : ∀ i x, candidate i x = evalWord gen (word x) (target i (orbit x)))
    (p : Equiv.Perm X) (hp : ∀ j, Commute p (gen j))
    (i : I) (hi : ∀ j, target i j = p (base j)) : p = candidate i := by
  ext x
  rw [hcandidate, hi]
  have he := congrArg (fun q : Equiv.Perm X => q (base (orbit x)))
    (commute_word gen p hp (word x)).eq
  change p (evalWord gen (word x) (base (orbit x))) = _ at he
  simpa only [hword, Equiv.Perm.mul_apply] using he

/-- A two-subgroup with an inner pointwise stabilizer suffices: place it in
a Sylow subgroup and transport the calculation by Sylow conjugacy. -/
theorem inner_of_fixing_twoSubgroup {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) (hK : IsPGroup 2 K)
    (hinner : ∀ a : MulAut G, (∀ x ∈ K, a x = x) → ∃ g, a = MulAut.conj g)
    (S : Sylow 2 G) (a : MulAut G) (ha : ∀ x ∈ S, a x = x) :
    ∃ g, a = MulAut.conj g := by
  obtain ⟨P, hKP⟩ := hK.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
  let e := MulAut.conj g
  have hm : (P : Subgroup G).map e.toMonoidHom = S :=
    congrArg (fun Q : Sylow 2 G => (Q : Subgroup G)) hg
  let b := e⁻¹ * a * e
  have hb : ∀ x ∈ K, b x = x := by
    intro x hx
    have hex : e x ∈ S := by
      change e x ∈ (S : Subgroup G)
      rw [← hm]
      exact Subgroup.mem_map_of_mem e.toMonoidHom (hKP hx)
    change e.symm (a (e x)) = x
    rw [ha (e x) hex, e.symm_apply_apply]
  obtain ⟨z, hz⟩ := hinner b hb
  refine ⟨e z, ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  have he := congrArg (fun c : MulAut G => e (c x)) hz
  change e (e.symm (a (e x))) = e (z * x * z⁻¹) at he
  simpa only [e.apply_symm_apply, map_mul, map_inv, MulAut.conj_apply] using he

end CFSG.Quasithin.SylowKernelCertificate
