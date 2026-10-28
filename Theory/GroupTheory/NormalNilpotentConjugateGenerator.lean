module
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Order.Atoms.Finite

/-!
# Recovering a normal nilpotent generator from a conjugate

Suppose a subgroup A lies in a normal nilpotent subgroup N, and together
with H generates the finite ambient group. If an ambient conjugate of A
lies in H, then H is the full group.

For a proper H choose a maximal overgroup M. The intersection N∩M is
normalized by M and is proper in N. The normalizer condition for nilpotent
groups supplies a normalizing element outside M, so maximality makes N∩M
normal in the ambient group. The conjugate containment then places A in M,
contradicting generation. This is the normal-nilpotent generator argument
used in the valid dihedral assembly of Stellmacher (7.8), journal p.36;
source role: `refs/latex/stellmacher-n-group.tex`.
-/

namespace Subgroup

public theorem eq_top_of_conjugate_normal_nilpotent_generator_le
    {G : Type*} [Group G] [Finite G]
    (N A₀ H : Subgroup G) (hN : N.Normal) (hNil : Group.IsNilpotent N)
    (hA₀N : A₀ ≤ N) (hgen : A₀ ⊔ H = ⊤)
    (x : G) (hconj : A₀.conjBy x ≤ H) : H = ⊤ := by
  classical
  by_contra hH
  obtain ⟨M,hM,hHM⟩ := (eq_top_or_exists_le_coatom H).resolve_left hH
  have hNnot : ¬ N ≤ M := by
    intro hNM
    apply hM.1
    apply top_le_iff.mp
    rw [← hgen]
    exact sup_le (hA₀N.trans hNM) hHM
  let K : Subgroup G := N ⊓ M
  have hKN : K ≤ N := inf_le_left
  have hKproper : K.subgroupOf N < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hNnot
    exact (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right
  let _ : Group.IsNilpotent N := hNil
  have hnormlt : K.subgroupOf N < normalizer (K.subgroupOf N : Set N) :=
    Group.normalizerCondition_of_isNilpotent (K.subgroupOf N) hKproper
  obtain ⟨n,hnnorm,hnK⟩ := SetLike.exists_of_lt hnormlt
  have hnNorm : (n : G) ∈ normalizer (K : Set G) := by
    rw [← subgroupOf_normalizer_eq hKN] at hnnorm
    exact hnnorm
  have hnnotM : (n : G) ∉ M := by
    intro hnM
    exact hnK ⟨n.property,hnM⟩
  have hMnorm : M ≤ normalizer (K : Set G) := by
    rw [le_normalizer_iff]
    intro m hm k hk
    exact ⟨hN.conj_mem k hk.1 m,
      M.mul_mem (M.mul_mem hm hk.2) (M.inv_mem hm)⟩
  have hMlt : M < normalizer (K : Set G) := by
    apply lt_of_le_of_ne hMnorm
    intro heq
    exact hnnotM (heq ▸ hnNorm)
  have hKnormal : K.Normal := normalizer_eq_top_iff.mp (hM.2 _ hMlt)
  have hA₀M : A₀ ≤ M := by
    intro a ha
    have haconj : x*a*x⁻¹ ∈ K :=
      ⟨hN.conj_mem a (hA₀N ha) x, hHM (hconj (mem_map_of_mem (MulAut.conj x).toMonoidHom ha))⟩
    have haback := hKnormal.conj_mem (x*a*x⁻¹) haconj x⁻¹
    have haK : a ∈ K := by simpa [mul_assoc] using haback
    exact haK.2
  apply hM.1
  apply top_le_iff.mp
  rw [← hgen]
  exact sup_le hA₀M hHM

end Subgroup
