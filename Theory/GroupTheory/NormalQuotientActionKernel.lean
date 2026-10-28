module
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Mathlib.GroupTheory.PGroup
/-!
# The kernel above a normal centerless quotient action

When a normal subgroup induces the inner action on a centerless quotient,
a p-group quotient of the ambient group and a p-group inner kernel force
the whole action kernel to be a p-group. Raising first into the normal
subgroup and then into its kernel proves the assertion elementwise.

Source: the faithful quotient-action step of Aschbacher–Smith 2.4.12(1), p.532.
-/
public section
namespace Theory.GroupTheory
open Subgroup
variable {H Y : Type*} [Group H] [Group Y]

theorem kernel_isPGroup_of_normal_inner_quotient
    {p : ℕ} (L : Subgroup H) [L.Normal]
    (hq : IsPGroup p (H ⧸ L)) (f : L →* Y) (hk : IsPGroup p f.ker)
    (hc : center Y = ⊥) (ρ : H →* MulAut Y)
    (hi : ∀ l : L, ρ l = MulAut.conj (f l)) : IsPGroup p ρ.ker := by
  have hinj := conj_injective_of_center_eq_bot hc
  intro k
  obtain ⟨m,hm⟩ := hq (QuotientGroup.mk' L (k:H))
  have hkm : (k:H)^(p^m) ∈ L := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' L ((k:H)^(p^m))=1
    simpa only [map_pow] using hm
  let l : L := ⟨(k:H)^(p^m),hkm⟩
  have hl : f l=1 := by
    apply hinj
    rw [←hi,map_one]
    change ρ ((k:H)^(p^m))=1
    rw [map_pow,show ρ (k:H)=1 from k.property,one_pow]
  obtain ⟨n,hn⟩ := hk ⟨l,hl⟩
  refine ⟨m+n,?_⟩
  apply Subtype.ext
  have he := congrArg (fun x:f.ker => ((x:L):H)) hn
  change ((k:H)^(p^m))^(p^n)=1 at he
  change (k:H)^(p^(m+n))=1
  simpa only [pow_add,pow_mul] using he
end Theory.GroupTheory
