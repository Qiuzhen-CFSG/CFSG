module

public import Theory.GroupTheory.SolvableRadical.Transport

/-!
# Radical quotients of homomorphisms with solvable kernel

The preimage of a solvable subgroup under a homomorphism with solvable kernel
is solvable, by the extension theorem. For a surjection of finite groups this
identifies the preimage of the solvable radical, and hence the two radical
quotients. The equivalence is induced by the original homomorphism.

Source: standard solvable extension theory; the radical identification used in
Aschbacher--Smith, *The Classification of Quasithin Groups*, E.1.10(4), p.211.
-/

@[expose] public section
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- Solvable kernels pull solvable subgroups back to solvable subgroups. -/
theorem isSolvable_comap_of_solvable_ker (f : G →* H)
    [Group.IsSolvable f.ker] (N : Subgroup H) [Group.IsSolvable N] :
    Group.IsSolvable (N.comap f) := by
  let i : f.ker →* N.comap f :=
    f.ker.subtype.codRestrict _ (by
      intro x
      change f x ∈ N
      rw [show f x = 1 from x.property]
      exact N.one_mem)
  let g : N.comap f →* N :=
    (f.comp (N.comap f).subtype).codRestrict _ (fun x => x.property)
  apply Group.isSolvable_of_ker_le_range i g
  intro x hx
  have hx' : f x.val = 1 := congrArg Subtype.val (show g x = 1 from hx)
  exact ⟨⟨x.val, hx'⟩, Subtype.ext rfl⟩

variable [Finite G] [Finite H]

/-- A surjection with solvable kernel pulls the radical back to the radical. -/
theorem comap_solvableRadical_eq_of_solvable_ker (f : G →* H)
    (hf : Function.Surjective f) [Group.IsSolvable f.ker] :
    (solvableRadical H).comap f = solvableRadical G := by
  apply le_antisymm
  · exact le_solvableRadical _ inferInstance (isSolvable_comap_of_solvable_ker f _)
  · exact map_le_iff_le_comap.mp (map_solvableRadical_le_of_surjective f hf)

/-- The radical quotients are canonically isomorphic across a solvable kernel. -/
noncomputable def solvableRadicalQuotientEquiv (f : G →* H)
    (hf : Function.Surjective f) [Group.IsSolvable f.ker] :
    G ⧸ solvableRadical G ≃* H ⧸ solvableRadical H :=
  QuotientGroup.liftEquiv (solvableRadical G)
    (φ := (QuotientGroup.mk' (solvableRadical H)).comp f)
    ((QuotientGroup.mk'_surjective (solvableRadical H)).comp hf)
    (by rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      comap_solvableRadical_eq_of_solvable_ker f hf])

end Subgroup
