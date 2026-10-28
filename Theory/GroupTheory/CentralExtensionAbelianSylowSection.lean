module
public import Theory.GroupTheory.CentralExtensionSections
public import Theory.GroupTheory.PerfectCentralCoverAbelianSylow

/-!
# Derived sections of central extensions with abelian Sylow preimages

The derived subgroup of a central extension of a perfect group covers that
base perfectly. An abelian Sylow preimage excludes the Sylow prime from
its central kernel by transfer. If the original kernel is a p-group, this
kernel is therefore trivial. The resulting section has exactly the
original extension's derived subgroup as its range.

Source application: the central short-root line in Aschbacher–Smith
F.4.42, printed p.295. No universal-cover or Schur-multiplier premise is used.
-/

open Subgroup
open scoped IsMulCommutative
public noncomputable section
namespace CentralExtension
variable {E B : Type*} [Group E] [Finite E] [Group B] [Finite B] [Group.IsPerfect B]

/-- A central p-extension splits over its perfect base if one Sylow
p-subgroup has an abelian full preimage. The section's range is exactly
the derived subgroup of the original extension. -/
theorem exists_derived_section_of_abelian_sylow_preimage
    {p : ℕ} [Fact p.Prime] (f : E →* B) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hp : IsPGroup p f.ker)
    (P : Sylow p B) (hP : IsMulCommutative ((P : Subgroup B).comap f)) :
    ∃ s : B →* E, f.comp s = MonoidHom.id B ∧ s.range = commutator E := by
  let d := derivedCover f hf hc
  let : Group.IsPerfect (commutator E) := d.isPerfect
  have hpd : IsPGroup p d.toMonoidHom.ker := hp.comap_subtype
  have had : IsMulCommutative ((P : Subgroup B).comap d.toMonoidHom) := by
    let : IsMulCommutative ((P : Subgroup B).comap f) := hP
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : (P : Subgroup B).comap f => a.val) (mul_comm
      (⟨x.val.val,x.property⟩ : (P : Subgroup B).comap f)
      (⟨y.val.val,y.property⟩ : (P : Subgroup B).comap f))
  have hnd := PerfectCentralCovering.not_dvd_card_kernel_of_abelian_sylow_preimage
    d.toMonoidHom d.surjective d.ker_le_center P had
  have hk : d.toMonoidHom.ker = ⊥ := card_eq_one.mp (hpd.card_eq_or_dvd.resolve_right hnd)
  let e := MulEquiv.ofBijective d.toMonoidHom
    ⟨(MonoidHom.ker_eq_bot_iff _).mp hk,d.surjective⟩
  refine ⟨(commutator E).subtype.comp e.symm.toMonoidHom,?_,?_⟩
  · ext b
    exact e.apply_symm_apply b
  · rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.symm.surjective]
    exact (MonoidHom.range_eq_map (commutator E).subtype).symm.trans (range_subtype _)
end CentralExtension
