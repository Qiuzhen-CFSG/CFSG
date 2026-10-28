module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.GroupTheory.Commutator.CentralDihedralSylow
public import GorensteinWalter.SL2ProjectiveCover

/-!
# Two-primary central kernels over the binary three-dimensional linear group

The actual PSL₂(7) ≃ SL₃(2) comparison transports the dihedral Sylow
calculation. Transfer bounds the derived part of a central two-kernel by
two; perfectness makes this the whole kernel. No triviality of that
kernel is asserted.

Source: Aschbacher--Smith C.1.13(b), pp.124--125, and the two-primary
cover calculation in Alperin--Brauer--Gorenstein II.3, Proposition 2.
The exceptional isomorphism retains the ATLAS attribution in
Theory/AtlasPort/ExceptionalIsomorphisms/Order168.lean.
-/

public section
open Subgroup Matrix
namespace BinaryLinearThree.CentralCover
private instance sevenPrime : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- A perfect central two-cover of the actual SL₃(2) has kernel of order at most two. -/
theorem kernel_card_le_two
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hf : Function.Surjective f) (hc : f.ker ≤ center E)
    (hk : IsPGroup 2 f.ker) : Nat.card f.ker ≤ 2 := by
  let e := Atlas.Comparisons.Exceptional.psl2SevenEquivSl3Two
  let f' := e.symm.toMonoidHom.comp f
  have he : f'.ker = f.ker := MonoidHom.ker_comp_of_injective _ _ e.symm.injective
  have hf' : Function.Surjective f' := e.symm.surjective.comp hf
  obtain ⟨_, _, _, _, _, hd⟩ :=
    GorensteinWalter.sl2_projective_cover_model (ZMod 7) (by norm_num) (by norm_num)
  let S : Sylow 2 E := Classical.choice inferInstance
  obtain ⟨n, hn, ⟨d⟩⟩ := hd (Sylow.mapSurjective hf' S)
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hh := CentralExtension.card_ker_inf_commutator_le_two_of_dihedral_sylow
    f' hf' (by rw [he]; exact hc) (by rw [he]; exact hk) S d
  simpa only [he, Group.IsPerfect.commutator_eq_top, inf_top_eq] using hh

end BinaryLinearThree.CentralCover

