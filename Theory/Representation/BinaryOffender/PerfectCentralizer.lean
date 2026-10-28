module

public import Theory.Representation.BinaryOffender.Homogeneous.Core
public import Theory.GroupTheory.SolvableResidual


/-!
# Perfect subgroups centralizing an Irr+ actor

The linear centralizer on an Irr+ section is cyclic. A perfect subgroup
which commutes with the actor and stabilizes the section therefore has
trivial image in that centralizer. This proves the cross-component
centralization step once the selected section is known to be the full
moved space, without requiring absolute irreducibility or a split module.

Source: Aschbacher–Smith, A.1.41 and proof of B.6.9, printed pp.31 and116
(1 March 2004 manuscript).
-/

public section

open Subgroup
open Representation.CentralizerField Representation.BinaryOffender.CentralizerField
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

theorem IsIrrPlus.le_fixedSpace_of_perfect_centralizes
    {L K : Subgroup G} {W : Submodule (ZMod 2) V} [Group.IsPerfect K]
    (hW : IsIrrPlus ρ L W) (hKL : K ≤ centralizer (L : Set G))
    (hKW : K ≤ subspaceStabilizer ρ W) : W ≤ fixedSpace ρ K := by
  let σ := (invariantSubspace ρ L W hW.choose).toRepresentation
  let C := linearCentralizer σ
  let a := (stabilizerRepresentation ρ W).asGroupHom.comp (inclusion hKW)
  have ha (k : K) : a k ∈ C := by
    apply (mem_linearCentralizer_iff σ _).mpr
    intro l v
    apply Subtype.ext
    change ρ k (ρ l v) = ρ l (ρ k v)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    rw [mem_centralizer_iff.mp (hKL k.property) l l.property]
  let f : K →* C := a.codRestrict C ha
  let : IsCyclic C :=
    (centralizer_cyclic_odd ρ L W hW.choose hW.choose_spec.1 hW.choose_spec.2).1
  let : Group.IsSolvable C :=
    Group.isSolvable_of_comm fun a b => (IsMulCommutative.is_comm (M := C)).comm a b
  have hf (k : K) : f k = 1 := by
    have hm := map_solvableResidual_le f
    rw [solvableResidual_eq_top, solvableResidual_eq_bot, ← MonoidHom.range_eq_map] at hm
    exact mem_bot.mp (hm (MonoidHom.mem_range.mpr ⟨k,rfl⟩))
  intro v hv k
  have hh := congrArg (fun c : C => c.val.val (⟨v,hv⟩ : W)) (hf k)
  exact congrArg Subtype.val hh

end Representation.BinaryOffender
