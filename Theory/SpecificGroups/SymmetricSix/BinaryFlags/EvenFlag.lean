module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry
/-!
# Even markings of the original binary flag

The stabilizer of the canonical point-plane flag contains an odd
transposition. Correcting a Sylow flag conjugator by that transposition
therefore marks both subspaces by the same even permutation. This keeps
both literal natural subspaces, and supplies a lift through the original
alternating quotient in the Section 13.5 source application.

Source: Aschbacher--Smith, Notation 13.2.1 and proof of 13.5.7,
printed pp.877 and 917--918.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

theorem exists_even_same_flag (g:S) : ∃a:alternatingGroup Ω,
    move g canonicalLine=move a.val canonicalLine ∧
    move g canonicalPlane=move a.val canonicalPlane := by
  classical
  by_cases hg:g∈alternatingGroup Ω
  · exact ⟨⟨g,hg⟩,rfl,rfl⟩
  let t:S:=Equiv.swap 0 1
  have ht1:t∈H1 := by decide
  have ht2:t∈H2 := by decide
  have hts:Equiv.Perm.sign t = -1 := by decide
  have hgs:Equiv.Perm.sign g = -1 :=
    (Int.units_eq_one_or _).resolve_left (fun h=>hg (Equiv.Perm.mem_alternatingGroup.mpr h))
  have hgt:g*t∈alternatingGroup Ω := by
    rw [Equiv.Perm.mem_alternatingGroup,map_mul,hgs,hts]
    norm_num
  refine ⟨⟨g*t,hgt⟩,?_,?_⟩
  · rw [move_mul]
    exact congrArg (move g) (canonicalLine_map_of_mem ht1).symm
  · rw [move_mul]
    exact congrArg (move g) ((canonicalPlane_stabilizer t).mpr ht2).symm

theorem sylow_even_flag_of_between (H:Subgroup S) (hH:alternatingGroup Ω≤H)
    (T:Sylow 2 H) (P Q:Submodule (ZMod 2) V)
    (hP:Module.finrank (ZMod 2) P=1) (hQ:Module.finrank (ZMod 2) Q=2)
    (hPi:∀x∈(T:Subgroup H).map H.subtype,move x P=P)
    (hQi:∀x∈(T:Subgroup H).map H.subtype,move x Q=Q) :
    ∃a:alternatingGroup Ω,P=move a.val canonicalLine ∧ Q=move a.val canonicalPlane := by
  obtain ⟨g,hgP,hgQ⟩:=sylow_flag_of_between H hH T P Q hP hQ hPi hQi
  obtain ⟨a,haP,haQ⟩:=exists_even_same_flag g.val
  exact ⟨a,hgP.trans haP,hgQ.trans haQ⟩
end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
