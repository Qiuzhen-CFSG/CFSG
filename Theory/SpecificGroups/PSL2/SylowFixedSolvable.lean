module

public import Theory.GroupAction.SylowFixedSolvable
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import Theory.SpecificGroups.PSL2.RankOneRoots

/-!
# Solvable fixed groups of binary PSL₂ Sylow fixers

Conjugate the pointwise fixed Sylow subgroup to the upper root group. The
proved automorphism calculation gives conjugation by an upper root element.
Nontriviality of the automorphism makes that element nonidentity, and its full
centralizer is exactly the root group. Thus the fixed group is a two-group,
and in particular solvable. The argument includes the field of order two.

Source: Aschbacher--Smith, E.6.22, printed p.254 (PDF p.265), using the
rank-one case of E.6.8(1), printed pp.247--248.
-/

public section
open Subgroup
namespace Theory.PSL2
open BenderSuzuki.Converse BenderSuzuki.ZD.Linear BenderSuzuki.MatrixGroups
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- A nonidentity automorphism fixing a binary PSL₂ Sylow subgroup pointwise
has solvable fixed subgroup. -/
theorem sylow_fixed_solvable (S : Sylow 2 (PSL2MatrixGroup F))
    (a : MulAut (PSL2MatrixGroup F)) (ha : a ≠ 1)
    (hfix : ∀ x ∈ S, a x = x) : _root_.Group.IsSolvable a.fixedSubgroup := by
  let U := Matrix.SpecialLinearGroup.upperUnipotentSylow F 2
  let P := U.mapSurjective (f := pi F) pi_surjective
  have hP : (P : Subgroup (PSL2MatrixGroup F)) = PUnip F := by
    rw [Sylow.coe_mapSurjective]
    change (Matrix.SpecialLinearGroup.upperUnipotent F).map (pi F) =
      (Unip F).map (pi F)
    congr 1
    ext g
    rw [Matrix.SpecialLinearGroup.mem_upperUnipotent, mem_Unip_iff]
    simp only [upper_transvection_eq_uni, eq_comm]
  apply MulAut.fixed_solvable_of_sylow P S _ a ha hfix
  intro b hb hfixP
  change ∀ x ∈ (P : Subgroup _), b x = x at hfixP
  rw [hP] at hfixP
  obtain ⟨x, hx, rfl⟩ :=
    BenderSuzuki.ZD.BaseAutomorphisms.psl2_aut_fixing_unipotent_inner b hfixP
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := (mem_Unip_iff u).mp hu
  have ht : t ≠ 0 := by
    intro he
    simp [he, uni_zero] at hb
  rw [MulAut.fixedSubgroup_conj, centralizer_root_eq ht]
  let : _root_.Group.IsNilpotent (PUnip F) := (hP ▸ P.isPGroup').isNilpotent
  infer_instance
end Theory.PSL2

