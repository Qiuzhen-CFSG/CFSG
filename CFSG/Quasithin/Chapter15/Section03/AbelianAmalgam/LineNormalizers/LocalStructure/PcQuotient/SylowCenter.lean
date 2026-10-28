module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PcQuotient.GeometryInput
public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.FixedLine
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# Sylow-center movement on the selected singular line

A nontrivial subgroup normalized by a Sylow two-subgroup of the actual
binary plus-four isometry group meets that Sylow subgroup's center. The
Sylow subgroup fixes a nonzero singular vector, and the selected singular
line contains this vector. A kernel-checked coordinate calculation shows
that every nonidentity element of this center preserves the line and moves
one of its vectors. This proves the finite model input for the first P_c
paragraph of 15.3.67, without any additional geometric premise.

Normality throughout is relative to the Sylow subgroup. The coordinates
are the existing bijection with actual linear isometries of the quadratic
form; no abstract group-family identification is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1121–1122 and 1152–1153, especially the proof of 15.3.67 on p.1153.
-/

public section

open Subgroup OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
open OrthogonalFourBinary.SylowGeometry

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure

set_option synthInstance.maxSize 10000

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The identity is the only central coordinate that can fail to move a line.
private theorem finite_central_movement : ∀ x : Space, x ≠ 0 → q x = 0 → ∀ k : Code,
    eval k x = x →
    (∀ j : Code, eval j x = x → ∀ v : Space,
      eval j (eval k v) = eval k (eval j v)) →
    k = ((0,0),(0,0),false) ∨
      ∀ i : LineCode, x.2 = planeEval i x.1 →
        preservesGraph k i ∧ ∃ v : Space,
          v.2 = planeEval i v.1 ∧ eval k v ≠ v := by
  decide +kernel

private theorem central_point_line_movement (x : Space) (hx : x ≠ 0)
    (hqx : form x = 0) (i : LineCode) (hxi : Multiplicative.ofAdd x ∈ graphLine i)
    (g : Actor) (hg : g ∈ MulAction.stabilizer Actor x) (hne : g ≠ 1)
    (hcentral : ∀ a ∈ MulAction.stabilizer Actor x, a * g = g * a) :
    g ∈ lineStabilizer (graphLine i) ∧
      ∃ v ∈ graphLine i, vectorAction g v ≠ v := by
  obtain ⟨k,rfl⟩ := codeMap_bijective.surjective g
  have hfix : eval k x = x := (candidate_eval k x).symm.trans hg
  have hcomm : ∀ j : Code, eval j x = x → ∀ v : Space,
      eval j (eval k v) = eval k (eval j v) := by
    intro j hj v
    have hj' : codeMap j ∈ MulAction.stabilizer Actor x := by
      change candidate j x = x
      rwa [candidate_eval]
    have he := congrArg (fun a : Actor => a.val v) (hcentral (codeMap j) hj')
    change candidate j (candidate k v) = candidate k (candidate j v) at he
    simpa only [candidate_eval] using he
  rcases finite_central_movement x hx hqx k hfix hcomm with hid | hmove
  · subst k
    apply (hne ?_).elim
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change candidate ((0,0),(0,0),false) v = v
    rw [candidate_eval]
    rfl
  · change x.2 = planePermutation i x.1 at hxi
    rw [planePermutation_eval] at hxi
    obtain ⟨hpres,v,hv,hvne⟩ := hmove i hxi
    refine ⟨(codeMap_mem_line k i).mpr hpres, Multiplicative.ofAdd v, ?_, ?_⟩
    · change v.2 = planePermutation i v.1
      rwa [planePermutation_eval]
    · change candidate k v ≠ v
      rwa [candidate_eval]

/-- Every nontrivial normal subgroup of the Sylow group has an element
preserving the selected singular line and acting nontrivially on it. -/
theorem normalSylowLineMovement : NormalSylowLineMovement := by
  intro P L hcard hs S hS Q hQP hN hQ
  let D := Q.subgroupOf (P : Subgroup Actor)
  let : D.Normal := (normal_subgroupOf_iff_le_normalizer hQP).mpr hN
  have hD : D ≠ ⊥ := by
    intro h
    apply hQ
    rw [← map_subgroupOf_eq_of_le hQP]
    change D.map (P : Subgroup Actor).subtype = ⊥
    rw [h, Subgroup.map_bot]
  obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp
    (center_inf_ne_bot_of_normal P.isPGroup' D hD)
  have hzne : z.val.val ≠ 1 := fun h => hz (Subtype.ext (Subtype.ext h))
  obtain ⟨i,rfl⟩ := singular_four_eq_graph L hcard hs
  obtain ⟨x,hx,hqx,hP⟩ := sylow_eq_point_stabilizer P
  have hxi : Multiplicative.ofAdd x ∈ graphLine i :=
    line_sylow_fixed_mem P (graphLine i) hcard hs S hS _ (by
      intro a ha
      have hh : a ∈ MulAction.stabilizer Actor x := hP ▸ ha
      exact hh)
  have hzg : z.val.val ∈ MulAction.stabilizer Actor x := hP ▸ z.val.property
  have hcentral : ∀ a ∈ MulAction.stabilizer Actor x,
      a * z.val.val = z.val.val * a := by
    intro a ha
    have haP : a ∈ (P : Subgroup Actor) := hP ▸ ha
    exact congrArg Subtype.val (mem_center_iff.mp z.property.1 ⟨a,haP⟩)
  obtain ⟨hline,v,hv,hmove⟩ := central_point_line_movement x hx hqx i hxi
    z.val.val hzg hzne hcentral
  exact ⟨z.val.val, ⟨z.property.2,hline⟩, v, hv, hmove⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure
