module
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.BinarySixObstruction
public import Theory.SpecificGroups.ClassicalOrthogonal.BinaryD3Comparison
public import Theory.Representation.NormalComponentConstituents.CenterlessImage
public import Theory.GroupTheory.SolvableResidual
public import Theory.Alternating.Aut
public import Theory.Quasithin.Rank
public import Theory.LinearAlgebra.QuadraticForm.IsometryGroup.Transport
public import Theory.SpecificGroups.ClassicalOrthogonal.BinarySixCoordinates
/-!
# Residual obstructions for binary quadratic six-spaces

The full split-six group is the actual deleted S₈ action. Its solvable residual
is A₈; every automorphism of A₈ comes from conjugation in S₈ and thus acts
linearly on the same module. For the minus space the literal commutator is
perfect, so it equals the solvable residual; its scalar quotient is injective
and gives the centerless model with cubic rank at least three.

Actual quadratic isometries transport these results to an arbitrary binary
six-space. The resulting alternative is used by the original selected
constituent in G.10.15, with its original central kernel and odd-rank bounds.
Source: Aschbacher--Smith G.10.15, printed p.363; the cited model constructions
and automorphism results in the imported modules.
-/

public noncomputable section
open Subgroup Theory.AlgebraicGroup
open Representation.BinaryOffender

namespace QuadraticForm.BinarySixResidual
private theorem symmetric_residual :
    solvableResidual (Equiv.Perm (Fin 8))=alternatingGroup (Fin 8) := by
  let : Group.IsPerfect (alternatingGroup (Fin 8)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  apply le_antisymm
  · exact (solvableResidual_le_derivedSeries 1).trans_eq
      (alternatingGroup.commutator_perm_eq (by simp))
  · exact le_solvableResidual_of_isPerfect _

/-- The embedded residual of an actual S₈ linear overgroup is centerless,
and every residual automorphism is induced by a linear map on that space. -/
theorem symmetric_eight_residual {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (D : Subgroup (V ≃ₗ[ZMod 2] V)) (e : D ≃* Equiv.Perm (Fin 8)) :
    center ((solvableResidual D).map D.subtype)=⊥ ∧
      ImageAutomorphismsLinear ((solvableResidual D).map D.subtype) := by
  let : Finite D := Finite.of_injective e e.injective
  have he : (solvableResidual D).map e.toMonoidHom=alternatingGroup (Fin 8) :=
    (map_solvableResidual_eq e.toMonoidHom e.surjective).trans symmetric_residual
  let R := (solvableResidual D).map D.subtype
  let j : R ≃* solvableResidual D :=
    ((solvableResidual D).equivMapOfInjective D.subtype D.subtype_injective).symm
  let f : R ≃* alternatingGroup (Fin 8) :=
    j.trans (((solvableResidual D).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr he))
  have hf (k : R) : (f k).val=e (j k).val := rfl
  have hj (k : R) : (j k).val.val=k.val := by
    have h := ((solvableResidual D).equivMapOfInjective D.subtype D.subtype_injective).apply_symm_apply k
    exact congrArg Subtype.val h
  constructor
  · apply bot_unique
    intro k hk
    apply mem_bot.mpr
    apply f.injective
    rw [map_one]
    apply mem_bot.mp
    rw [← alternatingGroup.center_eq_bot (by simp : 4≤Nat.card (Fin 8))]
    exact (Subgroup.centerCongr f ⟨k,hk⟩).property
  · intro α
    obtain ⟨σ,hσ⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
      8 (by decide) (by decide)).surjective (MulAut.congr f α)
    let c := e.symm σ
    refine ⟨c.val,?_⟩
    intro k x
    have hα : (α k).val = c.val*k.val*c.val⁻¹ := by
      have h := congrArg (fun β : MulAut (alternatingGroup (Fin 8)) => (β (f k)).val) hσ
      have hconj : e (j (α k)).val=σ*e (j k).val*σ⁻¹ := by
        simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hf,
          MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv] using h.symm
      have hD : (j (α k)).val=c*(j k).val*c⁻¹ := by
        apply e.injective
        simpa only [map_mul,map_inv,c,e.apply_symm_apply] using hconj
      have hh := congrArg Subtype.val hD
      simpa only [Subgroup.coe_mul,Subgroup.coe_inv,hj] using hh
    rw [hα]
    change c.val (k.val x)=c.val (k.val (c.val.symm (c.val x)))
    rw [c.val.symm_apply_apply]

open ClassicalOrthogonal.Minus.BinarySixObstruction
open ClassicalOrthogonal.TheoremDRootNormalizer

private theorem minus_residual : solvableResidual FullGroup = commutator FullGroup := by
  let : Group.IsPerfect OmegaGroup := ⟨omega_perfect⟩
  apply le_antisymm
  · exact solvableResidual_le_derivedSeries 1
  · exact le_solvableResidual_of_isPerfect _

/-- An isomorphism with the full minus-six isometry group identifies its
embedded solvable residual with the actual centerless rank-three model. -/
theorem minus_six_residual {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (D : Subgroup (V ≃ₗ[ZMod 2] V)) (e : D ≃* FullGroup) :
    center ((solvableResidual D).map D.subtype)=⊥ ∧
      3 ≤ primeRank 3 ((solvableResidual D).map D.subtype) := by
  let : Finite D := Finite.of_injective e e.injective
  have he : (solvableResidual D).map e.toMonoidHom=commutator FullGroup :=
    (map_solvableResidual_eq e.toMonoidHom e.surjective).trans minus_residual
  let R := (solvableResidual D).map D.subtype
  let j : R ≃* solvableResidual D :=
    ((solvableResidual D).equivMapOfInjective D.subtype D.subtype_injective).symm
  let f : R ≃* ClassicalGroup.POmegaMinus 3 (ZMod 2) :=
    j.trans ((((solvableResidual D).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr he)).trans (minusOmegaEquivProjective 3))
  let : Finite R := Finite.of_injective f f.injective
  have hc : center (ClassicalGroup.POmegaMinus 3 (ZMod 2))=⊥ := by
    let := isSimpleGroup
    exact (inferInstance : (center (ClassicalGroup.POmegaMinus 3 (ZMod 2))).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => not_isMulCommutative (center_eq_top_iff.mp ht))
  constructor
  · apply bot_unique
    intro k hk
    apply mem_bot.mpr
    apply f.injective
    rw [map_one]
    apply mem_bot.mp
    rw [← hc]
    exact (Subgroup.centerCongr f ⟨k,hk⟩).property
  · rw [primeRank_congr 3 f]
    exact primeRank_three_ge

/-- Each binary quadratic six-space has a centerless residual. Its actual
action either extends every automorphism linearly or has cubic rank at least
three, according to the sign of the quadratic form. -/
theorem orthogonal_six {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (q : QuadraticForm (ZMod 2) V)
    (hq : q.polarBilin.Nondegenerate) (hd : Module.finrank (ZMod 2) V=6) :
    center ((solvableResidual q.isometrySubgroup).map q.isometrySubgroup.subtype)=⊥ ∧
      (ImageAutomorphismsLinear ((solvableResidual q.isometrySubgroup).map
        q.isometrySubgroup.subtype) ∨
        3 ≤ primeRank 3 ((solvableResidual q.isometrySubgroup).map
          q.isometrySubgroup.subtype)) := by
  rcases QuadraticForm.BinarySixCoordinates.classify q hq hd with hp|hm
  · obtain ⟨a⟩ := hp
    have heq : (ClassicalOrthogonal.formD 3 (ZMod 2)).isometrySubgroup=
        quadraticIsometrySubgroup (ClassicalOrthogonal.formD 3 (ZMod 2)) := by
      ext g
      exact (QuadraticMap.mem_isometrySubgroup _ g).trans
        (mem_quadraticIsometrySubgroup _ g).symm
    let e : q.isometrySubgroup ≃* Equiv.Perm (Fin 8) :=
      a.isometrySubgroupCongr.trans ((MulEquiv.subgroupCongr heq).trans
        ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv.symm)
    obtain ⟨hc,hl⟩ := symmetric_eight_residual q.isometrySubgroup e
    exact ⟨hc,Or.inl hl⟩
  · obtain ⟨a⟩ := hm
    have heq : (ClassicalOrthogonal.Minus.quadraticForm (ZMod 2) 3).isometrySubgroup=
        quadraticIsometrySubgroup (ClassicalOrthogonal.Minus.quadraticForm (ZMod 2) 3) := by
      ext g
      exact (QuadraticMap.mem_isometrySubgroup _ g).trans
        (mem_quadraticIsometrySubgroup _ g).symm
    let e : q.isometrySubgroup ≃* FullGroup :=
      a.isometrySubgroupCongr.trans (MulEquiv.subgroupCongr heq)
    obtain ⟨hc,hr⟩ := minus_six_residual q.isometrySubgroup e
    exact ⟨hc,Or.inr hr⟩

end QuadraticForm.BinarySixResidual
