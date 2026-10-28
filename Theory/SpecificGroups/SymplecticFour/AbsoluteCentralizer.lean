module
public import Theory.Representation.AbsolutelyIrreducible
public import Theory.SpecificGroups.SymplecticFour.Flag
public import Mathlib.Algebra.CharP.Two

/-!
# The symplectic centralizer of an absolutely irreducible subgroup

The commuting algebra of an absolutely irreducible action consists of
scalars. A scalar symplectic isometry has square one, hence equals one
in characteristic two. This retains the literal embedded subgroup and
supplies centralizer rigidity in the model inspection of G.4.1.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour
variable {F:Type*} [Field F] [CharP F 2]

/-- Absolute irreducibility makes the full ambient symplectic centralizer trivial. -/
theorem centralizer_eq_bot_of_absolutelyIrreducible
    (N:Subgroup (Sp F))
    (ha:Representation.IsAbsolutelyIrreducible ((Representation.symplecticNatural 2).comp N.subtype)) :
    centralizer (N:Set (Sp F))=⊥ := by
  let ρ : Representation F N (Vector F) := (Representation.symplecticNatural 2).comp N.subtype
  let : ρ.IsAbsolutelyIrreducible := ha
  let : ρ.IsIrreducible :=
    Representation.IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible ρ
  apply le_bot_iff.mp
  intro g hg
  let f:ρ.End := {
    toLinearMap := (toLinear g).toLinearMap
    isIntertwining' n := by
      apply LinearMap.ext
      intro v
      change g•((n:Sp F)•v)=(n:Sp F)•(g•v)
      have hc := (mem_centralizer_iff.mp hg (n:Sp F) n.property).symm
      simpa only [←mul_smul] using congrArg (fun h:Sp F=>h•v) hc }
  obtain ⟨c,hc⟩ := (Representation.isAbsolutelyIrreducible_iff_surjective ρ).mp ha f
  have hscalar (v:Vector F) : g•v=c•v := by
    exact (congrArg (fun z:ρ.End=>z v) hc).symm
  let v:Vector F := Pi.single (Sum.inl 0) 1
  let w:Vector F := Pi.single (Sum.inr 0) 1
  have hs := preserves_form g v w
  rw [hscalar,hscalar] at hs
  have hc2 : c^2=1 := by
    simpa [form_apply,v,w,Fin.sum_univ_two,CharTwo.neg_eq,pow_two] using hs
  have hc1 : c=1 := CharTwo.sq_injective (hc2.trans (one_pow 2).symm)
  change g=1
  apply Subtype.ext
  ext i j
  have hh := congrFun (hscalar (Pi.single j 1)) i
  simpa [hc1,smul_eq_mulVec,Matrix.one_apply,Pi.single_apply] using hh
end Theory.SpecificGroups.SymplecticFour
