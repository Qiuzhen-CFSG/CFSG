module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Copies.Bounds
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl.DualExclusion
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl.SelfExtensions

/-!
# Homogeneous splitting of the actual two starred factors

The natural and dual-natural factors have combined fixed codimension
strictly larger than the rank of an elementary two-subgroup. Hence an
FF budget excludes mixed orientations. Taking the annihilator reverses
the actual short exact sequence and dualizes both factors, so the same
exclusion holds when the dual module has the budget.

The two source cases in Bounds therefore force matching orientations.
The proved binary natural self-extension theorem then supplies an actual
intertwining equivalence with two natural copies, or two dual-natural
copies, of SL3(2). This is the whole starred module. Identifying the
literal second-color starred layer and its full SL2(2) coordinates is a
separate restriction calculation.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the constituent conclusion across printed pp.911--912; the binary
extension calculation is Aschbacher--Smith B.4.9(2), printed pp.92--94.
-/

public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
open AbelianCore.QuotientRecognition.ExtensionControl

private def dualEquiv {V X : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) SL V} {τ : Representation (ZMod 2) SL X}
    (e : σ.Equiv τ) : σ.dual.Equiv τ.dual :=
  .mk e.symm.toLinearEquiv.dualMap (by
    intro g
    ext f w
    exact congrArg f (LinearMap.congr_fun (e.symm.isIntertwining' g⁻¹) w).symm)

private noncomputable def doubleDualEquiv {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL V) : σ.Equiv σ.dual.dual :=
  .mk (Module.evalEquiv (ZMod 2) V) (by
    intro g
    ext v f
    change f (σ g v) = f (σ (g⁻¹)⁻¹ v)
    rw [inv_inv])

section LinearExtension

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) SL V}

private def annihilatorRepresentation (N : Subrepresentation ρ) :
    Subrepresentation ρ.dual where
  toSubmodule := N.toSubmodule.dualAnnihilator
  apply_mem_toSubmodule g f hf := by
    rw [Submodule.mem_dualAnnihilator] at hf ⊢
    intro v hv
    exact hf (ρ g⁻¹ v) (N.apply_mem_toSubmodule g⁻¹ hv)

private noncomputable def annihilatorLowerEquiv (N : Subrepresentation ρ) :
    (annihilatorRepresentation N).toRepresentation.Equiv N.quotientRepresentation.dual :=
  .mk N.toSubmodule.dualQuotEquivDualAnnihilator.symm (by
    intro g
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ v => rfl)

private noncomputable def annihilatorUpperEquiv (N : Subrepresentation ρ) :
    (annihilatorRepresentation N).quotientRepresentation.Equiv N.toRepresentation.dual :=
  .mk (Subspace.quotAnnihilatorEquiv N.toSubmodule) (by
    intro g
    apply LinearMap.ext
    intro f
    induction f using Submodule.Quotient.induction_on with
    | _ f =>
      ext v
      rfl)

private theorem not_ff_dual_of_opposite [FiniteDimensional (ZMod 2) V]
    (N : Subrepresentation ρ)
    (h : (Nonempty (N.toRepresentation.Equiv BinaryLinearThree.W) ∧
          Nonempty (N.quotientRepresentation.Equiv BinaryLinearThree.W.dual)) ∨
         (Nonempty (N.toRepresentation.Equiv BinaryLinearThree.W.dual) ∧
          Nonempty (N.quotientRepresentation.Equiv BinaryLinearThree.W))) :
    ¬ IsFFModule ρ.dual := by
  apply not_ff_of_opposite_natural_layers ρ.dual (annihilatorRepresentation N)
  rcases h with ⟨⟨eN⟩, ⟨eQ⟩⟩ | ⟨⟨eN⟩, ⟨eQ⟩⟩
  · exact Or.inl ⟨⟨(annihilatorLowerEquiv N).trans
        ((dualEquiv eQ).trans (doubleDualEquiv BinaryLinearThree.W).symm)⟩,
      ⟨(annihilatorUpperEquiv N).trans (dualEquiv eN)⟩⟩
  · exact Or.inr ⟨⟨(annihilatorLowerEquiv N).trans (dualEquiv eQ)⟩,
      ⟨(annihilatorUpperEquiv N).trans
        ((dualEquiv eN).trans (doubleDualEquiv BinaryLinearThree.W).symm)⟩⟩

private theorem homogeneous_of_budget [FiniteDimensional (ZMod 2) V]
    (N : Subrepresentation ρ) (hN : NaturalOrDual N.toRepresentation)
    (hQ : NaturalOrDual N.quotientRepresentation)
    (hFF : IsFFModule ρ ∨ IsFFModule ρ.dual) :
    (Nonempty (N.toRepresentation.Equiv BinaryLinearThree.W) ∧
      Nonempty (N.quotientRepresentation.Equiv BinaryLinearThree.W)) ∨
    (Nonempty (N.toRepresentation.Equiv BinaryLinearThree.W.dual) ∧
      Nonempty (N.quotientRepresentation.Equiv BinaryLinearThree.W.dual)) := by
  have hn : ¬ ((Nonempty (N.toRepresentation.Equiv BinaryLinearThree.W) ∧
      Nonempty (N.quotientRepresentation.Equiv BinaryLinearThree.W.dual)) ∨
    (Nonempty (N.toRepresentation.Equiv BinaryLinearThree.W.dual) ∧
      Nonempty (N.quotientRepresentation.Equiv BinaryLinearThree.W))) := by
    intro h
    rcases hFF with hFF | hFF
    · exact not_ff_of_opposite_natural_layers ρ N h hFF
    · exact not_ff_dual_of_opposite N h hFF
  rcases hN with hN | hN <;> rcases hQ with hQ | hQ
  · exact Or.inl ⟨hN, hQ⟩
  · exact False.elim (hn (Or.inl ⟨hN, hQ⟩))
  · exact False.elim (hn (Or.inr ⟨hN, hQ⟩))
  · exact Or.inr ⟨hN, hQ⟩

private noncomputable def doubleProductEquiv {X Y : Type*}
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    {σ : Representation (ZMod 2) SL X} {τ : Representation (ZMod 2) SL Y}
    (e : σ.Equiv τ) : (σ.prod σ).Equiv (τ.prod τ) :=
  .mk (e.toLinearEquiv.prodCongr e.toLinearEquiv) (by
    intro g
    apply LinearMap.ext
    intro v
    exact Prod.ext (LinearMap.congr_fun (e.isIntertwining' g) v.1)
      (LinearMap.congr_fun (e.isIntertwining' g) v.2))

private theorem split_of_budget [FiniteDimensional (ZMod 2) V]
    (N : Subrepresentation ρ) (hN : NaturalOrDual N.toRepresentation)
    (hQ : NaturalOrDual N.quotientRepresentation)
    (hFF : IsFFModule ρ ∨ IsFFModule ρ.dual) :
    Nonempty (ρ.Equiv (BinaryLinearThree.W.prod BinaryLinearThree.W)) ∨
      Nonempty (ρ.Equiv (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual)) := by
  rcases homogeneous_of_budget N hN hQ hFF with ⟨hN, hQ⟩ | ⟨⟨eN⟩, ⟨eQ⟩⟩
  · exact Or.inl (homogeneous_splitting ρ N (MulEquiv.refl SL) hN hQ)
  · obtain ⟨e⟩ := homogeneous_splitting ρ N BinaryLinearThree.AutomorphismAction.graph
      ⟨eN.trans BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm⟩
      ⟨eQ.trans BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm⟩
    exact Or.inr ⟨e.trans (doubleProductEquiv
      BinaryLinearThree.AutomorphismAction.graphNaturalDual)⟩

end LinearExtension

open Subgroup Stellmacher.PushingUp.AmalgamGraph
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The two literal factors have matching orientations and their extension
splits. The crossing and contained estimates supply the original or dual
FF budget; no splitting or matching-orientation premise is added. -/
theorem TwoNaturalFactors.split_of_estimates
    (common : CommonFacts R source geometry)
    {d : LayerModule source (V R (alpha R))} (n : TwoNaturalFactors (geometry := geometry) d)
    (f : Seed.Frame source) (s : CriticalSegment geometry) (hest : Estimates d f s) :
    Nonempty ((starRepresentation (geometry := geometry) d).toRepresentation.Equiv
      (BinaryLinearThree.W.prod BinaryLinearThree.W)) ∨
    Nonempty ((starRepresentation (geometry := geometry) d).toRepresentation.Equiv
      (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual)) :=
  split_of_budget n.lower n.lower_natural n.upper_natural
    (star_or_dual_isFFModule_of_estimates common d f s hest)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
