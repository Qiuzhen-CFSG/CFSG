module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.Configuration
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.Homogeneous

/-!
# Marking the single quotient in the small-intersection branch

Every automorphism of the binary special linear group is inner or inner times
inverse transpose. A change of basis therefore aligns any natural quotient
marking with the specified marking on U_alpha, retaining both orientations.
The homomorphism, its exact kernel and ambient conjugation formula are preserved.

`CoreModule` specifies an actual elementary quotient with its FF-action, without
asserting its existence. The final conditional assembly applies the proved
binary homogeneous FF theorem. The geometric construction of `CoreModule` and
the proof that its coordinates have one copy and no fixed vectors remain
separate source obligations. None of these conditional results is (4.6.11).

Source: Meierfrankenfeld--Stellmacher (1993), (1.4), printed p.842, and
(4.6.10)--(4.6.11), printed pp.908--909. No odd-characteristic calculation is used.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph Matrix
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
open Linear Representation Representation.BinaryOffender

private noncomputable def changeBasis (g : SL) : W ≃ₗ[ZMod 2] W :=
  LinearMap.GeneralLinearGroup.toLinearEquiv ((specialLinearNatural 3).asGroupHom g⁻¹)

/-- Removing an inner change of basis leaves the natural action or its dual. -/
theorem marking_coordinates (a : SL ≃* SL) : ∃ e : W ≃ₗ[ZMod 2] W,
    (∀ g v, e ((a g).val.mulVec v) = g.val.mulVec (e v)) ∨
    (∀ g v, e ((a g).val.mulVec v) = dual g (e v)) := by
  classical
  by_cases ha : a ∈ MulAut.innerSubgroup SL
  · obtain ⟨k, rfl⟩ := ha
    refine ⟨changeBasis k, Or.inl ?_⟩
    intro g v
    change (specialLinearNatural 3) k⁻¹ ((specialLinearNatural 3) (k * g * k⁻¹) v) =
      (specialLinearNatural 3) g ((specialLinearNatural 3) k⁻¹ v)
    simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel_left]
  · obtain ⟨k, hk⟩ := BinaryLinearThree.AutomorphismAction.outer_eq_inner_graph a ha
    refine ⟨changeBasis k, Or.inr ?_⟩
    intro g v
    rw [hk]
    change (specialLinearNatural 3) k⁻¹
      ((specialLinearNatural 3) (k * BinaryLinearThree.AutomorphismAction.graph g * k⁻¹) v) =
      (specialLinearNatural 3) (BinaryLinearThree.AutomorphismAction.graph g)
        ((specialLinearNatural 3) k⁻¹ v)
    simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel_left]

universe u
variable {M : Type u} [Group M] {L R : Subgroup M}
    (source : LocalSource L R)

/-- An actual finite binary model of core/U with its faithful, fully moving
FF-action. Existence is a separate geometric obligation; no natural coordinates
or fixed-space condition are included. -/
structure CoreModule where
  Space : Type u
  [addCommGroup : AddCommGroup Space]
  [module : Module (ZMod 2) Space]
  [finite : Finite Space]
  representation : Representation (ZMod 2) SL Space
  projection : core R (alpha R) →* Multiplicative Space
  onto : Function.Surjective projection
  kernel : projection.ker = (U R (alpha R)).subgroupOf (core R (alpha R))
  action : ∀ (m : M) (x y : core R (alpha R)),
    (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
    (projection y).toAdd = representation (source.projection m) (projection x).toAdd
  faithful : Function.Injective representation
  full : subspaceCommutator representation ⊤ ⊤ = ⊤
  offending : IsFFModule representation

attribute [instance] CoreModule.addCommGroup CoreModule.module CoreModule.finite

variable {source}
variable {geometry : Geometry R} (common : CommonFacts R source geometry)

/-- Arbitrarily marked natural coordinates can be normalized to the existing
natural marking or its contragredient. -/
theorem normalize (β : SL ≃* SL)
    (q : core R (alpha R) →* Multiplicative W)
    (hq : Function.Surjective q)
    (hk : q.ker = (U R (alpha R)).subgroupOf (core R (alpha R)))
    (ha : ∀ (m : M) (x y : core R (alpha R)),
      (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
      (q y).toAdd = (β (source.projection m)).val.mulVec (q x).toAdd) :
    Nonempty (SingleQuotient source common (fun g v => g.val.mulVec v)) ∨
      Nonempty (SingleQuotient source common dual) := by
  let a : SL ≃* SL := common.natural.marking.symm.trans β
  obtain ⟨e, he⟩ := marking_coordinates a
  let em : Multiplicative W ≃* Multiplicative W := e.toAddEquiv.toMultiplicative
  let q' := em.toMonoidHom.comp q
  have hs : Function.Surjective q' := em.surjective.comp hq
  have hker : q'.ker = (U R (alpha R)).subgroupOf (core R (alpha R)) :=
    (MonoidHom.ker_comp_of_injective q em.toMonoidHom em.injective).trans hk
  have heq (m : M) : a (common.natural.marking (source.projection m)) =
      β (source.projection m) := by simp [a]
  rcases he with he | he
  · refine Or.inl ⟨⟨q', hs, hker, ?_⟩⟩
    intro m x y hy
    change e (q y).toAdd = (common.natural.marking (source.projection m)).val.mulVec
      (e (q x).toAdd)
    rw [ha m x y hy, ← heq]
    exact he _ _
  · refine Or.inr ⟨⟨q', hs, hker, ?_⟩⟩
    intro m x y hy
    change e (q y).toAdd = dual (common.natural.marking (source.projection m))
      (e (q x).toAdd)
    rw [ha m x y hy, ← heq]
    exact he _ _

open AbelianCore.QuotientRecognition
variable (d : CoreModule source)

/-- Recognition remains conditional on the geometric proof that there is one
copy and no extra fixed kernel. -/
theorem singleQuotient_of_moduleQuotient
    (q : ModuleQuotient d.representation 1)
    (hfix : fixedSpace d.representation ⊤ = ⊥) :
    Nonempty (SingleQuotient source common (fun g v => g.val.mulVec v)) ∨
      Nonempty (SingleQuotient source common dual) := by
  let e : (Fin 1 → W) ≃ₗ[ZMod 2] W := LinearEquiv.funUnique (Fin 1) (ZMod 2) W
  let f : d.Space →ₗ[ZMod 2] W := e.toLinearMap.comp q.projection
  have hf : Function.Injective f := e.injective.comp
    (LinearMap.ker_eq_bot.mp (q.kernel.trans hfix))
  let fm : Multiplicative d.Space →* Multiplicative W := f.toAddMonoidHom.toMultiplicative
  let qm := fm.comp d.projection
  apply normalize common q.marking qm
  · exact e.surjective.comp (q.surjective.comp d.onto)
  · exact (MonoidHom.ker_comp_of_injective d.projection fm hf).trans d.kernel
  · intro m x y hy
    change q.projection (d.projection y).toAdd 0 =
      (q.marking (source.projection m)).val.mulVec (q.projection (d.projection x).toAdd 0)
    rw [d.action m x y hy]
    exact q.equivariant _ _ 0

/-- The two remaining source obligations can be assembled independently. -/
theorem singleQuotient_of_FF_and_purity
    (hpure : ∀ m (_q : ModuleQuotient d.representation m),
      m = 1 ∧ fixedSpace d.representation ⊤ = ⊥) :
    Nonempty (SingleQuotient source common (fun g v => g.val.mulVec v)) ∨
      Nonempty (SingleQuotient source common dual) := by
  obtain ⟨m, ⟨q⟩⟩ := exists_moduleQuotient d.representation d.faithful d.full d.offending
  obtain ⟨rfl, hf⟩ := hpure m q
  exact singleQuotient_of_moduleQuotient common d q hf

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
