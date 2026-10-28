module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairResidual
public import Theory.Representation.BinaryPermutation.FivePairExtension

/-!
# The actual symmetric-five pair has sharp natural quotient coordinates

The given marked product retains the original fixed quotient and both actor
factors. The canonical odd-degree equivalence changes its natural coordinates
to five-letter cores. The two class-sum projectors split the original quotient
and identify every fixed codimension on this same actor product. No extra
fixed-space, splitting or action compatibility premise is required.

Source: Aschbacher–Smith B.6.9 and E.2.3(3), pp.115–116 and216–217.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction.SourceTwoFactorCase.MarkedProduct
open BinaryPermutation
variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) K V} {d : SourceTwoFactorCase ρ}

abbrev symmetricCoreEquiv : (natural (Fin 5) × natural (Fin 5)) ≃ₗ[ZMod 2]
    (core (Fin 5) × core (Fin 5)) :=
  (coreEquivNatural (Fin 5) (by decide)).symm.prodCongr
    (coreEquivNatural (Fin 5) (by decide)).symm

theorem symmetricCoreEquiv_action (g : FiveCentralExtension.Sym × FiveCentralExtension.Sym)
    (v : natural (Fin 5) × natural (Fin 5)) :
    symmetricCoreEquiv ((Representation.prod
      ((naturalRepresentation (Fin 5)).comp (MonoidHom.fst _ _))
      ((naturalRepresentation (Fin 5)).comp (MonoidHom.snd _ _))) g v) =
        FivePair.action g (symmetricCoreEquiv v) := by
  obtain ⟨v,rfl⟩ := symmetricCoreEquiv.symm.surjective v
  apply symmetricCoreEquiv.symm.injective
  simp only [LinearEquiv.symm_apply_apply,LinearEquiv.apply_symm_apply]
  exact Prod.ext (coreEquivNatural_equivariant (Fin 5) (by decide) g.1 v.1).symm
    (coreEquivNatural_equivariant (Fin 5) (by decide) g.2 v.2).symm

variable (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
def symmetricCoreMap : V →ₗ[ZMod 2] (core (Fin 5) × core (Fin 5)) :=
  symmetricCoreEquiv.toLinearMap.comp c.quotientMap

theorem symmetricCoreMap_surjective : Function.Surjective c.symmetricCoreMap :=
  symmetricCoreEquiv.surjective.comp c.quotientMap_surjective

theorem symmetricCoreMap_ker : c.symmetricCoreMap.ker = ρ.invariants := by
  ext v
  change symmetricCoreEquiv (c.quotientMap v) = 0 ↔ v ∈ ρ.invariants
  rw [LinearEquiv.map_eq_zero_iff]
  exact SetLike.ext_iff.mp c.quotientMap_ker v

theorem symmetricCoreMap_action (g : K) (v : V) :
    c.symmetricCoreMap (ρ g v) = FivePair.action (c.action.groupEquiv g) (c.symmetricCoreMap v) := by
  change symmetricCoreEquiv (c.quotientMap (ρ g v)) = _
  rw [c.quotientMap_action,symmetricCoreEquiv_action]
  rfl

/-- The same original paired S₅ mark preserves every fixed codimension; the
class-sum construction discharges the central extension comparison. -/
theorem symmetric_fixedCodim [FiniteDimensional (ZMod 2) V] (A : Subgroup K) :
    fixedCodim ρ A = fixedCodim FivePair.action (A.map c.action.groupEquiv.toMonoidHom) := by
  let σ := ρ.comp c.action.groupEquiv.symm.toMonoidHom
  have he (g : FiveCentralExtension.Sym × FiveCentralExtension.Sym) (v : V) :
      c.symmetricCoreMap (σ g v) = FivePair.action g (c.symmetricCoreMap v) := by
    simpa only [σ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using c.symmetricCoreMap_action (c.action.groupEquiv.symm g) v
  have hk (v : V) (hv : c.symmetricCoreMap v = 0)
      (g : FiveCentralExtension.Sym × FiveCentralExtension.Sym) : σ g v = v := by
    have hfix : v ∈ ρ.invariants := c.symmetricCoreMap_ker ▸ hv
    exact hfix (c.action.groupEquiv.symm g)
  have hh := FivePair.fixedCodim_eq σ c.symmetricCoreMap c.symmetricCoreMap_surjective he hk
    (A.map c.action.groupEquiv.toMonoidHom)
  have hA : (A.map c.action.groupEquiv.toMonoidHom).map c.action.groupEquiv.symm.toMonoidHom = A :=
    c.action.groupEquiv.mapSubgroup.symm_apply_apply A
  change Module.finrank (ZMod 2) (V ⧸ fixedSpace σ _) = _ at hh
  rw [fixedSpace_comp_map ρ c.action.groupEquiv.symm.toMonoidHom,hA] at hh
  exact hh
end CFSG.Quasithin.ChapterB.SourceInduction.SourceTwoFactorCase.MarkedProduct
