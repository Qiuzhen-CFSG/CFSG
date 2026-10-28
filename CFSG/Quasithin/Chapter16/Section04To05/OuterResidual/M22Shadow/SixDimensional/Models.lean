module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.Setup
public import Theory.Representation.AlternatingFiveLinearTwoObstruction
public import Theory.Representation.BinaryPermutation.SevenPointChiefFactor
public import Theory.Representation.BinaryTransvectionGroups.ReducedCommutation

/-!
# The seven-point model obstruction for the actual M₂₂ shadow

The imported linear results prove the centerless-case commutation and construct
the five-point A₅ chief factor inside the seven-point binary core. The theorem
below applies the latter to the actual subgroups V = Q⟨r,z⟩ and M and their
ambient conjugation action. A purported seven-point model and the natural
SL₂(4) section give an impossible equivariant injection of the five-point core.

This is a conditional endgame, not the two source case contradictions. The
marked transvections, trivial two-core, G.6.4 specialization, and the dihedral
Sylow/component argument must still construct the models fed to this theorem.
In particular it does not assume or prove a recognition theorem for arbitrary
six-dimensional actions. The action kernel is the relative C_M(V), as proved
in `M22Shadow.Setup`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 16.4.7, printed pp.1186–1187 (PDF pp.1203–1204).
-/

public section

open Module Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional
open BinaryPermutation BinaryPermutation.SevenPointChiefFactor
variable {G : Type*} [Group G]

/-- Comparison with a seven-point model is a genuine equivariant isomorphism
from the actual shadow space. The local natural section is specified through
the actual conjugation image M⁺. No homomorphic lift from A₅ to M is
required, so this comparison makes no splitting assumption on C_M(V). -/
theorem sevenPoint_shadow_obstruction
    (L : Subgroup G) (g r z : G)
    (ι : Five →* (shadowAction L g r z).range)
    (eV : shadowSpace L r z ≃* Multiplicative (core Seven))
    (hact : ∀ a v,
      eV ((ι a).val (eV.symm (Multiplicative.ofAdd v))) =
        Multiplicative.ofAdd (coreRepresentation Seven (fivePerm a) v))
    (W : Submodule (ZMod 2) (core Seven))
    (U : Submodule (ZMod 2) W)
    {F : Type*} [Field F] [CharP F 2] (hF : Nat.card F = 4)
    (f : Five →* SL(2,F)) (hf : Function.Injective f)
    (e : (W ⧸ U) ≃+ (Fin 2 → F))
    (hsection : ∀ a (w : W), ∃ w' : W,
      eV ((ι a).val (eV.symm (Multiplicative.ofAdd w.val))) =
          Multiplicative.ofAdd w'.val ∧
        e (U.mkQ w') = (f a).val *ᵥ e (U.mkQ w)) : False := by
  have hcoord (a : Five) (w : W) : ∃ w' : W,
      coreRepresentation Seven (fivePerm a) w = w'.val ∧
        e (U.mkQ w') = (f a).val *ᵥ e (U.mkQ w) := by
    obtain ⟨w', hw', he⟩ := hsection a w
    refine ⟨w', ?_, he⟩
    exact congrArg Multiplicative.toAdd ((hact a w).symm.trans hw')
  have hW (a : Five) (v : core Seven) (hv : v ∈ W) :
      coreRepresentation Seven (fivePerm a) v ∈ W := by
    obtain ⟨w', hw', _⟩ := hcoord a ⟨v, hv⟩
    rw [hw']
    exact w'.property
  have heq (a : Five) (w : W) :
      e (U.mkQ ⟨coreRepresentation Seven (fivePerm a) w, hW a w w.property⟩) =
        (f a).val *ᵥ e (U.mkQ w) := by
    obtain ⟨w', hw', he⟩ := hcoord a w
    have hh : (⟨coreRepresentation Seven (fivePerm a) w, hW a w w.property⟩ : W) = w' :=
      Subtype.ext hw'
    rw [hh]
    exact he
  have hU (a : Five) (w : W) (hw : w ∈ U) :
      (⟨coreRepresentation Seven (fivePerm a) w, hW a w w.property⟩ : W) ∈ U := by
    apply (Submodule.Quotient.mk_eq_zero U).mp
    apply e.injective
    have hz : U.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero U).mpr hw
    change e (U.mkQ ⟨coreRepresentation Seven (fivePerm a) w, hW a w w.property⟩) = e 0
    rw [heq, hz, map_zero]
    simp
  obtain ⟨hWdim, hUdim⟩ := plane_section_bounds W U hF e
  exact sevenCore_no_natural_section f hf W hWdim hW U hUdim hU e heq

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional
