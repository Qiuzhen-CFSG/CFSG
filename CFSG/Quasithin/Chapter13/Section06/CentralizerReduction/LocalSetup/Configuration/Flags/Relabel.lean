module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Inputs
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.Coordinates

/-!
# Relabelling an actual A₅ module and its normalizer action

A coordinate permutation is absorbed into the module embedding and conjugates
both action homomorphisms in the opposite direction. Equivariance, surjectivity
and the two-core kernel are preserved. This constructs the relabelled maps;
it does not assume or assert that a chosen permutation aligns the source flag.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed pp.877
and 926, where the invariant flag is put in the specified permutation coordinates.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
open Subgroup BinaryPermutation BinaryPermutation.FiveCentralizerGeometry

variable {G : Type*} [Group G] {L V : Subgroup G}
open FlagCoordinates
/-- Change both the module coordinates and the A₅ action by the same permutation. -/
def Marking.relabel (s : Marking L V) (g : Perm) : Marking L V where
  map := s.map.comp (coordinateEquiv g).toMonoidHom
  injective := s.injective.comp (coordinateEquiv g).injective
  range_eq := by
    rw [MonoidHom.range_comp, (coordinateEquiv g).toMonoidHom.range_eq_top.mpr
      (coordinateEquiv g).surjective, ← MonoidHom.range_eq_map, s.range_eq]
  action := (MulAut.conjNormal g⁻¹).toMonoidHom.comp s.action
  onto := (MulAut.conjNormal g⁻¹).surjective.comp s.onto
  equivariant l x := by
    change MulAut.conj (l : G) (s.map (Multiplicative.ofAdd (rho g x))) =
      s.map (Multiplicative.ofAdd (rho g (act (MulAut.conjNormal g⁻¹ (s.action l)) x)))
    rw [s.equivariant]
    apply congrArg (fun x : Space => s.map (Multiplicative.ofAdd x))
    simpa only [act, MulAut.conjNormal_apply, inv_inv] using intertwine g (s.action l).val x

@[simp] theorem Marking.relabel_map (s : Marking L V) (g : Perm) (x : Space) :
    (s.relabel g).map (Multiplicative.ofAdd x) = s.map (Multiplicative.ofAdd (rho g x)) := rfl

theorem Marking.relabel_kernel (s : Marking L V) (g : Perm) :
    (s.relabel g).action.ker = s.action.ker := by
  ext l
  change MulAut.conjNormal g⁻¹ (s.action l) = 1 ↔ s.action l = 1
  exact (MulAut.conjNormal g⁻¹).map_eq_one_iff

/-- Relabelling retains all the source flag subgroups and conjugation data. -/
def FlagSource.relabel {T : Sylow 2 G} {V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂) (g : Perm) : FlagSource T L V V₁ V₂ where
  module := d.module.relabel g
  action_kernel := (d.module.relabel_kernel g).trans d.action_kernel
  normalizerAction := (MulAut.conj g⁻¹).toMonoidHom.comp d.normalizerAction
  normalizer_equivariant n x := by
    change MulAut.conj (n : G) (d.module.map (Multiplicative.ofAdd (rho g x))) =
      d.module.map (Multiplicative.ofAdd (rho g (rho (g⁻¹ * d.normalizerAction n * g) x)))
    rw [d.normalizer_equivariant]
    exact congrArg (fun x : Space => d.module.map (Multiplicative.ofAdd x))
      (intertwine g (d.normalizerAction n) x)
  action_agrees l hl := by
    change g⁻¹ * d.normalizerAction ⟨l, hl⟩ * g =
      (MulAut.conjNormal g⁻¹ (d.module.action l)).val
    rw [d.action_agrees l hl, MulAut.conjNormal_apply, inv_inv]
  T_normalizes := d.T_normalizes
  V_le_T := d.V_le_T
  one_le_two := d.one_le_two
  two_le_V := d.two_le_V
  one_card := d.one_card
  two_card := d.two_card
  one_invariant := d.one_invariant
  two_invariant := d.two_invariant
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
