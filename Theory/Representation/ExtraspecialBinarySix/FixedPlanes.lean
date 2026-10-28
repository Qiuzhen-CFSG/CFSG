module
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.ExtraspecialModel.MinimalDegree
public import Theory.Representation.ExtraspecialCubicDisplacement
public import Theory.Representation.GoldschmidtONan.Basic
public import Theory.Representation.NormalInvariants

/-!
# Fixed planes of the original noncentral cubic actor

A faithful binary six-space for the extraspecial group of order 27 is
irreducible. Its center has no fixed vectors, and every noncentral cubic
subgroup fixes a plane of dimension two. Odd-order averaging gives the
complementary moved four-space. These calculations require no choice of
Sylow marking or component.

Source: Aschbacher--Smith, Notation 15.1.16(c), printed p.1092.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.ExtraspecialBinarySix

/-- The exact fixed and moved dimensions for any noncentral cubic subgroup. -/
theorem noncentral_cubic_planes {D U : Type*} [Group D] [Finite D]
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (hf : Function.Injective ρ)
    (P : Subgroup D) [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hd : Module.finrank (ZMod 2) U = 6)
    (X : Subgroup P) (hX : Nat.card X = 3) (hXZ : X ≠ center P) :
    Module.finrank (ZMod 2) (fixedSpace ρ (X.map P.subtype)) = 2 ∧
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (X.map P.subtype)) = 4 ∧
    IsCompl (fixedSpace ρ (X.map P.subtype))
      (subspaceCommutator ρ ⊤ (X.map P.subtype)) := by
  let σ : Representation (ZMod 2) P U := ρ.comp P.subtype
  have hσ : Function.Injective σ := hf.comp P.subtype_injective
  let : IsIrreducible σ := RankTwo.ExtraspecialModel.irreducible_of_faithful_six σ hσ hP hd
  have hz : invariants (σ.comp (center P).subtype) = ⊥ := by
    by_contra hn
    have hh := Representation.le_ker_of_normal_invariants_ne_bot σ (center P) hn
    have hb : center P = ⊥ := bot_unique (by
      simpa only [(MonoidHom.ker_eq_bot_iff _).mpr hσ] using hh)
    have hc := IsExtraspecial.center_order_p 3 P
    rw [hb,card_bot] at hc
    omega
  have hcod := BinaryCoprimeDegree.extraspecial_twentySeven_fixedCodim_subgroup σ hP hz X hX hXZ
  have hadd := fixedCodim_add_finrank σ X
  have hfix : Module.finrank (ZMod 2) (fixedSpace ρ (X.map P.subtype)) = 2 := by
    rw [←fixedSpace_comp_map]
    change Module.finrank (ZMod 2) (fixedSpace σ X) = 2
    rw [hd] at hcod hadd
    omega
  have hc : Nat.card (X.map P.subtype) = 3 :=
    (Nat.card_congr (X.equivMapOfInjective P.subtype P.subtype_injective).toEquiv).symm.trans hX
  have hcompl : IsCompl (fixedSpace ρ (X.map P.subtype))
      (subspaceCommutator ρ ⊤ (X.map P.subtype)) := by
    simpa only [RegularCyclicNormalClosure.displacementSpan,subspaceCommutator,eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) (by rw [hc]; decide))
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (fixedSpace ρ (X.map P.subtype)) (subspaceCommutator ρ ⊤ (X.map P.subtype))
  rw [hcompl.sup_eq_top,hcompl.inf_eq_bot,finrank_top,finrank_bot,hd,hfix] at hsum
  exact ⟨hfix,by omega,hcompl⟩

end Representation.ExtraspecialBinarySix
