module
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman
public import Theory.Representation.BinaryOffender.PerfectCentralizerDisplacement
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Solvable actors commuting with a fixed-free perfect factor

Glauberman's solvable FF theorem gives an inclusion-minimal best offender
of rank one. Its fixed codimension is at most one. On the other hand,
every nontrivial actor commuting with a fixed-free perfect binary factor
has fixed codimension at least three. These bounds exclude the offender.
The ambient and restricted actions use the same module and subgroup map.

The actual full-module application is Chapter10's Quiet.ThompsonCentralizer.
Source: Aschbacher--Smith B.1.8(1), printed p.70, and the perfect-factor
fixed-space argument in 13.1.9, printed p.871.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
variable {Q W : Type*} [Group Q] [Finite Q]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- A solvable reduced actor commuting with a fixed-free perfect factor has no FF-module. -/
theorem noFF_of_solvable_commuting_perfect (ρ : Representation (ZMod 2) Q W)
    (hf : Function.Injective ρ) (S C : Subgroup Q) [Group.IsPerfect S]
    (hfix : fixedSpace ρ S = ⊥) (hC : Group.IsSolvable C)
    (hcore : pCore 2 C = ⊥) (hc : C ≤ centralizer (S : Set Q)) :
    ¬ IsFFModule (ρ.comp C.subtype) := by
  rintro ⟨A,hA⟩
  obtain ⟨B,_,hB,_,_⟩ := hA.exists_quadratic_minimalBestOffender (ρ.comp C.subtype)
  have hr := Glauberman.minimalBestOffender_rank_one
    (ρ.comp C.subtype) (hf.comp C.subtype_injective) hC hcore hB
  have hb := (hB.1.isOffender (ρ.comp C.subtype)).2
  have hne : ¬ B.map C.subtype ≤ ρ.ker := by
    intro he
    have hz : ρ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff ρ).mpr hf
    have hm : B.map C.subtype = ⊥ := bot_unique (he.trans_eq hz)
    exact hB.1.1.1 ((map_eq_bot_iff_of_injective _ C.subtype_injective).mp hm)
  have hcomm : ⁅S,B.map C.subtype⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact le_centralizer_iff.mp ((show B.map C.subtype ≤ C from (map_le_range C.subtype B).trans_eq C.range_subtype).trans hc)
  have hd := three_le_fixedCodim_of_perfect_fixedSpace_eq_bot ρ S (B.map C.subtype)
    hfix hne hcomm
  have he : fixedCodim (ρ.comp C.subtype) B = fixedCodim ρ (B.map C.subtype) := by
    exact fixedCodim_map_equivariant (ρ.comp C.subtype) ρ C.subtype
      (LinearEquiv.refl (ZMod 2) W) (fun _ _ => rfl) B
  omega


end CFSG.Quasithin.ChapterB
