module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Natural.PairAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Rows
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.SeedCentralizer

/-!
# Exclusion of the natural row for a central Hall subgroup

Fixed lifting removes the Hall coefficient action without collapsing the
central section kernel. Both component actions are inner, and the original
Hall group therefore lies in L₀. The proved natural-section detection theorem
says that a nonidentity odd element of L₀ moves Ω₁Z(T). The central Hall
hypothesis forces every Hall element to be the identity, giving exactly
`NaturalActionTrivialAt` on the literal original quotient action.
Source: Aschbacher--Smith, 10.1.2(5) and 10.2.3, printed pp.742,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 Representation
universe u
variable {G : Type u} [Group G] [Finite G] (T : Sylow 2 G)
local instance (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2

theorem source_naturalActionTrivialAt : NaturalActionTrivialAt T := by
  intro L D H B c geometry n hn e d
  have hBR := natural_hall_le_orbit D c geometry n hn e d
  have hHZ : H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (by rw [commutator_comm]; exact c.central)
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  have mark : MovingHall.NaturalMarking D e :=
    ⟨⟨d⟩,t,ht,htn,geometry.crossed t ht htn⟩
  apply MonoidHom.ext
  intro b
  have hb : (b : G) = 1 := by
    by_contra hb
    let bR : localOrbit T L := ⟨b,hBR (mem_map_of_mem H.subtype b.property)⟩
    have hpow : bR ^ Nat.card B = 1 := by
      apply Subtype.ext
      exact congrArg (H.subtype.comp B.subtype) (pow_card_eq_one' (x := b))
    exact MovingHall.source_natural_odd_not_centralizes_omegaCenter D n hn
      (GaloisField.card 2 n (by omega)) e c.nonnormal mark bR (Nat.card B)
      (hall_odd D c) hpow (fun h => hb (congrArg Subtype.val h))
      (hHZ b.val.property)
  have hb' : b = 1 := (H.subtype_injective.comp B.subtype_injective) hb
  simp [hb']
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
