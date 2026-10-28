module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical.MixedCommutator
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical.QuadraticRadical

/-!
# Center control for the fourth-case Frattini centralizer

For the genuine binary MS pair in C.1.34(4), write Q = msQ K R,
P = Φ(Q), and D = C_Q(P). If D is nonabelian, then Z(D) = P.

The mixed-commutator calculation proves [D,Q] ≤ Z(Q), hence that squares
of D lie in Z(Q), and proves that P is elementary abelian. These discharge
both structural premises of the doubled-dual quadratic-radical theorem.
All three module sections and the natural moved center use the same marking e.
Together with the previously proved derived-subgroup bound, the center equality
supplies the full FrattiniCentralizerControl predicate.

This is an algebraic consequence of C.1.34(4), not a separately printed clause
of that theorem. The quotient and literal checked-map applications retain
nonabelianness and FrattiniCommutatorLarge explicitly. Their independent
source proofs remain with the parent assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, C.1.34(4),
printed pp.136–137, and its application in 13.6.22, printed pp.932–933;
Meierfrankenfeld–Stellmacher (1993), Lemma 4.5, printed pp.895–900.
-/

public section

open Subgroup
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical

local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn

variable {G : Type*} [Group G] [Finite G]
variable {K R S : Subgroup G} {κ : CFSG.Quasithin.GroupClass}

/-- The center containment under nonabelianness, with elementarity and square
placement proved from the genuine MS pair and the marked fourth alternative. -/
theorem caseFour_center_centralizer_le_frattini
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e)
    (hne : ⁅msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G),
      msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G)⁆ ≠ ⊥) :
    sCenter (msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G)) ≤
      frattiniIn (msQ K R) :=
  QuadraticRadical.caseFour_center_centralizer_le_frattini hMS e h
    (MixedCommutator.caseFour_frattini_elementary hMS e h)
    (MixedCommutator.caseFour_centralizer_square_mem_center hMS e h) hne

/-- The nonabelian Frattini centralizer has center exactly Φ(Q). -/
theorem caseFour_center_centralizer_eq_frattini
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e)
    (hne : ⁅msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G),
      msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G)⁆ ≠ ⊥) :
    sCenter (msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G)) =
      frattiniIn (msQ K R) :=
  le_antisymm (caseFour_center_centralizer_le_frattini hMS e h hne)
    (caseFour_frattini_le_center_centralizer e h)

/-- Without nonabelianness, the precise alternative is trivial derived
subgroup or center equal to Φ(Q). -/
theorem caseFour_centralizer_derived_eq_bot_or_center_eq_frattini
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    let Q := msQ K R
    let D := Q ⊓ centralizer (frattiniIn Q : Set G)
    ⁅D,D⁆ = ⊥ ∨ sCenter D = frattiniIn Q := by
  by_cases hne : ⁅msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G),
      msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G)⁆ = ⊥
  · exact Or.inl hne
  · exact Or.inr (caseFour_center_centralizer_eq_frattini hMS e h hne)

/-- The new center theorem discharges the remaining clause of the parent's
Frattini-centralizer control, under the explicit nonabelianness assumption. -/
theorem caseFour_control_of_nonabelian
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e)
    (hne : ⁅msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G),
      msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G)⁆ ≠ ⊥) :
    FrattiniCentralizerControl (msQ K R) (msQ K R ⊓ centralizer (K : Set G)) :=
  (caseFour_control_iff_center_le hMS e h).mpr
    (caseFour_center_centralizer_le_frattini hMS e h hne)

/-- Application to the literal central quotient; only nonabelianness and
the independently owned large-Frattini-commutator premise remain explicit. -/
theorem caseFour_quotient_control_of_nonabelian {H : Type*} [Group H]
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e)
    (hne : ⁅msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G),
      msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G)⁆ ≠ ⊥)
    (f : K →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hcard : Nat.card f.ker ∣ 2)
    (hN : f.ker.map K.subtype ≤ sCenter (K ⊔ R))
    (hPhi : FrattiniCommutatorLarge (msQ K R)) :
    ⁅(sCenter (pCore 2 H)).comap f, (⊤ : Subgroup K)⁆ ≤ sCenter (pCore 2 K) ∧
    ⁅(sCenter (pCore 2 H)).comap f, (⊤ : Subgroup K)⁆ =
      ⁅sCenter (pCore 2 K), (⊤ : Subgroup K)⁆ :=
  caseFour_quotient_control_of_center hMS e h f hf hk hcard hN
    (caseFour_center_centralizer_le_frattini hMS e h hne) hPhi

open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction

/-- The checked-map application at the actual source radical Tᵥ, with both
independently owned source premises retained for the parent assembly. -/
theorem caseFour_checked_commutator_of_nonabelian
    (T : Subgroup G) (v : G) (hK : K ≤ Gv v) (hv : v ^ 2 = 1)
    (hMS : LinearThreeMSPair κ K (Tv T v) 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K (Tv T v) S e)
    (hne : ⁅msQ K (Tv T v) ⊓ centralizer (frattiniIn (msQ K (Tv T v)) : Set G),
      msQ K (Tv T v) ⊓ centralizer (frattiniIn (msQ K (Tv T v)) : Set G)⁆ ≠ ⊥)
    (hPhi : FrattiniCommutatorLarge (msQ K (Tv T v))) :
    ⁅sourceZ0 K v hK,K⁆ = sourceU K :=
  caseFour_checked_commutator_of_structure T v hK hv hMS e h
    (caseFour_control_of_nonabelian hMS e h hne) hPhi

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical
