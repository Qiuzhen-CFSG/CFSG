module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.Baumann
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.Baumann.Maximal
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.Baumann.CenterAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.LocalInverter.Quotient
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule.Quotient
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.FieldDescent
public import Theory.NumberTheory.BinaryTorusParity

/-!
# The A₅ residual forces even symplectic field degree

In the actual 13.6.6 symplectic configuration, the marked residual Lᵥ
surjects onto a cubic group and already lies in B = N_K(T_K). Since
the Borel has order q⁴(q−1)², with q = 2^n, its field degree n is even.
Thus maximum-elementary placement needs only the proved field descent;
the odd-degree graph-cocycle premise is vacuous. Combining this placement
with the proved Sylow-center kernel gives the literal Thompson/Baumann
decomposition and the source Borel containment.

The actual earlier 13.6.4 and 13.6.5 inputs remain explicit. The equivalence
is from the whole component K, not K/Z(K); the cover reduction must precede
this application. Source: Aschbacher–Smith, proof of 13.6.6, printed p.927.

-/

public section
open Subgroup Stellmacher CFSG.Quasithin.ChapterB
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.SourceEvenDegree
open A5Module
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable (K : Subgroup H) (e : K ≃* Sp F)

omit [CharP F 2] in
/-- The earlier placement of the marked residual already rules out odd degree.
The cubic action, Borel inclusion and whole-component equivalence are literal. -/
theorem even_degree_of_marked_residual_in_borel {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    {L V : Subgroup H} (s : Marking L V) (S : Sylow 2 (Sp F))
    (hD : Lv L (markedV s) ≤ borelIn K e S) : Even n := by
  have hthree : 3 ∣ Nat.card (Lv L (markedV s)) := by
    simpa only [ResidualCoordinates.cubicGroup_card]
      using card_dvd_of_surjective (residualCubicAction s)
        (residualCubicAction_surjective s)
  have hB : 3 ∣ Nat.card (localBorel K e S) :=
    hthree.trans (card_dvd_of_injective
      (LocalInverter.borelLift K e S (Lv L (markedV s)) hD)
      (LocalInverter.borelLift_injective K e S (Lv L (markedV s)) hD))
  rw [Nat.card_congr (borelEquiv K e hF hn S).toEquiv, card_borel, hF] at hB
  have htwo : ¬ 3 ∣ (2 ^ n) ^ 4 := fun h =>
    (by decide : ¬ 3 ∣ 2)
      (Nat.prime_three.dvd_of_dvd_pow (Nat.prime_three.dvd_of_dvd_pow h))
  exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mp
    (Nat.prime_three.dvd_of_dvd_pow ((Nat.prime_three.dvd_mul.mp hB).resolve_left htwo))

/-- In even degree, the completed field descent supplies every needed outer
involution bound. No exceptional graph-cocycle theorem is used. -/
theorem maximum_elementary_placement_of_even_degree {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (heven : Even n)
    (R : Subgroup H) (hp : IsPGroup 2 R) (hR : R ≤ normalizer (K : Set H))
    (S : Sylow 2 (Sp F))
    (hSyl : (localSylow K e S : Subgroup K).map K.subtype = R ⊓ K)
    (E : Subgroup H) (hE : E ∈ elementaryAbelianMaxSubgroups R) :
    E ≤ (R ⊓ K) ⊔ (R ⊓ centralizer (K : Set H)) := by
  apply maximum_elementary_placement_of_coboundaries K e hF hn
    (half_frobenius_cocycle_coboundary hF hn) ?_ R hp hR S hSyl E hE
  intro hodd
  exact False.elim ((Nat.not_even_iff_odd.mpr hodd) heven)

/-- The marked A₅ configuration discharges both geometric premises in the
literal Thompson, omega-center and Baumann product identities. -/
theorem decomposition_of_marked_residual_in_borel {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    {L V : Subgroup H} (s : Marking L V)
    (R : Subgroup H) (hp : IsPGroup 2 R) (hR : R ≤ normalizer (K : Set H))
    (S : Sylow 2 (Sp F))
    (hSyl : (localSylow K e S : Subgroup K).map K.subtype = R ⊓ K)
    (hD : Lv L (markedV s) ≤ borelIn K e S) :
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ (R ⊓ K) ⊔
        elementaryAbelianMaxJ (R ⊓ centralizer (K : Set H)) ∧
    thompsonAlpha R = (center ↥(R ⊓ K)).map (R ⊓ K).subtype ⊔
        thompsonAlpha (R ⊓ centralizer (K : Set H)) ∧
    baumann R = (R ⊓ K) ⊔ baumann (R ⊓ centralizer (K : Set H)) := by
  have heven := even_degree_of_marked_residual_in_borel K e hF hn.le s S hD
  exact decomposition_of_local_geometry K e hF hn R S hSyl
    (maximum_elementary_placement_of_even_degree K e hF hn heven R hp hR S hSyl)
    (centralizer_omegaCenter_le_product K e hF hn R hR S hSyl)

/-- Source application: the normalized symplectic component configuration
proves B ≤ C_{M_V}(v), without any unproved local geometry or cocycle input. -/
theorem source_borel_containment_of_marked_residual {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    {L V : Subgroup H} (s : Marking L V) (T M : Subgroup H)
    (P : Sylow 2 (Gv (markedV s)))
    (hP : (P : Subgroup (Gv (markedV s))).map (Gv (markedV s)).subtype =
      Tv T (markedV s))
    (hK : K ≤ Gv (markedV s))
    (hTK : Tv T (markedV s) ≤ normalizer (K : Set H))
    (S : Sylow 2 (Sp F))
    (hSyl : (localSylow K e S : Subgroup K).map K.subtype = Tv T (markedV s) ⊓ K)
    (hD : Lv L (markedV s) ≤ borelIn K e S)
    (h1364 : baumann T = baumann (Tv T (markedV s)))
    (h1365 : Gv (markedV s) ⊓ normalizer (baumann T : Set H) ≤ Mv M (markedV s))
    (hMv : Mv M (markedV s) = normalizer (V : Set H) ⊓ Gv (markedV s)) :
    borelIn K e S ≤ normalizer (baumann T : Set H) ∧
      borelIn K e S ≤ normalizer (V : Set H) ⊓ Gv (markedV s) := by
  have heven := even_degree_of_marked_residual_in_borel K e hF hn.le s S hD
  have hp : IsPGroup 2 (Tv T (markedV s)) := hP ▸
    P.isPGroup'.map (Gv (markedV s)).subtype
  exact source_borel_containment_of_local_geometry K e hF hn T M V (markedV s)
    hK S hSyl
    (maximum_elementary_placement_of_even_degree K e hF hn heven
      (Tv T (markedV s)) hp hTK S hSyl)
    (centralizer_omegaCenter_le_product K e hF hn (Tv T (markedV s)) hTK S hSyl)
    h1364 h1365 hMv

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.SourceEvenDegree
