module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.LocalInverter.MarkedInverter
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.LocalInverter.Actors
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.LocalInverter.Quotient
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.LocalInverter.ModuleKernel

/-!
# The constructed inverter in the actual symplectic Borel

The marking and the specified local Sylow supply an element of Tᵥ ∩ L
inverting Lᵥ/O₂(Lᵥ). Embed that same element in the actual component
normalizer actors. The parent quotient transport then supplies a cubic
B/O₂(B) image that it inverts, while the module-kernel displacement theorem
proves that it centralizes B_C/O₂(B_C).

This discharges the actor-existence premise of the terminal Borel argument.
The quotient cardinal and the relative Borel placements remain the explicit
earlier-source inputs of the higher assembly; the Borel centralizer index
is a separate step of that assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.6.6, printed p.928 (PDF p.945).
-/

public section

open Subgroup Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.LocalInverter
open A5Module
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]
variable {L V : Subgroup H}

/-- One element of the specified Tᵥ simultaneously centralizes the
centralizing residual modulo its two-core and inverts a cubic in B/O₂(B).
This applies both parent constructions with their literal normalizer actions. -/
theorem exists_marked_borel_inverter (K : Subgroup H) (e : K ≃* Sp F)
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (s : Marking L V) (T : Subgroup H)
    (hk : s.action.ker = pCore 2 L) (hTL : T ≤ normalizer (L : Set H))
    (P : Sylow 2 (Gv (markedV s)))
    (hP : (P : Subgroup (Gv (markedV s))).map (Gv (markedV s)).subtype = Tv T (markedV s))
    (hcard : Nat.card (Lv L (markedV s) ⧸ pCore 2 (Lv L (markedV s))) = 3)
    (hTK : Tv T (markedV s) ≤ normalizer (K : Set H))
    (hSylow : (localSylow K e S : Subgroup K).map K.subtype = Tv T (markedV s) ⊓ K)
    (hD : Lv L (markedV s) ≤ borelIn K e S)
    (hBL : borelIn K e S ≤ normalizer (L : Set H)) :
    ∃ x : localActors K T (markedV s),
      ((x : normalizer (K : Set H)) : H) ∈ L ∧
      (∀ c ∈ centralizingResidual K e S V,
        (borelMap K e S c)⁻¹ * ((x : normalizer (K : Set H)) : H) *
          borelMap K e S c * ((x : normalizer (K : Set H)) : H)⁻¹ ∈
          ((centralizingResidual K e S V).pCoreIn 2).map (borelMap K e S)) ∧
      ∃ b : localBorel K e S,
        orderOf (QuotientGroup.mk' (pCore 2 (localBorel K e S)) b) = 3 ∧
        QuotientGroup.mk' (pCore 2 (localBorel K e S))
          (borelActor K e hF hn S (localActors K T (markedV s))
            (localActors_stabilize K e S T (markedV s) hTK hSylow) x b) =
          (QuotientGroup.mk' (pCore 2 (localBorel K e S)) b)⁻¹ := by
  obtain ⟨x, hx, hxN, hinv⟩ := exists_marked_inverter s T hk hTL P hP hcard
  let a : localActors K T (markedV s) := ⟨⟨x, hTK hx.1⟩, hx.1⟩
  have haL : ((a : normalizer (K : Set H)) : H) ∈ L := hx.2
  refine ⟨a, haL, ?_, ?_⟩
  · exact residual_displacement_of_marking K e hF hn S _
      (localActors_stabilize K e S T (markedV s) hTK hSylow) s hk a hBL haL
  · exact exists_local_cubic_image K e hF hn S _
      (localActors_stabilize K e S T (markedV s) hTK hSylow)
      L (markedV s) hD hcard a hxN hinv

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.LocalInverter
