module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.LocalInverter.Actors
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.LocalInverter.Displacement
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.LocalInverter.Quotient
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.LocalInverter.Generation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.LocalInverter.ModuleKernel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.LocalInverter.ImageIndex
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.LocalInverter.MarkedInverter.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule.Quotient

/-!
# Local constructions for the terminal symplectic Borel argument

The higher-field Borel is two-perfect, so its actual action on V has the
same cubic image as Lᵥ. This gives both source indices equal to three and
nontriviality of B_C = O²(C_B(V)). The actual Tᵥ actors preserve the
specified T_K, and the Sylow intersection with L supplies an inverter of
Lᵥ/O₂(Lᵥ). Its order-three quotient is proved from the marked A₅ action.
The local module kernel and relative normalization show that this same
element centralizes B_C/O₂(B_C). An injective quotient map transports
the cubic and its inversion into the literal B/O₂(B).

`local_index_and_inverter` assembles these constructions from the earlier
marked configuration, the genuine component equivalence and placements,
and the intermediate containment B ≤ C_{M_V}(v). The 13.6.5 equality is
written with the source convention M = N_H(L) (printed p.876), so B's
normalization of L is derived. No index, inverter, quotient cardinal or
residual-centralization conclusion is an input. The higher source assembly
still supplies the earlier configuration and the Baumann containment before
applying the terminal contradiction; this is not the whole of 13.6.6.

Source: Aschbacher–Smith, proof of 13.6.6, printed pp.927–928.
-/

public section

open Subgroup Theory.SpecificGroups.SymplecticFour BinaryPermutation
open BinaryPermutation.FiveCentralizerGeometry
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.LocalInverter
open A5Module
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {L V : Subgroup H}

/-- The local conclusions consumed by the terminal symplectic contradiction.
The two indices concern the literal centralizer and its embedded two-residual.
The same constructed element of the specified Tᵥ ∩ L inverts the full Lᵥ
quotient, has the required ambient displacement on B_C, and inverts an element
of order three in B/O₂(B). The component action retains its centralizer kernel.

The inputs are the earlier marked module and normalizer action, the actual
local Sylow, the normalized component and Lᵥ placement, the 13.6.5 equality,
and the Baumann branch's intermediate Borel containment. -/
theorem local_index_and_inverter (K : Subgroup H) (e : K ≃* Sp F)
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Sp F)) (s : Marking L V) (T : Subgroup H)
    (hk : s.action.ker = pCore 2 L)
    (ρ : normalizer (V : Set H) →* Equiv.Perm (Fin 5))
    (hρ : ∀ (u : normalizer (V : Set H)) (w : Space),
      MulAut.conj (u : H) (s.map (Multiplicative.ofAdd w)) =
        s.map (Multiplicative.ofAdd (coreRepresentation (Fin 5) (ρ u) w)))
    (hagree : ∀ (l : L) (hl : (l : H) ∈ normalizer (V : Set H)),
      ρ ⟨l, hl⟩ = (s.action l).val)
    (hTL : T ≤ normalizer (L : Set H))
    (P : Sylow 2 (Gv (markedV s)))
    (hP : (P : Subgroup (Gv (markedV s))).map (Gv (markedV s)).subtype =
      Tv T (markedV s))
    (hTK : Tv T (markedV s) ≤ normalizer (K : Set H))
    (hSylow : (localSylow K e S : Subgroup K).map K.subtype =
      Tv T (markedV s) ⊓ K)
    (hD : Lv L (markedV s) ≤ borelIn K e S)
    (hlocal : Mv (normalizer (L : Set H)) (markedV s) =
      normalizer (V : Set H) ⊓ Gv (markedV s))
    (hB : borelIn K e S ≤ normalizer (V : Set H) ⊓ Gv (markedV s)) :
    (borelActionOnV K e S (hB.trans inf_le_left)).range = (lvActionOnV s).range ∧
    (centralizerInBorel K e S V ⊔ pCore 2 (localBorel K e S)).index = 3 ∧
    (centralizingResidual K e S V ⊔ pCore 2 (localBorel K e S)).index = 3 ∧
    centralizingResidual K e S V ≠ ⊥ ∧
    IsPGroup 2 (localActors K T (markedV s)) ∧
    ∃ x : localActors K T (markedV s),
      ((x : normalizer (K : Set H)) : H) ∈ Tv T (markedV s) ⊓ L ∧
      (∃ hxN : ((x : normalizer (K : Set H)) : H) ∈
          normalizer (Lv L (markedV s) : Set H),
        ∀ d : Lv L (markedV s),
          QuotientGroup.mk' (pCore 2 (Lv L (markedV s)))
            ((Lv L (markedV s)).normalizerMonoidHom
              ⟨((x : normalizer (K : Set H)) : H), hxN⟩ d) =
            (QuotientGroup.mk' (pCore 2 (Lv L (markedV s))) d)⁻¹) ∧
      (∀ c ∈ centralizingResidual K e S V,
        (borelMap K e S c)⁻¹ * ((x : normalizer (K : Set H)) : H) *
          borelMap K e S c * ((x : normalizer (K : Set H)) : H)⁻¹ ∈
          ((centralizingResidual K e S V).pCoreIn 2).map (borelMap K e S)) ∧
      ∃ b : localBorel K e S,
        orderOf (QuotientGroup.mk' (pCore 2 (localBorel K e S)) b) = 3 ∧
        QuotientGroup.mk' (pCore 2 (localBorel K e S))
          (borelActor K e hF hn.le S (localActors K T (markedV s))
            (localActors_stabilize K e S T (markedV s) hTK hSylow) x b) =
          (QuotientGroup.mk' (pCore 2 (localBorel K e S)) b)⁻¹ := by
  have hindex := centralizer_sup_twoCore_index K e S s ρ hρ hagree hF hn hB hD
  have hresidual := (residual_index K e hF hn.le S V).trans hindex
  have hTv : IsPGroup 2 (Tv T (markedV s)) := hP ▸
    P.isPGroup'.map (Gv (markedV s)).subtype
  have hBL : borelIn K e S ≤ normalizer (L : Set H) :=
    (hB.trans_eq hlocal.symm).trans inf_le_left
  have hcard := residualQuotient_card s hk
  obtain ⟨x, hx, hxN, hinv⟩ := exists_marked_inverter s T hk hTL P hP hcard
  let a : localActors K T (markedV s) := ⟨⟨x, hTK hx.1⟩, hx.1⟩
  refine ⟨borelActionOnV_range_eq K e S s ρ hρ hagree hF hn hB hD,
    hindex, hresidual, residual_ne_bot K e hF hn S V hresidual,
    hTv.comap_subtype, a, hx, ⟨hxN, hinv⟩, ?_, ?_⟩
  · exact residual_displacement_of_marking K e hF hn.le S _
      (localActors_stabilize K e S T (markedV s) hTK hSylow) s hk a hBL hx.2
  · exact exists_local_cubic_image K e hF hn.le S _
      (localActors_stabilize K e S T (markedV s) hTK hSylow)
      L (markedV s) hD hcard a hxN hinv

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.LocalInverter
