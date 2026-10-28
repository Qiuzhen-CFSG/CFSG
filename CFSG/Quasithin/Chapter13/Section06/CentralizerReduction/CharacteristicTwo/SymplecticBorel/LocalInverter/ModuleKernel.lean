module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.ModuleMarking
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.LocalInverter.Displacement

/-!
# The marked A₅ module supplies the local centralizer kernel

Equivariance of the faithful marking proves L ≤ N_H(V). Three explicit
vectors detect every nonidentity A₅ permutation, so the earlier identity
ker(L → A₅) = O₂(L) gives C_L(V) ≤ O₂(L). Applying the displacement
theorem now proves the required centralization of B_C/O₂(B_C) directly
from the marked local module and the relative placement B ≤ N_H(L).

Source: Aschbacher–Smith, §13.2 setup on printed pp.876–877 and the
proof of 13.6.6 on printed pp.927–928.
-/

@[expose] public section

open Subgroup Theory.SpecificGroups.SymplecticFour
open BinaryPermutation.FiveCentralizerGeometry
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.LocalInverter
open A5Module
private theorem faithful : ∀ g : alternatingGroup (Fin 5),
    act g z = z → act g v = v → act g a = a → g = 1 := by
  decide +kernel

variable {H F : Type*} [Group H] [Field F] [Finite H] [Finite F]
variable {L V : Subgroup H}

omit [Field F] [Finite H] [Finite F] in
theorem marking_normalizes (s : Marking L V) : L ≤ normalizer (V : Set H) := by
  apply le_normalizer_iff.mpr
  intro l hl w hw
  obtain ⟨a, rfl⟩ := s.range_eq.symm ▸ hw
  have he := s.equivariant ⟨l, hl⟩ a.toAdd
  change l * s.map a * l⁻¹ = _ at he
  rw [he]
  exact s.range_eq.le ⟨_, rfl⟩

omit [Field F] [Finite H] [Finite F] in
theorem marking_centralizer_le_core (s : Marking L V)
    (hk : s.action.ker = pCore 2 L) : L ⊓ centralizer (V : Set H) ≤ L.pCoreIn 2 := by
  intro l hl
  have hfix (a : Space) : act (s.action ⟨l, hl.1⟩) a = a := by
    apply Multiplicative.ofAdd.injective
    apply s.injective
    rw [← s.equivariant]
    have ha : s.map (Multiplicative.ofAdd a) ∈ V := s.range_eq.le ⟨_, rfl⟩
    change l * s.map (Multiplicative.ofAdd a) * l⁻¹ = s.map (Multiplicative.ofAdd a)
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hl.2 _ ha).symm
  have hf := faithful (s.action ⟨l, hl.1⟩) (hfix z) (hfix v) (hfix a)
  exact ⟨⟨l, hl.1⟩, hk ▸ hf, rfl⟩

/-- Discharge the module normalizer and kernel premises for the actual marked
A₅ configuration. B's placement in N_H(L) and membership of x in L are the
remaining group placements; no residual centralization is assumed. -/
theorem residual_displacement_of_marking (K : Subgroup H) (e : K ≃* Sp F)
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (A : Subgroup (normalizer (K : Set H)))
    (hS : ∀ x ∈ A, (S : Subgroup (Sp F)).map (modelAction K e x).toMonoidHom = S)
    (s : Marking L V) (hk : s.action.ker = pCore 2 L) (x : A)
    (hBL : borelIn K e S ≤ normalizer (L : Set H))
    (hxL : ((x : normalizer (K : Set H)) : H) ∈ L) :
    ∀ c ∈ centralizingResidual K e S V,
      (borelMap K e S c)⁻¹ * ((x : normalizer (K : Set H)) : H) *
        borelMap K e S c * ((x : normalizer (K : Set H)) : H)⁻¹ ∈
        ((centralizingResidual K e S V).pCoreIn 2).map (borelMap K e S) :=
  residual_displacement K e hF hn S A hS L V x hBL
    (marking_normalizes s) (marking_centralizer_le_core s hk) hxL
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.LocalInverter
