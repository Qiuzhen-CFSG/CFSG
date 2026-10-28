module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.Common

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SmallBinaryCases
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The binary linear branches of the source irreducible action

The completed G.9 small-module recognition for PSL₄(2) and PSL₅(2)
supplies the exact alternatives consumed by the existing source sieve.
The degree-ten SL₅ premise is discharged by the proved exterior square/cube
classification. Field transport connects the literal Theorem C models.

Source: Aschbacher--Smith, G.9.3(11)--(13) and15.3.58,
printed pp.354--357 and1149.
-/

public section

open Subgroup Representation
open scoped MatrixGroups
open CFSG.Quasithin.ChapterG.Section09
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

/-- The completed PSL₄(2) alternatives feed the existing source sieve. -/
theorem SourceData.not_binary_four_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K)
    (hc : ComponentHypothesis KnownSimple.IsKnownSimple ρ X K K (s + 1))
    (e : K ≃* PSL(4,ZMod 2)) : False := by
  apply SmallBinaryCases.exclude h hK
  rcases BinaryLinearRecognition.four_alternatives hc e with ⟨hq, hd, hm⟩ | ⟨hq, hd, hm⟩
  · exact .binaryFourNatural hq hd hm
  · exact .orthogonalEight hq hd hm

/-- The actual PSL₅(2) action is excluded with no degree-ten classification premise. -/
theorem SourceData.not_binary_five_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K)
    (hc : ComponentHypothesis KnownSimple.IsKnownSimple ρ X K K (s + 1))
    (e : K ≃* PSL(5,ZMod 2)) : False := by
  have hten : ∀ σ : Representation (ZMod 2) Representation.SL5TenDimensional.Group W,
      Representation.IsIrreducible σ → Module.finrank (ZMod 2) W = 10 →
      Nonempty (σ.Equiv (Representation.SL5TenDimensional.exteriorAction 2)) ∨
      Nonempty (σ.Equiv (Representation.SL5TenDimensional.exteriorAction 3)) := by
    intro σ hi hd
    let := hi
    exact Representation.SL5TenDimensional.Classification.identification_of_finrank_ten σ hd
  rcases BinaryLinearRecognition.five_alternatives_of_ten_classification hc e hten with
    ⟨_, hd, _⟩ | ⟨he, _, hd, hm⟩
  · have := h.six_le_degree
    omega
  · exact SmallBinaryCases.exclude h hK (.binaryFive he (.inr ⟨hd, hm⟩))

/-- Both literal binary linear alternatives in Theorem C are impossible. -/
theorem SourceData.not_binary_linear_model (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K)
    (hc : ComponentHypothesis KnownSimple.IsKnownSimple ρ X K K (s + 1))
    (n : ℕ) (hn : n = 4 ∨ n = 5) (he : ClassicalGroup.IsPSL K n 2) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, hF]
    simp)
  let e' := e.trans (Atlas.fieldEquivPSL n eF)
  rcases hn with rfl | rfl
  · exact h.not_binary_four_component hK hc e'
  · exact h.not_binary_five_component hK hc e'

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
