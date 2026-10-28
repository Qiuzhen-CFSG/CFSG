module

public import CFSG.Quasithin.ChapterG.Section09.Setup
public import Theory.Representation.Quotient
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.HighestVector
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.EmptySupport
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.Endpoints
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.LowerBound
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.AdjacentSupport
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.SeparatedSupport
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.MiddleRoot

/-!
# Classification of the small faithful irreducible binary PSL₄ modules

Every nonzero finite-dimensional binary SL₄ module has a local highest vector.
Empty support is excluded by faithfulness and irreducibility. Singleton support
at either endpoint forces degree four. Adjacent active roots force at least
twelve independent vectors, and the separated pair of endpoint roots forces
eleven. Thus the cutoff ten leaves only singleton support. Middle-root support
constructs an equivalence with the exterior square, and the exceptional
PSL₄(2)–A₈ comparison identifies it with the literal split orthogonal action.

The final theorem `small_modules` discharges both root inputs in the conditional
reductions below and transfers through the actual SL₄-to-PSL₄ quotient
equivalence. Its orthogonal alternative retains the group and linear
intertwining equivalences. The argument works over the binary field itself,
without an absolute-irreducibility or splitting-field assumption.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3(11)--(12),
printed pp.354,356--357. The final consumer is `four_alternatives_of_small_modules`
in the parent `BinaryLinearRecognition` module, which is deliberately not
imported here. The source's next degree fourteen is stronger than the lower
bound eleven needed by this cutoff.
-/

@[expose] public section

open Representation
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules

open Representation.BinaryLinearRecognition

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Empty support is impossible in a faithful irreducible module. -/
theorem LocalHighestVector.nonempty_of_faithful
    {ρ : Representation (ZMod 2) Group V} [IsIrreducible ρ]
    (hf : Function.Injective ρ) {J : Finset (Fin 3)} {v : V}
    (h : LocalHighestVector ρ J v) (hv : v ≠ 0) : J.Nonempty := by
  by_contra he
  have hJ := Finset.not_nonempty_iff_eq_empty.mp he
  subst J
  have hlow := four_le_finrank_of_faithful ρ hf
  have hone := h.finrank_eq_one_of_empty hv
  omega

/-- Below degree eleven only the separated pair of endpoint roots remains to
be excluded. Adjacent active roots already force twelve independent vectors. -/
theorem LocalHighestVector.singleton_of_small_of_separated_bound
    {ρ : Representation (ZMod 2) Group V} [IsIrreducible ρ]
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V ≤ 10)
    {J : Finset (Fin 3)} {v : V} (h : LocalHighestVector ρ J v) (hv : v ≠ 0)
    (hsep : LocalHighestVector ρ {0, 2} v → 11 ≤ Module.finrank (ZMod 2) V) :
    ∃ i, J = {i} := by
  have hpos := Finset.card_pos.mpr (h.nonempty_of_faithful hf hv)
  have hcard : J.card = 1 := by
    by_contra he
    have htwo : 2 ≤ J.card := by omega
    have hcases : (0 ∈ J ∧ 1 ∈ J) ∨ (1 ∈ J ∧ 2 ∈ J) ∨ J = {0, 2} := by
      have hex : ∀ J : Finset (Fin 3), 2 ≤ J.card →
          (0 ∈ J ∧ 1 ∈ J) ∨ (1 ∈ J ∧ 2 ∈ J) ∨ J = {0, 2} := by decide
      exact hex J htwo
    rcases hcases with ⟨h0, h1⟩ | ⟨h1, h2⟩ | rfl
    · have hh := h.twelve_le_finrank_of_adjacent hv h0 h1 (by decide)
      omega
    · have hh := h.twelve_le_finrank_of_adjacent hv h1 h2 (by decide)
      omega
    · have hh := hsep h
      omega
  exact Finset.card_eq_one.mp hcard

/-- Assembly on the determinant-one matrix group from an explicit separated-root
bound and middle-root identification. -/
theorem linear_small_modules_of_root_inputs
    (ρ : Representation (ZMod 2) Group V) (hf : Function.Injective ρ)
    [IsIrreducible ρ] (hd : Module.finrank (ZMod 2) V ≤ 10)
    (hsep : ∀ v : V, v ≠ 0 → LocalHighestVector ρ {0, 2} v →
      11 ≤ Module.finrank (ZMod 2) V)
    (hmiddle : ∀ v : V, v ≠ 0 → LocalHighestVector ρ {1} v →
      Quasiequivalent ρ orthogonalEightAction) :
    Module.finrank (ZMod 2) V = 4 ∨ Quasiequivalent ρ orthogonalEightAction := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨J, v, hv, h⟩ := exists_localHighestVector ρ
  obtain ⟨i, rfl⟩ := h.singleton_of_small_of_separated_bound hf hd hv (hsep v hv)
  have hlow := four_le_finrank_of_faithful ρ hf
  fin_cases i
  · have hhigh := h.finrank_le_four_of_endpoint hv (Or.inl rfl)
    exact Or.inl (by omega)
  · exact Or.inr (hmiddle v hv h)
  · have hhigh := h.finrank_le_four_of_endpoint hv (Or.inr rfl)
    exact Or.inl (by omega)

/-- The exact universal input used by `four_alternatives_of_small_modules`,
conditional only on the two root calculations named here. The actual quotient
and intertwining maps transfer the result from SL₄(2) to PSL₄(2). -/
theorem small_modules_of_root_inputs
    (hsep : ∀ (ρ : Representation (ZMod 2) Group V) (v : V),
      v ≠ 0 → LocalHighestVector ρ {0, 2} v → 11 ≤ Module.finrank (ZMod 2) V)
    (hmiddle : ∀ (ρ : Representation (ZMod 2) Group V), IsIrreducible ρ →
      ∀ v : V, v ≠ 0 → LocalHighestVector ρ {1} v →
      Quasiequivalent ρ orthogonalEightAction)
    (σ : Representation (ZMod 2) PSL(4, ZMod 2) V)
    (hf : Function.Injective σ) (hi : IsIrreducible σ)
    (hd : Module.finrank (ZMod 2) V ≤ 10) :
    Module.finrank (ZMod 2) V = 4 ∨ Quasiequivalent σ orthogonalEightAction := by
  let e : Group ≃* PSL(4, ZMod 2) := Atlas.Order20160A8.sl4TwoEquivPSL
  let ρ := σ.comp e.toMonoidHom
  let : IsIrreducible ρ :=
    (irreducible_comp_surjective_iff e.toMonoidHom e.surjective σ).mpr hi
  have hfaith : Function.Injective ρ := hf.comp e.injective
  rcases linear_small_modules_of_root_inputs ρ hfaith hd (hsep ρ)
      (hmiddle ρ inferInstance) with hfour | hortho
  · exact Or.inl hfour
  · obtain ⟨E, f, hinter⟩ := hortho
    refine Or.inr ⟨e.symm.trans E, f, ?_⟩
    intro g v
    have hh := hinter (e.symm g) v
    simpa [ρ] using hh

/-- Every faithful irreducible binary PSL₄ module of degree at most ten has
degree four or is quasiequivalent to the literal six-dimensional orthogonal
A₈ action. This supplies the universal module input of
`four_alternatives_of_small_modules`. -/
theorem small_modules
    (σ : Representation (ZMod 2) PSL(4, ZMod 2) V)
    (hf : Function.Injective σ) (hi : IsIrreducible σ)
    (hd : Module.finrank (ZMod 2) V ≤ 10) :
    Module.finrank (ZMod 2) V = 4 ∨ Quasiequivalent σ orthogonalEightAction := by
  apply small_modules_of_root_inputs ?_ ?_ σ hf hi hd
  · intro ρ v hv h
    exact h.eleven_le_finrank_of_separated hv
  · intro ρ hi v hv h
    let : IsIrreducible ρ := hi
    exact h.quasiequivalent_orthogonalEight_of_middle hv

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
