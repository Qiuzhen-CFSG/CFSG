module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.RelativeNormalizer

/-!
# Folded exchange and the two cells of a triality root parabolic

The marked split Weyl subgroup fixes a root: e₁ + e₂ for the three arms,
and e₁ + e₄ for the central node. The checked D₄ root tables show that its
intersection with the twelve relative Weyl words consists precisely of the
identity and the corresponding folded reflection.

Iterating split simple-reflection exchange keeps the possible cell indices
inside that marked Weyl subgroup times the original index. Fixed-cell coverage
and split index uniqueness then reduce these possibilities to the two relative
cells. The same Weyl intersection, through the original root-parabolic
membership criterion, gives the two-cell decomposition of each parabolic.

The positive folded root element at parameter one witnesses nontriviality.
Its negative conjugate cannot lie in the Borel: the rank-one root word would
then put the nonidentity Weyl representative in the Borel, contradicting the
proved matrix-cell separation. These arguments use the original carrier and
subgroups for every positive binary exponent, including q = 2.

Source: GLS3 2.3.4(b), 2.3.5, §2.4 and 2.6.4–5
(`refs/KGroup/GLS3/chapter2.tex`). These are the concrete geometry inputs to the
triality parabolic amalgam appearing in Aschbacher–Smith F.1.12(4)
(`refs/quasithin.pdf`); no amalgam classification is asserted here.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates.SumExchangeData
namespace Triality.Standard.ConcreteBruhat.FoldedCellGeometry
open Parabolics DiagramFixed
noncomputable section

private def numberedWeyl : rootWeylGroup →* Equiv.Perm (Fin 24) :=
  rootEnumeration.symm.permCongrHom.toMonoidHom.comp rootWeylGroup.subtype

private lemma numbered_generator (i : Fin 4) :
    numberedWeyl (rootWeylGenerator i) = reflection i := by
  apply Equiv.ext
  intro r
  change rootEnumeration.symm (rootReflection i (rootEnumeration r)) = reflectionTable i r
  rw [rootReflection, ← rootEnumeration_reflectionTable, Equiv.symm_apply_apply]

private lemma numbered_representative (w : DihedralGroup 6) :
    numberedWeyl (rootRepresentative w) = representative w := by
  cases w <;>
    simp [rootRepresentative, representative, foldedRootReflection, map_mul, map_pow,
      numbered_generator, arm]

private def markedRoot : Node → Fin 24
  | .arms => 0
  | .central => 8

private lemma generator_fixes_marked (a : Node) (i : Fin 4) (hi : i ∈ a.support) :
    reflection i (markedRoot a) = markedRoot a := by
  cases a <;> fin_cases i <;>
    simp_all [Node.support, reflection, reflectionTable, markedRoot]

private lemma representative_fixes_marked_iff (a : Node) (w : DihedralGroup 6) :
    representative w (markedRoot a) = markedRoot a ↔ w = 1 ∨ w = relativeReflection a := by
  rw [representative_apply]
  cases a <;> revert w <;> decide +kernel

private lemma parabolic_fixes_marked (a : Node) {w : rootWeylGroup}
    (hw : w ∈ SplitNormalForm.parabolicWeyl a) :
    numberedWeyl w (markedRoot a) = markedRoot a := by
  induction hw using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, hi, rfl⟩ := hg
    rw [numbered_generator]
    exact generator_fixes_marked a i hi
  | one => simp
  | mul g h _ _ hg hh => simp only [map_mul, Equiv.Perm.mul_apply, hg, hh]
  | inv g _ hg =>
    apply (numberedWeyl g).injective
    simpa only [map_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using hg.symm

/-- The folded reflection uses exactly the simple generators of its marked
split parabolic Weyl subgroup. -/
theorem foldedRootReflection_mem_parabolicWeyl (a : Node) :
    foldedRootReflection a ∈ SplitNormalForm.parabolicWeyl a := by
  have h (i : Fin 4) (hi : i ∈ a.support) :
      rootWeylGenerator i ∈ SplitNormalForm.parabolicWeyl a :=
    Subgroup.subset_closure ⟨i, hi, rfl⟩
  cases a with
  | arms =>
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (h 0 (by simp [Node.support])) (h 2 (by simp [Node.support])))
      (h 3 (by simp [Node.support]))
  | central => exact h 1 (by simp [Node.support])

/-- Among the twelve relative Weyl words, precisely the identity and the
marked reflection belong to the original split parabolic Weyl subgroup. -/
theorem rootRepresentative_mem_parabolicWeyl_iff (a : Node) (w : DihedralGroup 6) :
    rootRepresentative w ∈ SplitNormalForm.parabolicWeyl a ↔
      w = 1 ∨ w = relativeReflection a := by
  constructor
  · intro hw
    apply (representative_fixes_marked_iff a w).mp
    rw [← numbered_representative]
    exact parabolic_fixes_marked a hw
  · rintro (rfl | rfl)
    · rw [rootRepresentative_one]
      exact Subgroup.one_mem _
    · rw [rootRepresentative_simple]
      exact foldedRootReflection_mem_parabolicWeyl a

section Binary
variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn
local notation "D" => InputRealization.inputs P rfl

/-- The original root-defined parabolic is the union of its two relative cells. -/
theorem mem_parabolic_iff (a : Node) (g : Carrier P) :
    g ∈ parabolic P a ↔ g ∈ borel P ∨ g ∈ cell P rfl (relativeReflection a) := by
  rw [FixedDescent.mem_parabolic_iff_exists_cell n hn]
  constructor
  · rintro ⟨w, hw, hg⟩
    rcases (rootRepresentative_mem_parabolicWeyl_iff a w).mp hw with rfl | rfl
    · exact Or.inl ((cell_one P rfl).le hg)
    · exact Or.inr hg
  · rintro (hb | hs)
    · exact ⟨1, (rootRepresentative_mem_parabolicWeyl_iff a 1).mpr (Or.inl rfl),
        (cell_one P rfl).ge hb⟩
    · exact ⟨relativeReflection a,
        (rootRepresentative_mem_parabolicWeyl_iff a _).mpr (Or.inr rfl), hs⟩

/-- Two-cell coverage in the form used to assemble the root-parabolic generators. -/
theorem parabolic_cell_cover (a : Node) (g : Carrier P) (hg : g ∈ parabolic P a) :
    g ∈ borel P ∨ g ∈ cell P rfl (relativeReflection a) :=
  (mem_parabolic_iff n hn a g).mp hg

/-- The positive folded root element at parameter one has a negative conjugate
outside the Borel, including over the smallest binary field. -/
theorem positive_conjugate_not_borel (a : Node) :
    simpleRepresentative P rfl a * rootElement P rfl true a 1 *
      simpleRepresentative P rfl a ∉ borel P := by
  rw [simpleRepresentative_positive P rfl a 1]
  intro hneg
  have hpos := unipotent_le_borel P (positive_mem_unipotent P rfl a 1)
  have hs : simpleRepresentative P rfl a ∈ borel P := by
    rw [simpleRepresentative_eq_root_word P rfl a]
    exact (borel P).mul_mem ((borel P).mul_mem hpos hneg) hpos
  have he : relativeReflection a = 1 :=
    (RelativeNormalizer.representative_mem_borel_iff n hn _).mp
      ((weylRepresentative_simple P rfl a).symm ▸ hs)
  exact (relativeReflection_involution a).1 he

/-- An explicit Borel element witnesses the nontriviality axiom at either node. -/
theorem exists_borel_conjugate_not_borel (a : Node) :
    ∃ b ∈ borel P, simpleRepresentative P rfl a * b *
      simpleRepresentative P rfl a ∉ borel P :=
  ⟨rootElement P rfl true a 1,
    unipotent_le_borel P (positive_mem_unipotent P rfl a 1),
    positive_conjugate_not_borel n hn a⟩

private lemma simple_mul_cell (i : Fin 4) (w : rootWeylGroup)
    {g : SplitGroup P} (hg : g ∈ SplitNormalForm.cell D w) :
    (D).lift (rootWeylGenerator i) * g ∈
      SplitNormalForm.cell D (rootWeylGenerator i * w) ∪ SplitNormalForm.cell D w := by
  obtain ⟨b, hb, c, hc, rfl⟩ := hg
  rcases SplitNormalForm.simple_reflection_exchange n hn D i w hb with h | h
  · exact Or.inl (by simpa only [mul_assoc] using
      SplitNormalForm.mul_borel_mem_cell D _ hc h)
  · exact Or.inr (by simpa only [mul_assoc] using
      SplitNormalForm.mul_borel_mem_cell D _ hc h)

private lemma simple_mul_parabolic_cells (a : Node) (w : rootWeylGroup)
    (i : Fin 4) (hi : i ∈ a.support) {g : SplitGroup P}
    (hg : ∃ v ∈ SplitNormalForm.parabolicWeyl a, g ∈ SplitNormalForm.cell D (v * w)) :
    ∃ v ∈ SplitNormalForm.parabolicWeyl a,
      (D).lift (rootWeylGenerator i) * g ∈ SplitNormalForm.cell D (v * w) := by
  obtain ⟨v, hv, hg⟩ := hg
  rcases simple_mul_cell n hn i (v * w) hg with h | h
  · refine ⟨rootWeylGenerator i * v,
      (SplitNormalForm.parabolicWeyl a).mul_mem (Subgroup.subset_closure ⟨i, hi, rfl⟩) hv, ?_⟩
    simpa only [mul_assoc] using h
  · exact ⟨v, hv, h⟩

private lemma folded_split_exchange (a : Node) (w : rootWeylGroup)
    {b : SplitGroup P} (hb : b ∈ splitBorel P) :
    ∃ v ∈ SplitNormalForm.parabolicWeyl a,
      (D).lift (foldedRootReflection a) * b * (D).lift w ∈
        SplitNormalForm.cell D (v * w) := by
  have hstart : ∃ v ∈ SplitNormalForm.parabolicWeyl a,
      b * (D).lift w ∈ SplitNormalForm.cell D (v * w) :=
    ⟨1, Subgroup.one_mem _, b, hb, 1, (splitBorel P).one_mem, by simp only [one_mul, mul_one]⟩
  cases a with
  | central =>
    simpa only [foldedRootReflection, mul_assoc] using
      simple_mul_parabolic_cells n hn .central w 1 (by simp [Node.support]) hstart
  | arms =>
    have h3 := simple_mul_parabolic_cells n hn .arms w 3 (by simp [Node.support]) hstart
    have h2 := simple_mul_parabolic_cells n hn .arms w 2 (by simp [Node.support]) h3
    have h0 := simple_mul_parabolic_cells n hn .arms w 0 (by simp [Node.support]) h2
    simpa only [foldedRootReflection, map_mul, mul_assoc] using h0

/-- Folded exchange on the actual characteristic-two triality carrier. -/
theorem simple_reflection_exchange (a : Node) (w : DihedralGroup 6)
    {b : Carrier P} (hb : b ∈ borel P) :
    simpleRepresentative P rfl a * b * weylRepresentative P rfl w ∈
      cell P rfl (relativeReflection a * w) ∪ cell P rfl w := by
  let g := simpleRepresentative P rfl a * b * weylRepresentative P rfl w
  obtain ⟨z, hz⟩ := FixedDescent.exists_mem_cell n hn g
  obtain ⟨v, hv, hvcell⟩ := folded_split_exchange n hn a (rootRepresentative w)
    ((FixedDescent.mem_descend_iff P rfl (splitBorel P) b).mp hb)
  have hsplit : FixedDescent.carrierToSplit P rfl g =
      (D).lift (foldedRootReflection a) * FixedDescent.carrierToSplit P rfl b *
        (D).lift (rootRepresentative w) := by
    simp only [g, map_mul, RelativeNormalizer.carrierToSplit_simple P rfl a,
      FixedDescent.carrierToSplit_representative P rfl w,
      ← FixedDescent.lift_rootRepresentative P rfl (relativeReflection a),
      ← FixedDescent.lift_rootRepresentative P rfl w, rootRepresentative_simple]
  have hindex : rootRepresentative z = v * rootRepresentative w :=
    SplitNormalForm.cell_index_unique n hn D
      ((FixedDescent.mem_cell_iff_split n hn z g).mp hz) (hsplit.symm ▸ hvcell)
  have hpar : rootRepresentative (z * w⁻¹) ∈ SplitNormalForm.parabolicWeyl a := by
    have he : rootRepresentative (z * w⁻¹) = v := by
      change rootRepresentativeHom (z * w⁻¹) = v
      rw [map_mul, map_inv]
      change rootRepresentative z * (rootRepresentative w)⁻¹ = v
      rw [hindex, mul_inv_cancel_right]
    exact he.symm ▸ hv
  rcases (rootRepresentative_mem_parabolicWeyl_iff a (z * w⁻¹)).mp hpar with he | he
  · have hzw : z = w := (mul_inv_eq_one.mp he)
    exact Or.inr (by simpa only [hzw] using hz)
  · have hzw : z = relativeReflection a * w := (mul_inv_eq_iff_eq_mul.mp he)
    exact Or.inl (by simpa only [hzw] using hz)

end Binary
end
end Triality.Standard.ConcreteBruhat.FoldedCellGeometry
