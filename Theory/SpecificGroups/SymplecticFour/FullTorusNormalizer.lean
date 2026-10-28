module
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
public import Theory.GroupTheory.CyclicHallNormalizerEscape

/-!
# Full split-torus normalizer escape in symplectic degree four

The standard form matrix interchanges both hyperbolic halves, simultaneously
inverting the two coordinates of the full split torus. It lies outside the
literal flag Borel and normalizes every subgroup of that torus.

The determinant characters split the Borel over its unipotent kernel, so the
full torus has two-primary index. Sylow conjugacy therefore places any odd
primary subgroup of the Borel into the torus by a Borel element. Conjugating
the form matrix back proves normalizer escape for the original subgroup.

This is the full-Cartan inversion in the symplectic case of Aschbacher--Smith,
Lemma 4.4.13(1), printed pp.623--624. In particular, no restriction to a
one-coordinate cyclic torus is imposed. The final characteristic-two theorem
retains the nonbinary field hypothesis of the source model.
-/

@[expose] public noncomputable section
open Matrix Subgroup
namespace Theory.SpecificGroups.SymplecticFour.FullTorusNormalizer
open EvenBorelTorus
variable {F : Type*} [Field F]

/-- The full rank-two split torus inside the literal flag Borel. -/
def torusInBorel : Subgroup (borel (F := F)) := torusSection.range

/-- The same full torus in the literal symplectic matrix group. -/
def torus : Subgroup (Sp F) := (borel.subtype.comp torusSection).range

theorem torus_le_borel : torus (F := F) ≤ borel := by
  rintro _ ⟨x, rfl⟩
  exact (torusSection x).property

private theorem symJ_intertwine (a b : Fˣ) :
    SymplecticGroup.symJ (Fin 2) F * diagonalTorus a b =
      diagonalTorus a⁻¹ b⁻¹ * SymplecticGroup.symJ (Fin 2) F := by
  apply Subtype.ext
  change J _ _ * diagonal _ = diagonal _ * J _ _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.J, Matrix.fromBlocks]

/-- The form matrix simultaneously inverts both independent diagonal parameters. -/
theorem symJ_conj_diagonalTorus (a b : Fˣ) :
    SymplecticGroup.symJ (Fin 2) F * diagonalTorus a b *
        (SymplecticGroup.symJ (Fin 2) F)⁻¹ = (diagonalTorus a b)⁻¹ := by
  have hi : diagonalTorus a⁻¹ b⁻¹ = (diagonalTorus a b)⁻¹ :=
    (CentralRootGeometry.diagonalTorusHom (F := F)).map_inv (a,b)
  rw [symJ_intertwine, mul_inv_cancel_right, hi]

theorem symJ_not_mem_borel : SymplecticGroup.symJ (Fin 2) F ∉ borel := by
  intro hw
  have he := ((mem_borel_iff _).mp hw).2 0 0
  simp [SymplecticGroup.symJ, Matrix.J, Matrix.fromBlocks] at he

theorem symJ_conj_torus (x : Sp F) (hx : x ∈ torus) :
    SymplecticGroup.symJ (Fin 2) F * x * (SymplecticGroup.symJ (Fin 2) F)⁻¹ = x⁻¹ := by
  obtain ⟨a, rfl⟩ := hx
  exact symJ_conj_diagonalTorus _ _

private theorem ker_sup_torusInBorel :
    (borelCharacters (F := F)).ker ⊔ torusInBorel = ⊤ := by
  apply top_unique
  intro b _
  have hk : b * (torusSection (borelCharacters b))⁻¹ ∈ (borelCharacters (F := F)).ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, characters_torusSection, mul_inv_cancel]
  have ht : torusSection (borelCharacters b) ∈ torusInBorel :=
    ⟨borelCharacters b, rfl⟩
  simpa only [inv_mul_cancel_right] using
    ((borelCharacters (F := F)).ker ⊔ torusInBorel).mul_mem
      (show b * (torusSection (borelCharacters b))⁻¹ ∈
        (borelCharacters (F := F)).ker ⊔ torusInBorel from
        (le_sup_left : (borelCharacters (F := F)).ker ≤ _ ) hk)
      (show torusSection (borelCharacters b) ∈
        (borelCharacters (F := F)).ker ⊔ torusInBorel from
        (le_sup_right : torusInBorel ≤ _ ) ht)

/-- Simultaneous inversion preserves every subgroup of the full torus. -/
theorem symJ_mem_normalizer_of_le_torus (A : Subgroup (Sp F)) (hA : A ≤ torus) :
    SymplecticGroup.symJ (Fin 2) F ∈ normalizer (A : Set (Sp F)) := by
  rw [mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    change SymplecticGroup.symJ (Fin 2) F * a *
      (SymplecticGroup.symJ (Fin 2) F)⁻¹ ∈ A
    rw [symJ_conj_torus a (hA ha)]
    exact A.inv_mem ha
  · intro a ha
    refine ⟨a⁻¹, A.inv_mem ha, ?_⟩
    change SymplecticGroup.symJ (Fin 2) F * a⁻¹ *
      (SymplecticGroup.symJ (Fin 2) F)⁻¹ = a
    rw [symJ_conj_torus _ (torus.inv_mem (hA ha)), inv_inv]

variable [Finite F]

theorem prime_not_dvd_torusInBorel_index {n p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = 2 ^ n) (hp : Odd p) :
    ¬ p ∣ (torusInBorel (F := F)).index := by
  have hd := Theory.GroupTheory.index_dvd_of_normal_supplement
    (borelCharacters (F := F)).ker torusInBorel ker_sup_torusInBorel
  have hk : IsPGroup 2 (borelCharacters (F := F)).ker := by
    rw [characters_ker]
    exact (isPGroup_unipotent hF).comap_subtype
  obtain ⟨k, hk⟩ := hk.exists_card_eq
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mp
  apply Nat.Coprime.of_dvd_right hd
  rw [hk]
  exact hp.coprime_two_right.pow_right k

/-- Every odd-primary subgroup of the actual Borel has an escaping normalizer. -/
theorem odd_normalizer_not_le_borel_of_card_eq_pow {n p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = 2 ^ n) (hp : Odd p)
    (A : Subgroup (Sp F)) (hA : IsPGroup p A) (hAB : A ≤ borel) :
    ¬ normalizer (A : Set (Sp F)) ≤ borel := by
  obtain ⟨g, hg⟩ := Theory.GroupTheory.exists_conj_le_of_prime_not_dvd_index
    torusInBorel (A.subgroupOf borel) (prime_not_dvd_torusInBorel_index hF hp)
    hA.comap_subtype
  have hconj : A.map (MulAut.conj (g : Sp F)).toMonoidHom ≤ torus := by
    rintro _ ⟨a, ha, rfl⟩
    have ht := hg ⟨⟨a, hAB ha⟩, ha, rfl⟩
    obtain ⟨x, hx⟩ := ht
    exact ⟨x, congrArg Subtype.val hx⟩
  have hw := symJ_mem_normalizer_of_le_torus _ hconj
  intro hN
  apply symJ_not_mem_borel (F := F)
  have hnConj : normalizer
      (A.map (MulAut.conj (g : Sp F)).toMonoidHom : Set (Sp F)) ≤ borel := by
    rw [← map_equiv_normalizer_eq]
    rintro _ ⟨x, hx, rfl⟩
    exact borel.mul_mem (borel.mul_mem g.property (hN hx)) (borel.inv_mem g.property)
  exact hnConj hw

/-- The source nonbinary characteristic-two model, retaining the original subgroup. -/
theorem odd_normalizer_not_le_borel [CharP F 2]
    (_hF : 2 < Nat.card F) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup (Sp F)) (hA : IsPGroup p A) (hAB : A ≤ borel) :
    ¬ normalizer (A : Set (Sp F)) ≤ borel := by
  let := Fintype.ofFinite F
  obtain ⟨n, _, hn⟩ := FiniteField.card F 2
  exact odd_normalizer_not_le_borel_of_card_eq_pow
    (by simpa only [Nat.card_eq_fintype_card] using hn) hp A hA hAB

end Theory.SpecificGroups.SymplecticFour.FullTorusNormalizer
