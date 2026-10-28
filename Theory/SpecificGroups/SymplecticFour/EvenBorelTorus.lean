module

public import Theory.SpecificGroups.SymplecticFour.Sylow.OddSubgroups
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Torus
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The rank-two split torus of an even symplectic Borel

The point and plane determinant characters give a surjection from the actual
flag Borel onto Fˣ × Fˣ. Its matrix section is diag(a,b/a,a⁻¹,a/b).
The kernel is the unipotent Sylow subgroup. More generally, on every subgroup
of this Borel the character kernel is exactly the two-core, since its image
has odd order. Diagonal elements belong to the two-residual by their odd
orders, so the residual has the same torus quotient. No equality of the
Borel and its residual is needed for this calculation.

Sylow conjugacy supplies an actual multiplicative equivalence with the
normalizer of any specified Sylow two-subgroup.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954; the standard
symplectic flag and its two determinant characters.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
variable {F : Type*} [Field F]

/-- A section of the two determinant characters, in the actual diagonal matrices. -/
def torusSection : (Fˣ × Fˣ) →* borel (F := F) where
  toFun x := ⟨diagonalTorus x.1 (x.1⁻¹ * x.2), diagonalTorus_mem_borel _ _⟩
  map_one' := by
    apply Subtype.ext
    change diagonalTorus 1 (1⁻¹ * 1) = (1 : Sp F)
    simpa only [CentralRootGeometry.diagonalTorusHom_apply, Prod.fst_one,
      Prod.snd_one, inv_one, one_mul] using
      (CentralRootGeometry.diagonalTorusHom (F := F)).map_one
  map_mul' x y := by
    apply Subtype.ext
    have h := (CentralRootGeometry.diagonalTorusHom (F := F)).map_mul
      (x.1, x.1⁻¹ * x.2) (y.1, y.1⁻¹ * y.2)
    simpa [CentralRootGeometry.diagonalTorusHom_apply, mul_comm, mul_left_comm,
      mul_assoc] using h

@[simp] theorem characters_torusSection (x : Fˣ × Fˣ) :
    borelCharacters (torusSection x) = x := by
  apply Prod.ext
  · exact diagonalTorus_point_character _ _
  · change determinantCharacter (plane F)
      ⟨diagonalTorus x.1 (x.1⁻¹ * x.2), _⟩ = x.2
    rw [diagonalTorus_plane_character]
    simp

theorem characters_surjective : Function.Surjective (borelCharacters (F := F)) :=
  fun x => ⟨torusSection x, characters_torusSection x⟩

theorem characters_ker : (borelCharacters (F := F)).ker = unipotent.subgroupOf borel := by
  ext b
  exact borelCharacters_eq_one b

/-- The determinant coordinates on a subgroup of the Borel. -/
def charactersOn {V : Subgroup (Sp F)} (hV : V ≤ borel) : V →* Fˣ × Fˣ :=
  borelCharacters.comp (inclusion hV)

theorem charactersOn_ker {V : Subgroup (Sp F)} (hV : V ≤ borel) :
    (charactersOn hV).ker = unipotent.subgroupOf V := by
  ext v
  exact borelCharacters_eq_one (inclusion hV v)

variable [Finite F]

theorem torus_odd {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Nat.Coprime 2 (Nat.card (Fˣ × Fˣ)) := by
  rw [Nat.card_prod, Nat.card_units, hF]
  apply Nat.Coprime.mul_right
  all_goals
    apply Nat.coprime_two_left.mpr
    have hn : n ≠ 0 := by
      intro hn
      have : 1 < Nat.card F := Finite.one_lt_card
      simp [hF, hn] at this
    have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
    have hm : (2 : ℕ) ^ n % 2 = 0 := by simp [Nat.pow_mod, hn]
    rw [Nat.odd_iff]
    omega

/-- In every subgroup of the Borel the character kernel is exactly its two-core. -/
theorem charactersOn_ker_eq_twoCore {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {V : Subgroup (Sp F)} (hV : V ≤ borel) :
    (charactersOn hV).ker = pCore 2 V := by
  let f := charactersOn hV
  have hk : IsPGroup 2 f.ker := by
    rw [show f.ker = unipotent.subgroupOf V from charactersOn_ker hV]
    exact (isPGroup_unipotent hF).comap_subtype
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, hk⟩
  · have he : (pCore 2 V).map f = ⊥ := by
      apply card_eq_one.mp
      exact (pCore_isPGroup.map f : IsPGroup 2 ((pCore 2 V).map f)).card_eq_or_dvd.resolve_right
        (fun h => (Nat.prime_two.coprime_iff_not_dvd.mp (torus_odd hF))
          (h.trans (card_subgroup_dvd_card _)))
    intro v hv
    exact he.le ⟨v, hv, rfl⟩

theorem twoCore_eq_unipotent {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    pCore 2 (borel (F := F)) = unipotent.subgroupOf borel := by
  rw [← charactersOn_ker_eq_twoCore hF le_rfl, charactersOn_ker]

/-- The full Borel quotient is the rank-two split torus. -/
def quotientTorusEquiv {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    borel (F := F) ⧸ pCore 2 (borel (F := F)) ≃* (Fˣ × Fˣ) :=
  (QuotientGroup.quotientMulEquivOfEq
    ((twoCore_eq_unipotent hF).trans characters_ker.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ characters_surjective)

/-- The source two-residual, embedded in the actual matrix group. -/
abbrev residual : Subgroup (Sp F) := (pResidual 2 (borel (F := F))).map borel.subtype

omit [Finite F] in
theorem residual_le_borel : residual (F := F) ≤ borel := map_subtype_le _

/-- Every diagonal torus element belongs to the two-residual. -/
theorem torusSection_mem_residual {n : ℕ} (hF : Nat.card F = 2 ^ n) (x : Fˣ × Fˣ) :
    (torusSection x).val ∈ residual := by
  refine ⟨torusSection x, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
  exact (torus_odd hF).of_dvd_right
    ((orderOf_map_dvd torusSection x).trans (orderOf_dvd_natCard (x := x)))

theorem residual_characters_surjective {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Function.Surjective (charactersOn (residual_le_borel (F := F))) := by
  intro x
  exact ⟨⟨(torusSection x).val, torusSection_mem_residual hF x⟩,
    characters_torusSection x⟩

/-- The core of the residual is its exact intersection with the unipotent group. -/
theorem residual_twoCore {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    pCore 2 (residual (F := F)) = unipotent.subgroupOf residual := by
  rw [← charactersOn_ker_eq_twoCore hF residual_le_borel, charactersOn_ker]

/-- Taking the source two-residual retains the entire rank-two split torus. -/
def residualQuotientTorusEquiv {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    residual (F := F) ⧸ pCore 2 (residual (F := F)) ≃* (Fˣ × Fˣ) :=
  (QuotientGroup.quotientMulEquivOfEq
    (charactersOn_ker_eq_twoCore hF residual_le_borel).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (residual_characters_surjective hF))

theorem residual_quotient_card {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Nat.card (residual (F := F) ⧸ pCore 2 (residual (F := F))) = (2 ^ n - 1) ^ 2 := by
  rw [Nat.card_congr (residualQuotientTorusEquiv hF).toEquiv, Nat.card_prod,
    Nat.card_units, hF, pow_two]

/-- Align the Borel with any specified Sylow subgroup by actual inner conjugation. -/
theorem sylow_normalizer_conjugate {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) :
    ∃ g : Sp F,
      unipotent.map (MulAut.conj g).toMonoidHom = (S : Subgroup (Sp F)) ∧
      borel.map (MulAut.conj g).toMonoidHom = normalizer (S : Set (Sp F)) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Sp F) (unipotentSylow hF hn) S
  have he : unipotent.map (MulAut.conj g).toMonoidHom = (S : Subgroup (Sp F)) :=
    congrArg Sylow.toSubgroup hg
  refine ⟨g, he, ?_⟩
  rw [borel_eq_normalizer_unipotent, map_equiv_normalizer_eq, he]
  rfl

def sylowNormalizerEquiv {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) : normalizer (S : Set (Sp F)) ≃* borel (F := F) := by
  classical
  let g := Classical.choose (sylow_normalizer_conjugate hF hn S)
  have hg := (Classical.choose_spec (sylow_normalizer_conjugate hF hn S)).2
  exact ((MulAut.conj g).subgroupMap borel |>.trans (MulEquiv.subgroupCongr hg)).symm

end Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
