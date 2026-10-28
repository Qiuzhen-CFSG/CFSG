module

public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Odd subgroups of symplectic Sylow normalizers

The two determinant characters on the actual flag Borel have common kernel
its unipotent Sylow subgroup. An odd subgroup therefore embeds in the product
of two copies of the multiplicative field group. Sylow conjugacy gives the
same embedding for any Sylow normalizer, proving abelianness and the split
Cartan prime restriction without assuming a torus conjugacy theorem.

Source: Aschbacher--Smith, `refs/quasithin.pdf`, A.3.15(5), printed pp.50--51,
and the symplectic case of Proposition 1.3.4, printed p.511.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative Pointwise
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F]
noncomputable def borelCharacters : borel (F := F) →* Fˣ × Fˣ :=
  ((determinantCharacter (point F)).comp (inclusion inf_le_left)).prod
    ((determinantCharacter (plane F)).comp (inclusion inf_le_right))

theorem borelCharacters_eq_one (b : borel (F := F)) :
    borelCharacters b = 1 ↔ (b : Sp F) ∈ unipotent := by
  rw [Prod.ext_iff]
  change (_ = 1 ∧ _ = 1) ↔ (b.val ∈ pointLocal ∧ b.val ∈ planeLocal)
  rw [pointLocal, planeLocal, mem_determinantKernel_iff, mem_determinantKernel_iff]
  exact ⟨fun h => ⟨⟨b.property.1, h.1⟩, ⟨b.property.2, h.2⟩⟩,
    fun h => ⟨h.1.choose_spec, h.2.choose_spec⟩⟩

noncomputable def oddBorelCharacters {B : Subgroup (Sp F)} (hB : B ≤ borel) :
    B →* Fˣ × Fˣ := borelCharacters.comp (inclusion hB)

variable [Finite F]

theorem oddBorelCharacters_injective {n p : ℕ} (hF : Nat.card F = 2^n)
    {B : Subgroup (Sp F)} (hB : B ≤ borel) (hp : Odd p) (hP : IsPGroup p B) :
    Function.Injective (oddBorelCharacters hB) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro b hb
  have hu : (b : Sp F) ∈ unipotent := (borelCharacters_eq_one (inclusion hB b)).mp hb
  exact Subtype.ext (((isPGroup_unipotent hF).disjoint_of_coprime hP
    (Nat.coprime_two_left.mpr hp)).le_bot ⟨hu, b.property⟩)

theorem odd_borel_abelian {n p : ℕ} (hF : Nat.card F = 2^n)
    {B : Subgroup (Sp F)} (hB : B ≤ borel) (hp : Odd p) (hP : IsPGroup p B) :
    IsMulCommutative B := by
  apply IsMulCommutative.of_comm
  intro a b
  apply oddBorelCharacters_injective hF hB hp hP
  simp only [map_mul, mul_comm]

theorem odd_borel_card_dvd {n p : ℕ} (hF : Nat.card F = 2^n)
    {B : Subgroup (Sp F)} (hB : B ≤ borel) (hp : Odd p) (hP : IsPGroup p B) :
    Nat.card B ∣ (2^n - 1)^2 := by
  have hd := card_dvd_of_injective _ (oddBorelCharacters_injective hF hB hp hP)
  simpa only [Nat.card_prod, Nat.card_units, hF, pow_two] using hd

theorem odd_borel_congruence {n p : ℕ} [Fact p.Prime] (hF : Nat.card F = 2^n)
    {B : Subgroup (Sp F)} (hB : B ≤ borel) (hp : Odd p) (hP : IsPGroup p B)
    (hne : B ≠ ⊥) : 2^n ≡ 1 [MOD p] := by
  have hd : p ∣ Nat.card B := hP.card_eq_or_dvd.resolve_left
    (fun h => hne (Subgroup.card_eq_one.mp h))
  have hpq : p ∣ 2^n - 1 := (Fact.out : p.Prime).dvd_of_dvd_pow
    (hd.trans (odd_borel_card_dvd hF hB hp hP))
  exact ((Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mpr hpq).symm

theorem odd_sylow_normalizer_embedding {n p : ℕ} (hF : Nat.card F = 2^n) (hn : 1 ≤ n)
    (U : Sylow 2 (Sp F)) {B : Subgroup (Sp F)} (hB : B ≤ normalizer (U : Set (Sp F)))
    (hp : Odd p) (hP : IsPGroup p B) :
    ∃ f : B →* Fˣ × Fˣ, Function.Injective f := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Sp F) U (unipotentSylow hF hn)
  let a := MulAut.conj g
  have hU : (U : Subgroup (Sp F)).map a.toMonoidHom = unipotent := by
    exact congrArg (fun V : Sylow 2 (Sp F) => (V : Subgroup (Sp F))) hg
  have hBa : B.map a.toMonoidHom ≤ borel := by
    rw [borel_eq_normalizer_unipotent, ← hU]
    exact (map_mono hB).trans (fun _ hx => (U : Subgroup (Sp F)).le_normalizer_map a.toMonoidHom hx)
  let f := (oddBorelCharacters hBa).comp (a.subgroupMap B).toMonoidHom
  exact ⟨f, (oddBorelCharacters_injective hF hBa hp (hP.map a.toMonoidHom)).comp
    (a.subgroupMap B).injective⟩

theorem odd_sylow_normalizer_abelian_card {n p : ℕ} (hF : Nat.card F = 2^n) (hn : 1 ≤ n)
    (U : Sylow 2 (Sp F)) {B : Subgroup (Sp F)} (hB : B ≤ normalizer (U : Set (Sp F)))
    (hp : Odd p) (hP : IsPGroup p B) :
    IsMulCommutative B ∧ Nat.card B ∣ (2^n - 1)^2 := by
  obtain ⟨f, hf⟩ := odd_sylow_normalizer_embedding hF hn U hB hp hP
  refine ⟨IsMulCommutative.of_comm (fun a b => hf (by simp only [map_mul, mul_comm])), ?_⟩
  simpa only [Nat.card_prod, Nat.card_units, hF, pow_two] using card_dvd_of_injective f hf

theorem odd_sylow_normalizer_congruence {n p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = 2^n) (hn : 1 ≤ n)
    (U : Sylow 2 (Sp F)) {B : Subgroup (Sp F)} (hB : B ≤ normalizer (U : Set (Sp F)))
    (hp : Odd p) (hP : IsPGroup p B) (hne : B ≠ ⊥) : 2^n ≡ 1 [MOD p] := by
  have hd : p ∣ Nat.card B := hP.card_eq_or_dvd.resolve_left
    (fun h => hne (Subgroup.card_eq_one.mp h))
  have hpq : p ∣ 2^n - 1 := (Fact.out : p.Prime).dvd_of_dvd_pow
    (hd.trans (odd_sylow_normalizer_abelian_card hF hn U hB hp hP).2)
  exact ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr hpq).symm
end Theory.SpecificGroups.SymplecticFour
