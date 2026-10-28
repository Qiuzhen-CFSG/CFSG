module

public import Theory.SpecificGroups.Tits.Presentation
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

/-!
# Normalizing central lifts of Parrott's generators

Ten explicit products of the 37 defining relators have exponent sums equal to
the ten basis vectors of the free abelian group on the generators. Their
commutative evaluations are checked below by integer group algebra. For a tuple
whose relator values are central, multiply each generator by the inverse value
of the corresponding product. The resulting tuple has the same projection,
all ten correction words evaluate to one, and it is independent of central
changes to the starting tuple. All its elements lie in the derived subgroup.

This constructs normalized lifts, not lifts satisfying all the original
relations. Vanishing of the remaining central relator values is a separate
obligation. The same exponent-sum identities prove perfectness of Parrott's
presentation directly, without its finite-model certification.

Source: Parrott, “A Characterization of the Tits' Simple Group” (1972), §5,
p.683, transcribed in `refs/original/n-group-global/parrott-tits-presentation.md`.
All words retain the source convention `a⁻¹ * b⁻¹ * a * b`.
-/

public section

open Tits
open scoped IsMulCommutative
namespace Tits.CentralCoverLifting.CompatibleGenerators

/-- Products of source relators with the exponent sum of the named generator. -/
@[expose] def correctionWord : ParrottGenerator → FreeGroup ParrottGenerator
  | .r1 => (parrottRelator .i_r1) ^ (-2 : ℤ) *
      (parrottRelator .i_r8)⁻¹ *
      parrottRelator .iii_s1_s8 *
      (parrottRelator .v_s5_s4)⁻¹ *
      parrottRelator .vi_s1_r1 *
      (parrottRelator .vii_s5) ^ (2 : ℤ) *
      parrottRelator .viii_s7
  | .r8 => (parrottRelator .i_r1) ^ (-3 : ℤ) *
      (parrottRelator .iii_s1_s7) ^ (3 : ℤ) *
      (parrottRelator .v_s7_s4) ^ (-3 : ℤ) *
      parrottRelator .vi_r8_s8 *
      (parrottRelator .vii_s2) ^ (3 : ℤ) *
      (parrottRelator .viii_s4)⁻¹
  | .s1 => (parrottRelator .iii_s1_s8)⁻¹ *
      parrottRelator .v_s5_s4 *
      parrottRelator .viii_s4 *
      (parrottRelator .viii_s7)⁻¹
  | .s2 => (parrottRelator .iii_s1_s7)⁻¹ *
      parrottRelator .v_s7_s4
  | .s3 => (parrottRelator .i_s1)⁻¹ *
      parrottRelator .v_s5_s4 *
      (parrottRelator .vii_s3)⁻¹ *
      (parrottRelator .viii_s4)⁻¹ *
      parrottRelator .viii_s3
  | .s4 => (parrottRelator .iv_s7_s2)⁻¹ *
      parrottRelator .v_s7_s4 *
      (parrottRelator .v_s5_s4)⁻¹
  | .s5 => parrottRelator .iii_s1_s8 *
      (parrottRelator .v_s5_s4)⁻¹ *
      (parrottRelator .vii_s5) ^ (-2 : ℤ) *
      parrottRelator .vii_s3 *
      (parrottRelator .viii_s4) ^ (2 : ℤ) *
      (parrottRelator .viii_s1)⁻¹ *
      (parrottRelator .viii_s3)⁻¹
  | .s6 => (parrottRelator .iv_s2_s8)⁻¹ *
      parrottRelator .iv_s7_s2 *
      (parrottRelator .v_s7_s4)⁻¹ *
      parrottRelator .v_s5_s4
  | .s7 => (parrottRelator .i_r1) ^ (2 : ℤ) *
      (parrottRelator .vii_r3) ^ (-2 : ℤ) *
      parrottRelator .viii_s1 *
      (parrottRelator .viii_s7)⁻¹ *
      (parrottRelator .viii_s3)⁻¹ *
      parrottRelator .viii_r3
  | .s8 => parrottRelator .i_r1 *
      (parrottRelator .iii_s1_s7)⁻¹ *
      parrottRelator .v_s7_s4 *
      (parrottRelator .vii_s2)⁻¹

/-- The explicit integer identities hold in every commutative group. -/
theorem correctionWord_commutative {A : Type*} [CommGroup A]
    (a : ParrottGenerator → A) (i : ParrottGenerator) :
    FreeGroup.lift a (correctionWord i) = a i := by
  cases i <;>
    simp only [correctionWord, parrottRelator, parrottR3, parrottR5, parrottR7,
      parrottCommutator, map_mul, map_inv, map_pow, map_zpow, FreeGroup.lift_apply_of] <;>
    apply Additive.ofMul.injective <;>
    simp only [ofMul_mul, ofMul_inv, ofMul_pow,
      ofMul_zpow] <;> abel

/-- Correction values belong to any subgroup containing the relator values. -/
theorem correctionWord_mem {E : Type*} [Group E]
    (g : ParrottGenerator → E) (H : Subgroup E)
    (h : ∀ j, FreeGroup.lift g (parrottRelator j) ∈ H) (i : ParrottGenerator) :
    FreeGroup.lift g (correctionWord i) ∈ H := by
  cases i <;> simp only [correctionWord, map_mul, map_inv, map_zpow]
  all_goals repeat first | exact h _ | apply H.mul_mem | apply H.inv_mem | apply H.zpow_mem

/-- A word in lifts projects to the same word in the original generators. -/
theorem lift_projection {E : Type*} [Group E] (π : E →* ParrottGroup)
    (g : ParrottGenerator → E) (hg : ∀ i, π (g i) = parrottGenerator i)
    (w : FreeGroup ParrottGenerator) :
    π (FreeGroup.lift g w) = FreeGroup.lift parrottGenerator w := by
  have hh : π.comp (FreeGroup.lift g) = FreeGroup.lift parrottGenerator := by
    ext i
    simpa using hg i
  exact DFunLike.congr_fun hh w

/-- Each source relator evaluated on arbitrary lifts lies in the kernel. -/
theorem relators_mem_ker {E : Type*} [Group E] (π : E →* ParrottGroup)
    (g : ParrottGenerator → E) (hg : ∀ i, π (g i) = parrottGenerator i)
    (j : ParrottRelatorIndex) : FreeGroup.lift g (parrottRelator j) ∈ π.ker := by
  rw [MonoidHom.mem_ker, lift_projection π g hg]
  exact parrott_generators_satisfy_relations j

/-- Evaluation separates a central change of the generators from the original word. -/
theorem lift_central_mul {E : Type*} [Group E] (g : ParrottGenerator → E)
    (c : ParrottGenerator → Subgroup.center E) (w : FreeGroup ParrottGenerator) :
    FreeGroup.lift (fun i => (c i : E) * g i) w =
      (FreeGroup.lift c w : E) * FreeGroup.lift g w := by
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of i => simp
  | inv_of i hi =>
    simp only [map_inv, FreeGroup.lift_apply_of, mul_inv_rev, Subgroup.coe_inv]
    exact ((c i).property.comm (g i)).inv_inv.eq.symm
  | mul x y hx hy =>
    simp only [map_mul, hx, hy, Subgroup.coe_mul]
    have hc := (Subgroup.mem_center_iff.mp (FreeGroup.lift c y).property (FreeGroup.lift g x))
    calc
      _ = (FreeGroup.lift c x : E) *
          (FreeGroup.lift g x * (FreeGroup.lift c y : E)) * FreeGroup.lift g y := by group
      _ = _ := by rw [hc]; group

/-- Correct each generator by the inverse of its specified relator product. -/
@[expose] def normalize {E : Type*} [Group E] (g : ParrottGenerator → E)
    (i : ParrottGenerator) : E := (FreeGroup.lift g (correctionWord i))⁻¹ * g i

/-- Normalization does not depend on central changes to the starting tuple. -/
theorem normalize_central_mul {E : Type*} [Group E] (g : ParrottGenerator → E)
    (c : ParrottGenerator → Subgroup.center E) :
    normalize (fun i => (c i : E) * g i) = normalize g := by
  funext i
  simp only [normalize, lift_central_mul, correctionWord_commutative]
  group

/-- The correction preserves the literal projection of each named generator. -/
theorem normalize_projection {E : Type*} [Group E] (π : E →* ParrottGroup)
    (g : ParrottGenerator → E) (hg : ∀ i, π (g i) = parrottGenerator i)
    (i : ParrottGenerator) : π (normalize g i) = parrottGenerator i := by
  have hc : FreeGroup.lift g (correctionWord i) ∈ π.ker :=
    correctionWord_mem g π.ker (relators_mem_ker π g hg) i
  simp only [normalize, map_mul, map_inv, MonoidHom.mem_ker.mp hc, inv_one, one_mul, hg]

/-- All ten normalization equations hold when the source relator values are central. -/
theorem normalize_correctionWord {E : Type*} [Group E] (g : ParrottGenerator → E)
    (hc : ∀ j, FreeGroup.lift g (parrottRelator j) ∈ Subgroup.center E)
    (i : ParrottGenerator) : FreeGroup.lift (normalize g) (correctionWord i) = 1 := by
  let c : ParrottGenerator → Subgroup.center E := fun k =>
    ⟨(FreeGroup.lift g (correctionWord k))⁻¹,
      (Subgroup.center E).inv_mem (correctionWord_mem g (Subgroup.center E) hc k)⟩
  change FreeGroup.lift (fun k => (c k : E) * g k) (correctionWord i) = 1
  rw [lift_central_mul, correctionWord_commutative]
  exact inv_mul_cancel _

/-- Normalization preserves centrality of the source relator values. -/
theorem normalize_relators_central {E : Type*} [Group E] (g : ParrottGenerator → E)
    (hc : ∀ j, FreeGroup.lift g (parrottRelator j) ∈ Subgroup.center E)
    (j : ParrottRelatorIndex) :
    FreeGroup.lift (normalize g) (parrottRelator j) ∈ Subgroup.center E := by
  let c : ParrottGenerator → Subgroup.center E := fun k =>
    ⟨(FreeGroup.lift g (correctionWord k))⁻¹,
      (Subgroup.center E).inv_mem (correctionWord_mem g (Subgroup.center E) hc k)⟩
  change FreeGroup.lift (fun k => (c k : E) * g k) (parrottRelator j) ∈ Subgroup.center E
  rw [lift_central_mul]
  exact (Subgroup.center E).mul_mem (FreeGroup.lift c (parrottRelator j)).property (hc j)

/-- Two choices of lifts in the same central extension give the same normalized tuple. -/
theorem normalize_eq_of_projection_eq {E : Type*} [Group E] (π : E →* ParrottGroup)
    (hc : π.ker ≤ Subgroup.center E) (g h : ParrottGenerator → E)
    (hgh : ∀ i, π (g i) = π (h i)) : normalize g = normalize h := by
  let c : ParrottGenerator → Subgroup.center E := fun i =>
    ⟨g i * (h i)⁻¹, hc (by simp [MonoidHom.mem_ker, hgh])⟩
  have he : g = fun i => (c i : E) * h i := by
    funext i
    dsimp [c]
    group
  calc
    normalize g = normalize (fun i => (c i : E) * h i) := congrArg normalize he
    _ = normalize h := normalize_central_mul h c



/-- Every normalized element lies in the derived subgroup, even before centrality is used. -/
theorem normalize_mem_commutator {E : Type*} [Group E]
    (g : ParrottGenerator → E) (i : ParrottGenerator) : normalize g i ∈ commutator E := by
  rw [← Abelianization.ker_of E, MonoidHom.mem_ker]
  have hh : (Abelianization.of : E →* Abelianization E).comp (FreeGroup.lift g) =
      FreeGroup.lift (fun i => Abelianization.of (g i)) := by
    ext i
    simp
  have hi := DFunLike.congr_fun hh (correctionWord i)
  change Abelianization.of (FreeGroup.lift g (correctionWord i)) =
    FreeGroup.lift (fun i => Abelianization.of (g i)) (correctionWord i) at hi
  rw [correctionWord_commutative] at hi
  simp only [normalize, map_mul, map_inv, hi, inv_mul_cancel]

/-- A tuple already satisfying all source relations is fixed by normalization. -/
theorem normalize_of_relations {E : Type*} [Group E]
    (g : ParrottGenerator → E) (hrel : SatisfiesParrottRelations g) : normalize g = g := by
  funext i
  have hc := correctionWord_mem g ⊥ (fun j => hrel j) i
  have he : FreeGroup.lift g (correctionWord i) = 1 := hc
  simp [normalize, he]

/-- Perfectness follows directly from the literal presentation and the integer identities. -/
theorem parrott_perfect_from_relators : Group.IsPerfect ParrottGroup := by
  constructor
  apply top_unique
  have hgen : Subgroup.closure (Set.range parrottGenerator) = ⊤ :=
    PresentedGroup.closure_range_of parrottRelatorSet
  rw [← hgen]
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  have h := normalize_mem_commutator parrottGenerator i
  rw [normalize_of_relations parrottGenerator parrott_generators_satisfy_relations] at h
  exact h

end Tits.CentralCoverLifting.CompatibleGenerators
