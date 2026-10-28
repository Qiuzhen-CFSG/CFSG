module

public import Theory.Representation.SL3.BinaryDefiningFactors.Classification
public import Theory.Representation.SL3.BinaryDefiningFactors.FrobeniusPeriod
public import Theory.Representation.SL3.BinaryDefiningFactors.SmallPatterns
public import Theory.Representation.EndFieldFrobenius
public import Mathlib.Tactic.Linarith
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Theory.Representation.Quotient
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic

/-!
# Small binary simple degrees for PSL(3,4)

Inflate a simple binary representation along the actual central quotient
SL(3,4) → PSL(3,4). Extend its commuting endomorphism field to an algebraic
closure and apply the proved SL₃ tensor-word classification. The exact
Frobenius period and the dimension tower leave degree six, degree nine,
or degree at least sixteen for a nontrivial action.

In the degree-six case the absolute representation is a natural module or
its dual, with its actual coefficient embedding. A nonidentity scalar of
order three acts nontrivially on either module, whereas inflation from the
projective quotient kills that scalar. Scalar extension preserves the latter
identity, giving a contradiction. A trivial simple action has dimension one.

Source: GLS III §§2.8.6, 2.8.8 and 2.8.10(c). The word-period and numerical
assembly adapts the proof in the G.9 `LinearThreeRecognition.AbsoluteExhaustion`
and `OrbitDegrees` modules, with only downward Theory/Mathlib imports.
This supplies the simple-degree input to the point-stabilizer route for
Aschbacher--Smith G.7.3(2), printed p.348; no character table is assumed.
-/

public section

set_option backward.isDefEq.respectTransparency false
open Representation
open scoped MatrixGroups TensorProduct MonoidAlgebra
namespace Representation.MathieuSmall.M22Recognition.PointRestriction.SimpleDegrees
noncomputable section
open Representation.SL3.BinaryDefiningFactors

private theorem eight_mul_le_pow {c t : ℕ} (hc : 8 ≤ c) (ht : 0 < t) :
    8 * t ≤ c ^ t := by
  induction t, ht using Nat.le_induction with
  | base => simpa using hc
  | succ t ht ih =>
    rw [pow_succ]
    nlinarith

private theorem eight_mul_le_three_pow {t : ℕ} (ht : 3 ≤ t) : 8 * t ≤ 3 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; nlinarith

private theorem orbit_degree_gap {s t a b : ℕ} (ht : 0 < t) (hab : 0 < a + b) :
    (a = 1 ∧ b = 0 ∧ t = 1) ∨ (a = 1 ∧ b = 0 ∧ t = 2) ∨
      8 * (s * t) ≤ s * (3 ^ a * 8 ^ b) ^ t := by
  by_cases hb : b = 0
  · subst b
    by_cases ha : a = 1
    · subst a
      rcases (by omega : t = 1 ∨ t = 2 ∨ 3 ≤ t) with ht1 | ht2 | ht3
      · exact Or.inl ⟨rfl, rfl, ht1⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl, ht2⟩)
      · right; right
        simpa [Nat.mul_left_comm] using Nat.mul_le_mul_left s (eight_mul_le_three_pow ht3)
    · have ha2 : 2 ≤ a := by omega
      have hp : 9 ≤ 3 ^ a := by
        simpa using Nat.pow_le_pow_right (by decide : 0 < 3) ha2
      right; right
      simpa [Nat.mul_left_comm] using Nat.mul_le_mul_left s (eight_mul_le_pow (by omega : 8 ≤ 3 ^ a) ht)
  · have hb1 : 1 ≤ b := by omega
    have hp : 8 ≤ 8 ^ b := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 8) hb1
    have hapos : 1 ≤ 3 ^ a := Nat.one_le_pow a 3 (by decide)
    have hc : 8 ≤ 3 ^ a * 8 ^ b := by nlinarith
    right; right
    simpa [Nat.mul_left_comm] using Nat.mul_le_mul_left s (eight_mul_le_pow hc ht)


variable {F V : Type*} [Field F] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(3,F) V) [IsIrreducible ρ]

private abbrev SchurField := Module.End (ZMod 2)[SL(3,F)] ρ.asModule
private abbrev SplittingField := AlgebraicClosure (SchurField ρ)
private abbrev schurDegree := Representation.schurDegree 2 ρ

/-- The actual commuting endomorphism field has characteristic two. -/
private instance schurField_charTwo : CharP (SchurField ρ) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField ρ)).injective 2

/-- An actual word equivalence determines the binary dimension. -/
private theorem finrank_of_word_model (ι : F →+* SplittingField ρ) (w : List Factor)
    (hmodel : Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv
      (wordRep ι w))) :
    Module.finrank (ZMod 2) V = schurDegree ρ * wordDegree w := by
  obtain ⟨φ⟩ := hmodel
  calc
    Module.finrank (ZMod 2) V = schurDegree ρ *
        Module.finrank (SplittingField ρ)
          (SplittingField ρ ⊗[SchurField ρ] ρ.asModule) :=
      Representation.finrank_eq_schurDegree_mul 2 ρ (SplittingField ρ)
    _ = schurDegree ρ * wordDegree w := by
      rw [φ.toLinearEquiv.finrank_eq, finrank_wordSpace]

private theorem eq_one_of_equiv {K G M N : Type*} [Field K] [Monoid G]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    {σ : Representation K G M} {τ : Representation K G N} (φ : σ.Equiv τ)
    (g : G) (h : τ g = 1) : σ g = 1 := by
  ext v
  apply φ.toLinearEquiv.injective
  change φ (σ g v) = φ v
  have hc := Representation.IntertwiningMap.isIntertwining σ τ φ.toIntertwiningMap g v
  rw [h] at hc
  exact hc

private theorem eq_one_of_schur_scalar_extension (g : SL(3,F))
    (h : extendScalars (SplittingField ρ) ρ.endFieldRep g = 1) : ρ g = 1 := by
  have he : ρ.endFieldRep g = 1 := by
    ext v
    apply (Module.FaithfullyFlat.tensorProduct_mk_injective
      (A := SchurField ρ) (B := SplittingField ρ) ρ.asModule)
    exact congrArg (fun f : Module.End (SplittingField ρ)
      (SplittingField ρ ⊗[SchurField ρ] ρ.asModule) => f (1 ⊗ₜ[SchurField ρ] v)) h
  ext v
  have hh := congrArg (fun f : Module.End (SchurField ρ) ρ.asModule =>
    ρ.asModuleEquiv (f (ρ.asModuleEquiv.symm v))) he
  simpa only [endFieldRep_apply, LinearEquiv.apply_symm_apply, Module.End.one_apply] using hh

/-- A nontrivial binary action has a nontrivial tensor factor. -/
private theorem counts_pos_of_word_model (hact : ∃ g, ρ g ≠ 1)
    (ι : F →+* SplittingField ρ) (w : List Factor)
    (hmodel : Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv
      (wordRep ι w))) :
    0 < naturalCount w + adjointCount w := by
  obtain ⟨φ⟩ := hmodel
  obtain ⟨g, hg⟩ := hact
  by_contra h
  have ha : naturalCount w = 0 := by omega
  have hb : adjointCount w = 0 := by omega
  exact hg (eq_one_of_schur_scalar_extension ρ g
    (eq_one_of_equiv φ g (wordRep_eq_one_of_counts_zero ι w ha hb g)))

/-- The binary dimension formula for an actual repeated-block model. -/
private theorem finrank_of_repeated_word_model (ι : F →+* SplittingField ρ)
    (w : List Factor) (t : ℕ)
    (hmodel : Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv
      (wordRep ι (List.replicate t w).flatten))) :
    Module.finrank (ZMod 2) V =
      schurDegree ρ * (3 ^ naturalCount w * 8 ^ adjointCount w) ^ t := by
  rw [finrank_of_word_model ρ ι _ hmodel, wordDegree_repeat]

/-- A block underlying a nontrivial binary action has a nontrivial factor. -/
private theorem counts_pos_of_repeated_word_model (hact : ∃ g, ρ g ≠ 1)
    (ι : F →+* SplittingField ρ) (w : List Factor) (t : ℕ)
    (hmodel : Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv
      (wordRep ι (List.replicate t w).flatten))) :
    0 < naturalCount w + adjointCount w := by
  have h := counts_pos_of_word_model ρ hact ι _ hmodel
  rw [naturalCount_repeat, adjointCount_repeat] at h
  by_contra hc
  have ha : naturalCount w = 0 := by omega
  have hb : adjointCount w = 0 := by omega
  simp [ha, hb] at h

/-- Numerical reduction retaining the exceptional word patterns. This does not
assert their equivalence to the published absolute natural or tensor models. -/
private theorem degree_alternatives_of_repeated_word_model (hact : ∃ g, ρ g ≠ 1)
    (ι : F →+* SplittingField ρ) (w : List Factor) (n t : ℕ)
    (ht : 0 < t)
    (hn : n = schurDegree ρ * t)
    (hmodel : Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv
      (wordRep ι (List.replicate t w).flatten))) :
    (naturalCount w = 1 ∧ adjointCount w = 0 ∧ t = 1 ∧
      schurDegree ρ = n ∧ Module.finrank (ZMod 2) V = 3 * n) ∨
    (naturalCount w = 1 ∧ adjointCount w = 0 ∧ t = 2 ∧
      n = 2 * schurDegree ρ ∧ Module.finrank (ZMod 2) V = 9 * schurDegree ρ) ∨
    8 * n ≤ Module.finrank (ZMod 2) V := by
  have hd := finrank_of_repeated_word_model ρ ι w t hmodel
  have hab := counts_pos_of_repeated_word_model ρ hact ι w t hmodel
  rcases orbit_degree_gap (s := schurDegree ρ) ht hab with
    ⟨ha, hb, ht1⟩ | ⟨ha, hb, ht2⟩ | hgap
  · left
    refine ⟨ha, hb, ht1, ?_, ?_⟩
    · simpa [ht1] using hn.symm
    · simpa [ha, hb, ht1, hn, Nat.mul_comm] using hd
  · right; left
    refine ⟨ha, hb, ht2, ?_, ?_⟩
    · simpa [ht2, Nat.mul_comm] using hn
    · simpa [ha, hb, ht2, Nat.mul_comm] using hd
  · right; right
    simpa [← hn, ← hd] using hgap

variable [Finite F] [CharP F 2]

/-- Every binary irreducible has an actual tensor-word model consisting of
positive copies of a block whose length is its Schur degree. The word
classification and exact Frobenius period are proved, not assumed. -/
private theorem exists_repeated_word_model (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = 2 ^ n) :
    ∃ (ι : F →+* SplittingField ρ) (t : ℕ) (b : List Factor),
      0 < t ∧ b.length = schurDegree ρ ∧ n = schurDegree ρ * t ∧
      Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv
        (wordRep ι (List.replicate t b).flatten)) := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Algebra (ZMod 2) (SplittingField ρ) := ZMod.algebra (SplittingField ρ) 2
  let : IsAbsolutelyIrreducible ρ.endFieldRep := endFieldRep_isAbsolutelyIrreducible ρ
  let : IsIrreducible (extendScalars (SplittingField ρ) ρ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension ρ.endFieldRep (SplittingField ρ)
  let ι : F →+* SplittingField ρ :=
    (IsAlgClosed.lift (R := ZMod 2) (S := F) (M := SplittingField ρ)).toRingHom
  obtain ⟨w, hw, he⟩ := exists_word_equiv ι n hcard
    (extendScalars (SplittingField ρ) ρ.endFieldRep)
  obtain ⟨t, b, ht, hb, hn, hrep⟩ :=
    exists_repeated_block_of_word_model ρ ι w n hn hw hcard
      (wordRep_isIrreducible ι n hcard)
      (fun u v hu hv h => (wordRep_equiv_iff ι n hcard u v hu hv).mp h) he
  exact ⟨ι, t, b, ht, hb, hn, hrep ▸ he⟩


private theorem dual_eq_one_imp_eq_one
    {K G W : Type*} [Field K] [Group G] [AddCommGroup W] [Module K W]
    (σ : Representation K G W) (g : G) (h : σ.dual g = 1) : σ g = 1 := by
  ext w
  apply Module.eval_apply_injective K
  ext f
  change f (σ g w) = f w
  have he := congrArg (fun t : Module.End K (Module.Dual K W) => t f (σ g w)) h
  change f (σ g⁻¹ (σ g w)) = f (σ g w) at he
  simpa only [σ.inv_self_apply] using he.symm

omit [Finite F] [CharP F 2] in
private theorem scalar_extension_eq_one (g : SL(3,F)) (h : ρ g = 1) :
    extendScalars (SplittingField ρ) ρ.endFieldRep g = 1 := by
  have he : ρ.endFieldRep g = 1 := by
    ext v
    apply ρ.asModuleEquiv.injective
    change ρ.asModuleEquiv (ρ.endFieldRep g v) = ρ.asModuleEquiv v
    simp only [endFieldRep_apply, LinearEquiv.apply_symm_apply, h, Module.End.one_apply]
  rw [extendScalars_apply, he, LinearMap.baseChange_one]

private theorem exists_central_scalar : ∃ c : Matrix.PSL3Four.F,
    c ≠ 1 ∧ c ^ 3 = 1 := by
  obtain ⟨c, hc⟩ := Matrix.PSL3Four.exists_fieldFrobenius_ne
  have hc0 : c ≠ 0 := by intro h; apply hc; simp [h]
  have hc1 : c ≠ 1 := by intro h; apply hc; simp [h]
  refine ⟨c, hc1, ?_⟩
  apply mul_right_cancel₀ hc0
  simpa only [← pow_succ, one_mul] using Matrix.PSL3Four.pow_four c

private def scalarElement (c : Matrix.PSL3Four.F) (hc : c ^ 3 = 1) :
    Matrix.PSL3Four.SL :=
  ⟨c • 1, by simp [hc]⟩

private theorem scalarElement_central (c : Matrix.PSL3Four.F) (hc : c ^ 3 = 1) :
    scalarElement c hc ∈ Subgroup.center Matrix.PSL3Four.SL := by
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨c, by simpa using hc, ?_⟩
  ext i j
  simp [scalarElement, Matrix.scalar_apply, Matrix.diagonal, Matrix.one_apply]

private theorem natural_scalar (c : Matrix.PSL3Four.F) (hc : c ^ 3 = 1)
    {K : Type*} [Field K] (ι : Matrix.PSL3Four.F →+* K) (v : Fin 3 → K) :
    natural ι (scalarElement c hc) v = ι c • v := by
  change Matrix.mulVec ((c • (1 : Matrix (Fin 3) (Fin 3) Matrix.PSL3Four.F)).map ι) v = _
  have hm : ((c • (1 : Matrix (Fin 3) (Fin 3) Matrix.PSL3Four.F)).map ι) =
      ι c • (1 : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    simp [Matrix.one_apply, apply_ite ι]
  rw [hm, Matrix.smul_mulVec, Matrix.one_mulVec]

private theorem natural_scalar_ne_one (c : Matrix.PSL3Four.F) (hc : c ^ 3 = 1)
    (hc1 : c ≠ 1) {K : Type*} [Field K] (ι : Matrix.PSL3Four.F →+* K) :
    natural ι (scalarElement c hc) ≠ 1 := by
  intro h
  have he := congrArg (fun t : Module.End K (Fin 3 → K) => t (fun _ => 1) 0) h
  rw [natural_scalar] at he
  have he' : ι c = ι 1 := by simpa using he
  exact hc1 (ι.injective he')

private theorem finrank_one_of_trivial
    {K G W : Type*} [Field K] [Group G] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (σ : Representation K G W) [σ.IsIrreducible]
    (h : ∀ g, σ g = 1) : Module.finrank K W = 1 := by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  let S : Subrepresentation σ :=
    ⟨Submodule.span K {w}, fun g v hv => by simpa only [h, Module.End.one_apply] using hv⟩
  have hS : S ≠ ⊥ := by
    intro hz
    have hwS : w ∈ S := Submodule.subset_span (Set.mem_singleton w)
    rw [hz] at hwS
    exact hw hwS
  have ht : S = ⊤ := (eq_bot_or_eq_top S).resolve_left hS
  have ht' : Submodule.span K {w} = ⊤ := congrArg Subrepresentation.toSubmodule ht
  have hd := finrank_span_singleton (K := K) hw
  rw [ht', finrank_top] at hd
  exact hd

/-- Every binary simple module of dimension at most twelve for the literal
projective group has degree one or nine. -/
theorem simple_degree {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (τ : Representation (ZMod 2) Matrix.PSL3Four.PSL W)
    [τ.IsIrreducible] (hhi : Module.finrank (ZMod 2) W ≤ 12) :
    Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 9 := by
  let π := QuotientGroup.mk' (Subgroup.center Matrix.PSL3Four.SL)
  let σ : Representation (ZMod 2) Matrix.PSL3Four.SL W := τ.comp π
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff π (QuotientGroup.mk'_surjective _) τ).mpr inferInstance
  by_cases hact : ∃ g, σ g ≠ 1
  swap
  · exact Or.inl (finrank_one_of_trivial σ (by simpa using hact))
  obtain ⟨ι, t, b, ht, hb, hnt, he⟩ := exists_repeated_word_model σ 2 (by decide)
    (by simpa using Matrix.PSL3Four.card_F)
  rcases degree_alternatives_of_repeated_word_model σ hact ι b 2 t ht hnt he with
    ⟨ha, hadj, ht1, hs, hd⟩ | ⟨ha, hadj, ht2, hs, hd⟩ | hgap
  · subst t
    rw [show (List.replicate 1 b).flatten = b by simp] at he
    obtain ⟨e⟩ := he
    obtain ⟨ι', hn | hd⟩ := wordRep_single_factor ι b ha hadj
    all_goals
      obtain ⟨c, hc1, hc⟩ := exists_central_scalar
      let z := scalarElement c hc
      have hz : σ z = 1 := by
        change τ (π z) = 1
        rw [show π z = 1 from (QuotientGroup.eq_one_iff z).mpr (scalarElement_central c hc)]
        exact τ.map_one
      have hez := scalar_extension_eq_one σ z hz
    · obtain ⟨f⟩ := hn
      exact False.elim (natural_scalar_ne_one c hc hc1 ι'
        (eq_one_of_equiv (e.trans f).symm z hez))
    · obtain ⟨f⟩ := hd
      exact False.elim (natural_scalar_ne_one c hc hc1 ι'
        (dual_eq_one_imp_eq_one _ z (eq_one_of_equiv (e.trans f).symm z hez)))
  · right
    omega
  · omega

end
end Representation.MathieuSmall.M22Recognition.PointRestriction.SimpleDegrees
