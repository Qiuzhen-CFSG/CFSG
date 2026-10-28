module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearTwo
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.SymplecticFour
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.G2

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import Theory.GroupAction.ModelConjugation.InnerImage
public import Theory.GroupAction.CyclicCommutatorTransport
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Assembly of the higher-field Borel torus calculations

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954 (PDF p.971).

The seven model branches calculate the Borel at any specified Sylow two-subgroup,
its two-residual, its genuine torus quotient, and the actions on that quotient.
Here their results are assembled in one source interface. A model witness
contains an actual multiplicative equivalence and the exact earlier
semilinear or graph/field automorphism-classification input. No Borel placement,
torus-action formula or torus conclusion is a field of that witness. In the
unitary cases the matrix field has order (2ⁿ)² and the fixed field has order 2ⁿ.
The special and projective carriers remain separate constructors.

Transport first carries the Sylow normalizer and residual through the model
isomorphism. It then carries both displacement fixation and the entire cyclic
commutator quotient. Thus the calculation applies to the specified actor,
including an arbitrary inner twist, without replacing it by an involution.
The resulting trichotomy has degrees two and six only for nonunitary models,
and degree three only for unitary models. Combining it with the outer
commutator bound leaves precisely L₂(4), (S)L₃(4), and (S)U₃(8) when that
quotient has order at most three.

Ambient conjugation requires only relative normalization of K. Its full fixer
is the embedded Sylow joined with C_T(K). The equivalence
`Model.conjugation_fixers_eq_sylow_iff` makes the additional kernel-control
obligation explicit. Neither that control nor the earlier automorphism
classification is proved here; the local source assembly must supply them.
The literal subgroup assertion from the source is retained in
`torusCentralizer_eq_requires_kernel_control`. These intrinsic calculations
are not the full exclusion theorem 13.8.20.
-/

@[expose] public section
open Subgroup
open Theory.GroupAction.ModelConjugation Theory.GroupAction.OddCommutatorImage
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.Assembly
variable {D E : Type*} [Group D] [Group E]

/-- The source B at a specified Sylow, inside the intrinsic model. -/
abbrev residualAt (S : Sylow 2 D) : Subgroup D := borelResidual (normalizer (S : Set D))

/-- Pointwise fixation of O³(B)O₂(B)/O₂(B), using actual displacements. -/
def FixesTorus (B : Subgroup D) (a : MulAut D) : Prop :=
  ∀ x ∈ residualIn 3 B ⊔ B.pCoreIn 2, a x * x⁻¹ ∈ B.pCoreIn 2

/-- Normality is only used inside B. -/
theorem fixesTorus_iff_left (B : Subgroup D) (a : MulAut D) :
    FixesTorus B a ↔ ∀ x ∈ residualIn 3 B ⊔ B.pCoreIn 2,
      x⁻¹ * a x ∈ B.pCoreIn 2 := by
  have hn : B ≤ normalizer (B.pCoreIn 2) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pCore 2 B).le_normalizer_map B.subtype
  constructor
  · intro h x hx
    have hxB := (sup_le (map_subtype_le _) (pCoreIn_le 2 B)) hx
    have hh := le_normalizer_iff.mp hn x⁻¹ (B.inv_mem hxB) _ (h x hx)
    simpa only [inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hh
  · intro h x hx
    have hxB := (sup_le (map_subtype_le _) (pCoreIn_le 2 B)) hx
    have hh := le_normalizer_iff.mp hn x hxB _ (h x hx)
    simpa only [mul_inv_cancel_left] using hh

/-- The order uses the intrinsic two-core of the full cyclic-action commutator. -/
noncomputable abbrev commutatorOrder (B : Subgroup D) (a : MulAut D) : ℕ :=
  let C := commutatorSubgroup (zpowers a) D B
  Nat.card (C ⧸ pCore 2 C)

/-- The source trichotomy and its exceptional-degree commutator restriction. -/
def TorusResult (D : Type*) [Group D] (n : ℕ) (unitary four : Bool) : Prop :=
  ∀ (S : Sylow 2 D) (A : Subgroup (MulAut D)), IsPGroup 2 A →
    (S : Subgroup D).map MulAut.conj ≤ A →
    (∀ a ∈ A, (S : Subgroup D).map a.toMonoidHom = S) →
    ((∀ a ∈ A, FixesTorus (residualAt S) a ↔ a ∈ (S : Subgroup D).map MulAut.conj) ∨
      (unitary = false ∧ (n = 2 ∨ n = 6)) ∨ (unitary = true ∧ n = 3)) ∧
    (unitary = false → (n = 2 ∨ n = 6) → ∀ a ∈ A,
      a ∉ MulAut.innerSubgroup D →
      (four = true ∧ n = 2) ∨ 3 < commutatorOrder (residualAt S) a)

/-- This deduction uses both the fixer calculation and the large-commutator bound. -/
theorem small_outer_fixer_exception {n : ℕ} {unitary four : Bool}
    (h : TorusResult D n unitary four)
    (S : Sylow 2 D) (A : Subgroup (MulAut D)) (hA : IsPGroup 2 A)
    (hinner : (S : Subgroup D).map MulAut.conj ≤ A)
    (hstable : ∀ a ∈ A, (S : Subgroup D).map a.toMonoidHom = S)
    (a : MulAut D) (ha : a ∈ A) (hout : a ∉ MulAut.innerSubgroup D)
    (hfix : FixesTorus (residualAt S) a)
    (hsmall : commutatorOrder (residualAt S) a ≤ 3) :
    (four = true ∧ n = 2) ∨ (unitary = true ∧ n = 3) := by
  obtain ⟨halt, hbound⟩ := h S A hA hinner hstable
  rcases halt with hfixers | ⟨hu, hn⟩ | hu
  · obtain ⟨s, _, hs⟩ := (hfixers a ha).mp hfix
    exact (hout ⟨s, hs⟩).elim
  · rcases hbound hu hn a ha hout with hex | hgt
    · exact Or.inl hex
    · exact (Nat.not_lt_of_ge hsmall hgt).elim
  · exact Or.inr hu

/-- Residual Borel transport uses the normalizer of the actual transported Sylow. -/
theorem residualAt_map [Finite D] (e : D ≃* E) (S : Sylow 2 D) :
    (residualAt S).map e.toMonoidHom = residualAt (S.mapSurjective (f := e.toMonoidHom) e.surjective) := by
  change (residualIn 2 (normalizer (S : Set D))).map e.toMonoidHom =
    residualIn 2 (normalizer ((S : Subgroup D).map e.toMonoidHom : Set E))
  exact (map_embedded_pResidual 2 _ e.toMonoidHom).trans
    (congrArg (residualIn 2) ((S : Subgroup D).map_normalizer_eq_of_bijective e.bijective))

/-- Actual displacement fixation is invariant under a model equivalence. -/
theorem fixesTorus_map_iff [Finite D] (e : D ≃* E) (B : Subgroup D) (a : MulAut D) :
    FixesTorus (B.map e.toMonoidHom) (MulAut.congr e a) ↔ FixesTorus B a := by
  unfold FixesTorus residualIn
  rw [← map_embedded_pResidual, ← map_pCoreIn_of_injective 2 B e.toMonoidHom e.injective,
    ← Subgroup.map_sup]
  constructor
  · intro h x hx
    have hh := h (e x) (mem_map_of_mem e.toMonoidHom hx)
    have he : MulAut.congr e a (e x) * (e x)⁻¹ = e (a x * x⁻¹) := by
      simp [MulAut.congr]
    rw [he] at hh
    exact (mem_map_iff_mem e.injective).mp hh
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa [MulAut.congr] using mem_map_of_mem e.toMonoidHom (h x hx)

/-- Transfer the entire source calculation, including its commutator quotient,
along an actual multiplicative equivalence. -/
theorem TorusResult.of_equiv [Finite D] (e : D ≃* E) {n : ℕ} {unitary four : Bool}
    (h : TorusResult E n unitary four) : TorusResult D n unitary four := by
  intro S A hA hinner hstable
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let A' := A.map (MulAut.congr e).toMonoidHom
  have hI : (S' : Subgroup E).map MulAut.conj ≤ A' := by
    change ((S : Subgroup D).map e.toMonoidHom).map MulAut.conj ≤ A'
    rw [← inner_image_congr e (S : Subgroup D)]
    exact map_mono hinner
  have hS : ∀ a ∈ A', (S' : Subgroup E).map a.toMonoidHom = S' := by
    rintro _ ⟨a, ha, rfl⟩
    exact stable_map_congr e _ a (hstable a ha)
  have hfix (a : MulAut D) :
      FixesTorus (residualAt S') (MulAut.congr e a) ↔ FixesTorus (residualAt S) a := by
    rw [← residualAt_map e S]
    exact fixesTorus_map_iff e _ a
  have hmem (a : MulAut D) :
      MulAut.congr e a ∈ (S' : Subgroup E).map MulAut.conj ↔
        a ∈ (S : Subgroup D).map MulAut.conj := by
    change MulAut.congr e a ∈ ((S : Subgroup D).map e.toMonoidHom).map MulAut.conj ↔ _
    rw [← inner_image_congr e (S : Subgroup D)]
    exact mem_map_iff_mem (MulAut.congr e).injective
  obtain ⟨halt, hb⟩ := h S' A' (hA.map _) hI hS
  constructor
  · rcases halt with hfixers | hex
    · exact Or.inl fun a ha => (hfix a).symm.trans
        ((hfixers _ (mem_map_of_mem _ ha)).trans (hmem a))
    · exact Or.inr hex
  · intro hu hn a ha hout
    have hh := hb hu hn (MulAut.congr e a) (mem_map_of_mem _ ha) (congr_outer e a hout)
    have hc := card_cyclic_commutator_quotient e a (residualAt S)
    dsimp only at hc
    rw [residualAt_map e S] at hc
    change commutatorOrder (residualAt S) a =
      commutatorOrder (residualAt S') (MulAut.congr e a) at hc
    exact hh.imp_right (fun hgt => hc.symm ▸ hgt)


open scoped MatrixGroups
open BenderSuzuki.MatrixGroups HermitianForm.BorelTorus
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterF.Source.Unitary

section Split
variable {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}

/-- Rank one has precisely the permitted degree-two small exception. -/
theorem linearTwo_result (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hcover : ∀ a : MulAut PSL(2,F), ∃ (g : PSL(2,F)) (σ : F ≃+* F),
      a = MulAut.conj g * Atlas.fieldEquivPSL 2 σ) :
    TorusResult PSL(2,F) n false true := by
  intro S A hA hI hS
  constructor
  · by_cases hn2 : n = 2
    · exact Or.inr (Or.inl ⟨rfl, Or.inl hn2⟩)
    by_cases hn6 : n = 6
    · exact Or.inr (Or.inl ⟨rfl, Or.inr hn6⟩)
    exact Or.inl fun a ha => (fixesTorus_iff_left _ a).trans
      (LinearTwo.actor_fixesResidualTorus_iff hn hF hn2 hn6 S A hA hS hcover a ha)
  · intro _ hex a ha hout
    rcases hex with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (LinearTwo.outer_commutator_quotient_card_gt_three
        hF S A hA hS hcover a ha hout)

/-- Special linear degree three retains its actual covering carrier. -/
theorem specialLinearThree_result (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hcover : Matrix.PSL3.OuterSolvable.standard F = ⊤) :
    TorusResult SL(3,F) n false true := by
  intro S A hA hI hS
  constructor
  · rcases LinearThree.special_actor_alternative hF hn hcover S A hA hS hI with
      h | h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨rfl, Or.inl h⟩)
    · exact Or.inr (Or.inl ⟨rfl, Or.inr h⟩)
  · intro _ hex a ha hout
    rcases hex with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (LinearThree.special_six_outer_commutator_of_standard
        hF hcover S A hA hS hI a ha hout)

/-- The projective linear calculation keeps its cubic scalar quotient. -/
theorem projectiveLinearThree_result (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hcover : Matrix.PSL3.OuterSolvable.standard F = ⊤) :
    TorusResult PSL(3,F) n false true := by
  intro S A hA hI hS
  constructor
  · rcases LinearThree.projective_actor_alternative hF hn hcover S A hA hS hI with
      h | h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨rfl, Or.inl h⟩)
    · exact Or.inr (Or.inl ⟨rfl, Or.inr h⟩)
  · intro _ hex a ha hout
    rcases hex with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (LinearThree.projective_six_outer_commutator_of_standard
        hF hcover S A hA hS hI a ha hout)

/-- Sp₄(4) is excluded as well as Sp₄(64) by its two torus factors. -/
theorem symplecticFour_result (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hcover : ∀ a : MulAut (Sp F), DiagramAutomorphisms.PreservesDiagram a →
      ∃ (g : Sp F) (σ : F ≃+* F),
        a = MulAut.conj g * DiagramAutomorphisms.fieldAutomorphism σ) :
    TorusResult (Sp F) n false false := by
  intro S A hA hI hS
  constructor
  · by_cases hn2 : n = 2
    · exact Or.inr (Or.inl ⟨rfl, Or.inl hn2⟩)
    by_cases hn6 : n = 6
    · exact Or.inr (Or.inl ⟨rfl, Or.inr hn6⟩)
    exact Or.inl fun a ha => (fixesTorus_iff_left _ a).trans
      (symplecticFour_fixes_residual_iff_mem_innerSylow
        hF hn hcover hn2 hn6 S A hA hI hS ha)
  · intro _ hex a ha hout
    exact Or.inr (symplecticFour_three_lt_commutator_quotient hF hn hcover hex S A hA hS ha hout)

/-- The actual octonion G₂ model has no small-commutator exception. -/
theorem g2_result (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hcover : Function.Surjective (Atlas.G2.LieAutomorphismExtensions.semilinearAction (F := F))) :
    TorusResult (Atlas.G2.Model F) n false false := by
  intro S A hA hI hS
  constructor
  · by_cases hn2 : n = 2
    · exact Or.inr (Or.inl ⟨rfl, Or.inl hn2⟩)
    by_cases hn6 : n = 6
    · exact Or.inr (Or.inl ⟨rfl, Or.inr hn6⟩)
    exact Or.inl fun _ ha => G2.fixesResidualTorusAt_iff_innerSylow
      hF hn hn2 hn6 hcover S A hA hS hI ha
  · intro _ hex a ha hout
    exact Or.inr (G2.exceptional_outer_commutator_gt_three hF hn hex hcover S A hA hS hI ha hout)
end Split

section Unitary
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E) {n : ℕ}

/-- The full special unitary torus leaves only fixed-field degree three. -/
theorem specialUnitaryThree_result (hcard : Nat.card E = (2 ^ n) ^ 2) (hn : 1 < n)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (hcover : ∀ a : MulAut (FormTransport.standardForm J).specialSubgroup,
      ∃ σ : E ≃+* E, (FormTransport.standardForm J).HasSpecialUnitarySemilinearForm a σ) :
    TorusResult J.specialSubgroup n true false := by
  intro S A hA hI hS
  constructor
  · rcases UnitaryThree.su_sylow_torus_alternative J hn hcard hconj hcover S A hA hI hS with
      h | h
    · exact Or.inr (Or.inr ⟨rfl, h⟩)
    · exact Or.inl h
  · intro h
    cases h

/-- The projective unitary calculation uses the actual scalar quotient over E. -/
theorem projectiveUnitaryThree_result (hcard : Nat.card E = (2 ^ n) ^ 2) (hn : 1 < n)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (hcover : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)),
      ∃ σ : E ≃+* E, (FormTransport.standardForm J).HasUnitarySemilinearForm a σ) :
    TorusResult (ProjectiveSpecialUnitaryMatrixGroup J) n true false := by
  intro S A hA hI hS
  constructor
  · rcases UnitaryThree.psu_sylow_torus_alternative J hn hcard hconj hcover S A hA hI hS with
      h | h
    · exact Or.inr (Or.inr ⟨rfl, h⟩)
    · exact Or.inl h
  · intro h
    cases h
end Unitary


universe u v
/-- The seven actual higher-field carriers, with only earlier automorphism
classification left explicit. The Boolean indices record unitary type and
whether degree two is a permitted small-commutator exception. Every case
contains a genuine group equivalence, not a disconnected family label. -/
inductive Model (D : Type u) [Group D] (n : ℕ) : Bool → Bool → Prop
  | linearTwo (F : Type v) [Field F] [Finite F] [CharP F 2]
      (hF : Nat.card F = 2 ^ n) (e : D ≃* PSL(2,F))
      (hcover : ∀ a : MulAut PSL(2,F), ∃ (g : PSL(2,F)) (σ : F ≃+* F),
        a = MulAut.conj g * Atlas.fieldEquivPSL 2 σ) : Model D n false true
  | specialLinearThree (F : Type v) [Field F] [Finite F] [CharP F 2]
      (hF : Nat.card F = 2 ^ n) (e : D ≃* SL(3,F))
      (hcover : Matrix.PSL3.OuterSolvable.standard F = ⊤) : Model D n false true
  | projectiveLinearThree (F : Type v) [Field F] [Finite F] [CharP F 2]
      (hF : Nat.card F = 2 ^ n) (e : D ≃* PSL(3,F))
      (hcover : Matrix.PSL3.OuterSolvable.standard F = ⊤) : Model D n false true
  | specialUnitaryThree (E : Type v) [Field E] [Finite E] (J : HermitianForm 3 E)
      (hE : Nat.card E = (2 ^ n) ^ 2) (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
      (e : D ≃* J.specialSubgroup)
      (hcover : ∀ a : MulAut (FormTransport.standardForm J).specialSubgroup,
        ∃ σ : E ≃+* E, (FormTransport.standardForm J).HasSpecialUnitarySemilinearForm a σ) :
      Model D n true false
  | projectiveUnitaryThree (E : Type v) [Field E] [Finite E] (J : HermitianForm 3 E)
      (hE : Nat.card E = (2 ^ n) ^ 2) (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
      (e : D ≃* ProjectiveSpecialUnitaryMatrixGroup J)
      (hcover : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)),
        ∃ σ : E ≃+* E, (FormTransport.standardForm J).HasUnitarySemilinearForm a σ) :
      Model D n true false
  | symplecticFour (F : Type v) [Field F] [Finite F] [CharP F 2]
      (hF : Nat.card F = 2 ^ n) (e : D ≃* Sp F)
      (hcover : ∀ a : MulAut (Sp F), DiagramAutomorphisms.PreservesDiagram a →
        ∃ (g : Sp F) (σ : F ≃+* F),
          a = MulAut.conj g * DiagramAutomorphisms.fieldAutomorphism σ) : Model D n false false
  | g2 (F : Type v) [Field F] [Finite F] [CharP F 2]
      (hF : Nat.card F = 2 ^ n) (e : D ≃* Atlas.G2.Model F)
      (hcover : Function.Surjective (Atlas.G2.LieAutomorphismExtensions.semilinearAction (F := F))) :
      Model D n false false

/-- Assemble all seven intrinsic calculations and transport them to the given
carrier. No Borel alignment, torus action or torus conclusion is assumed. -/
theorem Model.torusResult [Finite D] {n : ℕ} {unitary four : Bool}
    (model : Model D n unitary four) (hn : 1 < n) : TorusResult D n unitary four := by
  cases model with
  | linearTwo F hF e hcover =>
    exact (linearTwo_result hF hn hcover).of_equiv e
  | specialLinearThree F hF e hcover =>
    exact (specialLinearThree_result hF hn hcover).of_equiv e
  | projectiveLinearThree F hF e hcover =>
    exact (projectiveLinearThree_result hF hn hcover).of_equiv e
  | specialUnitaryThree E J hE hconj e hcover =>
    exact (specialUnitaryThree_result J hE hn hconj hcover).of_equiv e
  | projectiveUnitaryThree E J hE hconj e hcover =>
    exact (projectiveUnitaryThree_result J hE hn hconj hcover).of_equiv e
  | symplecticFour F hF e hcover =>
    exact (symplecticFour_result hF hn hcover).of_equiv e
  | g2 F hF e hcover =>
    exact (g2_result hF hn hcover).of_equiv e

/-- An outer fixer with small commutator quotient leaves exactly L₂(4),
(S)L₃(4), or (S)U₃(8), through the actual model witness. -/
theorem Model.small_outer_fixer_exception [Finite D] {n : ℕ} {unitary four : Bool}
    (model : Model D n unitary four) (hn : 1 < n)
    (S : Sylow 2 D) (A : Subgroup (MulAut D)) (hA : IsPGroup 2 A)
    (hinner : (S : Subgroup D).map MulAut.conj ≤ A)
    (hstable : ∀ a ∈ A, (S : Subgroup D).map a.toMonoidHom = S)
    (a : MulAut D) (ha : a ∈ A) (hout : a ∉ MulAut.innerSubgroup D)
    (hfix : FixesTorus (residualAt S) a)
    (hsmall : commutatorOrder (residualAt S) a ≤ 3) :
    (four = true ∧ n = 2) ∨ (unitary = true ∧ n = 3) :=
  Assembly.small_outer_fixer_exception (model.torusResult hn) S A hA hinner hstable a ha hout hfix hsmall


/-- Outside the exceptional parameters, the full preimage in the ambient
actor group is the embedded Sylow joined with the genuine action kernel.
The first disjunct is an equality of pointwise section-fixer conditions. -/
theorem Model.conjugation_alternative [Finite D] {n : ℕ} {unitary four : Bool}
    (model : Model D n unitary four) (hn : 1 < n)
    {G : Type*} [Group G] (T K : Subgroup G) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G)) (e : K ≃* D) (S : Sylow 2 D)
    (hST : (S : Subgroup D).map (K.subtype.comp e.symm.toMonoidHom) ≤ T)
    (hstable : ∀ t : T, (S : Subgroup D).map (action T K hTK e t).toMonoidHom = S) :
    (∀ t : T, FixesTorus (residualAt S) (action T K hTK e t) ↔
      (t : G) ∈ (S : Subgroup D).map (K.subtype.comp e.symm.toMonoidHom) ⊔
        (T ⊓ centralizer (K : Set G))) ∨
    (unitary = false ∧ (n = 2 ∨ n = 6)) ∨ (unitary = true ∧ n = 3) := by
  let ρ := action T K hTK e
  have hI := inner_le_action_range T K hTK e S hST
  have hS : ∀ a ∈ ρ.range, (S : Subgroup D).map a.toMonoidHom = S := by
    rintro _ ⟨t, rfl⟩
    exact hstable t
  have hA : IsPGroup 2 ρ.range := hT.of_surjective _ ρ.rangeRestrict_surjective
  rcases (model.torusResult hn S ρ.range hA hI hS).1 with hfix | hex
  · refine Or.inl fun t => ?_
    exact (hfix _ ⟨t, rfl⟩).trans (action_mem_inner_iff T K hTK e S hST t)
  · exact Or.inr hex

/-- This characterizes the extra kernel control required for the literal
source fixer equality. It is not supplied by an intrinsic model calculation. -/
theorem Model.conjugation_fixers_eq_sylow_iff [Finite D] {n : ℕ} {unitary four : Bool}
    (model : Model D n unitary four) (hn : 1 < n)
    (hgeneric : ¬ ((unitary = false ∧ (n = 2 ∨ n = 6)) ∨ (unitary = true ∧ n = 3)))
    {G : Type*} [Group G] (T K : Subgroup G) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G)) (e : K ≃* D) (S : Sylow 2 D)
    (hST : (S : Subgroup D).map (K.subtype.comp e.symm.toMonoidHom) ≤ T)
    (hstable : ∀ t : T, (S : Subgroup D).map (action T K hTK e t).toMonoidHom = S) :
    (∀ t : T, FixesTorus (residualAt S) (action T K hTK e t) ↔
      (t : G) ∈ (S : Subgroup D).map (K.subtype.comp e.symm.toMonoidHom)) ↔
      T ⊓ centralizer (K : Set G) ≤
        (S : Subgroup D).map (K.subtype.comp e.symm.toMonoidHom) := by
  have hfix := (model.conjugation_alternative hn T K hT hTK e S hST hstable).resolve_right hgeneric
  constructor
  · intro h x hx
    have hx' : x ∈ (S : Subgroup D).map (K.subtype.comp e.symm.toMonoidHom) ⊔
        (T ⊓ centralizer (K : Set G)) :=
      (show T ⊓ centralizer (K : Set G) ≤ _ from le_sup_right) hx
    exact (h ⟨x, hx.1⟩).mp ((hfix ⟨x, hx.1⟩).mpr hx')
  · intro h t
    rw [hfix t, sup_eq_left.mpr h]

/-- The same kernel is a necessary condition in the literal subgroup
centralizer convention used by the source assembly. -/
theorem torusCentralizer_eq_requires_kernel_control
    {G : Type*} [Group G] (T K B₀ : Subgroup G)
    (hBK : borelResidual B₀ ≤ K)
    (hsource : torusCentralizer T (borelResidual B₀) = B₀.pCoreIn 2) :
    T ⊓ centralizer (K : Set G) ≤ B₀.pCoreIn 2 :=
  (central_kernel_le_torusCentralizer T (borelResidual B₀) K hBK).trans_eq hsource

/-- The exceptional conclusion still contains the original genuine model
equivalence and exact field order; the family indices are not free tags. -/
theorem Model.small_outer_fixer_models [Finite D] {n : ℕ} {unitary four : Bool}
    (model : Model.{_, v} D n unitary four) (hn : 1 < n)
    (S : Sylow 2 D) (A : Subgroup (MulAut D)) (hA : IsPGroup 2 A)
    (hinner : (S : Subgroup D).map MulAut.conj ≤ A)
    (hstable : ∀ a ∈ A, (S : Subgroup D).map a.toMonoidHom = S)
    (a : MulAut D) (ha : a ∈ A) (hout : a ∉ MulAut.innerSubgroup D)
    (hfix : FixesTorus (residualAt S) a)
    (hsmall : commutatorOrder (residualAt S) a ≤ 3) :
    Model.{_, v} D 2 false true ∨ Model.{_, v} D 3 true false := by
  have hex := model.small_outer_fixer_exception hn S A hA hinner hstable a ha hout hfix hsmall
  rcases hex with ⟨hf, h2⟩ | ⟨hu, h3⟩
  · subst four
    subst n
    have hu : unitary = false := by cases model <;> rfl
    subst unitary
    exact Or.inl model
  · subst unitary
    subst n
    have hf : four = false := by cases model <;> rfl
    subst four
    exact Or.inr model

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.Assembly
