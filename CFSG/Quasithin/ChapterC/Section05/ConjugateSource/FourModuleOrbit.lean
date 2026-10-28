module
public import Theory.GroupAction.FourModuleOrbit
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# The four-module orbit in C.5.6(7)

This is the `s = 2` action argument on printed p.158 of the Aschbacher–Smith
combined manuscript (1 March 2004). The modules are the actual subgroups
`U₁`, `U₂`, `U₁ˣ`, and `U₂ˣ`, with the source's right conjugation convention.
Their invariant noncommutation relation rules out the cyclic and dihedral
possibilities directly, so the literal permutation image and kernel quotient
are Klein four-groups. Every actor square fixes each module, and the two
conjugate-generated factors commute.

The prior source steps retain responsibility for the index-two subgroup, the
original invariant pair and exchange, and the initial commutator statements.
`SourceInputs.toInputs` constructs invariance and distinctness of all four
modules from those facts; the module's self-commutation supplies the needed
abelianness. No
permutation table, missing cross commutator or quotient recognition is an
input to this argument.
-/

public section

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.FourModuleOrbit
open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- The source convention is right conjugation: `Uˣ = x⁻¹ U x`. -/
@[expose] def modules (U₁ U₂ : Subgroup G) (x : G) : Fin 4 → Subgroup G :=
  ![U₁, U₂, U₁.conjBy x⁻¹, U₂.conjBy x⁻¹]

/-- The actual four-module orbit and the previously established commutation
facts in the `s = 2` branch of C.5.6(7). -/
structure Inputs (M₀ T_H U₁ U₂ : Subgroup G) (x : G) : Prop where
  index_two : T_H.relIndex M₀ = 2
  x_mem : x ∈ M₀
  distinct : Function.Injective (modules U₁ U₂ x)
  invariant : ∀ g : M₀, ∀ i : Fin 4, ∃ j : Fin 4,
    modules U₁ U₂ x j = (modules U₁ U₂ x i).conjBy (g : G)
  pair_zero : ∀ g ∈ T_H, U₁.conjBy g = U₁ ∨ U₁.conjBy g = U₂
  pair_one : ∀ g ∈ T_H, U₂.conjBy g = U₁ ∨ U₂.conjBy g = U₂
  exchange : ∃ t : M₀, (t : G) ∈ T_H ∧ U₁.conjBy (t : G) = U₂
  noncommuting : ⁅U₁, U₁.conjBy x⁻¹⁆ ≠ ⊥
  original_commuting : ⁅U₁, U₂⁆ = ⊥
  cross_commuting : ⁅U₁.conjBy x⁻¹, U₂⁆ = ⊥

variable {M₀ T_H U₁ U₂ : Subgroup G} {x : G}

private noncomputable def moveIndex (h : Inputs M₀ T_H U₁ U₂ x)
    (g : M₀) (i : Fin 4) : Fin 4 := (h.invariant g i).choose

private theorem moveIndex_spec (h : Inputs M₀ T_H U₁ U₂ x)
    (g : M₀) (i : Fin 4) :
    modules U₁ U₂ x (moveIndex h g i) = (modules U₁ U₂ x i).conjBy (g : G) :=
  (h.invariant g i).choose_spec

/-- The actual conjugation permutation of the four original subgroups. -/
private noncomputable def permutation (h : Inputs M₀ T_H U₁ U₂ x) (g : M₀) :
    Equiv.Perm (Fin 4) where
  toFun := moveIndex h g
  invFun := moveIndex h g⁻¹
  left_inv i := by
    apply h.distinct
    rw [moveIndex_spec, moveIndex_spec]
    exact Subgroup.conjBy_inv _ _
  right_inv i := by
    apply h.distinct
    rw [moveIndex_spec, moveIndex_spec]
    exact Subgroup.conjBy_inv' _ _

/-- The homomorphism induced by literal left conjugation on the four modules.
The source's right conjugator `x` is represented by the actor `x⁻¹`. -/
noncomputable def action (h : Inputs M₀ T_H U₁ U₂ x) :
    M₀ →* Equiv.Perm (Fin 4) where
  toFun := permutation h
  map_one' := by
    apply Equiv.ext
    intro i
    apply h.distinct
    change modules U₁ U₂ x (moveIndex h 1 i) = modules U₁ U₂ x i
    rw [moveIndex_spec]
    exact Subgroup.conjBy_one _
  map_mul' g k := by
    apply Equiv.ext
    intro i
    apply h.distinct
    change modules U₁ U₂ x (moveIndex h (g*k) i) =
      modules U₁ U₂ x (moveIndex h g (moveIndex h k i))
    rw [moveIndex_spec, moveIndex_spec, moveIndex_spec]
    exact Subgroup.conjBy_mul _ _ _

theorem action_apply (h : Inputs M₀ T_H U₁ U₂ x) (g : M₀) (i : Fin 4) :
    modules U₁ U₂ x (action h g i) = (modules U₁ U₂ x i).conjBy (g : G) :=
  moveIndex_spec h g i

private theorem commutator_conjugate (A B : Subgroup G) (g : G) :
    ⁅A.conjBy g, B.conjBy g⁆ = ⊥ ↔ ⁅A,B⁆ = ⊥ := by
  rw [Subgroup.conjBy, Subgroup.conjBy, ← Subgroup.map_commutator]
  exact Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective

/-- The generic four-point argument applies to the genuine subgroup
commutator relation and conjugation homomorphism. -/
theorem source_setup (h : Inputs M₀ T_H U₁ U₂ x) :
    ∃ t : M₀, _root_.FourModuleOrbit.Setup (action h) (T_H.subgroupOf M₀)
      ⟨x⁻¹, M₀.inv_mem h.x_mem⟩ t
      (fun i j => ⁅modules U₁ U₂ x i, modules U₁ U₂ x j⁆ ≠ ⊥) := by
  obtain ⟨t,ht,he⟩ := h.exchange
  refine ⟨t, ?_⟩
  constructor
  · exact h.index_two
  · intro g hg
    rcases h.pair_zero (g : G) hg with he | he
    · left
      apply h.distinct
      rw [action_apply]
      exact he
    · right
      apply h.distinct
      rw [action_apply]
      exact he
  · intro g hg
    rcases h.pair_one (g : G) hg with he | he
    · left
      apply h.distinct
      rw [action_apply]
      exact he
    · right
      apply h.distinct
      rw [action_apply]
      exact he
  · apply h.distinct
    rw [action_apply]
    rfl
  · apply h.distinct
    rw [action_apply]
    rfl
  · exact ht
  · apply h.distinct
    rw [action_apply]
    exact he
  · intro i j hne
    rw [Subgroup.commutator_comm]
    exact hne
  · intro g i j hne
    rw [action_apply, action_apply]
    exact mt (commutator_conjugate _ _ _).mp hne
  · exact h.noncommuting
  · exact fun hh => hh h.cross_commuting

/-- The induced image in the source proof is a regular Klein four-group. -/
theorem image_isKleinFour (h : Inputs M₀ T_H U₁ U₂ x) :
    IsKleinFour (action h).range := by
  obtain ⟨t,hs⟩ := source_setup h
  exact hs.isKleinFour

/-- Every image element is determined uniquely by the image of `U₁`, and
all four modules occur. -/
theorem image_regular (h : Inputs M₀ T_H U₁ U₂ x) :
    Function.Bijective (fun p : (action h).range => (p : Equiv.Perm (Fin 4)) 0) := by
  obtain ⟨t,hs⟩ := source_setup h
  exact hs.regular

/-- The index-two subgroup has exactly two induced permutations. -/
theorem pair_image_card (h : Inputs M₀ T_H U₁ U₂ x) :
    Nat.card ((T_H.subgroupOf M₀).map (action h)) = 2 := by
  obtain ⟨t,hs⟩ := source_setup h
  exact hs.card_pair_range

/-- Every actor square fixes each original subgroup in the four-module orbit. -/
theorem square_fixes_modules (h : Inputs M₀ T_H U₁ U₂ x) (g : M₀) (i : Fin 4) :
    (modules U₁ U₂ x i).conjBy ((g : G)^2) = modules U₁ U₂ x i := by
  obtain ⟨t,hs⟩ := source_setup h
  have hsquare : action h (g^2) = 1 := by rw [map_pow, hs.square g]
  have ha := action_apply h (g^2) i
  rw [hsquare] at ha
  exact ha.symm

/-- In particular the source conjugator has a square normalizing every module. -/
theorem x_square_fixes_modules (h : Inputs M₀ T_H U₁ U₂ x) (i : Fin 4) :
    (modules U₁ U₂ x i).conjBy (x^2) = modules U₁ U₂ x i :=
  square_fixes_modules h ⟨x,h.x_mem⟩ i

/-- The missing cross commutator is forced by the action, rather than assumed. -/
theorem other_cross_commuting (h : Inputs M₀ T_H U₁ U₂ x) :
    ⁅U₁, U₂.conjBy x⁻¹⁆ = ⊥ := by
  obtain ⟨t,hs⟩ := source_setup h
  exact not_not.mp hs.other_cross_commuting

/-- All four cross pairs between the two conjugate-generated factors commute. -/
theorem cross_commutators (h : Inputs M₀ T_H U₁ U₂ x) :
    ⁅U₁, U₂⁆ = ⊥ ∧ ⁅U₁, U₂.conjBy x⁻¹⁆ = ⊥ ∧
    ⁅U₁.conjBy x⁻¹, U₂⁆ = ⊥ ∧ ⁅U₁.conjBy x⁻¹, U₂.conjBy x⁻¹⁆ = ⊥ :=
  ⟨h.original_commuting, other_cross_commuting h, h.cross_commuting,
    (commutator_conjugate _ _ _).mpr h.original_commuting⟩
/-- The two subgroups generated by corresponding conjugate pairs centralize
one another, as required for the factorization on printed p.158. -/
theorem conjugate_factors_commute (h : Inputs M₀ T_H U₁ U₂ x) :
    ⁅U₁ ⊔ U₁.conjBy x⁻¹, U₂ ⊔ U₂.conjBy x⁻¹⁆ = ⊥ := by
  obtain ⟨h00,h01,h10,h11⟩ := cross_commutators h
  simp only [Subgroup.commutator_eq_bot_iff_le_centralizer] at h00 h01 h10 h11 ⊢
  apply sup_le
  · exact Subgroup.le_centralizer_iff.mpr (sup_le
      (Subgroup.le_centralizer_iff.mp h00) (Subgroup.le_centralizer_iff.mp h01))
  · exact Subgroup.le_centralizer_iff.mpr (sup_le
      (Subgroup.le_centralizer_iff.mp h10) (Subgroup.le_centralizer_iff.mp h11))

/-- The source kernel `I` is the actual point stabilizer, proving regularity
without a separate stabilizer assumption. -/
theorem kernel_eq_normalizer (h : Inputs M₀ T_H U₁ U₂ x) :
    (action h).ker = (normalizer (U₁ : Set G)).subgroupOf M₀ := by
  obtain ⟨t,hs⟩ := source_setup h
  ext g
  constructor
  · intro hg
    have he : action h g = 1 := hg
    have ha := action_apply h g 0
    rw [he] at ha
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr ha.symm
  · intro hg
    have he : U₁.conjBy (g : G) = U₁ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have hz : action h g 0 = 0 := by
      apply h.distinct
      rw [action_apply]
      exact he
    have hr := hs.regular.1
    apply congrArg Subtype.val (hr (a₁ := ⟨action h g, ⟨g,rfl⟩⟩)
      (a₂ := ⟨1, ⟨1,(action h).map_one⟩⟩) hz)

/-- The literal quotient by the conjugation kernel, `M₀/I`, is a Klein
four-group. -/
theorem quotient_isKleinFour (h : Inputs M₀ T_H U₁ U₂ x) :
    IsKleinFour (M₀ ⧸ (action h).ker) := by
  have hk := image_isKleinFour h
  let e := QuotientGroup.quotientKerEquivRange (action h)
  refine ⟨?_, ?_⟩
  · exact (Nat.card_congr e.toEquiv).trans hk.card_four
  · exact (Monoid.exponent_eq_of_mulEquiv e).trans hk.exponent_two

/-- The four named subgroups are exactly the actual conjugacy orbit. -/
theorem modules_eq_conjugacy_orbit (h : Inputs M₀ T_H U₁ U₂ x) (V : Subgroup G) :
    (∃ i : Fin 4, V = modules U₁ U₂ x i) ↔
      ∃ g : M₀, V = U₁.conjBy (g : G) := by
  constructor
  · rintro ⟨i,rfl⟩
    obtain ⟨⟨p,g,rfl⟩, hg⟩ := (image_regular h).2 i
    refine ⟨g, ?_⟩
    have he := action_apply h g 0
    change action h g 0 = i at hg
    rw [hg] at he
    exact he
  · rintro ⟨g,rfl⟩
    exact ⟨action h g 0, (action_apply h g 0).symm⟩

/-- The original pair action and commutator conclusions before constructing
the four-module orbit. -/
structure SourceInputs (M₀ T_H U₁ U₂ : Subgroup G) (x : G) : Prop where
  index_two : T_H.relIndex M₀ = 2
  x_mem : x ∈ M₀
  pair_zero : ∀ g ∈ T_H, U₁.conjBy g = U₁ ∨ U₁.conjBy g = U₂
  exchange : ∃ t : M₀, (t : G) ∈ T_H ∧ U₁.conjBy (t : G) = U₂
  self_commuting : ⁅U₁, U₁⁆ = ⊥
  noncommuting : ⁅U₁, U₁.conjBy x⁻¹⁆ ≠ ⊥
  original_commuting : ⁅U₁, U₂⁆ = ⊥
  cross_commuting : ⁅U₁.conjBy x⁻¹, U₂⁆ = ⊥

private theorem SourceInputs.conjugate_outside_pair
    (h : SourceInputs M₀ T_H U₁ U₂ x) :
    U₁.conjBy x⁻¹ ≠ U₁ ∧ U₁.conjBy x⁻¹ ≠ U₂ := by
  constructor
  · intro he
    exact h.noncommuting (he.symm ▸ h.self_commuting)
  · intro he
    exact h.noncommuting (he.symm ▸ h.original_commuting)

/-- Pair exchange transfers the first module's invariant pair to the second. -/
theorem SourceInputs.pair_one (h : SourceInputs M₀ T_H U₁ U₂ x)
    (g : G) (hg : g ∈ T_H) : U₂.conjBy g = U₁ ∨ U₂.conjBy g = U₂ := by
  obtain ⟨t,ht,he⟩ := h.exchange
  have hp := h.pair_zero (g * (t : G)) (T_H.mul_mem hg ht)
  rw [Subgroup.conjBy_mul, he] at hp
  exact hp

/-- Noncommutation forces the selected conjugator outside the original pair
subgroup; this is not an additional source premise. -/
theorem SourceInputs.x_outside (h : SourceInputs M₀ T_H U₁ U₂ x) : x ∉ T_H := by
  intro hx
  rcases h.pair_zero x⁻¹ (T_H.inv_mem hx) with he | he
  · exact h.conjugate_outside_pair.1 he
  · exact h.conjugate_outside_pair.2 he

private theorem SourceInputs.outside_image
    (h : SourceInputs M₀ T_H U₁ U₂ x) (g : M₀) (hg : (g : G) ∉ T_H) :
    U₁.conjBy (g : G) ≠ U₁ ∧ U₁.conjBy (g : G) ≠ U₂ := by
  let H := T_H.subgroupOf M₀
  let y : M₀ := ⟨x⁻¹, M₀.inv_mem h.x_mem⟩
  have hy : y ∉ H := by
    intro hy
    change x⁻¹ ∈ T_H at hy
    exact h.x_outside (by simpa only [inv_inv] using T_H.inv_mem hy)
  have hg' : g ∉ H := hg
  have hk : y*g⁻¹ ∈ H := (H.mul_mem_iff_of_index_two h.index_two).mpr (by
    simp only [Subgroup.inv_mem_iff]; exact iff_of_false hy hg')
  have he : (U₁.conjBy (g : G)).conjBy ((y*g⁻¹ : M₀) : G) = U₁.conjBy x⁻¹ := by
    rw [Subgroup.conjBy_conjBy]
    simp [y, mul_assoc]
  constructor
  · intro ha
    rw [ha] at he
    rcases h.pair_zero _ hk with hh | hh
    · exact h.conjugate_outside_pair.1 (he.symm.trans hh)
    · exact h.conjugate_outside_pair.2 (he.symm.trans hh)
  · intro ha
    rw [ha] at he
    rcases h.pair_one _ hk with hh | hh
    · exact h.conjugate_outside_pair.1 (he.symm.trans hh)
    · exact h.conjugate_outside_pair.2 (he.symm.trans hh)

private theorem SourceInputs.original_image
    (h : SourceInputs M₀ T_H U₁ U₂ x) (A : Subgroup G)
    (hA : A = U₁ ∨ A = U₂) (g : M₀) :
    ∃ j : Fin 4, modules U₁ U₂ x j = A.conjBy (g : G) := by
  let H := T_H.subgroupOf M₀
  let y : M₀ := ⟨x⁻¹, M₀.inv_mem h.x_mem⟩
  have hp (k : M₀) (hk : k ∈ H) : A.conjBy (k : G) = U₁ ∨ A.conjBy (k : G) = U₂ := by
    rcases hA with rfl | rfl
    · exact h.pair_zero _ hk
    · exact h.pair_one _ hk
  by_cases hg : g ∈ H
  · rcases hp g hg with he | he
    · exact ⟨0,he.symm⟩
    · exact ⟨1,he.symm⟩
  have hy : y ∉ H := by
    intro hy
    change x⁻¹ ∈ T_H at hy
    exact h.x_outside (by simpa only [inv_inv] using T_H.inv_mem hy)
  have hk : y⁻¹*g ∈ H := (H.mul_mem_iff_of_index_two h.index_two).mpr (by
    simp only [Subgroup.inv_mem_iff]; exact iff_of_false hy hg)
  have he : A.conjBy (g : G) =
      (A.conjBy ((y⁻¹*g : M₀) : G)).conjBy x⁻¹ := by
    rw [Subgroup.conjBy_conjBy]
    simp [y]
  rcases hp (y⁻¹*g) hk with hh | hh
  · rw [hh] at he
    exact ⟨2,he.symm⟩
  · rw [hh] at he
    exact ⟨3,he.symm⟩

/-- The index-two condition constructs invariance of the four named modules;
it is not an additional orbit hypothesis. -/
theorem SourceInputs.invariant (h : SourceInputs M₀ T_H U₁ U₂ x)
    (g : M₀) (i : Fin 4) : ∃ j : Fin 4,
      modules U₁ U₂ x j = (modules U₁ U₂ x i).conjBy (g : G) := by
  let y : M₀ := ⟨x⁻¹, M₀.inv_mem h.x_mem⟩
  fin_cases i
  · exact h.original_image U₁ (Or.inl rfl) g
  · exact h.original_image U₂ (Or.inr rfl) g
  · change ∃ j, modules U₁ U₂ x j = (U₁.conjBy x⁻¹).conjBy (g : G)
    rw [Subgroup.conjBy_conjBy]
    exact h.original_image U₁ (Or.inl rfl) (g*y)
  · change ∃ j, modules U₁ U₂ x j = (U₂.conjBy x⁻¹).conjBy (g : G)
    rw [Subgroup.conjBy_conjBy]
    exact h.original_image U₂ (Or.inr rfl) (g*y)

/-- Noncommutation and the original pair exchange force all four labels to be
distinct. Only the source module's self-commutation is needed. -/
theorem SourceInputs.distinct (h : SourceInputs M₀ T_H U₁ U₂ x) :
    Function.Injective (modules U₁ U₂ x) := by
  obtain ⟨t,ht,he⟩ := h.exchange
  have h01 : U₁ ≠ U₂ := by
    intro heq
    apply h.noncommuting
    rw [heq, Subgroup.commutator_comm]
    simpa only [heq] using h.cross_commuting
  have h20 := h.conjugate_outside_pair.1
  have h21 := h.conjugate_outside_pair.2
  have h23 : U₁.conjBy x⁻¹ ≠ U₂.conjBy x⁻¹ := by
    intro hconj
    apply h01
    have heq := congrArg (fun A : Subgroup G => A.conjBy x) hconj
    simpa only [Subgroup.conjBy_inv'] using heq
  let y : M₀ := ⟨x⁻¹, M₀.inv_mem h.x_mem⟩
  have hy : (y : G) ∉ T_H := by
    intro hy
    change x⁻¹ ∈ T_H at hy
    exact h.x_outside (by simpa only [inv_inv] using T_H.inv_mem hy)
  have hyt : ((y*t : M₀) : G) ∉ T_H := by
    intro hyt
    exact hy (by simpa using T_H.mul_mem hyt (T_H.inv_mem ht))
  have hd := h.outside_image (y*t) hyt
  have hd' : U₁.conjBy ((y*t : M₀) : G) = U₂.conjBy x⁻¹ := by
    change U₁.conjBy (x⁻¹ * (t : G)) = U₂.conjBy x⁻¹
    rw [Subgroup.conjBy_mul, he]
  rw [hd'] at hd
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals first
    | exact (h01 hij).elim
    | exact (h01 hij.symm).elim
    | exact (h20 hij).elim
    | exact (h20 hij.symm).elim
    | exact (h21 hij).elim
    | exact (h21 hij.symm).elim
    | exact (h23 hij).elim
    | exact (h23 hij.symm).elim
    | exact (hd.1 hij).elim
    | exact (hd.1 hij.symm).elim
    | exact (hd.2 hij).elim
    | exact (hd.2 hij.symm).elim

/-- The source hypotheses construct the entire four-module orbit input. -/
theorem SourceInputs.toInputs (h : SourceInputs M₀ T_H U₁ U₂ x) :
    Inputs M₀ T_H U₁ U₂ x where
  index_two := h.index_two
  x_mem := h.x_mem
  distinct := h.distinct
  invariant := h.invariant
  pair_zero := h.pair_zero
  pair_one := h.pair_one
  exchange := h.exchange
  noncommuting := h.noncommuting
  original_commuting := h.original_commuting
  cross_commuting := h.cross_commuting


/-- C.5.6(7)'s complete four-module permutation and cross-commutation step,
from the original source pair action and commutator facts. -/
theorem SourceInputs.conclusion (h : SourceInputs M₀ T_H U₁ U₂ x) :
    IsKleinFour (action h.toInputs).range ∧
    IsKleinFour (M₀ ⧸ (action h.toInputs).ker) ∧
    Function.Bijective (fun p : (action h.toInputs).range =>
      (p : Equiv.Perm (Fin 4)) 0) ∧
    Nat.card ((T_H.subgroupOf M₀).map (action h.toInputs)) = 2 ∧
    (∀ i : Fin 4, (modules U₁ U₂ x i).conjBy (x^2) = modules U₁ U₂ x i) ∧
    ⁅U₁ ⊔ U₁.conjBy x⁻¹, U₂ ⊔ U₂.conjBy x⁻¹⁆ = ⊥ :=
  ⟨image_isKleinFour h.toInputs, quotient_isKleinFour h.toInputs,
    image_regular h.toInputs, pair_image_card h.toInputs,
    x_square_fixes_modules h.toInputs, conjugate_factors_commute h.toInputs⟩

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.FourModuleOrbit

end
