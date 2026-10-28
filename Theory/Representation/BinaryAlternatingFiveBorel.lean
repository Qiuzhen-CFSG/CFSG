module

public import Theory.Representation.BinaryPermutationNaturalStructure
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Theory.PGroupCore

/-!
# The Borel module in the binary A₅ permutation core

Let B be the stabilizer of 4 in the actual alternating group on Fin 5.
Its commutator on the augmentation core is the three-space consisting of
vectors vanishing at 4. The explicit A₄ marking and extension by zero identify
this module with the four-point augmentation core. Its fixed line is generated
by (1,1,1,1,0), and its quotient is the actual natural four-point section.
The quotient action has Klein four kernel, equal to O₂(B), and a faithful
cyclic-three quotient actor.

A three-cycle extracts a weight-two vector from any nonconstant vector;
double transitivity then spans the core. Thus an invariant proper subspace
has dimension at most one. This proves indecomposability and excludes an
invariant plane, including after transport along a surjective actor map.
The weight-two argument is adapted from BinaryPermutationNaturalStructure,
whose public theorem is stated only in degree at least five. The small
kernel certificate checks 24 permutations and 16 binary vectors.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
1 March 2004 manuscript, proof of Lemma 13.6.15, printed p.930;
binary permutation conventions are those of §B.3, printed p.83.
-/

public section

open Equiv Module Representation
namespace BinaryPermutation.AlternatingFiveBorel

/-- The actual point stabilizer at the fifth coordinate. -/
abbrev B : Subgroup (alternatingGroup (Fin 5)) :=
  MulAction.stabilizer (alternatingGroup (Fin 5)) (4 : Fin 5)

private def firstFour : Fin 4 ≃ {i : Fin 5 // i ≠ 4} where
  toFun i := ⟨i.castSucc, by exact Fin.castSucc_ne_last i⟩
  invFun i := ⟨i.val.val, by
    have hn : i.val.val ≠ 4 := fun h => i.property (Fin.ext h)
    have := i.val.isLt
    omega⟩
  left_inv _ := by exact rfl
  right_inv _ := by exact rfl

private def liftPerm : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 5) :=
  Equiv.Perm.extendDomainHom firstFour

private theorem liftPerm_cast (g : Equiv.Perm (Fin 4)) (i : Fin 4) :
    liftPerm g i.castSucc = (g i).castSucc :=
  Equiv.Perm.extendDomain_apply_image g firstFour i

private theorem liftPerm_last (g : Equiv.Perm (Fin 4)) : liftPerm g 4 = 4 :=
  Equiv.Perm.extendDomain_apply_not_subtype g firstFour (by simp)

private theorem liftPerm_sign (g : Equiv.Perm (Fin 4)) : (liftPerm g).sign = g.sign :=
  Equiv.Perm.sign_extendDomain g firstFour

/-- Extend a four-letter even permutation by fixing the fifth letter. -/
def inclusion : alternatingGroup (Fin 4) →* B where
  toFun g := ⟨⟨liftPerm g.val, by
    rw [Equiv.Perm.mem_alternatingGroup, liftPerm_sign]
    exact g.property⟩, liftPerm_last g.val⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact liftPerm.map_one
  map_mul' g h := by apply Subtype.ext; apply Subtype.ext; exact liftPerm.map_mul _ _

@[simp] theorem inclusion_cast (g : alternatingGroup (Fin 4)) (i : Fin 4) :
    (inclusion g).val.val i.castSucc = (g.val i).castSucc := liftPerm_cast _ _

private theorem lift_surjective (g : B) : ∃ h, liftPerm h = g.val.val := by
  have hfix : g.val.val 4 = 4 := g.property
  have hp : ∀ i : Fin 5, g.val.val i ≠ 4 ↔ i ≠ 4 := by
    intro i; rw [← hfix, g.val.val.injective.ne_iff, hfix]
  let h := firstFour.symm.permCongr (g.val.val.subtypePerm hp)
  refine ⟨h, ?_⟩
  apply Equiv.ext; intro i
  induction i using Fin.lastCases with
  | last => exact (liftPerm_last _).trans hfix.symm
  | cast i =>
    rw [liftPerm_cast]
    exact congrArg Subtype.val (firstFour.apply_symm_apply ((g.val.val.subtypePerm hp) (firstFour i)))

/-- The marking of the full Borel by A₄. -/
noncomputable def marking : alternatingGroup (Fin 4) ≃* B :=
  MulEquiv.ofBijective inclusion ⟨by
    intro g h he
    apply Subtype.ext
    apply Equiv.Perm.extendDomainHom_injective firstFour
    exact congrArg (fun b : B => b.val.val) he, by
    intro g
    obtain ⟨h, he⟩ := lift_surjective g
    have hh : h ∈ alternatingGroup (Fin 4) := by
      rw [Equiv.Perm.mem_alternatingGroup, ← liftPerm_sign, he]
      exact g.val.property
    exact ⟨⟨h, hh⟩, Subtype.ext (Subtype.ext he)⟩⟩

abbrev I := core (Fin 5)
abbrev action : Representation (ZMod 2) B I :=
  (alternatingCoreRepresentation (Fin 5)).comp B.subtype

/-- The coordinate description of the commutator, proved in `commutator_eq_moved`. -/
def moved : Submodule (ZMod 2) I :=
  LinearMap.ker ((LinearMap.proj (4 : Fin 5)).comp (core (Fin 5)).subtype)

@[simp] theorem mem_moved (v : I) : v ∈ moved ↔ v.val 4 = 0 := Iff.rfl

private def extend (v : Full (Fin 4)) : Full (Fin 5) := ![v 0, v 1, v 2, v 3, 0]

private theorem extend_cast (v : Full (Fin 4)) (i : Fin 4) : extend v i.castSucc = v i := by
  fin_cases i <;> rfl

private theorem extend_last (v : Full (Fin 4)) : extend v 4 = 0 := by exact rfl

/-- Extend the four-point augmentation core by a zero fifth coordinate. -/
def coreEquivMoved : core (Fin 4) ≃ₗ[ZMod 2] moved where
  toFun v := ⟨⟨extend v.val, by
    change (∑ i : Fin 5, extend v.val i) = 0
    rw [Fin.sum_univ_castSucc]
    simpa only [extend_cast, show (Fin.last 4 : Fin 5) = 4 from rfl, extend_last, add_zero, mem_core] using v.property⟩, by rfl⟩
  invFun v := ⟨fun i => v.val.val i.castSucc, by
    have h := v.val.property
    change (∑ i : Fin 5, v.val.val i) = 0 at h
    rw [Fin.sum_univ_castSucc, show (Fin.last 4 : Fin 5) = 4 from rfl, (mem_moved _).mp v.property, add_zero] at h
    exact h⟩
  left_inv v := by ext i; exact extend_cast _ i
  right_inv v := by
    apply Subtype.ext; apply Subtype.ext; funext i
    induction i using Fin.lastCases with
    | last => simpa only [show (Fin.last 4 : Fin 5) = 4 from rfl, extend_last] using ((mem_moved _).mp v.property).symm
    | cast i => exact extend_cast _ i
  map_add' v w := by
    apply Subtype.ext; apply Subtype.ext; funext i
    fin_cases i <;> rfl
  map_smul' c v := by
    apply Subtype.ext; apply Subtype.ext; funext i
    fin_cases i <;> rfl

theorem finrank_moved : finrank (ZMod 2) moved = 3 := by
  rw [← coreEquivMoved.finrank_eq, finrank_core]
  rfl

theorem moved_stable (g : B) (v : I) (hv : v ∈ moved) : action g v ∈ moved := by
  change v.val (g.val.val.symm 4) = 0
  have h : g.val.val.symm 4 = 4 := g.val.val.symm_apply_eq.mpr g.property.symm
  rw [h]; exact hv

/-- Restriction of the original five-point action to its moved three-space. -/
def movedRepresentation : Representation (ZMod 2) B moved where
  toFun g := (action g).restrict (moved_stable g)
  map_one' := by ext v i; rfl
  map_mul' g h := by ext v i; rfl

theorem coreEquivMoved_equivariant (g : alternatingGroup (Fin 4)) (v : core (Fin 4)) :
    coreEquivMoved (alternatingCoreRepresentation (Fin 4) g v) =
      movedRepresentation (marking g) (coreEquivMoved v) := by
  apply Subtype.ext; apply Subtype.ext; funext i
  induction i using Fin.lastCases with
  | last =>
    change extend (alternatingCoreRepresentation (Fin 4) g v).val 4 = extend v.val ((liftPerm g.val).symm 4)
    rw [show (liftPerm g.val).symm = liftPerm g.val.symm from (map_inv liftPerm g.val).symm]
    rw [liftPerm_last]
    rfl
  | cast i =>
    change extend (alternatingCoreRepresentation (Fin 4) g v).val i.castSucc = extend v.val ((liftPerm g.val).symm i.castSucc)
    rw [show (liftPerm g.val).symm = liftPerm g.val.symm from (map_inv liftPerm g.val).symm]
    rw [liftPerm_cast]
    simp only [extend_cast]; rfl


section FourStructure
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
private lemma binary_add (x y : ZMod 2) (h : x ≠ y) : x + y = 1 := by
  revert x y; decide

private lemma binary_cases (x y z : ZMod 2) (h : x ≠ y) : z = x ∨ z = y := by
  revert x y z; decide

private lemma cycle_pair (W : Submodule (ZMod 2) (Full Ω))
    (hW : ∀ g : alternatingGroup Ω, ∀ v ∈ W, representation Ω g.val v ∈ W)
    {v : Full Ω} (hv : v ∈ W) {a b c : Ω}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hvab : v a ≠ v b) (hvbc : v b = v c) :
    Pi.single a (1 : ZMod 2) + Pi.single b 1 ∈ W := by
  let g : alternatingGroup Ω := ⟨swap a b * swap b c, by
    simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap hbc]⟩
  have heq : v + representation Ω g.val v = Pi.single a 1 + Pi.single b 1 := by
    ext i
    by_cases hi : i = a
    · subst i
      simp [g, Equiv.Perm.mul_def, hab, ← hvbc, binary_add _ _ hvab]
    by_cases hj : i = b
    · subst i
      simp [g, Equiv.Perm.mul_def, swap_apply_of_ne_of_ne hab hac,
        hab.symm, binary_add _ _ hvab.symm]
    by_cases hk : i = c
    · subst i
      simp [g, Equiv.Perm.mul_def, swap_apply_of_ne_of_ne hac.symm hbc.symm,
        hac.symm, hbc.symm, ← hvbc, CharTwo.add_self_eq_zero]
    · simp [g, Equiv.Perm.mul_def, swap_apply_of_ne_of_ne hi hj,
        swap_apply_of_ne_of_ne hj hk, hi, hj, CharTwo.add_self_eq_zero]
  rw [← heq]
  exact W.add_mem hv (hW g v hv)

private lemma pair_of_nonconstant (hn : 3 ≤ Fintype.card Ω)
    (W : Submodule (ZMod 2) (Full Ω))
    (hW : ∀ g : alternatingGroup Ω, ∀ v ∈ W, representation Ω g.val v ∈ W)
    {v : Full Ω} (hv : v ∈ W) {a b : Ω} (hab : v a ≠ v b) :
    Pi.single a (1 : ZMod 2) + Pi.single b 1 ∈ W := by
  have hab' : a ≠ b := fun h => hab (congrArg v h)
  have hc : ({a,b} : Finset Ω).card < (Finset.univ : Finset Ω).card := by
    have := Finset.card_le_two (a := a) (b := b)
    simpa only [Finset.card_univ] using (lt_of_le_of_lt this (by omega))
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  rcases binary_cases (v a) (v b) (v c) hab with heq | heq
  · simpa [add_comm] using cycle_pair W hW hv hab'.symm (Ne.symm hc.1) (Ne.symm hc.2)
      hab.symm heq.symm
  · exact cycle_pair W hW hv hab' (Ne.symm hc.2) (Ne.symm hc.1) hab heq.symm

omit [Fintype Ω] in
private lemma permute_single (g : Equiv.Perm Ω) (a : Ω) :
    representation Ω g (Pi.single a (1 : ZMod 2)) = Pi.single (g a) 1 := by
  ext i
  simp [Pi.single_apply, Equiv.symm_apply_eq]

private lemma all_pairs (hn : 4 ≤ Fintype.card Ω)
    (W : Submodule (ZMod 2) (Full Ω))
    (hW : ∀ g : alternatingGroup Ω, ∀ v ∈ W, representation Ω g.val v ∈ W)
    {a b : Ω} (hab : a ≠ b)
    (hp : Pi.single a (1 : ZMod 2) + Pi.single b 1 ∈ W) (i j : Ω) :
    Pi.single i (1 : ZMod 2) + Pi.single j 1 ∈ W := by
  by_cases hij : i = j
  · subst j
    convert W.zero_mem using 1
    ext k
    exact CharTwo.add_self_eq_zero _
  have := alternatingGroup.isMultiplyPretransitive Ω
  have ht : MulAction.IsMultiplyPretransitive (alternatingGroup Ω) Ω 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card Ω - 2)
      (by simpa only [Nat.card_eq_fintype_card] using (show 2 ≤ Fintype.card Ω - 2 by omega))
      (Nat.sub_le _ _)
  obtain ⟨g, ha, hb⟩ := (MulAction.is_two_pretransitive_iff.mp ht) hab hij
  have hg := hW g _ hp
  rw [map_add, permute_single, permute_single] at hg
  exact (show g.val a = i from ha) ▸ (show g.val b = j from hb) ▸ hg

private lemma core_le_of_pairs (W : Submodule (ZMod 2) (Full Ω)) (a : Ω)
    (hp : ∀ i j, Pi.single i (1 : ZMod 2) + Pi.single j 1 ∈ W) : core Ω ≤ W := by
  intro v hv
  have heq : (∑ i, v i • (Pi.single i (1 : ZMod 2) + Pi.single a 1)) = v := by
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
    have hsum : ∑ i, v i = 0 := hv
    rw [hsum, zero_smul, add_zero]
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using Finset.univ_sum_single v
  rw [← heq]
  exact W.sum_mem fun i _ => W.smul_mem _ (hp i a)

-- The weight-two proof needs degree four here.
private theorem invariant_le_constants_or_core_le_four (hn : 4 ≤ Fintype.card Ω)
    (W : Submodule (ZMod 2) (Full Ω))
    (hW : ∀ g : alternatingGroup Ω, ∀ v ∈ W, representation Ω g.val v ∈ W) :
    W ≤ constants Ω ∨ core Ω ≤ W := by
  classical
  by_cases h : ∀ v ∈ W, ∀ a b, v a = v b
  · left
    intro v hv
    have : Nonempty Ω := Fintype.card_pos_iff.mp (by omega)
    let a : Ω := Classical.choice inferInstance
    apply Submodule.mem_span_singleton.mpr
    exact ⟨v a, funext fun i => by simpa [allOne] using h v hv a i⟩
  · push Not at h
    obtain ⟨v, hv, a, b, hab⟩ := h
    right
    apply core_le_of_pairs W a
    exact all_pairs (by omega) W hW (fun h => hab (congrArg v h))
      (pair_of_nonconstant (by omega) W hW hv hab)


end FourStructure

private theorem core_four_submodule_dichotomy (P : Submodule (ZMod 2) (core (Fin 4)))
    (hP : ∀ g : alternatingGroup (Fin 4), ∀ v ∈ P,
      alternatingCoreRepresentation (Fin 4) g v ∈ P) :
    finrank (ZMod 2) P ≤ 1 ∨ P = ⊤ := by
  let W := P.map (core (Fin 4)).subtype
  have hW : ∀ g : alternatingGroup (Fin 4), ∀ v ∈ W,
      representation (Fin 4) g.val v ∈ W := by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨alternatingCoreRepresentation (Fin 4) g v, hP g v hv, rfl⟩
  rcases invariant_le_constants_or_core_le_four (by decide : 4 ≤ Fintype.card (Fin 4)) W hW with h | h
  · left
    have hd := Submodule.finrank_mono h
    rw [finrank_constants] at hd
    simpa only [W, Submodule.finrank_map_subtype_eq] using hd
  · right
    apply top_unique
    intro v _
    obtain ⟨w, hw, he⟩ := h v.property
    exact (show w = v from Subtype.ext he) ▸ hw

/-- Every proper invariant subspace of the moved module has dimension at most one. -/
theorem moved_submodule_dichotomy (P : Submodule (ZMod 2) moved)
    (hP : ∀ g : B, ∀ v ∈ P, movedRepresentation g v ∈ P) :
    finrank (ZMod 2) P ≤ 1 ∨ P = ⊤ := by
  let Q := P.comap coreEquivMoved.toLinearMap
  have hQ : ∀ g : alternatingGroup (Fin 4), ∀ v ∈ Q,
      alternatingCoreRepresentation (Fin 4) g v ∈ Q := by
    intro g v hv
    change coreEquivMoved (alternatingCoreRepresentation (Fin 4) g v) ∈ P
    rw [coreEquivMoved_equivariant]
    exact hP (marking g) _ hv
  rcases core_four_submodule_dichotomy Q hQ with h | h
  · left
    have he := (coreEquivMoved.ofSubmodule' P).finrank_eq
    exact he ▸ h
  · right
    apply top_unique
    intro v _
    obtain ⟨w, rfl⟩ := coreEquivMoved.surjective v
    exact show w ∈ Q from h ▸ Submodule.mem_top

/-- The full Borel has no invariant plane in its moved module. -/
theorem no_invariant_plane (P : Submodule (ZMod 2) moved)
    (hP : ∀ g : B, ∀ v ∈ P, movedRepresentation g v ∈ P) :
    finrank (ZMod 2) P ≠ 2 := by
  rcases moved_submodule_dichotomy P hP with h | rfl
  · omega
  · rw [finrank_top, finrank_moved]; decide


private def cycle012 : alternatingGroup (Fin 4) :=
  ⟨swap 0 1 * swap 1 2, by simp [Perm.mem_alternatingGroup]⟩

private def cycle013 : alternatingGroup (Fin 4) :=
  ⟨swap 0 1 * swap 1 3, by simp [Perm.mem_alternatingGroup]⟩

@[simp] theorem action_marking_cast (g : alternatingGroup (Fin 4)) (v : I) (i : Fin 4) :
    (action (marking g) v).val i.castSucc = v.val (g.val.symm i).castSucc := by
  change v.val ((liftPerm g.val).symm i.castSucc) = _
  rw [show (liftPerm g.val).symm = liftPerm g.val.symm from (map_inv liftPerm g.val).symm,
    liftPerm_cast]

@[simp] theorem action_last (g : B) (v : I) : (action g v).val 4 = v.val 4 := by
  change v.val (g.val.val.symm 4) = _
  rw [g.val.val.symm_apply_eq.mpr g.property.symm]

/-- The vector spanning the Borel fixed line, in the five original coordinates. -/
def fixedVector : I := ⟨![1, 1, 1, 1, 0], by rw [mem_core]; decide⟩

@[simp] theorem fixedVector_cast (i : Fin 4) : fixedVector.val i.castSucc = 1 := by
  fin_cases i <;> rfl

theorem fixedVector_fixed (g : B) : action g fixedVector = fixedVector := by
  obtain ⟨a, rfl⟩ := marking.surjective g
  apply Subtype.ext; funext i
  induction i using Fin.lastCases with
  | last => exact action_last _ _
  | cast i => rw [action_marking_cast, fixedVector_cast, fixedVector_cast]

theorem fixedVector_ne_zero : fixedVector ≠ 0 := by
  intro h
  exact one_ne_zero (congrArg (fun v : I => v.val 0) h)

theorem fixed_eq_line : action.invariants = Submodule.span (ZMod 2) {fixedVector} := by
  apply le_antisymm
  · intro v hv
    have h01 := congrArg (fun w : I => w.val (1 : Fin 4).castSucc) (hv (marking cycle012))
    have h12 := congrArg (fun w : I => w.val (2 : Fin 4).castSucc) (hv (marking cycle012))
    have h03 := congrArg (fun w : I => w.val (3 : Fin 4).castSucc) (hv (marking cycle013))
    rw [action_marking_cast] at h01 h12 h03
    change v.val 0 = v.val 1 at h01
    change v.val 1 = v.val 2 at h12
    change v.val 1 = v.val 3 at h03
    have h4 : v.val 4 = 0 := by
      have h := v.property
      simp only [mem_core, Fin.sum_univ_succ] at h
      simpa [← h03, ← h12, ← h01, ← add_assoc, CharTwo.add_self_eq_zero] using h
    apply Submodule.mem_span_singleton.mpr
    refine ⟨v.val 0, ?_⟩
    apply Subtype.ext; funext i
    fin_cases i <;> simp [fixedVector, ← h03, ← h12, ← h01, h4, smul_eq_mul]
  · apply Submodule.span_le.mpr
    intro v hv
    obtain rfl : v = fixedVector := hv
    exact fixedVector_fixed

theorem fixed_le_moved : action.invariants ≤ moved := by
  rw [fixed_eq_line, Submodule.span_le, Set.singleton_subset_iff]
  rfl

theorem finrank_fixed : finrank (ZMod 2) action.invariants = 1 := by
  rw [fixed_eq_line]
  exact finrank_span_singleton fixedVector_ne_zero

private theorem commutator_stable (g : B) {v : I} (hv : v ∈ Coinvariants.ker action) :
    action g v ∈ Coinvariants.ker action := by
  have hle : Coinvariants.ker action ≤ (Coinvariants.ker action).comap (action g) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨h, w⟩, rfl⟩
    change action g (action h w - w) ∈ Coinvariants.ker action
    have he : action g (action h w - w) =
        (action (g * h) w - w) - (action g w - w) := by
      rw [map_sub, map_mul, Module.End.mul_apply]; abel
    rw [he]
    exact (Coinvariants.ker action).sub_mem (Coinvariants.sub_mem_ker _ _)
      (Coinvariants.sub_mem_ker _ _)
  exact hle hv

/-- The commutator is exactly the augmentation-zero vectors vanishing at 4. -/
theorem commutator_eq_moved : Coinvariants.ker action = moved := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    change (action g v).val 4 - v.val 4 = 0
    rw [action_last, sub_self]
  · let Q := (Coinvariants.ker action).comap
        (moved.subtype.comp coreEquivMoved.toLinearMap)
    let W := Q.map (core (Fin 4)).subtype
    have hQ : ∀ g : alternatingGroup (Fin 4), ∀ v ∈ Q,
        alternatingCoreRepresentation (Fin 4) g v ∈ Q := by
      intro g v hv
      change (coreEquivMoved (alternatingCoreRepresentation (Fin 4) g v)).val ∈ Coinvariants.ker action
      rw [coreEquivMoved_equivariant]
      exact commutator_stable (marking g) hv
    have hW : ∀ g : alternatingGroup (Fin 4), ∀ v ∈ W,
        representation (Fin 4) g.val v ∈ W := by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨alternatingCoreRepresentation (Fin 4) g v, hQ g v hv, rfl⟩
    have hn : ¬ W ≤ constants (Fin 4) := by
      let v : I := ⟨![1, 0, 0, 0, 1], by rw [mem_core]; decide⟩
      let w : core (Fin 4) := ⟨![1, 1, 0, 0], by rw [mem_core]; decide⟩
      have he : action (marking cycle012) v - v = (coreEquivMoved w).val := by
        apply Subtype.ext; funext i
        fin_cases i <;> decide
      have hw : w ∈ Q := by
        change (coreEquivMoved w).val ∈ Coinvariants.ker action
        rw [← he]
        exact Coinvariants.sub_mem_ker (marking cycle012) v
      intro h
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (h ⟨w, hw, rfl⟩)
      have h0 := congrFun hc 0
      have h2 := congrFun hc 2
      change c * 1 = 1 at h0
      change c * 1 = 0 at h2
      exact one_ne_zero (h0.symm.trans h2)
    have hc : core (Fin 4) ≤ W :=
      (invariant_le_constants_or_core_le_four (by decide : 4 ≤ Fintype.card (Fin 4)) W hW).resolve_left hn
    intro v hv
    obtain ⟨w, he⟩ := coreEquivMoved.surjective ⟨v, hv⟩
    obtain ⟨u, hu, hue⟩ := hc w.property
    have huw : u = w := Subtype.ext hue
    subst u
    change (coreEquivMoved w).val ∈ Coinvariants.ker action at hu
    simpa only [he] using hu


/-- Indecomposability as the absence of a nontrivial invariant direct sum. -/
theorem indecomposable (P Q : Submodule (ZMod 2) moved)
    (hP : ∀ g : B, ∀ v ∈ P, movedRepresentation g v ∈ P)
    (hQ : ∀ g : B, ∀ v ∈ Q, movedRepresentation g v ∈ Q)
    (h : IsCompl P Q) : P = ⊥ ∨ Q = ⊥ := by
  rcases moved_submodule_dichotomy P hP with hp | rfl
  · rcases moved_submodule_dichotomy Q hQ with hq | rfl
    · have hd := Submodule.finrank_add_le_finrank_add_finrank P Q
      rw [h.sup_eq_top, finrank_top, finrank_moved] at hd
      omega
    · exact Or.inl (by simpa using h.inf_eq_bot)
  · exact Or.inr (by simpa using h.inf_eq_bot)

/-- Surjective actor transport: this is the input used with D = L_v and
W = [W_K,L_v] in the proof of 13.6.15. -/
theorem no_invariant_plane_of_surjective
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (q : D →* B) (hq : Function.Surjective q)
    (e : W ≃ₗ[ZMod 2] moved)
    (he : ∀ d w, e (ρ d w) = movedRepresentation (q d) (e w))
    (P : Submodule (ZMod 2) W) (hP : ∀ d w, w ∈ P → ρ d w ∈ P) :
    finrank (ZMod 2) P ≠ 2 := by
  have h := no_invariant_plane (P.map e.toLinearMap) (by
    intro b v hv
    obtain ⟨d, rfl⟩ := hq b
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨ρ d w, hP d w hw, he d w⟩)
  rwa [e.finrank_map_eq] at h

/-- The fixed line considered as a submodule of the commutator. -/
noncomputable def fixedInMoved : Submodule (ZMod 2) moved := action.invariants.comap moved.subtype

/-- Projection onto the actual four-point natural section, using the same marking. -/
def projection : moved →ₗ[ZMod 2] natural (Fin 4) :=
  (coreToNatural (Fin 4)).comp coreEquivMoved.symm.toLinearMap

theorem projection_surjective : Function.Surjective projection :=
  coreToNatural_surjective.comp coreEquivMoved.symm.surjective

theorem projection_equivariant (g : alternatingGroup (Fin 4)) (v : moved) :
    projection (movedRepresentation (marking g) v) =
      alternatingNaturalRepresentation (Fin 4) g (projection v) := by
  obtain ⟨u, rfl⟩ := coreEquivMoved.surjective v
  rw [← coreEquivMoved_equivariant]
  change coreToNatural (Fin 4) (coreEquivMoved.symm (coreEquivMoved _)) =
    alternatingNaturalRepresentation (Fin 4) g
      (coreToNatural (Fin 4) (coreEquivMoved.symm (coreEquivMoved _)))
  simp only [LinearEquiv.symm_apply_apply]
  exact coreToNatural_equivariant g.val u

private def fourOne : core (Fin 4) := ⟨allOne (Fin 4), by rw [mem_core]; decide⟩

private theorem coreEquivMoved_fourOne : (coreEquivMoved fourOne).val = fixedVector := by exact rfl

theorem projection_ker : projection.ker = fixedInMoved := by
  ext v
  obtain ⟨u, rfl⟩ := coreEquivMoved.surjective v
  change coreToNatural (Fin 4) (coreEquivMoved.symm (coreEquivMoved u)) = 0 ↔
    (coreEquivMoved u).val ∈ action.invariants
  rw [LinearEquiv.symm_apply_apply, fixed_eq_line]
  have hz : coreToNatural (Fin 4) u = 0 ↔ u.val ∈ constants (Fin 4) := by
    constructor
    · intro h
      exact (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr h)
  rw [hz]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    have hu : u = c • fourOne := Subtype.ext hc.symm
    rw [hu, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [coreEquivMoved_fourOne]))
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    funext i
    have hi := congrArg (fun v : I => v.val i.castSucc) hc
    change c * fixedVector.val i.castSucc = extend u.val i.castSucc at hi
    simpa only [fixedVector_cast, extend_cast, Pi.smul_apply, allOne, smul_eq_mul] using hi

/-- The quotient is exactly the natural four-point section, not merely a plane
of the same dimension. -/
noncomputable def quotientEquivNatural : (moved ⧸ fixedInMoved) ≃ₗ[ZMod 2] natural (Fin 4) :=
  (Submodule.quotEquivOfEq _ _ projection_ker.symm).trans
      (projection.quotKerEquivOfSurjective projection_surjective)

@[simp] theorem quotientEquivNatural_mk (v : moved) :
    quotientEquivNatural (fixedInMoved.mkQ v) = projection v := by exact rfl

theorem finrank_natural_section : finrank (ZMod 2) (natural (Fin 4)) = 2 := by
  rw [finrank_natural_even (Fin 4) (by decide)]
  rfl

-- A small certificate: only 24 permutations and 16 binary vectors are tested.
private theorem kernel_test : ∀ g : Equiv.Perm (Fin 4), g.sign = 1 →
    ((∀ v : Fin 4 → ZMod 2, (∑ i, v i) = 0 →
      ∀ i, v (g.symm i) - v i = v (g.symm 0) - v 0) ↔ g ^ 2 = 1) := by
  decide +kernel


/-- The four-point natural action has exactly the Klein four kernel. -/
theorem natural_kernel : (alternatingNaturalRepresentation (Fin 4)).asGroupHom.ker =
    alternatingGroup.kleinFour (Fin 4) := by
  ext g
  have hact : g ∈ (alternatingNaturalRepresentation (Fin 4)).asGroupHom.ker ↔
      ∀ v : Fin 4 → ZMod 2, (∑ i, v i) = 0 →
        ∀ i, v (g.val.symm i) - v i = v (g.val.symm 0) - v 0 := by
    constructor
    · intro h v hv i
      have he := congrArg (fun f : Units (Module.End (ZMod 2) (natural (Fin 4))) =>
        (f : Module.End (ZMod 2) (natural (Fin 4))) (coreToNatural (Fin 4) ⟨v, hv⟩)) h
      have hd : representation (Fin 4) g.val v - v ∈ constants (Fin 4) :=
        (Submodule.Quotient.eq _).mp (congrArg Subtype.val he)
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hd
      exact (congrFun hc i).symm.trans (congrFun hc 0)
    · intro h
      apply Units.ext
      apply LinearMap.ext
      intro w
      obtain ⟨v, rfl⟩ := coreToNatural_surjective w
      apply Subtype.ext
      apply (Submodule.Quotient.eq _).mpr
      apply Submodule.mem_span_singleton.mpr
      refine ⟨v.val (g.val.symm 0) - v.val 0, ?_⟩
      funext i
      change (v.val (g.val.symm 0) - v.val 0) * 1 = v.val (g.val.symm i) - v.val i
      rw [mul_one]
      exact (h v.val v.property i).symm
  rw [hact, kernel_test g.val g.property]
  constructor
  · intro hg
    have ho : orderOf g.val ∣ 2 ^ 1 := by
      simpa using orderOf_dvd_of_pow_eq_one hg
    rcases alternatingGroup.mem_kleinFour_of_order_two_pow (by simp : Nat.card (Fin 4) = 4)
      g.property ho with h | h
    · have he : g = 1 := Subtype.ext (Perm.cycleType_eq_zero.mp h)
      rw [he]; exact Subgroup.one_mem _
    · exact Subgroup.subset_closure h
  · intro hg
    have he := Subgroup.pow_exponent_eq_one hg
    rw [alternatingGroup.exponent_kleinFour_of_card_eq_four (by simp : Nat.card (Fin 4) = 4)] at he
    exact congrArg Subtype.val he

/-- The quotient action on M/C_I(B). -/
noncomputable def quotientRepresentation : Representation (ZMod 2) B (moved ⧸ fixedInMoved) :=
  movedRepresentation.quotient fixedInMoved (by
    intro g v hv
    change action g v.val ∈ action.invariants
    have he : action g v.val = v.val := hv g
    rw [he]
    exact hv)

/-- Equivariance on the actual quotient maps and the fixed first-four marking. -/
theorem quotientEquivNatural_equivariant (g : alternatingGroup (Fin 4))
    (v : moved ⧸ fixedInMoved) :
    quotientEquivNatural (quotientRepresentation (marking g) v) =
      alternatingNaturalRepresentation (Fin 4) g (quotientEquivNatural v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change quotientEquivNatural (fixedInMoved.mkQ (movedRepresentation (marking g) v)) = _
    exact projection_equivariant g v

/-- The normal four-group in B, with the same marking as its module. -/
noncomputable def sectionKernel : Subgroup B :=
  (alternatingGroup.kleinFour (Fin 4)).comap marking.symm.toMonoidHom

instance sectionKernel_normal : sectionKernel.Normal := by
  exact (alternatingGroup.normal_kleinFour (by simp : Nat.card (Fin 4) = 4)).comap
    marking.symm.toMonoidHom

theorem quotient_action_kernel : quotientRepresentation.asGroupHom.ker = sectionKernel := by
  ext b
  obtain ⟨g, rfl⟩ := marking.surjective b
  change quotientRepresentation.asGroupHom (marking g) = 1 ↔
    marking.symm (marking g) ∈ alternatingGroup.kleinFour (Fin 4)
  rw [MulEquiv.symm_apply_apply, ← natural_kernel]
  constructor
  · intro h
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := quotientEquivNatural.surjective v
    change alternatingNaturalRepresentation (Fin 4) g (quotientEquivNatural w) = quotientEquivNatural w
    rw [← quotientEquivNatural_equivariant]
    have hw := congrArg (fun f : Units (Module.End (ZMod 2) (moved ⧸ fixedInMoved)) =>
      (f : Module.End (ZMod 2) (moved ⧸ fixedInMoved)) w) h
    exact congrArg quotientEquivNatural hw
  · intro h
    apply Units.ext
    apply LinearMap.ext
    intro w
    apply quotientEquivNatural.injective
    change quotientEquivNatural (quotientRepresentation (marking g) w) = quotientEquivNatural w
    rw [quotientEquivNatural_equivariant]
    exact congrArg (fun f : Units (Module.End (ZMod 2) (natural (Fin 4))) =>
      (f : Module.End (ZMod 2) (natural (Fin 4))) (quotientEquivNatural w)) h


/-- The kernel has four elements. -/
theorem card_sectionKernel : Nat.card sectionKernel = 4 := by
  have he : (alternatingGroup.kleinFour (Fin 4)).map marking.toMonoidHom = sectionKernel :=
    Subgroup.map_equiv_eq_comap_symm' _ _
  rw [← he]
  exact (Nat.card_congr (marking.subgroupMap (alternatingGroup.kleinFour (Fin 4))).toEquiv.symm).trans
    (alternatingGroup.kleinFour_card_of_card_eq_four (by simp))

/-- The faithful quotient actor has order three. -/
theorem card_quotient_actor : Nat.card (B ⧸ sectionKernel) = 3 := by
  have hb : Nat.card B = 12 :=
    (Nat.card_congr marking.toEquiv.symm).trans
      (alternatingGroup.card_of_card_eq_four (by simp))
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup sectionKernel
  rw [hb, card_sectionKernel] at h
  omega

instance quotient_actor_isCyclic : IsCyclic (B ⧸ sectionKernel) :=
  isCyclic_of_prime_card card_quotient_actor

instance quotient_trivial_on_kernel :
    Representation.IsTrivial (quotientRepresentation.comp sectionKernel.subtype) where
  out g := by
    have h : quotientRepresentation.asGroupHom g.val = 1 := by
      change g.val ∈ quotientRepresentation.asGroupHom.ker
      rw [quotient_action_kernel]
      exact g.property
    exact congrArg (fun f : Units (Module.End (ZMod 2) (moved ⧸ fixedInMoved)) =>
      (f : Module.End (ZMod 2) (moved ⧸ fixedInMoved))) h

/-- The action factors through the actual cyclic-three quotient B/ker. -/
noncomputable def cubicRepresentation :
    Representation (ZMod 2) (B ⧸ sectionKernel) (moved ⧸ fixedInMoved) :=
  quotientRepresentation.ofQuotient sectionKernel

@[simp] theorem cubicRepresentation_mk (g : B) (v : moved ⧸ fixedInMoved) :
    cubicRepresentation (QuotientGroup.mk g) v = quotientRepresentation g v := by exact rfl

theorem cubicRepresentation_faithful : Function.Injective cubicRepresentation.asGroupHom := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H g =>
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [← quotient_action_kernel]
    exact hx


@[simp] theorem marking_cast (g : alternatingGroup (Fin 4)) (i : Fin 4) :
    (marking g).val.val i.castSucc = (g.val i).castSucc := inclusion_cast g i

/-- The line submodule of M is the whole fixed space, of dimension one. -/
theorem finrank_fixedInMoved : finrank (ZMod 2) fixedInMoved = 1 :=
  (Submodule.comapSubtypeEquivOfLe fixed_le_moved).finrank_eq.trans finrank_fixed

theorem fixedInMoved_fixed (g : B) (v : moved) (hv : v ∈ fixedInMoved) :
    movedRepresentation g v = v := Subtype.ext (hv g)

theorem finrank_quotient : finrank (ZMod 2) (moved ⧸ fixedInMoved) = 2 :=
  quotientEquivNatural.finrank_eq.trans finrank_natural_section

/-- The same kernel is the intrinsic two-core of B. -/
theorem sectionKernel_eq_twoCore : sectionKernel = pCore 2 B := by
  have hk : alternatingGroup.kleinFour (Fin 4) = pCore 2 (alternatingGroup (Fin 4)) := by
    obtain ⟨S : Sylow 2 (alternatingGroup (Fin 4))⟩ := Sylow.nonempty (G := alternatingGroup (Fin 4))
    have he := alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four (by simp) S
    apply le_antisymm
    · apply le_sSup
      exact ⟨alternatingGroup.normal_kleinFour (by simp), he ▸ S.isPGroup'⟩
    · rw [← he]
      exact pCore_isPGroup.le_sylow_of_normal S
  rw [sectionKernel, ← Subgroup.map_equiv_eq_comap_symm', hk]
  exact pCore_map_iso 2 marking

/-- The natural four-point section is irreducible for A₄ (hence for its
faithful cyclic-three quotient). -/
theorem natural_irreducible :
    Representation.IsIrreducible (alternatingNaturalRepresentation (Fin 4)) := by
  have hd : 0 < finrank (ZMod 2) (natural (Fin 4)) := by rw [finrank_natural_section]; decide
  have : Nontrivial (natural (Fin 4)) := Module.nontrivial_of_finrank_pos hd
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro P
  let S := P.toSubmodule.comap (coreToNatural (Fin 4))
  let W := S.map (core (Fin 4)).subtype
  have hW : ∀ g : alternatingGroup (Fin 4), ∀ v ∈ W,
      representation (Fin 4) g.val v ∈ W := by
    rintro g _ ⟨u, hu, rfl⟩
    refine ⟨coreRepresentation (Fin 4) g.val u, ?_, rfl⟩
    change coreToNatural (Fin 4) (coreRepresentation (Fin 4) g.val u) ∈ P.toSubmodule
    rw [coreToNatural_equivariant]
    exact P.apply_mem_toSubmodule g hu
  rcases invariant_le_constants_or_core_le_four (by decide : 4 ≤ Fintype.card (Fin 4)) W hW with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨v, rfl⟩ := coreToNatural_surjective x
    have hv : v.val ∈ W := ⟨v, hx, rfl⟩
    have hz : coreToNatural (Fin 4) v = 0 := by
      apply Subtype.ext
      exact (Submodule.Quotient.mk_eq_zero (constants (Fin 4))).mpr (h hv)
    exact hz
  · right
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm le_top
    intro x _
    obtain ⟨v, rfl⟩ := coreToNatural_surjective x
    obtain ⟨u, hu, huv⟩ := h v.property
    exact (show u = v from Subtype.ext huv) ▸ hu

/-- Coordinate specification of extension by zero. -/
@[simp] theorem coreEquivMoved_apply_cast (v : core (Fin 4)) (i : Fin 4) :
    (coreEquivMoved v).val.val i.castSucc = v.val i := extend_cast _ i

@[simp] theorem coreEquivMoved_apply_last (v : core (Fin 4)) :
    (coreEquivMoved v).val.val 4 = 0 := by exact rfl

/-- The inverse simply forgets the fifth coordinate. -/
@[simp] theorem coreEquivMoved_symm_apply (v : moved) (i : Fin 4) :
    (coreEquivMoved.symm v).val i = v.val.val i.castSucc := by exact rfl

/-- The restricted action retains the original five-point coordinates. -/
@[simp] theorem movedRepresentation_apply (g : B) (v : moved) :
    (movedRepresentation g v).val = action g v.val := by exact rfl

/-- The fixed generator in the original coordinate ordering. -/
theorem fixedVector_coordinates : fixedVector.val = ![1, 1, 1, 1, 0] := by exact rfl

end BinaryPermutation.AlternatingFiveBorel
