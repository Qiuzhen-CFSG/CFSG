module
public import Theory.SpecificGroups.SymmetricEight.TranspositionAutomorphisms
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# The eight-point action of automorphisms of A₈

The proved conjugation isomorphism S₈ ≃ Aut(A₈), transported through an
actual equivalence L ≃ A₈, identifies automorphisms with permutations of
the eight points. An involution has one, two, three or four disjoint
transpositions; equal cycle types give actual conjugacy. Inner automorphisms
correspond exactly to even permutations. An odd actor together with Inn(L)
generates the whole automorphism group, and the resulting S₈ equivalence
retains both the inner embedding and the actor's permutation.

For an actor of cycle type 2³1², the two fixed points and the actual generated
overgroup are established here. Its A₄ fixed two-residual is a separate
calculation. These are the action and coverage ingredients for
Aschbacher–Smith, *The Classification of Quasithin Groups*, 16.1.4(9),
printed p.1171; no matrix root/graph labels are inferred from cycle names.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymmetricEight.Involutions
open Equiv Subgroup
abbrev A := alternatingGroup (Fin 8)
abbrev S := Perm (Fin 8)

/-- Conjugation realizes the full automorphism group of A₈ on eight points. -/
noncomputable def permutationAutEquiv : S ≃* MulAut A :=
  MulEquiv.ofBijective (MulAut.conjNormal : S →* MulAut A)
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by decide) (by decide))

theorem permutationAutEquiv_apply (q : S) :
    permutationAutEquiv q = MulAut.conjNormal q := rfl

theorem permutationAutEquiv_inner (q : A) :
    permutationAutEquiv q.val = MulAut.conj q := MulAut.conjNormal_val

theorem permutationAutEquiv_mem_inner (q : S) :
    permutationAutEquiv q ∈ MulAut.innerSubgroup A ↔ q ∈ alternatingGroup (Fin 8) := by
  constructor
  · rintro ⟨a, ha⟩
    have he : permutationAutEquiv a.val = permutationAutEquiv q :=
      (permutationAutEquiv_inner a).trans ha
    exact permutationAutEquiv.injective he ▸ a.property
  · intro hq
    exact ⟨⟨q, hq⟩, (permutationAutEquiv_inner ⟨q, hq⟩).symm⟩

/-- The transposition representative. -/
def onePair : S := swap 0 1
/-- The representative with two disjoint transpositions. -/
def twoPairs : S := swap 0 1 * swap 2 3
/-- The exceptional representative with three transpositions and two fixed points. -/
def threePairs : S := swap 0 1 * swap 2 3 * swap 4 5
/-- The fixed-point-free involution representative. -/
def fourPairs : S := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

theorem onePair_cycleType : onePair.cycleType = {2} := by decide +kernel
theorem twoPairs_cycleType : twoPairs.cycleType = {2, 2} := by decide +kernel
theorem threePairs_cycleType : threePairs.cycleType = {2, 2, 2} := by decide +kernel
theorem fourPairs_cycleType : fourPairs.cycleType = {2, 2, 2, 2} := by decide +kernel

theorem involution_cycleType {q : S} (hq : orderOf q = 2) :
    q.cycleType = {2} ∨ q.cycleType = {2, 2} ∨
      q.cycleType = {2, 2, 2} ∨ q.cycleType = {2, 2, 2, 2} := by
  have hs : q ^ 2 = 1 := hq ▸ pow_orderOf_eq_one q
  have hc := Perm.cycleType_of_pow_prime_eq_one hs
  have hn : q.cycleType.card ≠ 0 := by
    intro hz
    have h : q = 1 := Perm.card_cycleType_eq_zero.mp hz
    simp [h] at hq
  have hb := q.sum_cycleType_le
  rw [hc, Multiset.sum_replicate] at hb
  have hd : q.cycleType.card = 1 ∨ q.cycleType.card = 2 ∨
      q.cycleType.card = 3 ∨ q.cycleType.card = 4 := by
    simp only [Fintype.card_fin, smul_eq_mul] at hb
    omega
  rcases hd with h | h | h | h <;> simp [h] at hc <;> tauto

theorem involution_conjugacy {q : S} (hq : orderOf q = 2) :
    IsConj q onePair ∨ IsConj q twoPairs ∨ IsConj q threePairs ∨ IsConj q fourPairs := by
  simpa only [Perm.isConj_iff_cycleType_eq, onePair_cycleType, twoPairs_cycleType,
    threePairs_cycleType, fourPairs_cycleType] using involution_cycleType hq

theorem alternating_sup_zpowers_eq_top {q : S} (hq : q ∉ alternatingGroup (Fin 8)) :
    alternatingGroup (Fin 8) ⊔ zpowers q = ⊤ := by
  have hsign : Perm.sign q = -1 :=
    (Int.units_eq_one_or _).resolve_left (fun h => hq (Perm.mem_alternatingGroup.mpr h))
  apply top_unique
  intro x _
  by_cases hx : x ∈ alternatingGroup (Fin 8)
  · exact (le_sup_left : alternatingGroup (Fin 8) ≤ alternatingGroup (Fin 8) ⊔ zpowers q) hx
  · have hxsign : Perm.sign x = -1 :=
      (Int.units_eq_one_or _).resolve_left (fun h => hx (Perm.mem_alternatingGroup.mpr h))
    have hmem : x * q⁻¹ ∈ alternatingGroup (Fin 8) := by
      rw [Perm.mem_alternatingGroup, map_mul, map_inv, hxsign, hsign]
      decide
    have hh := (alternatingGroup (Fin 8) ⊔ zpowers q).mul_mem
      ((le_sup_left : alternatingGroup (Fin 8) ≤ alternatingGroup (Fin 8) ⊔ zpowers q) hmem)
      ((le_sup_right : zpowers q ≤ alternatingGroup (Fin 8) ⊔ zpowers q) (mem_zpowers q))
    simpa only [inv_mul_cancel_right] using hh

variable {L : Type*} [Group L]

/-- The eight-point action attached to an actual alternating model of L. -/
noncomputable def automorphismPermutationEquiv (e : L ≃* A) : MulAut L ≃* S :=
  (MulAut.congr e).trans permutationAutEquiv.symm

/-- The permutation action induces precisely the given automorphism of L. -/
theorem automorphismPermutationEquiv_action (e : L ≃* A) (a : MulAut L) (x : L) :
    (e (a x)).val = automorphismPermutationEquiv e a * (e x).val *
      (automorphismPermutationEquiv e a)⁻¹ := by
  have h := permutationAutEquiv.apply_symm_apply (MulAut.congr e a)
  have hh := congrArg (fun b : MulAut A => (b (e x)).val) h
  rw [permutationAutEquiv_apply, MulAut.conjNormal_apply] at hh
  change _ = (e (a (e.symm (e x)))).val at hh
  simpa only [e.symm_apply_apply, automorphismPermutationEquiv, MulEquiv.trans_apply] using hh.symm

theorem automorphismPermutationEquiv_inner (e : L ≃* A) (x : L) :
    automorphismPermutationEquiv e (MulAut.conj x) = (e x).val := by
  apply permutationAutEquiv.injective
  change permutationAutEquiv (permutationAutEquiv.symm (MulAut.congr e (MulAut.conj x))) = _
  rw [permutationAutEquiv.apply_symm_apply, MulAut.congr_conj, permutationAutEquiv_inner]

theorem automorphismPermutationEquiv_mem_alternating (e : L ≃* A) (a : MulAut L) :
    automorphismPermutationEquiv e a ∈ alternatingGroup (Fin 8) ↔
      a ∈ MulAut.innerSubgroup L := by
  constructor
  · intro ha
    let q : A := ⟨automorphismPermutationEquiv e a, ha⟩
    refine ⟨e.symm q, ?_⟩
    apply (automorphismPermutationEquiv e).injective
    rw [automorphismPermutationEquiv_inner, e.apply_symm_apply]
  · rintro ⟨x, rfl⟩
    rw [automorphismPermutationEquiv_inner]
    exact (e x).property

/-- Exhaustive involution conjugacy in the actual automorphism group. -/
theorem automorphism_involution_conjugacy (e : L ≃* A) (a : MulAut L)
    (ha : orderOf a = 2) :
    IsConj (automorphismPermutationEquiv e a) onePair ∨
      IsConj (automorphismPermutationEquiv e a) twoPairs ∨
      IsConj (automorphismPermutationEquiv e a) threePairs ∨
      IsConj (automorphismPermutationEquiv e a) fourPairs := by
  apply involution_conjugacy
  rwa [(automorphismPermutationEquiv e).orderOf_eq]

/-- Any outer actor supplements Inn(L) to the full automorphism group. -/
theorem inner_sup_zpowers_eq_top (e : L ≃* A) (a : MulAut L)
    (ha : a ∉ MulAut.innerSubgroup L) : MulAut.innerSubgroup L ⊔ zpowers a = ⊤ := by
  let f := automorphismPermutationEquiv e
  have hm : (MulAut.innerSubgroup L).map f.toMonoidHom = alternatingGroup (Fin 8) := by
    ext q
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (automorphismPermutationEquiv_mem_alternating e b).mpr hb
    · intro hq
      refine ⟨f.symm q, ?_, f.apply_symm_apply q⟩
      apply (automorphismPermutationEquiv_mem_alternating e _).mp
      change f (f.symm q) ∈ alternatingGroup (Fin 8)
      rwa [f.apply_symm_apply]
  have htop : (MulAut.innerSubgroup L ⊔ zpowers a).map f.toMonoidHom = ⊤ := by
    rw [Subgroup.map_sup, hm, MonoidHom.map_zpowers]
    exact alternating_sup_zpowers_eq_top
      (fun h => ha ((automorphismPermutationEquiv_mem_alternating e a).mp h))
  apply top_unique
  intro b _
  have hb : f b ∈ (MulAut.innerSubgroup L ⊔ zpowers a).map f.toMonoidHom := by
    rw [htop]
    trivial
  obtain ⟨c, hc, he⟩ := hb
  exact f.injective he ▸ hc

/-- The actual generated overgroup, with its specified eight-point action. -/
noncomputable def generatedEquivSymmetric (e : L ≃* A) (a : MulAut L)
    (ha : a ∉ MulAut.innerSubgroup L) :
    (MulAut.innerSubgroup L ⊔ zpowers a : Subgroup (MulAut L)) ≃* S :=
  (MulEquiv.subgroupCongr (inner_sup_zpowers_eq_top e a ha)).trans
    (Subgroup.topEquiv.trans (automorphismPermutationEquiv e))

theorem generatedEquivSymmetric_apply (e : L ≃* A) (a : MulAut L)
    (ha : a ∉ MulAut.innerSubgroup L) (b : (MulAut.innerSubgroup L ⊔ zpowers a : Subgroup (MulAut L))) :
    generatedEquivSymmetric e a ha b = automorphismPermutationEquiv e b.val := rfl

theorem outer_of_threePairs (e : L ≃* A) (a : MulAut L)
    (ha : (automorphismPermutationEquiv e a).cycleType = {2, 2, 2}) :
    a ∉ MulAut.innerSubgroup L := by
  intro hi
  have hs := Perm.mem_alternatingGroup.mp
    ((automorphismPermutationEquiv_mem_alternating e a).mpr hi)
  rw [Perm.sign_of_cycleType, ha] at hs
  exact (by decide : (-1 : ℤˣ) ^ 9 ≠ 1) hs

theorem threePairs_fixedPoints {q : S} (hq : q.cycleType = {2, 2, 2}) :
    Fintype.card (Function.fixedPoints q) = 2 := by
  rw [Perm.card_fixedPoints, hq]
  decide

/-- The overgroup equivalence restricts to the chosen embedding of L. -/
theorem generatedEquivSymmetric_inner (e : L ≃* A) (a : MulAut L)
    (ha : a ∉ MulAut.innerSubgroup L) (x : L) :
    generatedEquivSymmetric e a ha
      ⟨MulAut.conj x, (le_sup_left : MulAut.innerSubgroup L ≤
        MulAut.innerSubgroup L ⊔ zpowers a) ⟨x, rfl⟩⟩ = (e x).val :=
  automorphismPermutationEquiv_inner e x

/-- The overgroup equivalence retains the actor itself. -/
theorem generatedEquivSymmetric_actor (e : L ≃* A) (a : MulAut L)
    (ha : a ∉ MulAut.innerSubgroup L) :
    generatedEquivSymmetric e a ha
      ⟨a, (le_sup_right : zpowers a ≤ MulAut.innerSubgroup L ⊔ zpowers a)
        (mem_zpowers a)⟩ = automorphismPermutationEquiv e a := rfl

end Theory.SpecificGroups.SymmetricEight.Involutions
