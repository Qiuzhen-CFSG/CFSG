module

public import Theory.GroupTheory.NoncentralChiefRefinement.ModuleStrata
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod

/-!
# Chief refinement of homogeneous binary sections

Pull back the coordinate-support flag along the literal quotient map and the
supplied equivariant coordinates. Every term is normal in the ambient group.
Evaluation at the newly admitted coordinate is surjective, with kernel the
preceding term, so the successive relative quotient has one-copy coordinates.
An intermediate ambient-normal subgroup gives an invariant binary subspace;
irreducibility makes it an endpoint. Nontrivial action makes all these chief
factors noncentral, and their number is the original multiplicity.

The construction also covers zero copies: its length and count are zero and
its endpoints coincide. The module-stratum consumer additionally handles
central sections by arbitrary finite chief refinement. Finiteness is needed
only for that central branch, not for the homogeneous construction.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.2.5(8), printed pp.335–336, PDF pp.346–347. This supplies the homogeneous
stratum refinement used by the separate full-filtration assembly.
-/

@[expose] public section

open Subgroup
namespace NoncentralChiefRefinement
variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
variable {A B : NormalNode K} {ρ : Representation (ZMod 2) K V}

private theorem covBy_of_binary_map (hAB : A < B) [Representation.IsIrreducible ρ]
    (q : B.val →* Multiplicative V)
    (hk : ∀ b : B.val, q b = 1 ↔ (b : K) ∈ A.val)
    (he : ∀ k b, (q (MulAut.conjNormal k b)).toAdd = ρ k (q b).toAdd) :
    A ⋖ B := by
  apply (covBy_iff_isChief A B).mpr
  refine ⟨inferInstance, inferInstance, hAB, ?_⟩
  intro Z hZ hAZ hZB
  let W : Subrepresentation ρ :=
    { toSubmodule := AddSubgroup.toZModSubmodule 2
        ((Z.subgroupOf B.val).map q).toAddSubgroup
      apply_mem_toSubmodule := by
        intro k v hv
        change Multiplicative.ofAdd v ∈ (Z.subgroupOf B.val).map q at hv
        obtain ⟨b, hb, hbe⟩ := hv
        change Multiplicative.ofAdd (ρ k v) ∈ (Z.subgroupOf B.val).map q
        refine ⟨MulAut.conjNormal k b, hZ.conj_mem b hb k, ?_⟩
        apply Multiplicative.toAdd.injective
        rw [he, hbe]
        rfl }
  rcases eq_bot_or_eq_top W with hW | hW
  · left
    apply le_antisymm _ hAZ
    intro z hz
    have hmem : (q ⟨z, hZB hz⟩).toAdd ∈ W :=
      ⟨⟨z, hZB hz⟩, hz, rfl⟩
    rw [hW] at hmem
    have heq : q ⟨z, hZB hz⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      exact hmem
    exact (hk _).mp heq
  · right
    apply le_antisymm hZB
    intro b hb
    have hmem : (q ⟨b, hb⟩).toAdd ∈ W := by rw [hW]; trivial
    change q ⟨b, hb⟩ ∈ (Z.subgroupOf B.val).map q at hmem
    obtain ⟨z, hz, heq⟩ := hmem
    have hker : q (z⁻¹ * ⟨b, hb⟩) = 1 := by
      rw [map_mul, map_inv, heq, inv_mul_cancel]
    have ha := hAZ ((hk _).mp hker)
    have hm := Z.mul_mem hz ha
    simpa using hm

namespace SectionCoordinates

/-- A binary homogeneous section is a two-group, without a finiteness assumption. -/
theorem isPGroup {m : ℕ} (c : SectionCoordinates A B ρ m) :
    IsPGroup 2 (Section A B) := by
  have hp : IsPGroup 2 (Multiplicative (Fin m → V)) := by
    intro x
    refine ⟨1, ?_⟩
    change (2 ^ 1 : ℕ) • x.toAdd = 0
    rw [pow_one, ← Nat.cast_smul_eq_nsmul (ZMod 2) 2 x.toAdd]
    change (2 : ZMod 2) • x.toAdd = 0
    rw [show (2 : ZMod 2) = 0 by decide, zero_smul]
  exact hp.of_equiv c.equiv.symm

/-- One irreducible, nontrivially acted-on copy gives an ambient chief interval. -/
theorem covBy (hAB : A ≤ B) [Representation.IsIrreducible ρ]
    (hρ : ∃ k v, ρ k v ≠ v) (c : SectionCoordinates A B ρ 1) : A ⋖ B := by
  have hlt : A < B := lt_of_le_of_ne hAB (by
    intro heq
    apply c.not_isCentral (by decide) hρ
    rw [isCentral_iff_commutator_le, heq]
    exact Subgroup.commutator_le_right _ _)
  let q : B.val →* Multiplicative V :=
    { toFun := fun b => Multiplicative.ofAdd
        ((c.equiv (QuotientGroup.mk' (A.val.subgroupOf B.val) b)).toAdd 0)
      map_one' := by simp
      map_mul' := by intros; simp }
  apply covBy_of_binary_map (ρ := ρ) hlt q
  · intro b
    change (c.equiv (QuotientGroup.mk' (A.val.subgroupOf B.val) b)).toAdd 0 = 0 ↔ _
    constructor
    · intro h
      have he : c.equiv (QuotientGroup.mk' (A.val.subgroupOf B.val) b) = 1 := by
        apply Multiplicative.toAdd.injective
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        simpa [hi] using h
      have he' := c.equiv.injective (he.trans c.equiv.map_one.symm)
      exact (QuotientGroup.eq_one_iff (N := A.val.subgroupOf B.val) b).mp he'
    · intro hb
      have he : QuotientGroup.mk' (A.val.subgroupOf B.val) b = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hb
      simp [he]
  · intro k b
    exact c.equivariant k (QuotientGroup.mk' (A.val.subgroupOf B.val) b) 0

variable {m : ℕ} (c : SectionCoordinates A B ρ m)

/-- Coordinates composed with the literal quotient projection. -/
def quotientCoordinates : B.val →* Multiplicative (Fin m → V) :=
  c.equiv.toMonoidHom.comp (QuotientGroup.mk' (A.val.subgroupOf B.val))

@[simp] theorem quotientCoordinates_conj (k : K) (b : B.val) (j : Fin m) :
    (c.quotientCoordinates (MulAut.conjNormal k b)).toAdd j =
      ρ k ((c.quotientCoordinates b).toAdd j) :=
  c.equivariant k (QuotientGroup.mk' (A.val.subgroupOf B.val) b) j

/-- Pullback of vectors supported in the first `n` coordinates. Normality is
in the whole ambient group, by the given equivariance. -/
def supportNode (n : ℕ) : NormalNode K :=
  ⟨{ carrier := {x | ∃ hx : x ∈ B.val,
        ∀ j : Fin m, n ≤ j.val → (c.quotientCoordinates ⟨x, hx⟩).toAdd j = 0}
     one_mem' := ⟨B.val.one_mem, by
       intro j hj
       change (c.quotientCoordinates 1).toAdd j = 0
       rw [map_one]
       rfl⟩
     mul_mem' := by
       rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
       refine ⟨B.val.mul_mem hx hy, ?_⟩
       intro j hj
       change (c.quotientCoordinates (⟨x, hx⟩ * ⟨y, hy⟩)).toAdd j = 0
       rw [map_mul]
       change (c.quotientCoordinates ⟨x, hx⟩).toAdd j +
         (c.quotientCoordinates ⟨y, hy⟩).toAdd j = 0
       rw [hx' j hj, hy' j hj, add_zero]
     inv_mem' := by
       rintro x ⟨hx, hx'⟩
       refine ⟨B.val.inv_mem hx, ?_⟩
       intro j hj
       change (c.quotientCoordinates (⟨x, hx⟩⁻¹)).toAdd j = 0
       simp [hx' j hj] },
    ⟨by
      rintro x ⟨hx, hx'⟩ k
      refine ⟨B.property.conj_mem x hx k, ?_⟩
      intro j hj
      change (c.quotientCoordinates (MulAut.conjNormal k ⟨x, hx⟩)).toAdd j = 0
      rw [c.quotientCoordinates_conj, hx' j hj, map_zero]⟩⟩

theorem supportNode_le (n : ℕ) : c.supportNode n ≤ B := fun _ hx => hx.1

theorem supportNode_mono : Monotone c.supportNode := by
  intro n l hnl x hx
  exact ⟨hx.1, fun j hj => hx.2 j (hnl.trans hj)⟩

theorem supportNode_zero (hAB : A ≤ B) : c.supportNode 0 = A := by
  apply Subtype.ext
  apply le_antisymm
  · rintro x ⟨hx, hcoords⟩
    have he : c.quotientCoordinates ⟨x, hx⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      funext j
      exact hcoords j (Nat.zero_le _)
    have hq : QuotientGroup.mk' (A.val.subgroupOf B.val) ⟨x, hx⟩ = 1 :=
      c.equiv.injective (he.trans c.equiv.map_one.symm)
    exact (QuotientGroup.eq_one_iff (N := A.val.subgroupOf B.val) ⟨x, hx⟩).mp hq
  · intro x hx
    refine ⟨hAB hx, ?_⟩
    have hq : QuotientGroup.mk' (A.val.subgroupOf B.val) ⟨x, hAB hx⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hx
    intro j hj
    change (c.equiv (QuotientGroup.mk' (A.val.subgroupOf B.val) ⟨x, hAB hx⟩)).toAdd j = 0
    rw [hq, c.equiv.map_one]
    rfl

theorem supportNode_last : c.supportNode m = B := by
  apply le_antisymm (c.supportNode_le m)
  intro x hx
  exact ⟨hx, fun j hj => False.elim (Nat.not_le_of_gt j.isLt hj)⟩

/-- Evaluation at the newly admitted coordinate, written as one copy. -/
def stepMap (i : Fin m) : (c.supportNode (i.val + 1)).val →*
    Multiplicative (Fin 1 → V) where
  toFun x := Multiplicative.ofAdd (fun _ =>
    (c.quotientCoordinates ⟨x.val, (c.supportNode_le _ x.property)⟩).toAdd i)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext j
    exact congrArg (fun y : Multiplicative (Fin m → V) => y.toAdd i)
      c.quotientCoordinates.map_one
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext j
    exact congrArg (fun y : Multiplicative (Fin m → V) => y.toAdd i)
      (c.quotientCoordinates.map_mul
        ⟨x.val, c.supportNode_le _ x.property⟩
        ⟨y.val, c.supportNode_le _ y.property⟩)

theorem stepMap_surjective (i : Fin m) : Function.Surjective (c.stepMap i) := by
  classical
  intro v
  let w : Fin m → V := fun j => if j = i then v.toAdd 0 else 0
  obtain ⟨x, hx⟩ := c.equiv.surjective (Multiplicative.ofAdd w)
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (A.val.subgroupOf B.val) x
  have hb : (b : K) ∈ (c.supportNode (i.val + 1)).val := by
    refine ⟨b.property, ?_⟩
    intro j hj
    have hji : j ≠ i := by intro he; subst j; omega
    change (c.equiv (QuotientGroup.mk' (A.val.subgroupOf B.val) b)).toAdd j = 0
    rw [hx]
    simp [w, hji]
  refine ⟨⟨b, hb⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  change (c.equiv (QuotientGroup.mk' (A.val.subgroupOf B.val) b)).toAdd i = v.toAdd j
  rw [hx]
  simp [w, hj]

theorem stepMap_ker (i : Fin m) :
    (c.stepMap i).ker =
      (c.supportNode i.val).val.subgroupOf (c.supportNode (i.val + 1)).val := by
  ext x
  change c.stepMap i x = 1 ↔ (x : K) ∈ (c.supportNode i.val).val
  constructor
  · intro hx
    refine ⟨c.supportNode_le _ x.property, ?_⟩
    intro j hj
    by_cases heq : j = i
    · subst j
      exact congrArg (fun y : Multiplicative (Fin 1 → V) => y.toAdd 0) hx
    · exact x.property.2 j (by have hv : j.val ≠ i.val := fun h => heq (Fin.ext h); omega)
  · rintro ⟨hx, hx'⟩
    apply Multiplicative.toAdd.injective
    funext j
    exact hx' i le_rfl

/-- The first isomorphism theorem for the actual successive relative quotient. -/
noncomputable def stepCoordinates (i : Fin m) :
    SectionCoordinates (c.supportNode i.val) (c.supportNode (i.val + 1)) ρ 1 where
  equiv := (QuotientGroup.quotientMulEquivOfEq (c.stepMap_ker i).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (c.stepMap i) (c.stepMap_surjective i))
  equivariant k x j := by
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
      ((c.supportNode i.val).val.subgroupOf (c.supportNode (i.val + 1)).val) x
    rw [sectionAction_mk]
    change (c.quotientCoordinates
      (MulAut.conjNormal k ⟨b.val, c.supportNode_le _ b.property⟩)).toAdd i = _
    exact c.quotientCoordinates_conj k ⟨b.val, c.supportNode_le _ b.property⟩ i

end SectionCoordinates



namespace SectionCoordinates
variable {m : ℕ} (c : SectionCoordinates A B ρ m)

/-- A chief series obtained by admitting one homogeneous coordinate at a time. -/
noncomputable def chiefSeries [Representation.IsIrreducible ρ]
    (hρ : ∃ k v, ρ k v ≠ v) : ChiefSeries K where
  length := m
  toFun i := c.supportNode i.val
  step i := (c.stepCoordinates i).covBy
    (c.supportNode_mono (Nat.le_succ i.val)) hρ

@[simp] theorem chiefSeries_length [Representation.IsIrreducible ρ]
    (hρ : ∃ k v, ρ k v ≠ v) : (c.chiefSeries hρ).length = m := rfl

@[simp] theorem chiefSeries_head [Representation.IsIrreducible ρ]
    (hρ : ∃ k v, ρ k v ≠ v) (hAB : A ≤ B) : (c.chiefSeries hρ).head = A :=
  c.supportNode_zero hAB

@[simp] theorem chiefSeries_last [Representation.IsIrreducible ρ]
    (hρ : ∃ k v, ρ k v ≠ v) : (c.chiefSeries hρ).last = B :=
  c.supportNode_last

/-- Each actual chief quotient has the prescribed one-copy coordinates. -/
noncomputable def chiefSeriesCoordinates [Representation.IsIrreducible ρ]
    (hρ : ∃ k v, ρ k v ≠ v) (i : Fin (c.chiefSeries hρ).length) :
    SectionCoordinates ((c.chiefSeries hρ) i.castSucc) ((c.chiefSeries hρ) i.succ) ρ 1 :=
  c.stepCoordinates i

/-- All the constructed chief intervals are noncentral two-factors. -/
theorem chiefSeries_noncentralTwo [Representation.IsIrreducible ρ]
    (hρ : ∃ k v, ρ k v ≠ v) (i : Fin (c.chiefSeries hρ).length) :
    IsNoncentralTwo ((c.chiefSeries hρ) i.castSucc) ((c.chiefSeries hρ) i.succ) :=
  ⟨(c.chiefSeriesCoordinates hρ i).isPGroup,
    (c.chiefSeriesCoordinates hρ i).not_isCentral (by decide) hρ⟩

/-- Homogeneous multiplicity is the actual noncentral two-chief count. -/
theorem chiefSeries_count [Representation.IsIrreducible ρ]
    (hρ : ∃ k v, ρ k v ≠ v) : (c.chiefSeries hρ).noncentralTwoCount = m := by
  unfold ChiefSeries.noncentralTwoCount
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (c.chiefSeries_noncentralTwo hρ))]
  simp

include c in
/-- The homogeneous refinement, including multiplicity zero, with every factor
marked by its actual equivariant one-copy quotient coordinates. -/
theorem exists_chief_refinement (hAB : A ≤ B) [Representation.IsIrreducible ρ]
    (hρ : ∃ k v, ρ k v ≠ v) :
    ∃ s : ChiefSeries K, s.head = A ∧ s.last = B ∧ s.length = m ∧
      s.noncentralTwoCount = m ∧
      ∀ i : Fin s.length,
        Nonempty (SectionCoordinates (s i.castSucc) (s i.succ) ρ 1) ∧
        IsNoncentralTwo (s i.castSucc) (s i.succ) :=
  ⟨c.chiefSeries hρ, c.chiefSeries_head hρ hAB, c.chiefSeries_last hρ,
    rfl, c.chiefSeries_count hρ,
    fun i => ⟨⟨c.chiefSeriesCoordinates hρ i⟩, c.chiefSeries_noncentralTwo hρ i⟩⟩

end SectionCoordinates

/-- Refinement of a module stratum with its multiplicity and marked noncentral
chief factors. The central branch uses an arbitrary chief refinement and has
count zero; its length is not constrained by the multiplicity. This is the
stratum-level input to the G.2.5(8) full-filtration assembly. -/
theorem IsModuleStratum.exists_chief_refinement [Finite K] {m : ℕ}
    (h : IsModuleStratum ρ A B m) (hAB : A ≤ B) [Representation.IsIrreducible ρ]
    (hρ : ∃ k v, ρ k v ≠ v) :
    ∃ s : ChiefSeries K, s.head = A ∧ s.last = B ∧ s.noncentralTwoCount = m ∧
      ∀ i : Fin s.length, IsNoncentralTwo (s i.castSucc) (s i.succ) →
        Nonempty (SectionCoordinates (s i.castSucc) (s i.succ) ρ 1) := by
  rcases h with ⟨hc, rfl⟩ | hc
  · obtain ⟨s, hs0, hsl⟩ := exists_chiefSeries A B hAB
    have hcentral : IsCentral s.head s.last := by rw [hs0, hsl]; exact hc
    refine ⟨s, hs0, hsl, s.noncentralTwoCount_eq_zero_of_central hcentral, ?_⟩
    intro i hi
    exact (hi.2 (hcentral.subinterval (CompositionSeries.head_le i.castSucc)
      (CompositionSeries.le_last i.succ))).elim
  · obtain ⟨c⟩ := hc
    obtain ⟨s, hs0, hsl, _, hcount, hf⟩ := c.exists_chief_refinement hAB hρ
    exact ⟨s, hs0, hsl, hcount, fun i _ => (hf i).1⟩

end NoncentralChiefRefinement
