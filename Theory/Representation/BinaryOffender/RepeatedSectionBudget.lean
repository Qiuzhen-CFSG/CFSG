module
public import Theory.Representation.BinaryParabolicNatural.RepeatedOffender
public import Theory.Representation.BinaryOffender.QuadraticImageBound
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.FaithfulRankOne

/-!
# Rank loss and FF bounds on repeated invariant sections

Restrict a binary representation to an overgroup of an elementary actor and
pass to a literal invariant section. The actor's image rank cannot increase;
the difference is the exact rank lost in the action kernel. Fixed codimension
cannot increase either. Equivariant coordinates on r identical copies then
multiply the constituent's displacement by r, retaining the same actor.

For a rank-deficit bound of at most one, multiplicity greater than one and
kernel rank loss at most one force an FF-offender on the constituent image.
Multiplicity at least three, zero rank loss and actor rank at most two force
the sharp values r = 3, j = 1, actor rank 2 and constituent displacement 1.

The Chapter 13 consumer constructs the ambient bound by B.2.4 and applies
B.5.6 to exclude the odd-prime-by-two section. Selecting that section and its
coordinates remains a separate mathematical step of the source argument.
Source: Aschbacher--Smith, 13.1.9, printed pp.870--871, especially (*).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender.RepeatedSectionBudget
variable {Q V I : Type*} [Group Q] [Finite Q]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [AddCommGroup I] [Module (ZMod 2) I] [FiniteDimensional (ZMod 2) I]

omit [Finite Q] [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) I] in
private theorem copy_kernel (ρ : Representation (ZMod 2) Q V)
    (τ : Representation (ZMod 2) Q I) {r : ℕ} (hr : 0 < r)
    (e : V ≃ₗ[ZMod 2] (Fin r → I))
    (he : ∀ g v, e (ρ g v) = fun i => τ g (e v i)) : ρ.ker = τ.ker := by
  ext g
  constructor
  · intro hg
    apply LinearMap.ext
    intro v
    have hh := congrFun (he g (e.symm (fun _ => v))) ⟨0,hr⟩
    change ρ g = 1 at hg
    rw [hg] at hh
    simpa only [Module.End.one_apply, e.apply_symm_apply] using hh.symm
  · intro hg
    apply LinearMap.ext
    intro v
    apply e.injective
    rw [he]
    change τ g = 1 at hg
    simp only [hg, Module.End.one_apply]

omit [Finite Q] [FiniteDimensional (ZMod 2) V] in
private theorem copy_fixedCodim (ρ : Representation (ZMod 2) Q V)
    (τ : Representation (ZMod 2) Q I) {r : ℕ}
    (e : V ≃ₗ[ZMod 2] (Fin r → I))
    (he : ∀ g v, e (ρ g v) = fun i => τ g (e v i)) (A : Subgroup Q) :
    fixedCodim ρ A = r * fixedCodim τ A := by
  have hh := fixedCodim_map_equivariant ρ (BinaryParabolicNatural.copies (Fin r) τ)
    (MonoidHom.id Q) e he A
  simpa only [Subgroup.map_id, BinaryParabolicNatural.fixedCodim_copies,
    Fintype.card_fin] using hh

variable (ρ : Representation (ZMod 2) Q V) (E A : Subgroup Q)

/-- The actual action of the same actor on the indicated invariant section. -/
@[expose] def actor (U W : Subrepresentation (ρ.comp E.subtype)) :=
  actionSubgroup (sectionRepresentation (ρ.comp E.subtype) U W) (A.subgroupOf E)

/-- The rank lost in passing from the original actor to this section. -/
@[expose] def epsilon (U W : Subrepresentation (ρ.comp E.subtype)) : ℕ :=
  rank A - rank (actor ρ E A U W)

variable {ρ E A}

omit [Finite Q] in
private theorem relative_rank (hAE : A ≤ E) : rank (A.subgroupOf E) = rank A :=
  congrArg (Nat.log 2) (Nat.card_congr (subgroupOfEquivOfLe hAE).toEquiv)

omit [FiniteDimensional (ZMod 2) V] in
theorem actor_rank_le (hAE : A ≤ E)
    (U W : Subrepresentation (ρ.comp E.subtype)) : rank (actor ρ E A U W) ≤ rank A := by
  have hc := Nat.card_le_card_of_surjective _
    ((actionHom (sectionRepresentation (ρ.comp E.subtype) U W)).subgroupMap_surjective
      (A.subgroupOf E))
  have hl := Nat.log_mono_right (b := 2) hc
  exact hl.trans_eq (relative_rank hAE)

omit [FiniteDimensional (ZMod 2) V] in
theorem epsilon_add_rank (hAE : A ≤ E)
    (U W : Subrepresentation (ρ.comp E.subtype)) :
    epsilon ρ E A U W + rank (actor ρ E A U W) = rank A :=
  Nat.sub_add_cancel (actor_rank_le hAE U W)

/-- Restriction and the literal section quotient consume at most the original
B.2.4 bound, with the exact actor kernel recorded by epsilon. -/
theorem section_bound (hAE : A ≤ E)
    (U W : Subrepresentation (ρ.comp E.subtype)) {j : ℕ}
    (hb : fixedCodim ρ A ≤ j + rank A) :
    fixedCodim (imageRepresentation (sectionRepresentation (ρ.comp E.subtype) U W))
        (actor ρ E A U W) ≤ j + epsilon ρ E A U W + rank (actor ρ E A U W) := by
  have hs := fixedCodim_section_le (ρ.comp E.subtype) U W (A.subgroupOf E)
  have he : fixedCodim (ρ.comp E.subtype) (A.subgroupOf E) = fixedCodim ρ A := by
    unfold fixedCodim
    rw [fixedSpace_comp_map, map_subgroupOf_eq_of_le hAE]
  rw [he] at hs
  have hl := epsilon_add_rank (ρ := ρ) hAE U W
  have hsimage : fixedCodim (imageRepresentation
      (sectionRepresentation (ρ.comp E.subtype) U W)) (actor ρ E A U W) ≤
      fixedCodim ρ A := by
    simpa only [actor, fixedCodim_actionSubgroup] using hs
  omega

omit [FiniteDimensional (ZMod 2) V] in
/-- The odd-prime construction needs only a nontrivial section image and
original actor rank at most two to obtain epsilon in {0,1}. -/
theorem epsilon_le_one (hAE : A ≤ E) (hA : IsElementaryTwo A)
    (U W : Subrepresentation (ρ.comp E.subtype))
    (hne : actor ρ E A U W ≠ ⊥) (hr : rank A ≤ 2) : epsilon ρ E A U W ≤ 1 := by
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 (A.subgroupOf E) :=
    IsElementaryAbelian.subgroupOf hAE
  have he : IsElementaryTwo (actor ρ E A U W) := ⟨hne, IsElementaryAbelian.map _⟩
  have hp := he.rank_pos
  unfold epsilon
  omega

omit [Finite Q] [FiniteDimensional (ZMod 2) V] in
/-- Faithfulness on the chosen section removes the rank loss exactly. -/
theorem epsilon_eq_zero (hAE : A ≤ E)
    (U W : Subrepresentation (ρ.comp E.subtype))
    (hf : ∀ a ∈ A.subgroupOf E, (∀ v,
      sectionRepresentation (ρ.comp E.subtype) U W a v = v) → a = 1) :
    epsilon ρ E A U W = 0 := by
  unfold epsilon actor
  rw [actionSubgroup_rank _ _ hf, relative_rank hAE, Nat.sub_self]

/-- Source (*) for an actual equivariant decomposition into r copies. -/
theorem copies_bound (hAE : A ≤ E)
    (U W : Subrepresentation (ρ.comp E.subtype))
    (τ : Representation (ZMod 2) E I) {r j : ℕ}
    (e : (W.toSubmodule ⧸ (sectionLower (ρ.comp E.subtype) U W).toSubmodule) ≃ₗ[ZMod 2]
      (Fin r → I))
    (he : ∀ g v, e (sectionRepresentation (ρ.comp E.subtype) U W g v) =
      fun i => τ g (e v i))
    (hb : fixedCodim ρ A ≤ j + rank A) :
    r * fixedCodim (imageRepresentation τ) (actionSubgroup τ (A.subgroupOf E)) ≤
      j + epsilon ρ E A U W + rank (actor ρ E A U W) := by
  have hs := section_bound hAE U W hb
  rw [actor, fixedCodim_actionSubgroup, copy_fixedCodim _ τ e he] at hs
  simpa only [actor, fixedCodim_actionSubgroup] using hs

omit [Finite Q] [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) I] in
/-- The image of the actor has the same rank on W and on one copy of I.
This uses the actual coordinate equations and a positive multiplicity. -/
theorem copies_actor_rank (U W : Subrepresentation (ρ.comp E.subtype))
    (τ : Representation (ZMod 2) E I) {r : ℕ} (hr : 0 < r)
    (e : (W.toSubmodule ⧸ (sectionLower (ρ.comp E.subtype) U W).toSubmodule) ≃ₗ[ZMod 2]
      (Fin r → I))
    (he : ∀ g v, e (sectionRepresentation (ρ.comp E.subtype) U W g v) =
      fun i => τ g (e v i)) :
    rank (actor ρ E A U W) = rank (actionSubgroup τ (A.subgroupOf E)) := by
  unfold actor
  rw [rank_actionSubgroup_eq_log_relIndex, rank_actionSubgroup_eq_log_relIndex,
    copy_kernel _ τ hr e he]

/-- With r > 1 and epsilon at most one, (*) makes the actual constituent
image an FF-module. The inequality is proved, not supplied as a premise. -/
theorem copies_offender (hAE : A ≤ E) (hA : IsElementaryTwo A)
    (U W : Subrepresentation (ρ.comp E.subtype))
    (τ : Representation (ZMod 2) E I) {r j : ℕ} (hr : 1 < r) (hj : j ≤ 1)
    (e : (W.toSubmodule ⧸ (sectionLower (ρ.comp E.subtype) U W).toSubmodule) ≃ₗ[ZMod 2]
      (Fin r → I))
    (he : ∀ g v, e (sectionRepresentation (ρ.comp E.subtype) U W g v) =
      fun i => τ g (e v i))
    (hb : fixedCodim ρ A ≤ j + rank A)
    (hne : actor ρ E A U W ≠ ⊥) (hε : epsilon ρ E A U W ≤ 1) :
    IsOffender (imageRepresentation τ) (actionSubgroup τ (A.subgroupOf E)) := by
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 (A.subgroupOf E) := IsElementaryAbelian.subgroupOf hAE
  have hs : IsElementaryTwo (actor ρ E A U W) := ⟨hne,IsElementaryAbelian.map _⟩
  have hsame := copies_actor_rank (A := A) U W τ (by omega : 0 < r) e he
  have hp := hs.rank_pos
  rw [hsame] at hp
  have hi : IsElementaryTwo (actionSubgroup τ (A.subgroupOf E)) := by
    refine ⟨?_,IsElementaryAbelian.map _⟩
    intro hzero
    rw [hzero,BinaryOffender.rank_bot] at hp
    omega
  refine ⟨hi,?_⟩
  have hb' := copies_bound hAE U W τ e he hb
  rw [hsame] at hb'
  by_contra! hn
  have hm := Nat.mul_le_mul_right
    (fixedCodim (imageRepresentation τ) (actionSubgroup τ (A.subgroupOf E)))
    (show 2 ≤ r by omega)
  omega

/-- Once the surviving action has multiplicity at least three and no rank
loss, every numerical inequality in (*) is sharp. -/
theorem copies_sharp (hAE : A ≤ E) (hA : IsElementaryTwo A)
    (U W : Subrepresentation (ρ.comp E.subtype))
    (τ : Representation (ZMod 2) E I) {r j : ℕ} (hr : 3 ≤ r) (hj : j ≤ 1)
    (e : (W.toSubmodule ⧸ (sectionLower (ρ.comp E.subtype) U W).toSubmodule) ≃ₗ[ZMod 2]
      (Fin r → I))
    (he : ∀ g v, e (sectionRepresentation (ρ.comp E.subtype) U W g v) =
      fun i => τ g (e v i))
    (hb : fixedCodim ρ A ≤ j + rank A)
    (hne : actor ρ E A U W ≠ ⊥) (hε : epsilon ρ E A U W = 0)
    (hA2 : rank A ≤ 2) :
    r = 3 ∧ j = 1 ∧ rank A = 2 ∧ rank (actor ρ E A U W) = 2 ∧
      fixedCodim (imageRepresentation τ) (actionSubgroup τ (A.subgroupOf E)) = 1 ∧
      fixedCodim ρ A = 3 := by
  have hoff := copies_offender hAE hA U W τ (by omega : 1 < r) hj e he hb hne
    (by omega : epsilon ρ E A U W ≤ 1)
  have hp := fixedCodim_pos_of_faithful (imageRepresentation τ)
    (imageRepresentation_injective τ) hoff.1.1
  have hs := copies_bound hAE U W τ e he hb
  have hl := epsilon_add_rank (ρ := ρ) hAE U W
  have hmul := Nat.mul_le_mul_right
    (fixedCodim (imageRepresentation τ) (actionSubgroup τ (A.subgroupOf E))) hr
  have hbound : 3 * fixedCodim (imageRepresentation τ)
      (actionSubgroup τ (A.subgroupOf E)) ≤ 3 := hmul.trans (hs.trans (by omega))
  have hc : fixedCodim (imageRepresentation τ) (actionSubgroup τ (A.subgroupOf E)) = 1 := by
    omega
  rw [hc,mul_one] at hs
  have hr3 : r = 3 := by omega
  have hj1 : j = 1 := by omega
  have hAeq : rank A = 2 := by omega
  have hbareq : rank (actor ρ E A U W) = 2 := by omega
  refine ⟨hr3,hj1,hAeq,hbareq,hc,?_⟩
  have hs' := fixedCodim_section_le (ρ.comp E.subtype) U W (A.subgroupOf E)
  have hrest : fixedCodim (ρ.comp E.subtype) (A.subgroupOf E) = fixedCodim ρ A := by
    unfold fixedCodim
    rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le hAE]
  rw [copy_fixedCodim _ τ e he,hrest] at hs'
  rw [fixedCodim_actionSubgroup] at hc
  rw [hr3,hc,mul_one] at hs'
  omega

end Representation.BinaryOffender.RepeatedSectionBudget
