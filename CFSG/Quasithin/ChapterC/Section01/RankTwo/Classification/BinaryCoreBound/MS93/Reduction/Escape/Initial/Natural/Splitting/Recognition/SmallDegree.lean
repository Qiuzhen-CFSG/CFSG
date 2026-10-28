module

public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.FieldTheory.Finiteness

/-!
# Splitting small moving spaces for binary SL₃(2) actions

A nontrivial binary SL₃(2) representation of dimension at most three has
zero fixed space. Indeed, simplicity and order 168 exclude nontrivial actions
in dimension at most two. A nonzero fixed space would leave such a quotient;
perfectness then excludes the resulting action with central displacements.

Perfectness also makes the action on the full moving space nontrivial.
If that space and the quotient by all fixed vectors both have dimension at
most three, the moving space has dimension exactly three and is a complement
to the fixed space. Simplicity gives faithfulness of its restricted action.

This is the small-degree splitting argument for the binary specialization of
Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two* (1993),
(1.4)--(1.5), pp.842--843, used in (4.3.1)(iii), p.883.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open Matrix.PSL3Two (SL)
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Splitting.Recognition

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem action_trivial_of_finrank_le_two (σ : Representation (ZMod 2) SL V)
    (hd : Module.finrank (ZMod 2) V ≤ 2) : ∀ g v, σ g v = v := by
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  rcases (inferInstance : σ.ker.Normal).eq_bot_or_eq_top with hb | ht
  · have hinj := σ.ker_eq_bot_iff.mp hb
    let : Finite (Module.End (ZMod 2) V) := Module.finite_of_finite (ZMod 2)
    have hc := Nat.card_le_card_of_injective σ hinj
    rw [Matrix.PSL3Two.card_SL, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod, Module.finrank_linearMap] at hc
    have hp : 2 ^ (Module.finrank (ZMod 2) V * Module.finrank (ZMod 2) V) ≤ 2 ^ 4 :=
      Nat.pow_le_pow_right (by decide) (by nlinarith)
    norm_num at hp
    omega
  · have he : σ = 1 := MonoidHom.ker_eq_top_iff.mp ht
    intro g v
    rw [he]
    rfl

omit [FiniteDimensional (ZMod 2) V] in
private theorem faithful_of_nontrivial (σ : Representation (ZMod 2) SL V)
    (hn : ∃ g v, σ g v ≠ v) : Function.Injective σ := by
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  rcases (inferInstance : σ.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact σ.ker_eq_bot_iff.mp hb
  · have he : σ = 1 := MonoidHom.ker_eq_top_iff.mp ht
    obtain ⟨g, v, hv⟩ := hn
    exact False.elim (hv (by rw [he]; rfl))

private theorem fixed_eq_bot_of_small_nontrivial (σ : Representation (ZMod 2) SL V)
    (hd : Module.finrank (ZMod 2) V ≤ 3) (hn : ∃ g v, σ g v ≠ v) :
    fixedSpace σ ⊤ = ⊥ := by
  let : Group.IsPerfect SL := Atlas.sl_perfect (F := ZMod 2) 3 (by decide)
  let F : Subrepresentation σ := {
    toSubmodule := fixedSpace σ ⊤
    apply_mem_toSubmodule := fun g v hv => by
      rw [show σ g v = v from hv ⟨g, mem_top g⟩]
      exact hv }
  by_contra hb
  have hp : 0 < Module.finrank (ZMod 2) F.toSubmodule :=
    Nat.pos_of_ne_zero (fun h => hb (Submodule.finrank_eq_zero.mp h))
  have hsum := F.toSubmodule.finrank_quotient_add_finrank
  have hfixQ := action_trivial_of_finrank_le_two F.quotientRepresentation (by omega)
  have hC : subspaceCommutator σ ⊤ ⊤ ≤ fixedSpace σ ⊤ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, v, _, rfl⟩
    exact (Submodule.Quotient.eq F.toSubmodule).mp (hfixQ g (F.toSubmodule.mkQ v))
  have hall := le_fixedSpace_of_commutator_le_fixedSpace σ ⊤ ⊤
    (le_subspaceStabilizer σ ⊤ (by simp)) hC
  obtain ⟨g, v, hv⟩ := hn
  exact hv (hall Submodule.mem_top ⟨g, mem_top g⟩)

/-- The literal space spanned by all action differences, with its restricted action. -/
@[expose] noncomputable def movingSubrepresentation (σ : Representation (ZMod 2) SL V) :
    Subrepresentation σ where
  toSubmodule := Coinvariants.ker σ
  apply_mem_toSubmodule g v hv := by
    have h := (Coinvariants.ker σ).add_mem (Coinvariants.sub_mem_ker g v) hv
    simpa only [sub_add_cancel] using h

omit [FiniteDimensional (ZMod 2) V] in
private theorem moving_nontrivial (σ : Representation (ZMod 2) SL V)
    (hn : ∃ g v, σ g v ≠ v) :
    ∃ g v, (movingSubrepresentation σ).toRepresentation g v ≠ v := by
  let : Group.IsPerfect SL := Atlas.sl_perfect (F := ZMod 2) 3 (by decide)
  by_contra! hfix
  have hC : subspaceCommutator σ ⊤ ⊤ ≤ fixedSpace σ ⊤ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, v, _, rfl⟩ a
    exact congrArg Subtype.val (hfix a.val
      ⟨σ g v - v, Coinvariants.sub_mem_ker g v⟩)
  have hall := le_fixedSpace_of_commutator_le_fixedSpace σ ⊤ ⊤
    (le_subspaceStabilizer σ ⊤ (by simp)) hC
  obtain ⟨g, v, hv⟩ := hn
  exact hv (hall Submodule.mem_top ⟨g, mem_top g⟩)

/-- If the moving-space dimension and fixed-space codimension are both at most
three, a nontrivial SL₃(2) action has a faithful three-dimensional moving
space complementary to its full fixed space. -/
theorem linear_splitting (σ : Representation (ZMod 2) SL V)
    (hn : ∃ g v, σ g v ≠ v)
    (hmove : Module.finrank (ZMod 2) (Coinvariants.ker σ) ≤ 3)
    (hfixed : fixedCodim σ ⊤ ≤ 3) :
    Module.finrank (ZMod 2) (Coinvariants.ker σ) = 3 ∧
    Function.Injective (movingSubrepresentation σ).toRepresentation ∧
    IsCompl (Coinvariants.ker σ) (fixedSpace σ ⊤) := by
  let W := movingSubrepresentation σ
  have hnW := moving_nontrivial σ hn
  have hdW : Module.finrank (ZMod 2) W.toSubmodule = 3 := by
    have hnot : ¬ Module.finrank (ZMod 2) W.toSubmodule ≤ 2 := by
      intro h
      obtain ⟨g, v, hv⟩ := hnW
      exact hv (action_trivial_of_finrank_le_two W.toRepresentation h g v)
    change Module.finrank (ZMod 2) W.toSubmodule ≤ 3 at hmove
    omega
  have hfW := faithful_of_nontrivial W.toRepresentation hnW
  have hFW := fixed_eq_bot_of_small_nontrivial W.toRepresentation hmove hnW
  have hdis : Disjoint (Coinvariants.ker σ) (fixedSpace σ ⊤) := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro v hv
    have h : (⟨v, hv.1⟩ : W.toSubmodule) ∈ fixedSpace W.toRepresentation ⊤ := by
      intro a
      exact Subtype.ext (hv.2 a)
    rw [hFW] at h
    exact congrArg Subtype.val (show (⟨v, hv.1⟩ : W.toSubmodule) = 0 from h)
  have hsum := (Coinvariants.ker σ).finrank_sup_add_finrank_inf_eq (fixedSpace σ ⊤)
  rw [hdis.eq_bot, finrank_bot, add_zero] at hsum
  have hdim := fixedCodim_add_finrank σ (⊤ : Subgroup SL)
  have hsup : Coinvariants.ker σ ⊔ fixedSpace σ ⊤ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hle := Submodule.finrank_le (Coinvariants.ker σ ⊔ fixedSpace σ ⊤)
    change Module.finrank (ZMod 2) (Coinvariants.ker σ) = 3 at hdW
    omega
  exact ⟨hdW, hfW, ⟨hdis, codisjoint_iff.mpr hsup⟩⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Splitting.Recognition
