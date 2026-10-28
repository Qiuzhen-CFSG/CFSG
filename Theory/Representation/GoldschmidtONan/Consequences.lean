module

public import Theory.Representation.GoldschmidtONan.Basic
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.SpecificGroups.Frobenius21.Recognition
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.GroupTheory.IndexNormal

/-!
# Normality, model recognition, and irreducibility consequences

The normalization condition is equivalent to relative normality in the
actual fixed-space stabilizer. A normal actor gives the singleton alternative.
A two-member orbit gives a normal subgroup of index two, by its actual action
on the two subspaces. Thus irreducibility and absence of such a subgroup
exclude the first three alternatives. The order-21 recognition theorem then
identifies the remaining group with the concrete Frobenius model.

The irreducibility statements explicitly assume the four-case conclusion;
they are consequences of Proposition 14.2, not a proof of that proposition.
Source: GLS, Number 2, Chapter C, Definition 14.1, Proposition 14.2 and its
following remark (`refs/KGroup/GLS2/ChapterC.tex`).
-/

public section

namespace Representation.GoldschmidtONan
open BinaryOffender RegularCyclicNormalClosure
variable {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}

/-- Setwise invariance is exactly the singleton-orbit case. -/
theorem singletonCase_iff_invariant :
    SingletonCase ρ Y ↔ Invariant ρ (fixedSpace ρ Y) := by
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    ext W
    constructor
    · rintro ⟨x, rfl⟩
      exact h x
    · intro hW
      have he : W = fixedSpace ρ Y := hW
      subst W
      exact ⟨1, h 1⟩

/-- Recognition identifies the exceptional group with the concrete C₇ ⋊ C₃. -/
theorem exceptionalCase_iff_model [Finite X] :
    ExceptionalCase ρ Y ↔
      Module.finrank (ZMod 2) (fixedSpace ρ Y) = 1 ∧
      Module.finrank (ZMod 2) V = 3 ∧ Nonempty (X ≃* Frobenius21.Model) := by
  constructor
  · rintro ⟨hf, hv, hc, hn⟩
    exact ⟨hf, hv, Frobenius21.nonempty_mulEquiv_of_card_eq hc hn⟩
  · rintro ⟨hf, hv, ⟨e⟩⟩
    refine ⟨hf, hv, (Nat.card_congr e.toEquiv).trans Frobenius21.card_model, ?_⟩
    intro hcomm
    apply Frobenius21.not_commutative
    intro a b
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    simpa only [map_mul] using congrArg e (hcomm a b)

/-- An invariant subspace of an irreducible representation is zero or the whole space. -/
theorem Invariant.eq_bot_or_top [IsIrreducible ρ] {W : Submodule (ZMod 2) V}
    (hW : Invariant ρ W) : W = ⊥ ∨ W = ⊤ := by
  let S : Subrepresentation ρ := ⟨W, fun x v hv => by
    have hm := Submodule.mem_map_of_mem (f := ρ x) hv
    rwa [hW x] at hm⟩
  rcases eq_bot_or_eq_top S with hs | hs
  · exact Or.inl (congrArg Subrepresentation.toSubmodule hs)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule hs)

/-- Irreducibility excludes alternatives (i) and (iii).
This consequence is conditional on the four-case theorem. -/
theorem Input.swapped_or_exceptional_of_irreducible [Finite X] [IsIrreducible ρ]
    (h : Input ρ Y) (ha : Alternatives ρ Y) : SwappedCase ρ Y ∨ ExceptionalCase ρ Y := by
  rcases ha with ha | ha | ha | ha
  · rcases ha.2.eq_bot_or_top with hf | hf
    · exact False.elim (h.fixed_nontrivial hf)
    · exact False.elim (h.fixed_ne_top hf)
  · exact Or.inl ha
  · rcases ha.2.2.eq_bot_or_top with hd | hd
    · exact False.elim (h.moved_ne_bot hd)
    · exact False.elim (h.moved_ne_top hd)
  · exact Or.inr ha

/-- The setwise stabilizer criterion written as equality of image subspaces. -/
theorem mem_subspaceStabilizer_iff_map (W : Submodule (ZMod 2) V) (x : X) :
    x ∈ subspaceStabilizer ρ W ↔ W.map (ρ x) = W := by
  constructor
  · intro hx
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact (hx v).2 hv
    · intro v hv
      refine ⟨ρ x⁻¹ v, ?_, ?_⟩
      · apply (hx (ρ x⁻¹ v)).1
        simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
          map_one, Module.End.one_apply] using hv
      · simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
          map_one, Module.End.one_apply]
  · intro hx v
    constructor
    · intro hv
      rw [← hx] at hv
      obtain ⟨w, hw, he⟩ := hv
      have hwv := action_injective x he
      subst w
      exact hw
    · intro hv
      rw [← hx]
      exact ⟨v, hv, rfl⟩

/-- The normalization clause is precisely normality inside the fixed-space stabilizer. -/
theorem normal_in_stabilizer_iff :
    (∀ x : X, (fixedSpace ρ Y).map (ρ x) = fixedSpace ρ Y →
      Y.map (MulAut.conj x).toMonoidHom = Y) ↔
    (Y.subgroupOf (subspaceStabilizer ρ (fixedSpace ρ Y))).Normal := by
  have hYS : Y ≤ subspaceStabilizer ρ (fixedSpace ρ Y) := by
    apply le_subspaceStabilizer
    intro y hy v hv
    rw [show ρ y v = v from hv ⟨y, hy⟩]
    exact hv
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYS]
  constructor
  · intro h x hx
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (h x ((mem_subspaceStabilizer_iff_map _ x).mp hx))
  · intro h x hx
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (h ((mem_subspaceStabilizer_iff_map _ x).mpr hx))

/-- A normal actor gives the first alternative without further hypotheses. -/
theorem singletonCase_of_normal (hY : Y.Normal) : SingletonCase ρ Y := by
  let : Y.Normal := hY
  apply singletonCase_iff_invariant.mpr
  intro x
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact (le_comap_invariants ρ Y x) hv
  · intro v hv
    refine ⟨ρ x⁻¹ v, (le_comap_invariants ρ Y x⁻¹) hv, ?_⟩
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
      map_one, Module.End.one_apply]

/-- For a Goldschmidt–O'Nan pair, the singleton case is equivalent to normality of Y. -/
theorem Input.singletonCase_iff_normal (h : Input ρ Y) : SingletonCase ρ Y ↔ Y.Normal := by
  constructor
  · intro hs
    exact Subgroup.normal_iff_map_conj_eq.mpr fun x => h.normal_in_stabilizer x (hs.2 x)
  · exact singletonCase_of_normal

/-- A two-member fixed-space orbit gives an actual normal subgroup of index two. -/
theorem Input.normal_index_two_of_swapped [Finite X] (h : Input ρ Y)
    (hs : SwappedCase ρ Y) : ∃ H : Subgroup X, H.Normal ∧ H.index = 2 := by
  let F := fixedSpace ρ Y
  let D := displacementSpan ρ Y ⊤
  let H := subspaceStabilizer ρ F
  have hne : F ≠ D := h.fixed_ne_moved
  obtain ⟨horbit, t, _, htF, htD⟩ := hs
  change F.map (ρ t) = D at htF
  change D.map (ρ t) = F at htD
  have hmul (a b : X) : F.map (ρ (a * b)) = (F.map (ρ b)).map (ρ a) := by
    rw [← Submodule.map_comp, map_mul]
    rfl
  have hindex : H.index = 2 := by
    apply Subgroup.index_eq_two_iff'.mpr
    refine ⟨t, fun b => ?_⟩
    have hb : F.map (ρ b) = F ∨ F.map (ρ b) = D := by
      have hm : F.map (ρ b) ∈ fixedOrbit ρ Y := ⟨b, rfl⟩
      rw [horbit] at hm
      exact hm
    change Xor (t * b ∈ subspaceStabilizer ρ F) (b ∈ subspaceStabilizer ρ F)
    rw [mem_subspaceStabilizer_iff_map, mem_subspaceStabilizer_iff_map, hmul]
    rcases hb with hb | hb
    · simp [xor_iff_iff_not, hb, htF, hne.symm]
    · simp [xor_iff_iff_not, hb, htD, hne.symm]
  exact ⟨H, H.normal_of_index_eq_two hindex, hindex⟩

/-- The remark following Proposition 14.2, conditional only on that proposition:
irreducibility and absence of a normal index-two subgroup force the concrete model. -/
theorem Input.model_of_irreducible_of_no_index_two [Finite X] [IsIrreducible ρ]
    (h : Input ρ Y) (ha : Alternatives ρ Y)
    (hindex : ∀ H : Subgroup X, H.Normal → H.index ≠ 2) :
    Module.finrank (ZMod 2) (fixedSpace ρ Y) = 1 ∧
      Module.finrank (ZMod 2) V = 3 ∧ Nonempty (X ≃* Frobenius21.Model) := by
  rcases h.swapped_or_exceptional_of_irreducible ha with hs | he
  · obtain ⟨H, hH, hi⟩ := h.normal_index_two_of_swapped hs
    exact False.elim (hindex H hH hi)
  · exact exceptionalCase_iff_model.mp he

end Representation.GoldschmidtONan
