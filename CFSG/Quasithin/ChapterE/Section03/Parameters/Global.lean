module

public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module
public import CFSG.Quasithin.ChapterE.Section03.WeakClosure
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Global weak-closure parameters and the actual automizer action

The action used here is the faithful action of the image of `N_G(V)` in
`Aut(V)` on the binary vector space underlying the elementary abelian group
`V`. The global parameter `globalR` minimizes actual quotient codimensions
among subgroups whose ambient centralizer escapes `N_G(V)`. Its value is
infinity when that family is empty, in particular when `V` is normal.

Conjugating a witness conjugates both its centralizer and the normalizer of
`V` and preserves relative index. This proves invariance of `r` and E.3.4.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.3.1–5,
printed pp. 231–232.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- The actual induced automorphism group `Aut_G(V)`. -/
abbrev Automizer (V : Subgroup G) := V.normalizerMonoidHom.range

/-- The faithful binary action of `Aut_G(V)` on `V`. -/
noncomputable def automizerRepresentation (V : Subgroup G) [IsElementaryAbelian 2 V] :
    Representation (ZMod 2) (Automizer V) (Additive V) where
  toFun a := a.val.toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by ext v; rfl
  map_mul' _ _ := by ext v; rfl

theorem automizerRepresentation_injective (V : Subgroup G) [IsElementaryAbelian 2 V] :
    Function.Injective (automizerRepresentation V) := by
  intro a b h
  apply Subtype.ext
  apply MulEquiv.ext
  intro v
  exact congrArg (fun f : Module.End (ZMod 2) (Additive V) => f (Additive.ofMul v)) h

/-- The image `Aut_A(V)`; the subgroup-of operation restricts to `A ∩ N_G(V)`. -/
def inducedAutomizer (V A : Subgroup G) : Subgroup (Automizer V) :=
  (A.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom.rangeRestrict

/-- Binary codimension, agreeing with the dimension of the actual quotient
when `V` is elementary abelian. -/
noncomputable def subgroupCorank (V U : Subgroup G) : ℕ := Nat.log 2 (U.relIndex V)

theorem subgroupCorank_eq_quotient_finrank [Finite G]
    (V U : Subgroup G) [IsElementaryAbelian 2 V] :
    subgroupCorank V U = Module.finrank (ZMod 2) (Additive (V ⧸ U.subgroupOf V)) :=
  Subgroup.log_relIndex_eq_quotient_finrank V U

/-- E.3.3. Empty minimizing families have value infinity. -/
noncomputable def globalR (V : Subgroup G) : ℕ∞ :=
  ⨅ (U : Subgroup G) (_ : U ≤ V ∧ ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)),
    (subgroupCorank V U : ℕ∞)

/-- The source's local abbreviation `m`. -/
noncomputable def localM (V : Subgroup G) [IsElementaryAbelian 2 V] : ℕ :=
  moduleM (automizerRepresentation V)

/-- The source's local abbreviation `a`. -/
noncomputable def localA (V : Subgroup G) [IsElementaryAbelian 2 V] : ℕ∞ :=
  moduleA (automizerRepresentation V)

/-- E.3.5: `s = min(r,m)`, with the finite module parameter bounding `s`. -/
noncomputable def globalS (V : Subgroup G) [IsElementaryAbelian 2 V] : ℕ∞ :=
  min (globalR V) (localM V : ℕ∞)

theorem globalR_le_corank {V U : Subgroup G} (hUV : U ≤ V)
    (h : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)) :
    globalR V ≤ (subgroupCorank V U : ℕ∞) :=
  iInf_le_of_le U (iInf_le_of_le ⟨hUV, h⟩ le_rfl)

/-- Every subgroup of corank strictly below `r` has its centralizer in `N_G(V)`. -/
theorem centralizer_le_normalizer_of_corank_lt_globalR {V U : Subgroup G}
    (hUV : U ≤ V) (h : (subgroupCorank V U : ℕ∞) < globalR V) :
    centralizer (U : Set G) ≤ normalizer (V : Set G) := by
  by_contra hn
  exact (not_le_of_gt h) (globalR_le_corank hUV hn)

theorem globalR_eq_top_of_normal (V : Subgroup G) [V.Normal] : globalR V = ⊤ := by
  apply top_unique
  apply le_iInf
  intro U
  apply le_iInf
  rintro ⟨_, h⟩
  exact (h (by rw [Subgroup.normalizer_eq_top]; exact le_top)).elim

/-- The lower bound following E.3.3, including the empty-family case. -/
theorem one_le_globalR [Finite G] (V : Subgroup G) : 1 ≤ globalR V := by
  apply le_iInf
  intro U
  apply le_iInf
  rintro ⟨hUV, h⟩
  have hne : U.relIndex V ≠ 1 := by
    intro heq
    have heq' := le_antisymm hUV (Subgroup.relIndex_eq_one.mp heq)
    subst U
    exact h (centralizer_le_normalizer _)
  have hpos : U.relIndex V ≠ 0 := by
    intro hz
    have hdvd := U.relIndex_dvd_card V
    rw [hz, zero_dvd_iff] at hdvd
    exact Nat.card_pos.ne' hdvd
  have hlog : 1 ≤ subgroupCorank V U := Nat.log_pos (by decide) (by omega)
  exact_mod_cast hlog

theorem globalS_le_globalR (V : Subgroup G) [IsElementaryAbelian 2 V] :
    globalS V ≤ globalR V := min_le_left _ _

theorem globalS_le_localM (V : Subgroup G) [IsElementaryAbelian 2 V] :
    globalS V ≤ (localM V : ℕ∞) := min_le_right _ _

theorem globalS_ne_top (V : Subgroup G) [IsElementaryAbelian 2 V] : globalS V ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (globalS_le_localM V)

private theorem centralizer_map_equiv (U : Subgroup G) (e : G ≃* G) :
    (centralizer (U : Set G)).map e.toMonoidHom =
      centralizer (U.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

private theorem globalR_map_le (V : Subgroup G) (e : G ≃* G) :
    globalR (V.map e.toMonoidHom) ≤ globalR V := by
  apply le_iInf
  intro U
  apply le_iInf
  rintro ⟨hUV, h⟩
  have h' : ¬ centralizer (U.map e.toMonoidHom : Set G) ≤
      normalizer (V.map e.toMonoidHom : Set G) := by
    rw [← centralizer_map_equiv, ← map_equiv_normalizer_eq]
    intro hc
    exact h ((Subgroup.map_le_map_iff_of_injective e.injective).mp hc)
  have hi := globalR_le_corank (Subgroup.map_mono hUV) h'
  simpa only [subgroupCorank, Subgroup.relIndex_map_map_of_injective U V (f := e.toMonoidHom) e.injective] using hi

theorem globalR_map_equiv (V : Subgroup G) (e : G ≃* G) :
    globalR (V.map e.toMonoidHom) = globalR V := by
  apply le_antisymm (globalR_map_le V e)
  have h := globalR_map_le (V.map e.toMonoidHom) e.symm
  have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext x
    exact e.symm_apply_apply x
  simpa only [Subgroup.map_map, hcomp, Subgroup.map_id] using h

/-- E.3.4(1). The estimate only needs `B ≤ Vᵍ`; the source additionally
assumes that `B` normalizes `V`. -/
theorem globalR_le_conjugate_corank {V B : Subgroup G} (g : G)
    (hB : B ≤ V.map (MulAut.conj g).toMonoidHom)
    (h : ¬ V ⊓ centralizer (B : Set G) ≤
      normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    globalR V ≤ (subgroupCorank (V.map (MulAut.conj g).toMonoidHom) B : ℕ∞) := by
  rw [← globalR_map_equiv V (MulAut.conj g)]
  exact globalR_le_corank hB (fun hc => h (inf_le_right.trans hc))

/-- E.3.4(2): nonnormalizing conjugates supply witnesses for `r`. -/
theorem globalR_le_conjugate_centralizer_corank {V : Subgroup G} (g : G)
    (h : ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    globalR V ≤ (subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      ((V.map (MulAut.conj g).toMonoidHom) ⊓ centralizer (V : Set G)) : ℕ∞) := by
  rw [← globalR_map_equiv V (MulAut.conj g)]
  apply globalR_le_corank inf_le_left
  intro hc
  apply h
  exact (le_centralizer_iff.mpr inf_le_right).trans hc

/-- Infinity means precisely that the minimizing family is empty. -/
theorem globalR_eq_top_iff (V : Subgroup G) :
    globalR V = ⊤ ↔ ∀ U ≤ V, centralizer (U : Set G) ≤ normalizer (V : Set G) := by
  constructor
  · intro h U hUV
    by_contra hn
    have hle := globalR_le_corank hUV hn
    rw [h] at hle
    exact (by simp : ¬ (⊤ : ℕ∞) ≤ (subgroupCorank V U : ℕ∞)) hle
  · intro h
    apply top_unique
    apply le_iInf
    intro U
    apply le_iInf
    rintro ⟨hUV, hn⟩
    exact (hn (h U hUV)).elim

/-- The positivity observation following E.3.5. -/
theorem one_le_globalS [Finite G] (V : Subgroup G) [IsElementaryAbelian 2 V]
    (hV : V ≠ ⊥) : 1 ≤ globalS V := by
  let _ : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).mpr hV
  apply le_min (one_le_globalR V)
  exact_mod_cast moduleM_pos (automizerRepresentation V) (automizerRepresentation_injective V)

end CFSG.Quasithin.ChapterE
