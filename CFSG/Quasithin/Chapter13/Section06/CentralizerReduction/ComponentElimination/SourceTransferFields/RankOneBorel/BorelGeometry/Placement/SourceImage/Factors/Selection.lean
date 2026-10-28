module

public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Algebra.Group.Pi.Basic
public import Lean.Elab.Tactic.Omega

/-!
# Selecting a factor above a simple two-residual

If a simple subgroup contains O²(Y), every nontrivial O² of a normal direct
factor lies in that subgroup. Simplicity makes the intersection the whole
simple subgroup. Pairwise disjointness then excludes two factors.
The internal product and its coordinate embeddings are retained explicitly.

Source application: Aschbacher–Smith, E.2.3(1), printed pp.216–217,
in the rank-one argument of 13.6.18, printed p.931.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceFactors
/-- An internal direct product with its literal factor embeddings. Normality,
disjointness and generation are retained as convenient consequences of the
internal product, so clients need not reconstruct them from coordinates. -/
structure InternalFactors (Y : Type*) [Group Y] where
  size : ℕ
  size_cases : size = 1 ∨ size = 2
  factor : Fin size → Subgroup Y
  normal : ∀ i, (factor i).Normal
  disjoint : Pairwise (fun i j => Disjoint (factor i) (factor j))
  generate : (⨆ i, factor i) = ⊤
  product : (∀ i, factor i) ≃* Y
  product_single : ∀ i x, product (Pi.mulSingle i x) = (x : Y)

variable {Y : Type*} [Group Y] (d : InternalFactors Y)

/-- A simple subgroup containing the ambient two-residual contains the
nontrivial residual of each normal factor, and hence lies in that factor. -/
theorem residual_le_factor (N : Subgroup Y) [IsSimpleGroup N]
    (hres : pResidual 2 Y ≤ N) (i : Fin d.size)
    (hx : ∃ x : d.factor i, x ≠ 1 ∧ Nat.Coprime 2 (orderOf x)) :
    N ≤ d.factor i := by
  let Q := (pResidual 2 (d.factor i)).map (d.factor i).subtype
  let : (d.factor i).Normal := d.normal i
  have hQN : Q ≤ N := (map_pResidual_le 2 _).trans hres
  have hQf : Q ≤ d.factor i := map_subtype_le _
  have hQne : Q ≠ ⊥ := by
    obtain ⟨x, hxne, hxc⟩ := hx
    intro he
    have hxm : (x : Y) ∈ Q := mem_map_of_mem _ (mem_pResidual_of_orderOf_coprime hxc)
    rw [he, mem_bot] at hxm
    exact hxne (Subtype.ext hxm)
  let : Q.Normal := inferInstance
  have htop : Q.subgroupOf N = ⊤ := by
    apply (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Q.subgroupOf N) inferInstance).resolve_left
    intro hbot
    apply hQne
    rw [← map_subgroupOf_eq_of_le hQN, hbot, Subgroup.map_bot]
  intro n hn
  apply hQf
  have hnQ : (⟨n, hn⟩ : N) ∈ Q.subgroupOf N := by rw [htop]; trivial
  exact hnQ

/-- Two distinct direct factors cannot both contain this nontrivial simple
subgroup. This selects a single factor, rather than assuming one. -/
theorem size_eq_one (N : Subgroup Y) [IsSimpleGroup N]
    (hres : pResidual 2 Y ≤ N)
    (hx : ∀ i, ∃ x : d.factor i, x ≠ 1 ∧ Nat.Coprime 2 (orderOf x)) :
    d.size = 1 := by
  rcases d.size_cases with h | h
  · exact h
  · exfalso
    let i : Fin d.size := ⟨0, by omega⟩
    let j : Fin d.size := ⟨1, by omega⟩
    have hij : i ≠ j := by intro he; have := congrArg Fin.val he; dsimp [i, j] at this; omega
    have hn : N ≤ ⊥ := by
      have hd := (d.disjoint hij).le_bot
      exact (le_inf (residual_le_factor d N hres i (hx i))
        (residual_le_factor d N hres j (hx j))).trans hd
    exact (N.nontrivial_iff_ne_bot.mp inferInstance) (bot_unique hn)

/-- The selected factor is the whole product group. -/
theorem unique_factor_top (h : d.size = 1) (i : Fin d.size) : d.factor i = ⊤ := by
  apply top_unique
  rw [← d.generate]
  apply iSup_le
  intro j
  have he : j = i := Fin.ext (by have := j.isLt; have := i.isLt; omega)
  rw [he]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceFactors

end
