module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.Generators.Hyperplanes
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.Residual
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Solvable
public import Theory.GroupTheory.TwoLocalCharacteristicControl

/-!
# Source 13.6.25 from the earlier marked A₅ setup

The actual quotient L/O₂(L) acts through the five-point coordinates, so
surjectivity gives the required A₅ orbits. The published 13.6.24 and the
escaping centralizer in 13.6.3 give r=3. The hyperplane argument puts every
corank-zero or corank-one generator in C_T(V)=O₂(LT). Weak closure inside
this normal intermediate subgroup proves Wᵢ ◁ LT without LT ≤ N_G(T).
It also gives w>1.

The E.3.35 input below is universal in V,T,M,H and the Sylow subgroup of H;
it retains uniqueness among maximal two-locals, C_H(V) ≤ M, and C_T(V) ≤ S.
Here uniqueness follows from the earlier uniqueness over LT, and the actual
ambient Sylow T supplies the relative Sylow of every overgroup H. Consequently
n(H)>1 holds on all of H(T,M), and every solvable member of H(T) lies in M.
The final theorem applies the latter to the literal residual consumer.

These are conditional source deductions. The setup contains earlier facts
from the FSU, 13.2.6, 13.3.2 and 13.6.2,3,7, with the actual A₅ quotient,
its conjugation action, and Hypothesis 13.3.1(4)'s uniform choice retained.
It contains none of the weak-closure or parameter conclusions. Its global
source applicability remains with Chapter 13 assembly. The independent
localA=1 producer is qt-13-06-source-five-module-a; the universal E.3.35
producer is qt-e-03. Both are discharged by the parent, not asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
E.3.35(1), printed pp.238–239; 13.6.24–26, printed pp.933–934.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters

open Subgroup Theory.GroupTheory
open _root_.CFSG.Quasithin.ChapterE
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G]

/-- The universal numeric implication of source E.3.35(1). Its solvable
specialization follows from the proved E.1.13. This is an explicit earlier
input, not an assertion that E.3.35 has been proved by this module. -/
def EarlierE335 : Prop :=
  ∀ (V : Subgroup G) [IsElementaryAbelian 2 V] (T : Sylow 2 G),
    HypothesisE322 V T → ∀ (M H : Subgroup G) (S : Sylow 2 H),
      maximalTwoLocalOvergroups (normalizer
        (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) = {M} →
      H ⊓ centralizer (V : Set G) ≤ M →
      (T : Subgroup G) ⊓ centralizer (V : Set G) ≤
        (S : Subgroup H).map H.subtype →
      (generationParameter H : ℕ∞) < min (globalW V (T : Subgroup G)) (globalR V) →
      H ≤ M

/-- Earlier local source data for the A₅ branch. LT is literally L ⊔ T,
and both normalizers, the quotient map and its actual action are retained.
The uniform-A₅ clause is exactly Hypothesis 13.3.1(4). The remaining fields
are earlier source facts, not conclusions of 13.6.25. -/
structure EarlierA5Setup (T : Sylow 2 G) (L V M MV : Subgroup G)
    [IsElementaryAbelian 2 V] where
  local_component : L ∈ MainForward.faithfulLocalComponents T
  quotient : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)
  uniform_A5 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∀ K ∈ MainForward.faithfulLocalComponents T,
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
  coordinates : FiveCoordinates V
  normalizes : L ⊔ (T : Subgroup G) ≤ normalizer (V : Set G)
  actor_quotient : ∀ l : L, coordinates.actor
      ⟨l.val, normalizes (show l.val ∈ L ⊔ (T : Subgroup G) from mem_sup_left l.property)⟩ =
      (quotient (QuotientGroup.mk' (pCore 2 L) l)).val
  module_le : V ≤ (T : Subgroup G)
  local_normalizer : M = normalizer (L : Set G)
  module_normalizer : MV = normalizer (V : Set G)
  normalizer_le : MV ≤ M
  unique_overgroup : maximalTwoLocalOvergroups (L ⊔ (T : Subgroup G)) = {M}
  centralizer_eq : (T : Subgroup G) ⊓ centralizer (V : Set G) =
    (L ⊔ (T : Subgroup G)).pCoreIn 2
  v : V
  z : V
  nonsingular : BinaryPermutation.FiveGeometry.form (coordinates.equiv v).toAdd ≠ 0
  z_nonidentity : z ≠ 1
  singular : BinaryPermutation.FiveGeometry.form (coordinates.equiv z).toAdd = 0
  fusion : ∀ x : V, x ≠ 1 → ∀ a : G, MulAut.conj a x.val ∈ V →
    ∃ n ∈ normalizer (V : Set G), MulAut.conj n x.val = MulAut.conj a x.val
  abelian_closure : IsMulCommutative (centralizerConjugateClosure V z.val)
  nonsingular_centralizer : centralizer ({v.val} : Set G) ≤ MV
  singular_escape : ¬ centralizer ({z.val} : Set G) ≤ M

namespace EarlierA5Setup
variable {T : Sylow 2 G} {L V M MV : Subgroup G} [IsElementaryAbelian 2 V]
    (s : EarlierA5Setup T L V M MV)

include s

omit [Finite G] in
/-- The actual quotient action supplies A₅ in the normalizer actor image. -/
theorem alternating_le_actor : alternatingGroup (Fin 5) ≤ s.coordinates.actor.range := by
  intro a ha
  obtain ⟨q, hq⟩ := s.quotient.surjective ⟨a, ha⟩
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  refine ⟨⟨l.val, s.normalizes (mem_sup_left l.property)⟩, ?_⟩
  rw [s.actor_quotient, hl, hq]

omit [Finite G] in
theorem module_ne_bot : V ≠ ⊥ := by
  intro h
  exact s.z_nonidentity (Subtype.ext (mem_bot.mp (h ▸ s.z.property)))

omit [Finite G] in
/-- E.3.22 uses normality in the actual Sylow, not ambient normality. -/
theorem hypothesisE322 : HypothesisE322 V T :=
  ⟨s.module_ne_bot, s.module_le, le_sup_right.trans s.normalizes⟩

omit [Finite G] in
/-- The source commuting-conjugate result, with all its earlier premises
instantiated in the actual marked module. -/
theorem commuting_conjugates (g : G) (hg : g ∉ normalizer (V : Set G))
    (hi : V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  let := s.abelian_closure
  exact (source_13_6_24_from_earlier V s.coordinates.equiv s.v s.z
    s.nonsingular s.z_nonidentity s.singular (s.coordinates.orbits s.alternating_le_actor)
    s.fusion (s.module_normalizer ▸ s.nonsingular_centralizer) g hg hi).2.2

/-- No r-bound is assumed: its value is supplied by the published coordinate proof. -/
theorem globalR_eq_three : globalR V = 3 := by
  let := s.abelian_closure
  exact globalR_eq_three_from_coordinates s.coordinates M s.v s.z
    s.nonsingular s.z_nonidentity s.singular s.alternating_le_actor s.fusion
    (s.module_normalizer ▸ s.nonsingular_centralizer)
    (s.module_normalizer ▸ s.normalizer_le) s.singular_escape

/-- Uniqueness over LT transfers to the literal Q=C_T(V)=O₂(LT). -/
theorem unique_over_core_normalizer :
    maximalTwoLocalOvergroups
      (normalizer (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) = {M} := by
  have hmem : M ∈ maximalTwoLocalOvergroups (L ⊔ (T : Subgroup G)) :=
    s.unique_overgroup.symm ▸ Set.mem_singleton M
  have hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M := by
    intro N hN hLN
    exact Set.mem_singleton_iff.mp (s.unique_overgroup ▸ ⟨hN, hLN⟩)
  have hVQ : V ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [← s.centralizer_eq]
    exact le_inf s.module_le (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hQ : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≠ ⊥ := by
    intro h
    exact s.module_ne_bot (le_bot_iff.mp (hVQ.trans_eq h))
  rw [s.centralizer_eq]
  exact unique_twoLocal_overgroup_normalizer
    (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))) hQ
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))) hmem.1 hu

/-- The complete generator conclusion for the two source indices. -/
theorem generator_central (ha : localA V = 1) {i : ℕ} (hi : i = 0 ∨ i = 1)
    {A : Subgroup G} (hA : A ∈ conjugateCorankFamily V i) (hAT : A ≤ (T : Subgroup G)) :
    A ≤ centralizer (V : Set G) :=
  Generators.generator_central s.hypothesisE322.normalizes s.globalR_eq_three ha
    s.commuting_conjugates (by omega) hA hAT

/-- Containment and relative normality, using the normal intermediate core. -/
theorem weakClosure_core_and_normal (ha : localA V = 1)
    {i : ℕ} (hi : i = 0 ∨ i = 1) :
    indexedWeakClosure V (T : Subgroup G) i ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
    Chapter3.NormalIn (indexedWeakClosure V (T : Subgroup G) i) (L ⊔ (T : Subgroup G)) := by
  have hW : indexedWeakClosure V (T : Subgroup G) i ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [← s.centralizer_eq]
    exact Generators.weakClosure_le_centralizer s.hypothesisE322.normalizes
      s.globalR_eq_three ha s.commuting_conjugates (by omega)
  exact ⟨hW, weakClosure_normalIn_of_centralizer_eq_twoCore V (T : Subgroup G)
    (L ⊔ (T : Subgroup G)) i s.centralizer_eq hW⟩

theorem globalW_gt_one (ha : localA V = 1) : 1 < globalW V (T : Subgroup G) :=
  Generators.globalW_gt_one s.hypothesisE322.normalizes s.globalR_eq_three ha
    s.commuting_conjugates

/-- Every premise of the universal E.3.35 implication is discharged here.
The relative Sylow is T.subtype hTH, whose ambient image is exactly T. -/
theorem le_of_generationParameter_lt (he : EarlierE335 (G := G))
    {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hn : (generationParameter H : ℕ∞) <
      min (globalW V (T : Subgroup G)) (globalR V)) : H ≤ M := by
  apply he V T s.hypothesisE322 M H (T.subtype hTH) s.unique_over_core_normalizer
  · exact inf_le_right.trans ((centralizer_le_normalizer _).trans
      (s.module_normalizer ▸ s.normalizer_le))
  · simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      (show (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ (T : Subgroup G) from inf_le_left)
  · exact hn

/-- Source 13.6.25(2) uses all of H(T,M), with no minimality restriction. -/
theorem generationParameter_gt_one (ha : localA V = 1) (he : EarlierE335 (G := G))
    {H : Subgroup G} (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G)) :
    1 < generationParameter H := by
  by_contra hn
  have hle : generationParameter H ≤ 1 := by omega
  apply hH.2
  apply s.le_of_generationParameter_lt he hH.1.2
  apply lt_min
  · exact lt_of_le_of_lt (by exact_mod_cast hle) (s.globalW_gt_one ha)
  · rw [s.globalR_eq_three]
    exact lt_of_le_of_lt (show (generationParameter H : ℕ∞) ≤ 1 by exact_mod_cast hle)
      (by norm_num)

/-- Source 13.6.25(3), literally the contract consumed by Residual. -/
theorem solvable_HOver_le (ha : localA V = 1) (he : EarlierE335 (G := G)) :
    ∀ H ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable H → H ≤ M := by
  intro H hH hsolv
  let := hsolv
  by_contra hn
  have hgt := s.generationParameter_gt_one ha he ⟨hH, hn⟩
  exact (not_lt_of_ge (generationParameter_le_one_of_solvable (G := H))) hgt

end EarlierA5Setup

/-- All four assertions of 13.6.25, from earlier source facts and the two
independently owned earlier inputs. The extra core containment is retained
for later consumers. -/
theorem source_13_6_25_from_earlier
    {T : Sylow 2 G} {L V M MV : Subgroup G} [IsElementaryAbelian 2 V]
    (s : EarlierA5Setup T L V M MV) (ha : localA V = 1) (he : EarlierE335 (G := G)) :
    (∀ i : ℕ, i = 0 ∨ i = 1 →
      indexedWeakClosure V (T : Subgroup G) i ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      Chapter3.NormalIn (indexedWeakClosure V (T : Subgroup G) i) (L ⊔ (T : Subgroup G))) ∧
    (∀ H ∈ Chapter1.HOutside G (T : Set G) (M : Set G), 1 < generationParameter H) ∧
    (∀ H ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable H → H ≤ M) ∧
    globalR V = 3 ∧ 1 < globalW V (T : Subgroup G) :=
  ⟨fun _ hi => s.weakClosure_core_and_normal ha hi,
    fun _ hH => s.generationParameter_gt_one ha he hH,
    s.solvable_HOver_le ha he, s.globalR_eq_three, s.globalW_gt_one ha⟩

/-- Actual residual consumer: the solvable subgroup XT is placed in M by
13.6.25(3), with its literal quotient and prime-to-p residual conventions. -/
theorem source_13_6_26_2_from_generators
    {T : Sylow 2 G} {L V M MV : Subgroup G} [IsElementaryAbelian 2 V]
    (s : EarlierA5Setup T L V M MV) (ha : localA V = 1) (he : EarlierE335 (G := G))
    (h1338 : Earlier1338Two T) (L₁ G₁ : Subgroup G)
    {H : Subgroup G} (hH : H ∈ Chapter13.Section08.Source.Hz L₁ (T : Subgroup G) G₁ M)
    (p : ℕ) [Fact p.Prime] (hp : 3 < p) : O2p H p = Chapter13.Section08.Source.QH H := by
  exact source_13_6_26_2_of_13_6_25_3 T L L₁ G₁ M s.local_component
    s.local_normalizer h1338 (s.solvable_HOver_le ha he) hH p hp

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
