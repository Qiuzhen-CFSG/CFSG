module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer.Models
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Statements
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Maximal
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Transport
public import Theory.GroupTheory.SolvableSylowControl.AbelianProduct
public import Theory.GroupTheory.SolvableSylowControl.SolvableImage
public import Theory.NumberTheory.BinarySemilinearTorusDivisors

/-!
# Cartan witnesses in the original natural-layer Sylow normalizer

An odd abelian subgroup permuting with an ambient Sylow has solvable join.
The concrete nonbinary model control therefore puts that entire join in the
normalizer of its intersection with the original layer. The action kernel on
any enlargement of V is contained in O₂(L), so this works on both V and V_M
without splitting the covering module. The final arithmetic reduction uses
the order of the actual cyclic Cartan subgroup, not a module dimension.

Source: Aschbacher--Smith A.3.15(5), E.3.37 and 11.2.1,
printed pp.50--51,239,766--767. The weak-closure owner retains the remaining
semilinear exponent calculation and the final generation assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer

variable {X : Type*} [Group X] [Finite X]

/-- The whole Cartan product normalizes its original layer Sylow intersection. -/
theorem witness_normalizes_layer_sylow (K : Subgroup X) [K.Normal]
    (hK : SolvableSylowControl 2 K) {c : ℕ} (w : NPrimeWitness X c) :
    w.abelianGroup ⊔ (w.sylow : Subgroup X) ≤
      normalizer ((w.sylow : Subgroup X) ⊓ K : Set X) := by
  let := w.abelian
  exact odd_abelian_permuting_normalizes_layer_sylow K w.abelianGroup
    w.sylow w.odd w.permutes hK

/-- Restrict the complete witness to that literal normalizer. -/
def normalizerWitness (K : Subgroup X) [K.Normal]
    (hK : SolvableSylowControl 2 K) {c : ℕ} (w : NPrimeWitness X c) :
    NPrimeWitness (normalizer ((w.sylow : Subgroup X) ⊓ K : Set X)) c :=
  MarkedModels.restrictWitness w _
    (le_sup_left.trans (witness_normalizes_layer_sylow K hK w))
    (le_sup_right.trans (witness_normalizes_layer_sylow K hK w))

/-- An odd exponent bound on the layer Sylow normalizer bounds the Cartan parameter. -/
theorem nPrime_le_of_normalizer_exponent (K : Subgroup X) [K.Normal]
    (hK : SolvableSylowControl 2 K) {n : ℕ} (hn : 0 < n)
    (hexp : ∀ (P : Sylow 2 X) (a : X),
      a ∈ normalizer ((P : Subgroup X) ⊓ K : Set X) →
      Odd (orderOf a) → a ^ (n * (2 ^ n - 1)) = 1) : nPrime X ≤ n := by
  apply nPrime_le_iff.mpr
  intro c w
  let := w.cyclic
  obtain ⟨a,ha⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp
    (inferInstance : IsCyclic w.cyclicGroup)
  have ho : Odd (orderOf (a : X)) := by
    rw [Subgroup.orderOf_coe, ha]
    exact w.odd.of_dvd_nat (card_dvd_of_le w.cyclic_le)
  have hmem : (a : X) ∈ normalizer ((w.sylow : Subgroup X) ⊓ K : Set X) :=
    witness_normalizes_layer_sylow K hK w (mem_sup_left (w.cyclic_le a.property))
  have hd := orderOf_dvd_of_pow_eq_one (hexp w.sylow a hmem ho)
  rw [Subgroup.orderOf_coe, ha, w.card] at hd
  exact Theory.NumberTheory.binary_mersenne_exponent_le_of_semilinear_torus_dvd hn hd

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

include D S

/-- The original component inherits control through its two-core quotient. -/
theorem component_solvable_sylow_control : SolvableSylowControl 2 L := by
  let c := coordinates D S
  apply SolvableSylowControl.of_surjective_pKernel (QuotientGroup.mk' (pCore 2 L))
    (QuotientGroup.mk'_surjective _)
  · rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  · exact SolvableSylowControl.of_equiv c.groupEquiv (model_solvable_sylow_control D S c)

/-- Every action kernel on an enlargement of V is contained in the original two-core. -/
theorem enlarged_action_kernel_le_core {U : Subgroup G} (hVU : V ≤ U)
    (hLU : L ≤ normalizer (U : Set G)) :
    (localAction U L hLU).ker ≤ pCore 2 L := by
  let c := coordinates D S
  intro l hl
  have hC := (mem_ker_localAction U L hLU l).mp hl
  have hV : localAction V L D.normalizes l = 1 :=
    (mem_ker_localAction V L D.normalizes l).mpr (centralizer_le hVU hC)
  have hq := (Parameters.FullAutomizer.layerAction_eq_one_iff D S c l).mp hV
  apply (QuotientGroup.eq_one_iff l).mp
  apply c.groupEquiv.injective
  exact hq.trans c.groupEquiv.map_one.symm

/-- The image on an enlargement retains solvable Sylow control. -/
theorem enlarged_layer_solvable_sylow_control {U : Subgroup G} (hVU : V ≤ U)
    (hLU : L ≤ normalizer (U : Set G)) :
    SolvableSylowControl 2 (inducedAutomizer U L) := by
  have hp : IsPGroup 2 (localAction U L hLU).ker :=
    pCore_isPGroup.of_injective (inclusion (enlarged_action_kernel_le_core D S hVU hLU))
      (inclusion_injective _)
  let := hp.isNilpotent
  exact SolvableSylowControl.of_surjective_solvable_kernel
    (localAction U L hLU) (localAction_surjective U L hLU)
    (component_solvable_sylow_control D S)

/-- Control in the relative image inside the actual ambient automizer. -/
theorem relative_layer_solvable_sylow_control {U J : Subgroup G}
    (hVU : V ≤ U) (hLJ : L ≤ J) (hJU : J ≤ normalizer (U : Set G)) :
    SolvableSylowControl 2 ((inducedAutomizer U L).subgroupOf (inducedAutomizer U J)) :=
  SolvableSylowControl.of_equiv
    (subgroupOfEquivOfLe (show inducedAutomizer U L ≤ inducedAutomizer U J from
      map_mono (comap_mono hLJ)))
    (enlarged_layer_solvable_sylow_control D S hVU (hLJ.trans hJU))

/-- The actual Cartan product on V or V_M normalizes its relative layer Sylow. -/
theorem actual_witness_normalizes_layer_sylow {U J : Subgroup G}
    (hVU : V ≤ U) (hLJ : L ≤ J) (hJU : J ≤ normalizer (U : Set G))
    (hJL : J ≤ normalizer (L : Set G))
    {c : ℕ} (w : NPrimeWitness (inducedAutomizer U J) c) :
    w.abelianGroup ⊔ (w.sylow : Subgroup (inducedAutomizer U J)) ≤ normalizer
      ((w.sylow : Subgroup (inducedAutomizer U J)) ⊓
        (inducedAutomizer U L).subgroupOf (inducedAutomizer U J) : Set (inducedAutomizer U J)) := by
  let hLN : (L.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJL
  let := inducedAutomizer_normal_in hLJ hJU hLN
  exact witness_normalizes_layer_sylow _ (relative_layer_solvable_sylow_control D S hVU hLJ hJU) w

/-- Apply the Cartan reduction on the literal action of J on an enlargement of V. -/
theorem actual_nPrime_le_of_normalizer_exponent {U J : Subgroup G}
    (hVU : V ≤ U) (hLJ : L ≤ J) (hJU : J ≤ normalizer (U : Set G))
    (hJL : J ≤ normalizer (L : Set G)) {n : ℕ} (hn : 0 < n)
    (hexp : ∀ (P : Sylow 2 (inducedAutomizer U J)) (a : inducedAutomizer U J),
      a ∈ normalizer ((P : Subgroup (inducedAutomizer U J)) ⊓
        (inducedAutomizer U L).subgroupOf (inducedAutomizer U J) :
          Set (inducedAutomizer U J)) →
      Odd (orderOf a) → a ^ (n * (2 ^ n - 1)) = 1) :
    nPrime (inducedAutomizer U J) ≤ n := by
  let hLN : (L.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJL
  let := inducedAutomizer_normal_in hLJ hJU hLN
  exact nPrime_le_of_normalizer_exponent _
    (relative_layer_solvable_sylow_control D S hVU hLJ hJU) hn hexp

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer
