module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits.TableSupport
public import Theory.GroupTheory.SubgroupClosureFinite
import Mathlib.Tactic.FinCases

/-!
# A marked odd Sylow configuration in J₂

Explicit words in the original ATLAS generators give a subgroup of order
25 and an ambient inverter. Small transition tables prove coverage;
a single point separates the normal forms. All permutation identities and
word comparisons are checked by Lean's kernel.

Source: Aschbacher–Smith I.1.3(1), printed p.407, GLS3 §6.1.
Permutation data: ATLAS J2G1-p100B0, with attribution retained in
Theory/SpecificGroups/LeechRelated/AtlasCarriers/source/. Discovery scripts
and regeneration data are in the adjacent source directory; they are not
proof oracles. The resulting configuration feeds the perfect-cover transfer
argument in J2UpperBound.OddPrimary.
-/

@[expose] public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2.UpperBound.OddLocal.Five
open Sporadic.LeechRelated.J2 GeneratorPair GeneratorPair.SecondOrbitCertificate
open Theory.GroupTheory Subgroup
open scoped commutatorElement

set_option maxRecDepth 20000

private theorem checkFin_true {n : ℕ} (f : Fin n → Bool)
    (h : checkFin f = true) (i : Fin n) : f i = true := by
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt] using hi

private theorem allFin₂ {n m : ℕ} (P : Fin n → Fin m → Prop)
    [∀ i j, Decidable (P i j)]
    (h : checkFin (fun i => checkFin (fun j => decide (P i j))) = true) :
    ∀ i j, P i j := by
  intro i
  exact allFin _ (checkFin_true _ h i)

private theorem allFin₃ {n m l : ℕ} (P : Fin n → Fin m → Fin l → Prop)
    [∀ i j k, Decidable (P i j k)]
    (h : checkFin (fun i => checkFin (fun j => checkFin (fun k => decide (P i j k)))) = true) :
    ∀ i j k, P i j k := by
  intro i
  exact allFin₂ _ (checkFin_true _ h i)

private def fastA : Equiv.Perm (Fin 100) where
  toFun := packedMap 470534163730062869911363024468043625726304620038018037366950930285973911676205782046213865496771569892128340730334015622028359153083123020292251731884913318734969411873230468091871540321808628302024410068142547
  invFun := packedMap 470534163730062869911363024468043625726304620038018037366950930285973911676205782046213865496771569892128340730334015622028359153083123020292251731884913318734969411873230468091871540321808628302024410068142547
  left_inv := by apply allFin; decide +kernel
  right_inv := by apply allFin; decide +kernel

private theorem fastA_eq : tableA = fastA := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private def fastB : Equiv.Perm (Fin 100) where
  toFun := packedMap 3234967701574023288017704270913789399548845676982065206373928870228913752386975839948414443758577378205229365791802719998856417312117905715024748407215049785228781853510609863692219811450715825262485969147626773
  invFun := packedMap 3377862216939204608209019933455681426219024363596881756892669536352030827785925351345362563460844105849526589246761354822075856259740605599629990671129056314103711580268098197814694108667979975332570640941909071
  left_inv := by apply allFin; decide +kernel
  right_inv := by apply allFin; decide +kernel

private theorem fastB_eq : tableB = fastB := by
  apply Equiv.ext
  apply allFin
  decide +kernel

def xWord : List (Fin 3) := [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0]
def x : Carrier := evalWord ![a, b, b⁻¹] xWord
private def xTable : Equiv.Perm (Fin 100) where
  toFun := packedMap 1335357000877646785566193815263779355671435455113912620348342603978473676920397786007005339408150961946444518367228508469088886131493128313753339933474888413437193707923286063280870537893165232991063882407942457
  invFun := packedMap 2817968705578134610616339031002514266145912978124065124526186138441273609538227646067563772653235549035149529457760412600242271980070028118935806778272904173457750903696833415156901837105428259396972787654396984
  left_inv := by apply allFin; decide +kernel
  right_inv := by apply allFin; decide +kernel

private theorem x_table : inclusion x = xTable := by
  change evalWord ![generatorA, generatorB, generatorB⁻¹] xWord = xTable
  rw [generatorA_eq_table, generatorB_eq_table, fastA_eq, fastB_eq]
  apply Equiv.ext
  apply allFin
  decide +kernel

def yWord : List (Fin 3) := [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 1]
def y : Carrier := evalWord ![a, b, b⁻¹] yWord
private def yTable : Equiv.Perm (Fin 100) where
  toFun := packedMap 333116507897720688842746771166660882793645004374564089308203312849978193721244466282995124028163980137885332168715584784092570712709496882986227598852218831697569931872370140319046167781392199291377713835001395
  invFun := packedMap 217866304104256973905065549486734790477084435377158356165710948421628775834681402701287070527000808141724282355078855630983527254682906177127017384073569744580160332323459145314884188787510644855855410722316432
  left_inv := by apply allFin; decide +kernel
  right_inv := by apply allFin; decide +kernel

private theorem y_table : inclusion y = yTable := by
  change evalWord ![generatorA, generatorB, generatorB⁻¹] yWord = yTable
  rw [generatorA_eq_table, generatorB_eq_table, fastA_eq, fastB_eq]
  apply Equiv.ext
  apply allFin
  decide +kernel

def rWord : List (Fin 3) := [0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1]
def r : Carrier := evalWord ![a, b, b⁻¹] rWord
private def rTable : Equiv.Perm (Fin 100) where
  toFun := packedMap 1346674128207290768493924302952693161184194416198632350711025559314387046123736118675848834793230029901068777155397475451062707632236731795584610186362544400415595497352682633277192861619334979993794292850577024
  invFun := packedMap 1346674128207290768493924302952693161184194416198632350711025559314387046123736118675848834793230029901068777155397475451062707632236731795584610186362544400415595497352682633277192861619334979993794292850577024
  left_inv := by apply allFin; decide +kernel
  right_inv := by apply allFin; decide +kernel

private theorem r_table : inclusion r = rTable := by
  change evalWord ![generatorA, generatorB, generatorB⁻¹] rWord = rTable
  rw [generatorA_eq_table, generatorB_eq_table, fastA_eq, fastB_eq]
  apply Equiv.ext
  apply allFin
  decide +kernel

theorem x_pow : x ^ 5 = 1 := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  simp only [map_pow, map_one, x_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

theorem y_pow : y ^ 5 = 1 := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  simp only [map_pow, map_one, y_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

theorem r_inverts_x : r * x * r⁻¹ = x⁻¹ := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  simp only [map_mul, map_inv, r_table, x_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

theorem x_commute_y : Commute x y := by
  change x * y = y * x
  apply Sporadic.LeechRelated.J2.inclusion_injective
  simp only [map_mul, x_table, y_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

theorem r_commute_y : Commute r y := by
  change r * y = y * r
  apply Sporadic.LeechRelated.J2.inclusion_injective
  simp only [map_mul, r_table, y_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

def P : Subgroup Carrier := closure ({x, y} : Set Carrier)
private def generators : Fin 2 → Carrier := ![x, y]
private def reps (i : Fin 25) : Carrier := x ^ (i.val / 5) * y ^ (i.val % 5)
private def repsTable (i : Fin 25) : Equiv.Perm (Fin 100) := xTable ^ (i.val / 5) * yTable ^ (i.val % 5)
private theorem reps_table (i : Fin 25) : inclusion (reps i) = repsTable i := by
  simp only [reps, repsTable, map_mul, map_pow, x_table, y_table]

private def next : Fin 25 → Fin 2 → Fin 25 :=
  ![![5, 1], ![6, 2], ![7, 3], ![8, 4], ![9, 0], ![10, 6], ![11, 7], ![12, 8], ![13, 9], ![14, 5], ![15, 11], ![16, 12], ![17, 13], ![18, 14], ![19, 10], ![20, 16], ![21, 17], ![22, 18], ![23, 19], ![24, 15], ![0, 21], ![1, 22], ![2, 23], ![3, 24], ![4, 20]]
private def prev : Fin 25 → Fin 2 → Fin 25 :=
  ![![20, 4], ![21, 0], ![22, 1], ![23, 2], ![24, 3], ![0, 9], ![1, 5], ![2, 6], ![3, 7], ![4, 8], ![5, 14], ![6, 10], ![7, 11], ![8, 12], ![9, 13], ![10, 19], ![11, 15], ![12, 16], ![13, 17], ![14, 18], ![15, 24], ![16, 20], ![17, 21], ![18, 22], ![19, 23]]
private theorem transitions (i : Fin 25) (j : Fin 2) :
    reps i * generators j = reps (next i j) := by
  have hg : inclusion (generators j) = (![xTable, yTable] : Fin 2 → _) j := by
    fin_cases j
    · exact x_table
    · exact y_table
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_mul, reps_table, reps_table, hg]
  clear hg
  apply Equiv.ext
  revert i j
  apply allFin₃
  decide +kernel

private theorem index_inverse : ∀ i j, next (prev i j) j = i := by
  apply allFin₂
  decide +kernel

private def point : Fin 25 → Fin 100 := ![0, 51, 74, 88, 16, 57, 94, 55, 61, 82, 81, 96, 62, 39, 9, 77, 69, 95, 43, 86, 56, 23, 52, 54, 35]

private theorem reps_point (i : Fin 25) : inclusion (reps i) 0 = point i := by
  rw [reps_table]
  revert i
  apply allFin
  decide +kernel

private theorem reps_injective : Function.Injective reps := by
  have hpt : Function.Injective point := by
    apply allFin₂
    decide +kernel
  intro i j h
  apply hpt
  rw [← reps_point, ← reps_point, h]

private theorem reps_mem (i : Fin 25) : reps i ∈ P := by
  have hx : x ∈ P := subset_closure (by simp)
  have hy : y ∈ P := subset_closure (by simp)
  exact P.mul_mem (P.pow_mem hx _) (P.pow_mem hy _)

/-- Cardinality of the literal generated subgroup, with complete coverage. -/
theorem card_P : Nat.card P = 25 := by
  have hgen : ({x, y} : Set Carrier) = Set.range generators := by
    ext g
    simp [generators, or_comm]
  let e : Fin 25 → P := fun i => ⟨reps i, reps_mem i⟩
  have hi : Function.Injective e := fun i j h => reps_injective (congrArg Subtype.val h)
  have hs : Function.Surjective e := by
    intro g
    have hg : g.val ∈ closure (Set.range generators) := by
      simpa only [← hgen, P] using g.property
    obtain ⟨i, he⟩ := SubgroupEnumeration.closure_range_subset_range_of_transitions
      generators reps 0 next prev (by simp [reps]) transitions index_inverse hg
    exact ⟨i, Subtype.ext he⟩
  calc
    Nat.card P = Nat.card (Fin 25) := Nat.card_congr (Equiv.ofBijective e ⟨hi, hs⟩).symm
    _ = 25 := Nat.card_fin _

end Theory.SpecificGroups.J2HSMultipliers.J2.UpperBound.OddLocal.Five
