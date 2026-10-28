module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits.TableSupport
public import Theory.GroupTheory.SubgroupClosureFinite
import Mathlib.Tactic.FinCases

/-!
# A marked odd Sylow configuration in J₂

Explicit words in the original ATLAS generators give a subgroup of order
27 and an ambient inverter. Small transition tables prove coverage;
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
namespace Theory.SpecificGroups.J2HSMultipliers.J2.UpperBound.OddLocal.Three
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

def xWord : List (Fin 3) := [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0]
def x : Carrier := evalWord ![a, b, b⁻¹] xWord
private def xTable : Equiv.Perm (Fin 100) where
  toFun := packedMap 1166422140678029045824788618358742553087896066124450935881299451974507560190204699048908093455063552193725964321552437973310355927545277644612911098109021023897129964085980931159961592201715026309853655881118080
  invFun := packedMap 61818170434501880512913960878634266825475085499825614381426040722839148326902207583555310014740110883931477559484321655481427491010219745706534687416273728848353640870635663043220512118482134578806032316124672
  left_inv := by apply allFin; decide +kernel
  right_inv := by apply allFin; decide +kernel

private theorem x_table : inclusion x = xTable := by
  change evalWord ![generatorA, generatorB, generatorB⁻¹] xWord = xTable
  rw [generatorA_eq_table, generatorB_eq_table, fastA_eq, fastB_eq]
  apply Equiv.ext
  apply allFin
  decide +kernel

def yWord : List (Fin 3) := [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2]
def y : Carrier := evalWord ![a, b, b⁻¹] yWord
private def yTable : Equiv.Perm (Fin 100) where
  toFun := packedMap 804472164276747045510973585713504989736030762782125814553377049055842276098323819895672420469269393118491590544053488949169415327197953100155483591620120316585440946773478670458216792112124340891975132031443712
  invFun := packedMap 1952990990553004511658654678487905721196216138459440469815118636358728371366373930014564294342527080584743385321164275193406813088634033765687830241164511078126200243822329055825948463257605936326036549698408704
  left_inv := by apply allFin; decide +kernel
  right_inv := by apply allFin; decide +kernel

private theorem y_table : inclusion y = yTable := by
  change evalWord ![generatorA, generatorB, generatorB⁻¹] yWord = yTable
  rw [generatorA_eq_table, generatorB_eq_table, fastA_eq, fastB_eq]
  apply Equiv.ext
  apply allFin
  decide +kernel

def rWord : List (Fin 3) := [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0]
def r : Carrier := evalWord ![a, b, b⁻¹] rWord
private def rTable : Equiv.Perm (Fin 100) where
  toFun := packedMap 1182195016523508587941804434251445235715175970073165450235043368013691442226537177326151583239734073289992003030306006200133834232362997606576162455468456102328914600976181000311554949264758866236565751034101888
  invFun := packedMap 1182195016523508587941804434251445235715175970073165450235043368013691442226537177326151583239734073289992003030306006200133834232362997606576162455468456102328914600976181000311554949264758866236565751034101888
  left_inv := by apply allFin; decide +kernel
  right_inv := by apply allFin; decide +kernel

private theorem r_table : inclusion r = rTable := by
  change evalWord ![generatorA, generatorB, generatorB⁻¹] rWord = rTable
  rw [generatorA_eq_table, generatorB_eq_table, fastA_eq, fastB_eq]
  apply Equiv.ext
  apply allFin
  decide +kernel

theorem x_pow : x ^ 3 = 1 := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  simp only [map_pow, map_one, x_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

theorem y_pow : y ^ 3 = 1 := by
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

theorem r_inverts_y : r * y * r⁻¹ = y⁻¹ := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  simp only [map_mul, map_inv, r_table, y_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

theorem x_commute_commutator : Commute x ⁅x, y⁆ := by
  change x * ⁅x, y⁆ = ⁅x, y⁆ * x
  apply Sporadic.LeechRelated.J2.inclusion_injective
  simp only [map_mul, map_commutatorElement, x_table, y_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

theorem y_commute_commutator : Commute y ⁅x, y⁆ := by
  change y * ⁅x, y⁆ = ⁅x, y⁆ * y
  apply Sporadic.LeechRelated.J2.inclusion_injective
  simp only [map_mul, map_commutatorElement, x_table, y_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

theorem r_commute_commutator : Commute r ⁅x, y⁆ := by
  change r * ⁅x, y⁆ = ⁅x, y⁆ * r
  apply Sporadic.LeechRelated.J2.inclusion_injective
  simp only [map_mul, map_commutatorElement, x_table, y_table, r_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

theorem commutator_ne_one : ⁅x, y⁆ ≠ 1 := by
  intro h
  have ht := congrArg (fun g : Carrier => inclusion g 1) h
  have hn : inclusion ⁅x, y⁆ 1 ≠ inclusion 1 1 := by
    simp only [map_commutatorElement, map_one, x_table, y_table]
    decide +kernel
  exact hn ht

private def z : Carrier := y⁻¹ * x⁻¹ * y * x
def P : Subgroup Carrier := closure ({x, y} : Set Carrier)
private def generators : Fin 2 → Carrier := ![x, y]
private def reps (i : Fin 27) : Carrier := x ^ (i.val / 9) * y ^ (i.val / 3 % 3) * z ^ (i.val % 3)
private def repsTable (i : Fin 27) : Equiv.Perm (Fin 100) := xTable ^ (i.val / 9) * yTable ^ (i.val / 3 % 3) * (yTable⁻¹ * xTable⁻¹ * yTable * xTable) ^ (i.val % 3)
private theorem reps_table (i : Fin 27) : inclusion (reps i) = repsTable i := by
  simp only [reps, repsTable, z, map_mul, map_pow, map_inv, x_table, y_table]

private def next : Fin 27 → Fin 2 → Fin 27 :=
  ![![9, 3], ![10, 4], ![11, 5], ![13, 6], ![14, 7], ![12, 8], ![17, 0], ![15, 1], ![16, 2], ![18, 12], ![19, 13], ![20, 14], ![22, 15], ![23, 16], ![21, 17], ![26, 9], ![24, 10], ![25, 11], ![0, 21], ![1, 22], ![2, 23], ![4, 24], ![5, 25], ![3, 26], ![8, 18], ![6, 19], ![7, 20]]
private def prev : Fin 27 → Fin 2 → Fin 27 :=
  ![![18, 6], ![19, 7], ![20, 8], ![23, 0], ![21, 1], ![22, 2], ![25, 3], ![26, 4], ![24, 5], ![0, 15], ![1, 16], ![2, 17], ![5, 9], ![3, 10], ![4, 11], ![7, 12], ![8, 13], ![6, 14], ![9, 24], ![10, 25], ![11, 26], ![14, 18], ![12, 19], ![13, 20], ![16, 21], ![17, 22], ![15, 23]]
private theorem transitions (i : Fin 27) (j : Fin 2) :
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

private def point : Fin 27 → Fin 100 := ![1, 37, 74, 70, 35, 63, 34, 41, 31, 99, 81, 9, 97, 19, 42, 72, 93, 47, 28, 27, 86, 14, 96, 58, 30, 3, 82]

private theorem reps_point (i : Fin 27) : inclusion (reps i) 1 = point i := by
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

private theorem reps_mem (i : Fin 27) : reps i ∈ P := by
  have hx : x ∈ P := subset_closure (by simp)
  have hy : y ∈ P := subset_closure (by simp)
  have hz : z ∈ P := P.mul_mem (P.mul_mem (P.mul_mem (P.inv_mem hy)
    (P.inv_mem hx)) hy) hx
  exact P.mul_mem (P.mul_mem (P.pow_mem hx _) (P.pow_mem hy _)) (P.pow_mem hz _)

/-- Cardinality of the literal generated subgroup, with complete coverage. -/
theorem card_P : Nat.card P = 27 := by
  have hgen : ({x, y} : Set Carrier) = Set.range generators := by
    ext g
    simp [generators, or_comm]
  let e : Fin 27 → P := fun i => ⟨reps i, reps_mem i⟩
  have hi : Function.Injective e := fun i j h => reps_injective (congrArg Subtype.val h)
  have hs : Function.Surjective e := by
    intro g
    have hg : g.val ∈ closure (Set.range generators) := by
      simpa only [← hgen, P] using g.property
    obtain ⟨i, he⟩ := SubgroupEnumeration.closure_range_subset_range_of_transitions
      generators reps 0 next prev (by simp [reps]) transitions index_inverse hg
    exact ⟨i, Subtype.ext he⟩
  calc
    Nat.card P = Nat.card (Fin 27) := Nat.card_congr (Equiv.ofBijective e ⟨hi, hs⟩).symm
    _ = 27 := Nat.card_fin _

end Theory.SpecificGroups.J2HSMultipliers.J2.UpperBound.OddLocal.Three
