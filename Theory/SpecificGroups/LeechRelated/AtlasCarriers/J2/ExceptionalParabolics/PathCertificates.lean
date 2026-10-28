module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.BorelAutomorphisms.Generators
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Overlap.Inner
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.GroupAction.RankTwoCosetGeometry.PathKernelTransport
public import Theory.GroupAction.RankTwoCosetGeometry.PathOrderLowerBound
public import Theory.GroupAction.CubicTree.ArcReversal
public import Theory.GroupAction.RankTwoCosetGeometry.AlternatingFive
public import Theory.GroupAction.RankTwoCosetGeometry.PathCardinality
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount
import Mathlib.Tactic.FinCases

/-!
# Native cubic--quintic five-path certificates for J₂

The native marked parabolics `l₁` and `p₂` form the cubic--quintic coset
geometry. A kernel-checked degree-100 permutation table supplies one explicit
nonbacktracking five-path. Its fixer is contained in a six-element subset of
the 384-element Borel, so orbit--stabilizer gives rooted five-path
transitivity. Reversal transports the certificate to the opposite root type.
These are the finite model facts used by the field-four DGS source transport.
-/
@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.PathCertificates
open Theory.GroupTheory GeneratorPair Seed PairNormalizer
open PairNormalizer.SylowData PairNormalizer.QuotientData PairNormalizer.RadicalData
open GeneratorPair.SecondOrbitCertificate SecondParabolic.Overlap
open SecondParabolic.BorelAutomorphisms
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
local notation "Jα" => Seed.p₂
local notation "Jβ" => Seed.l₁

def family : Bool → Subgroup Carrier := fun i => if i then Jα else Jβ

def turnWord : List (Fin 3) := [2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1]
def turn : Carrier := localWord turnWord
def turnValues : Fin 100 → Fin 100 := ![63, 74, 12, 97, 84, 66, 90, 88, 16, 60, 69, 34, 7, 6, 9, 46, 87, 62, 93, 17, 72, 83, 52, 79, 50, 73, 21, 98, 2, 18, 13, 10, 82, 68, 80, 11, 27, 42, 24, 92, 96, 26, 67, 36, 70, 99, 94, 53, 85, 22, 86, 5, 23, 37, 56, 77, 29, 58, 25, 35, 78, 20, 55, 51, 30, 45, 0, 47, 32, 40, 65, 41, 4, 95, 8, 43, 38, 19, 89, 49, 59, 33, 81, 71, 61, 91, 76, 1, 28, 14, 64, 39, 48, 54, 3, 57, 31, 15, 75, 44]
def turnInvValues : Fin 100 → Fin 100 := ![66, 87, 28, 94, 72, 51, 13, 12, 74, 14, 31, 35, 2, 30, 89, 97, 8, 19, 29, 77, 61, 26, 49, 52, 38, 58, 41, 36, 88, 56, 64, 96, 68, 81, 11, 59, 43, 53, 76, 91, 69, 71, 37, 75, 99, 65, 15, 67, 92, 79, 24, 63, 22, 47, 93, 62, 54, 95, 57, 80, 9, 84, 17, 0, 90, 70, 5, 42, 33, 10, 44, 83, 20, 25, 1, 98, 86, 55, 60, 23, 34, 82, 32, 21, 4, 48, 50, 16, 7, 78, 6, 85, 39, 18, 46, 73, 40, 3, 27, 45]
theorem turn_left : Function.LeftInverse turnInvValues turnValues := by decide +kernel
def turnTable : Equiv.Perm (Fin 100) := tablePerm turnValues turnInvValues turn_left
  (rightInverse_of_leftInverse_fin turn_left)
private theorem inclusion_localWord (w : List (Fin 3)) :
    inclusion (localWord w) = evalWord ![tableA, tableB, tableB⁻¹] w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change inclusion (![a, b, b⁻¹] i * localWord w) = _
    rw [map_mul, ih]
    congr 1
    fin_cases i <;> simp [a, b, inclusion, generatorA_eq_table, generatorB_eq_table]
set_option maxRecDepth 100000 in
private theorem turn_word : evalWord ![tableA,tableB,tableB⁻¹] turnWord = turnTable := by
  decide +kernel
theorem turn_inclusion : inclusion turn = turnTable :=
  (inclusion_localWord turnWord).trans turn_word
set_option maxRecDepth 100000 in
theorem turn_mem_l₁ : turn ∈ Jβ := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply inclusion_injective
  rw [map_mul,map_mul,turn_inclusion]
  change turnTable * inclusion FirstFusion.t = inclusion FirstFusion.t * turnTable
  rw [FirstFusion.inclusion_t]
  decide +kernel
set_option maxRecDepth 100000 in
private theorem turn_bad_check : ∀ i : Fin 64,
    qTable i 0 ≠ (turnTable * qGenTable 0 * turnTable⁻¹) 0 ∨
    qTable i 1 ≠ (turnTable * qGenTable 0 * turnTable⁻¹) 1 := by
  apply allFin
  decide +kernel
theorem turn_not_mem_p₂ : turn ∉ p₂ := by
  intro h
  have hh := ((Subgroup.mem_normalizer_iff.mp h) (q₂Generator 0)).mp
    (Subgroup.subset_closure ⟨0, rfl⟩)
  obtain ⟨i, hi⟩ := exists_qElement hh
  have he := congrArg inclusion hi
  rw [qElement_inclusion,map_mul,map_mul,map_inv,turn_inclusion,q₂Generator_inclusion] at he
  rcases turn_bad_check i with hx | hx
  · exact hx (congrArg (fun p : Equiv.Perm (Fin 100) => p 0) he)
  · exact hx (congrArg (fun p : Equiv.Perm (Fin 100) => p 1) he)
theorem odd_mem_alpha : oddGenerator 0 ∈ Jα :=
  oddGenerator_mem_p₂ 0
theorem turn_not_alpha : turn ∉ Jα := turn_not_mem_p₂
theorem odd_not_beta : oddGenerator 0 ∉ Jβ := u_not_mem_l₁

def path (i : Bool) : BasedWalk (graph family) 5 (base family i) :=
  alternatingFive family i (if i then oddGenerator 0 else turn)
    (if i then turn else oddGenerator 0)
    (by cases i <;> simp [family, turn_mem_l₁, odd_mem_alpha])
    (by cases i <;> simp [family, turn_mem_l₁, odd_mem_alpha])

theorem path_nonbacktracking (i : Bool) : (path i).Nonbacktracking := by
  unfold path
  apply alternatingFive_nonbacktracking
  · cases i <;> simp [family, turn_not_alpha, odd_not_beta]
  · cases i <;> simp [family, turn_not_alpha, odd_not_beta]

theorem family_inf (i : Bool) : family i ⊓ family (!i) = B := by
  cases i
  · simp only [family, Bool.not_false, ↓reduceIte]
    exact SecondParabolic.Overlap.l₁_inf_p₂_eq_B PairNormalizer.card_p₂
  · simp only [family, Bool.not_true, ↓reduceIte]
    rw [inf_comm]
    exact SecondParabolic.Overlap.l₁_inf_p₂_eq_B PairNormalizer.card_p₂
def longWord : Carrier := turn * oddGenerator 0 * turn * oddGenerator 0
def terminalCenterValues : Fin 100 → Fin 100 := ![32, 48, 91, 5, 4, 3, 46, 89, 85, 22, 88, 94, 12, 19, 49, 15, 72, 54, 86, 13, 30, 51, 9, 35, 31, 71, 83, 27, 45, 29, 20, 24, 0, 33, 43, 23, 36, 96, 58, 39, 68, 60, 59, 34, 77, 28, 6, 47, 1, 14, 69, 21, 95, 53, 17, 98, 87, 57, 38, 42, 41, 61, 62, 80, 78, 79, 66, 67, 40, 50, 99, 25, 16, 74, 73, 90, 76, 44, 64, 65, 63, 92, 82, 26, 84, 8, 18, 56, 10, 7, 75, 2, 81, 93, 11, 52, 37, 97, 55, 70]
theorem terminalCenter_involutive : Function.Involutive terminalCenterValues := by
  change ∀ i, terminalCenterValues (terminalCenterValues i) = i
  decide +kernel
def terminalCenterTable : Equiv.Perm (Fin 100) :=
  tablePerm terminalCenterValues terminalCenterValues terminalCenter_involutive terminalCenter_involutive
set_option maxRecDepth 100000 in
theorem terminalCenter_inclusion : inclusion (longWord * z * longWord⁻¹) = terminalCenterTable := by
  simp only [longWord,map_mul,map_inv,turn_inclusion,oddGenerator_inclusion]
  change _ * inclusion FirstFusion.t * _ = _
  rw [FirstFusion.inclusion_t]
  decide +kernel
set_option maxRecDepth 100000 in
private theorem surviving_indices : ∀ i : Fin 384,
    bTable i (terminalCenterTable 1) = terminalCenterTable (bTable i 1) →
      i = 0 ∨ i = 83 ∨ i = 140 ∨ i = 238 ∨ i = 277 ∨ i = 355 := by
  apply allFin
  decide +kernel

def smallFixer : Subgroup Carrier := B ⊓ Subgroup.centralizer {longWord * z * longWord⁻¹}

set_option maxRecDepth 100000 in
theorem path_true_fixer_le : pathStabilizer family (path true) ≤ smallFixer := by
  have h := alternatingFive_fixer_le family true (oddGenerator 0) turn odd_mem_alpha turn_mem_l₁
  rw [family_inf] at h
  intro g hg
  have hh := h hg
  refine ⟨hh.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have hb : longWord⁻¹ * g * longWord ∈ B := by
    have hb0 := hh.2
    change (MulAut.conj longWord⁻¹).toMonoidHom g ∈ B at hb0
    change longWord⁻¹ * g * (longWord⁻¹)⁻¹ ∈ B at hb0
    rw [inv_inv] at hb0
    exact hb0
  have ht := SecondParabolic.Overlap.B_le_l₁ hb
  have he := Subgroup.mem_centralizer_singleton_iff.mp ht
  calc
    g * (longWord * z * longWord⁻¹) =
        longWord * (longWord⁻¹ * g * longWord) * z * longWord⁻¹ := by
      simp only [mul_assoc, mul_inv_cancel_left]
    _ = longWord * z * (longWord⁻¹ * g * longWord) * longWord⁻¹ := by
      simpa only [mul_assoc] using
        congrArg (fun t : Carrier => longWord * t * longWord⁻¹) he
    _ = (longWord * z * longWord⁻¹) * g := by
      simp only [mul_assoc, mul_inv_cancel, mul_one]

private def surviving : Finset (Fin 384) := {0,83,140,238,277,355}

theorem card_smallFixer : Nat.card smallFixer ≤ 6 := by
  classical
  let e : Fin 384 ≃ B := Equiv.ofBijective bElement
    ((show Function.Surjective bElement from exists_bElement).bijective_of_nat_card_le
      (by rw [card_B]; simp))
  have hs (g : smallFixer) : e.symm ⟨g.val,g.property.1⟩ ∈ surviving := by
    let j := e.symm ⟨g.val,g.property.1⟩
    have he : (bElement j : Carrier) = g.val := congrArg Subtype.val (e.apply_symm_apply _)
    have hc := congrArg inclusion (Subgroup.mem_centralizer_singleton_iff.mp g.property.2)
    have hc' : inclusion g.val * terminalCenterTable =
        terminalCenterTable * inclusion g.val := by
      rw [← terminalCenter_inclusion]
      simpa only [map_mul] using hc
    rw [← he, bElement_table] at hc'
    have hp := congrArg (fun p : Equiv.Perm (Fin 100) => p 1) hc'
    change bTable j (terminalCenterTable 1) = terminalCenterTable (bTable j 1) at hp
    rcases surviving_indices j hp with hj | hj | hj | hj | hj | hj <;>
      simp only [j] at hj <;> simp [surviving,hj]
  let f : smallFixer → {i : Fin 384 // i ∈ surviving} := fun g => ⟨e.symm ⟨g.val,g.property.1⟩,hs g⟩
  have hi : Function.Injective f := by
    intro g h he
    apply Subtype.ext
    dsimp only [f] at he
    have hj : e.symm ⟨g.val,g.property.1⟩ = e.symm ⟨h.val,h.property.1⟩ :=
      congrArg Subtype.val he
    have hx := e.symm.injective hj
    exact congrArg (fun b : B => (b : Carrier)) hx
  have hc : Nat.card {i : Fin 384 // i ∈ surviving} = 6 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    decide +kernel
  exact hc ▸ Nat.card_le_card_of_injective f hi

theorem path_true_fixer_card_le : Nat.card (pathStabilizer family (path true)) ≤ 6 :=
  (Nat.card_le_card_of_injective (Subgroup.inclusion path_true_fixer_le)
    (Subgroup.inclusion_injective _)).trans card_smallFixer

theorem card_family (i : Bool) : Nat.card (family i) = if i then 1152 else 1920 := by
  cases i
  · exact FirstParabolic.card_l₁
  · exact PairNormalizer.card_p₂

theorem family_indices (i : Bool) :
    ((family (!i)).subgroupOf (family i)).index = if i then 3 else 5 := by
  have h := ((family (!i)).subgroupOf (family i)).card_mul_index
  have he : (family (!i)).subgroupOf (family i) = B.subgroupOf (family i) := by
    rw [← family_inf i, Subgroup.inf_subgroupOf_left]
  have hle : B ≤ family i := by rw [← family_inf i]; exact inf_le_left
  have hb : Nat.card (B.subgroupOf (family i)) = 384 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_B]
  rw [he, hb, card_family i] at h
  rw [he]
  cases i <;> dsimp at * <;> omega

theorem card_five_paths (i : Bool) :
    Nat.card {p : BasedWalk (graph family) 5 (base family i) // p.Nonbacktracking} =
      if i then 192 else 320 := by
  have hc := card_neighbors_of_indices family (fun i => if i then 3 else 5) family_indices
  have (v : Vertex family) : Finite ((graph family).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; cases v.type <;> decide)
  have hf : ∀ {v w : Vertex family}, (graph family).Adj v w → w.type = !v.type := by
    intro v w h
    have hne := h.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  have h := BasedWalk.card_nonbacktracking_succ (graph family)
    (fun v : Vertex family => v.type) (fun i => if i then 3 else 5) hf hc 4 (base family i)
  rw [h]
  cases i <;> decide

theorem exists_path_fixer_card_le (i : Bool) :
    ∃ p : BasedWalk (graph family) 5 (base family i), p.Nonbacktracking ∧
      Nat.card (pathStabilizer family p) ≤ 6 := by
  cases i with
  | true => exact ⟨path true,path_nonbacktracking true,path_true_fixer_card_le⟩
  | false =>
    let p := path true
    have ht : p.endpoint.type = false := rfl
    let r := Theory.GroupAction.CubicTree.reverse p
    have hr : r.Nonbacktracking :=
      Theory.GroupAction.CubicTree.nonbacktracking_reverse p (path_nonbacktracking true)
    obtain ⟨q,hq,g,hg⟩ := exists_base_path_translate family ht r hr
    refine ⟨q,hq,?_⟩
    have he : pathStabilizer family r = pathStabilizer family p := by
      ext x
      change (∀ w ∈ r.vertices, x • w = w) ↔ (∀ w ∈ p.vertices, x • w = w)
      simp only [r,Theory.GroupAction.CubicTree.vertices_reverse,List.mem_reverse]
    have hm := pathStabilizer_map_conj_of_vertices family q r g hg
    have hc : Nat.card (pathStabilizer family q) = Nat.card (pathStabilizer family p) := by
      rw [← he,← hm,Subgroup.card_map_of_injective (MulAut.conj g).injective]
    rw [hc]
    exact path_true_fixer_card_le

theorem rootPathTransitive_five (i : Bool) :
    RootPathTransitive (graph family) Carrier (base family i) 5 := by
  obtain ⟨p,hp,hc⟩ := exists_path_fixer_card_le i
  have : Finite {p : BasedWalk (graph family) 5 (base family i) // p.Nonbacktracking} :=
    Nat.finite_of_card_ne_zero (by rw [card_five_paths]; cases i <;> decide)
  apply rootPathTransitive_of_pathStabilizer_card_le family p hp (by decide : 0 < 6) hc
  rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base,card_family,card_five_paths]
  cases i <;> decide

end Sporadic.LeechRelated.J2.ExceptionalParabolics.PathCertificates

