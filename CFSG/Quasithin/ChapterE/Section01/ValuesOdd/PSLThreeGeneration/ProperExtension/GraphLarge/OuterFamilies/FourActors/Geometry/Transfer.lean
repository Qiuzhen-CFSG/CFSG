module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FourActors.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.Reduction
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Transferring outer-family controls to an inner four-group

Two conjugates of the original outer actor containing inner involutions w
and wz control the commutator with D = <w,z>. The Sylow subgroup centralizes
z, so both actor centralizers in the Sylow centralize D. Moreover, D has
order four, and D lies in the join of the two actors. Since both actors lie
in M, the commutator product identity transfers their separate controls to D.
The existing inner four-group mixing calculation then generates the graph
extension. D itself is never asserted to belong to the original family.

`OuterFourConjugateFusion` isolates the remaining concrete conjugacy input.
Its existence is not proved here. The separate solvable full-Sylow mixing
construction applies directly, without an inner-family hypothesis.

Source: Aschbacher--Smith E.1.1--5 and E.1.14(7), printed pp.209--210,214;
A.3.21(a), p.55; the reference in E.1.14(7) to Aschbacher (1982), Lemma 4.11.
The transfers here are deductions from explicit model inputs, not a proof
of the unconditional book theorem.
-/

public section
open Subgroup
open scoped commutatorElement

private theorem commutator_join_le {G : Type*} [Group G]
    (X B C M : Subgroup G) (hBM : B ≤ M) (hCM : C ≤ M)
    (hB : ⁅X,B⁆ ≤ M) (hC : ⁅X,C⁆ ≤ M) : ⁅X,B ⊔ C⁆ ≤ M := by
  let S : Bool → Subgroup G := fun b => if b then B else C
  have hSM : (⨆ b, S b) ≤ M := iSup_le fun b => by cases b <;> assumption
  have hcomm (b : Bool) : ⁅X, S b⁆ ≤ M := by cases b <;> assumption
  have hh : ⁅X, ⨆ b, S b⁆ ≤ M := by
    apply commutator_le.mpr
    intro x hx y hy
    induction hy using iSup_induction' with
    | hp b y hy => exact hcomm b (commutator_mem_commutator hx hy)
    | h1 => simpa only [commutatorElement_one_right] using M.one_mem
    | hmul a b ha hb iha ihb =>
      rw [commutatorElement_mul_right_eq_mul_conj]
      simpa only [mul_assoc] using
        M.mul_mem iha (M.mul_mem (M.mul_mem (hSM ha) ihb) (M.inv_mem (hSM ha)))
  simpa only [iSup_bool_eq, S, Bool.false_eq_true, ↓reduceIte] using hh

private theorem mem_line {G : Type*} [Group G] [Finite G] {z x : G}
    (hz : orderOf z = 2) (hx : x ∈ zpowers z) : x = 1 ∨ x = z := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hz] at hx
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  have hn2 : n < 2 := Finset.mem_range.mp hn
  interval_cases n <;> simp

private theorem inner_pair_card {G : Type*} [Group G] [Finite G]
    {w z : G} (hw : orderOf w = 2) (hz : orderOf z = 2) (hne : w ≠ z)
    (hc : w * z = z * w) :
    IsElementaryAbelian 2 (zpowers w ⊔ zpowers z : Subgroup G) ∧
      Nat.card (zpowers w ⊔ zpowers z : Subgroup G) = 4 := by
  let : IsElementaryAbelian 2 (zpowers w) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hw ▸ pow_orderOf_eq_one w)
  let : IsElementaryAbelian 2 (zpowers z) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hz ▸ pow_orderOf_eq_one z)
  have hcentral : zpowers z ≤ centralizer (zpowers w : Set G) := by
    apply le_centralizer_iff.mpr
    apply zpowers_le.mpr
    intro y hy
    rcases mem_line hz hy with rfl | rfl
    · simp
    · exact hc.symm
  have hd : Disjoint (zpowers w) (zpowers z) := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    rintro x ⟨hx, hy⟩
    rw [mem_bot]
    rcases mem_line hw hx with rfl | rfl
    · rfl
    rcases mem_line hz hy with h | h
    · exact h
    · exact (hne h).elim
  refine ⟨IsElementaryAbelian.sup_of_le_centralizer hcentral, ?_⟩
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (hcentral.trans (Subgroup.centralizer_le_normalizer _)) hd, Nat.card_zpowers, Nat.card_zpowers, hw, hz]

private theorem centralizer_pair {G : Type*} [Group G] (R : Subgroup G) (w z : G)
    (hw : R ≤ centralizer ({w} : Set G)) (hz : R ≤ centralizer ({z} : Set G)) :
    R ≤ centralizer (zpowers w ⊔ zpowers z : Subgroup G) := by
  apply le_centralizer_iff.mpr
  apply sup_le
  · apply zpowers_le.mpr
    intro t ht
    exact mem_centralizer_singleton_iff.mp (hw ht)
  · apply zpowers_le.mpr
    intro t ht
    exact mem_centralizer_singleton_iff.mp (hz ht)

open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge
open CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
variable (F : Type*) [Field F] [Finite F]

/-- Two conjugates of the original outer actor meet the two noncentral lines
of an inner four-group through z. No new member of the family is introduced. -/
@[expose] def OuterFourConjugateFusion : Prop :=
  ∀ (T : Sylow 2 (graphExtension F)) (A : Subgroup (graphExtension F)),
    IsElementaryAbelian 2 A → A ≤ (T : Subgroup _) → Nat.card A = 4 →
    Nat.card (A ⊓ innerPart F : Subgroup _) = 2 →
    ∀ z : graphExtension F, orderOf z = 2 → z ∈ innerPart F → z ∈ A →
    (T : Subgroup _) ≤ centralizer ({z} : Set _) →
    ∃ g h w : graphExtension F,
      A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup _) ∧
      A.map (MulAut.conj h).toMonoidHom ≤ (T : Subgroup _) ∧
      w ∈ innerPart F ∧ orderOf w = 2 ∧ w ≠ z ∧
      w ∈ A.map (MulAut.conj g).toMonoidHom ∧
      w * z ∈ A.map (MulAut.conj h).toMonoidHom

/-- The full-Sylow solvable witness applies to outer actors as well. -/
theorem fourActorCentralizerGeneration_of_solvable_mixing
    (hgeometry : SolvableMixing F) : FourActorCentralizerGeneration F := by
  intro T Ω _ _ _ A _ _ _ _ z hz hzL _ hTz M hCM _ hsol _
  obtain ⟨H, hTH, hs, hmix⟩ := hgeometry T z hz hzL hTz
  exact eq_top_of_mixing F z M hCM (hmix.mono F (hsol H hTH hs))

/-- The original actors control the inner four-group commutator jointly.
This uses actual conjugates, not membership of the inner four-group in Ω. -/
theorem fourActorCentralizerGeneration_of_conjugate_fusion
    (hgeometry : FourGroupOddMixing F) (hfusion : OuterFourConjugateFusion F) :
    FourActorCentralizerGeneration F := by
  intro T Ω hΩ _ _ A hA hAT hfour hinter z hz hzL hzA hTz M hCM _ _ hodd
  obtain ⟨g, h, w, hBT, hCT, hwL, hw, hwz, hwB, hwzC⟩ :=
    hfusion T A (hΩ.1 A hA) hAT hfour hinter z hz hzL hzA hTz
  let B := A.map (MulAut.conj g).toMonoidHom
  let C := A.map (MulAut.conj h).toMonoidHom
  let D := zpowers w ⊔ zpowers z
  have hwT : w ∈ (T : Subgroup _) := hBT hwB
  have hzT : z ∈ (T : Subgroup _) := hAT hzA
  have hwcomm : w * z = z * w := mem_centralizer_singleton_iff.mp (hTz hwT)
  obtain ⟨hDE, hDcard⟩ := inner_pair_card hw hz hwz hwcomm
  have hDT : D ≤ (T : Subgroup _) := sup_le (zpowers_le.mpr hwT) (zpowers_le.mpr hzT)
  have hDL : D ≤ innerPart F := sup_le (zpowers_le.mpr hwL) (zpowers_le.mpr hzL)
  have hzD : z ∈ D := mem_sup_right (mem_zpowers z)
  have hBC : D ≤ B ⊔ C := by
    have hwBC : w ∈ B ⊔ C := mem_sup_left hwB
    have hwzBC : w * z ∈ B ⊔ C := mem_sup_right hwzC
    have hzBC : z ∈ B ⊔ C := by
      simpa only [inv_mul_cancel_left] using (B ⊔ C).mul_mem ((B ⊔ C).inv_mem hwBC) hwzBC
    exact sup_le (zpowers_le.mpr hwBC) (zpowers_le.mpr hzBC)
  have hcentB : (T : Subgroup _) ⊓ centralizer (B : Set (graphExtension F)) ≤
      (T : Subgroup _) ⊓ centralizer (D : Set (graphExtension F)) := by
    apply le_inf inf_le_left
    apply centralizer_pair
    · intro t ht
      exact mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp ht.2) w hwB).symm
    · exact inf_le_left.trans hTz
  have hcentC : (T : Subgroup _) ⊓ centralizer (C : Set (graphExtension F)) ≤
      (T : Subgroup _) ⊓ centralizer (D : Set (graphExtension F)) := by
    apply le_inf inf_le_left
    apply centralizer_pair
    · intro t ht
      apply mem_centralizer_singleton_iff.mpr
      have htz := mem_centralizer_singleton_iff.mp (hTz ht.1)
      have htwz := ((mem_centralizer_iff.mp ht.2) (w * z) hwzC).symm
      apply mul_right_cancel (b := z)
      calc
        t * w * z = t * (w * z) := mul_assoc _ _ _
        _ = (w * z) * t := htwz
        _ = w * t * z := by rw [mul_assoc, ← htz, ← mul_assoc]
    · exact inf_le_left.trans hTz
  obtain ⟨r, hr, hor, X, hX, hn, hmix⟩ := hgeometry T D hDE hDcard hDT hDL z hz hzD hTz
  have hTM : (T : Subgroup _) ≤ M := hTz.trans hCM
  have hXB : ⁅X, B⁆ ≤ M := hodd B (hΩ.2 g A hA) hBT r hr hor X hX (hcentB.trans hn)
  have hXC : ⁅X, C⁆ ≤ M := hodd C (hΩ.2 h A hA) hCT r hr hor X hX (hcentC.trans hn)
  have hXD : ⁅X, D⁆ ≤ M := (commutator_mono le_rfl hBC).trans
    (commutator_join_le X B C M (hBT.trans hTM) (hCT.trans hTM) hXB hXC)
  exact eq_top_of_mixing F z M hCM (hmix.mono F hXD)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
