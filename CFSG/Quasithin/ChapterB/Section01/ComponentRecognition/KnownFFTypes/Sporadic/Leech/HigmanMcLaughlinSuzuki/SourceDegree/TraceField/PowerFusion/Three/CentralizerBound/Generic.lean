module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Certificate
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.PowerFusion.Three.CubicCoverage

/-! Kernel checked stabilizer-chain pruning for the literal HS cubic centralizer.

The residual orbit colours are the stabilizer-chain orbit partitions.  The
single letter in `cubicLetters` is the distinguished cubic.  All finite
identities in the transition certificates below are checked by Lean's kernel.
Source: ATLAS HSG1-p100B0, class 3A.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.ThreePowerFusion.CentralizerCertificate
open Theory.GroupTheory
open Sporadic.LeechRelated.HS.OrderCertificate
set_option maxRecDepth 100000
set_option Elab.async false
abbrev Perm := Equiv.Perm (Fin 100)
def prefix0 (_ : Fin 1) : Perm := 1
def cubicImage (x : Fin 100) : Fin 100 :=
  ⟨(3590466344902948551500625880980508819832494606187222822039878239244387711950573130115437290048217149180348662678481892044422835610802713319183385920130626599983898057698595368469169751438366140358681017099494366 >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

def cubicPreimage (x : Fin 100) : Fin 100 :=
  ⟨(3766358194415054432431872030361567221117552467915209481939698628316670309266301918384587288391129662634053215462575692351710928147551825924256149324224257358047247188724763289543387824437679782136312604234444347 >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

theorem cubicInverse : ∀ x, cubicPreimage (cubicImage x) = x := by
  apply allFin
  decide +kernel

def cubicTable : Perm := tablePerm cubicImage cubicPreimage cubicInverse
  (rightInverse_of_leftInverse_fin cubicInverse)

theorem cubicTable_eq : cubicTable = (cubic : Perm) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

def cubicLetters : List Perm := [cubicTable]
def screen (color : Fin 100 → Nat) (base : List (Fin 100)) (p : Perm) : Bool :=
  base.all fun b => cubicLetters.all fun a =>
    decide (color (p⁻¹ (a (p b))) = color (a b))
def stageCheck {n : Nat} (gen : Fin n → Perm) (color : Fin 100 → Nat)
    (base : List (Fin 100)) (i : Fin n) : Bool :=
  base.all (fun b => decide (gen i b = b)) &&
    checkFin (fun x => decide (color (gen i x) = color x))
theorem word_properties {n : Nat} (gen : Fin n → Perm) (inv : Fin n → Fin n)
    (hi : ∀ i, gen (inv i) = (gen i)⁻¹) (color : Fin 100 → Nat)
    (base : List (Fin 100)) (hc : ∀ i, stageCheck gen color base i = true)
    {h : Perm} (hh : h ∈ wordSubgroup gen inv hi) :
    (∀ b ∈ base, h b = b) ∧ (∀ x, color (h x) = color x) := by
  obtain ⟨w, rfl⟩ := hh
  have hg i := Bool.and_eq_true_iff.mp (hc i)
  induction w with
  | nil => exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  | cons i w ih =>
    constructor
    · intro b hb
      change gen i (evalWord gen w b) = b
      rw [ih.1 b hb]
      exact decide_eq_true_eq.mp (List.all_eq_true.mp (hg i).1 b hb)
    · intro x
      change color (gen i (evalWord gen w x)) = color x
      rw [allFin _ (hg i).2, ih.2]
theorem screen_of_commute (color : Fin 100 → Nat) (base : List (Fin 100))
    (p h : Perm) (hfix : ∀ b ∈ base, h b = b)
    (hcolor : ∀ x, color (h x) = color x)
    (hc : ∀ a ∈ cubicLetters, a * (p * h) = (p * h) * a) :
    screen color base p = true := by
  apply List.all_eq_true.mpr
  intro b hb; apply List.all_eq_true.mpr; intro a ha
  apply decide_eq_true_eq.mpr
  have he := congrArg (fun q : Perm => q b) (hc a ha)
  change a (p (h b)) = p (h (a b)) at he
  rw [hfix b hb] at he
  have hval : p⁻¹ (a (p b)) = h (a b) := by
    rw [he]; exact p.symm_apply_apply _
  rw [hval, hcolor]
theorem decompose {n m q : Nat} (gen : Fin n → Perm) (inv : Fin n → Fin n)
    (hi : ∀ i, gen (inv i) = (gen i)⁻¹) (ng : Fin q → Perm) (ni : Fin q → Fin q)
    (hni : ∀ i, ng (ni i) = (ng i)⁻¹) (rep : Fin m → Perm)
    (act : Fin n → Fin m → Fin m) (factor : Fin n → Fin m → List (Fin q))
    (r : Fin m) (hr : rep r = 1)
    (hs : ∀ i j, gen i * rep j = rep (act i j) * evalWord ng (factor i j))
    {g : Perm} (hg : g ∈ wordSubgroup gen inv hi) :
    ∃ j, ∃ h ∈ wordSubgroup ng ni hni, g = rep j * h := by
  obtain ⟨w, rfl⟩ := hg
  induction w with
  | nil => exact ⟨r, 1, Subgroup.one_mem _, by simp [evalWord, hr]⟩
  | cons i w ih =>
    obtain ⟨j, h, hh, he⟩ := ih
    refine ⟨act i j, evalWord ng (factor i j) * h,
      Subgroup.mul_mem _ ⟨factor i j, rfl⟩ hh, ?_⟩
    change gen i * evalWord gen w = _
    rw [he, ← mul_assoc, hs, mul_assoc]
theorem advance {n m t : Nat} (H K : Subgroup Perm) (p : Fin n → Perm)
    (q : Fin m → Perm) (rep : Fin t → Perm) (color : Fin 100 → Nat)
    (base : List (Fin 100)) (hd : ∀ h ∈ H, ∃ j, ∃ v ∈ K, h = rep j * v)
    (hK : ∀ v ∈ K, (∀ b ∈ base, v b = b) ∧ (∀ x, color (v x) = color x))
    (ht : ∀ i j, screen color base (p i * rep j) = true → ∃ l,
      p i * rep j = q l) {g : Perm}
    (hc : ∀ a ∈ cubicLetters, a * g = g * a)
    (hg : ∃ i, ∃ h ∈ H, g = p i * h) : ∃ i, ∃ h ∈ K, g = q i * h := by
  obtain ⟨i, h, hh, he⟩ := hg
  obtain ⟨j, v, hv, hf⟩ := hd h hh
  have heq : g = (p i * rep j) * v := by rw [he, hf, mul_assoc]
  have hs := screen_of_commute color base (p i * rep j) v (hK v hv).1 (hK v hv).2
    (by simpa only [← heq] using hc)
  obtain ⟨l, hl⟩ := ht i j hs
  exact ⟨l, v, hv, by rw [heq, hl]⟩
/-- Boolean finite checking does not build nested decidability proofs. -/
theorem checkFin_true {n : Nat} {f : Fin n → Bool}
    (h : checkFin f = true) (i : Fin n) : f i = true := by
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt] using hi

theorem allFin₂ {n m : Nat} (P : Fin n → Fin m → Prop) [DecidableRel P]
    (h : checkFin (fun i => checkFin (fun j => decide (P i j))) = true) :
    ∀ i j, P i j := by
  intro i j
  exact of_decide_eq_true (checkFin_true (checkFin_true h i) j)

theorem transition_check {n m q : Nat} (p : Fin n → Perm) (r : Fin m → Perm)
    (s : Fin q → Perm) (next : Fin n → Fin m → Fin q)
    (color : Fin 100 → Nat) (base : List (Fin 100))
    (h : checkFin (fun i => checkFin (fun j =>
      !screen color base (p i * r j) ||
      checkFin (fun x => decide ((p i * r j) x = s (next i j) x)))) = true) :
    ∀ i j, screen color base (p i * r j) = true → p i * r j = s (next i j) := by
  intro i j hs
  have hx := checkFin_true (checkFin_true h i) j
  simp only [hs, Bool.not_true, Bool.false_or] at hx
  apply Equiv.ext
  intro x
  exact of_decide_eq_true (checkFin_true hx x)

end Sporadic.LeechRelated.HS.ThreePowerFusion.CentralizerCertificate
