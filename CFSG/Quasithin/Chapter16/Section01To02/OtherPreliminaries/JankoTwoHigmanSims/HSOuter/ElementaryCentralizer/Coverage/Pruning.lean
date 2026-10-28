module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer.Kernel
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Certificate

/-!
# Stabilizer-chain pruning for HS elementary centralizers

Adapted from `HS.EvenLocalCandidates.LargeElementaryCentralizers.Generic`.
A commuting permutation written as a partial representative times a residual
stabilizer must preserve the residual orbit colors at every fixed base point.
This criterion prunes the existing kernel-certified HS stabilizer chain.
Here the letters consist of the single specified outer involution. The final
application checks membership of every survivor in the candidate subgroup.

Source: ATLAS HSG1-p100B0; GLS volume 3, Table 5.3m, printed p.274;
Aschbacher–Smith 16.1.5(10), printed p.1172, GLS3 Table 5.3m, class 2C.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer.Coverage
open Theory.GroupTheory Sporadic.LeechRelated.HS.OrderCertificate
set_option maxRecDepth 100000
set_option Elab.async false

abbrev Perm := Equiv.Perm (Fin 100)

def prefix0 (_ : Fin 1) : Perm := 1

def letters : List Perm := [elementaryPermutation]

def screen (color : Fin 100 → Nat) (base : List (Fin 100)) (p : Perm) : Bool :=
  base.all fun b => letters.all fun a =>
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
    (hc : ∀ a ∈ letters, a * (p * h) = (p * h) * a) :
    screen color base p = true := by
  apply List.all_eq_true.mpr
  intro b hb
  apply List.all_eq_true.mpr
  intro a ha
  apply decide_eq_true_eq.mpr
  have he := congrArg (fun q : Perm => q b) (hc a ha)
  change a (p (h b)) = p (h (a b)) at he
  rw [hfix b hb] at he
  have hval : p⁻¹ (a (p b)) = h (a b) := by
    rw [he]
    exact p.symm_apply_apply _
  rw [hval, hcolor]

theorem decompose {n m q : Nat}
    (gen : Fin n → Perm) (inv : Fin n → Fin n)
    (hi : ∀ i, gen (inv i) = (gen i)⁻¹)
    (ng : Fin q → Perm) (ni : Fin q → Fin q)
    (hni : ∀ i, ng (ni i) = (ng i)⁻¹)
    (rep : Fin m → Perm) (act : Fin n → Fin m → Fin m)
    (factor : Fin n → Fin m → List (Fin q))
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

theorem advance {n m t : Nat} (H K : Subgroup Perm)
    (p : Fin n → Perm) (q : Fin m → Perm) (rep : Fin t → Perm)
    (color : Fin 100 → Nat) (base : List (Fin 100))
    (hd : ∀ h ∈ H, ∃ j, ∃ v ∈ K, h = rep j * v)
    (hK : ∀ v ∈ K, (∀ b ∈ base, v b = b) ∧ (∀ x, color (v x) = color x))
    (ht : ∀ i j, screen color base (p i * rep j) = true → ∃ l, p i * rep j = q l)
    {g : Perm} (hc : ∀ a ∈ letters, a * g = g * a)
    (hg : ∃ i, ∃ h ∈ H, g = p i * h) : ∃ i, ∃ h ∈ K, g = q i * h := by
  obtain ⟨i, h, hh, he⟩ := hg
  obtain ⟨j, v, hv, hf⟩ := hd h hh
  have heq : g = (p i * rep j) * v := by rw [he, hf, mul_assoc]
  have hs := screen_of_commute color base (p i * rep j) v (hK v hv).1 (hK v hv).2
    (by simpa only [← heq] using hc)
  obtain ⟨l, hl⟩ := ht i j hs
  exact ⟨l, v, hv, by rw [heq, hl]⟩

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer.Coverage
