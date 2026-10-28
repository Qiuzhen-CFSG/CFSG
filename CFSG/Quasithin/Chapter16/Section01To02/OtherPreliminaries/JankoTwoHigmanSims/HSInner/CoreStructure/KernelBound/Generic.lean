module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralInvolutionCore
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.LargeElementaryCentralizers.Generic

/-!
# Necessary screens for the actual HS pair kernel

Write a kernel element as `p * h`, with `h` in a residual stabilizer.
At a fixed base point, commutation with `e0` restricts the residual orbit
color of the conjugate image. At an `e0`-fixed letter, pair preservation
requires one of the two permitted images to have the correct residual color.
These necessary conditions support exhaustive pruning of the certified chain.

Source: Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3 Table 5.3m,
printed p.274. Only the existing concrete pair kernel and certified HS chain
are used. Residual orbit colors need invariance, not an assumed orbit theorem.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure.KernelBound
open Theory.GroupTheory
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.OrderCertificate
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore (twin)

abbrev Perm := Equiv.Perm (Fin 100)

def prefix0 (_ : Fin 1) : Perm := 1

def PairCondition (g : Perm) : Prop :=
  ∀ i : Fin 100, (e0 : Perm) i = i → g i = i ∨ g i = twin i

def screen (color : Fin 100 → Nat) (base : List (Fin 100)) (p : Perm) : Bool :=
  base.all (fun b => decide (color (p⁻¹ ((e0 : Perm) (p b))) = color ((e0 : Perm) b))) &&
    checkFin (fun i => decide ((e0 : Perm) i = i →
      color (p⁻¹ i) = color i ∨ color (p⁻¹ (twin i)) = color i))

theorem screen_of_pair (color : Fin 100 → Nat) (base : List (Fin 100))
    (p h : Perm) (hfix : ∀ b ∈ base, h b = b)
    (hcolor : ∀ x, color (h x) = color x)
    (hc : (e0 : Perm) * (p * h) = (p * h) * (e0 : Perm))
    (hp : PairCondition (p * h)) : screen color base p = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    intro b hb
    apply decide_eq_true_eq.mpr
    have he := congrArg (fun q : Perm => q b) hc
    change (e0 : Perm) (p (h b)) = p (h ((e0 : Perm) b)) at he
    rw [hfix b hb] at he
    have hval : p⁻¹ ((e0 : Perm) (p b)) = h ((e0 : Perm) b) := by
      rw [he]
      exact p.symm_apply_apply _
    rw [hval, hcolor]
  · apply List.all_eq_true.mpr
    intro n hn
    have hn' : n < 100 := List.mem_range.mp hn
    simp only [dif_pos hn']
    apply decide_eq_true_eq.mpr
    intro hi
    rcases hp ⟨n, hn'⟩ hi with he | he
    · left
      have hval : p⁻¹ ⟨n, hn'⟩ = h ⟨n, hn'⟩ := by
        exact (congrArg p.symm he).symm.trans (p.symm_apply_apply _)
      rw [hval, hcolor]
    · right
      have hval : p⁻¹ (twin ⟨n, hn'⟩) = h ⟨n, hn'⟩ := by
        exact (congrArg p.symm he).symm.trans (p.symm_apply_apply _)
      rw [hval, hcolor]

theorem advance {n m t : Nat} (H K : Subgroup Perm)
    (p : Fin n → Perm) (q : Fin m → Perm) (rep : Fin t → Perm)
    (color : Fin 100 → Nat) (base : List (Fin 100))
    (hd : ∀ h ∈ H, ∃ j, ∃ v ∈ K, h = rep j * v)
    (hK : ∀ v ∈ K, (∀ b ∈ base, v b = b) ∧ (∀ x, color (v x) = color x))
    (ht : ∀ i j, screen color base (p i * rep j) = true → ∃ l, p i * rep j = q l)
    {g : Perm} (hc : (e0 : Perm) * g = g * (e0 : Perm)) (hp : PairCondition g)
    (hg : ∃ i, ∃ h ∈ H, g = p i * h) : ∃ i, ∃ h ∈ K, g = q i * h := by
  obtain ⟨i, h, hh, he⟩ := hg
  obtain ⟨j, v, hv, hf⟩ := hd h hh
  have heq : g = (p i * rep j) * v := by rw [he, hf, mul_assoc]
  have hs := screen_of_pair color base (p i * rep j) v (hK v hv).1 (hK v hv).2
    (by simpa only [← heq] using hc) (by simpa only [← heq] using hp)
  obtain ⟨l, hl⟩ := ht i j hs
  exact ⟨l, v, hv, by rw [heq, hl]⟩

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure.KernelBound
