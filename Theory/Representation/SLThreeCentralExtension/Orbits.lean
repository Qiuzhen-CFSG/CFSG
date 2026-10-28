module

public import Theory.Representation.SLThreeCentralExtension
public import Theory.Representation.PSL3Two.NaturalOrbits
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.FinCases

/-!
# The nonfixed orbit in the binary SL₃ natural extension

The natural action is transitive on ordered distinct nonzero pairs. If an
orbit upstairs met each nonzero fiber of a central two-element kernel only
once, its equivariant section would have a constant additivity defect.
Shifting each nonzero lift by that fixed defect gives a linear equivariant
section, contradicting indecomposability. Thus the original extension has
one orbit outside its fixed line.

Source: Aschbacher--Smith, 12.4.7 and B.4.8(2), printed pp.814 and 91.
-/

@[expose] public section
open Representation Module
namespace Representation.OneCohomology.SLThreeCentralExtension
open BinaryLinearThree

private theorem pair_independent (a b : Vector) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) : LinearIndependent (ZMod 2) ![a,b] := by
  rw [linearIndependent_fin2]
  refine ⟨hb, ?_⟩
  intro c
  have hc : c = 0 ∨ c = 1 := by revert c; decide
  rcases hc with rfl | rfl
  · simpa using ha.symm
  · simpa using hab.symm

private theorem natural_pair_transitive (a b c d : Vector)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hc : c ≠ 0) (hd : d ≠ 0) (hcd : c ≠ d) :
    ∃ g : BinaryLinearThree.Group, W g a = c ∧ W g b = d := by
  let ba := (pair_independent a b ha hb hab).linearCombinationEquiv
  let bc := (pair_independent c d hc hd hcd).linearCombinationEquiv
  let f := ba.symm.trans bc
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have h0 : e a = c := by
    have h := he (ba (Finsupp.single 0 1))
    simpa [f, ba, bc] using h.symm
  have h1 : e b = d := by
    have h := he (ba (Finsupp.single 1 1))
    simpa [f, ba, bc] using h.symm
  have hdet : (LinearMap.toMatrix' e.toLinearMap).det = 1 := by
    rw [LinearMap.det_toMatrix']
    exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ e.isUnit_det'.ne_zero
  refine ⟨⟨LinearMap.toMatrix' e.toLinearMap, hdet⟩, ?_, ?_⟩
  · change Matrix.toLin' (LinearMap.toMatrix' e.toLinearMap) a = c
    rwa [Matrix.toLin'_toMatrix']
  · change Matrix.toLin' (LinearMap.toMatrix' e.toLinearMap) b = d
    rwa [Matrix.toLin'_toMatrix']

variable {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
  (ρ : Representation (ZMod 2) BinaryLinearThree.Group X)

private theorem split_of_equivariant_section
    (p : ρ.IntertwiningMap W) (z : X)
    (hker : ∀ x, p x = 0 ↔ x = 0 ∨ x = z)
    (hfix : ∀ g, ρ g z = z)
    (s : Vector → X) (hps : ∀ v, p (s v) = v)
    (hseq : ∀ g v, s (W g v) = ρ g (s v)) :
    ∃ t : Vector →ₗ[ZMod 2] X, p.toLinearMap.comp t = LinearMap.id ∧
      ∀ g v, t (W g v) = ρ g (t v) := by
  let a : Vector := ![1,0,0]
  let b : Vector := ![0,1,0]
  let c := s a + s b + s (a+b)
  have hc : p c = 0 := by
    simp only [c, map_add, hps]
    exact ZModModule.add_self (a+b)
  have hcf : ∀ g, ρ g c = c := by
    rcases (hker c).mp hc with h | h
    · simp [h]
    · simpa [h] using hfix
  have hdef : ∀ u v : Vector, u ≠ 0 → v ≠ 0 → u ≠ v →
      s u + s v + s (u+v) = c := by
    intro u v hu hv huv
    obtain ⟨g, hg, hg'⟩ := natural_pair_transitive a b u v
      (by decide) (by decide) (by decide) hu hv huv
    rw [← hg, ← hg', ← map_add, hseq, hseq, hseq, ← map_add, ← map_add]
    exact hcf g
  let t : Vector → X := fun v => if v = 0 then 0 else s v + c
  have ht0 : t 0 = 0 := by simp [t]
  have htadd : ∀ u v, t (u+v) = t u + t v := by
    intro u v
    by_cases hu : u = 0
    · simp [hu, ht0]
    by_cases hv : v = 0
    · simp [hv, ht0]
    by_cases huv : u = v
    · subst v
      simp [ZModModule.add_self, ht0]
    have huv0 : u+v ≠ 0 := by
      rw [← ZModModule.sub_eq_add]
      exact sub_ne_zero.mpr huv
    simp only [t, if_neg hu, if_neg hv, if_neg huv0]
    have hh := hdef u v hu hv huv
    have hh' := congrArg (fun x => x + s (u+v)) hh
    have he : s u + s v = c + s (u+v) := by
      simpa only [add_assoc, ZModModule.add_self, add_zero] using hh'
    calc
      s (u+v) + c = s u + s v := (he.trans (add_comm _ _)).symm
      _ = (s u+c) + (s v+c) := by
        rw [add_add_add_comm, ZModModule.add_self, add_zero]
  let tl : Vector →ₗ[ZMod 2] X := {
    toFun := t
    map_add' := htadd
    map_smul' := by
      intro r v
      have hr : r = 0 ∨ r = 1 := by revert r; decide
      rcases hr with rfl | rfl
      · simpa using ht0
      · simp }
  refine ⟨tl, ?_, ?_⟩
  · apply LinearMap.ext
    intro v
    change p (t v) = v
    by_cases hv : v = 0
    · simp [hv, ht0]
    · simp [t, hv, hps, hc]
  · intro g v
    change t (W g v) = ρ g (t v)
    by_cases hv : v = 0
    · simp [hv, ht0]
    have hgv : W g v ≠ 0 := by
      intro he
      have hh := congrArg (W g⁻¹) he
      apply hv
      simpa [← Module.End.mul_apply, ← map_mul] using hh
    simp [t, hv, hgv, hseq, hcf]

/-- A nonsplit natural extension by its original fixed line has a single
orbit outside that line. No fusion or module-classification premise is used. -/
theorem transitive_outside_kernel
    (p : ρ.IntertwiningMap W) (z : X) (hz : z ≠ 0)
    (hker : ∀ x, p x = 0 ↔ x = 0 ∨ x = z)
    (hfix : ∀ g, ρ g z = z)
    (hind : ∀ A B : Submodule (ZMod 2) X,
      (∀ g v, v ∈ A → ρ g v ∈ A) →
      (∀ g v, v ∈ B → ρ g v ∈ B) → IsCompl A B → A = ⊥ ∨ B = ⊥)
    (x y : X) (hx : p x ≠ 0) (hy : p y ≠ 0) :
    ∃ g, ρ g x = y := by
  classical
  have hzker : p z = 0 := (hker z).mpr (Or.inr rfl)
  have hxz : ∃ g, ρ g x = x+z := by
    by_contra hn
    have huniq : ∀ g h, p (ρ g x) = p (ρ h x) → ρ g x = ρ h x := by
      intro g h he
      have hh : p (ρ g x - ρ h x) = 0 := by simp [he]
      rcases (hker _).mp hh with hh | hh
      · exact sub_eq_zero.mp hh
      · apply False.elim
        apply hn
        refine ⟨h⁻¹*g, ?_⟩
        have hh' := congrArg (ρ h⁻¹) (sub_eq_iff_eq_add.mp hh)
        simpa [map_add, hfix, ← Module.End.mul_apply, ← map_mul, add_comm] using hh'
    have hex : ∀ v : Vector, v ≠ 0 → ∃ w : X,
        (∃ g, ρ g x = w) ∧ p w = v := by
      intro v hv
      obtain ⟨g, hg⟩ := natural_transitive_nonzero (p x) v hx hv
      refine ⟨ρ g x, ⟨g, rfl⟩, ?_⟩
      rw [p.isIntertwining, hg]
    let s : Vector → X := fun v => if hv : v = 0 then 0 else Classical.choose (hex v hv)
    have hs0 : s 0 = 0 := by simp [s]
    have hs : ∀ v, v ≠ 0 → (∃ g, ρ g x = s v) ∧ p (s v) = v := by
      intro v hv
      simpa only [s, dif_neg hv] using Classical.choose_spec (hex v hv)
    have hps : ∀ v, p (s v) = v := by
      intro v
      by_cases hv : v = 0
      · simp [hv, hs0]
      · exact (hs v hv).2
    have hseq : ∀ g v, s (W g v) = ρ g (s v) := by
      intro g v
      by_cases hv : v = 0
      · simp [hv, hs0]
      have hgv : W g v ≠ 0 := by
        intro he
        apply hv
        have hh := congrArg (W g⁻¹) he
        simpa [← Module.End.mul_apply, ← map_mul] using hh
      obtain ⟨a, ha⟩ := (hs (W g v) hgv).1
      obtain ⟨b, hb⟩ := (hs v hv).1
      have he : p (ρ a x) = p (ρ (g*b) x) := by
        rw [ha, hps, map_mul, Module.End.mul_apply, hb, p.isIntertwining, hps]
      simpa [map_mul, Module.End.mul_apply, ha, hb] using huniq a (g*b) he
    obtain ⟨t, ht, hte⟩ := split_of_equivariant_section ρ p z hker hfix s hps hseq
    have hcompl : IsCompl p.toLinearMap.ker t.range := by
      constructor
      · rw [disjoint_iff]
        apply bot_unique
        rintro w ⟨hw, v, rfl⟩
        have hv : v = 0 := by simpa using LinearMap.congr_fun ht v |>.symm.trans hw
        simp [hv]
      · rw [codisjoint_iff]
        apply top_unique
        intro w _
        have hkerw : w-t (p w) ∈ p.toLinearMap.ker := by
          change p (w-t (p w)) = 0
          rw [map_sub, show p (t (p w)) = p w from LinearMap.congr_fun ht (p w), sub_self]
        have hsum := Submodule.add_mem_sup hkerw (show t (p w) ∈ t.range from ⟨_, rfl⟩)
        simpa using hsum
    have hkstable : ∀ g v, v ∈ p.toLinearMap.ker → ρ g v ∈ p.toLinearMap.ker := by
      intro g v hv
      change p (ρ g v) = 0
      rw [p.isIntertwining, show p v = 0 from hv, map_zero]
    have htstable : ∀ g v, v ∈ t.range → ρ g v ∈ t.range := by
      rintro g _ ⟨v, rfl⟩
      exact ⟨W g v, hte g v⟩
    rcases hind _ _ hkstable htstable hcompl with hk | hr
    · exact hz (show z ∈ (⊥ : Submodule (ZMod 2) X) from hk ▸ hzker)
    · have hv := LinearMap.congr_fun ht (p x)
      have ht0 : t (p x) = 0 := by
        exact (show t (p x) ∈ (⊥ : Submodule (ZMod 2) X) from
          hr ▸ (show t (p x) ∈ t.range from ⟨_, rfl⟩))
      exact hx (by simpa [ht0] using hv.symm)
  obtain ⟨g, hg⟩ := natural_transitive_nonzero (p x) (p y) hx hy
  have he : p (y-ρ g x) = 0 := by rw [map_sub, p.isIntertwining, hg, sub_self]
  rcases (hker _).mp he with he | he
  · exact ⟨g, (sub_eq_zero.mp he).symm⟩
  · obtain ⟨h, hh⟩ := hxz
    refine ⟨g*h, ?_⟩
    rw [map_mul, Module.End.mul_apply, hh, map_add, hfix]
    exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp he).symm

end Representation.OneCohomology.SLThreeCentralExtension
