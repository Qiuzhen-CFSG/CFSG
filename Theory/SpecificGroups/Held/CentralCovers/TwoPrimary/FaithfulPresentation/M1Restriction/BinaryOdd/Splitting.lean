module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd.Parity
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryImages
import Mathlib.Tactic.Group

/-!
# Excluding a common central twist of the marked M₁ generators

If the three marked lifts multiplied by a central involution satisfy the
local presentation, its checked upper bound and the concrete M₁ lower bound
make the resulting local map injective. Inverting that map gives a section
on the actual source subgroup. Its pointwise difference from the original
lift is a homomorphism into the central binary kernel. The checked Schreier
parity identity says the product of the three difference values is one;
all three values are the common twist, which must therefore be trivial.

Sources: John Bray's ATLAS `Held/Model/Source/HeG1-P1.M`; the exact local
bounds in `M1Restriction` and the Schreier identity in `BinaryOdd.Parity`.
-/

public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd
open Subgroup.CosetWordCertificate PerfectCentralCovering

private theorem local_section {E : Type*} [Group E]
    (f : E →* He) (g : Fin 3 → E)
    (hrel : ∀ i, eval g (relationLetters i) = 1)
    (hg : ∀ i, f (g i) = concreteGenerator i) :
    ∃ β : m1 →* E, (∀ p, f (β p) = m1Map p) ∧
      ∀ i, β ⟨liftedGenerator i, liftedGenerator_mem i⟩ = g i := by
  let l : LocalPresentation →* E := PresentedGroup.toGroup (f := g) (by
    rintro _ ⟨i,rfl⟩
    exact hrel i)
  have hl (i : Fin 3) : l (PresentedGroup.of i) = g i := PresentedGroup.toGroup.of _
  let q := f.comp l
  have hr : q.range = concreteSubgroup := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
      (Set.range localRelator), MonoidHom.map_closure, ← Set.range_comp]
    change Subgroup.closure (Set.range (fun i => f (l (PresentedGroup.of i)))) = _
    simp only [hl, hg]
    rfl
  have hb := localPresentation_bound
  let := hb.1
  have hc : Nat.card LocalPresentation ≤ Nat.card q.range := by
    rw [hr]
    exact hb.2.trans concrete_lower_bound
  let e : LocalPresentation ≃* q.range := MulEquiv.ofBijective q.rangeRestrict
    (q.rangeRestrict_surjective.bijective_of_nat_card_le hc)
  let j : m1 →* q.range := m1Map.codRestrict q.range (fun p => by
    rw [hr, ← m1Map_range]
    exact ⟨p,rfl⟩)
  let β : m1 →* E := l.comp (e.symm.toMonoidHom.comp j)
  refine ⟨β, ?_, ?_⟩
  · intro p
    change q (e.symm (j p)) = m1Map p
    exact congrArg Subtype.val (e.apply_symm_apply (j p))
  · intro i
    have hj : j ⟨liftedGenerator i, liftedGenerator_mem i⟩ = e (PresentedGroup.of i) := by
      apply Subtype.ext
      change m1Map ⟨liftedGenerator i, liftedGenerator_mem i⟩ = f (l (PresentedGroup.of i))
      rw [hl, hg]
      exact m1Map_apply _
    change l (e.symm (j ⟨liftedGenerator i, liftedGenerator_mem i⟩)) = g i
    rw [hj, e.symm_apply_apply, hl]

/-- A common central binary twist satisfying the local presentation is trivial.
The cardinal bound gives a local section; its difference character contradicts
binary parity unless the twist is one. -/
theorem common_twist_eq_one {E : Type*} [Group E] [Finite E]
    (f : Cover E He) (hcard : Nat.card f.toMonoidHom.ker = 2)
    (h : Presentation →* E) (ht : f.toMonoidHom.comp h = presentationMap)
    (z : E) (hzker : z ∈ f.toMonoidHom.ker)
    (hrel : ∀ i, eval (fun j => h (liftedGenerator j) * z) (relationLetters i) = 1) : z = 1 := by
  have hz := f.ker_le_center hzker
  have hs : z ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨z,hzker⟩ : f.toMonoidHom.ker))
    rw [hcard] at hh
    exact congrArg Subtype.val hh
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hs)
  have hm (p : Presentation) : f.toMonoidHom (h p) = presentationMap p :=
    DFunLike.congr_fun ht p
  obtain ⟨β,hβ,hβgen⟩ := local_section f.toMonoidHom
    (fun i => h (liftedGenerator i) * z) hrel (fun i => by
      rw [map_mul, hzker, mul_one, hm]
      rfl)
  have hk (p : m1) : h p.val * (β p)⁻¹ ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hm, hβ, m1Map_apply, mul_inv_cancel]
  let d : m1 →* E := {
    toFun p := h p.val * (β p)⁻¹
    map_one' := by simp
    map_mul' p q := by
      have hc := Subgroup.mem_center_iff.mp (f.ker_le_center (hk q)) (β p)⁻¹
      simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
      calc
        _ = h p.val * (h q.val * (β q)⁻¹) * (β p)⁻¹ := by group
        _ = (h p.val * (β p)⁻¹) * (h q.val * (β q)⁻¹) := by
          rw [mul_assoc, ← hc, ← mul_assoc] }
  let : CommGroup f.toMonoidHom.ker := {
    mul_comm a b := Subtype.ext (Subgroup.mem_center_iff.mp (f.ker_le_center a.property) b).symm }
  let χ : m1 →* f.toMonoidHom.ker := d.codRestrict _ hk
  have hχsq (a : f.toMonoidHom.ker) : a ^ 2 = 1 := by
    have ha := pow_card_eq_one' (x := a)
    rwa [hcard] at ha
  have hd (i : Fin 3) : (χ ⟨liftedGenerator i, liftedGenerator_mem i⟩ : E) = z := by
    change h (liftedGenerator i) * (β ⟨liftedGenerator i, liftedGenerator_mem i⟩)⁻¹ = z
    rw [hβgen, mul_inv_rev, hzi, ← mul_assoc, Subgroup.mem_center_iff.mp hz]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hp := congrArg Subtype.val (marked_binary_parity hχsq χ)
  change (χ ⟨liftedGenerator 0, liftedGenerator_mem 0⟩ : E) *
    (χ ⟨liftedGenerator 1, liftedGenerator_mem 1⟩ : E) *
    (χ ⟨liftedGenerator 2, liftedGenerator_mem 2⟩ : E) = 1 at hp
  rw [hd, hd, hd, ← pow_two, hs, one_mul] at hp
  exact hp
end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd
