module
public import Theory.Representation.FirstCohomology
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-!
# Splitting actual conjugation extensions by vanishing first cohomology

The displacement of an element under conjugation is a crossed homomorphism
in the given abelian section. If the action factors through the specified
surjection and its first cohomology vanishes, subtracting a principal
cocycle gives an element centralized by the whole actor. This splits the
original subgroup as its section times its fixed subgroup. An actor
subgroup with no fixed vectors on the section has the same centralizer.

The coordinates retain the literal subgroup inclusion and conjugation.
No splitting or fixed-subgroup equality is assumed.
Source application: Aschbacher--Smith, original 4.3.9, printed p.616;
I.1.5--6 for the cohomological argument.
-/

public section
open Subgroup
namespace Representation.OneCohomology
variable {k G A V : Type*} [Field k] [Group G] [Group A]
  [AddCommGroup V] [Module k V]

theorem conjugation_fixed_lift (K D : Subgroup G) (f : K →* A)
    (hf : Function.Surjective f) (ρ : Representation k A V)
    (e : D ≃* Multiplicative V)
    (he : ∀ (g : K) (v : V),
      (e.symm (Multiplicative.ofAdd (ρ (f g) v)) : G) =
        g * (e.symm (Multiplicative.ofAdd v) : G) * (g : G)⁻¹)
    [Subsingleton (H1 ρ)] (u : G)
    (hker : ∀ g : K, f g = 1 → (g : G) * u = u * g)
    (hdisp : ∀ g : K, (g : G) * u * (g : G)⁻¹ * u⁻¹ ∈ D) :
    ∃ a : D, (a : G)⁻¹ * u ∈ centralizer (K : Set G) := by
  classical
  let d (g : K) : D := ⟨(g : G) * u * (g : G)⁻¹ * u⁻¹, hdisp g⟩
  let c (g : K) : V := (e (d g)).toAdd
  have hc (g : K) : (e.symm (Multiplicative.ofAdd (c g)) : G) =
      (g : G) * u * (g : G)⁻¹ * u⁻¹ :=
    congrArg Subtype.val (e.symm_apply_apply (d g))
  have hdesc {g t : K} (hgt : f g = f t) : c g = c t := by
    have h := hker (t⁻¹ * g) (by rw [map_mul, map_inv, hgt, inv_mul_cancel])
    have hd : (g : G) * u * (g : G)⁻¹ * u⁻¹ =
        (t : G) * u * (t : G)⁻¹ * u⁻¹ := by
      change (t : G)⁻¹ * g * u = u * ((t : G)⁻¹ * g) at h
      have hh := congrArg (fun z : G => (t : G) * z * (g : G)⁻¹ * u⁻¹) h
      simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_right] using hh
    exact congrArg (fun a : D => (e a).toAdd) (Subtype.ext hd)
  have hmul (g t : K) : c (g * t) = ρ (f g) (c t) + c g := by
    apply Multiplicative.ofAdd.injective
    apply e.symm.injective
    apply Subtype.ext
    rw [hc]
    change _ = (e.symm (Multiplicative.ofAdd (ρ (f g) (c t)) *
      Multiplicative.ofAdd (c g)) : G)
    rw [map_mul]
    change _ = (e.symm (Multiplicative.ofAdd (ρ (f g) (c t))) : G) *
      (e.symm (Multiplicative.ofAdd (c g)) : G)
    rw [he, hc, hc]
    simp only [coe_mul, mul_inv_rev]
    group
  let b (a : A) : K := (hf a).choose
  have hb (a : A) : f (b a) = a := (hf a).choose_spec
  let z : cocycles ρ := ⟨fun a => c (b a), by
    intro a t
    exact (hdesc (show f (b (a*t)) = f (b a * b t) by rw [map_mul,hb,hb,hb])).trans
      (by rw [hmul, hb])⟩
  obtain ⟨v,hv⟩ := (classMap_eq_zero_iff ρ z).mp (Subsingleton.elim _ _)
  have hcv (g : K) : c g = ρ (f g) v - v := by
    exact (hdesc (hb (f g)).symm).trans
      (congrArg (fun z : cocycles ρ => z.val (f g)) hv).symm
  let a : D := e.symm (Multiplicative.ofAdd v)
  refine ⟨a, mem_centralizer_iff.mpr ?_⟩
  intro g hg
  have hh := hc ⟨g,hg⟩
  rw [hcv, sub_eq_add_neg] at hh
  change (e.symm (Multiplicative.ofAdd (ρ (f ⟨g,hg⟩) v) *
    (Multiplicative.ofAdd v)⁻¹) : G) = _ at hh
  rw [map_mul, map_inv] at hh
  change (e.symm (Multiplicative.ofAdd (ρ (f ⟨g,hg⟩) v)) : G) * (a : G)⁻¹ = _ at hh
  rw [he] at hh
  change g * (a : G) * g⁻¹ * (a : G)⁻¹ = g * u * g⁻¹ * u⁻¹ at hh
  have hh' := congrArg (fun z : G => (g * (a : G))⁻¹ * z * u * g) hh
  group at hh'
  have hh'' := congrArg (fun z : G => g * z) hh'
  simpa only [zpow_neg_one, mul_assoc, mul_inv_cancel_left] using hh''.symm

theorem sup_centralizer_eq_of_conjugation_H1 (K E D : Subgroup G)
    (hDE : D ≤ E) (f : K →* A) (hf : Function.Surjective f)
    (ρ : Representation k A V) (e : D ≃* Multiplicative V)
    (he : ∀ (g : K) (v : V),
      (e.symm (Multiplicative.ofAdd (ρ (f g) v)) : G) =
        g * (e.symm (Multiplicative.ofAdd v) : G) * (g : G)⁻¹)
    [Subsingleton (H1 ρ)]
    (hker : ∀ g : K, f g = 1 → (g : G) ∈ centralizer (E : Set G))
    (hdisp : ∀ (g : K) (u : E), (g : G) * u * (g : G)⁻¹ * (u : G)⁻¹ ∈ D) :
    D ⊔ (E ⊓ centralizer (K : Set G)) = E := by
  apply le_antisymm (sup_le hDE inf_le_left)
  intro u hu
  obtain ⟨a,ha⟩ := conjugation_fixed_lift K D f hf ρ e he u
    (fun g hg => (mem_centralizer_iff.mp (hker g hg) u hu).symm)
    (fun g => hdisp g ⟨u,hu⟩)
  have hz : (a : G)⁻¹ * u ∈ E := E.mul_mem (E.inv_mem (hDE a.property)) hu
  simpa using (D ⊔ (E ⊓ centralizer (K : Set G))).mul_mem
    (mem_sup_left a.property) (mem_sup_right ⟨hz,ha⟩)

theorem centralizer_eq_of_conjugation_H1 (K L E D : Subgroup G)
    (hLK : L ≤ K) (f : K →* A) (hf : Function.Surjective f)
    (ρ : Representation k A V) (e : D ≃* Multiplicative V)
    (he : ∀ (g : K) (v : V),
      (e.symm (Multiplicative.ofAdd (ρ (f g) v)) : G) =
        g * (e.symm (Multiplicative.ofAdd v) : G) * (g : G)⁻¹)
    [Subsingleton (H1 ρ)]
    (hker : ∀ g : K, f g = 1 → (g : G) ∈ centralizer (E : Set G))
    (hdisp : ∀ (g : K) (u : E), (g : G) * u * (g : G)⁻¹ * (u : G)⁻¹ ∈ D)
    (hfixed : D ⊓ centralizer (L : Set G) = ⊥) :
    E ⊓ centralizer (L : Set G) = E ⊓ centralizer (K : Set G) := by
  apply le_antisymm
  · intro u hu
    obtain ⟨a,ha⟩ := conjugation_fixed_lift K D f hf ρ e he u
      (fun g hg => (mem_centralizer_iff.mp (hker g hg) u hu.1).symm)
      (fun g => hdisp g ⟨u,hu.1⟩)
    have haL : (a : G) ∈ centralizer (L : Set G) := by
      have hh := (centralizer (L : Set G)).mul_mem hu.2
        ((centralizer (L : Set G)).inv_mem (centralizer_le hLK ha))
      simpa using hh
    have ha1 : (a : G) = 1 := mem_bot.mp (hfixed.le ⟨a.property,haL⟩)
    exact ⟨hu.1, by simpa [ha1] using ha⟩
  · exact inf_le_inf_left _ (centralizer_le hLK)
end Representation.OneCohomology

namespace Representation.OneCohomology
variable {k A V W : Type*} [Field k] [Group A]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

theorem H1_prod_subsingleton (ρ : Representation k A V) (σ : Representation k A W)
    [Subsingleton (H1 ρ)] [Subsingleton (H1 σ)] :
    Subsingleton (H1 (ρ.prod σ)) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro f _
  let f₁ : cocycles ρ := ⟨fun g => (f.val g).1, by
    intro g t
    exact congrArg Prod.fst (f.property g t)⟩
  let f₂ : cocycles σ := ⟨fun g => (f.val g).2, by
    intro g t
    exact congrArg Prod.snd (f.property g t)⟩
  obtain ⟨v,hv⟩ := (classMap_eq_zero_iff ρ f₁).mp (Subsingleton.elim _ _)
  obtain ⟨w,hw⟩ := (classMap_eq_zero_iff σ f₂).mp (Subsingleton.elim _ _)
  refine ⟨(v,w), ?_⟩
  apply Subtype.ext
  funext g
  exact Prod.ext (congrArg (fun z : cocycles ρ => z.val g) hv)
    (congrArg (fun z : cocycles σ => z.val g) hw)
end Representation.OneCohomology

