module
public import Theory.Representation.FirstCohomologyAutomorphism
public import Theory.Representation.FirstCohomologyConjugationSplitting
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Normalizers detected by first cohomology

If an abelian subgroup R is normalized by H, the intersection R ∩ H is
an H-module. Vanishing first cohomology makes every normalizer in R a
product of an element of R ∩ H and a centralizer of H. Consequently a
trivial centralizer gives N_R(H)=R ∩ H. The coordinates retain the actual
quotient and conjugation action.

Source: Aschbacher–Smith C.1.35, printed p.138.
-/


@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Representation.OneCohomology
variable {k G B V : Type*} [Field k] [Group G] [Group B]
  [AddCommGroup V] [Module k V]

/-- An abelian normalizing group with trivial centralizer has no extra
normalizers when the first cohomology of its intersection vanishes. -/
theorem inf_normalizer_eq_of_H1_zero (H R : Subgroup G) [IsMulCommutative R]
    (hHR : H ≤ normalizer (R : Set G))
    (f : H →* B) (hf : Function.Surjective f)
    (hk : f.ker = R.subgroupOf H)
    (e : R.subgroupOf H ≃* Multiplicative V) (ρ : Representation k B V)
    (he : ∀ (g : H) (v : V),
      (e.symm (Multiplicative.ofAdd (ρ (f g) v)) : H) =
        g * (e.symm (Multiplicative.ofAdd v) : H) * g⁻¹)
    [Subsingleton (H1 ρ)]
    (hc : R ⊓ centralizer (H : Set G) = ⊥) :
    R ⊓ normalizer (H : Set G) = R ⊓ H := by
  apply le_antisymm ?_ (inf_le_inf_left _ H.le_normalizer)
  rintro x ⟨hx,hxn⟩
  let α := H.normalizerMonoidHom ⟨x,hxn⟩
  have hd (g : H) : ((α g : H) : G) * (g : G)⁻¹ ∈ R := by
    change x * (g : G) * x⁻¹ * (g : G)⁻¹ ∈ R
    have hn := (mem_normalizer_iff.mp (hHR g.property) x⁻¹).mp (R.inv_mem hx)
    convert R.mul_mem hx hn using 1
    group
  have hfix (a : H) (ha : a ∈ R.subgroupOf H) : α a = a := by
    apply Subtype.ext
    change x * (a : G) * x⁻¹ = a
    have hm := congrArg Subtype.val (mul_comm (⟨x,hx⟩ : R) ⟨a,ha⟩)
    change x * (a : G) = (a : G) * x at hm
    rw [hm,mul_inv_cancel_right]
  obtain ⟨a,ha⟩ := automorphism_inner_of_H1_zero (R.subgroupOf H) f hf hk e ρ he α
    (fun g => by
      have hh : α g * g⁻¹ ∈ f.ker := hk.symm ▸ hd g
      exact mul_inv_eq_one.mp (by simpa only [MonoidHom.mem_ker,map_mul,map_inv] using hh)) hfix
  have hz : (a : H).val * x ∈ R ⊓ centralizer (H : Set G) := by
    refine ⟨R.mul_mem a.property hx,mem_centralizer_iff.mpr ?_⟩
    intro g hg
    have hh := congrArg Subtype.val (ha ⟨g,hg⟩)
    change x * g * x⁻¹ = (a : H).val⁻¹ * g * (a : H).val at hh
    have hh' := congrArg (fun z : G => (a : H).val * z * x) hh
    simpa only [mul_assoc,mul_inv_cancel_left,inv_mul_cancel_right,inv_mul_cancel,mul_one] using hh'.symm
  have hz' : (a : H).val * x = 1 := mem_bot.mp (hc.le hz)
  refine ⟨hx,?_⟩
  have heq : x = (a : H).val⁻¹ := eq_inv_of_mul_eq_one_right hz'
  rw [heq]
  exact H.inv_mem (a : H).property

/-- A marked commutator submodule suffices: cohomology first identifies the
whole intersection, then controls its normalizer. -/
theorem inf_normalizer_eq_of_H1_section (H R D : Subgroup G) [IsMulCommutative R]
    (hHR : H ≤ normalizer (R : Set G))
    (f : H →* B) (hf : Function.Surjective f)
    (hk : f.ker = R.subgroupOf H) (hDH : D ≤ H) (hDR : D ≤ R)
    (e : D ≃* Multiplicative V) (ρ : Representation k B V)
    (he : ∀ (g : H) (v : V),
      (e.symm (Multiplicative.ofAdd (ρ (f g) v)) : G) =
        (g : G) * (e.symm (Multiplicative.ofAdd v) : G) * (g : G)⁻¹)
    [Subsingleton (H1 ρ)]
    (hd : ∀ (g : H) (u : (R ⊓ H : Subgroup G)),
      (g : G) * u * (g : G)⁻¹ * (u : G)⁻¹ ∈ D)
    (hc : R ⊓ centralizer (H : Set G) = ⊥) :
    R ⊓ normalizer (H : Set G) = D := by
  have hker (g : H) (hg : f g = 1) : (g : G) ∈ centralizer (R ⊓ H : Set G) := by
    have hgR : (g : G) ∈ R := hk.le hg
    apply mem_centralizer_iff.mpr
    intro x hx
    exact congrArg Subtype.val (mul_comm (⟨x,hx.1⟩ : R) ⟨g,hgR⟩)
  have hh := sup_centralizer_eq_of_conjugation_H1 H (R ⊓ H) D
    (le_inf hDR hDH) f hf ρ e he hker hd
  have hz : (R ⊓ H) ⊓ centralizer (H : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ inf_le_left).trans hc.le)
  rw [hz,sup_bot_eq] at hh
  let eN : R.subgroupOf H ≃* D := {
    toFun := fun a => ⟨(a : H),hh.ge ⟨a.property,(a : H).property⟩⟩
    invFun := fun a => ⟨⟨a,hDH a.property⟩,hDR a.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  have hen (g : H) (v : V) :
      ((eN.trans e).symm (Multiplicative.ofAdd (ρ (f g) v)) : H) =
        g * ((eN.trans e).symm (Multiplicative.ofAdd v) : H) * g⁻¹ := by
    apply Subtype.ext
    exact he g v
  exact (inf_normalizer_eq_of_H1_zero H R hHR f hf hk
    (eN.trans e) ρ hen hc).trans hh.symm
end Representation.OneCohomology
