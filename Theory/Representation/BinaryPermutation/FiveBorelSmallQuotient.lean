module
public import Theory.Representation.BinaryPermutation.FiveBorelTwoAction

/-!
# Small Borel quotients of the binary A₅ module

Every invariant subgroup of the deleted five-point module larger than its
fixed line contains the Borel commutator three-space. Two orbit calculations
on sixteen vectors prove this without enumerating subspaces. Consequently
any Borel-invariant homomorphism to a group of order at most four kills
all Borel displacements. Sylow conjugacy transports the statement to every
Borel, and restrictions to the two summands give the diagonal two-copy case.

The original local Cartan application uses the actual image of the omega-span
in CT/O₂(CT), retaining its entire kernel. Source: Aschbacher--Smith 5.1.13,
printed pp.635--638, refs/quasithin.pdf; binary permutation conventions of B.3.
-/

public noncomputable section
open Subgroup
namespace BinaryPermutation.FiveBorelSmallQuotient
open AlternatingFiveFlag AlternatingFiveBorel FiveCentralizerGeometry
local instance : DecidablePred (· ∈ B) := fun g => inferInstanceAs (Decidable (g.val 4=4))
local instance : Fintype B := Subtype.fintype _

private theorem difference_not_line : ∀ x : Space, x ≠ 0 → x ≠ z →
    ∃ g : B, rho g.val.val x - x ≠ 0 ∧ rho g.val.val x - x ≠ z := by
  decide +kernel

private theorem sum_to_line : ∀ x : Space, x.val 4 = 0 → x ≠ 0 → x ≠ z →
    ∃ g : B, rho g.val.val x + x = z := by
  decide +kernel

/-- Every invariant subgroup larger than the fixed line contains the Borel commutator. -/
theorem three_le_of_large_invariant (E : Subgroup (Multiplicative Space))
    (hsize : 2 < Nat.card E)
    (hi : ∀ g : B, ∀ x ∈ E, Multiplicative.ofAdd (rho g.val.val x.toAdd) ∈ E) :
    three ≤ E := by
  have hn : ¬ E ≤ line := fun he => by
    have hc := card_le_of_le he
    rw [line_card] at hc
    omega
  obtain ⟨x,hx,hxn⟩ := SetLike.not_le_iff_exists.mp hn
  have hx0 : x.toAdd ≠ 0 := fun hh => hxn (Or.inl hh)
  have hxz : x.toAdd ≠ z := fun hh => hxn (Or.inr hh)
  obtain ⟨g,hg0,hgz⟩ := difference_not_line x.toAdd hx0 hxz
  let y := rho g.val.val x.toAdd - x.toAdd
  have hy : Multiplicative.ofAdd y ∈ E := by
    simpa only [y, ofAdd_sub, ofAdd_toAdd, div_eq_mul_inv] using E.mul_mem (hi g x hx) (E.inv_mem hx)
  have hyt : Multiplicative.ofAdd y ∈ three := difference_mem_three g x.toAdd
  obtain ⟨a,ha⟩ := sum_to_line y hyt hg0 hgz
  have hz : Multiplicative.ofAdd z ∈ E := by
    rw [←ha,ofAdd_add]
    exact E.mul_mem (hi a _ hy) hy
  have hl : line ≤ E := by
    rintro v (rfl | rfl)
    · exact E.one_mem
    · exact hz
  have hI : E ⊓ three = three := by
    rcases three_line_irreducible (E ⊓ three) (le_inf hl line_le_three) inf_le_right
      (fun b v hv => ⟨hi b v hv.1,three_invariant b v hv.2⟩) with he | he
    · have hyline : Multiplicative.ofAdd y ∈ line := he ▸ (show Multiplicative.ofAdd y ∈ E ⊓ three from ⟨hy,hyt⟩)
      exact False.elim (hyline.elim hg0 hgz)
    · exact he
  exact hI.symm ▸ inf_le_left

/-- A Borel-invariant map from the deleted five-point module to a group of
order at most four kills every Borel displacement. -/
theorem standard_small_image {D : Type*} [Group D] [Finite D]
    (f : Multiplicative Space →* D) (hD : Nat.card D ≤ 4)
    (hi : ∀ g : B, ∀ x ∈ f.ker,
      Multiplicative.ofAdd (rho g.val.val x.toAdd) ∈ f.ker) :
    ∀ g : B, ∀ x : Space,
      f (Multiplicative.ofAdd (rho g.val.val x)) = f (Multiplicative.ofAdd x) := by
  have hcard : Nat.card (Multiplicative Space) = 16 := by
    change Nat.card Space = 16
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hr : Nat.card f.range ≤ 4 :=
    (Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective).trans hD
  have hc : Nat.card f.ker * Nat.card f.range = 16 := by
    rw [←index_ker,f.ker.card_mul_index,hcard]
  have hk : 2 < Nat.card f.ker := by nlinarith
  have hthree := three_le_of_large_invariant f.ker hk hi
  intro g x
  have hh : f (Multiplicative.ofAdd (rho g.val.val x - x)) = 1 :=
    hthree (difference_mem_three g x)
  rw [ofAdd_sub] at hh
  simpa only [div_eq_mul_inv,map_mul,map_inv,mul_inv_eq_one] using hh

/-- The same small-quotient statement at every Sylow normalizer of A₅. -/
theorem core_small_image {D : Type*} [Group D] [Finite D]
    (P : Sylow 2 (alternatingGroup (Fin 5)))
    (f : Multiplicative Space →* D) (hD : Nat.card D ≤ 4)
    (hi : ∀ a ∈ normalizer (P : Set (alternatingGroup (Fin 5))),
      ∀ x ∈ f.ker, Multiplicative.ofAdd (rho a.val x.toAdd) ∈ f.ker) :
    ∀ a ∈ normalizer (P : Set (alternatingGroup (Fin 5))), ∀ x : Space,
      f (Multiplicative.ofAdd (rho a.val x)) = f (Multiplicative.ofAdd x) := by
  obtain ⟨i,hiP⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer P
  have ht : ∀ i : Fin 5, ∃ g : alternatingGroup (Fin 5), g.val 4 = i := by decide +kernel
  obtain ⟨g,hg⟩ := ht i
  let f' := f.comp ((rho g.val).toAddMonoidHom.toMultiplicative)
  have htrans (b : B) (v : Space) :
      rho g.val (rho b.val.val v) = rho (g * b.val * g⁻¹).val (rho g.val v) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ←Module.End.mul_apply, ←map_mul,
      mul_assoc, inv_mul_cancel, mul_one]
  have hbi (b : B) : g * b.val * g⁻¹ ∈ normalizer (P : Set (alternatingGroup (Fin 5))) := by
    rw [hiP]
    change g.val (b.val.val (g.val.symm i)) = i
    rw [←hg,Equiv.symm_apply_apply,show b.val.val 4 = 4 from b.property]
  have hfi : ∀ b : B, ∀ x ∈ f'.ker,
      Multiplicative.ofAdd (rho b.val.val x.toAdd) ∈ f'.ker := by
    intro b x hx
    change f (Multiplicative.ofAdd (rho g.val (rho b.val.val x.toAdd))) = 1
    rw [htrans]
    exact hi _ (hbi b) _ hx
  intro a ha x
  have hb : g⁻¹*a*g ∈ B := by
    have hai : a.val i = i := by
      have hh : a ∈ MulAction.stabilizer (alternatingGroup (Fin 5)) i := hiP ▸ ha
      exact hh
    change g.val.symm (a.val (g.val 4)) = 4
    rw [hg,hai,←hg,Equiv.symm_apply_apply]
  have hh := standard_small_image f' hD hfi ⟨g⁻¹*a*g,hb⟩ (rho g.val⁻¹ x)
  change f (Multiplicative.ofAdd (rho g.val (rho (g⁻¹*a*g).val (rho g.val⁻¹ x)))) =
    f (Multiplicative.ofAdd (rho g.val (rho g.val⁻¹ x))) at hh
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,←Module.End.mul_apply,←map_mul,
    mul_assoc,mul_inv_cancel_left,inv_mul_cancel_left,mul_inv_cancel,mul_one,map_one,Module.End.one_apply] using hh

/-- A small invariant quotient of the natural deleted module is Borel-fixed. -/
theorem natural_small_image {D : Type*} [Group D] [Finite D]
    (P : Sylow 2 (alternatingGroup (Fin 5)))
    (f : Multiplicative (natural (Fin 5)) →* D) (hD : Nat.card D ≤ 4)
    (hi : ∀ a ∈ normalizer (P : Set (alternatingGroup (Fin 5))),
      ∀ x ∈ f.ker, Multiplicative.ofAdd
        (alternatingNaturalRepresentation (Fin 5) a x.toAdd) ∈ f.ker) :
    ∀ a ∈ normalizer (P : Set (alternatingGroup (Fin 5))),
      ∀ x : natural (Fin 5), f (Multiplicative.ofAdd
        (alternatingNaturalRepresentation (Fin 5) a x)) = f (Multiplicative.ofAdd x) := by
  let e := coreEquivNatural (Fin 5) (by decide)
  let f' := f.comp e.toAddEquiv.toMultiplicative.toMonoidHom
  have hi' : ∀ a ∈ normalizer (P : Set (alternatingGroup (Fin 5))),
      ∀ x ∈ f'.ker, Multiplicative.ofAdd (rho a.val x.toAdd) ∈ f'.ker := by
    intro a ha x hx
    change f (Multiplicative.ofAdd (e (rho a.val x.toAdd))) = 1
    rw [coreEquivNatural_equivariant]
    exact hi a ha _ hx
  intro a ha x
  have hh := core_small_image P f' hD hi' a ha (e.symm x)
  change f (Multiplicative.ofAdd (e (rho a.val (e.symm x)))) =
    f (Multiplicative.ofAdd (e (e.symm x))) at hh
  change f (Multiplicative.ofAdd ((coreEquivNatural (Fin 5) (by decide)) (rho a.val (e.symm x)))) = _ at hh
  rw [coreEquivNatural_equivariant] at hh
  change f (Multiplicative.ofAdd ((naturalRepresentation (Fin 5) a.val) (e (e.symm x)))) = _ at hh
  rw [e.apply_symm_apply] at hh
  exact hh

/-- The diagonal Borel also fixes every quotient of two copies of order at most four. -/
theorem pair_small_image {D : Type*} [Group D] [Finite D]
    (P : Sylow 2 (alternatingGroup (Fin 5)))
    (f : Multiplicative (natural (Fin 5) × natural (Fin 5)) →* D)
    (hD : Nat.card D ≤ 4)
    (hi : ∀ a ∈ normalizer (P : Set (alternatingGroup (Fin 5))),
      ∀ x ∈ f.ker, Multiplicative.ofAdd
        (alternatingNaturalRepresentation (Fin 5) a x.toAdd.1,
         alternatingNaturalRepresentation (Fin 5) a x.toAdd.2) ∈ f.ker) :
    ∀ a ∈ normalizer (P : Set (alternatingGroup (Fin 5))),
      ∀ x : natural (Fin 5) × natural (Fin 5), f (Multiplicative.ofAdd
        (alternatingNaturalRepresentation (Fin 5) a x.1,
         alternatingNaturalRepresentation (Fin 5) a x.2)) = f (Multiplicative.ofAdd x) := by
  let f₁ := f.comp ((LinearMap.inl (ZMod 2) (natural (Fin 5)) (natural (Fin 5))).toAddMonoidHom.toMultiplicative)
  let f₂ := f.comp ((LinearMap.inr (ZMod 2) (natural (Fin 5)) (natural (Fin 5))).toAddMonoidHom.toMultiplicative)
  have hi₁ : ∀ a ∈ normalizer (P : Set (alternatingGroup (Fin 5))),
      ∀ x ∈ f₁.ker, Multiplicative.ofAdd (alternatingNaturalRepresentation (Fin 5) a x.toAdd) ∈ f₁.ker := by
    intro a ha x hx
    have hh := hi a ha (Multiplicative.ofAdd (x.toAdd,0)) hx
    change f (Multiplicative.ofAdd (_, _)) = 1 at hh
    change f (Multiplicative.ofAdd (alternatingNaturalRepresentation (Fin 5) a x.toAdd, 0)) = 1
    simpa only [toAdd_ofAdd, Prod.fst, Prod.snd, map_zero] using hh
  have hi₂ : ∀ a ∈ normalizer (P : Set (alternatingGroup (Fin 5))),
      ∀ x ∈ f₂.ker, Multiplicative.ofAdd (alternatingNaturalRepresentation (Fin 5) a x.toAdd) ∈ f₂.ker := by
    intro a ha x hx
    have hh := hi a ha (Multiplicative.ofAdd (0,x.toAdd)) hx
    change f (Multiplicative.ofAdd (_, _)) = 1 at hh
    change f (Multiplicative.ofAdd (0, alternatingNaturalRepresentation (Fin 5) a x.toAdd)) = 1
    simpa only [toAdd_ofAdd, Prod.fst, Prod.snd, map_zero] using hh
  intro a ha x
  have h₁ := natural_small_image P f₁ hD hi₁ a ha x.1
  have h₂ := natural_small_image P f₂ hD hi₂ a ha x.2
  have he (v w : natural (Fin 5)) :
      f (Multiplicative.ofAdd (v,w)) =
        f₁ (Multiplicative.ofAdd v) * f₂ (Multiplicative.ofAdd w) := by
    change f (Multiplicative.ofAdd (v,w)) = f (Multiplicative.ofAdd (v,0)) * f (Multiplicative.ofAdd (0,w))
    rw [←map_mul,←ofAdd_add]
    simp only [Prod.mk_add_mk,add_zero,zero_add]
  rw [he,h₁,h₂,←he]
end BinaryPermutation.FiveBorelSmallQuotient
