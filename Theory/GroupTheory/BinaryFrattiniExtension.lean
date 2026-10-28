module
public import Theory.Frattini.SquareImage
public import Theory.ElementaryAbelian.Quotient
public import Theory.Frattini.PGroupMap
public import Mathlib.GroupTheory.Sylow

/-!
# Frattini bounds through two-group extensions

An elementary image of a group factors through its Frattini quotient. Apply
this first to an extension's kernel, then to its quotient, to bound the number
of generators of a finite two-group by the sum for its kernel and quotient.
A kernel contained in the Frattini subgroup contributes no generators.

The final lemma transports a square root of a central involution into an
arbitrary Sylow two-subgroup by Sylow conjugacy. These are the structural
inputs to the odd G₂ Sylow calculation in `G2.OddFrattiniSixteen`, used in
Aschbacher--Smith 4.4.10--11, printed p.621.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace BinaryFrattiniExtension
variable {P Q E : Type*} [Group P] [Finite P] [Group Q] [Finite Q]
  [Group E] [Finite E] [IsElementaryAbelian 2 E]

omit [Finite E] in
/-- An elementary abelian two-image is an image of the Frattini quotient. -/
theorem elementary_card_le (f : P →* E)
    (hf : Function.Surjective f) : Nat.card E ≤ Nat.card (P ⧸ frattini P) := by
  let g := QuotientGroup.lift (frattini P) f
    (Theory.GroupTheory.frattini_le_ker_of_square_image f (fun x =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) _))
  apply Nat.card_le_card_of_surjective g
  intro x
  obtain ⟨y,rfl⟩ := hf x
  exact ⟨QuotientGroup.mk' _ y,rfl⟩

omit [Finite E] in
/-- Kernel and quotient Frattini orders bound every elementary two-image of an extension. -/
theorem elementary_extension_card_le
    (f : P →* Q) (hf : Function.Surjective f)
    (g : P →* E) (hg : Function.Surjective g) :
    Nat.card E ≤ Nat.card (f.ker ⧸ frattini f.ker) * Nat.card (Q ⧸ frattini Q) := by
  let N := f.ker.map g
  let : IsElementaryAbelian 2 N := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom N.subtype N.subtype_injective).trans
      (IsElementaryAbelian.exponent_dvd_p 2 E) }
  let r := g.subgroupMap f.ker
  have hN : Nat.card N ≤ Nat.card (f.ker ⧸ frattini f.ker) :=
    elementary_card_le r (g.subgroupMap_surjective _)
  let a : (P ⧸ f.ker) →* (E ⧸ N) := QuotientGroup.lift f.ker
    ((QuotientGroup.mk' N).comp g) (by
      intro x hx
      exact (QuotientGroup.eq_one_iff _).mpr (mem_map_of_mem g hx))
  have ha : Function.Surjective a := by
    intro y
    obtain ⟨e,rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨x,rfl⟩ := hg e
    exact ⟨QuotientGroup.mk' f.ker x,rfl⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  let b := a.comp e.symm.toMonoidHom
  have hQ : Nat.card (E ⧸ N) ≤ Nat.card (Q ⧸ frattini Q) :=
    elementary_card_le b (ha.comp e.symm.surjective)
  rw [card_eq_card_quotient_mul_card_subgroup N,mul_comm]
  exact Nat.mul_le_mul hN hQ

/-- Generator numbers of finite two-groups are subadditive in extensions. -/
theorem card_le (hP : IsPGroup 2 P) (f : P →* Q) (hf : Function.Surjective f) :
    Nat.card (P ⧸ frattini P) ≤
      Nat.card (f.ker ⧸ frattini f.ker) * Nat.card (Q ⧸ frattini Q) := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  exact elementary_extension_card_le f hf (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _)
/-- Killing a subgroup of the Frattini subgroup preserves the required upper bound. -/
theorem card_le_of_frattini_kernel (hP : IsPGroup 2 P)
    (f : P →* Q) (hf : Function.Surjective f) (hk : f.ker ≤ frattini P) :
    Nat.card (P ⧸ frattini P) ≤ Nat.card (Q ⧸ frattini Q) := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let a : (P ⧸ f.ker) →* (P ⧸ frattini P) := QuotientGroup.lift _
    (QuotientGroup.mk' _) (by rw [QuotientGroup.ker_mk']; exact hk)
  have ha : Function.Surjective a := by
    intro x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (frattini P) x
    exact ⟨QuotientGroup.mk' _ y,rfl⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  exact elementary_card_le (a.comp e.symm.toMonoidHom)
    (ha.comp e.symm.surjective)

/-- A central involution which is a square has a square root in every Sylow two-subgroup. -/
theorem central_square_in_sylow {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) {z x : G} (hz : z ∈ center G) (hx : x ^ 2 = z)
    (hz2 : z ^ 2 = 1) : ∃ y : P, (y : G) ^ 2 = z := by
  have hx4 : x ^ (2^2) = 1 := by rw [show 2^2=2*2 by decide,pow_mul,hx,hz2]
  have hd : Nat.card (zpowers x) ∣ 2^2 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hx4
  obtain ⟨n,_,hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hC : IsPGroup 2 (zpowers x) := IsPGroup.of_card hn
  obtain ⟨S,hS⟩ := hC.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G S P
  let e : S ≃* P := (S.equivSMul g).trans
    (MulEquiv.subgroupCongr (congrArg Sylow.toSubgroup hg))
  refine ⟨e ⟨x,hS (mem_zpowers x)⟩,?_⟩
  change (g*x*g⁻¹)^2=z
  rw [←MulAut.conj_apply,←map_pow,hx]
  change g*z*g⁻¹=z
  rw [(mem_center_iff.mp hz g),mul_inv_cancel_right]


end BinaryFrattiniExtension
