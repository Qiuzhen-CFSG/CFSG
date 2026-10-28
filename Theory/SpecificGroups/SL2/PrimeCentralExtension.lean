module

public import Theory.GroupTheory.PerfectCentralPGroupSplit
public import Theory.SpecificGroups.SL2.SylowConsequences

/-!
# Central defining-prime extensions of SL2 over a prime field

For p > 3, SL2(p) is perfect and its Sylow p-subgroups are cyclic.
The general central p-kernel splitting theorem therefore constructs a
section of every finite central extension with p-group kernel. No full
Schur-multiplier calculation is needed.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
A.1.33(2), printed p.29.
-/

namespace Matrix.SpecialLinearGroup
open Subgroup

/-- A central extension by a group of defining-prime power order has an
actual section of its given map onto SL2(p). -/
public theorem exists_section_of_central_prime_kernel
    {E : Type*} [Group E] [Finite E] {p : ℕ} [Fact p.Prime]
    (hp : 3 < p) (f : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (hf : Function.Surjective f) (hc : f.ker ≤ center E) (hk : IsPGroup p f.ker) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* E,
      f.comp s = MonoidHom.id _ := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    exact fun h => Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p)
      ((ZMod.natCast_eq_zero_iff 2 p).mp h)
  have hsq : (2 : ZMod p) ^ 2 ≠ 1 := by
    intro h
    have h3 : (3 : ZMod p) = 0 := by linear_combination h
    have : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3
    exact Nat.not_dvd_of_pos_of_lt (by decide) hp this
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
    ⟨Matrix.SL2.commutator_eq_top h2 hsq⟩
  apply PerfectCentralCovering.exists_section_of_central_pGroup_kernel f hf hc hk
  intro S
  exact (Matrix.SpecialLinearGroup.sylowEquivAdditive (ZMod p) p S).isCyclic.mp inferInstance
variable {L : Type*} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]

/-- In a subgroup covering the SL2 quotient with central p-kernel, the
splitting supplies an actual order-p element outside the normal p-subgroup. -/
public theorem exists_prime_order_outside_normal_subgroup (P : Subgroup L) [P.Normal]
    (hP : IsPGroup p P) (hp : 3 < p)
    (eQ : L ⧸ P ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (C : Subgroup L)
    (hC : Function.Surjective ((QuotientGroup.mk' P).comp C.subtype))
    (hcentral : ∀ x : C, (x : L) ∈ P → x ∈ center C) :
    ∃ x ∈ C, orderOf x = p ∧ x ∉ P := by
  let f := eQ.toMonoidHom.comp ((QuotientGroup.mk' P).comp C.subtype)
  have hf : Function.Surjective f := eQ.surjective.comp hC
  have hker (x : C) : x ∈ f.ker ↔ (x : L) ∈ P := by
    change eQ (QuotientGroup.mk' P (x : L)) = 1 ↔ (x : L) ∈ P
    rw [map_eq_one_iff eQ eQ.injective]
    exact QuotientGroup.eq_one_iff (x : L)
  have hfc : f.ker ≤ center C := fun x hx => hcentral x ((hker x).mp hx)
  let k : f.ker →* P := (C.subtype.comp f.ker.subtype).codRestrict P
    (fun x => (hker x).mp x.property)
  have hki : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : P => (z : L)) h
  have hfp : IsPGroup p f.ker := hP.of_injective k hki
  obtain ⟨s, hs⟩ := Matrix.SpecialLinearGroup.exists_section_of_central_prime_kernel
    hp f hf hfc hfp
  have hsec (b) : f (s b) = b := DFunLike.congr_fun hs b
  have hsi : Function.Injective s := by
    intro a b hab
    simpa only [hsec] using congrArg f hab
  let U := Matrix.SpecialLinearGroup.upperUnipotent (ZMod p)
  have hU : p ∣ Nat.card U := by
    rw [Matrix.SpecialLinearGroup.card_upperUnipotent, Nat.card_zmod]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hU
  let x := s (u : Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
  have huB : orderOf (u : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = p :=
    (orderOf_injective U.subtype U.subtype_injective u).trans hu
  have hx : orderOf (x : L) = p :=
    (orderOf_injective C.subtype C.subtype_injective x).trans
      ((orderOf_injective s hsi _).trans huB)
  refine ⟨x, x.property, hx, ?_⟩
  intro hxP
  have hfx : f x = 1 := (hker x).mpr hxP
  have hu1 : (u : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = 1 :=
    (hsec u).symm.trans hfx
  have : p = 1 := by simpa only [hu1, orderOf_one] using huB.symm
  exact (Fact.out : p.Prime).ne_one this

end Matrix.SpecialLinearGroup
