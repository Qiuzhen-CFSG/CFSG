module

public import Theory.Representation.BinaryCoprimeDegree
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Cubic displacement in an extraspecial group of order 27

A nontrivial central cubic moves at least six binary dimensions: its displacement
space is invariant and the cubic still acts nontrivially there. A commutator
moves at most twice as much as its first entry. Thus a noncentral element of an
extraspecial group of order 27 has fixed codimension at least three in any
faithful binary representation. This rules out a single noncentral cyclic-three
chief factor in the unitary branch of Aschbacher–Smith 13.3.12, printed p.890.
-/

public section

open Module Subgroup
open scoped commutatorElement
namespace Representation.BinaryCoprimeDegree
variable {P V : Type*} [Group P] [Finite P] [IsExtraspecial 3 P]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem central_cubic_displacement_ge_six
    (ρ : Representation (ZMod 2) P V) (hρ : Function.Injective ρ)
    (hcard : Nat.card P=3^3) {z : P} (hz : z∈center P) (hz1 : z≠1) :
    6≤finrank (ZMod 2) (LinearMap.range (ρ z-1)) := by
  let D := ρ z-1
  let W : Subrepresentation ρ := ⟨D.range,by
    intro g v hv
    obtain ⟨w,rfl⟩ := hv
    refine ⟨ρ g w,?_⟩
    have hc : ρ z (ρ g w)=ρ g (ρ z w) := by
      simp only [←Module.End.mul_apply,←map_mul,(mem_center_iff.mp hz g).symm]
    simp only [D,LinearMap.sub_apply,Module.End.one_apply,map_sub,hc]⟩
  have hz3 : z^3=1 := by
    have hh := pow_card_eq_one' (x:=(⟨z,hz⟩:center P))
    rw [IsExtraspecial.center_order_p 3 P] at hh
    exact congrArg Subtype.val hh
  have hW : ¬center P≤W.toRepresentation.ker := by
    intro hc
    have he : W.toRepresentation z=1 := hc hz
    have hadd (v : V) : v+v=0 := by
      have hh := two_smul (ZMod 2) v
      rw [show (2:ZMod 2)=0 by decide,zero_smul] at hh
      exact hh.symm
    have hneg (v : V) : -v=v := (neg_eq_iff_add_eq_zero).mpr (hadd v)
    have hsquare (v : V) : ρ z (ρ z v)=v := by
      have hh := congrArg Subtype.val (LinearMap.congr_fun he (⟨D v,⟨v,rfl⟩⟩:W))
      change ρ z (ρ z v-v)=ρ z v-v at hh
      have heq : ρ z (ρ z v)+ρ z v=v+ρ z v := by
        simpa only [map_sub,sub_eq_add_neg,hneg,map_add,add_comm] using hh
      exact add_right_cancel heq
    have hfix (v : V) : ρ z v=v := by
      have hh : ρ z (ρ z (ρ z v))=v := by
        have heq : ρ z^3=1 := by rw [←map_pow,hz3,map_one]
        have hv := LinearMap.congr_fun heq v
        simpa only [pow_succ,Module.End.mul_apply,pow_zero,Module.End.one_apply] using hv
      rw [hsquare] at hh
      exact hh
    have hid : ρ z=ρ 1 := by rw [map_one];exact LinearMap.ext hfix
    exact hz1 (hρ hid)
  have hb := extraspecial_finrank_le_of_center_not_le_ker (p:=3) (by decide)
    W.toRepresentation hcard hW
  rw [BinaryPrimeDegree.orderOf_two_mod_three] at hb
  exact hb

/-- A noncentral cubic in an extraspecial group of order27 cannot move only
one nontrivial binary cyclic-three factor. -/
theorem noncentral_fixedCodim_ge_three
    (ρ : Representation (ZMod 2) P V) (hρ : Function.Injective ρ)
    (hcard : Nat.card P=3^3) {x : P} (hx : x∉center P) :
    3≤BinaryOffender.fixedCodim ρ (zpowers x) := by
  obtain ⟨y,hy⟩ := not_forall.mp (fun hh => hx (mem_center_iff.mpr hh))
  have hz : ⁅x,y⁆∈center P := commutator_le_center_of_isExtraspecial_local (q:=3)
    (Subgroup.commutator_mem_commutator (mem_top x) (mem_top y))
  have hz1 : ⁅x,y⁆≠1 := by
    intro h
    exact hy (commutatorElement_eq_one_iff_mul_comm.mp h).symm
  have hb := central_cubic_displacement_ge_six ρ hρ hcard hz hz1
  have hu := BinaryOffender.fixedCodim_commutator_le_twice ρ x y
  rw [BinaryOffender.fixedCodim_zpowers_eq_displacement_rank] at hu
  change finrank (ZMod 2) (LinearMap.range (ρ ⁅x,y⁆-1))≤_ at hu
  omega
end Representation.BinaryCoprimeDegree
