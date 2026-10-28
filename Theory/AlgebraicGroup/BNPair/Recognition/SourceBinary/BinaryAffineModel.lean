module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.SolvableNineAction
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Affine coordinates for the exceptional binary unitary panel

A faithful solvable doubly transitive action of degree nine and order 144
is the natural affine action of a Sylow two-subgroup of GL₂(3) on F₃².
The regular elementary normal subgroup supplies translation coordinates;
its point stabilizer acts faithfully on those coordinates. Its order is
sixteen, so its matrix image is Sylow in GL₂(3). The internal semidirect
product gives an actual group isomorphism and an equivariant panel bijection,
with the base point and its full stabilizer preserved.

This is the concrete local model required by the remaining binary unitary
branch of Fong--Seitz I (2A)--(2B), pp.7--9, and (5B)--(5C), pp.25--26.
It does not exclude that branch or identify a rank-two completion.
BinaryAffineApplications applies it to the original marked source cover.
-/

public noncomputable section
open Subgroup MulAction Matrix
open Matrix.GeneralLinearGroup.PrimeThreeFiveResidual
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.BinaryPanel

abbrev Nine := Multiplicative (Fin 2 → ZMod 3)
abbrev PlaneGL := GL (Fin 2) (ZMod 3)
@[expose] def sylowPlaneAction (S : Sylow 2 PlaneGL) : S →* MulAut Nine :=
  (planeAction 3).comp (S : Subgroup PlaneGL).subtype
abbrev AffineNine (S : Sylow 2 PlaneGL) := Nine ⋊[sylowPlaneAction S] S

variable {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω]
  [FaithfulSMul G Ω] [Finite Ω]

omit [Finite G] [FaithfulSMul G Ω] [Finite Ω] in
private theorem regular_complement (N : Subgroup G) (o : Ω)
    (hreg : ∀ x y : Ω, ∃! n : N, (n : G) • x = y) :
    N.IsComplement' (stabilizer G o) := by
  change Function.Bijective (fun p : N × stabilizer G o => (p.1 : G) * p.2)
  constructor
  · rintro ⟨a,k⟩ ⟨b,l⟩ he
    have hab : (a : G) • o = (b : G) • o := by
      have hh := congrArg (fun g : G => g • o) he
      change ((a : G) * (k : G)) • o = ((b : G) * (l : G)) • o at hh
      simp only [mul_smul] at hh
      rw [show (k : G) • o = o from k.property,show (l : G) • o = o from l.property] at hh
      exact hh
    obtain ⟨c,hc,hu⟩ := hreg o ((a : G) • o)
    have ha : a = b := (hu a rfl).trans (hu b hab.symm).symm
    have hk : k = l := Subtype.ext (mul_left_cancel (by simpa only [ha] using he))
    exact Prod.ext ha hk
  · intro g
    obtain ⟨a,ha,_⟩ := hreg o (g • o)
    refine ⟨(a,⟨(a : G)⁻¹*g,?_⟩),by simp⟩
    rw [mem_stabilizer_iff,mul_smul,← ha,inv_smul_smul]

/-- A faithful solvable action of order 144 and degree nine has actual affine Sylow coordinates. -/
theorem exists_affine_sylow_comparison
    (ht : IsMultiplyPretransitive G Ω 2) [Group.IsSolvable G]
    (hc : Nat.card Ω = 9) (hg : Nat.card G = 144) (o : Ω) :
    ∃ (S : Sylow 2 PlaneGL) (e : AffineNine S ≃* G) (c : Nine ≃ Ω),
      c 1 = o ∧
      (∀ a v, e a • c v = c (a.left * planeAction 3 (a.right : PlaneGL) v)) ∧
      (SemidirectProduct.inr : S →* AffineNine S).range.map e.toMonoidHom = stabilizer G o := by
  obtain ⟨N,hNn,hNe,hNc,hreg⟩ := regular_nine_of_solvable ht hc o
  let := hNn
  let := hNe
  obtain ⟨b,d,hd⟩ := exists_plane_coordinates (show Nat.card N = 3^2 by simpa using hNc)
  let C := stabilizer G o
  let γ : C →* MulAut N := N.normalizerMonoidHom.comp (inclusion (N.normalizer_eq_top ▸ le_top))
  let f : C →* PlaneGL := d.toMonoidHom.comp γ
  have hγ : Function.Injective γ := stabilizer_action_injective N o hreg
  have hf : Function.Injective f := d.injective.comp hγ
  let : IsPreprimitive G Ω := isPreprimitive_of_is_two_pretransitive ht
  have hC : Nat.card C = 16 := by
    have hh := C.index_mul_card
    rw [index_stabilizer_of_transitive,hc,hg] at hh
    omega
  have hr : Nat.card f.range = 16 := (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hC
  have hp : IsPGroup 2 f.range := IsPGroup.of_card (n := 4) hr
  have hGL : Nat.card PlaneGL = 48 := by rw [Matrix.card_GL_field]; decide
  have hidx : f.range.index = 3 := by
    have hh := f.range.index_mul_card
    rw [hr,hGL] at hh
    omega
  let S : Sylow 2 PlaneGL := hp.toSylow (by rw [hidx]; decide)
  let k : C ≃* S := MonoidHom.ofInjective hf
  have hcompat (z : C) : (γ z).trans b = b.trans (sylowPlaneAction S (k z)) := by
    apply MulEquiv.ext
    intro n
    exact (hd (γ z) n).symm
  let m := SemidirectProduct.mulEquivSubgroup (regular_complement N o hreg)
  let e : AffineNine S ≃* G := (SemidirectProduct.congr b k hcompat).symm.trans m
  have hbij : Function.Bijective (fun n : N => (n : G) • o) := by
    refine ⟨?_,?_⟩
    · intro a z he
      obtain ⟨n,hn,hu⟩ := hreg o ((a : G) • o)
      exact (hu a rfl).trans (hu z he.symm).symm
    · intro x
      obtain ⟨n,hn,_⟩ := hreg o x
      exact ⟨n,hn⟩
  let c : Nine ≃ Ω := b.symm.toEquiv.trans (Equiv.ofBijective _ hbij)
  have hc_apply (v : Nine) : c v = (b.symm v : G) • o := rfl
  have he_apply (a : AffineNine S) : e a = (b.symm a.left : G) * (k.symm a.right : G) := by
    rfl
  refine ⟨S,e,c,?_,?_,?_⟩
  · rw [hc_apply,map_one]; exact one_smul G o
  · intro a v
    rw [he_apply,hc_apply,hc_apply]
    have hconj : b.symm (planeAction 3 (a.right : PlaneGL) v) =
        γ (k.symm a.right) (b.symm v) := by
      apply b.injective
      rw [b.apply_symm_apply,← hd,b.apply_symm_apply]
      change planeAction 3 (a.right : PlaneGL) v = planeAction 3 (k (k.symm a.right) : PlaneGL) v
      rw [k.apply_symm_apply]
    rw [map_mul,hconj]
    change ((b.symm a.left : G) * (k.symm a.right : G)) • ((b.symm v : G) • o) =
      ((b.symm a.left : G) * ((k.symm a.right : G) * (b.symm v : G) * (k.symm a.right : G)⁻¹)) • o
    simp only [mul_smul]
    rw [show (k.symm a.right : G)⁻¹ • o = o from (k.symm a.right)⁻¹.property]
  · apply le_antisymm
    · rintro _ ⟨_,⟨s,rfl⟩,rfl⟩
      change e (SemidirectProduct.inr s) ∈ _
      rw [he_apply]
      simpa only [SemidirectProduct.left_inr,SemidirectProduct.right_inr,map_one,Subgroup.coe_one,one_mul]
        using (k.symm s).property
    · intro g hg
      refine ⟨SemidirectProduct.inr (k ⟨g,hg⟩),⟨k ⟨g,hg⟩,rfl⟩,?_⟩
      change e (SemidirectProduct.inr (k ⟨g,hg⟩)) = g
      rw [he_apply]
      simp only [SemidirectProduct.left_inr,SemidirectProduct.right_inr,map_one,Subgroup.coe_one,one_mul,k.symm_apply_apply]
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.BinaryPanel
