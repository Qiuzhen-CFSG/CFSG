module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.SymplecticEquality.Natural
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.ZeroIntersection
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry

/-!
# Lifting natural-module transitivity to the original elementary core

The natural Sp₄ action is transitive on nonzero vectors. Thus every
noncentral element of P is congruent modulo Z to a conjugate of a fixed
noncentral element of A. Both that conjugate and its central correction
are involutions. Hence all elements of P have square one, so P is
elementary abelian. The action and the linear equivalence use the literal
original quotient maps, not an abstract orbit hypothesis.

Source: Aschbacher–Smith E.2.14(5), printed p.227.
-/

public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement Representation
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition
open Representation.BinaryOffender
open scoped Matrix MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

theorem P_elementary_of_symplectic_four_natural
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (hF : 3 < Nat.card F)
    (η : (X ⧸ J M) ≃* commutator (Sp F)) :
    letI := h.Z_normal
    letI := h.core_geometry.1
    let q := QuotientGroup.mk' (Z V g)
    letI := h.quotient_direct_sum.1
    letI := ZMod.algebra F 2
    ∀ (e : Additive ((P V M g).map q) ≃ₗ[ZMod 2] ((Fin 2 ⊕ Fin 2) → F)),
      (∀ x u, e (normalRepresentation ((P V M g).map q) (q x) u) =
        binaryNatural F (η (QuotientGroup.mk' (J M) x)) (e u)) →
      IsElementaryAbelian 2 (P V M g) := by
  let := h.Z_normal
  let := h.core_geometry.1
  let := h.elementary
  let := h.A_elementary
  let q := QuotientGroup.mk' (Z V g)
  let U := (P V M g).map q
  let := h.quotient_direct_sum.1
  let := ZMod.algebra F 2
  let : Group.IsPerfect (Sp F) := (CentralCovers.Even.isQuasisimple hF).toIsPerfect
  dsimp only
  intro e he
  obtain ⟨a,ha,han⟩ : ∃ a ∈ A V M g, a ∉ Z V g := by
    by_contra! hh
    have ht := h.actor_rank_pos hproper hfit
    have hi : (Z V g).relIndex (A V M g) = 1 := relIndex_eq_one.mpr hh
    rw [hi,Nat.log_one_right] at ht
    omega
  have haU : q a ∈ U := mem_map_of_mem q (show a ∈ P V M g from
    (show A V M g ≤ P V M g from le_sup_right) ha)
  let av : Additive U := Additive.ofMul ⟨q a,haU⟩
  have ha0 : e av ≠ 0 := by
    intro hz
    have he0 : av = 0 := e.injective (hz.trans e.map_zero.symm)
    have he1 : q a = 1 := congrArg (fun z : Additive U => (z.toMul : X ⧸ Z V g)) he0
    exact han ((QuotientGroup.eq_one_iff _).mp he1)
  have hp2 (p : P V M g) : p^2 = 1 := by
    apply Subtype.ext
    change (p : X)^2 = 1
    by_cases hpZ : (p : X) ∈ Z V g
    · exact elemPow_eq_one_of_isElementaryAbelian (A := V) p hpZ.1
    · have hpU : q p ∈ U := mem_map_of_mem q p.property
      let pv : Additive U := Additive.ofMul ⟨q p,hpU⟩
      have hp0 : e pv ≠ 0 := by
        intro hz
        have he0 : pv = 0 := e.injective (hz.trans e.map_zero.symm)
        have he1 : q p = 1 := congrArg (fun z : Additive U => (z.toMul : X ⧸ Z V g)) he0
        exact hpZ ((QuotientGroup.eq_one_iff _).mp he1)
      obtain ⟨s,hs⟩ := TwoLocalCover.nonzero_vector_transitive ha0 hp0
      let s' : commutator (Sp F) := ⟨s, by rw [Group.IsPerfect.commutator_eq_top]; trivial⟩
      have hs' : binaryNatural F s' (e av) = e pv := hs
      obtain ⟨y,hy⟩ := η.surjective s'
      obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (J M) y
      have hη : η (QuotientGroup.mk' (J M) x) = s' := by rw [hx,hy]
      have heq := he x av
      rw [hη,hs'] at heq
      have hq : q (x*a*x⁻¹) = q p := by
        have hd := congrArg (fun z : Additive U => (z.toMul : X ⧸ Z V g))
          (e.injective heq)
        change q x * q a * (q x)⁻¹ = q p at hd
        simpa only [map_mul,map_inv] using hd
      let c := x*a*x⁻¹
      let z := c⁻¹ * (p : X)
      have hz : z ∈ Z V g := by
        apply (QuotientGroup.eq_one_iff _).mp
        change q z = 1
        rw [map_mul,map_inv,hq,inv_mul_cancel]
      have hc2 : c^2 = 1 := by
        change (MulAut.conj x a)^2 = 1
        rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (A := A V M g) a ha,map_one]
      have hz2 : z^2 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := V) z hz.1
      have hcz : Commute c z := (mem_center_iff.mp
        ((h.core_geometry.2.2.trans inf_le_right) hz) c)
      have hpc : (p : X) = c*z := by dsimp [z]; group
      rw [hpc,hcz.mul_pow,hc2,hz2,one_mul]
  have hinv (p : P V M g) : p⁻¹ = p :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hp2 p)
  exact { toIsMulCommutative := ⟨⟨fun a b => by
            calc a*b = (a*b)⁻¹ := (hinv _).symm
                 _ = b⁻¹*a⁻¹ := mul_inv_rev _ _
                 _ = b*a := by rw [hinv,hinv]⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp2 }
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
