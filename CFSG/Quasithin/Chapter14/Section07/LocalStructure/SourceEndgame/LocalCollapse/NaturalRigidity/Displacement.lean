module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity.Displacement.PointImage
public import Theory.Representation.SLThreeCentralExtension.Involutions

/-!
# Displacement by the actual parabolic two-core

When C_Q(L) vanishes and V < QC, the already constructed QC module has
dimension four and no nonzero fixed vectors. The involution theorem
therefore identifies each involution's displacement with its fixed plane.
Two translations in the point radical fix distinct planes of the natural
three-space, and these planes span it. The actual point-radical image
proved in PointImage transports this calculation along the unchanged qL
and the original natural coordinates.

The resulting linear displacement gives the literal [QC,O₂(L₁)] = V.
Applying the existing escape argument excludes V < QC. The final equality
QC = V retains hKC and hQL, whose discharge belongs to the natural-rigidity
assembly owner; no additional universal B.4.8 premise is needed here.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemma 14.7.74, printed p.1077 (PDF p.1094), paragraph beginning “Let B”;
the involution geometry in B.4.8(3), printed p.91.
-/

public section

open Subgroup Representation Representation.BinaryOffender Matrix.PSL3Two
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity.Displacement

private theorem translations :
    Bruhat.upper 1 ∈ MarkedAutomorphisms.pointV ∧
    Bruhat.upper 2 ∈ MarkedAutomorphisms.pointV ∧
    (Bruhat.upper 1)^2 = 1 ∧ (Bruhat.upper 2)^2 = 1 ∧
    Bruhat.upper 1 ≠ 1 ∧ Bruhat.upper 2 ≠ 1 := by decide +kernel

private theorem split_fixed (v : BinaryLinearThree.Vector) :
    ∃ x y : BinaryLinearThree.Vector, x + y = v ∧
      BinaryLinearThree.W (Bruhat.upper 1) x = x ∧
      BinaryLinearThree.W (Bruhat.upper 2) y = y := by
  refine ⟨![v 0,0,v 2], ![0,v 1,0], ?_, ?_, ?_⟩
  · ext i; fin_cases i <;> simp
  · change (Bruhat.upper 1).val.mulVec _ = _
    ext i; fin_cases i <;> simp [Bruhat.upper, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · change (Bruhat.upper 2).val.mulVec _ = _
    ext i; fin_cases i <;> simp [Bruhat.upper, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem split_fixed_conjugate (g : SL) (v : BinaryLinearThree.Vector) :
    ∃ x y : BinaryLinearThree.Vector, x + y = v ∧
      BinaryLinearThree.W (g * Bruhat.upper 1 * g⁻¹) x = x ∧
      BinaryLinearThree.W (g * Bruhat.upper 2 * g⁻¹) y = y := by
  obtain ⟨x,y,hxy,hx,hy⟩ := split_fixed (BinaryLinearThree.W g⁻¹ v)
  refine ⟨BinaryLinearThree.W g x, BinaryLinearThree.W g y, ?_, ?_, ?_⟩
  · rw [← map_add, hxy, self_inv_apply]
  · simp only [map_mul, Module.End.mul_apply, inv_self_apply, hx]
  · simp only [map_mul, Module.End.mul_apply, inv_self_apply, hy]

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  [FiniteDimensional (ZMod 2) M]

private theorem point_displacement
    (ρ : Representation (ZMod 2) BinaryLinearThree.Group M)
    (N : Subrepresentation ρ) (e : N.toRepresentation.Equiv BinaryLinearThree.W)
    (hq : OneCohomology.HasTrivialQuotient N)
    (hdim : Module.finrank (ZMod 2) M = 4) (hfix : ρ.invariants = ⊥)
    (g : SL) :
    subspaceCommutator ρ ⊤ (MarkedAutomorphisms.pointV.map (MulAut.conj g).toMonoidHom) =
      N.toSubmodule := by
  let A := MarkedAutomorphisms.pointV.map (MulAut.conj g).toMonoidHom
  let D := subspaceCommutator ρ ⊤ A
  have ht (t : SL) (htA : t ∈ A) (ho : orderOf t = 2) {v : M}
      (hv : ρ t v = v) : v ∈ D := by
    have hc := BinaryLinearThree.NaturalExtension.involution_codim_of_fixed_zero ρ hdim hfix t ho
    have he := (BinaryLinearThree.NaturalExtension.involution_range_eq_fixed ρ hdim t ho hc).1
    have hr : v ∈ LinearMap.range (ρ t - LinearMap.id) := by
      rw [he, mem_fixedSpace_zpowers_iff]
      exact hv
    obtain ⟨w,hw⟩ := hr
    exact hw ▸ Submodule.subset_span ⟨t,htA,w,Submodule.mem_top,rfl⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨t,_,v,_,rfl⟩
    exact hq t v
  · intro v hv
    let n : N.toSubmodule := ⟨v,hv⟩
    obtain ⟨x,y,hxy,hx,hy⟩ := split_fixed_conjugate g (e n)
    have hn : e.symm x + e.symm y = n := by
      apply e.toLinearEquiv.injective
      simpa using hxy
    have hx' : ρ (g * Bruhat.upper 1 * g⁻¹) (e.symm x).val = (e.symm x).val := by
      have hh : N.toRepresentation (g * Bruhat.upper 1 * g⁻¹) (e.symm x) = e.symm x := by
        apply e.toLinearEquiv.injective
        change e (N.toRepresentation (g * Bruhat.upper 1 * g⁻¹) (e.symm x)) = e (e.symm x)
        rw [show e (N.toRepresentation (g * Bruhat.upper 1 * g⁻¹) (e.symm x)) =
          BinaryLinearThree.W (g * Bruhat.upper 1 * g⁻¹) (e (e.symm x)) from
          LinearMap.congr_fun (e.isIntertwining' _) _]
        simpa using hx
      exact congrArg Subtype.val hh
    have hy' : ρ (g * Bruhat.upper 2 * g⁻¹) (e.symm y).val = (e.symm y).val := by
      have hh : N.toRepresentation (g * Bruhat.upper 2 * g⁻¹) (e.symm y) = e.symm y := by
        apply e.toLinearEquiv.injective
        change e (N.toRepresentation (g * Bruhat.upper 2 * g⁻¹) (e.symm y)) = e (e.symm y)
        rw [show e (N.toRepresentation (g * Bruhat.upper 2 * g⁻¹) (e.symm y)) =
          BinaryLinearThree.W (g * Bruhat.upper 2 * g⁻¹) (e (e.symm y)) from
          LinearMap.congr_fun (e.isIntertwining' _) _]
        simpa using hy
      exact congrArg Subtype.val hh
    have h1 : g * Bruhat.upper 1 * g⁻¹ ∈ A := ⟨_,translations.1,rfl⟩
    have h2 : g * Bruhat.upper 2 * g⁻¹ ∈ A := ⟨_,translations.2.1,rfl⟩
    have ho1 : orderOf (g * Bruhat.upper 1 * g⁻¹) = 2 := by
      change orderOf ((MulAut.conj g) (Bruhat.upper 1)) = 2
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime translations.2.2.1 translations.2.2.2.2.1
    have ho2 : orderOf (g * Bruhat.upper 2 * g⁻¹) = 2 := by
      change orderOf ((MulAut.conj g) (Bruhat.upper 2)) = 2
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime translations.2.2.2.1 translations.2.2.2.2.2
    have hd := D.add_mem (ht _ h1 ho1 hx') (ht _ h2 ho2 hy')
    have hv' : (e.symm x).val + (e.symm y).val = v := congrArg Subtype.val hn
    rw [← hv']
    exact hd
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity.Displacement

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity.Displacement
open Chapter12.Section08 CriticalFusion.Source
open scoped commutatorElement IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (a : Prior d)
  (hKC : ⁅QC T L V, K F⁆ ≤ F.U)

/-- The two-core of the original point parabolic moves the entire natural layer. -/
theorem linear_displacement [IsElementaryAbelian 2 (QC T L V)]
    (hQL : QL T L = ⊥) (hlt : V < QC T L V) :
    BinaryOffender.subspaceCommutator (action d a hKC) ⊤ (parabolicMap d).range =
      (naturalPart d a hKC).toSubmodule := by
  obtain ⟨g,hg⟩ := exists_parabolicMap_range d
  rw [hg]
  exact point_displacement (action d a hKC) (naturalPart d a hKC)
    (naturalEquiv d a hKC) (trivialQuotient d a hKC)
    (QC_finrank_eq_four d a hKC hQL hlt) (fixed_eq_bot d a hKC hQL) g

include a hKC in
/-- The literal equality cited in 14.7.74, with the elementary instance discharged. -/
theorem QC_parabolic_displacement (hQL : QL T L = ⊥) (hlt : V < QC T L V) :
    ⁅QC T L V, (F.Li L 1).pCoreIn 2⁆ = V := by
  let := QC_elementary d a hQL
  exact commutator_eq_of_linear_displacement d a hKC (linear_displacement d a hKC hQL hlt)

include a hKC in
/-- The source escape argument excludes the proper natural extension. -/
theorem false_of_proper_QC (hQL : QL T L = ⊥) (hlt : V < QC T L V) : False := by
  let := QC_elementary d a hQL
  exact false_of_linear_displacement d a hKC (linear_displacement d a hKC hQL hlt)

include a hKC in
/-- Natural rigidity after the separately supplied centralizer vanishing. -/
theorem QC_eq_V_of_QL_eq_bot (hQL : QL T L = ⊥) : QC T L V = V := by
  by_contra hne
  exact false_of_proper_QC d a hKC hQL (lt_of_le_of_ne (V_le_QC d a) (Ne.symm hne))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity.Displacement
