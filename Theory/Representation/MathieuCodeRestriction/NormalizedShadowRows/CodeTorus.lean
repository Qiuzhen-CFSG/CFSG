module
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.Flags
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators
public import Theory.Representation.MathieuCodeRestriction.Duality
public import Theory.Mathieu.M24.ChapterHStabilizers.ElementaryFusion
public import Theory.Representation.BinaryOffender.FixedQuotientKernel
public import Theory.LinearAlgebra.QuadraticRankOneDisplacement
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Cubics normalizing rank-six code actors

Every elementary rank-six subgroup of the native M24 fuses to the intrinsic
sextet or trio core. Their fixed code spaces have dimensions four and two;
the trio calculation uses the actual cocode commutator space and code duality.
A cubic cannot have a fixed three-space inside either fixed space: the trio
space is too small, and on the sextet space the cubic would have displacement
rank one, hence square one in characteristic two.

This is the rank-six case of Aschbacher--Smith H.16.7, printed p.405,
refs/quasithin.pdf, for the whole code and full native actor. The rank-four
case is supplied by the cubic centralizer calculation in the companion module.
-/

public noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Representation Representation.BinaryOffender Subgroup
namespace MathieuCode.NormalizedShadowRows.CodeTorus

private theorem square_eq_one_of_rank_one {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] (e : U ≃ₗ[ZMod 2] U)
    (h : Module.finrank (ZMod 2) (LinearMap.range (e.toLinearMap - LinearMap.id)) = 1) :
    e ^ 2 = 1 := by
  obtain ⟨f,v,he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr h.le
  have he' (x : U) : e x = x + f x • v :=
    congrArg (fun l : U →ₗ[ZMod 2] U => l x) he
  have hfv : f v = 0 := by
    rcases (by decide : ∀ x : ZMod 2, x=0 ∨ x=1) (f v) with hz | ho
    · exact hz
    have hev : e v = 0 := by rw [he',ho,one_smul,ZModModule.add_self]
    have hv := e.map_eq_zero_iff.mp hev
    rw [hv,map_zero] at ho
    exact (zero_ne_one ho).elim
  apply LinearEquiv.ext
  intro x
  change e (e x) = x
  rw [he',he',map_add,map_smul,hfv,smul_zero,add_zero]
  simp only [add_assoc,ZModModule.add_self,add_zero]

private theorem cubic_fixed_not_hyperplane
    {X U : Type*} [Group X] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) X U) (x : X) (hx : x^3=1)
    (W : Submodule (ZMod 2) U) (hW : x ∈ subspaceStabilizer ρ W)
    (hle : fixedSpace ρ (zpowers x) ≤ W)
    (hd : Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) (fixedSpace ρ (zpowers x)) + 1) : False := by
  let σ := stabilizerRepresentation ρ W
  let x' : subspaceStabilizer ρ W := ⟨x,hW⟩
  let e : W ≃ₗ[ZMod 2] W := LinearMap.GeneralLinearGroup.toLinearEquiv (σ.asGroupHom x')
  have hk : (e.toLinearMap - LinearMap.id).ker = (fixedSpace ρ (zpowers x)).comap W.subtype := by
    ext v
    change e v - v = 0 ↔ _
    rw [sub_eq_zero]
    change e v = v ↔ (v : U) ∈ fixedSpace ρ (zpowers x)
    rw [mem_fixedSpace_zpowers_iff]
    exact Subtype.ext_iff
  have hf := (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have hr := (e.toLinearMap - LinearMap.id).finrank_range_add_finrank_ker
  rw [hk] at hr
  have he2 := square_eq_one_of_rank_one e (by omega)
  have he3 : e^3=1 := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    change ρ x (ρ x (ρ x v.val)) = v.val
    have h := LinearMap.congr_fun (congrArg ρ hx) v.val
    simpa only [pow_succ,pow_zero,map_mul,map_one,Module.End.mul_apply,Module.End.one_apply] using h
  have he1 : e=1 := by
    calc e = e^3 := by rw [pow_succ,he2,one_mul]
         _ = 1 := he3
  have hz : e.toLinearMap - LinearMap.id = 0 := by
    apply LinearMap.ext
    intro v
    change e v - v = 0
    rw [he1]
    exact sub_self _
  rw [hz,LinearMap.range_zero,finrank_bot] at hr
  omega

/-- The fixed space of an elementary rank-six actor on the whole native code
has dimension two or four. -/
theorem rank_six_fixed_dimension (A : Subgroup M24) [IsElementaryAbelian 2 A]
    (hr : rank A = 6) :
    Module.finrank (ZMod 2) (fixedSpace codeRepresentation A) = 2 ∨
    Module.finrank (ZMod 2) (fixedSpace codeRepresentation A) = 4 := by
  have hc : Nat.card A = 64 := by
    have hn : A ≠ ⊥ := by intro he; rw [he,Representation.BinaryOffender.rank_bot] at hr; omega
    rw [(show IsElementaryTwo A from ⟨hn,inferInstance⟩).card_eq_two_pow_rank,hr]
    decide
  obtain ⟨g,hg | hg⟩ := M24ChapterHStabilizers.ElementaryFusion.large_elementary_fused_into_core A (by omega)
  · have he : A.map (MulAut.conj g).toMonoidHom = SextetCore.core :=
      Subgroup.eq_of_le_of_card_ge hg (by rw [card_map_of_injective (MulAut.conj g).injective,hc,SextetCore.core_ambient_card])
    right
    rw [(fixedSpaceConjEquiv codeRepresentation A g).finrank_eq,he]
    change Module.finrank (ZMod 2) (fixedSpace codeRepresentation (CodeFlags.sextetCore standardSextet)) = 4
    rw [CodeFlags.sextetCore_fixedSpace,CodeFlags.sextetCodeSpace_finrank]
  · have he : A.map (MulAut.conj g).toMonoidHom = M24ChapterHStabilizers.ElementaryFusion.trioCore :=
      Subgroup.eq_of_le_of_card_ge hg (by
        rw [card_map_of_injective (MulAut.conj g).injective,hc]
        change Nat.card M24ChapterHStabilizers.TrioAction.core ≤ 64
        rw [M24ChapterHStabilizers.TrioAction.core_ambient_card])
    left
    rw [(fixedSpaceConjEquiv codeRepresentation A g).finrank_eq,he]
    have hd := fixedCodim_map_equivariant codeRepresentation cocodeRepresentation.dual
      (MonoidHom.id M24) codeDuality.toLinearEquiv
      (fun g x => LinearMap.congr_fun (codeDuality.isIntertwining' g) x)
      M24ChapterHStabilizers.ElementaryFusion.trioCore
    rw [Subgroup.map_id,fixedCodim_dual_eq_moved_finrank] at hd
    have ht : M24ChapterHStabilizers.ElementaryFusion.trioCore =
        (pCore 2 (trioStabilizer standardTrio)).map (trioStabilizer standardTrio).subtype := rfl
    rw [ht,← TrioCalculation.standard_pairSpace_eq_twoCore_commutator,TrioCalculation.finrank_pairSpace] at hd
    rw [← ht] at hd
    have hs := fixedCodim_add_finrank codeRepresentation M24ChapterHStabilizers.ElementaryFusion.trioCore
    rw [hd,finrank_code] at hs
    omega

/-- A cubic normalizing a rank-six elementary actor cannot have a fixed
three-space contained in that actor's fixed space on the code. -/
theorem no_cubic_fixed_three_of_rank_six (A : Subgroup M24) [IsElementaryAbelian 2 A]
    (hr : rank A = 6) (x : M24) (hx : orderOf x = 3)
    (hn : x ∈ normalizer (A : Set M24))
    (hle : fixedSpace codeRepresentation (zpowers x) ≤ fixedSpace codeRepresentation A)
    (hd : Module.finrank (ZMod 2) (fixedSpace codeRepresentation (zpowers x)) = 3) : False := by
  rcases rank_six_fixed_dimension A hr with ha | ha
  · have := Submodule.finrank_mono hle
    omega
  · exact cubic_fixed_not_hyperplane codeRepresentation x
      (by rw [← hx]; exact pow_orderOf_eq_one x) _
      (normalizer_le_stabilizer_fixedSpace codeRepresentation A hn) hle (by omega)

end MathieuCode.NormalizedShadowRows.CodeTorus
