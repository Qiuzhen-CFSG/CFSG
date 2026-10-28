module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPlaneStabilizer
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPlaneResidual
public import Theory.GroupTheory.PCoreSurjective

/-!
# The two-core of the original Mathieu plane residual

The full plane action of N_L(U) restricts surjectively to its solvable
residual. Its M24 marking has two-group kernel. The exact native plane
stabilizer and perfectness kill the symmetric-three affine factor, so the
remaining action kernel is a two-group. Since GL3(2) is simple and perfect,
this kernel is exactly the residual's two-core.

Both the centralizer equality and quotient equivalence are transported to
the literal embedded residual, retaining the original plane coordinates
and conjugation action. NonFFSourceMathieuM24Component applies these
results to the chosen-module offender and its compatible pair.
Source: Aschbacher--Smith H.15.6(2) and 8.2.6(3), printed pp.401,717,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open PairOvergroups PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation
open scoped Pointwise MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
variable {G : Type*} [Group G] [Finite G]

/-- The literal plane action of the original residual has its two-core as kernel. -/
theorem plane_residual_core_action
    (W L U : Subgroup G) [IsElementaryAbelian 2 W]
    (hLW : L ≤ normalizer (W : Set G)) (hUW : U ≤ W)
    (q : L →* M24) (hq : Function.Surjective q) (hq2 : IsPGroup 2 q.ker)
    (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (hF : ∀ (l : L) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨l,hLW l.property⟩ w)) =
        cocodeRepresentation (q l) (F (Additive.ofMul w)))
    (hplane : ∀ w : W, (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ standardPlaneMap.range) :
    let N := L ⊓ normalizer (U : Set G)
    let R := solvableResidual N
    ∃ (e : U ≃* Multiplicative Vector) (r : R →* BinaryLinear.GL Vector),
      Function.Surjective r ∧ r.ker = pCore 2 R ∧
      r.ker = (centralizer (U : Set G)).comap (N.subtype.comp R.subtype) ∧
      (∀ u : U, standardPlaneMap (e u).toAdd =
        F (Additive.ofMul (inclusion hUW u))) ∧
      ∀ (x : R) (u : U),
        (e (U.normalizerMonoidHom ⟨x.val.val,x.val.property.2⟩ u)).toAdd =
          r x (e u).toAdd := by
  let N := L ⊓ normalizer (U : Set G)
  let R := solvableResidual N
  obtain ⟨e,π,hπ,hker,he,ha⟩ := plane_normalizer_action W L U hLW hUW q hq F hF hplane
  let r := π.comp R.subtype
  have hr : Function.Surjective r := residual_surjective π hπ
  let j : R →* L := (inclusion (show N ≤ L from inf_le_left)).comp R.subtype
  have hj : Function.Injective j := (inclusion_injective inf_le_left).comp R.subtype_injective
  let f := q.comp j
  have hf : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.ker.comap j)
    exact hq2.comap_of_injective j hj
  have hs (x : R) : f x ∈ subspaceStabilizer cocodeRepresentation standardPlaneMap.range := by
    intro v
    obtain ⟨w,rfl⟩ := F.surjective v
    change cocodeRepresentation (q (j x)) (F (Additive.ofMul w.toMul)) ∈ _ ↔
      F (Additive.ofMul w.toMul) ∈ _
    rw [←hF,←hplane,←hplane]
    exact (mem_normalizer_iff.mp x.val.property.2 w.toMul.val).symm
  have hkfix (k : r.ker) (v : Vector) :
      cocodeRepresentation (f k.val) (standardPlaneMap v) = standardPlaneMap v := by
    obtain ⟨u,hu⟩ := e.surjective (Multiplicative.ofAdd v)
    have huv : (e u).toAdd = v := congrArg Multiplicative.toAdd hu
    have hkc : k.val.val.val ∈ centralizer (U : Set G) := hker.le k.property
    have hcomm : W.normalizerMonoidHom ⟨j k.val,hLW (j k.val).property⟩
        (inclusion hUW u) = inclusion hUW u := by
      apply Subtype.ext
      exact (mul_inv_eq_iff_eq_mul).mpr (hkc _ u.property).symm
    rw [←huv,he]
    change cocodeRepresentation (q (j k.val)) (F (Additive.ofMul (inclusion hUW u))) = _
    rw [←hF,hcomm]
  have hkr : IsPGroup 2 r.ker := perfect_plane_kernel_isTwoGroup f hf hs r.ker hkfix
  let : Finite (BinaryLinear.GL Vector) := Finite.of_surjective r hr
  let : Group.IsPerfect (BinaryLinear.GL Vector) := BinaryLinear.linearGroup_isPerfect 3 (by decide)
  let := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup (BinaryLinear.GL Vector) :=
    (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.isSimpleGroup
  have hcore : pCore 2 (BinaryLinear.GL Vector) = ⊥ := by
    rcases (inferInstance : (pCore 2 (BinaryLinear.GL Vector)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · have hp : IsPGroup 2 (BinaryLinear.GL Vector) :=
        (h ▸ (pCore_isPGroup (p := 2) (G := BinaryLinear.GL Vector))).of_equiv topEquiv
      let : Group.IsNilpotent (BinaryLinear.GL Vector) := hp.isNilpotent
      exact (Group.IsPerfect.not_isSolvable (BinaryLinear.GL Vector) inferInstance).elim
  have hrc : r.ker = pCore 2 R := by
    have hh := r.comap_pCore_of_ker_isPGroup hr hkr
    simpa only [hcore,MonoidHom.comap_bot] using hh
  refine ⟨e,r,hr,hrc,?_,he,fun x u => ha x.val u⟩
  ext x
  exact show π x.val = 1 ↔ x.val.val ∈ centralizer (U : Set G) from
    SetLike.ext_iff.mp hker x.val

/-- Identify both the embedded residual's actual centralizer and its quotient. -/
theorem plane_residual_core_quotient
    (W L U : Subgroup G) [IsElementaryAbelian 2 W]
    (hLW : L ≤ normalizer (W : Set G)) (hUW : U ≤ W)
    (q : L →* M24) (hq : Function.Surjective q) (hq2 : IsPGroup 2 q.ker)
    (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (hF : ∀ (l : L) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨l,hLW l.property⟩ w)) =
        cocodeRepresentation (q l) (F (Additive.ofMul w)))
    (hplane : ∀ w : W, (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ standardPlaneMap.range) :
    let R := Chapter8.Section02.Normalizer.localResidual L U
    R.pCoreIn 2 = R ⊓ centralizer (U : Set G) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* BinaryLinear.GL Vector) := by
  let N := L ⊓ normalizer (U : Set G)
  let R₀ := solvableResidual N
  let R := Chapter8.Section02.Normalizer.localResidual L U
  obtain ⟨e,r,hr,hcore,hker,_,_⟩ := plane_residual_core_action W L U hLW hUW q hq hq2 F hF hplane
  let b : R₀ ≃* R := R₀.equivMapOfInjective N.subtype N.subtype_injective
  have hb : R.subtype.comp b.toMonoidHom = N.subtype.comp R₀.subtype := by
    ext x
    rfl
  have hc : R.pCoreIn 2 = (pCore 2 R₀).map (N.subtype.comp R₀.subtype) := by
    rw [pCoreIn,←pCore_map_iso 2 b,map_map,hb]
  refine ⟨?_,⟨(QuotientGroup.congr _ _ b.symm (pCore_map_iso 2 b.symm)).trans
    ((QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective r hr))⟩⟩
  rw [hc,←hcore,hker]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨mem_map_of_mem N.subtype y.property,hy⟩
  · rintro ⟨⟨y,hy,rfl⟩,hx⟩
    exact ⟨⟨y,hy⟩,hx,rfl⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
