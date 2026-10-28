module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.SingleEndpoint
public import Theory.GroupTheory.SplitExtensionGivenComplement
public import Theory.SpecificGroups.PSL3.CartanActions.FullTorusFixer
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.SpecificGroups.SL2.Affine.Core

/-!
# The actual endpoint marked as the full PSL₃(4) point parabolic

The original natural kernel coordinates and quotient-marked complement
give affine coordinates on the same actual endpoint. Transport to the
canonical field identifies the whole group with the full projective point
parabolic. The original elementary sixteen maps to its intrinsic two-core.
No abstract recognition or endpoint-isomorphism premise is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private def standard_affine_equiv :
    Matrix.SL2.Affine Representation.SL2FourNatural.F ≃*
      Matrix.SL2.Affine Matrix.PSL3Four.F := by
  let e := Representation.SL2FourNatural.standardVectorEquiv.toAddEquiv.toMultiplicative
  let k := Representation.SL2FourNatural.standardGroupEquiv
  apply SemidirectProduct.congr e k
  intro g
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  exact Representation.SL2FourNatural.standard_equivariant g v.toAdd

private def canonical_point_affine_equiv :
    Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F ≃*
      Matrix.SL2.Affine Matrix.PSL3Four.F := by
  have he : Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F =
      Matrix.PSL3.LinearThree.pointLocal Matrix.PSL3Four.F := by
    rw [Matrix.PSL3.LinearThree.pointParabolic_eq_sup]
    exact sup_eq_left.mpr
      (Matrix.PSL3.CartanActions.FullTorusFixer.borel_le_pointLocal_of_card_four Matrix.PSL3Four.card_F)
  exact (MulEquiv.subgroupCongr he).trans
    (Matrix.PSL3.LinearThree.pointLocalEquivAffine Matrix.PSL3Four.F)

/-- The same original sixteen is the intrinsic two-core of an actual
subgroup marked as the full canonical PSL₃(4) point parabolic. -/
theorem TypeAt.sixteen_point_parabolic (h : TypeAt z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (hCA : centralizer (A : Set G) = A)
    (hpure : ∀ x ∈ A, x ≠ 1 → IsConj x z)
    (hpoints : ∀ x ∈ A, x ≠ 1 →
      Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) :
    ∃ (P : Subgroup G), A ≤ P ∧ P ≤ normalizer (A : Set G) ∧
      Nat.card P = 960 ∧ P.pCoreIn 2 = A ∧
      ∃ e : P ≃* Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F,
        (A.subgroupOf P).map e.toMonoidHom =
          pCore 2 (Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F) := by
  obtain ⟨P, K, hAP, hPN, _, hP, _, _, _, q, hq, hk, c, hc, hcomp, _, _⟩ :=
    h.sixteen_natural_endpoint A hA hCA hpure hpoints
  let a : q.ker ≃* A := (MulEquiv.subgroupCongr hk).trans (subgroupOfEquivOfLe hAP)
  let w := a.trans c
  have hw (g : P) (u : q.ker) :
      w (MulAut.conjNormal g u) = Matrix.SL2.naturalAction Representation.SL2FourNatural.F (q g) (w u) := by
    have he : a (MulAut.conjNormal g u) = A.normalizerMonoidHom (inclusion hPN g) (a u) := by
      apply Subtype.ext
      rfl
    change c (a (MulAut.conjNormal g u)) = _
    rw [he]
    exact hc g (a u)
  obtain ⟨f, hfq, _, _, _⟩ := exists_marked_semidirect_equiv_of_given_complement
    q hq w (Matrix.SL2.naturalAction Representation.SL2FourNatural.F) hw
    (K.subgroupOf P) (hk ▸ hcomp)
  have hfcore : pCore 2 P = q.ker := by
    apply (Subgroup.map_injective (f := f.toMonoidHom) f.injective)
    rw [pCore_map_iso, Matrix.SL2.affine_twoCore_eq]
    apply le_antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := f.surjective y
      refine ⟨x, ?_, rfl⟩
      change q x = 1
      exact (hfq x).symm.trans hy
    · rintro y ⟨x, hx, rfl⟩
      change (f x).right = 1
      exact (hfq x).trans hx
  have hcore : pCore 2 P = A.subgroupOf P := hfcore.trans hk
  have hambient : P.pCoreIn 2 = A := by
    change (pCore 2 P).map P.subtype = A
    rw [hcore, map_subgroupOf_eq_of_le hAP]
  let e := (f.trans standard_affine_equiv).trans canonical_point_affine_equiv.symm
  refine ⟨P, hAP, hPN, hP, hambient, e, ?_⟩
  rw [← hcore, pCore_map_iso]

end CFSG.Quasithin.HigmanSims
