module
public import Theory.GroupTheory.IndexTwoOmegaDiagonal
public import Theory.Representation.BinaryConjugationSection.SL2CubicFixed
/-!
# A central diagonal detects cubic natural action

A central involution in an index-two subgroup produces an involution in the
omega-center by multiplying it with its outside conjugate. If the two moved
factors intersect only in the retained coordinate kernel, a cubic natural
actor fixing this diagonal would fix a nonzero natural vector, a contradiction.

Source: Aschbacher–Smith10.1.2(5), printed p.742.
-/

public noncomputable section
open Subgroup Stellmacher Representation
open scoped IsMulCommutative MatrixGroups
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G]
  {R S T W Z : Subgroup G} {K : Type*} [Field K] [CharP K 2]
local instance omegaDiagonalAlgebra : Algebra (ZMod 2) K := ZMod.algebra K 2

theorem natural_cubic_not_centralizes_omegaCenter_of_diagonal (q : R →* SL(2,K))
    (n : BinaryConjugationSection R W Z (SL2.BinarySmall.natural.comp q))
    (hST : S ≤ T) (hi : S.relIndex T = 2)
    (t : G) (ht : t ∈ T) (htS : t ∉ S)
    (hRWt : R ≤ normalizer (W.map (MulAut.conj t).toMonoidHom : Set G))
    (hinter : W ⊓ W.map (MulAut.conj t).toMonoidHom ≤ Z)
    (w : W) (hwS : (w:G) ∈ omegaOneCenterAmbient S)
    (hc : Commute (w:G) (t*w*t⁻¹)) (hw : n.coordinates w ≠ 1)
    (b : R) (hb : orderOf (q b) = 3) :
    (b:G) ∉ centralizer (omegaOneCenterAmbient T : Set G) := by
  intro hbZ
  let v := t*(w:G)*t⁻¹
  have hv : v ∈ W.map (MulAut.conj t).toMonoidHom := mem_map_of_mem _ w.property
  have hz : (w:G)*v ∈ omegaOneCenterAmbient T :=
    indexTwo_diagonal_mem_omegaCenter S T hST hi t ht htS w hwS hc
  have hfixed : (b:G)*((w:G)*v)*(b:G)⁻¹ = (w:G)*v := by
    rw [←hbZ _ hz,mul_inv_cancel_right]
  let wb : W := ⟨(b:G)*w*(b:G)⁻¹,
    (mem_normalizer_iff.mp (n.normalized b.property) w).mp w.property⟩
  have hvb : (b:G)*v*(b:G)⁻¹ ∈ W.map (MulAut.conj t).toMonoidHom :=
    (mem_normalizer_iff.mp (hRWt b.property) v).mp hv
  have hdiff : ((w⁻¹*wb : W):G) = v*((b:G)*v*(b:G)⁻¹)⁻¹ := by
    have he : (wb:G)*((b:G)*v*(b:G)⁻¹) = (w:G)*v := by
      calc
        (wb:G)*((b:G)*v*(b:G)⁻¹) = (b:G)*((w:G)*v)*(b:G)⁻¹ := by dsimp [wb]; group
        _ = _ := hfixed
    calc
      ((w⁻¹*wb : W):G) = (w:G)⁻¹*((wb:G)*((b:G)*v*(b:G)⁻¹))*((b:G)*v*(b:G)⁻¹)⁻¹ := by change (w:G)⁻¹*(wb:G) = _; group
      _ = v*((b:G)*v*(b:G)⁻¹)⁻¹ := by rw [he]; group
  have hker : ((w⁻¹*wb : W):G) ∈ Z := by
    apply hinter
    refine ⟨(w⁻¹*wb).property,?_⟩
    rw [hdiff]
    exact (W.map (MulAut.conj t).toMonoidHom).mul_mem hv
      ((W.map (MulAut.conj t).toMonoidHom).inv_mem hvb)
  have hcoord : n.coordinates wb = n.coordinates w := by
    have he := (n.coordinates_eq_one_iff (w⁻¹*wb)).mpr hker
    rw [map_mul,map_inv,inv_mul_eq_one] at he
    exact he.symm
  have he := n.equivariant b w
  have hzero : (n.coordinates w).toAdd = 0 := by
    apply Matrix.SL2.cubic_fixed_eq_zero (q b) hb
    exact he.symm.trans (congrArg Multiplicative.toAdd hcoord)
  exact hw (Multiplicative.toAdd.injective hzero)
end Representation.BinaryConjugationSection
