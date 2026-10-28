module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.ModuleCover

/-!
# Permitted critical rechoice for 14.7.70

Multiplying the original H-rechoice by an element of L₁T preserves the
second-vertex alignment of the actual critical path. Characteristicity of
O₂(L₁T) preserves Uα ≤ R₁. Conjugation commutes with the literal star map
H → H/O₂(H), so the preceding order-two conclusion survives this same
rechoice. Both Uα and Zα use its one updated conjugator.

The rank-three groups below are actual subgroup constructions, using the
two-residual O²(Y_E), not the two-core. They provide a common interface for
the local geometry and Goldschmidt arguments. `Rechoice.Statement` states
all four source clauses; it is not asserted by the transport lemmas here.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Lemma 14.7.70, printed pp.1073–1075.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

namespace Rechoice
/-- The source permits rechoice in L₁T, not in arbitrary H. -/
def group (F : InvariantFlag T V 3) (L : Subgroup G) : Subgroup G :=
  F.Li L 1 ⊔ (T : Subgroup G)

theorem group_le_H : group F L ≤ F.H :=
  sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)

theorem group_le_LT : group F L ≤ L ⊔ (T : Subgroup G) :=
  sup_le_sup ((F.Li_le L 1).trans inf_le_left) le_rfl

theorem group_normalizes_R₁ : group F L ≤ normalizer (F.Ri L 1 : Set G) :=
  (group F L).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 (group F L)))

private theorem conjugate_mul (A : Subgroup G) (g h : G) :
    conjugate A (g * h) = conjugate (conjugate A g) h := by
  unfold conjugate
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

/-- Conjugation and the literal H/O₂(H) image commute. -/
theorem star_conjugate (A : Subgroup G) (hAH : A ≤ F.H) (h : F.H) :
    star F (conjugate A h) = conjugate (star F A) (starMap F h) := by
  have hc : conjugate A h ≤ F.H :=
    (map_mono hAH).trans_eq ((conjugate_eq_iff F.H h).mpr (F.H.le_normalizer h.property))
  have hs : (conjugate A h).subgroupOf F.H = conjugate (A.subgroupOf F.H) h := by
    apply map_injective F.H.subtype_injective
    rw [map_subgroupOf_eq_of_le hc]
    unfold conjugate
    rw [map_map]
    have he : F.H.subtype.comp (MulAut.conj h⁻¹).toMonoidHom =
        (MulAut.conj (h : G)⁻¹).toMonoidHom.comp F.H.subtype := by ext x; rfl
    rw [he, ← map_map, map_subgroupOf_eq_of_le hAH]
  unfold star
  rw [hs]
  unfold conjugate
  rw [map_map, map_map]
  congr 1

end Rechoice

namespace CriticalPath
variable (c : CriticalPath (L := L) F)

/-- The same critical path, with its H-rechoice multiplied by an element
of L₁T. Its second vertex remains aligned with the original base vertex. -/
def reselect (n : Rechoice.group F L) : CriticalPath (L := L) F where
  b := c.b
  radius := c.radius
  gammaConjugator := c.gammaConjugator
  path := c.path
  geodesic := c.geodesic
  length := c.length
  first := c.first
  critical := c.critical
  rechoice := c.rechoice * ⟨n, Rechoice.group_le_H n.property⟩
  alignment := by
    rw [map_mul, mul_inv_rev, mul_smul, c.alignment]
    apply MulAction.mem_stabilizer_iff.mp
    rw [Subgroup.CosetGeometry.stabilizer_base]
    change (n : G)⁻¹ ∈ L ⊔ (T : Subgroup G)
    exact inv_mem (Rechoice.group_le_LT n.property)

@[simp] theorem reselect_b (n : Rechoice.group F L) : (c.reselect n).b = c.b := rfl

@[simp] theorem reselect_conjugator (n : Rechoice.group F L) :
    (c.reselect n).conjugator = c.conjugator * (n : G) := by
  change (c.gammaConjugator : G) * ((c.rechoice : G) * n) = _
  exact (mul_assoc _ _ _).symm

theorem reselect_Uα (n : Rechoice.group F L) :
    (c.reselect n).Uα = conjugate c.Uα n := by
  rw [Uα, reselect_conjugator, Rechoice.conjugate_mul]
  rfl

theorem reselect_Zα (n : Rechoice.group F L) :
    (c.reselect n).Zα = conjugate c.Zα n := by
  rw [Zα, reselect_conjugator, Rechoice.conjugate_mul]
  rfl

/-- All earlier image conditions survive the very same rechoice. -/
theorem reselect_earlierImages (earlier : c.EarlierImages) (n : Rechoice.group F L) :
    (c.reselect n).EarlierImages where
  placement := by
    rw [reselect_Uα]
    exact (map_mono earlier.placement).trans_eq
      ((conjugate_eq_iff (F.Ri L 1) n).mpr (Rechoice.group_normalizes_R₁ n.property))
  image_eq := earlier.image_eq
  sylow := earlier.sylow

/-- An actual application: source 14.7.66 remains valid after rechoice. -/
theorem reselect_images (earlier : c.EarlierImages) (n : Rechoice.group F L) :
    star F (c.reselect n).Uα ≤ star F (Q T L) ∧
      Chapter1.IsSylowIn 2 (star F (Q T L)) (star F (K F)) :=
  (c.reselect n).lemma_14_7_66 (c.reselect_earlierImages earlier n)

/-- The image of the reselected actor is a conjugate in the same quotient. -/
theorem reselect_star (earlier : c.EarlierImages) (n : Rechoice.group F L) :
    star F (c.reselect n).Uα = conjugate (star F c.Uα)
      (starMap F ⟨n, Rechoice.group_le_H n.property⟩) := by
  rw [reselect_Uα]
  exact Rechoice.star_conjugate (F := F) c.Uα (c.Uα_le_H earlier)
    ⟨n, Rechoice.group_le_H n.property⟩

/-- In particular the preceding 14.7.69 conclusion is preserved. -/
theorem reselect_star_card (earlier : c.EarlierImages) (n : Rechoice.group F L) :
    Nat.card (star F (c.reselect n).Uα) = Nat.card (star F c.Uα) := by
  rw [c.reselect_star earlier n]
  let h : F.H := ⟨n, Rechoice.group_le_H n.property⟩
  let e := MulAut.conj (starMap F h)⁻¹
  exact (Nat.card_congr ((star F c.Uα).equivMapOfInjective e.toMonoidHom
    e.injective).toEquiv).symm

end CriticalPath

namespace Rechoice
variable (c : CriticalPath (L := L) F)

/-- The rank-two subgroup called E on printed p.1074. -/
def E : Subgroup G := F.Vi 1 ⊔ c.Zα

/-- The subgroup generated by the two actual vertex two-cores. -/
def YE : Subgroup G := F.H.pCoreIn 2 ⊔ c.Qα

/-- The two-residual O²(Y_E), included in G. -/
def Y : Subgroup G := (pResidual 2 (YE c)).map (YE c).subtype

/-- The ambient group of the proposed Goldschmidt triple. -/
def I : Subgroup G := group F L ⊔ Y c

/-- The conjugate span on which the terminal H.5.5 argument acts. -/
def VI : Subgroup G := conjugateSpanBy (F.Vi 1) (I c)

/-- The local E-generation calculation places the complete L₁-span in the
same module used by the terminal recognition argument. -/
theorem span_Zα_le_VI
    (hE : E c ≤ conjugateSpanBy (F.Vi 1) (Y c)) :
    conjugateSpanBy c.Zα (F.Li L 1) ≤ VI c := by
  have hZI : c.Zα ≤ VI c := (le_sup_right : c.Zα ≤ E c).trans
    (hE.trans (conjugateSpanBy_mono le_rfl (le_sup_right : Y c ≤ I c)))
  exact conjugateSpanBy_le hZI
    (((le_sup_left : F.Li L 1 ≤ group F L).trans
      (le_sup_left : group F L ≤ I c)).trans
      (le_normalizer_conjugateSpanBy (F.Vi 1) (I c)))

/-- All source clauses concern one consistently reselected critical pair.
In clause (4) it is Uα that is L-conjugate to U; the original conjugator
is not required to belong to L. This proposition still needs a proof. -/
def Statement [Finite G] {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    (d : Data T L V F W) : Prop :=
  ∃ n : group F L,
    (c.reselect n).Zα ≤ F.Vi 2 ∧
    primeRank 2 d.U₀ ≤ 2 ∧
    F.U ⊓ (c.reselect n).Uα = d.U₀ ⊔ V ∧
    F.U ⊓ (c.reselect n).Uα = ⁅F.U, (c.reselect n).Uα⁆ ⊔ V ∧
    F.U ⊓ (c.reselect n).Uα = ⁅F.U, (c.reselect n).Uα⁆ ⊔ d.U₀ ∧
    c.b = 3 ∧ ∃ l ∈ L, (c.reselect n).Uα = conjugate F.U l

end Rechoice
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
