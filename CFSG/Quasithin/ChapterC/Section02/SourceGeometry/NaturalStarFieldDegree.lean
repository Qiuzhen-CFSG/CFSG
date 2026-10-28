module

public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import Theory.Representation.SymplecticFourOrthogonalCover.Roots.Binary
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder

/-!
# Nonbinary fields in the full natural star rows

The actual star component is perfect. The full groups Sp₄(2) and G₂(2)
are not perfect, so their full natural rows have field degree greater
than one. The separate derived binary and A₆ rows are untouched.

Source: the natural alternatives of B.5.1(2) used in C.4.1 and 12.7.5,
printed pp.99,151 and 840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}

omit [Finite G] in
/-- The full symplectic star marking cannot be over the two-element field. -/
theorem star_symplectic_degree_gt_one_from_source
    (h : Input KnownSimple.IsKnownSimple H R M K) (F : BinaryField)
    (e : starImage K R K ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) :
    1 < F.degree := by
  by_contra hn
  have hd : F.degree = 1 := by have := F.degree_pos; omega
  have hc : Nat.card F.Carrier = 2 := by rw [F.card_eq,hd]; norm_num
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  let : Group.IsPerfect (starImage K R K) :=
    Group.IsPerfect.ofSurjective (coreToStar_surjective h.normalizes)
  let : Group.IsPerfect (Matrix.symplecticGroup (Fin 2) F.Carrier) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  apply Representation.SymplecticFourOrthogonalCover.Roots.card_two_root_not_mem_derived hc
  rw [Group.IsPerfect.commutator_eq_top]
  trivial

omit [Finite G] in
/-- The full G₂ star marking cannot be over the two-element field. -/
theorem star_g2_degree_gt_one_from_source
    (h : Input KnownSimple.IsKnownSimple H R M K) (F : BinaryField)
    (e : starImage K R K ≃* Atlas.G2.Model F.Carrier) :
    1 < F.degree := by
  by_contra hn
  have hd : F.degree = 1 := by have := F.degree_pos; omega
  have hc : Nat.card F.Carrier = 2 := by rw [F.card_eq,hd]; norm_num
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  let : Group.IsPerfect (starImage K R K) :=
    Group.IsPerfect.ofSurjective (coreToStar_surjective h.normalizes)
  let : Group.IsPerfect (Atlas.G2.Model F.Carrier) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hcard := Atlas.G2.DerivedEvenOrder.card_derived_binary hc
  rw [Group.IsPerfect.commutator_eq_top,card_top,Atlas.G2.card_Model,hc] at hcard
  norm_num at hcard

end CFSG.Quasithin.ChapterC.C27Source
