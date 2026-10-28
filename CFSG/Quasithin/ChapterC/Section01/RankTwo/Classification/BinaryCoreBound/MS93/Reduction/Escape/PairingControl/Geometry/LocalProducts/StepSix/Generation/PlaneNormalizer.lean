module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.Action
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.FiniteGeometry.Planes

/-!
# The literal normalizer of a plane in the natural layer

Use the natural coordinates of `OppositeSectionAt`, with its own marked
projection throughout. Equivariance and injectivity identify the preimage of
the full matrix plane stabilizer with the actual relative normalizer. Thus
its image is the full plane stabilizer and it contains the actual local
kernel. Maximality of an order-four plane stabilizer now gives generation
with any local subgroup that does not normalize the plane; the kernel
containment lifts this equality back to the vertex stabilizer.

The imported finite geometry is a statement about the literal binary matrix
model. No `LocalControl`, `CommonFacts`, or later propagation premise is used.

Source: Meierfrankenfeld--Stellmacher (1993), the generation equality following
(4.3.2)(6), printed p.885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
open Selection.Centralizer.Generation
open Propagation.Backward.Products.Selection.Choices (modelAction planeStabilizer)
open Propagation.Backward.Products.Selection.Choices.FiniteGeometry (planeStabilizer_isCoatom)
variable {M : Type*} [Group M] {R : Subgroup M} {a : Vertex R}

namespace PlaneNormalizer

/-- Coordinates retain every subgroup of the actual natural layer. -/
theorem naturalImage_injective (o : OppositeSectionAt a)
    {E F : Subgroup (FreeAmalgam R)} (hE : E ≤ U R a) (hF : F ≤ U R a)
    (h : naturalImage o E = naturalImage o F) : E = F := by
  have hh := map_injective (naturalEquiv o).injective h
  have hm := congrArg (Subgroup.map (U R a).subtype) hh
  simpa only [map_subgroupOf_eq_of_le hE, map_subgroupOf_eq_of_le hF] using hm

/-- The same marking transports the plane and its conjugates. -/
theorem naturalImage_conjugate (o : OppositeSectionAt a) (g : stabilizer R a)
    (E : Subgroup (FreeAmalgam R)) (hE : E ≤ U R a) :
    naturalImage o (E.map (MulAut.conj (g : FreeAmalgam R)).toMonoidHom) =
      (naturalImage o E).map (modelAction (markedProjection o g)).toMonoidHom := by
  apply le_antisymm
  · rintro _ ⟨v, ⟨u, hu, huv⟩, rfl⟩
    refine ⟨naturalEquiv o ⟨u, hE hu⟩, ⟨⟨u, hE hu⟩, hu, rfl⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    exact (naturalEquiv_conjugation o g ⟨u, hE hu⟩ v huv.symm).symm
  · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    let v : U R a := ⟨g * (u : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹,
      (mem_normalizer_iff.mp (U_normalized a g.property) u).mp u.property⟩
    refine ⟨v, ⟨u, hu, rfl⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    exact naturalEquiv_conjugation o g u v rfl

/-- Exact preimage, including the action kernel, of the full setwise stabilizer. -/
theorem planeStabilizer_comap (o : OppositeSectionAt a)
    (E : Subgroup (FreeAmalgam R)) (hE : E ≤ U R a) :
    (planeStabilizer (naturalImage o E)).comap (markedProjection o) =
      (stabilizer R a ⊓ normalizer (E : Set (FreeAmalgam R))).subgroupOf
        (stabilizer R a) := by
  ext g
  have hg : E.map (MulAut.conj (g : FreeAmalgam R)).toMonoidHom ≤ U R a :=
    (map_mono hE).trans
      (mem_normalizer_iff_map_conj_eq.mp (U_normalized a g.property)).le
  change (naturalImage o E).map (modelAction (markedProjection o g)).toMonoidHom =
    naturalImage o E ↔ (g : FreeAmalgam R) ∈ stabilizer R a ∧
      (g : FreeAmalgam R) ∈ normalizer (E : Set (FreeAmalgam R))
  rw [and_iff_right g.property, mem_normalizer_iff_map_conj_eq,
    ← naturalImage_conjugate o g E hE]
  exact ⟨fun h => naturalImage_injective o hg hE h, congrArg (naturalImage o)⟩

/-- The relative normalizer has the entire plane-stabilizer image. -/
theorem relativeNormalizer_image (o : OppositeSectionAt a)
    (E : Subgroup (FreeAmalgam R)) (hE : E ≤ U R a) :
    actorImage o (stabilizer R a ⊓ normalizer (E : Set (FreeAmalgam R))) =
      planeStabilizer (naturalImage o E) := by
  rw [actorImage, ← planeStabilizer_comap o E hE]
  exact map_comap_eq_self_of_surjective
    (o.naturalU.marking.surjective.comp o.surjective) _

/-- The literal local kernel belongs to the relative normalizer. -/
theorem kernel_le_relativeNormalizer (o : OppositeSectionAt a)
    (E : Subgroup (FreeAmalgam R)) (hE : E ≤ U R a) :
    Q R a ≤ stabilizer R a ⊓ normalizer (E : Set (FreeAmalgam R)) := by
  intro x hx
  let g : stabilizer R a := ⟨x, hx.1⟩
  have hk : g ∈ (markedProjection o).ker := (markedProjection_kernel o).symm ▸ hx
  have hm : g ∈ (planeStabilizer (naturalImage o E)).comap (markedProjection o) :=
    (ker_le_comap _ _) hk
  rw [planeStabilizer_comap o E hE] at hm
  exact hm

/-- Full quotient generation lifts through the contained actual local kernel. -/
theorem generation_lifts (o : OppositeSectionAt a)
    (H K : Subgroup (FreeAmalgam R))
    (hH : H ≤ stabilizer R a) (hK : K ≤ stabilizer R a)
    (hQ : Q R a ≤ H ⊔ K)
    (hgen : actorImage o H ⊔ actorImage o K = ⊤) :
    H ⊔ K = stabilizer R a := by
  have hm : ((H ⊔ K).subgroupOf (stabilizer R a)).map (markedProjection o) = ⊤ := by
    rw [subgroupOf_sup hH hK, Subgroup.map_sup]
    exact hgen
  have hc : (actorImage o (H ⊔ K)).comap (markedProjection o) =
      (H ⊔ K).subgroupOf (stabilizer R a) := by
    apply comap_map_eq_self
    rw [markedProjection_kernel]
    exact fun _ hx => hQ hx
  change (((H ⊔ K).subgroupOf (stabilizer R a)).map (markedProjection o)).comap _ = _ at hc
  rw [hm, comap_top] at hc
  exact le_antisymm (sup_le hH hK) (subgroupOf_eq_top.mp hc.symm)

/-- A nonnormalizing local actor completes an order-four plane normalizer. -/
theorem generation_of_not_normalizing (o : OppositeSectionAt a)
    (E K : Subgroup (FreeAmalgam R)) (hE : E ≤ U R a)
    (hcard : Nat.card (naturalImage o E) = 4) (hK : K ≤ stabilizer R a)
    (hnot : ¬ K ≤ normalizer (E : Set (FreeAmalgam R))) :
    (stabilizer R a ⊓ normalizer (E : Set (FreeAmalgam R))) ⊔ K =
      stabilizer R a := by
  apply generation_lifts o _ _ inf_le_left hK
    ((kernel_le_relativeNormalizer o E hE).trans le_sup_left)
  rw [relativeNormalizer_image o E hE]
  apply (planeStabilizer_isCoatom _ hcard).2
  refine ⟨le_sup_left, ?_⟩
  intro hle
  apply hnot
  intro x hx
  let g : stabilizer R a := ⟨x, hK hx⟩
  have hg : markedProjection o g ∈ actorImage o K := mem_map_of_mem _ hx
  have hp : g ∈ (planeStabilizer (naturalImage o E)).comap (markedProjection o) :=
    hle ((show actorImage o K ≤ planeStabilizer (naturalImage o E) ⊔
      actorImage o K from le_sup_right) hg)
  rw [planeStabilizer_comap o E hE] at hp
  exact hp.2

end PlaneNormalizer
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
