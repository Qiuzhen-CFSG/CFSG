module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceComparison.Marking
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicNormalizerExtension

/-!
# Compatible vertex and local A₅ maps for the source J₂ system

The dihedral comparison identifies the local vertex overlaps. Their
literal embeddings are the normalizers of the marked cubic subgroups
inside the local A₅ groups. Extending the prescribed S₃ isomorphism
therefore supplies a local A₅ map agreeing with the vertex map on every
element of the intersection. Surjectivity gives the reverse containment
needed to preserve that intersection exactly.

The last theorem applies the construction to the published source and
ATLAS uniqueness systems. It supplies the agreement, local-vertex and
pointwise-edge conditions of a similarity. The local setwise-edge
condition still requires an adjustment of these maps; it is not asserted
for the arbitrary extension selected here. Source pentagon contraction
is also a separate obligation.

Source: Aschbacher, *Sporadic Groups* (1994), 47.10, pp.266–267.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceComparison
open SourceLocal SourceLocal.PrimeNormalizers.ThreeLocal
open Theory.GroupTheory.GraphUniquenessSystem
open Sporadic.LeechRelated.J2

private def overlapNormalizerEquiv {A : Type*} [Group A]
    (X K : Subgroup A) (hX : X ≤ K) :
    K.subgroupOf (normalizer (X : Set A)) ≃* normalizer (X.subgroupOf K : Set K) where
  toFun g := ⟨⟨g.val.val, g.property⟩, by
    rw [← subgroupOf_normalizer_eq hX]
    exact g.val.property⟩
  invFun g := ⟨⟨g.val.val, by
    have h := g.property
    change g.val ∈ (normalizer (X : Set A)).subgroupOf K
    simpa only [subgroupOf_normalizer_eq hX] using h⟩, g.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- Once the literal dihedral markings are aligned, the prescribed overlap
map extends to an actual local A₅ isomorphism. -/
theorem local_comparison (D : Seed G) (F : EdgeFrame D)
    (eM : M D ≃* RecognitionGeometry.M)
    (hK : ∀ m : M D, (m : G) ∈ F.K ↔ (eM m : Carrier) ∈ RecognitionGeometry.K) :
    ∃ eK : F.K ≃* RecognitionGeometry.K,
      (D.X.subgroupOf F.K).map eK.toMonoidHom =
        RecognitionGeometry.X.subgroupOf RecognitionGeometry.K ∧
      (∀ (g : G) (hgK : g ∈ F.K) (hgM : g ∈ M D),
        (eM ⟨g, hgM⟩ : Carrier) = (eK ⟨g, hgK⟩ : Carrier)) ∧
      (∀ g : F.K, (g : G) ∈ M D ↔ (eK g : Carrier) ∈ RecognitionGeometry.M) := by
  have hX : D.X ≤ F.K := le_sup_left.trans
    (F.endpoints_le (InvolutionGeometry.Applications.edgeFixer_equiv D F.adjacent))
  have htX : RecognitionGeometry.X ≤ RecognitionGeometry.K :=
    le_sup_left.trans RecognitionGeometry.X_sup_Y_le_K
  let V := F.K.subgroupOf (M D)
  let W := RecognitionGeometry.K.subgroupOf RecognitionGeometry.M
  let eV : V ≃* W :=
    { toFun := fun v => ⟨eM v, (hK v).mp v.property⟩
      invFun := fun w => ⟨eM.symm w, (hK _).mpr (by rw [eM.apply_symm_apply]; exact w.property)⟩
      left_inv := fun _ => Subtype.ext (eM.symm_apply_apply _)
      right_inv := fun _ => Subtype.ext (eM.apply_symm_apply _)
      map_mul' := fun _ _ => Subtype.ext (map_mul eM _ _) }
  let f := (overlapNormalizerEquiv D.X F.K hX).symm.trans
    (eV.trans (overlapNormalizerEquiv RecognitionGeometry.X RecognitionGeometry.K htX))
  obtain ⟨eK, heX, he⟩ := alternatingGroup.FiveLocalGeometry.extend_cubic_normalizer
    F.localEquiv RecognitionGeometry.LocalA5.localEquiv
    (D.X.subgroupOf F.K) (RecognitionGeometry.X.subgroupOf RecognitionGeometry.K)
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv, D.card_X])
    (by rw [Nat.card_congr (subgroupOfEquivOfLe htX).toEquiv, RecognitionGeometry.card_X]) f
  have hagree (g : G) (hgK : g ∈ F.K) (hgM : g ∈ M D) :
      (eM ⟨g, hgM⟩ : Carrier) = (eK ⟨g, hgK⟩ : Carrier) := by
    exact (congrArg Subtype.val (he ((overlapNormalizerEquiv D.X F.K hX)
      ⟨⟨g, hgM⟩, hgK⟩))).symm
  refine ⟨eK, heX, hagree, ?_⟩
  intro g
  constructor
  · intro hg
    rw [← hagree g g.property hg]
    exact (eM ⟨g, hg⟩).property
  · intro hg
    let m : M D := eM.symm ⟨eK g, hg⟩
    have hmK : (m : G) ∈ F.K := (hK m).mpr (by
      change (eM (eM.symm ⟨eK g, hg⟩) : Carrier) ∈ _
      rw [eM.apply_symm_apply]
      exact (eK g).property)
    have hmg : (m : G) = g := by
      have hh := hagree m hmK m.property
      have heq : (eK ⟨m, hmK⟩ : Carrier) = eK g := by
        rw [← hh]
        change (eM (eM.symm ⟨eK g, hg⟩) : Carrier) = _
        rw [eM.apply_symm_apply]
      exact congrArg Subtype.val (eK.injective (Subtype.ext heq))
    exact hmg ▸ m.property

/-- Both local maps and their agreement on the actual shared S₃ are constructed.
The setwise local edge alignment is the remaining comparison condition. -/
theorem compatible_local_maps (D : Seed G) :
    ∃ (eM : (sourceSystem D).vertexGroup ≃* ConcreteSystem.system.vertexGroup)
      (eK : (sourceSystem D).H ≃* ConcreteSystem.system.H),
      (∀ (g : G) (hgK : g ∈ (sourceSystem D).H) (hgM : g ∈ (sourceSystem D).vertexGroup),
        (eM ⟨g, hgM⟩ : Carrier) = (eK ⟨g, hgK⟩ : Carrier)) ∧
      (∀ g : (sourceSystem D).H, (g : G) ∈ (sourceSystem D).vertexGroup ↔
        (eK g : Carrier) ∈ ConcreteSystem.system.vertexGroup) ∧
      (∀ m : (sourceSystem D).vertexGroup, (m : G) ∈ (sourceSystem D).edgeGroup ↔
        (eM m : Carrier) ∈ ConcreteSystem.system.edgeGroup) := by
  obtain ⟨e, _, hE, hB⟩ := marked_edge_comparison D (sourceFrame D)
  obtain ⟨d, _, hd, hv⟩ := local_comparison D (sourceFrame D) e
    (vertex_overlap_of_marked D (sourceFrame D) e hB)
  have hM : (sourceSystem D).vertexGroup = M D := D.stabilizer_eq_normalizer D.base
  let eM := (MulEquiv.subgroupCongr hM).trans
    (e.trans (MulEquiv.subgroupCongr ConcreteSystem.system_vertexGroup.symm))
  let eK : (sourceSystem D).H ≃* ConcreteSystem.system.H :=
    d.trans (MulEquiv.subgroupCongr ConcreteSystem.system_local.symm)
  refine ⟨eM, eK, ?_, ?_, ?_⟩
  · intro g hgK hgM
    exact hd g hgK (hM ▸ hgM)
  · intro g
    rw [hM, ConcreteSystem.system_vertexGroup]
    exact hv g
  · intro m
    rw [ConcreteSystem.system_edgeGroup]
    exact hE (MulEquiv.subgroupCongr hM m)

end CFSG.Quasithin.Janko23.J2Recognition.SourceComparison
