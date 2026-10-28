module

public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixRealization

/-!
# Restriction of the exceptional marked matrix amalgam

Compatible actual isomorphisms from the two matrix local groups restrict to a
single faithful map on their common Sylow subgroup. Explicit images of the
matrix unipotent subgroup, root planes and highest-root element then give the
marked Sylow isomorphism. The agreement is on the entire local intersection;
no equality of that intersection with the Sylow group is asserted.

`SourceMarking` records exactly the subgroup alignments required from the
source's β. It is an input to the restriction theorem, not a recognition
result. Constructing β from the source hypotheses remains a separate task.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, §5.3.2
and §5.3.7, printed pp. 659--661 (PDF pp. 676--678).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter5.Section03ExceptionalSylowModel.MarkedRecognition

open Matrix.PSL3Four Matrix.PSL3Four.SylowModel

universe u
variable {G : Type u} [Group G]

/-- Actual local isomorphisms, including agreement on the whole overlap. -/
structure CompatibleLocalIsomorphisms (M₁ M₂ : Subgroup G) where
  left : MatrixRealization.local₁ ≃* M₁
  right : MatrixRealization.local₂ ≃* M₂
  agree : ∀ (g : FieldExtension) (h₁ : g ∈ MatrixRealization.local₁) (h₂ : g ∈ MatrixRealization.local₂),
    (left ⟨g, h₁⟩ : G) = (right ⟨g, h₂⟩ : G)

namespace CompatibleLocalIsomorphisms
variable {M₁ M₂ : Subgroup G} (β : CompatibleLocalIsomorphisms M₁ M₂)

def leftAmbient : MatrixRealization.local₁ →* G := M₁.subtype.comp β.left.toMonoidHom
def rightAmbient : MatrixRealization.local₂ →* G := M₂.subtype.comp β.right.toMonoidHom

def embedding : SylowModel.T →* G := β.leftAmbient.comp MatrixRealization.localEmbedding₁

theorem embedding_eq_right : β.embedding = β.rightAmbient.comp MatrixRealization.localEmbedding₂ := by
  ext a
  exact β.agree (MatrixRealization.embedding a) _ _

theorem embedding_injective : Function.Injective β.embedding :=
  Subtype.val_injective.comp (β.left.injective.comp MatrixRealization.localEmbedding₁_injective)

/-- Restrict the local isomorphism to any specified image of the matrix Sylow. -/
def restrict (P : Subgroup G) (hP : β.embedding.range = P) : SylowModel.T ≃* P :=
  (MonoidHom.ofInjective β.embedding_injective).trans (MulEquiv.subgroupCongr hP)

@[simp] theorem restrict_apply (P : Subgroup G) (hP : β.embedding.range = P)
    (a : SylowModel.T) : (β.restrict P hP a : G) = β.embedding a := rfl

private theorem map_local₁ (A : Subgroup SylowModel.T) :
    A.map MatrixRealization.localEmbedding₁ = (A.map MatrixRealization.embedding).subgroupOf MatrixRealization.local₁ := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, he⟩
    exact ⟨a, ha, Subtype.ext he⟩

private theorem map_local₂ (A : Subgroup SylowModel.T) :
    A.map MatrixRealization.localEmbedding₂ = (A.map MatrixRealization.embedding).subgroupOf MatrixRealization.local₂ := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, he⟩
    exact ⟨a, ha, Subtype.ext he⟩

theorem map_mark_left (A : Subgroup SylowModel.T) :
    A.map β.embedding =
      ((A.map MatrixRealization.embedding).subgroupOf MatrixRealization.local₁).map β.leftAmbient := by
  rw [← map_local₁, Subgroup.map_map]
  rfl

theorem map_mark_right (A : Subgroup SylowModel.T) :
    A.map β.embedding =
      ((A.map MatrixRealization.embedding).subgroupOf MatrixRealization.local₂).map β.rightAmbient := by
  rw [← map_local₂, Subgroup.map_map, β.embedding_eq_right]

theorem range_embedding : β.embedding.range =
    ((MatrixRealization.sylow : Subgroup FieldExtension).subgroupOf MatrixRealization.local₁).map β.leftAmbient := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨MatrixRealization.localEmbedding₁ a, ⟨a, rfl⟩, rfl⟩
  · rintro ⟨b, ⟨a, ha⟩, rfl⟩
    exact ⟨a, congrArg β.leftAmbient (Subtype.ext ha)⟩

/-- The precise alignment contract supplied by a marked source amalgam β.
Each premise concerns an actual local isomorphism, not an abstract quotient
order or a desired Sylow-group identification. -/
structure SourceMarking (P S V₁ V₂ Z : Subgroup G) (z : G) : Prop where
  sylow_image :
    ((MatrixRealization.sylow : Subgroup FieldExtension).subgroupOf MatrixRealization.local₁).map β.leftAmbient = P
  unipotent_image : (MatrixRealization.unipotent.subgroupOf MatrixRealization.local₁).map β.leftAmbient = S
  plane₁_image : (MatrixRealization.rootPlane₁.subgroupOf MatrixRealization.local₁).map β.leftAmbient = V₁
  plane₂_image : (MatrixRealization.rootPlane₂.subgroupOf MatrixRealization.local₂).map β.rightAmbient = V₂
  highestRoot_image : (MatrixRealization.highestRoot.subgroupOf MatrixRealization.local₁).map β.leftAmbient = Z
  involution_image : β.leftAmbient
    ⟨MatrixRealization.centralInvolution, MatrixRealization.sylow_le_local₁ ⟨SylowModel.z, rfl⟩⟩ = z

variable {P S V₁ V₂ Z : Subgroup G} {z : G}

def markedEquiv (h : β.SourceMarking P S V₁ V₂ Z z) : SylowModel.T ≃* P :=
  β.restrict P (β.range_embedding.trans h.sylow_image)

/-- All five marks are transported by the same restricted group isomorphism.
In particular the second plane is transported using the right-hand local map. -/
theorem markedEquiv_marks (h : β.SourceMarking P S V₁ V₂ Z z) :
    let f := P.subtype.comp (β.markedEquiv h).toMonoidHom
    SylowModel.S.map f = S ∧ SylowModel.V₁.map f = V₁ ∧
      SylowModel.V₂.map f = V₂ ∧ SylowModel.Z.map f = Z ∧ f SylowModel.z = z := by
  change SylowModel.S.map β.embedding = S ∧ SylowModel.V₁.map β.embedding = V₁ ∧
    SylowModel.V₂.map β.embedding = V₂ ∧ SylowModel.Z.map β.embedding = Z ∧
      β.embedding SylowModel.z = z
  exact ⟨(β.map_mark_left _).trans h.unipotent_image,
    (β.map_mark_left _).trans h.plane₁_image,
    (β.map_mark_right _).trans h.plane₂_image,
    (β.map_mark_left _).trans h.highestRoot_image, h.involution_image⟩

/-- Specialization to the actual Sylow subgroup in the source ambient group. -/
def markedSylowEquiv (P : Sylow 2 G)
    (h : β.SourceMarking (P : Subgroup G) S V₁ V₂ Z z) : SylowModel.T ≃* P :=
  β.markedEquiv h

end CompatibleLocalIsomorphisms
end CFSG.Quasithin.Chapter5.Section03ExceptionalSylowModel.MarkedRecognition
