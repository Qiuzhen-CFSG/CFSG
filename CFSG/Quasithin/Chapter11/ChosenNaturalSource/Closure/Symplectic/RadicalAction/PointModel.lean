module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Setup
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction
public import Theory.GroupTheory.PCoreInRestriction


/-!
# The point-radical calculation on the chosen source quotient

The map below is literally the chosen symplectic group equivalence composed
with `L → L/O₂(L)`. Images retain the original subgroup restrictions to `L`.
Since the map has a two-group kernel, it preserves the embedded two-cores.
Given the preceding geometric identifications of the local and Cartan images
with a conjugate point local and point parabolic, the native calculation
proves the two strict chief factors, binary indecomposability, root identity,
and natural displacement and hyperplane-fixer conclusions on these images.
No radical-action conclusion is assumed in those identifications.

This supplies assertion (!) in Aschbacher--Smith 11.5.7 on the actual marked
quotient action (refs/quasithin.pdf, printed pp.782--783). The parent source
assembly retains the geometric identifications and transport from the chosen
quotient to the full original module, including its central attachment.
-/

@[expose] public noncomputable section

open Subgroup
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.PointModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D} (m : MarkedFlag E)

/-- The actual source quotient map, followed by its given symplectic marking. -/
def quotientMap : L →* Sp E.input.field.Carrier :=
  m.action.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

/-- The source bar image, retaining the restriction of the original subgroup to `L`. -/
def image (A : Subgroup G) : Subgroup (Sp E.input.field.Carrier) :=
  (A.subgroupOf L).map (quotientMap m)

/-- The marking adds no kernel to the original two-core quotient. -/
theorem quotientMap_ker : (quotientMap m).ker = pCore 2 L := by
  ext x
  change m.action.groupEquiv (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
  rw [← m.action.groupEquiv.map_one, m.action.groupEquiv.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

/-- A two-group kernel preserves the literal embedded two-core of each local subgroup. -/
theorem image_core (A : Subgroup G) (hA : A ≤ L) :
    image m (A.pCoreIn 2) = (image m A).pCoreIn 2 := by
  have hk : IsPGroup 2 (quotientMap m).ker := by
    rw [quotientMap_ker]
    exact pCore_isPGroup
  change ((A.pCoreIn 2).subgroupOf L).map (quotientMap m) = _
  rw [← pCoreIn_subgroupOf 2 A L hA]
  exact map_pCoreIn_of_ker_isPGroup (quotientMap m) hk _

/-- Original relative normalization descends through that same quotient map. -/
theorem image_normalizes (A B : Subgroup G)
    (hn : B ≤ normalizer (A : Set G)) :
    image m B ≤ normalizer (image m A : Set (Sp E.input.field.Carrier)) := by
  apply le_trans _ (le_normalizer_map (quotientMap m))
  apply map_mono
  exact (comap_mono hn).trans (A.le_normalizer_comap L.subtype)

/-- The intrinsic center of the original local image is the conjugate literal long root. -/
theorem center_identification (g : Sp E.input.field.Carrier)
    (hlocal : image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom) :
    (center (image m E.L₁)).map (image m E.L₁).subtype =
      (RootSubgroup.group 0).map (MulAut.conj g).toMonoidHom := by
  rw [hlocal, ← PointRadicalAction.map_embedded_center _ _ (MulAut.conj g).injective,
    PointRadicalAction.center_eq_root E.input.field.card_eq E.input.nonbinary]

/-- Both chief factors are nontrivial on the original source quotient images. -/
theorem chief_series (g : Sp E.input.field.Carrier)
    (hlocal : image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom) :
    ⊥ < (center (image m E.L₁)).map (image m E.L₁).subtype ∧
    (center (image m E.L₁)).map (image m E.L₁).subtype <
      image m (E.L₁.pCoreIn 2) := by
  rw [image_core m E.L₁ E.L₁_le, hlocal,
    ← PointRadicalAction.map_embedded_center _ _ (MulAut.conj g).injective]
  exact PointRadicalAction.conjugate_chief_series E.input.field.card_eq E.input.nonbinary g

/-- The native lattice acts on arbitrary binary subgroups of the original
quotient image; there is no defining-field subspace hypothesis. -/
theorem image_invariant_lattice (g : Sp E.input.field.Carrier)
    (hlocal : image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom)
    (hcartan : image m (E.L₁ ⊔ E.X) = pointParabolic.map (MulAut.conj g).toMonoidHom)
    (A : Subgroup (Sp E.input.field.Carrier))
    (hA : A ≤ image m (E.L₁.pCoreIn 2))
    (hn : image m (E.L₁ ⊔ E.X) ≤ normalizer (A : Set (Sp E.input.field.Carrier))) :
    A = ⊥ ∨ A = (center (image m E.L₁)).map (image m E.L₁).subtype ∨
      A = image m (E.L₁.pCoreIn 2) := by
  rw [image_core m E.L₁ E.L₁_le, hlocal] at hA ⊢
  rw [hcartan] at hn
  rw [← PointRadicalAction.map_embedded_center _ _ (MulAut.conj g).injective]
  exact PointRadicalAction.invariant_lattice_conjugate
    E.input.field.card_eq E.input.nonbinary g A hA hn

/-- Application to original subgroups normalized by the original local--Cartan join. -/
theorem invariant_lattice (g : Sp E.input.field.Carrier)
    (hlocal : image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom)
    (hcartan : image m (E.L₁ ⊔ E.X) = pointParabolic.map (MulAut.conj g).toMonoidHom)
    (A : Subgroup G) (hA : A ≤ E.L₁.pCoreIn 2)
    (hn : E.L₁ ⊔ E.X ≤ normalizer (A : Set G)) :
    image m A = ⊥ ∨
    image m A = (center (image m E.L₁)).map (image m E.L₁).subtype ∨
    image m A = image m (E.L₁.pCoreIn 2) := by
  have ha : image m A ≤ (image m E.L₁).pCoreIn 2 := by
    rw [← image_core m E.L₁ E.L₁_le]
    exact map_mono (comap_mono hA)
  have hp := image_normalizes m A (E.L₁ ⊔ E.X) hn
  rw [hcartan] at hp
  rw [hlocal] at ha
  have hr := PointRadicalAction.invariant_lattice_conjugate
    E.input.field.card_eq E.input.nonbinary g (image m A) ha hp
  rw [image_core m E.L₁ E.L₁_le, hlocal,
    ← PointRadicalAction.map_embedded_center _ _ (MulAut.conj g).injective]
  exact hr

/-- The original radical image is a binary vector group. -/
theorem core_elementaryAbelian (g : Sp E.input.field.Carrier)
    (hlocal : image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom) :
    IsElementaryAbelian 2 (image m (E.L₁.pCoreIn 2)) := by
  rw [image_core m E.L₁ E.L₁_le, hlocal,
    ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
  let := PointRadicalAction.core_elementaryAbelian E.input.field.card_eq E.input.nonbinary
  exact IsElementaryAbelian.map (MulAut.conj g).toMonoidHom

/-- The center of the original local image moves precisely the conjugate point. -/
theorem center_displacement (g : Sp E.input.field.Carrier)
    (hlocal : image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom) :
    displacementSpace ((center (image m E.L₁)).map (image m E.L₁).subtype) =
      (point E.input.field.Carrier).map (toLinear g).toLinearMap := by
  rw [hlocal, ← PointRadicalAction.map_embedded_center _ _ (MulAut.conj g).injective]
  exact PointRadicalAction.conjugate_center_displacement
    E.input.field.card_eq E.input.nonbinary g

/-- The original two-core image moves precisely the conjugate perpendicular hyperplane. -/
theorem core_displacement (g : Sp E.input.field.Carrier)
    (hlocal : image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom) :
    displacementSpace (image m (E.L₁.pCoreIn 2)) =
      ((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap := by
  rw [image_core m E.L₁ E.L₁_le, hlocal]
  exact PointRadicalAction.conjugate_core_displacement
    E.input.field.card_eq E.input.nonbinary g

/-- The full natural hyperplane fixer is the intrinsic center of the original local image. -/
theorem hyperplane_fixer (g : Sp E.input.field.Carrier)
    (hlocal : image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom) :
    fixingSubgroup (Sp E.input.field.Carrier)
      (((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap : Set (Vector E.input.field.Carrier)) =
      (center (image m E.L₁)).map (image m E.L₁).subtype := by
  rw [hlocal, ← PointRadicalAction.map_embedded_center _ _ (MulAut.conj g).injective]
  exact PointRadicalAction.conjugate_hyperplane_fixer
    E.input.field.card_eq E.input.nonbinary g

/-- Both strict chief-series terms are invariant under the original Cartan image. -/
theorem normalizes_center_and_core (g : Sp E.input.field.Carrier)
    (hlocal : image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom)
    (hcartan : image m (E.L₁ ⊔ E.X) = pointParabolic.map (MulAut.conj g).toMonoidHom) :
    image m (E.L₁ ⊔ E.X) ≤ normalizer
      ((center (image m E.L₁)).map (image m E.L₁).subtype : Set (Sp E.input.field.Carrier)) ∧
    image m (E.L₁ ⊔ E.X) ≤ normalizer
      (image m (E.L₁.pCoreIn 2) : Set (Sp E.input.field.Carrier)) := by
  rw [image_core m E.L₁ E.L₁_le, hlocal, hcartan,
    ← PointRadicalAction.map_embedded_center _ _ (MulAut.conj g).injective,
    ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
  have h := PointRadicalAction.normalizes_center_and_core
    E.input.field.card_eq E.input.nonbinary
  exact ⟨(map_mono h.1).trans (le_normalizer_map _),
    (map_mono h.2).trans (le_normalizer_map _)⟩

/-- There are no nontrivial invariant binary summands of the original radical image. -/
theorem indecomposable (g : Sp E.input.field.Carrier)
    (hlocal : image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom)
    (hcartan : image m (E.L₁ ⊔ E.X) = pointParabolic.map (MulAut.conj g).toMonoidHom)
    (A B : Subgroup (Sp E.input.field.Carrier))
    (hA : image m (E.L₁ ⊔ E.X) ≤ normalizer (A : Set (Sp E.input.field.Carrier)))
    (hB : image m (E.L₁ ⊔ E.X) ≤ normalizer (B : Set (Sp E.input.field.Carrier)))
    (hjoin : A ⊔ B = image m (E.L₁.pCoreIn 2)) (hmeet : A ⊓ B = ⊥) :
    A = ⊥ ∨ B = ⊥ := by
  by_cases ha : A = ⊥
  · exact Or.inl ha
  by_cases hb : B = ⊥
  · exact Or.inr hb
  have hchain := chief_series m g hlocal
  have hc (C : Subgroup (Sp E.input.field.Carrier))
      (hC : C ≤ image m (E.L₁.pCoreIn 2))
      (hn : image m (E.L₁ ⊔ E.X) ≤ normalizer (C : Set (Sp E.input.field.Carrier)))
      (hne : C ≠ ⊥) : (center (image m E.L₁)).map (image m E.L₁).subtype ≤ C := by
    rcases image_invariant_lattice m g hlocal hcartan C hC hn with h | h | h
    · exact (hne h).elim
    · exact h.ge
    · exact hchain.2.le.trans h.ge
  have hle := le_inf (hc A (le_sup_left.trans hjoin.le) hA ha)
    (hc B (le_sup_right.trans hjoin.le) hB hb)
  rw [hmeet] at hle
  exact (hchain.1.not_ge hle).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.PointModel
