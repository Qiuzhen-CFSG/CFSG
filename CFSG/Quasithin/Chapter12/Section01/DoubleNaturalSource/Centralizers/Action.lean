module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ModelGeometry
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Inner

/-!
# The literal doubled-orbit action and point stabilizers

The natural summand detects every element of L/O₂(L), so the component
conjugation kernel is exactly O₂(L). This embeds that quotient into the
actual normalizer action quotient. Both component and full-normalizer
point stabilizers are images of their original relative centralizers.
The component embedding retains the supplied natural-plus-dual coordinates.

These identifications supply the quotient and kernel conventions needed
when applying H.9 to the centralizers in 12.1.1 and 12.1.3--7.
Source: Aschbacher--Smith, combined manuscript, printed pp.787--792.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryNaturalDual BinaryLinear.OuterCyclic
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)

def componentConjugation : L →* MulAut (componentOrbit V (T : Subgroup G)) :=
  (normalizerAction T L V B.orbit_eq).comp (inclusion L.le_normalizer)

theorem coordinates_componentConjugation (l : L) (w : componentOrbit V (T : Subgroup G)) :
    B.coordinates (B.componentConjugation l w) = Multiplicative.ofAdd
      (naturalDualRepresentation (B.component (QuotientGroup.mk' (pCore 2 L) l))
        (B.coordinates w).toAdd) := by
  apply B.coordinates.symm.injective
  rw [B.coordinates.symm_apply_apply]
  apply Subtype.ext
  exact (B.component_action l w).symm

theorem componentConjugation_ker : B.componentConjugation.ker = pCore 2 L := by
  ext l
  constructor
  · intro hl
    have he : B.componentConjugation l = 1 := hl
    have hg : B.component (QuotientGroup.mk' (pCore 2 L) l) = 1 := by
      apply LinearEquiv.ext
      intro x
      let w := B.coordinates.symm (Multiplicative.ofAdd (x, 0))
      have hh := B.coordinates_componentConjugation l w
      rw [he, MulAut.one_apply] at hh
      have hh' := congrArg (fun y => y.toAdd.1) hh
      simpa only [w, B.coordinates.apply_symm_apply, naturalDualRepresentation_apply,
        toAdd_ofAdd, LinearEquiv.coe_one, id_eq] using hh'.symm
    have hq : QuotientGroup.mk' (pCore 2 L) l = 1 := B.component.injective (by simpa using hg)
    exact (QuotientGroup.eq_one_iff l).mp hq
  · intro hl
    have hq : QuotientGroup.mk' (pCore 2 L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    change B.componentConjugation l = 1
    apply MulEquiv.ext
    intro w
    apply B.coordinates.injective
    rw [B.coordinates_componentConjugation, hq, map_one, map_one]
    rfl

include B in
theorem component_centralizer_eq_twoCore :
    (centralizer (componentOrbit V (T : Subgroup G) : Set G)).subgroupOf L = pCore 2 L := by
  rw [← B.componentConjugation_ker, componentConjugation, ← MonoidHom.comap_ker,
    normalizerAction_ker]
  rfl

def componentProjection : L →* LinearGroup n :=
  B.component.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

theorem componentProjection_surjective : Function.Surjective B.componentProjection :=
  B.component.surjective.comp (QuotientGroup.mk'_surjective _)

theorem component_point_centralizer_map (w : componentOrbit V (T : Subgroup G)) :
    ((centralizer ({(w : G)} : Set G)).subgroupOf L).map B.componentProjection =
      VectorStabilizers.representationStabilizer naturalDualRepresentation (B.coordinates w).toAdd := by
  ext a
  constructor
  · rintro ⟨l, hl, rfl⟩
    change naturalDualRepresentation (B.componentProjection l) (B.coordinates w).toAdd =
      (B.coordinates w).toAdd
    have he : B.componentConjugation l w = w := by
      apply Subtype.ext
      change (l : G) * (w : G) * (l : G)⁻¹ = (w : G)
      have hc := mem_centralizer_singleton_iff.mp hl
      change (l : G) * (w : G) = (w : G) * (l : G) at hc
      rw [hc, mul_inv_cancel_right]
    exact congrArg Multiplicative.toAdd ((B.coordinates_componentConjugation l w).symm.trans
      (congrArg B.coordinates he))
  · intro ha
    obtain ⟨l, rfl⟩ := B.componentProjection_surjective a
    refine ⟨l, ?_, rfl⟩
    change (l : G) ∈ centralizer ({(w : G)} : Set G)
    apply mem_centralizer_singleton_iff.mpr
    have he : B.componentConjugation l w = w := by
      apply B.coordinates.injective
      rw [B.coordinates_componentConjugation]
      exact congrArg Multiplicative.ofAdd ha
    have he' := congrArg Subtype.val he
    change (l : G) * (w : G) * (l : G)⁻¹ = (w : G) at he'
    calc
      (l : G) * (w : G) = ((l : G) * (w : G) * (l : G)⁻¹) * (l : G) := by group
      _ = (w : G) * (l : G) := by rw [he']

abbrev ActionQuotient := normalizer (L : Set G) ⧸ (normalizerAction T L V B.orbit_eq).ker

def quotientAction : B.ActionQuotient →* MulAut (componentOrbit V (T : Subgroup G)) :=
  QuotientGroup.kerLift (normalizerAction T L V B.orbit_eq)

theorem quotientAction_injective : Function.Injective B.quotientAction :=
  QuotientGroup.kerLift_injective _

def actionProjection : normalizer (L : Set G) →* B.ActionQuotient :=
  QuotientGroup.mk' _

theorem actionProjection_surjective : Function.Surjective B.actionProjection :=
  QuotientGroup.mk'_surjective _

theorem quotientAction_projection_apply (m : normalizer (L : Set G))
    (w : componentOrbit V (T : Subgroup G)) :
    (B.quotientAction (B.actionProjection m) w : G) = (m : G) * (w : G) * (m : G)⁻¹ := rfl

def componentToActionQuotient : L →* B.ActionQuotient :=
  B.actionProjection.comp (inclusion L.le_normalizer)

theorem componentToActionQuotient_ker : B.componentToActionQuotient.ker = pCore 2 L := by
  rw [← B.componentConjugation_ker]
  ext l
  change B.actionProjection (inclusion L.le_normalizer l) = 1 ↔ B.componentConjugation l = 1
  rw [← B.quotientAction_injective.eq_iff, map_one]
  rfl

def componentEmbedding : (L ⧸ pCore 2 L) →* B.ActionQuotient :=
  QuotientGroup.lift _ B.componentToActionQuotient B.componentToActionQuotient_ker.ge

theorem componentEmbedding_injective : Function.Injective B.componentEmbedding := by
  exact (QuotientGroup.injective_lift_iff _ _ _).mpr B.componentToActionQuotient_ker.symm

variable [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

def quotientRepresentation :
    Representation (ZMod 2) B.ActionQuotient (Additive (componentOrbit V (T : Subgroup G))) :=
  Representation.elementaryRepresentation B.quotientAction

theorem quotient_stabilizer_comap (w : componentOrbit V (T : Subgroup G)) :
    (VectorStabilizers.representationStabilizer B.quotientRepresentation (Additive.ofMul w)).comap
      B.actionProjection = (centralizer ({(w : G)} : Set G)).subgroupOf (normalizer (L : Set G)) := by
  ext m
  change B.quotientAction (B.actionProjection m) w = w ↔ _
  rw [Subtype.ext_iff, B.quotientAction_projection_apply]
  change (m : G) * (w : G) * (m : G)⁻¹ = (w : G) ↔
    (m : G) ∈ centralizer ({(w : G)} : Set G)
  rw [mem_centralizer_singleton_iff]
  exact mul_inv_eq_iff_eq_mul

theorem quotient_point_centralizer_map (w : componentOrbit V (T : Subgroup G)) :
    ((centralizer ({(w : G)} : Set G)).subgroupOf (normalizer (L : Set G))).map
      B.actionProjection = VectorStabilizers.representationStabilizer B.quotientRepresentation
        (Additive.ofMul w) := by
  rw [← B.quotient_stabilizer_comap]
  exact map_comap_eq_self_of_surjective B.actionProjection_surjective _

theorem componentEmbedding_coordinates (q : L ⧸ pCore 2 L)
    (w : Additive (componentOrbit V (T : Subgroup G))) :
    B.linearCoordinates (B.quotientRepresentation (B.componentEmbedding q) w) =
      naturalDualRepresentation (B.component q) (B.linearCoordinates w) := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  exact congrArg Multiplicative.toAdd (B.coordinates_componentConjugation l w.toMul)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
