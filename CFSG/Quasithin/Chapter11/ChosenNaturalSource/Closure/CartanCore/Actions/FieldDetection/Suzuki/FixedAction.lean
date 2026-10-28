module

public import Theory.SpecificGroups.Suzuki.BorelCoprimeFieldAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Suzuki.Coordinates
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Parameters
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Components
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.PointNormalizer.Kernel

/-!
# Constructing the field actor on a fixed Suzuki component

The original Cartan action preserves T∩I because this intersection is R₁∩I.
Transport its actual nonidentity quotient actor through the Suzuki marking.
Coprimality rules out a purely inner actor, while preservation of the root
subgroup places its inner factor in the Borel. The resulting field action
uses the original element of X, the original quotient map and the literal
Borel N_I(T∩I). Sylow conjugacy constructs the marking and the fixed-component
normalizer theorem supplies all coefficient lifts.

Only preceding point/Cartan geometry and the actual Suzuki quotient remain
explicit. The closure assembly owner discharges these earlier-source inputs.
Source: Aschbacher--Smith 11.5.6(3), printed pp.780--781.
-/

public noncomputable section
open Subgroup BenderSuzuki BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.SuzukiBorelFieldQuotient
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.Suzuki
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
variable {L V : Subgroup G} {D : ChosenModule T L V} {E : Geometry D}
variable {I : Subgroup G} {m : ℕ}

/-- Construct the field actor from the actual nonidentity coprime quotient action. -/
theorem OrbitCoordinates.exists_fieldAction_of_fixed (c : OrbitCoordinates T I m)
    (hm : 0 < m) (hTI : (T : Subgroup G) ≤ normalizer (I : Set G))
    (hc : Nat.Coprime (Nat.card E.X) (Nat.card I))
    (x : normalizer (I : Set G)) (hx : (x : G) ∈ E.X)
    (hxs : (x : G) ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G))
    (hne : coreQuotientAction I x ≠ 1) : Nonempty (FieldAction E c hm) := by
  have horbit : orbit T I = I := le_antisymm
    (conjugateSpanBy_le le_rfl hTI) (le_conjugateSpanBy I (T : Subgroup G))
  have hIO : I ≤ orbit T I := le_conjugateSpanBy I (T : Subgroup G)
  have hxb : (x : G) ∈ normalizer (borel T I : Set G) := by
    rw [borel, horbit]
    exact inf_normalizer_le_normalizer_inf
      ⟨x.property, (normalizer _).le_normalizer hxs⟩
  let α := MulAut.congr c.component (coreQuotientAction I x)
  let q := c.component.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have heq (i : I) : α (q i) = q (I.normalizerMonoidHom x i) := by
    change c.component (coreQuotientAction I x (c.component.symm
      (c.component (QuotientGroup.mk' (pCore 2 I) i)))) = _
    rw [c.component.symm_apply_apply, coreQuotientAction_apply_mk]
    rfl
  have hq : ((T : Subgroup G).subgroupOf I).map q = SuzukiRootSubgroup m := by
    have hmap : ((T : Subgroup G).subgroupOf I).map
        (inclusion hIO) =
        (T : Subgroup G).subgroupOf (orbit T I) := by
      ext a
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact hb
      · intro ha
        exact ⟨⟨a, horbit.le a.property⟩, ha, rfl⟩
    have he : q = c.quotient.comp (inclusion hIO) := by
      apply MonoidHom.ext
      intro i
      exact (c.restriction i).symm
    rw [he, ← map_map, hmap, c.sylow_image]
  have hroot : (SuzukiRootSubgroup m).map α.toMonoidHom = SuzukiRootSubgroup m := by
    rw [← hq]
    have he : α.toMonoidHom.comp q = q.comp (I.normalizerMonoidHom x).toMonoidHom := by
      apply MonoidHom.ext
      intro i
      exact heq i
    rw [map_map, he, ← map_map]
    congr 1
    ext i
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ((mem_normalizer_iff.mp hxs j).mp ⟨hj, j.property⟩).1
    · intro hi
      refine ⟨(I.normalizerMonoidHom x).symm i, ?_,
        (I.normalizerMonoidHom x).apply_symm_apply i⟩
      exact ((mem_normalizer_iff.mp ((normalizer _).inv_mem hxs) i).mp
        ⟨hi, i.property⟩).1
  have hcop : Nat.Coprime (orderOf α) (Nat.card (SuzukiMatrixGroup m)) := by
    apply hc.of_dvd
    · exact ((orderOf_map_dvd (MulAut.congr c.component).toMonoidHom _).trans
        (orderOf_map_dvd (coreQuotientAction I) x)).trans (by
          rw [← Subgroup.orderOf_coe x]
          exact E.X.orderOf_dvd_natCard hx)
    · exact card_dvd_of_surjective q
        (c.component.surjective.comp (QuotientGroup.mk'_surjective _))
  have hα : α ≠ 1 := by
    intro h
    apply hne
    exact (MulAut.congr c.component).injective (h.trans (map_one _).symm)
  obtain ⟨b, σ, hσ, ha⟩ := exists_borel_inner_field_of_coprime m hm α hα hcop hroot
  refine ⟨⟨⟨x, hxb⟩, hx, b, σ, hσ, ?_⟩⟩
  intro y
  apply Subtype.ext
  rw [borelActor_apply, ← ha]
  let i : I := ⟨y, horbit.le y.property.1⟩
  change c.quotient _ = α (c.quotient _)
  change c.quotient (inclusion hIO
      (I.normalizerMonoidHom x i)) =
    α (c.quotient (inclusion hIO i))
  have hy : c.quotient (inclusion hIO ((I.normalizerMonoidHom x) i)) =
      q ((I.normalizerMonoidHom x) i) := by
    exact c.restriction ((I.normalizerMonoidHom x) i)
  have hyi : c.quotient (inclusion hIO i) = q i := by
    exact c.restriction i
  rw [hy, hyi]
  exact (heq i).symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.Suzuki

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CartanActions.FieldDetection.Suzuki
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
variable {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- The literal Sylow intersection is R₁∩I, so the Cartan preserves it. -/
theorem cartan_normalizes_component_sylow
    (hp : E.point ≠ ⊥) (hT : (T : Subgroup G) ≤ E.G₁)
    (hX : E.X ≤ E.G₁) (ho : Odd (Nat.card E.X))
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I) :
    E.X ≤ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G) := by
  have hRT : E.R₁ ≤ (T : Subgroup G) := by
    simpa only [R₁, Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (E.L₁ ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have he : (T : Subgroup G) ⊓ I = E.R₁ ⊓ I := by
    apply le_antisymm
    · exact le_inf (fun _ h => E.sylow_inter_Y_le_R₁ hT ⟨h.1, hI.1 h.2⟩) inf_le_right
    · exact inf_le_inf_right I hRT
  rw [he]
  exact (le_inf hXR (E.cartan_normalizes_component hp hX ho hI)).trans
    inf_normalizer_le_normalizer_inf

/-- The fixed Suzuki branch has no field-action, coordinate or lifting premise. -/
theorem suzuki_borel_movement_of_fixed_quotient
    (hp : E.point ≠ ⊥) (hT : (T : Subgroup G) ≤ E.G₁)
    (hX : E.X ≤ E.G₁) (ho : Odd (Nat.card E.X))
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (eX : E.X ≃* (E.input.field.Carrierˣ × E.input.field.Carrierˣ))
    (hc : Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1))
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hTI : (T : Subgroup G) ≤ normalizer (I : Set G))
    {m : ℕ} (hm : 0 < m) (e : (I ⧸ pCore 2 I) ≃* SuzukiMatrixGroup m)
    (hmoved : ¬ ⁅I, E.X⁆ ≤ E.Y.pCoreIn 2) : E.BorelMovement := by
  obtain ⟨_, c, _⟩ := exists_orbitCoordinates_of_fixed hTI hm e
  obtain ⟨x, hx, hne⟩ := E.exists_component_quotient_mover hp hX ho hI hmoved
  obtain ⟨a⟩ := c.exists_fieldAction_of_fixed hm hTI
    (E.cartan_coprime_component_of_split_marking eX hc hI) x hx
    (E.cartan_normalizes_component_sylow hp hT hX ho hXR hI hx) hne
  exact a.borel_movement
    (conjugateSpanBy_le hI.1 (hT.trans E.G₁_normalizes_Y))
    (c.normalizerLifts_of_fixed hm hTI)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
