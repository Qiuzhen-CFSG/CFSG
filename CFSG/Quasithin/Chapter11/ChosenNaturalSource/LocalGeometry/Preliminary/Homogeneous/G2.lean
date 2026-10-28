module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Homogeneous.Twists
public import Theory.Representation.G2NaturalSemilinear
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage

/-!
# The full chosen-natural G₂ quotient is homogeneous

Every automorphism of G₂ over the supplied nonbinary field is inner-field.
Its actual natural operator and coefficient transport give a binary intertwiner.
Transporting through the original L/O₂(L) marking identifies all normalizer
twists of the chosen central quotient. The generating-seed argument then proves
homogeneity on the literal V_M/C_{V_M}(L), without assuming V_M = V.

Source: Aschbacher--Smith, 11.0.3(2), printed p.760. The model and its
inner-field theorem retain the ATLAS attribution in the imported modules.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
private theorem g2_natural_twist (F : Type*) [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] (hq : 2 < Nat.card F) (a : MulAut (Atlas.G2.Model F)) :
    ∃ e : Atlas.G2.Natural.Space F ≃ₗ[ZMod 2] Atlas.G2.Natural.Space F,
      ∀ g v, e (Atlas.G2.Natural.action F g v) = Atlas.G2.Natural.action F (a g) (e v) := by
  obtain ⟨g, φ, ha⟩ := Atlas.G2.LieAutomorphismExtensions.exists_inner_field hq a
  let ρ := restrictScalars (k := ZMod 2) (Atlas.G2.Natural.action F)
  let c := Atlas.G2.Natural.BinarySemilinear.fieldEquivalence F φ
  let b : Atlas.G2.Natural.Space F ≃ₗ[ZMod 2] Atlas.G2.Natural.Space F :=
    LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)
  refine ⟨c.trans b, ?_⟩
  intro x v
  change Atlas.G2.Natural.action F g (c (Atlas.G2.Natural.action F x v)) =
    Atlas.G2.Natural.action F (a x) (Atlas.G2.Natural.action F g (c v))
  rw [Atlas.G2.Natural.BinarySemilinear.fieldEquivalence_action, ha]
  change Atlas.G2.Natural.action F g
      (Atlas.G2.Natural.action F (Atlas.G2.fieldEquiv φ x) (c v)) =
    Atlas.G2.Natural.action F (g * Atlas.G2.fieldEquiv φ x * g⁻¹)
      (Atlas.G2.Natural.action F g (c v))
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

/-- Every automorphism twist of the chosen G₂ central quotient has the
same binary module type, with the original full quotient marking. -/
theorem chosen_g2_central_twist
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) (a : MulAut L) :
    ∃ e : D.chosenCentralQuotient ≃ₗ[ZMod 2] D.chosenCentralQuotient,
      ∀ l v, e (D.chosenCentralAction l v) = D.chosenCentralAction (a l) (e v) := by
  let aQ := QuotientGroup.congr (pCore 2 L) (pCore 2 L) a (pCore_map_iso 2 a)
  let α := (MulAut.congr m.groupEquiv) aQ
  have hq : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) S.nonbinary
  obtain ⟨b, hb⟩ := g2_natural_twist S.field.Carrier hq α
  let e := m.linearEquiv.trans (b.trans m.linearEquiv.symm)
  refine ⟨e, ?_⟩
  intro l v
  apply m.linearEquiv.injective
  change m.linearEquiv (m.linearEquiv.symm (b (m.linearEquiv (D.chosenCentralAction l v)))) = _
  rw [m.linearEquiv.apply_symm_apply]
  change b (m.linearEquiv (D.centralQuotientAction (QuotientGroup.mk' (pCore 2 L) l) v)) = _
  rw [m.intertwines]
  change b (Atlas.G2.Natural.action S.field.Carrier _ (m.linearEquiv v)) = _
  rw [hb]
  change _ = m.linearEquiv (D.centralQuotientAction (QuotientGroup.mk' (pCore 2 L) (a l)) (e v))
  rw [m.intertwines]
  have he : m.linearEquiv (e v) = b (m.linearEquiv v) := m.linearEquiv.apply_symm_apply _
  rw [he]
  congr 2
  change m.groupEquiv (aQ (m.groupEquiv.symm (m.groupEquiv _))) = _
  rw [m.groupEquiv.symm_apply_apply]
  rfl

section G2
variable (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Source 11.0.3(2) in the G₂ row: the literal full quotient is a single
isotypic component for the unchanged L-action. Its conjugation formula fixes
both the group quotient and the action conventions. -/
theorem fullModule_g2_homogeneous
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) :
    letI := fullModule_elementary D S
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    ∃ σ : Representation (ZMod 2) M
        (Additive (U ⧸ (centralizer (L : Set G)).subgroupOf U)),
      (∃ I : Subrepresentation (σ.comp (L.subgroupOf M).subtype),
        IsIrreducible I.toRepresentation ∧ homogeneousPart I ⊤ = ⊤) ∧
      (∀ (g : M) (v : U),
        σ g (Additive.ofMul (QuotientGroup.mk'
          ((centralizer (L : Set G)).subgroupOf U) v)) =
          Additive.ofMul (QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf U)
            ⟨(g : G) * (v : G) * (g : G)⁻¹,
              (mem_normalizer_iff.mp (le_normalizer_componentOrbit V M g.property) v).mp
                v.property⟩)) := by
  apply fullModule_homogeneous_of_normalizer_twists D S
  intro g
  exact chosen_g2_central_twist D S m (L.normalizerMonoidHom g)
end G2

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
