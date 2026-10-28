module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.PanelKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.CartanTransport

/-!
# Original endpoint kernels in the Ree source reconstruction

The entire original common Borel pulls back from the full marked quotient
Borel. Taking cores inside the corresponding endpoints then commutes with
the marking. This identifies both original panel kernels with Kᵢ on the
same quotient, and transports the injective source-root projection to the
original faithful endpoint quotient. The quotient equivalence retains its
representative formula and commutes with the two root projections.

Consequently [Rᵢ,H ∩ Kᵢ] = 1 is available with Kᵢ expressed in the original
source coordinates. The independent marking can be the original or the
geometric one. The generated-carrier specialization explicitly retains Q.q.
No local perfectness assumption is used. This is the kernel/centralization
step of Fong–Seitz I (3B), p.13, and the proof of (6H)(a), p.51, applied to
DGS's literal source quotient. It is not a proof of the remaining (6H) clauses.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)

/-- The core is formed in the original endpoint and uses its entire common Borel. -/
def originalPanelKernel : Subgroup (parabolic L S i) :=
  ((commonBorel L S).subgroupOf (parabolic L S i)).normalCore

instance : (originalPanelKernel (L := L) (S := S) i).Normal :=
  inferInstanceAs ((commonBorel L S).subgroupOf (parabolic L S i)).normalCore.Normal

include h in
theorem panelKernel_comap_endpoint :
    (panelKernel Q i).comap (endpoint Q e i).toMonoidHom =
      originalPanelKernel (L := L) (S := S) i := by
  have hb : (endpointBorel Q i).comap (endpoint Q e i).toMonoidHom =
      (commonBorel L S).subgroupOf (parabolic L S i) := endpoint_borel_comap Q e h i
  ext x
  change (∀ y : Endpoint Q i, y * endpoint Q e i x * y⁻¹ ∈ endpointBorel Q i) ↔
    ∀ y : parabolic L S i, y*x*y⁻¹ ∈ (commonBorel L S).subgroupOf (parabolic L S i)
  constructor
  · intro hx y
    have hz := hx (endpoint Q e i y)
    rw [← map_inv, ← map_mul, ← map_mul] at hz
    change y*x*y⁻¹ ∈ (endpointBorel Q i).comap (endpoint Q e i).toMonoidHom at hz
    rwa [hb] at hz
  · intro hx y
    obtain ⟨z,rfl⟩ := (endpoint Q e i).surjective y
    have hz := hx z
    rw [← hb] at hz
    change endpoint Q e i (z*x*z⁻¹) ∈ endpointBorel Q i at hz
    simpa only [map_mul, map_inv] using hz

include h in
/-- Both original kernels have exactly the source core image under the endpoint marking. -/
theorem originalPanelKernel_image :
    (originalPanelKernel (L := L) (S := S) i).map (endpointMap Q e i) =
      embeddedPanelKernel Q i := by
  rw [← panelKernel_comap_endpoint Q e h i]
  change (((panelKernel Q i).comap (endpoint Q e i).toMonoidHom).map
    ((Endpoint Q i).subtype.comp (endpoint Q e i).toMonoidHom)) = _
  rw [← map_map, map_comap_eq, (endpoint Q e i).toMonoidHom.range_eq_top_of_surjective
    (endpoint Q e i).surjective, top_inf_eq]
  rfl

/-- Lift the source root to the full original endpoint, including nonperfect rank-one factors. -/
def originalRootLift : simpleRoot Q split i →* parabolic L S i :=
  (endpoint Q e i).symm.toMonoidHom.comp (rootInEndpoint Q split i)

@[simp] theorem originalRootLift_image (r : simpleRoot Q split i) :
    endpointMap Q e i (originalRootLift Q e split i r) = (r : X ⧸ Q.D) := by
  change ((endpoint Q e i) ((endpoint Q e i).symm (rootInEndpoint Q split i r)) : X ⧸ Q.D) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- The lift projects through the actual original endpoint core, not a substituted two-core. -/
def originalRootProjection : simpleRoot Q split i →*
    (parabolic L S i ⧸ originalPanelKernel (L := L) (S := S) i) :=
  (QuotientGroup.mk' (originalPanelKernel (L := L) (S := S) i)).comp
    (originalRootLift Q e split i)

include h in
theorem originalRootProjection_injective :
    Function.Injective (originalRootProjection Q e split i) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro r hr
  have hk : originalRootLift Q e split i r ∈ originalPanelKernel (L := L) (S := S) i :=
    (QuotientGroup.eq_one_iff _).mp hr
  have hm := mem_map_of_mem (endpointMap Q e i) hk
  rw [originalPanelKernel_image Q e h i, originalRootLift_image] at hm
  exact Subtype.ext ((disjoint_def.mp (simpleRoot_disjoint_panelKernel Q split i)) r.property hm)

include h in
/-- The source (6H) centralization step with the kernel expressed in original coordinates. -/
theorem source_rankOne_commutator_cartanKernel :
    ⁅rankOneRootGroup Q split i,
      Q.tits.B ⊓ Q.tits.N ⊓
        (originalPanelKernel (L := L) (S := S) i).map (endpointMap Q e i)⁆ = ⊥ := by
  rw [originalPanelKernel_image Q e h i]
  exact rankOneRootGroup_commutator_cartanKernel Q split i

/-- The natural marked equivalence of the two actual faithful endpoint quotients. -/
def originalPanelQuotientEquiv :
    (parabolic L S i ⧸ originalPanelKernel (L := L) (S := S) i) ≃*
      (Endpoint Q i ⧸ panelKernel Q i) :=
  QuotientGroup.congr _ _ (endpoint Q e i) (by
    change (originalPanelKernel (L := L) (S := S) i).map (endpoint Q e i).toMonoidHom = panelKernel Q i
    rw [← panelKernel_comap_endpoint Q e h i, map_comap_eq,
      (endpoint Q e i).toMonoidHom.range_eq_top_of_surjective
        (endpoint Q e i).surjective, top_inf_eq])

@[simp] theorem originalPanelQuotientEquiv_mk (x : parabolic L S i) :
    originalPanelQuotientEquiv Q e h i
      (QuotientGroup.mk' (originalPanelKernel (L := L) (S := S) i) x) =
      QuotientGroup.mk' (panelKernel Q i) (endpoint Q e i x) :=
  QuotientGroup.congr_mk' _ _ _ _ _

/-- The lifted root and the source root have the same image in the faithful quotient. -/
theorem originalRootProjection_commutes (r : simpleRoot Q split i) :
    originalPanelQuotientEquiv Q e h i (originalRootProjection Q e split i r) =
      rootProjection Q split i r := by
  rw [originalRootProjection, MonoidHom.comp_apply, originalPanelQuotientEquiv_mk]
  change QuotientGroup.mk' (panelKernel Q i)
    ((endpoint Q e i) ((endpoint Q e i).symm (rootInEndpoint Q split i r))) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Specializing to the generated carrier keeps the same original quotient map. -/
theorem originalRootLift_quotient (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (i : Fin 2) (r : simpleRoot Q split i) :
    Q.q ⟨originalRootLift Q (originalMarkedIso Q) split i r,
      parabolic_le_generated i (originalRootLift Q (originalMarkedIso Q) split i r).property⟩ =
      (r : (generated L S) ⧸ Q.D) := by
  have he := originalRootLift_image Q (originalMarkedIso Q) split i r
  fin_cases i
  · exact (originalMarkedIso_left_apply Q _).symm.trans he
  · exact (originalMarkedIso_right_apply Q _).symm.trans he

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
