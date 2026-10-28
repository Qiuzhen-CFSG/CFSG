module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Assembly
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.PlaneNormalizer
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness

/-!
# Assembly of the original chosen plane

The original offender theorem constructs every input to the residual-plane
geometry. In particular full support is proved, not assumed. The resulting
plane has the source normalizer, centralizer, numerical and omega-center
properties without the remaining prime-complement residual identity.

Only 15.2.5 (the two maximal overgroups) and 15.2.8 (the actual wreath
quotients) remain explicit in this construction; SmallWholeAction proves
15.2.1 from ChosenSmallSource. Their producer is qt-e-152-small-parabolic
and their final discharge belongs to qt-e-152-chosen-action-contradiction.

The final conditional assembly also retains exactly 15.2.12(2) and the
identity in 15.2.12(4), on the literal embedded K and its Mc-orbit span.
These remain with qt-e-152-residual-geometry. No root or Held exclusion is
inferred from the earlier geometry. This module supplies the actual action
consumer of that identity and keeps all the short structural alternatives
available for 15.2.15, 15.2.21 and 15.2.27.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Notation 15.2.9 and Lemmas 15.2.10--14, printed pp.1110--1112,
refs/quasithin.pdf.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
open CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Cyclic
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
open ChosenGeometry ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- Every original outside offender supplies the literal residual input.
The action alternatives and all local offender premises are discharged. -/
theorem ChosenSmallSource.residualInput_of_preceding
    {T : Sylow 2 G} {M Mc V H B : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc})
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) : ResidualInput h H B := by
  obtain ⟨_,_,hc,_,hn,hz⟩ := (h.offender_plane h.action_alternatives hH he).2 B hB
  exact ⟨hH,he,htwo,hB,hc,hn,hz⟩

end CFSG.Quasithin.Chapter15.Section02

namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterD ChapterD.UniqueFactor Cyclic
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}

/-- The embedded residual centralizes the actual commutator plane. -/
theorem ResidualInput.residual_centralizes_plane
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    residual H ≤ centralizer (⁅V,B⁆ : Subgroup G) := by
  intro k hk z hz
  obtain ⟨z',hz',rfl⟩ := d.plane_central hz
  exact (congrArg Subtype.val ((mem_center_iff.mp hz') ⟨k,hk⟩)).symm

/-- The index-two row retains the actual Sz(2) or natural Omega model,
without assuming Kc = O^{3′}(Mc). The other models have full Sylow image
of order two and therefore give the equal-plane row. -/
theorem ResidualInput.source_plane_alternatives
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    letI := h.prepared.elementary
    (planeCentralizer T ⁅V,B⁆ = (T : Subgroup G) ∧ centralInvolutions T = ⁅V,B⁆) ∨
      ((Nonempty (internalActionImage M V h.prepared.normalized ≃*
          BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
        SourceCases.Omega (imageRepresentation M V h.prepared.normalized)) ∧
        Nat.card (centralInvolutions T) = 2 ∧
        (planeCentralizer T ⁅V,B⁆).relIndex (T : Subgroup G) = 2) := by
  let := h.prepared.elementary
  rcases d.plane_alternatives with he | ⟨hc,hi⟩
  · exact Or.inl he
  refine Or.inr ⟨?_,hc,hi⟩
  rcases d.restricted_models_or_omega with hm | ho
  · have hsmall : ¬ (Nonempty (internalActionImage M V h.prepared.normalized ≃*
        Equiv.Perm (Fin 3)) ∨ Nonempty (internalActionImage M V h.prepared.normalized ≃*
        DihedralGroup 5)) := by
      intro hs
      obtain ⟨hA,hq⟩ := d.actor_quadratic_of_plane
      have hle : actor M V B h.prepared.normalized ≤
          actor M V (T : Subgroup G) h.prepared.normalized :=
        map_mono (comap_mono d.offender_le_sylow)
      have he := equal_plane_of_full_sylow_image h d.full d.offender_le_sylow hA hq
        (eq_of_le_of_card_ge hle ((sylow_image_card_two h hs).le.trans
          (quadratic_fixed_eq_moved h _ hA hq).1.ge))
      rw [he.1,relIndex_self] at hi
      contradiction
    rcases hm with ⟨_,hs⟩ | ⟨_,hd | hz⟩
    · exact (hsmall (Or.inl hs)).elim
    · exact (hsmall (Or.inr hd)).elim
    · exact Or.inl hz
  · exact Or.inr ho

/-- The constructed source geometry independent of the two outstanding
residual clauses. The plane is an actual original offender commutator. -/
structure ConstructedPlane {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (H ZS : Subgroup G) : Prop where
  geometry : ChosenPlaneGeometry h H ZS
  original : ∃ B ∈ sigmaOutside (T : Subgroup G) H, ZS = ⁅V,B⁆
  elementary : IsElementaryAbelian 2 ZS
  residual_mem_Xi : residual H ∈ Chapter1.Xi G (T : Subgroup G)
  unique_overgroup : ∀ N, IsMaximalTwoLocal N → H ≤ N → N = Mc
  residual_center : ZS ≤ (center (residual H)).map (residual H).subtype
  partner_centralizes : partnerSpan H Mc ≤ centralizer (centralInvolutions T : Set G)
  models : letI := h.prepared.elementary
    RestrictedModels h ∨ SourceCases.Omega (imageRepresentation M V h.prepared.normalized)
  partner_eq : Mc = centralizer (centralInvolutions T : Set G)
  seed_le : centralInvolutions T ≤ ZS
  alternatives : letI := h.prepared.elementary
    (planeCentralizer T ZS = (T : Subgroup G) ∧ centralInvolutions T = ZS) ∨
      ((Nonempty (internalActionImage M V h.prepared.normalized ≃*
          BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
        SourceCases.Omega (imageRepresentation M V h.prepared.normalized)) ∧
        Nat.card (centralInvolutions T) = 2 ∧
        (planeCentralizer T ZS).relIndex (T : Subgroup G) = 2)
  omega_center : ZS = omegaOneCenterAmbient (planeCentralizer T ZS)
  intersection : M ⊓ Mc = M ⊓ centralizer (centralInvolutions T : Set G)
  centralizer_product : M ⊓ centralizer (centralInvolutions T : Set G) =
    (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G)
  parameters : letI := h.prepared.elementary
    ChapterE.moduleM (imageRepresentation M V h.prepared.normalized) = 2 ∧
      ChapterE.moduleA (imageRepresentation M V h.prepared.normalized) = 1

/-- Assembly of the full-support and geometric deductions, on the original
offender plane and literal S = T ∩ C_G([V,B]). -/
theorem ResidualInput.constructed_plane
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    ConstructedPlane h H ⁅V,B⁆ where
  geometry := d.geometry
  original := ⟨B,d.offender,rfl⟩
  elementary := by
    let := h.prepared.elementary
    exact IsElementaryAbelian.of_injective (inclusion d.plane_le) (inclusion_injective _)
  residual_mem_Xi := d.mem_Xi
  unique_overgroup := source_chosen_HStar_unique d.outside d.two_overgroups
  residual_center := d.plane_central
  partner_centralizes := d.centralizes
  models := d.restricted_models_or_omega
  partner_eq := d.partner_eq_centralizer
  seed_le := d.seed_le_plane
  alternatives := d.source_plane_alternatives
  omega_center := d.plane_eq_omegaCenter
  intersection := by rw [d.partner_eq_centralizer]
  centralizer_product := h.seed_centralizer_eq d.full
  parameters := h.module_parameters

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry

namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
open ChosenGeometry ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- Construct H and an original offender B, proving full support and the
source plane geometry. Only the preceding 15.2.5 and 15.2.8 remain explicit. -/
theorem ChosenSmallSource.exists_constructed_plane
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc})
    (hquotient : ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((H ⧸ pCore 2 H) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    ∃ H B, B ∈ sigmaOutside (T : Subgroup G) H ∧ ConstructedPlane h H ⁅V,B⁆ := by
  obtain ⟨H,hH,_,he⟩ := h.exists_wreath_local hquotient
  obtain ⟨B,d⟩ := h.exists_residualInput_of_preceding h.action_alternatives hH he htwo
  exact ⟨H,B,d.offender,d.constructed_plane⟩

/-- The actual consumer of the missing 15.2.12(4) identity. All plane,
offender, centralization and full-support inputs to 15.2.13 are discharged.
The equality remains with qt-e-152-residual-geometry. -/
theorem ChosenSmallSource.actionPreceding_of_residual
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc})
    (hres : partnerSpan H Mc = threePrimeResidual Mc) : ActionPreceding h H := by
  let := h.prepared.elementary
  obtain ⟨B,d⟩ := h.exists_residualInput_of_preceding h.action_alternatives hH he htwo
  refine ⟨h.action_alternatives,hH,htwo,he,d.full,
    (h.offender_plane h.action_alternatives hH he).1,?_,hres,d.centralizes⟩
  intro C hC
  have e := h.residualInput_of_preceding hH he htwo hC
  exact ⟨e.actor_quadratic_of_plane.1,e.actor_quadratic_of_plane.2,
    e.plane_le,e.plane_card,e.plane_normalized,hH.1.1.2.trans e.plane_normalized,
    e.plane_normalizer,e.residual_centralizes_plane⟩

end CFSG.Quasithin.Chapter15.Section02

namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- All requested 15.2.9--14 conclusions on the distinguished plane.
This is an output: its constructor below proves the common image and plane
clauses, while retaining the two explicitly named earlier residual clauses. -/
structure DistinguishedPlane {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (H ZS : Subgroup G)
    : Prop extends ConstructedPlane h H ZS where
  residual_eq : partnerSpan H Mc = threePrimeResidual Mc
  structural : StructuralAlternatives T H Mc
  restricted_action : letI := h.prepared.elementary
    Cyclic.RestrictedModels h ∨
      (SourceCases.Omega (imageRepresentation M V h.prepared.normalized) ∧
        ∀ B ∈ sigmaOutside (T : Subgroup G) H,
          pPrimeCore 2 (internalActionImage M V h.prepared.normalized) =
            ⁅pPrimeCore 2 (internalActionImage M V h.prepared.normalized),
              actor M V B h.prepared.normalized⁆)
  common_image : letI := h.prepared.elementary
    let D := internalActionImage M V h.prepared.normalized
    let ρ := imageRepresentation M V h.prepared.normalized
    ∃ B₀ : Subgroup D,
      B₀ ≤ actor M V (T : Subgroup G) h.prepared.normalized ∧ Nat.card B₀ = 2 ∧
      pPrimeCore 2 D = ⁅pPrimeCore 2 D,B₀⁆ ∧
      (∀ A : Subgroup D, A ≤ actor M V (T : Subgroup G) h.prepared.normalized →
        Nat.card A = 2 → pPrimeCore 2 D = ⁅pPrimeCore 2 D,A⁆ → A = B₀) ∧
      ZS = ambientSpace V (subspaceCommutator ρ ⊤ B₀) ∧
      ZS = ambientSpace V (fixedSpace ρ B₀) ∧
      ∀ B ∈ sigmaOutside (T : Subgroup G) H,
        actor M V B h.prepared.normalized = B₀ ∧
        V ⊓ centralizer (B : Set G) = ZS ∧ ⁅V,B⁆ = ZS

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry

namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

/-- Conditional final assembly of the requested distinguished source plane.
The residual hypothesis is exactly the outstanding output of
qt-e-152-residual-geometry, on every actual ResidualInput. It is neither
replaced by a model tag nor claimed discharged here. The two preceding
clauses are produced by qt-e-152-small-parabolic; the final Section 15.2
owner qt-e-152-chosen-action-contradiction discharges them all. -/
theorem ChosenSmallSource.distinguished_plane_of_residuals
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc})
    (hquotient : ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((H ⧸ pCore 2 H) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hresidual : ∀ H B, ResidualInput h H B →
      partnerSpan H Mc = threePrimeResidual Mc ∧ StructuralAlternatives T H Mc) :
    ∃ H ZS, DistinguishedPlane h H ZS := by
  let := h.prepared.elementary
  obtain ⟨H,hH,_,he⟩ := h.exists_wreath_local hquotient
  obtain ⟨B,d⟩ := h.exists_residualInput_of_preceding h.action_alternatives hH he htwo
  obtain ⟨hr,hs⟩ := hresidual H B d
  have a := h.actionPreceding_of_residual hH he htwo hr
  obtain ⟨B₀,hP,hc,hm,hu,_,_,hall,hfix,hmodels,_⟩ := a.distinguished_plane
  have hg := d.constructed_plane
  rw [(hall B d.offender).2.2] at hg
  refine ⟨H,ambientSpace V (subspaceCommutator
    (imageRepresentation M V h.prepared.normalized) ⊤ B₀),?_⟩
  exact { toConstructedPlane := hg
          residual_eq := hr
          structural := hs
          restricted_action := hmodels
          common_image := ⟨B₀,hP,hc,hm,hu,rfl,hfix,hall⟩ }

end CFSG.Quasithin.Chapter15.Section02

namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The literal 15.2.15 consumer of the assembled plane. The residual maps
agree by the proved O^{3′} convention bridge, and the two centralizer
equalities give the exact intersection required by uniqueness. -/
theorem DistinguishedPlane.uniqueness_preceding
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : DistinguishedPlane h H ZS)
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc}) :
    PlaneUniquenessPreceding h H ZS where
  geometry := d.geometry
  two_maximals := htwo
  partner_eq := d.partner_eq
  seed_le := d.seed_le
  center_cases := by
    rcases d.alternatives with he | he
    · exact Or.inl he.2
    · exact Or.inr he.2
  omega_center := d.omega_center
  residual_centralizes := by
    intro k hk z hz
    obtain ⟨z',hz',rfl⟩ := d.residual_center hz
    exact (congrArg Subtype.val ((mem_center_iff.mp hz') ⟨k,hk⟩)).symm
  orbit_residual := d.residual_eq.trans (threePrimeResidual_eq Mc)
  intersection := d.intersection.trans d.centralizer_product

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry

