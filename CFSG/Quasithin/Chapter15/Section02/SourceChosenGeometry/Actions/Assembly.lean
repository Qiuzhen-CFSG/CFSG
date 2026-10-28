module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Cyclic
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Omega
/-!
# Original chosen-action and distinguished-plane conclusions

The four original action alternatives are reduced to the S₃, D₁₀, Sz(2)
and natural Omega rows. The cubic plane obstruction gives the odd-core
characterization of the common involution image; its actual moved space
defines the distinguished ambient plane. Both model branches supply the
literal centralizers, numerical alternatives and omega-center identity.

The input record contains only the preceding 15.2.1--12 conclusions.
Their final discharge belongs to qt-e-152-plane-geometry, with the
offender-plane and residual-geometry producers. All local model recognition,
action transport and numerical clauses are proved here.

Source: Aschbacher--Smith 15.2.13--14, printed pp.1111--1112,
combined manuscript (1 March 2004), refs/quasithin.pdf.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
open Cyclic
variable {G : Type*} [Group G] [Finite G]
structure ActionPreceding {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (H : Subgroup G) : Prop where
  alternatives : letI := h.prepared.elementary
    SmallActionAlternatives T M V h.prepared.normalized
  outside : H ∈ Chapter3.HStar (T : Subgroup G) M
  two_overgroups : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc}
  quotient : Nonempty ((H ⧸ pCore 2 H) ≃*
    RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))
  full : V = localModule T M
  nonempty : (sigmaOutside (T : Subgroup G) H).Nonempty
  planes : letI := h.prepared.elementary
    ∀ B ∈ sigmaOutside (T : Subgroup G) H,
      IsElementaryTwo (actor M V B h.prepared.normalized) ∧
      IsQuadratic (imageRepresentation M V h.prepared.normalized)
        (actor M V B h.prepared.normalized) ∧
      ⁅V,B⁆ ≤ V ∧ Nat.card (⁅V,B⁆ : Subgroup G) = 4 ∧
      H ≤ normalizer (⁅V,B⁆ : Subgroup G) ∧
      (T : Subgroup G) ≤ normalizer (⁅V,B⁆ : Subgroup G) ∧
      normalizer (⁅V,B⁆ : Subgroup G) ≤ Mc ∧
      ChosenGeometry.residual H ≤ centralizer (⁅V,B⁆ : Subgroup G)
  residual_eq : partnerSpan H Mc = threePrimeResidual Mc
  residual_centralizes : partnerSpan H Mc ≤ centralizer (centralInvolutions T : Set G)

private theorem ActionPreceding.cyclic {T : Sylow 2 G} {M Mc V H : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : ActionPreceding h H)
    (ho : letI := h.prepared.elementary
      ¬ SourceCases.Omega (imageRepresentation M V h.prepared.normalized)) :
    Cyclic.Preceding h H where
  alternatives := d.alternatives
  non_omega := ho
  outside := d.outside
  two_overgroups := d.two_overgroups
  quotient := d.quotient
  full := d.full
  nonempty := d.nonempty
  planes := d.planes
  residual_eq := d.residual_eq
  residual_centralizes := d.residual_centralizes

private theorem ActionPreceding.omega {T : Sylow 2 G} {M Mc V H : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : ActionPreceding h H)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized)) :
    Omega.Preceding h H where
  omega := ho
  outside := d.outside
  two_overgroups := d.two_overgroups
  quotient := d.quotient
  full := d.full
  nonempty := d.nonempty
  planes := d.planes
  residual_eq := d.residual_eq
  residual_centralizes := d.residual_centralizes

/-- Original 15.2.13(1), with actual isomorphisms, the original J-hat marking,
natural Omega coordinates, and its full odd-core commutator clause. -/
theorem ActionPreceding.restricted_models {T : Sylow 2 G} {M Mc V H : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : ActionPreceding h H) :
    letI := h.prepared.elementary
    Cyclic.RestrictedModels h ∨
      (SourceCases.Omega (imageRepresentation M V h.prepared.normalized) ∧
        ∀ B ∈ sigmaOutside (T : Subgroup G) H,
          pPrimeCore 2 (internalActionImage M V h.prepared.normalized) =
            ⁅pPrimeCore 2 (internalActionImage M V h.prepared.normalized),
              actor M V B h.prepared.normalized⁆) := by
  let := h.prepared.elementary
  by_cases ho : SourceCases.Omega (imageRepresentation M V h.prepared.normalized)
  · exact Or.inr ⟨ho,fun B hB => (d.omega ho).oddCore_commutator hB⟩
  · exact Or.inl (d.cyclic ho).restricted_models

/-- Original 15.2.13(2): the odd-core characterization determines a unique
order-two subgroup of the literal Sylow image, and all source offenders
have this image and its same ambient fixed/moved plane. -/
theorem ActionPreceding.common_plane {T : Sylow 2 G} {M Mc V H : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : ActionPreceding h H) :
    letI := h.prepared.elementary
    ∃ B₀ : Subgroup (internalActionImage M V h.prepared.normalized),
      B₀ ≤ actor M V (T : Subgroup G) h.prepared.normalized ∧ Nat.card B₀ = 2 ∧
      pPrimeCore 2 (internalActionImage M V h.prepared.normalized) =
        ⁅pPrimeCore 2 (internalActionImage M V h.prepared.normalized),B₀⁆ ∧
      (∀ A : Subgroup (internalActionImage M V h.prepared.normalized),
        A ≤ actor M V (T : Subgroup G) h.prepared.normalized → Nat.card A = 2 →
        pPrimeCore 2 (internalActionImage M V h.prepared.normalized) =
          ⁅pPrimeCore 2 (internalActionImage M V h.prepared.normalized),A⁆ → A = B₀) ∧
      ∀ B ∈ sigmaOutside (T : Subgroup G) H,
        actor M V B h.prepared.normalized = B₀ ∧
        V ⊓ centralizer (B : Set G) = ⁅V,B⁆ ∧
        ⁅V,B⁆ = ambientSpace V (subspaceCommutator
          (imageRepresentation M V h.prepared.normalized) ⊤ B₀) ∧
        ambientSpace V (subspaceCommutator
          (imageRepresentation M V h.prepared.normalized) ⊤ B₀) =
          ambientSpace V (fixedSpace (imageRepresentation M V h.prepared.normalized) B₀) ∧
        centralInvolutions T ≤ ⁅V,B⁆ := by
  let := h.prepared.elementary
  by_cases ho : SourceCases.Omega (imageRepresentation M V h.prepared.normalized)
  · exact (d.omega ho).common_plane
  · obtain ⟨B₀,hP,hc,hm,hu,hf⟩ := (d.cyclic ho).source_common_plane
    exact ⟨B₀,hP,hc,hm,fun A hA hAc _ => hu A hA hAc,hf⟩

/-- Original 15.2.14(1),(5), retaining literal ambient intersections. -/
theorem ActionPreceding.centralizers {T : Sylow 2 G} {M Mc V H : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : ActionPreceding h H) :
    Mc = centralizer (centralInvolutions T : Set G) ∧
      M ⊓ Mc = M ⊓ centralizer (centralInvolutions T : Set G) ∧
      M ⊓ centralizer (centralInvolutions T : Set G) =
        (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) := by
  let := h.prepared.elementary
  by_cases ho : SourceCases.Omega (imageRepresentation M V h.prepared.normalized)
  · exact (d.omega ho).source_centralizers
  · exact (d.cyclic ho).source_centralizers

/-- Original 15.2.14(2)--(4),(6). The index-two alternative retains the actual
Sz(2) isomorphism or natural Omega action, and the plane is elementary of order four. -/
theorem ActionPreceding.plane_geometry {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : ActionPreceding h H)
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) :
    letI := h.prepared.elementary
    ChosenPlaneGeometry h H ⁅V,B⁆ ∧ IsElementaryAbelian 2 (⁅V,B⁆ : Subgroup G) ∧
      centralInvolutions T ≤ ⁅V,B⁆ ∧
      ((planeCentralizer T ⁅V,B⁆ = (T : Subgroup G) ∧ centralInvolutions T = ⁅V,B⁆) ∨
        ((Nonempty (internalActionImage M V h.prepared.normalized ≃*
            BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
          SourceCases.Omega (imageRepresentation M V h.prepared.normalized)) ∧
          Nat.card (centralInvolutions T) = 2 ∧
          (planeCentralizer T ⁅V,B⁆).relIndex (T : Subgroup G) = 2)) ∧
      ⁅V,B⁆ = omegaOneCenterAmbient (planeCentralizer T ⁅V,B⁆) ∧
      ChapterE.moduleM (imageRepresentation M V h.prepared.normalized) = 2 ∧
      ChapterE.moduleA (imageRepresentation M V h.prepared.normalized) = 1 := by
  let := h.prepared.elementary
  have he : IsElementaryAbelian 2 (⁅V,B⁆ : Subgroup G) :=
    IsElementaryAbelian.of_injective (inclusion (d.planes B hB).2.2.1) (inclusion_injective _)
  by_cases ho : SourceCases.Omega (imageRepresentation M V h.prepared.normalized)
  · obtain ⟨hg,hz,hm,hc,hi,hw⟩ := (d.omega ho).source_plane_geometry hB
    exact ⟨hg,he,hz,Or.inr ⟨Or.inr hm,hc,hi⟩,hw,h.module_parameters⟩
  · obtain ⟨hg,hz,hcases,hw⟩ := (d.cyclic ho).source_plane_geometry hB
    refine ⟨hg,he,hz,?_,hw,h.module_parameters⟩
    exact hcases.elim Or.inl (fun hh => Or.inr ⟨Or.inl hh.1,hh.2⟩)


/-- The distinguished-plane consumer for qt-e-152-plane-geometry.
The plane is literally the moved subspace of the unique image B₀, embedded
back into G. This assembles every clause of original 15.2.13--14 from the
preceding source conclusions; no action-model or numerical callback remains. -/
theorem ActionPreceding.distinguished_plane
    {T : Sylow 2 G} {M Mc V H : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : ActionPreceding h H) :
    letI := h.prepared.elementary
    let D := internalActionImage M V h.prepared.normalized
    let ρ := imageRepresentation M V h.prepared.normalized
    ∃ B₀ : Subgroup D,
      B₀ ≤ actor M V (T : Subgroup G) h.prepared.normalized ∧ Nat.card B₀ = 2 ∧
      pPrimeCore 2 D = ⁅pPrimeCore 2 D,B₀⁆ ∧
      (∀ A : Subgroup D, A ≤ actor M V (T : Subgroup G) h.prepared.normalized →
        Nat.card A = 2 → pPrimeCore 2 D = ⁅pPrimeCore 2 D,A⁆ → A = B₀) ∧
      let ZS := ambientSpace V (subspaceCommutator ρ ⊤ B₀)
      ChosenPlaneGeometry h H ZS ∧ IsElementaryAbelian 2 ZS ∧
      (∀ B ∈ sigmaOutside (T : Subgroup G) H,
        actor M V B h.prepared.normalized = B₀ ∧
        V ⊓ centralizer (B : Set G) = ZS ∧ ⁅V,B⁆ = ZS) ∧
      ZS = ambientSpace V (fixedSpace ρ B₀) ∧
      (Cyclic.RestrictedModels h ∨
        (SourceCases.Omega ρ ∧ ∀ B ∈ sigmaOutside (T : Subgroup G) H,
          pPrimeCore 2 D = ⁅pPrimeCore 2 D,actor M V B h.prepared.normalized⁆)) ∧
      Mc = centralizer (centralInvolutions T : Set G) ∧
      centralInvolutions T ≤ ZS ∧
      ((planeCentralizer T ZS = (T : Subgroup G) ∧ centralInvolutions T = ZS) ∨
        ((Nonempty (D ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
          SourceCases.Omega ρ) ∧ Nat.card (centralInvolutions T) = 2 ∧
          (planeCentralizer T ZS).relIndex (T : Subgroup G) = 2)) ∧
      ZS = omegaOneCenterAmbient (planeCentralizer T ZS) ∧
      M ⊓ Mc = M ⊓ centralizer (centralInvolutions T : Set G) ∧
      M ⊓ centralizer (centralInvolutions T : Set G) =
        (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) ∧
      ChapterE.moduleM ρ = 2 ∧ ChapterE.moduleA ρ = 1 := by
  let := h.prepared.elementary
  obtain ⟨B₀,hP,hc,hm,hu,hplanes⟩ := d.common_plane
  obtain ⟨B,hB⟩ := d.nonempty
  have he := (hplanes B hB).2.2.1
  obtain ⟨hg,hel,hz,hcases,hw,hparams⟩ := d.plane_geometry hB
  rw [he] at hg hel hz hcases hw
  obtain ⟨hMc,hint,hprod⟩ := d.centralizers
  refine ⟨B₀,hP,hc,hm,hu,hg,hel,?_,(hplanes B hB).2.2.2.1,
    d.restricted_models,hMc,hz,hcases,hw,hint,hprod,hparams⟩
  intro C hC
  obtain ⟨hi,hf,hm,_,_⟩ := hplanes C hC
  exact ⟨hi,hf.trans hm,hm⟩

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
