module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Cyclic.Transport
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Cyclic.CommonImage
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Cyclic.Maximality
/-!
# Conditional cyclic source geometry

The preceding-input record retains the original chosen action, HStar member,
wreath quotient, full support, sigma family, planes and embedded residuals.
It contains no restricted classification, common image or fixed/moved equality.
The theorems construct the unique common order-two image, transport its fixed
and moved plane back to G, prove seed containment, and establish the equal-plane
alternative in the S₃ and D₁₀ models. The same inputs discharge the ambient
cubic obstruction needed by the remaining model recognition.

Restricted-model recognition, the odd-core commutator characterization and
the Sz(2) numerical alternative remain separate obligations. These conditional
results do not assert completion of the original source theorem.

Source: Aschbacher--Smith 15.2.13--14, printed pp.1111--1112,
combined manuscript of 1 March 2004, refs/quasithin.pdf.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Cyclic
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The exact preceding source conclusions retained by the non-Omega branch.
No restricted model, common image, fixed/moved equality or numerical plane
alternative is assumed. K is the embedded O²(H), Kc its literal Mc-orbit span. -/
structure Preceding {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (H : Subgroup G) : Prop where
  alternatives : letI := h.prepared.elementary
    SmallActionAlternatives T M V h.prepared.normalized
  non_omega : letI := h.prepared.elementary
    ¬ SourceCases.Omega (imageRepresentation M V h.prepared.normalized)
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

/-- The sigma actors lie in the fixed ambient Sylow subgroup because they lie
in the two-core of H. -/
theorem Preceding.actor_le_sylow {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) : B ≤ (T : Subgroup G) := by
  obtain ⟨A,hA,hAT,rfl⟩ := exists_offender_of_mem_sigmaOutside hB
  have hh := map_mono (f := H.subtype)
    (pCore_isPGroup.le_sylow_of_normal (T.subtype d.outside.1.1.2))
  change (pCore 2 H).map H.subtype ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
  rw [map_subgroupOf_eq_of_le d.outside.1.1.2] at hh
  exact inf_le_right.trans hh

/-- All literal ambient commutator planes are the fixed and moved plane of one
order-two image. The odd-core characterization remains a model calculation. -/
theorem Preceding.common_plane {T : Sylow 2 G} {M Mc V H : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H) :
    letI := h.prepared.elementary
    ∃ B₀ : Subgroup (internalActionImage M V h.prepared.normalized),
      B₀ ≤ actor M V (T : Subgroup G) h.prepared.normalized ∧ Nat.card B₀ = 2 ∧
      (∀ A : Subgroup (internalActionImage M V h.prepared.normalized),
        A ≤ actor M V (T : Subgroup G) h.prepared.normalized → Nat.card A = 2 → A = B₀) ∧
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
  obtain ⟨B,hB⟩ := d.nonempty
  let B₀ := actor M V B h.prepared.normalized
  have hBT := d.actor_le_sylow hB
  have hBP : B₀ ≤ actor M V (T : Subgroup G) h.prepared.normalized :=
    map_mono (comap_mono hBT)
  obtain ⟨hc,hfm⟩ := quadratic_fixed_eq_moved h B₀ (d.planes B hB).1 (d.planes B hB).2.1
  refine ⟨B₀,hBP,hc,?_,?_⟩
  · intro A hAP hAc
    exact order_two_images_eq h d.alternatives d.non_omega hAP hBP hAc hc
  · intro C hC
    have hCT := d.actor_le_sylow hC
    have he : actor M V C h.prepared.normalized = B₀ :=
      quadratic_images_eq h d.alternatives d.non_omega _ _
        (map_mono (comap_mono hCT)) hBP (d.planes C hC).1 (d.planes B hB).1
        (d.planes C hC).2.1 (d.planes B hB).2.1
    refine ⟨he,ambient_fixed_eq_commutator h (hCT.trans h.maximal.1.2)
      (d.planes C hC).1 (d.planes C hC).2.1,?_,?_,
      seed_le_commutator h d.full hCT (d.planes C hC).1 (d.planes C hC).2.1⟩
    · rw [←he]
      exact (ambientSpace_moved _ h.prepared.le_selected (hCT.trans h.maximal.1.2)).symm
    · exact congrArg (ambientSpace V) hfm.symm

/-- The exact equal-plane alternative in the S₃ and D₁₀ rows. -/
theorem Preceding.equal_plane {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hm : Nonempty (internalActionImage M V h.prepared.normalized ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (internalActionImage M V h.prepared.normalized ≃* DihedralGroup 5))
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) :
    planeCentralizer T ⁅V,B⁆ = (T : Subgroup G) ∧ centralInvolutions T = ⁅V,B⁆ := by
  let := h.prepared.elementary
  have hBT := d.actor_le_sylow hB
  have hA := (d.planes B hB).1
  have hq := (d.planes B hB).2.1
  apply equal_plane_of_full_sylow_image h d.full hBT hA hq
  have hle : actor M V B h.prepared.normalized ≤
      actor M V (T : Subgroup G) h.prepared.normalized := map_mono (comap_mono hBT)
  exact eq_of_le_of_card_ge hle ((sylow_image_card_two h hm).le.trans
    (quadratic_fixed_eq_moved h _ hA hq).1.ge)

/-- The earlier Kc conclusion discharges the ambient cubic obstruction for
every plane in this same source family. -/
theorem Preceding.cubic_obstruction {T : Sylow 2 G} {M Mc V H B X : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) (hX : IsPGroup 3 X)
    (hXN : X ≤ normalizer (⁅V,B⁆ : Subgroup G)) :
    X ≤ centralizer (⁅V,B⁆ : Subgroup G) := by
  let := h.prepared.elementary
  have hp := (d.planes B hB).2.2
  exact h.threeSubgroup_plane_normalizer_centralizes hp.1 hp.2.1 hp.2.2.2.1 hp.2.2.2.2.1
    (d.residual_eq ▸ d.residual_centralizes) hX hXN
end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Cyclic
