module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.Preparation
public import Theory.GroupAction.TypedCosetGeometry
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowKernelCore

/-!
# Moving the selected endpoint along the actual coset edge

The two types are cosets of YT and H. Incidence supplies a representative in
H, whose inverse sends the chosen neighbor gamma2 to the standard YT vertex.
Conjugation transports the whole edge stabilizer and its intrinsic two-core;
the core image in H/O₂(H) is then computed using its actual quotient map.

At a vertex represented by gH the attached subgroup is g V_H g⁻¹, with
V_H = localSpan V H. It is independent of the representative. The action
module remains U_H/Z with U_H = localSpan ZS H. The book uses right actions:
its gamma h is h⁻¹ • gamma here, and its V_gamma^h is
selectedConjugate H V_gamma h⁻¹. These inverse conventions are explicit
in the conclusions, including the equation for the new endpoint.

This proves transport conditional on F.9.13(2)'s original edge-core bound.
It does not construct the critical endpoint or prove that bound. Best-offender
status is supplied for this endpoint on the specified SectionAction; ordinary
offending or a smaller arbitrary two-subgroup cannot replace that input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.13,
printed p.322, and the paragraph after 15.3.49(h), printed p.1143.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ConjugatePlacement
variable {G : Type*} [Group G]

/-- The actual coset types: false is YT and true is H. -/
def family (Y T H : Subgroup G) : Bool → Subgroup G :=
  fun i => if i then H else Y ⊔ T

/-- A vertex of the typed YT/H coset geometry. -/
abbrev Vertex (Y T H : Subgroup G) := CosetGeometry.Vertex (family Y T H)
/-- The standard vertex of either coset type. -/
abbrev base (Y T H : Subgroup G) (i : Bool) : Vertex Y T H :=
  CosetGeometry.base (family Y T H) i

/-- The pointwise stabilizer of the two endpoints, in the ambient group. -/
def edgeGroup (Y T H : Subgroup G) (v w : Vertex Y T H) : Subgroup G :=
  MulAction.stabilizer G v ⊓ MulAction.stabilizer G w

/-- Incidence with the H vertex supplies an element of H moving the neighbor to gamma0. -/
theorem exists_move_neighbor (Y T H : Subgroup G) (v : Vertex Y T H)
    (ht : v.type = false) (hv : CosetGeometry.Incident (family Y T H) (base Y T H true) v) :
    ∃ h : H, (h : G) • v = base Y T H false := by
  obtain ⟨g, hg, he⟩ := (CosetGeometry.incident_base_iff (family Y T H) true v).mp hv
  have hgH : g ∈ H := hg
  have hv' : g • base Y T H false = v := by
    rcases v with ⟨i, q⟩
    dsimp at ht
    subst i
    change CosetGeometry.Vertex.mk false (g • ((1 : G) : G ⧸ family Y T H false)) = _
    rw [MulAction.Quotient.smul_mk]
    simpa only [smul_eq_mul, mul_one] using congrArg (CosetGeometry.Vertex.mk false) he
  refine ⟨⟨g⁻¹, H.inv_mem hgH⟩, ?_⟩
  rw [← hv']
  exact inv_smul_smul g _

/-- Conjugating an edge transports its full pointwise stabilizer. -/
theorem edgeGroup_map (Y T H : Subgroup G) (v w : Vertex Y T H) (g : G) :
    (edgeGroup Y T H v w).map (MulAut.conj g).toMonoidHom =
      edgeGroup Y T H (g • v) (g • w) := by
  simp only [edgeGroup, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.map_inf _ _ _ (MulAut.conj g).injective

/-- The standard edge stabilizer is the actual intersection of its vertex groups. -/
theorem edgeGroup_base (Y T H : Subgroup G) :
    edgeGroup Y T H (base Y T H true) (base Y T H false) = H ⊓ (Y ⊔ T) := by
  simp only [edgeGroup, base, CosetGeometry.stabilizer_base, family, Bool.false_eq_true,
    ↓reduceIte]

/-- The neighbor-moving element carries the initial edge-core containment into the standard edge core. -/
theorem move_edge_core (Y Y0 T H A : Subgroup G) (v : Vertex Y T H)
    (hB : H ⊓ (Y ⊔ T) = Y0 ⊔ T) (h : H) (hv : (h : G) • v = base Y T H false)
    (hA : A ≤ (edgeGroup Y T H (base Y T H true) v).pCoreIn 2) :
    selectedConjugate H A h ≤ (Y0 ⊔ T).pCoreIn 2 := by
  have hf : (h : G) • base Y T H true = base Y T H true := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [base, CosetGeometry.stabilizer_base]
    exact h.property
  have he := edgeGroup_map Y T H (base Y T H true) v (h : G)
  rw [hf, hv, edgeGroup_base, hB] at he
  have hm := map_mono (f := (MulAut.conj (h : G)).toMonoidHom) hA
  rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj (h : G)).injective, he] at hm
  exact hm

/-- The local two-core has exactly the two-core of the image as its star image. -/
theorem starImage_core [Finite G] (H B : Subgroup G) (hBH : B ≤ H) :
    starImage H (B.pCoreIn 2) = (starImage H B).pCoreIn 2 := by
  have he : ((B.subgroupOf H).pCoreIn 2).map H.subtype = B.pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le hBH]
  have hc : (B.pCoreIn 2).subgroupOf H = (B.subgroupOf H).pCoreIn 2 := by
    rw [← he]
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact (Subtype.ext hyx : y = x) ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  change ((B.pCoreIn 2).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) = _
  rw [hc]
  apply map_pCoreIn_of_ker_isPGroup
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup

/-- Joins inside H pass to the star quotient. -/
theorem starImage_join (H A B : Subgroup G) (hAH : A ≤ H) (hBH : B ≤ H) :
    starImage H (A ⊔ B) = starImage H A ⊔ starImage H B := by
  simp only [starImage, subgroupOf_sup hAH hBH, Subgroup.map_sup]

/-- Right-action placement, conditional on the initial edge-core bound and the standard edge intersection. -/
theorem exists_placed_of_edgeCore [Finite G]
    (Y Y0 T H A : Subgroup G) (v : Vertex Y T H)
    (ht : v.type = false) (hv : CosetGeometry.Incident (family Y T H) (base Y T H true) v)
    (hB : H ⊓ (Y ⊔ T) = Y0 ⊔ T)
    (hA : A ≤ (edgeGroup Y T H (base Y T H true) v).pCoreIn 2) :
    ∃ h : H, (h : G)⁻¹ • v = base Y T H false ∧
      selectedConjugate H A h⁻¹ ≤ (Y0 ⊔ T).pCoreIn 2 ∧
      starImage H (selectedConjugate H A h⁻¹) ≤
        (starImage H Y0 ⊔ starImage H T).pCoreIn 2 := by
  obtain ⟨k, hk⟩ := exists_move_neighbor Y T H v ht hv
  have hcore := move_edge_core Y Y0 T H A v hB k hk hA
  have hYH : Y0 ⊔ T ≤ H := hB ▸ inf_le_left
  refine ⟨k⁻¹, by simpa using hk, by simpa using hcore, ?_⟩
  have hs := map_mono (f := QuotientGroup.mk' (pCore 2 H)) (comap_mono (f := H.subtype) hcore)
  change starImage H (selectedConjugate H A k) ≤ starImage H ((Y0 ⊔ T).pCoreIn 2) at hs
  rw [starImage_core H _ hYH, starImage_join H Y0 T (le_sup_left.trans hYH) (le_sup_right.trans hYH)] at hs
  simpa only [inv_inv] using hs

/-- The genuine conjugate of V_H attached to the H-type vertex represented by g. -/
def endpointModule (V H : Subgroup G) (g : G) : Subgroup G :=
  (localSpan V H).map (MulAut.conj g).toMonoidHom

/-- The endpoint module depends only on the coset vertex, not its representative. -/
theorem endpointModule_congr (V Y T H : Subgroup G) (g k : G)
    (he : g • base Y T H true = k • base Y T H true) :
    endpointModule V H g = endpointModule V H k := by
  have hkg : k⁻¹ * g ∈ H := by
    have hs : k⁻¹ * g ∈ MulAction.stabilizer G (base Y T H true) := by
      apply MulAction.mem_stabilizer_iff.mpr
      rw [mul_smul, he, inv_smul_smul]
    rwa [base, CosetGeometry.stabilizer_base] at hs
  have hn : (localSpan V H).map (MulAut.conj (k⁻¹ * g)).toMonoidHom = localSpan V H :=
    mem_normalizer_iff_map_conj_eq.mp ((le_normalizer_conjugateSpanBy V H) hkg)
  calc
    endpointModule V H g =
        ((localSpan V H).map (MulAut.conj (k⁻¹ * g)).toMonoidHom).map
          (MulAut.conj k).toMonoidHom := by
      unfold endpointModule
      rw [map_map]
      congr 1
      ext x
      change g * x * g⁻¹ = k * ((k⁻¹ * g) * x * (k⁻¹ * g)⁻¹) * k⁻¹
      group
    _ = endpointModule V H k := by rw [hn]; rfl

/-- Book right conjugation corresponds to the inverse in the prepared left-conjugation API. -/
theorem endpointModule_right (V H : Subgroup G) (g : G) (h : H) :
    endpointModule V H ((h : G)⁻¹ * g) = selectedConjugate H (endpointModule V H g) h⁻¹ := by
  unfold endpointModule selectedConjugate
  rw [map_map]
  congr 1
  ext x
  change ((h : G)⁻¹ * g) * x * ((h : G)⁻¹ * g)⁻¹ = (h : G)⁻¹ * (g * x * g⁻¹) * ((h : G)⁻¹)⁻¹
  group

/-- Construct the moved endpoint and preserve its exact quadratic best-offender assertions and span. -/
theorem exists_selected_endpoint_of_edgeCore [Finite G]
    (Y Y0 T H V ZS Z : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (g : G) (gamma2 : Vertex Y T H)
    (ht : gamma2.type = false)
    (hadj : CosetGeometry.Incident (family Y T H) (base Y T H true) gamma2)
    (hB : H ⊓ (Y ⊔ T) = Y0 ⊔ T)
    (hcore : endpointModule V H g ≤ (edgeGroup Y T H (base Y T H true) gamma2).pCoreIn 2)
    (hbest : IsBestOffender action.representation (starImage H (endpointModule V H g)))
    (hquad : IsQuadratic action.representation (starImage H (endpointModule V H g))) :
    ∃ h : H, (h : G)⁻¹ • gamma2 = base Y T H false ∧
      ((h : G)⁻¹ * g) • base Y T H true = (h : G)⁻¹ • (g • base Y T H true) ∧
      endpointModule V H ((h : G)⁻¹ * g) = selectedConjugate H (endpointModule V H g) h⁻¹ ∧
      endpointModule V H ((h : G)⁻¹ * g) ≤ (Y0 ⊔ T).pCoreIn 2 ∧
      starImage H (endpointModule V H ((h : G)⁻¹ * g)) ≤ (starImage H Y0 ⊔ starImage H T).pCoreIn 2 ∧
      IsBestOffender action.representation (starImage H (endpointModule V H ((h : G)⁻¹ * g))) ∧
      IsQuadratic action.representation (starImage H (endpointModule V H ((h : G)⁻¹ * g))) ∧
      localSpan (endpointModule V H ((h : G)⁻¹ * g)) H = localSpan (endpointModule V H g) H := by
  have hAH : endpointModule V H g ≤ H := by
    have hle := hcore.trans ((pCoreIn_le 2 _).trans (inf_le_left : edgeGroup Y T H (base Y T H true) gamma2 ≤ _))
    simpa only [base, CosetGeometry.stabilizer_base, family, ↓reduceIte] using hle
  obtain ⟨h, hv, ha, hs⟩ := exists_placed_of_edgeCore Y Y0 T H (endpointModule V H g) gamma2 ht hadj hB hcore
  have ho := selectedConjugate_offender H ZS Z (endpointModule V H g) action hAH h⁻¹ hbest hquad
  refine ⟨h, hv, mul_smul _ _ _, endpointModule_right V H g h, ?_⟩
  rw [endpointModule_right]
  exact ⟨ha, hs, ho.1, ho.2, selectedConjugate_span H (endpointModule V H g) h⁻¹⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ConjugatePlacement
