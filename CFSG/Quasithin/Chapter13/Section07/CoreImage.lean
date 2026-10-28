module

public import CFSG.Quasithin.Chapter13.Section07.OrdinaryQuotient
public import CFSG.Quasithin.Chapter13.Section07.SeedCommutator
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreNormal


/-!
# The full original local-core image in 13.7.9

The F.9 point-normalizer containment makes the image of O₂(H) normal in
the actual natural-line stabilizer. Its original V_H subgroup supplies
the point transposition. The earlier noncentrality on V₃ excludes the
cyclic transposition image, so the native point-core theorem forces the
entire core. All subgroup maps and natural coordinates are retained.

The final consumer transports original13.5.4(5) from G₁ to every H below
it. That earlier noncentrality and genuine F.9 applicability remain with
the Section13.5 source owner; no core-image identity is assumed.
Source: Aschbacher–Smith,13.7.9(1), pp.940–941.
-/

@[expose] public section

open Subgroup BinaryPermutation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion NaturalAction
open Section08.TransvectionQuotients.FiveSeed.BarMarking
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

private theorem coordinate_mem_image (A : Subgroup G) (v : V) :
    (d.coordinate v).toAdd ∈ image d A ↔ v.val ∈ A := by
  constructor
  · intro hv
    obtain ⟨w,hw,he⟩ := (mem_image d A _).mp hv
    exact d.coordinate.injective he ▸ hw
  · intro hv
    exact (mem_image d A _).mpr ⟨v,hv,rfl⟩

theorem permutation_stabilizes_iff (A : Subgroup G) (hA : A ≤ V)
    (x : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    permutation d x ∈ subspaceStabilizer (naturalRepresentation (Fin 6)) (image d A) ↔
      x.val ∈ normalizer (A : Set G) := by
  constructor
  · intro hx
    apply mem_normalizer_fintype
    intro a ha
    let v : V := ⟨a,hA ha⟩
    have hh := (hx (d.coordinate v).toAdd).mpr ((coordinate_mem_image d A v).mpr ha)
    rw [← conjugation d x v] at hh
    exact (coordinate_mem_image d A _).mp hh
  · intro hx
    apply (mem_stabilizer_iff_map _ _).mpr
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨w,hw,rfl⟩
      obtain ⟨v,hv,rfl⟩ := (mem_image d A _).mp hw
      rw [← conjugation d x v]
      apply (coordinate_mem_image d A _).mpr
      exact (mem_normalizer_iff.mp hx v.val).mp hv
    · exact (LinearMap.GeneralLinearGroup.toLinearEquiv
        ((naturalRepresentation (Fin 6)).asGroupHom (permutation d x))).finrank_map_eq _

private theorem point_normalizer_le_local
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) :
    (L ⊔ (T : Subgroup G)) ⊓ normalizer (V₁ : Set G) ≤ H := by
  have hr := normalizer_residual_eq L V₁ (T : Subgroup G) T.isPGroup' d.normalizes_L
  have hn := residual_normalizer_sup_sylow
    (L ⊔ (T : Subgroup G)) V₁ T le_sup_right d.line_stable
  have he : normalizer (V₁ : Set G) = centralizer (V₁ : Set G) :=
    le_antisymm (normalizer_le_centralizer_of_card_two V₁ d.line_card)
      (Subgroup.centralizer_le_normalizer _)
  rw [hr, he] at hn
  rw [he]
  exact hn.symm.trans_le h.local_le

/-- The literal image of O₂(H) is the full core of the original natural-point stabilizer. -/
theorem nonabelian_core_image
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃, Section08.Source.QH H⁆ ≠ ⊥) :
    ((Section08.Source.QH H).subgroupOf (L ⊔ (T : Subgroup G))).map (permutation d) =
      (subspaceStabilizer (naturalRepresentation (Fin 6)) (image d V₁)).pCoreIn 2 := by
  let X : Subgroup G := L ⊔ (T : Subgroup G)
  let Q := Section08.Source.QH H
  let N := (Q.subgroupOf X).map (permutation d)
  let B := X ⊓ normalizer (V₁ : Set G)
  let C := subspaceStabilizer (naturalRepresentation (Fin 6)) (image d V₁)
  have hQX : Q ≤ X := h.QH_le_T.trans le_sup_right
  have hBV : V₁ ≤ V := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)
  have hQC : Q ≤ normalizer (V₁ : Set G) :=
    ((pCoreIn_le 2 H).trans h.H_centralizes).trans (Subgroup.centralizer_le_normalizer _)
  have hBN : B ≤ normalizer (Q : Set G) := (point_normalizer_le_local d h).trans
    (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
  have hBimage : (B.subgroupOf X).map (permutation d) = C := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (permutation_stabilizes_iff d V₁ hBV x).mpr hx.2
    · intro y hy
      obtain ⟨x,rfl⟩ := nonabelian_permutation_surjective d h hU hV y
      exact ⟨x,⟨x.property,(permutation_stabilizes_iff d V₁ hBV x).mp hy⟩,rfl⟩
  have hn : C ≤ normalizer (N : Set (Equiv.Perm (Fin 6))) := by
    rw [← hBimage]
    apply le_trans (map_mono ?_) (le_normalizer_map (permutation d))
    exact (comap_mono hBN).trans (le_normalizer_comap X.subtype)
  have hnC : N ≤ C := by
    rw [← hBimage]
    exact map_mono (comap_mono (le_inf hQX hQC))
  have hp : IsPGroup 2 N :=
    ((isPGroup_pCoreIn 2 H).of_equiv (subgroupOfEquivOfLe hQX).symm).map (permutation d)
  obtain ⟨t,ht,htA,_⟩ := nonabelian_transposition_images d h hU hV
  have htN : t ∈ N := by
    have hAN : ((Section08.Source.VH H V).subgroupOf X).map (permutation d) ≤ N :=
      map_mono (comap_mono (VH_le_core d h hU))
    rw [htA] at hAN
    exact hAN (mem_zpowers _)
  have hnot : ¬ N ≤ zpowers t := by
    intro hsmall
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    intro q hq v hv
    have him : permutation d ⟨q,hQX hq⟩ ∈
        ((Section08.Source.VH H V).subgroupOf X).map (permutation d) := by
      rw [htA]
      exact hsmall (mem_map_of_mem _ hq)
    obtain ⟨x,hx,hxe⟩ := him
    let vV : V := ⟨v,d.seed_le hv⟩
    have hc : x.val ∈ centralizer (V₃ : Set G) :=
      (centralizer_le (le_conjugateSpanBy V₃ H)) ((VH_centralizes_UH d h hU) hx).2
    have he := conjugation d ⟨q,hQX hq⟩ vV
    rw [← hxe, ← conjugation d x vV] at he
    have he' := congrArg Subtype.val (d.coordinate.injective he)
    change q*v*q⁻¹=x.val*v*x.val⁻¹ at he'
    rw [← hc v hv, mul_inv_cancel_right] at he'
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  exact Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreNormal.eq_point_core
    (image d V₁) (image_dim d V₁ hBV 1 d.line_card) N hp hnC hn t ht htN hnot

/-- The earlier ambient noncentrality 13.5.4(5) supplies the seed hypothesis
for every actual H below the original point normalizer. -/
theorem core_image_of_point_noncentral
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hHG : H ≤ G₁) (hne : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥) :
    ((Section08.Source.QH H).subgroupOf (L ⊔ (T : Subgroup G))).map (permutation d) =
      (subspaceStabilizer (naturalRepresentation (Fin 6)) (image d V₁)).pCoreIn 2 :=
  nonabelian_core_image d h hU hV (seed_noncentral_on_local_core h hHG hne)

end CFSG.Quasithin.Chapter13.Section07
