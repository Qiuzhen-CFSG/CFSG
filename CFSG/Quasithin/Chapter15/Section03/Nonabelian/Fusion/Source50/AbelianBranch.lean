module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Initial
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Image
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Source50Model.Fixed

/-!
# The abelian alternative in the original 15.3.51

An abelian U centralizes its seed ZS. In the literal orthogonal Sylow
action, the pointwise stabilizer of ZS is the plane stabilizer S. Every
nontrivial normal Sylow image fixes only vectors in ZS. These two concrete
facts give U≤S and V∩U=ZS before the separate abelian exclusion.

Source: Aschbacher–Smith, Lemma 15.3.51(2b), printed p.1145.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open OrthogonalGeometry
variable {G : Type*} [Group G] [Finite G]
variable (d : CharacteristicTwo.LocalData G) (H : Subgroup G)
  (h : (localSetup d H).Hypothesis)
include h

omit h in
private theorem seed_coordinate_plane :
    d.ZS = (fixedVectors (OrthogonalGeometry.Source50Model.planePart
      (d.action.sylowImage d.T d.sylow_le))).map d.action.vectorEmbedding := by
  rw [show d.ZS = fixedPlane d.V d.S from rfl,
    d.action.fixedPlane_eq_map (X := d.S) (inf_le_left.trans d.sylow_le),
    d.action.image_planeStabilizer, OrthogonalGeometry.setwise_plane_eq_ker]
  rfl

theorem abelian_span_le_plane_stabilizer
    (hc : IsMulCommutative (localSpan d.ZS H)) : localSpan d.ZS H ≤ d.S := by
  let U := localSpan d.ZS H
  have hUT : U ≤ (d.T : Subgroup G) := h.UH_le_QH.trans h.QH_le_T
  have hUM : U ≤ d.M := hUT.trans d.sylow_le
  have hUC : U ≤ centralizer (d.ZS : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr hc).trans
      (centralizer_le (le_conjugateSpanBy d.ZS H))
  intro u hu
  refine ⟨hUT hu,?_⟩
  have hp : d.action.actor ⟨u,hUM hu⟩ ∈ OrthogonalGeometry.Source50Model.planePart
      (d.action.sylowImage d.T d.sylow_le) := by
    rw [← OrthogonalGeometry.Source50Model.pointwise_plane_fixed]
    refine ⟨mem_map_of_mem d.action.actor (hUT hu),?_⟩
    have hcentral := hUC hu
    rw [seed_coordinate_plane] at hcentral
    have hc' : (⟨u,hUM hu⟩ : d.M) ∈ (centralizer
        ((fixedVectors (OrthogonalGeometry.Source50Model.planePart
          (d.action.sylowImage d.T d.sylow_le))).map d.action.vectorEmbedding : Set G)).subgroupOf
          d.M := hcentral
    rw [d.action.centralizer_map_eq_comap] at hc'
    exact hc'
  have hs : d.action.actor ⟨u,hUM hu⟩ ∈ setwise (orthogonalCoordinatePlane 1) := by
    rw [setwise_plane_eq_ker]
    exact hp.2
  exact (show (⟨u,hUM hu⟩ : d.M) ∈ (normalizer (d.V₁ : Set G)).subgroupOf d.M from
    (d.action.plane_normalizer_eq_comap 1).symm ▸ hs)

theorem abelian_span_intersection
    (hf : ∀ g : G, d.V.map (MulAut.conj g).toMonoidHom ≤ d.M →
      d.V.map (MulAut.conj g).toMonoidHom ≤ centralizer (d.V : Set G))
    (hnon : ¬ IsMulCommutative (localSpan d.V H))
    (hc : IsMulCommutative (localSpan d.ZS H)) : d.ZS = d.V ⊓ localSpan d.ZS H := by
  let U := localSpan d.ZS H
  have hUM : U ≤ d.M := h.UH_le_QH.trans (h.QH_le_T.trans d.sylow_le)
  have hfix : fixedPlane d.V U ≤ d.ZS := by
    rw [d.action.fixedPlane_eq_map hUM,seed_coordinate_plane]
    apply map_mono
    exact OrthogonalGeometry.Source50Model.fixedVectors_le_plane_fixed
      (d.action.sylowImage d.T d.sylow_le) (d.action.image U)
      (span_image_le_sylow d H h) (sylow_normalizes_span_image d H h)
      (span_action_ne_bot d H h hf hnon)
  apply le_antisymm (le_inf h.plus_le (le_conjugateSpanBy _ _))
  exact (inf_le_inf_left d.V (le_centralizer_iff_isMulCommutative.mpr hc)).trans hfix

theorem abelian_alternative
    (hf : ∀ g : G, d.V.map (MulAut.conj g).toMonoidHom ≤ d.M →
      d.V.map (MulAut.conj g).toMonoidHom ≤ centralizer (d.V : Set G))
    (hnon : ¬ IsMulCommutative (localSpan d.V H))
    (hc : IsMulCommutative (localSpan d.ZS H)) :
    IsElementaryAbelian 2 (localSpan d.ZS H) ∧ localSpan d.ZS H ≤ d.S ∧
      d.ZS = d.V ⊓ localSpan d.ZS H :=
  ⟨elementary_U_of_commutative d H h hc,
    abelian_span_le_plane_stabilizer d H h hc,
    abelian_span_intersection d H h hf hnon hc⟩

/-- Containment in S is also sufficient: the seed ZS centralizes S, hence
it centralizes its own H-span. -/
theorem commutative_span_iff_le_plane_stabilizer :
    IsMulCommutative (localSpan d.ZS H) ↔ localSpan d.ZS H ≤ d.S := by
  constructor
  · exact abelian_span_le_plane_stabilizer d H h
  · intro hUS
    apply (conjugateSpanBy_commutative_iff _ _).mpr
    exact (show d.ZS ≤ centralizer (d.S : Set G) from inf_le_right).trans
      (centralizer_le hUS)

/-- Nonabelianness forces the actual U image to escape the plane
stabilizer image; no assertion about the size of U/Z enters here. -/
theorem nonabelian_image_outside_stabilizer
    (hu : ¬ IsMulCommutative (localSpan d.ZS H)) :
    ¬ d.action.image (localSpan d.ZS H) ≤ d.action.image d.S := by
  intro him
  apply hu
  apply (commutative_span_iff_le_plane_stabilizer d H h).mpr
  intro u huU
  have huT := h.QH_le_T (h.UH_le_QH huU)
  let um : d.M := ⟨u,d.sylow_le huT⟩
  have ha := him (mem_map_of_mem d.action.actor (show um ∈
    (localSpan d.ZS H).subgroupOf d.M from huU))
  rw [d.action.image_planeStabilizer] at ha
  refine ⟨huT,?_⟩
  exact (show um ∈ (normalizer (d.V₁ : Set G)).subgroupOf d.M from
    (d.action.plane_normalizer_eq_comap 1).symm ▸ ha.2)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
