module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Inputs
public import Theory.GroupTheory.ComponentLocalOrbitCore

/-!
# Transport of the marked A₈ enlargement

The source chooses a new involution by conjugation inside C_G(z), where L is
normal. The actual enlargement is equivariant because both the layer and the
orbit-generated subgroup are equivariant. Transporting its S₈ marking also
transports the embedded A₈, the embedded A₆, and both centralizer Sylows.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the paragraph
after Lemma 16.3.11, printed p.1181 / PDF p.1198.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.ThompsonObstruction
variable {G : Type*} [Group G]

private def onSubgroup (e : G ≃* G) {H J : Subgroup G}
    (he : H.map e.toMonoidHom = J) : H ≃* J :=
  (e.subgroupMap H).trans (MulEquiv.subgroupCongr he)

private theorem onSubgroup_map (e : G ≃* G) {H J : Subgroup G}
    (he : H.map e.toMonoidHom = J) (A : Subgroup G) :
    (A.subgroupOf H).map (onSubgroup e he).toMonoidHom =
      (A.map e.toMonoidHom).subgroupOf J := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_map_of_mem _ hy
  · intro hx
    obtain ⟨y, rfl⟩ := (onSubgroup e he).surjective x
    obtain ⟨a, ha, heq⟩ := hx
    refine ⟨y, ?_, rfl⟩
    change (y : G) ∈ A
    rwa [← e.injective heq]

private theorem onSubgroup_map_symm (e : G ≃* G) {H J : Subgroup G}
    (he : H.map e.toMonoidHom = J) (A : Subgroup G) :
    ((A.map e.toMonoidHom).subgroupOf J).map (onSubgroup e he).symm.toMonoidHom =
      A.subgroupOf H := by
  rw [← onSubgroup_map e he A, map_map]
  simp

private theorem layer_map_le {H J : Type*} [Group H] [Group J] (e : H ≃* J) :
    (componentLayer H).map e.toMonoidHom ≤ componentLayer J := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro L hL
  exact map_le_iff_le_comap.mp (le_sSup (hL.map_equiv e))

private theorem layer_map {H J : Type*} [Group H] [Group J] (e : H ≃* J) :
    (componentLayer H).map e.toMonoidHom = componentLayer J := by
  apply le_antisymm (layer_map_le e)
  have h := map_mono (f := e.toMonoidHom) (layer_map_le e.symm)
  simpa [map_map] using h

private theorem layerIn_map (H : Subgroup G) (e : G ≃* G) :
    (ComponentTransfer.layerIn H).map e.toMonoidHom =
      ComponentTransfer.layerIn (H.map e.toMonoidHom) := by
  unfold ComponentTransfer.layerIn
  change ((componentLayer H).map H.subtype).map (e : G →* G) =
    (componentLayer (H.map (e : G →* G))).map (H.map (e : G →* G)).subtype
  rw [← layer_map (e.subgroupMap H), map_map, map_map]
  rfl

/-- The enlargement is transported as the actual layer closure of L. -/
theorem enlargement_map (t : G) (L : Subgroup G) (e : G ≃* G) :
    (enlargement t L).map e.toMonoidHom =
      enlargement (e t) (L.map e.toMonoidHom) := by
  unfold enlargement ComponentTransfer.layerClosure
  rw [map_componentOrbit, layerIn_map, involutionCentralizer, map_centralizer_equiv,
    Set.image_singleton]

private theorem sylow_transport [Finite G] {H J A : Subgroup G} (e : G ≃* G)
    (he : H.map e.toMonoidHom = J)
    (h : ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = A) :
    ∃ S : Sylow 2 J, (S : Subgroup J).map J.subtype = A.map e.toMonoidHom := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S.mapSurjective (f := (onSubgroup e he).toMonoidHom)
    (onSubgroup e he).surjective, ?_⟩
  change ((S : Subgroup H).map (onSubgroup e he).toMonoidHom).map J.subtype = _
  rw [← hS, map_map, map_map]
  rfl

/-- All fields of the marked enlargement survive an automorphism fixing z
and preserving L, including both actual centralizer Sylow subgroups. -/
noncomputable def MarkedEnlargement.transport [Finite G] {z t : G} {L : Subgroup G}
    (d : MarkedEnlargement z t L) (e : G ≃* G) (hz : e z = z)
    (hL : L.map e.toMonoidHom = L) : MarkedEnlargement z (e t) L := by
  have hK : (enlargement t L).map e.toMonoidHom = enlargement (e t) L := by
    rw [enlargement_map, hL]
  have hJ : (enlargement t L ⊔ zpowers z).map e.toMonoidHom =
      enlargement (e t) L ⊔ zpowers z := by
    simp only [Subgroup.map_sup, hK, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hz]
  let f := onSubgroup e hJ
  refine {
    component := ?_
    equiv := f.symm.trans d.equiv
    enlargement_image := ?_
    component_image := ?_
    involution_image := ?_
    centralizer_component_sylow := ?_
    centralizer_enlargement_sylow := ?_ }
  · have hc := (show Theory.GroupTheory.IsComponentIn (enlargement t L)
        (involutionCentralizer t) from d.component).map e
    rwa [hK, involutionCentralizer, map_centralizer_equiv, Set.image_singleton] at hc
  · change ((enlargement (e t) L).subgroupOf _).map
      (d.equiv.toMonoidHom.comp f.symm.toMonoidHom) = _
    have hm := onSubgroup_map_symm e hJ (enlargement t L)
    rw [hK] at hm
    rw [← map_map, hm, d.enlargement_image]
  · change (L.subgroupOf _).map (d.equiv.toMonoidHom.comp f.symm.toMonoidHom) = _
    have hm := onSubgroup_map_symm e hJ L
    rw [hL] at hm
    rw [← map_map, hm, d.component_image]
  · change d.equiv (f.symm _) = _
    rw [show f.symm ⟨z, (le_sup_right : zpowers z ≤ enlargement (e t) L ⊔ zpowers z) (mem_zpowers z)⟩ =
        ⟨z, (le_sup_right : zpowers z ≤ enlargement t L ⊔ zpowers z) (mem_zpowers z)⟩ from ?_]
    · exact d.involution_image
    · apply f.injective
      rw [f.apply_symm_apply]
      apply Subtype.ext
      exact hz.symm
  · have he : (involutionCentralizer t ⊓ centralizer (L : Set G)).map e.toMonoidHom =
        involutionCentralizer (e t) ⊓ centralizer (L : Set G) := by
      rw [map_inf _ _ _ e.injective, involutionCentralizer,
        map_centralizer_equiv, Set.image_singleton, map_centralizer_equiv,
        show e '' (L : Set G) = (L : Set G) from congrArg (fun A : Subgroup G => (A : Set G)) hL]
    have hs := sylow_transport e he d.centralizer_component_sylow
    simpa [Subgroup.map_sup, MonoidHom.map_zpowers, hz] using hs
  · have he : (involutionCentralizer t ⊓ centralizer (enlargement t L : Set G)).map
        e.toMonoidHom = involutionCentralizer (e t) ⊓
          centralizer (enlargement (e t) L : Set G) := by
      rw [map_inf _ _ _ e.injective, involutionCentralizer,
        map_centralizer_equiv, Set.image_singleton, map_centralizer_equiv,
        show e '' (enlargement t L : Set G) = (enlargement (e t) L : Set G) from
          congrArg (fun A : Subgroup G => (A : Set G)) hK]
    have hs := sylow_transport e he d.centralizer_enlargement_sylow
    simpa [MonoidHom.map_zpowers] using hs

end CFSG.Quasithin.Chapter16.ThompsonObstruction
