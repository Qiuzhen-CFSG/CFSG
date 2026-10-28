module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryGraph
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedWeakClosureFixedSpace

/-!
# The crossed centralizers in the odd escaping graph

The literal zeroth weak closure centralizes Z_S. Sylow conjugacy inside
an overgroup H of T that normalizes Z_S therefore puts every conjugate
of the natural seed contained in H into C_H(Z_S). This extends to any
conjugate of the H-closure contained in H.

The normalized odd critical endpoint supplies both opposite placements.
Transporting its modules and stabilizer through the actual generated-group
embedding identifies them with the original H-closure and its conjugate.
The weak-closure argument then proves both crossed centralizer bounds,
with the same ambient conjugator in every expression.

These are the assertions marked (!) in 6.1.19. The subsequent index-two
normalizer argument and the nonabelianness conclusion remain with
qt-d-1222-rankone-recognition-natural. No odd-branch exclusion or final
6.1.27 reduction is asserted here.
Source: Aschbacher–Smith, 6.1.12(3) and 6.1.19, printed pp.670,673–674.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Subgroup.CosetGeometry.RankTwo
open CFSG.Quasithin.ChapterF.Section07.Track
open CFSG.Quasithin.ChapterF.Section07.CriticalPairs
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem conjugate_twice (B : Subgroup G) (a b : G) :
    (B.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      B.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply,mul_assoc]

/-- Weak-closure control transports from T to every conjugate lying in
an overgroup of T that normalizes Z_S. -/
theorem conjugate_le_centralizer_in_vertex
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n)
    {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hHN : H ≤ Escape.H (T : Subgroup G) L R)
    (g : G) (hg : (layer L R).map (MulAut.conj g).toMonoidHom ≤ H) :
    (layer L R).map (MulAut.conj g).toMonoidHom ≤ Escape.I (T : Subgroup G) L R := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let I := Escape.I (T : Subgroup G) L R
  let := h.layer_elementary
  have hp : IsPGroup 2 (A.subgroupOf H) :=
    ((IsElementaryAbelian.isPGroup 2 B).map (MulAut.conj g).toMonoidHom).comap_subtype
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  obtain ⟨m,hm⟩ := MulAction.exists_smul_eq H P (T.subtype hTH)
  have hmap : (P : Subgroup H).map (MulAut.conj m).toMonoidHom = (T : Subgroup G).subgroupOf H := by
    change ((m • P : Sylow 2 H) : Subgroup H) = _
    rw [hm,Sylow.coe_subtype]
  have hAT : A.map (MulAut.conj (m : G)).toMonoidHom ≤ (T : Subgroup G) := by
    rintro _ ⟨a,ha,rfl⟩
    have hh : (MulAut.conj m) (⟨a,hg ha⟩ : H) ∈ (T : Subgroup G).subgroupOf H :=
      hmap ▸ mem_map_of_mem (MulAut.conj m).toMonoidHom
        (hP (show (⟨a,hg ha⟩ : H) ∈ A.subgroupOf H from ha))
    exact hh
  have he : A.map (MulAut.conj (m : G)).toMonoidHom =
      B.map (MulAut.conj ((m : G) * g)).toMonoidHom := conjugate_twice B g m
  rw [he] at hAT
  have hw := (natural_weak_closure_bounds_of_globalS_eq h hnat hs).2.trans inf_le_right
  have hc := (W_zero_le_iff B (T : Subgroup G) I).mp hw ((m : G) * g) hAT
  have hI : I.map (MulAut.conj (m : G)).toMonoidHom = I :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer_le_normalizer_centralizer _)
      (hHN m.property))
  apply (map_le_map_iff_of_injective (f := (MulAut.conj (m : G)).toMonoidHom)
    (MulAut.conj (m : G)).injective).mp
  rwa [hI,he]

/-- Every conjugate of the local closure contained in the original vertex
centralizes its central line. This is the placement used in 6.1.19 (!). -/
theorem closure_conjugate_le_centralizer
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n)
    {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hHN : H ≤ Escape.H (T : Subgroup G) L R)
    (g : G) (hg : (conjugateSpanBy (layer L R) H).map (MulAut.conj g).toMonoidHom ≤ H) :
    (conjugateSpanBy (layer L R) H).map (MulAut.conj g).toMonoidHom ≤
      Escape.I (T : Subgroup G) L R := by
  rw [conjugateSpanBy_eq_iSup_conj,Subgroup.map_iSup] at hg ⊢
  apply iSup_le
  intro a
  have ha := (le_iSup (fun a : H => ((layer L R).map
    (MulAut.conj (a : G)).toMonoidHom).map (MulAut.conj g).toMonoidHom) a).trans hg
  rw [conjugate_twice] at ha ⊢
  exact conjugate_le_centralizer_in_vertex h hnat hs hTH hHN _ ha

namespace OddConfiguration
variable (d : OddConfiguration T L M R)

/-- The original ambient conjugator of the normalized critical endpoint. -/
@[expose] def representative : G := d.endpoint.val.val

/-- The actual module at the H-vertex. -/
@[expose] def localClosure : Subgroup G := conjugateSpanBy (layer L R) d.H

private theorem base_module_map :
    let K := (L ⊔ (T : Subgroup G)) ⊔ d.H
    let F : Bool → Subgroup K := fun i => if i then d.H.subgroupOf K
      else (L ⊔ (T : Subgroup G)).subgroupOf K
    (vertexModule F d.D.seed (base F true)).map K.subtype = d.localClosure := by
  dsimp only
  rw [second_base_module_eq_conjugate_join _ _ d.D.seed_normalized,
    ←conjugateSpanBy_eq_iSup_conj,map_conjugateSpanBy,d.seed_map]
  change conjugateSpanBy (layer L R)
    ((d.H.subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ d.H)).map _ ) = _
  rw [map_subgroupOf_eq_of_le le_sup_right]
  rfl

private theorem conjugate_map (A : Subgroup ((L ⊔ (T : Subgroup G)) ⊔ d.H : Subgroup G)) :
    (A.map (MulAut.conj d.endpoint.val).toMonoidHom).map
      ((L ⊔ (T : Subgroup G)) ⊔ d.H).subtype =
    (A.map ((L ⊔ (T : Subgroup G)) ⊔ d.H).subtype).map
      (MulAut.conj d.representative).toMonoidHom := by
  rw [map_map,map_map]
  rfl

/-- Both critical endpoint modules are the literal conjugate closures,
and each lies in the opposite H-vertex. -/
theorem opposite_placements :
    d.localClosure.map (MulAut.conj d.representative).toMonoidHom ≤ d.H ∧
      d.localClosure ≤ d.H.map (MulAut.conj d.representative).toMonoidHom ∧
      ⁅d.localClosure,d.localClosure.map (MulAut.conj d.representative).toMonoidHom⁆ ≤
        d.localClosure ⊓ d.localClosure.map (MulAut.conj d.representative).toMonoidHom := by
  let K := (L ⊔ (T : Subgroup G)) ⊔ d.H
  let F : Bool → Subgroup K := fun i => if i then d.H.subgroupOf K
    else (L ⊔ (T : Subgroup G)).subgroupOf K
  have he : (vertexModule F d.D.seed d.endpoint.vertex).map K.subtype =
      d.localClosure.map (MulAut.conj d.representative).toMonoidHom := by
    rw [NormalizedEndpoint.vertex,vertexModule_translate _ _ d.D.seed_normalized,
      d.conjugate_map,d.base_module_map]
  have hstab : (stabilizer F d.endpoint.vertex).map K.subtype =
      d.H.map (MulAut.conj d.representative).toMonoidHom := by
    rw [NormalizedEndpoint.vertex,stabilizer_translate,
      show stabilizer F (base F true) = F true from Subgroup.CosetGeometry.stabilizer_base F true,
      d.conjugate_map]
    change ((d.H.subgroupOf K).map K.subtype).map _ = _
    rw [map_subgroupOf_eq_of_le le_sup_right]
  have hleft := map_mono (f := K.subtype) (d.endpoint.endpoint_module_le d.distance)
  have hright := map_mono (f := K.subtype) (d.endpoint.reverse_module_le d.distance)
  have hpair := map_mono (f := K.subtype) d.pair
  rw [he] at hleft
  change d.localClosure.map (MulAut.conj d.representative).toMonoidHom ≤
    (d.H.subgroupOf K).map K.subtype at hleft
  rw [map_subgroupOf_eq_of_le le_sup_right] at hleft
  rw [d.base_module_map,hstab] at hright
  rw [map_commutator,map_inf _ _ _ K.subtype_injective,d.base_module_map,he] at hpair
  exact ⟨hleft,hright,hpair⟩

/-- The crossed central-line centralization marked (!) in 6.1.19, with
both literal endpoint subgroups and the same original conjugator. -/
theorem crossed_centralization
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n) :
    d.localClosure.map (MulAut.conj d.representative).toMonoidHom ≤
        d.H ⊓ Escape.I (T : Subgroup G) L R ∧
      d.localClosure ≤ (d.H ⊓ Escape.I (T : Subgroup G) L R).map
        (MulAut.conj d.representative).toMonoidHom := by
  have hHN : d.H ≤ Escape.H (T : Subgroup G) L R := d.overgroup.trans
    (sup_le (Subgroup.centralizer_le_normalizer _) h.sylow_normalizes_ZS)
  obtain ⟨hleft,hright,_⟩ := d.opposite_placements
  have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  have hinv (A : Subgroup G) : (A.map (MulAut.conj d.representative).toMonoidHom).map
      (MulAut.conj d.representative⁻¹).toMonoidHom = A := by
    rw [conjugate_twice,inv_mul_cancel,hid,Subgroup.map_id]
  have hback : d.localClosure.map (MulAut.conj d.representative⁻¹).toMonoidHom ≤ d.H := by
    have hh := map_mono (f := (MulAut.conj d.representative⁻¹).toMonoidHom) hright
    rwa [hinv] at hh
  have hc := closure_conjugate_le_centralizer h hnat hs d.hstar.1.1.2 hHN
    d.representative hleft
  have hci := closure_conjugate_le_centralizer h hnat hs d.hstar.1.1.2 hHN
    d.representative⁻¹ hback
  refine ⟨le_inf hleft hc,?_⟩
  have hh := map_mono (f := (MulAut.conj d.representative).toMonoidHom) (le_inf hback hci)
  rw [conjugate_twice,mul_inv_cancel,hid,Subgroup.map_id] at hh
  exact hh

end OddConfiguration
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph
