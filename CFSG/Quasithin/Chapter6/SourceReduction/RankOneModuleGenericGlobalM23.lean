module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.NormalizerCompatibility
public import Theory.Mathieu.M23.QuasithinGeometry.SourceRecognition.CoreAlignment
/-!
# Ambient M23 recognition for the original nonmaximal linear branch

The constructed vertex coordinates already preserve L, the full exceptional
core as a subgroup, and its normalizer H. Restricting these coordinates and the
same heptad marking to H gives an automorphism of the native pair/heptad
intersection. The coset-orbit marking identifies its entire edge intersection.
The native core-action calculation therefore corrects the vertex coordinates
pointwise on the core while preserving the whole edge fixer. Self-centralization
then determines Ix, and the previously proved whole-Ix correction, edge rigidity
and uniqueness-system recognition give an actual ambient equivalence with M23.

No extra recognition or generation premise is used. The original Preparation,
full KnownSimple input, selected field, and both compatible amalgam orientations
are retained. Earlier construction supplies the source 5.2.11--22 local results
and genuine ambient generation. The unused hgen/hthree/hN assumptions of the
original consumer may be omitted here.

Source: Aschbacher--Smith 5.2.10 and 5.2.20(5), printed pp.653--658.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Sporadic.Mathieu.M23Geometry GraphUniquenessSystem
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private def swapIntersection (P Q : Subgroup Sporadic.Mathieu.M23) :
    P.subgroupOf Q ≃* Q.subgroupOf P where
  toFun a := ⟨⟨a.val.val,a.property⟩,a.val.property⟩
  invFun a := ⟨⟨a.val.val,a.property⟩,a.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

omit [Finite G] in
/-- Align the actual vertex map on the full core while preserving the edge.
The same heptad map identifies H and its intersection with the edge. -/
theorem heptad_marked_vertex_core_alignment
    (J H X L : Subgroup G) (hHJ : H ≤ J) (hHX : H ≤ X)
    (hUH : J.pCoreIn 2 ≤ H)
    (ζ : J ≃* heptadStabilizer)
    (hcore : (pCore 2 J).map ζ.toMonoidHom = heptadKernel)
    (hζH : (H.subgroupOf J).map ζ.toMonoidHom =
      pairStabilizer.subgroupOf heptadStabilizer)
    (hζedge : ∀ r : H, (r : G) ∈ L ↔
      (ζ ⟨r,hHJ r.property⟩ : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup)
    (β : X ≃* pairStabilizer)
    (hβU : ((J.pCoreIn 2).subgroupOf X).map β.toMonoidHom =
      heptadKernelAmbient.subgroupOf pairStabilizer)
    (hβH : (H.subgroupOf X).map β.toMonoidHom =
      heptadStabilizer.subgroupOf pairStabilizer)
    (hβedge : ∀ a : X, (a : G) ∈ L ↔
      (β a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup) :
    ∃ β' : X ≃* pairStabilizer,
      (H.subgroupOf X).map β'.toMonoidHom = heptadStabilizer.subgroupOf pairStabilizer ∧
      (∀ (u : X) (hu : (u : G) ∈ J.pCoreIn 2),
        (β' u : Sporadic.Mathieu.M23) =
          (ζ ⟨u,pCoreIn_le 2 J hu⟩ : Sporadic.Mathieu.M23)) ∧
      ∀ a : X, (a : G) ∈ L ↔
        (β' a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup := by
  let D := pairStabilizer.subgroupOf heptadStabilizer
  let N := heptadKernel.subgroupOf D
  let E := (standardSystem.edgeGroup.subgroupOf heptadStabilizer).subgroupOf D
  let e : H ≃* D := (subgroupOfEquivOfLe hHJ).symm.trans
    ((ζ.subgroupMap (H.subgroupOf J)).trans (MulEquiv.subgroupCongr hζH))
  let b : H ≃* D := (subgroupOfEquivOfLe hHX).symm.trans
    ((β.subgroupMap (H.subgroupOf X)).trans ((MulEquiv.subgroupCongr hβH).trans
      (swapIntersection heptadStabilizer pairStabilizer)))
  have he (r : H) : (e r).val.val = (ζ ⟨r,hHJ r.property⟩ : Sporadic.Mathieu.M23) := rfl
  have hb (r : H) : (b r).val.val = (β ⟨r,hHX r.property⟩ : Sporadic.Mathieu.M23) := rfl
  have heN (r : H) : e r ∈ N ↔ (r : G) ∈ J.pCoreIn 2 := by
    change ζ ⟨r,hHJ r.property⟩ ∈ heptadKernel ↔ _
    rw [←hcore]
    exact (mem_map_iff_mem (f := ζ.toMonoidHom) ζ.injective
      (K := pCore 2 J) (x := ⟨r,hHJ r.property⟩)).trans
      (mem_map_iff_mem (f := J.subtype) J.subtype_injective
        (K := pCore 2 J) (x := ⟨r,hHJ r.property⟩)).symm
  have hbN (r : H) : b r ∈ N ↔ (r : G) ∈ J.pCoreIn 2 := by
    have hh := mem_map_iff_mem (f := β.toMonoidHom) β.injective
      (K := (J.pCoreIn 2).subgroupOf X) (x := ⟨r,hHX r.property⟩)
    rw [hβU] at hh
    have hk := mem_map_iff_mem (f := heptadStabilizer.subtype)
      heptadStabilizer.subtype_injective (K := heptadKernel) (x := (b r).val)
    exact hk.symm.trans hh
  have heE (r : H) : e r ∈ E ↔ (r : G) ∈ L := (hζedge r).symm
  have hbE (r : H) : b r ∈ E ↔ (r : G) ∈ L := (hβedge ⟨r,hHX r.property⟩).symm
  let α := b.symm.trans e
  have hαN : N.map α.toMonoidHom = N := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨u,hu,rfl⟩
      obtain ⟨r,rfl⟩ := b.surjective u
      change e (b.symm (b r)) ∈ N
      rw [b.symm_apply_apply]
      exact (heN r).mpr ((hbN r).mp hu)
    · rw [card_map_of_injective α.injective]
  have hαE : E.map α.toMonoidHom = E := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨u,hu,rfl⟩
      obtain ⟨r,rfl⟩ := b.surjective u
      change e (b.symm (b r)) ∈ E
      rw [b.symm_apply_apply]
      exact (heE r).mpr ((hbE r).mp hu)
    · rw [card_map_of_injective α.injective]
  obtain ⟨g,hgn,hg⟩ := heptad_pair_core_automorphism_realized_preserving_edge α hαN hαE
  let gp : pairStabilizer := ⟨g.val.val,g.property⟩
  let β' := β.trans (MulAut.conj gp)
  have hgH : gp ∈ heptadStabilizer.subgroupOf pairStabilizer := g.val.property
  refine ⟨β',?_,?_,?_⟩
  · change (H.subgroupOf X).map ((MulAut.conj gp).toMonoidHom.comp β.toMonoidHom) = _
    rw [←map_map,hβH]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((heptadStabilizer.subgroupOf pairStabilizer).le_normalizer hgH)
  · intro u hu
    let r : H := ⟨u,hUH hu⟩
    have hr := hg ⟨(b r).val,(hbN r).mpr hu⟩
    have hh := congrArg Subtype.val hr
    change (e (b.symm (b r))).val.val = _ at hh
    rw [b.symm_apply_apply] at hh
    exact hh.symm
  · intro a
    exact (hβedge a).trans (mem_normalizer_iff.mp hgn (β a : Sporadic.Mathieu.M23))


omit [Finite G] in
/-- The same local orbit marking identifies the entire edge intersection,
by comparing each endpoint with its marked translate. -/
theorem heptad_marked_edge_of_orbit
    {V : Type*} [MulAction G V] (U : System G V) (J : Subgroup G)
    (ζ : J ≃* heptadStabilizer)
    (horbit : ∀ a b : J, a • U.x = b • U.x ↔ ζ a • x.val = ζ b • x.val)
    (t : J) (ht : t • U.x = U.y) (htn : ζ t • x.val = y.val) (a : J) :
    (a : G) ∈ U.edgeGroup ↔
      (ζ a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup := by
  have hx := horbit a 1
  simp only [map_one,one_smul] at hx
  have hy := horbit (a*t) t
  simp only [mul_smul,ht,map_mul,htn] at hy
  rw [standardSystem_edgeGroup]
  exact and_congr hx hy

/-- Source 5.2.10, the nonmaximal linear branch: the original ambient group
is actually isomorphic to M23. Both overlap maps and the whole exceptional core
are aligned before uniqueness-system recognition is applied. -/
theorem Preparation.linear_nonmaximal_m23_equiv
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    Nonempty (G ≃* Sporadic.Mathieu.M23) := by
  obtain ⟨J,hJ,hKJ,U,ζ,hUJ,β,hx,hv,he0,hcore,hK,hHm,hMm,hIm,hvM,hedgeM,hesM,
    horbit,ht,hrigid,hcoreEdge,hβedge,hβlinear,hβU,hβH⟩ :=
    d.linear_nonmaximal_coset_core_placement h hH hp F hm hF he hnonmax
  have hXJ : U.vertexGroup ⊓ J = H := by
    rw [hv]
    exact d.linear_exceptional_pair_intersection h hH hp F hm hF he hJ hKJ
  have hHJ : H ≤ J := hXJ.ge.trans inf_le_right
  have hHX : H ≤ U.vertexGroup := hXJ.ge.trans inf_le_left
  have hUH : J.pCoreIn 2 ≤ H := by
    exact (le_inf (hcoreEdge.trans (inf_le_right.trans inf_le_left))
      (pCoreIn_le 2 J)).trans_eq hXJ
  obtain ⟨t,htI,ht,htn⟩ := ht
  have hζedge (r : H) : (r : G) ∈ U.edgeGroup ↔
      (ζ ⟨r,hHJ r.property⟩ : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup :=
    heptad_marked_edge_of_orbit U J ζ horbit t ht htn ⟨r,hHJ r.property⟩
  obtain ⟨β',hβH',hβcore',hβedge'⟩ := heptad_marked_vertex_core_alignment
    J H U.vertexGroup U.edgeGroup hHJ hHX hUH ζ hcore hHm hζedge β hβU hβH hβedge
  obtain ⟨e,_⟩ := heptad_marked_recognition_of_normalizer_core_comparison
    U J H hUJ hXJ ζ hcore hcoreEdge hIm hvM hesM hrigid β' hβH' hβcore' hβedge'
  exact ⟨e⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
