module

public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.SourceContainment.Actor
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import CFSG.Quasithin.ChapterG.Section02.CentralClosure
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreGeometry

/-!
# The original plane specialization of G.2

The actual plane actor together with T has no invariant subgroup strictly
between V₂ and V. A possible hyperplane is V₁-perpendicular by the native
Sylow action; its invariance would make the cubic plane actor fix V₁,
contrary to the marked pair rotation. This supplies the original G.2
hypothesis and hence puts the plane conjugate closure in O₂(N_G(V₂)),
with Frattini subgroup and commutator in V₂.

The final theorem applies this closure to an actual conjugator in N_G(V₂).
No global plane-fusion statement is an input or conclusion.
Source: Aschbacher--Smith, 13.5.6(1) and the G.2 step, printed p.917.
-/

@[expose] public section
open Subgroup BinaryPermutation Module Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry
open Section08.SourceCompletion Section07.NaturalAction TwoBlocks
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry NaturalPairing
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

private theorem image_normalized (A:Subgroup G) (hA:A≤V) (l:L)
    (hl:l.val∈normalizer (A:Set G)) :
    move (localMap d l) (image d A)=image d A := by
  have h:=QuadraticSource.image_conjugate_by_local d A hA
    (inclusion (QuadraticSource.L_le_local d) l)
  change image d (A.map (MulAut.conj l.val).toMonoidHom)=
    move (QuadraticSource.permutation d (inclusion (QuadraticSource.L_le_local d) l)) (image d A) at h
  rw [←localMap_eq_full d l] at h
  have he:A.map (MulAut.conj l.val).toMonoidHom=A:=mem_normalizer_iff_map_conj_eq.mp hl
  rw [he] at h
  exact h.symm

theorem planeActor_not_normalizes_line :
    ¬planeActor (L:=L) (V₂:=V₂)≤normalizer (V₁:Set G) := by
  intro hn
  obtain ⟨a,ha,hp⟩:=QuadraticSource.source_even_flag d
  have hr:(planeLocalMap d).range=L2.map (MulAut.conj a.val).toMonoidHom := by
    rw [planeLocalMap_range d,planeLocal_image d,hp,flagStabilizer_move,flagStabilizer_plane]
    rw [L2,Subgroup.map_inf _ _ _ (MulAut.conj a.val).injective,conjugate_alternating]
  have hR:(pResidual 2 (planeLocal (L:=L) (V₂:=V₂))).map (planeLocalMap d)=
      ((pResidual 2 L2).map L2.subtype).map (MulAut.conj a.val).toMonoidHom := by
    have hh:=map_embedded_pResidual 2 (⊤:Subgroup (planeLocal (L:=L) (V₂:=V₂))) (planeLocalMap d)
    rw [←MonoidHom.range_eq_map,hr,←map_embedded_pResidual] at hh
    have ht:(pResidual 2 (⊤:Subgroup (planeLocal (L:=L) (V₂:=V₂)))).map
        (⊤:Subgroup (planeLocal (L:=L) (V₂:=V₂))).subtype=
        pResidual 2 (planeLocal (L:=L) (V₂:=V₂)):=
      map_pResidual_of_surjective 2 _ topEquiv.surjective
    rwa [ht] at hh
  have hm:pairRotation∈(pResidual 2 L2).map L2.subtype := by
    let r:L2:=⟨pairRotation,pairRotation_mem_H2,by change Equiv.Perm.sign _=1;decide⟩
    have hpow:r^3=1:=Subtype.ext (show pairRotation^3=1 by decide)
    exact ⟨r,mem_pResidual_of_orderOf_coprime
      (Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hpow) (by decide)),rfl⟩
  have hm':(MulAut.conj a.val) pairRotation∈
      (pResidual 2 (planeLocal (L:=L) (V₂:=V₂))).map (planeLocalMap d):=
    hR.symm ▸ mem_map_of_mem _ hm
  obtain ⟨r,hrR,her⟩:=hm'
  have hl:move ((MulAut.conj a.val) pairRotation) (move a.val canonicalLine)=move a.val canonicalLine:=by
    rw [←ha,←her]
    exact image_normalized d V₁
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le))
      ⟨r.val,r.property.1⟩ (hn (mem_map_of_mem _ hrR))
  have hh:move pairRotation canonicalLine=canonicalLine:=by
    rw [move_conjugate] at hl
    exact (move_injective a.val) hl
  exact (by decide : pairRotation∉H1) ((canonicalLine_stabilizer pairRotation).mp hh)

private theorem stable_hyperplane (A:Subgroup G) (_hA:A≤V)
    (hd:finrank (ZMod 2) (image d A)=3)
    (hT:(T:Subgroup G)≤normalizer (A:Set G)) :
    image d A=form.orthogonal (image d V₁) := by
  let f:=Section07.NaturalAction.permutation d
  let Q:=(T.subtype (show (T:Subgroup G)≤L⊔T from le_sup_right)).mapSurjective
    f.rangeRestrict_surjective
  have hQ:(Q:Subgroup f.range).map f.range.subtype=
      ((T:Subgroup G).subgroupOf (L⊔T)).map f:=by
    rw [Sylow.coe_mapSurjective,map_map,Sylow.coe_subtype]
    rfl
  apply NaturalHyperplanes.sylow_invariant_hyperplane_eq_orthogonal
    f.range (alternating_le_range d) Q (image d V₁) (image d A)
    (image_dim d V₁ (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) 1 d.line_card) hd
  · rw [hQ];exact image_stable d V₁ d.line_stable
  · rw [hQ];exact image_stable d A hT

theorem source_plane_interval (A:Subgroup G) (hPA:V₂≤A) (hAV:A≤V)
    (hn:planeActor (L:=L) (V₂:=V₂)⊔(T:Subgroup G)≤normalizer (A:Set G)) :
    A=V₂ ∨ A=V := by
  have hle:image d V₂≤ image d A:=by
    rintro w ⟨v,hv,rfl⟩;exact ⟨v,hPA hv,rfl⟩
  have hdim:2≤finrank (ZMod 2) (image d A):=by
    simpa only [image_dim d V₂ (d.plane_le_seed.trans d.seed_le) 2 d.plane_card] using
      Submodule.finrank_mono hle
  have hup:finrank (ZMod 2) (image d A)≤4:=by
    simpa [finrank_natural_even (Fin 6) (by decide)] using Submodule.finrank_le (image d A)
  have hcases:finrank (ZMod 2) (image d A)=2 ∨
      finrank (ZMod 2) (image d A)=3 ∨ finrank (ZMod 2) (image d A)=4:=by omega
  rcases hcases with h2|h3|h4
  · left
    apply QuadraticSource.image_injective_on_subgroups d hAV (d.plane_le_seed.trans d.seed_le)
    exact (Submodule.eq_of_le_of_finrank_eq hle
      ((image_dim d V₂ (d.plane_le_seed.trans d.seed_le) 2 d.plane_card).trans h2.symm)).symm
  · exfalso
    apply planeActor_not_normalizes_line d
    intro x hx
    have hxL:x∈L:=(planeActor_le.trans inf_le_left) hx
    have hs:=stable_hyperplane d A hAV h3 (le_sup_right.trans hn)
    have hm:move (localMap d ⟨x,hxL⟩) (image d V₁)=image d V₁:=by
      have hh:=orthogonal_invariant (image d A) (localMap d ⟨x,hxL⟩)
        (image_normalized d A hAV ⟨x,hxL⟩ (hn (mem_sup_left hx)))
      rwa [hs,LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate form_alt.isRefl] at hh
    have hh:=normalizes_plane_of_localMap_stabilizes d
      (zpowers (⟨x,hxL⟩:L)) V₁ (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le))
      ((Subgroup.map_le_iff_le_comap).mpr (zpowers_le.mpr ((mem_stabilizer_iff_map _ _).mpr hm)))
    exact hh (mem_map_of_mem _ (mem_zpowers (⟨x,hxL⟩:L)))
  · right
    have he:image d A=⊤:=Submodule.eq_top_of_finrank_eq
      (h4.trans (finrank_natural_even (Fin 6) (by decide)).symm)
    apply le_antisymm hAV
    intro v hv
    have hm:(d.coordinate ⟨v,hv⟩).toAdd∈image d A:=he.symm ▸ Submodule.mem_top
    obtain ⟨w,hw,heq⟩:=hm
    have hwv:w=⟨v,hv⟩:=d.coordinate.injective heq
    change w.val∈A at hw
    simpa only [hwv] using hw

def planeSetup : ChapterG.Section02.Setup G where
  V:=V
  V₁:=V₂
  L:=L
  T:=T
  H:=normalizer (V₂:Set G)

theorem source_plane_g2 : (planeSetup (T:=T) (L:=L) (V:=V) (V₂:=V₂)).Hypothesis := by
  have hn:V₂≠⊥:=by
    intro he
    have hc:=d.plane_card
    rw [he,card_bot] at hc
    contradiction
  have hp:IsPGroup 2 V₂:=T.isPGroup'.to_le
    (d.plane_le_seed.trans (d.seed_le.trans d.chosen.le_sylow))
  have hc:generalizedFitting (normalizer (V₂:Set G))=pCore 2 (normalizer (V₂:Set G)):=by
    apply generalizedFitting_eq_pCore_of_selfCentralizing 2
    apply Chapter1.mem_He_iff.mp
    exact Chapter1.twoLocal_mem_He_of_sylow_le T
      (d.counterexample.qtke.evenCharacteristic T) ⟨V₂,hn,hp,rfl⟩ d.plane_stable
  refine {
    elementary:=elementary d
    point_ne_bot:=hn
    point_le:=d.plane_le_seed.trans d.seed_le
    residual:=(pResidual_eq_top_iff 2 L).mpr d.counterexample.local_component.2.1.2.1
    V_le_T:=d.chosen.le_sylow
    T_normalizes_point:=d.plane_stable
    T_normalizes_V:=le_sup_right.trans d.normalizes_V
    T_normalizes_L:=d.normalizes_L
    sylow_LT:=⟨T.subtype (show (T:Subgroup G)≤L⊔T from le_sup_right),
      map_subgroupOf_eq_of_le (show (T:Subgroup G)≤L⊔T from le_sup_right)⟩
    H_le:=le_rfl
    local_le:=sup_le (planeActor_le.trans inf_le_right) d.plane_stable
    sylow_H:=⟨T.subtype d.plane_stable,map_subgroupOf_eq_of_le d.plane_stable⟩
    characteristic_two:=hc
    local_normalizes_V:=sup_le
      ((planeActor_le.trans inf_le_left).trans (le_sup_left.trans d.normalizes_V))
      (le_sup_right.trans d.normalizes_V)
    quotient_nonzero:=?_
    irreducible:=source_plane_interval d }
  intro he
  have hcard:Nat.card V₃≤Nat.card V₂:=
    Nat.card_le_card_of_injective (inclusion (d.seed_le.trans he.symm.le))
      (inclusion_injective _)
  rw [d.seed_card,d.plane_card] at hcard
  omega

theorem source_plane_closure_le_core :
    conjugateSpanBy V (normalizer (V₂:Set G))≤(normalizer (V₂:Set G)).pCoreIn 2 := by
  have h:=source_plane_g2 d
  exact le_pCoreIn_of_normalizes h.U_isPGroup h.U_le_H (le_normalizer_conjugateSpanBy _ _)

theorem source_module_le_plane_core : V≤(normalizer (V₂:Set G)).pCoreIn 2 :=
  (le_conjugateSpanBy _ _).trans (source_plane_closure_le_core d)

theorem source_plane_closure_frattini :
    (frattini (conjugateSpanBy V (normalizer (V₂:Set G)))).map
      (conjugateSpanBy V (normalizer (V₂:Set G))).subtype≤V₂ :=
  (source_plane_g2 d).frattini_U_le_point

theorem source_plane_closure_le_sylow :
    conjugateSpanBy V (normalizer (V₂:Set G))≤(T:Subgroup G) :=
  (source_plane_g2 d).U_normal_in_T.1

theorem source_plane_closure_normalizes_module :
    conjugateSpanBy V (normalizer (V₂:Set G))≤normalizer (V:Set G) :=
  (source_plane_closure_le_sylow d).trans (le_sup_right.trans d.normalizes_V)

theorem source_plane_closure_commutator :
    ⁅conjugateSpanBy V (normalizer (V₂:Set G)),
      conjugateSpanBy V (normalizer (V₂:Set G))⁆≤V₂ := by
  let U:=conjugateSpanBy V (normalizer (V₂:Set G))
  let : Fact (IsPGroup 2 U):=⟨(source_plane_g2 d).U_isPGroup⟩
  have hh:=map_mono (f:=U.subtype) (commutator_le_frattini_of_isPGroup (R:=U) (p:=2))
  rw [map_subtype_commutator] at hh
  exact hh.trans (source_plane_closure_frattini d)

theorem source_plane_normalizer_conjugate (g:G) (hg:g∈normalizer (V₂:Set G)) :
    V.map (MulAut.conj g).toMonoidHom≤normalizer (V:Set G) ∧
    ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V₂ := by
  have hv:V.map (MulAut.conj g).toMonoidHom≤conjugateSpanBy V (normalizer (V₂:Set G)):=by
    rintro _ ⟨v,hv,rfl⟩
    exact (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy V _ hg) v).mp
      (le_conjugateSpanBy _ _ hv)
  exact ⟨hv.trans (source_plane_closure_normalizes_module d),
    (commutator_mono (le_conjugateSpanBy _ _) hv).trans (source_plane_closure_commutator d)⟩

end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry
