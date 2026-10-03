module
public import Stellmacher.SectionThree.ArbitrarySylowCommutatorSupplement
public import Stellmacher.SectionEight.LocalQuotientOddCoreSupplement
public import Stellmacher.SectionNine.DistanceOneImagePreparation

/-!
# The relative odd commutator and the full edge generate the initial quotient

For the original distance-one action data and any supplied faithful quotient
of the initial stabilizer acting on its center, let `X` be the image of the
actual crossed-center product and `F=[O₂′(bar G),X]`. Then `F` together with
the image of the full edge stabilizer generates the quotient.

The crossed-center product is a two-group inside the full edge stabilizer,
and source (4) keeps it outside the initial two-core. Conjugate this subgroup
inside the edge into the distinguished Sylow subgroup. The arbitrary-Sylow-
subgroup consequence of (3.4) makes its commutator with the initial residual
supplement the Sylow subgroup. Conjugating back gives generation with the
full edge. Mapping this equality through the supplied projection, the proved
containment of the residual image in the quotient's odd core gives the result.

This is the generation assertion in Stellmacher (9.1)(8), Journal of Algebra
190 (1997), p.47, `refs/files/stellmacher-n-group.pdf`. It precedes the fixed
complement elimination and assumes neither the final faithful classification
nor containment or normality of the crossed product in the chosen Sylow.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix Subgroup
open scoped Pointwise
universe u

private theorem exists_conjugate_le_sylow_in_overgroup
    {G : Type*} [Group G] [Finite G] (P K S V : Subgroup G)
    (hKP : K ≤ P) (hSK : S ≤ K) (hVP : V ≤ K)
    (hSyl : IsSylowTwoIn S P) (hV : IsPGroup 2 V) :
    ∃ k : K, V.map (MulAut.conj (k : G)).toMonoidHom ≤ S := by
  obtain ⟨hSP, sylow, hsylow⟩ := hSyl
  let KP := K.subgroupOf P
  have hSylK : (sylow : Subgroup P) ≤ KP := by
    intro s hs
    exact hSK (hsylow ▸ mem_map_of_mem P.subtype hs)
  let e := subgroupOfEquivOfLe hKP
  let sylK : Sylow 2 K := (sylow.subtype hSylK).mapSurjective
    (f := e.toMonoidHom) e.surjective
  have hsylK : (sylK : Subgroup K).map K.subtype = S := by
    change (((sylow.subtype hSylK : Sylow 2 KP) : Subgroup KP).map e.toMonoidHom).map K.subtype = S
    rw [Subgroup.map_map]
    have hf : K.subtype.comp e.toMonoidHom = P.subtype.comp KP.subtype := by ext x; rfl
    rw [hf, ← Subgroup.map_map, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hSylK, hsylow]
  have hVKp : IsPGroup 2 (V.subgroupOf K) := hV.of_equiv (subgroupOfEquivOfLe hVP).symm
  obtain ⟨Q, hQ⟩ := hVKp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K Q sylK
  refine ⟨k, ?_⟩
  rintro x ⟨v, hv, rfl⟩
  have hvQ : (⟨v,hVP hv⟩ : K) ∈ Q := hQ hv
  have hconj : (MulAut.conj k) (⟨v,hVP hv⟩ : K) ∈ sylK := by
    rw [← hk]
    change (MulAut.conj k) • (⟨v,hVP hv⟩ : K) ∈ (MulAut.conj k) • (Q : Set K)
    exact Set.smul_mem_smul_set hvQ
  rw [← hsylK]
  exact mem_map_of_mem K.subtype hconj

private theorem residual_commutator_sup_overgroup
    {G : Type*} [Group G] [Finite G]
    (S : Subgroup G) (h : SectionThree.Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ SectionThree.PSet ⊤ S) (hsolv : Group.IsSolvable P)
    (K V : Subgroup G) (hKP : K ≤ P) (hSK : S ≤ K)
    (hVK : V ≤ K) (hVp : IsPGroup 2 V) (hnot : ¬ V ≤ twoCoreAmbient P) :
    ⁅twoResidualAmbient P,V⁆ ⊔ K = P := by
  classical
  obtain ⟨k,hk⟩ := exists_conjugate_le_sylow_in_overgroup P K S V hKP hSK hVK
    ⟨hSK.trans hKP,hP.1.2.1⟩ hVp
  let f := (MulAut.conj (k : G)).toMonoidHom
  have hkP : (k : G) ∈ P := hKP k.property
  have hPm : P.map f = P := mem_normalizer_iff_map_conj_eq.mp (P.le_normalizer hkP)
  have hKm : K.map f = K := mem_normalizer_iff_map_conj_eq.mp (K.le_normalizer k.property)
  have hQm : (twoCoreAmbient P).map f = twoCoreAmbient P := by
    exact mem_normalizer_iff_map_conj_eq.mp
      (((normal_subgroupOf_iff_le_normalizer (twoCoreIn_le P)).mp
        (twoCoreIn_normal P)) hkP)
  have hRm : (twoResidualAmbient P).map f = twoResidualAmbient P :=
    map_twoResidualAmbient_of_subgroup_image P f P hPm
  have hVnot : ¬ V.map f ≤ twoCoreAmbient P := by
    intro hh
    apply hnot
    rw [← hQm] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj (k : G)).injective).mp hh
  have hgen := SectionThree.residual_commutator_sup_sylow_of_not_le_core
    S h P hP hsolv (V.map f) hk hVnot
  have hgenK : ⁅twoResidualAmbient P,V.map f⁆ ⊔ K = P :=
    le_antisymm (sup_le ((Subgroup.commutator_le_sup _ _).trans
      (sup_le (map_subtype_le _) (hk.trans (hSK.trans hKP)))) hKP)
      (hgen.symm.le.trans (sup_le_sup_left hSK _))
  apply Subgroup.map_injective (f := f) (MulAut.conj (k : G)).injective
  rw [Subgroup.map_sup, map_commutator, hRm, hKm, hPm]
  exact hgenK

/-- The actual relative odd commutator together with the full edge image
covers the supplied faithful initial quotient. -/
public theorem distance_one_relative_commutator_sup_edge
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneActionData ctx)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer
        (ZAt ctx.Γ ctx.criticalPath.a : Set G)) (ZAt ctx.Γ ctx.criticalPath.a)) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
      (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
    let edge := stabilizer ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ ctx.criticalPath.a'
    let _ := w.groupX
    let X := (V.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection
    ⁅SectionOne.oddCore w.X,X⁆ ⊔
      (edge.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection = ⊤ := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let next := Γ.act data.x⁻¹ cp.a
  let C := z Γ cp.a ⊓ stabilizer Γ next
  let D := z Γ next ⊓ stabilizer Γ cp.a
  let V := C ⊔ D
  let edge := stabilizer Γ cp.a ⊓ stabilizer Γ cp.a'
  let _ := w.groupX
  let _ := w.finiteX
  have hlen : cp.length = 1 := hb
  have hstep : cp.firstStep = cp.a' := by
    calc
      cp.firstStep = cp.path ⟨1,by omega⟩ := cp.path_first.symm
      _ = cp.path ⟨cp.length,Nat.lt_succ_self _⟩ := by congr 1; apply Fin.ext; exact hb.symm
      _ = cp.a' := cp.path_end
  have hVedge : V ≤ edge := by
    refine le_inf ((distance_one_product_factors Γ cp.a next).2.2.1.trans inf_le_left) ?_
    have hVE : V ≤ data.E := by
      rw [data.generated]
      exact sup_le_sup inf_le_left inf_le_left
    exact hVE.trans data.E_le
  have hTP : T ≤ edge := by
    change T ≤ stabilizer Γ cp.a ⊓ stabilizer Γ cp.a'
    rw [← hstep]
    exact cp.S_le_edge_stabilizers
  have hneigh : cp.a' ∈ neighborhood Γ cp.a := by
    rw [neighborhood,Γ.neighbors_def]
    exact (Γ.distance_symm _ _).trans (cp.endpoint_distance.trans hb)
  let _ := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hneigh
  have hZnext : z Γ next = (z Γ cp.a).map (MulAut.conj data.x).toMonoidHom := by
    rw [z_act,inv_inv]
  let _ : IsElementaryAbelian 2 (z Γ next) := by
    rw [hZnext]
    exact IsElementaryAbelian.map (MulAut.conj data.x).toMonoidHom
  have hCp : IsPGroup 2 C := (IsElementaryAbelian.isPGroup 2 (z Γ cp.a)).to_le inf_le_left
  have hDp : IsPGroup 2 D := (IsElementaryAbelian.isPGroup 2 (z Γ next)).to_le inf_le_left
  have hVp : IsPGroup 2 V := hCp.to_sup_of_normal_right' hDp
    (distance_one_product_factors Γ cp.a next).1
  have hnot : ¬ V ≤ twoCoreAmbient P := by
    intro hh
    have hbound := (distance_one_local_geometry ctx hb data).2.2
    change 4 * Nat.card (V ⊓ q Γ cp.a : Subgroup G) ≤ Nat.card V at hbound
    have hcore : twoCoreAmbient P = q Γ cp.a := by rw [q,Γ.twoCoreAt_def]; rfl
    rw [← hcore,inf_eq_left.mpr hh] at hbound
    have hpos : 0 < Nat.card V := Nat.card_pos
    omega
  have hgen := residual_commutator_sup_overgroup T (sectionThreeHypotheses ctx.sectionSeven)
    P ((pFamily_iff_pSet _ _ _).mp (edge_local_data ctx.sectionSeven Γ cp).1.1)
    (edge_local_data ctx.sectionSeven Γ cp).1.2 edge V inf_le_left hTP hVedge hVp hnot
  let R := twoResidualAmbient (⊤ : Subgroup P)
  have hRmap : R.map P.subtype = twoResidualAmbient P :=
    map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup P) P.subtype P
      (by rw [← MonoidHom.range_eq_map,range_subtype])
  have hnative : ⁅R,V.subgroupOf P⁆ ⊔ edge.subgroupOf P = ⊤ := by
    apply Subgroup.map_injective (f := P.subtype) P.subtype_injective
    rw [Subgroup.map_sup,map_commutator,hRmap,
      map_subgroupOf_eq_of_le (hVedge.trans inf_le_left),
      map_subgroupOf_eq_of_le inf_le_left, ← MonoidHom.range_eq_map,range_subtype]
    exact hgen
  have hmap := congrArg (Subgroup.map w.projection) hnative
  rw [Subgroup.map_sup,map_commutator,
    map_top_of_surjective w.projection w.surjective] at hmap
  apply top_unique
  rw [← hmap]
  exact sup_le_sup_right (Subgroup.commutator_mono
    (SectionEight.local_quotient_residual_image_le_oddCore ctx.sectionSeven Γ cp w) le_rfl) _

end Stellmacher.SectionNine
