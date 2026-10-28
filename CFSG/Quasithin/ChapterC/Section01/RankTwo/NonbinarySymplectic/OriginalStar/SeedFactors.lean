module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.MarkedImage
public import Theory.Representation.SymplecticFourOrthogonalCover.SylowSeedFactors

/-!
# Two original-radical-normal factors of the marked Sylow seed

The literal original natural cover splits its full component Sylow seed
into U intersect D and the displacement of its second central layer by the
component Sylow. The factors have orders at most q and exactly q, and their
intersection is trivial. The original odd-index witness selects a component
Sylow normalized by the original radical; this normalizes both factors.

If the characteristic star cut loses marked component image, transport
through the original holomorph selects one of these factors at a neighbor
of beta. It is normalized by the same original radical, has order at most
q, lies in Q_alpha, and is moved by Ltilde_alpha intersect Q_beta. Its
commutator with the full Q_alpha lies in the full fixed core D_alpha.
The alternative is the actual original star-saturation conclusion.

This proves the small-factor step in the opening of MS93 (3.7), printed
p.872, without a Sylow assumption on the original radical. The remaining
dual-module contradiction, marked preservation and field restriction are
not asserted here. The second central layer is taken with respect to the
selected component Sylow; its intrinsic definition proves the required
normalization even when the original radical has outer action.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

/-- The two source factors of the full original component Sylow seed. -/
theorem componentSylowSeed_factors
    {a : Vertex R} (ha : color R a=false) (P : Sylow 2 (Ltilde R a)) :
    let T := componentSylowActor R a P
    let B := componentSylowSeed R a P
    let A := U R a ⊓ fixedCore R a
    let X := commutatorPreimage (U R a) T B
    B=A ⊔ ⁅X,T⁆ ∧ Nat.card A ≤ Nat.card F ∧
      Nat.card (⁅X,T⁆ : Subgroup (FreeAmalgam R))=Nat.card F ∧ Disjoint A ⁅X,T⁆ := by
  obtain ⟨E,hE,e,he,j,hj,hjU,f,hf,hact,hker⟩ := h.initial_cover_at_vertex ha
  let C := K.map (QuotientGroup.mk' (pCore 2 H))
  let : C.Normal := h.component_image_structure.2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) (QuotientGroup.mk' (pCore 2 H))
    (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)) C
  let T := componentSylowActor R a P
  let actorEquiv : (P : Subgroup (Ltilde R a)) ≃* T :=
    (P : Subgroup (Ltilde R a)).equivMapOfInjective
      (Ltilde R a).subtype (Ltilde R a).subtype_injective
  let π : T →* L (K := E.Carrier) :=
    (f.comp (P : Subgroup (Ltilde R a)).subtype).comp actorEquiv.symm.toMonoidHom
  let := finite_stabilizer R a
  let : Finite (Ltilde R a) := Finite.of_injective
    (inclusion (Ltilde_le_stabilizer a)) (inclusion_injective _)
  let S := P.mapSurjective (f := f) hf
  have hπ : π.range=(S : Subgroup (L (K := E.Carrier))) := by
    change π.range=(P.mapSurjective (f := f) hf : Subgroup _)
    rw [Sylow.coe_mapSurjective,MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective actorEquiv.symm.toMonoidHom actorEquiv.symm.surjective,
      ←MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype]
  have hT (t : T) (v : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (π t) v))=
        (t : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(t : FreeAmalgam R)⁻¹ := by
    have hh := hact (actorEquiv.symm t) v
    have hval : ((actorEquiv.symm t : P) : FreeAmalgam R)=(t : FreeAmalgam R) :=
      congrArg Subtype.val (actorEquiv.apply_symm_apply t)
    exact hval ▸ hh
  obtain ⟨geometry,hpos,_⟩ := h.positive_even_geometry
  have hUQ : U R a ≤ Q R a := (U_le_Z _).trans
    ((geometry.omega_bound a ha (by rwa [geometry.distance_constant a ha])).trans (omegaCenter_le _))
  have hAk (v : s.space.toSubmodule) :
      j (Multiplicative.ofAdd v) ∈ U R a ⊓ fixedCore R a ↔ MovedSection.coverProjection s e v=0 := by
    have hvU : j (Multiplicative.ofAdd v) ∈ U R a := hjU ▸ ⟨_,rfl⟩
    exact ⟨fun hv => (hker v).mpr hv.2.2,fun hv => ⟨hvU,hUQ hvU,(hker v).mp hv⟩⟩
  have hh := embedded_sylow_seed_factors (U R a) T (U R a ⊓ fixedCore R a)
    j hj hjU π S hπ hT (MovedSection.coverProjection s e) he hAk inf_le_left
  have hcard : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  rwa [hcard] at hh

private theorem seed_factors_normalized
    {a : Vertex R} (ha : color R a=false) (P : Sylow 2 (Ltilde R a)) (N : Subgroup (FreeAmalgam R))
    (hNS : N ≤ stabilizer R a)
    (hNT : N ≤ normalizer (componentSylowActor R a P : Set (FreeAmalgam R))) :
    N ≤ normalizer (U R a ⊓ fixedCore R a : Set (FreeAmalgam R)) ∧
    N ≤ normalizer ((⁅commutatorPreimage (U R a) (componentSylowActor R a P)
      (componentSylowSeed R a P),componentSylowActor R a P⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  let : IsElementaryAbelian 2 (U R a) := h.vertex_moving_elementary ha
  let U₀ := U R a
  let T := componentSylowActor R a P
  let B := componentSylowSeed R a P
  have hNU : N ≤ normalizer (U₀ : Set (FreeAmalgam R)) := hNS.trans (U_normalized _)
  have hNL : N ≤ normalizer (Ltilde R a : Set (FreeAmalgam R)) := by
    have ht := le_normalizer_map (H := pResidual 2 (stabilizer R a)) (stabilizer R a).subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at ht
    exact hNS.trans ht
  have hND : N ≤ normalizer (fixedCore R a : Set (FreeAmalgam R)) :=
    (le_inf (hNS.trans (Q_normalized R a))
      (hNL.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hNB : N ≤ normalizer (B : Set (FreeAmalgam R)) :=
    (le_inf hNU (hNT.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hUB : U₀ ≤ normalizer (B : Set (FreeAmalgam R)) := by
    have hUc : U₀ ≤ centralizer (U₀ : Set (FreeAmalgam R)) :=
      le_centralizer_iff_isMulCommutative.mpr inferInstance
    exact (hUc.trans (centralizer_le inf_le_left)).trans (centralizer_le_normalizer _)
  have hNX := commutatorPreimage_normalized U₀ T B N hUB hNU hNT hNB
  refine ⟨(le_inf hNU hND).trans inf_normalizer_le_normalizer_inf,?_⟩
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hNX hx),mem_normalizer_iff_map_conj_eq.mp (hNT hx)]


/-- The original source star either is saturated, or loses marked image on
an actual original-radical-normal factor of order at most q. The whole
fixed attachment and the literal component--radical actor are retained. -/
theorem exists_source_star_saturation_or_moved_small_factor :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R,
      Y.map (embedS R)=componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      ((let Tstar := (starCentralizer R Y).map R.subtype
        let Mstar := K ⊔ Tstar
        Tstar.subgroupOf Mstar=R.subgroupOf Mstar ∧
          (normalizer (Tstar.subgroupOf Mstar : Set Mstar)).pCoreIn 2=
            Tstar.subgroupOf Mstar) ∨
        ∃ δ : Vertex R, ∃ Pδ : Sylow 2 (Ltilde R δ), ∃ J : Subgroup (FreeAmalgam R),
          color R δ=false ∧ Adjacent R δ (beta R) ∧
          J ≤ componentSylowSeed R δ Pδ ∧
          componentSylowSeed R δ Pδ ≤ (starSpan R Y).map (embedS R) ∧
          J ≤ Q R (alpha R) ∧
          Q R (beta R) ≤ normalizer (J : Set (FreeAmalgam R)) ∧
          Nat.card J ≤ Nat.card F ∧
          ⁅J,Ltilde R (alpha R) ⊓ Q R (beta R)⁆ ≠ ⊥ ∧
          ⁅J,Q R (alpha R)⁆ ≤ fixedCore R (alpha R)) := by
  classical
  obtain ⟨geometry,hpos,_⟩ := h.positive_even_geometry
  obtain ⟨P,hTP,_⟩ := exists_vertex_sylow h
  let T := componentSylowActor R (alpha R) P
  let B := componentSylowSeed R (alpha R) P
  let A := U R (alpha R) ⊓ fixedCore R (alpha R)
  let D := ⁅commutatorPreimage (U R (alpha R)) T B,T⁆
  have hUQ : U R (alpha R) ≤ Q R (alpha R) :=
    (U_le_Z _).trans ((geometry.omega_bound _ rfl
      (by rwa [geometry.distance_constant _ rfl])).trans (omegaCenter_le _))
  have hBR : B ≤ Q R (beta R) :=
    (inf_le_left.trans hUQ).trans (Q_le_adjacent_h R rfl (base_adjacent R))
  have hRS : Q R (beta R) ≤ stabilizer R (alpha R) :=
    fun _ hx => hx.2 _ (adjacent_symm _ (base_adjacent _))
  have hnB : Q R (beta R) ≤ normalizer (B : Set (FreeAmalgam R)) :=
    (le_inf (hRS.trans (U_normalized _))
      (hTP.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  let Y := B.comap (embedS R)
  have hY : Y.map (embedS R)=B := by
    apply map_comap_eq_self
    rw [←embedM_comp_subtype,MonoidHom.range_comp,range_subtype]
    simpa only [Q_beta] using hBR
  have hnY : Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) := by
    rwa [hY]
  refine ⟨P,Y,hY,hnY,?_⟩
  by_cases hm : (((starCentralizer R Y).map R.subtype).subgroupOf K).map
      (DistanceTwoRecognition.componentProjection h)=(R.subgroupOf K).map
        (DistanceTwoRecognition.componentProjection h)
  · exact Or.inl (star_radical_saturated_of_marked_image_eq h geometry hpos P Y hY hnY hm)
  · obtain ⟨k,hmove⟩ := exists_moved_holomorph_seed_of_marked_image_ne h Y hm
    obtain ⟨he,hAc,hDc,_⟩ := componentSylowSeed_factors h (a := alpha R) rfl P
    change B=A ⊔ D at he
    change Nat.card A ≤ Nat.card F at hAc
    change Nat.card D=Nat.card F at hDc
    obtain ⟨hNA,hND⟩ := seed_factors_normalized h rfl P (Q R (beta R)) hRS hTP
    let φ := (MulAut.conj (k : FreeAmalgam R)).toMonoidHom
    let A' := A.map φ
    let D' := D.map φ
    have he' : B.map φ=A' ⊔ D' := by rw [he,Subgroup.map_sup]
    have hkb : (k : FreeAmalgam R) ∈ stabilizer R (beta R) := by
      simpa only [beta,stabilizer_h_base] using k.property
    have hfix : act R (k : FreeAmalgam R)⁻¹ (beta R)=beta R :=
      (stabilizer R (beta R)).inv_mem hkb
    have hnA' : Q R (beta R) ≤ normalizer (A' : Set (FreeAmalgam R)) := by
      simpa only [hfix,inv_inv] using
        map_seed_normalized_at_act R A hNA (k : FreeAmalgam R)⁻¹
    have hnD' : Q R (beta R) ≤ normalizer (D' : Set (FreeAmalgam R)) := by
      simpa only [hfix,inv_inv] using
        map_seed_normalized_at_act R D hND (k : FreeAmalgam R)⁻¹
    have hcA' : Nat.card A' ≤ Nat.card F := by
      rw [←Nat.card_congr (A.equivMapOfInjective φ (MulAut.conj _).injective).toEquiv]
      exact hAc
    have hcD' : Nat.card D' ≤ Nat.card F := by
      rw [←Nat.card_congr (D.equivMapOfInjective φ (MulAut.conj _).injective).toEquiv,hDc]
    have hmv : ⁅A' ⊔ D',Ltilde R (alpha R) ⊓ Q R (beta R)⁆ ≠ ⊥ := by
      rw [←he']
      simpa only [hY] using hmove
    have hchoose : ∃ J : Subgroup (FreeAmalgam R), J ≤ B.map φ ∧
        Q R (beta R) ≤ normalizer (J : Set (FreeAmalgam R)) ∧
        Nat.card J ≤ Nat.card F ∧
        ⁅J,Ltilde R (alpha R) ⊓ Q R (beta R)⁆ ≠ ⊥ := by
      by_cases ha : ⁅A',Ltilde R (alpha R) ⊓ Q R (beta R)⁆=⊥
      · refine ⟨D',he'.symm ▸ le_sup_right,hnD',hcD',?_⟩
        intro hd
        exact hmv (commutator_eq_bot_iff_le_centralizer.mpr
          (sup_le (commutator_eq_bot_iff_le_centralizer.mp ha)
            (commutator_eq_bot_iff_le_centralizer.mp hd)))
      · exact ⟨A',he'.symm ▸ le_sup_left,hnA',hcA',ha⟩
    obtain ⟨J,hJB,hnJ,hcJ,hmJ⟩ := hchoose
    obtain ⟨Pδ,hPδ⟩ := exists_componentSylowSeed_act R (alpha R) P (k : FreeAmalgam R)⁻¹
    simp only [inv_inv] at hPδ
    have hs : B.map φ ≤ (starSpan R Y).map (embedS R) := by
      have heq : (starSpan R Y).map (embedS R)=
          (⨆ k : Hbar R, (Y.map (embedS R)).map
            (MulAut.conj (k : FreeAmalgam R)).toMonoidHom) ⊔ Z R (beta R) := by
        simpa only [map_map,embedM_comp_subtype] using starSpan_map_graph R Y
      rw [heq,←hY]
      exact (le_iSup (fun k : Hbar R => (Y.map (embedS R)).map
        (MulAut.conj (k : FreeAmalgam R)).toMonoidHom) k).trans le_sup_left
    have hstarQ : (starSpan R Y).map (embedS R) ≤ Q R (alpha R) := by
      apply h.original_starSpan_le_core_of_distance geometry hpos Y P hY hnY rfl
      have hd : (cosetGraph R).dist (beta R) (alpha R)=1 := by
        rw [SimpleGraph.dist_comm]
        exact SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr (base_adjacent R))
      have heven := geometry.even (alpha R) rfl
      rw [geometry.distance_constant _ rfl] at heven
      change Even (geometry.b R) at heven
      obtain ⟨m,hm⟩ := heven
      omega
    have hstar : (starSpan R Y).map (embedS R) ≤ sourceStarAlpha R Y := by
      have hh := (sourceStarAlpha_le_iff R Y (sourceStarAlpha R Y)).mp le_rfl (1 : Mbar R)
      have hid : (MulAut.conj (1 : FreeAmalgam R)).toMonoidHom=MonoidHom.id _ := by
        apply MonoidHom.ext
        intro x
        change 1*x*1⁻¹=x
        simp
      simpa only [OneMemClass.coe_one,hid,Subgroup.map_id] using hh
    have hjD : ⁅J,Q R (alpha R)⁆ ≤ fixedCore R (alpha R) := by
      obtain ⟨z,path,hfirst⟩ := exists_original_critical_path_through_beta geometry hpos
      exact (commutator_mono (hJB.trans (hs.trans hstar)) le_rfl).trans
        (h.original_sourceStarAlpha_core_displacement geometry hpos path hfirst Y P hY hnY)
    obtain ⟨_,hadj⟩ := transported_seed_edges R (1 : Mbar R) k
    simp only [OneMemClass.coe_one,inv_one,act_one] at hadj
    refine Or.inr ⟨_,Pδ,J,?_,hadj,?_,?_,hJB.trans (hs.trans hstarQ),hnJ,hcJ,hmJ,hjD⟩
    · rw [action_preserves_color]
      rfl
    · rwa [hPδ]
    · rwa [hPδ]

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
