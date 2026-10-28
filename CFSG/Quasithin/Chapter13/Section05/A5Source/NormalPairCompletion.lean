module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalSylow
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalUniqueness
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairResidualNormal
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveCentralizer
public import CFSG.Quasithin.Chapter3.Section02
public import Theory.GroupTheory.TwoLayerCentralizer

/-!
# The normal A₅ pair and the maximal two-core

The literal orthogonal action places the image of the selected pair I in
one symmetric-three factor of the normalizer of the local cubic subgroup.
The Sylow index argument gives H = L₁IT. Normality first lifts to O²(I),
then to I itself. Its two-core is the original quaternion closure U_H.

The two-layer centralizer lemma makes O²(I) centralize C_T(L₁). Hence
C_T(L) is a normal two-subgroup of ⟨L,T,H⟩, whose two-core is trivial by
the original F.9 hypothesis. The A₅ block formula then gives O₂(LT)=V.
The actual maximal-local uniqueness and 3.2.11 recover O₂(N_G(L))=V,
N_G(V)=N_G(L), and C_G(V)=V.

These source consumers discharge the maximal-core premise in 13.5.17.
The identification H=G₁, the equality N_G(L)=LT, and the weak-BN/model
recognition steps remain separate obligations.

Source: Aschbacher–Smith 13.5.15 and 13.5.17, printed pp.920–922.
-/

open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.PairNormalGeometry
open ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}

structure Data (h : D.Hypothesis) where
  q : QuaternionCentralProductData D.UH
  center_map : (center D.UH).map D.UH.subtype = D.V₁
  seed_index : D.Vplus.relIndex D.V = 2
  seed_commutator : D.Vplus = ⁅D.V,D.L₁⁆
  normal : (D.L₁.subgroupOf D.H).Normal
  nonabelian : ¬ IsMulCommutative D.UH
  cubic_card : Nat.card (Section08.Source.starImage D.H D.L₁) = 3

variable (h : D.Hypothesis) (data : Data h)
include h data

theorem module_not_le_core : ¬ D.V ≤ D.QH :=
  fun hv => data.nonabelian (h.UH_elementary_of_V_le_QH hv).toIsMulCommutative

noncomputable def starEmbedding : Section08.Source.Hstar D.H →* BinaryFourPlus.Wreath :=
  h.closureStarEmbedding data.q data.center_map

theorem starEmbedding_injective : Function.Injective (starEmbedding h data) :=
  h.closureStarEmbedding_injective _ _

theorem starEmbedding_mk (x : D.H) :
    starEmbedding h data (QuotientGroup.mk' (pCore 2 D.H) x) =
      closureOrthogonalAction D.H le_rfl data.q x := rfl

theorem module_actor_singular (v : D.V) :
    BinaryFourPlus.SingularDisplacements
      (starEmbedding h data
        (QuotientGroup.mk' (pCore 2 D.H) (inclusion h.V_le_H v))) := by
  rw [starEmbedding_mk]
  apply data.q.wreath_singular_displacement
  intro u
  apply Subtype.ext
  change (((v:G)*(u:G)*(v:G)⁻¹)*(u:G)⁻¹)^2=1
  let : IsElementaryAbelian 2 D.V := h.elementary
  have hc := h.core_module_commutator_le_seed data.seed_index (module_not_le_core h data)
  apply elemPow_eq_one_of_isElementaryAbelian (G:=G) (A:=D.V)
  apply h.plus_le
  rw [show ((v:G)*(u:G)*(v:G)⁻¹)*(u:G)⁻¹=⁅(v:G),(u:G)⁆ from rfl,
    ←commutatorElement_inv]
  exact D.Vplus.inv_mem (hc (commutator_mem_commutator (h.UH_le_QH u.property) v.property))

noncomputable def localCubic : Subgroup BinaryFourPlus.Wreath :=
  (Section08.Source.starImage D.H D.L₁).map (starEmbedding h data)

theorem localCubic_card : Nat.card (localCubic h data)=3 := by
  rw [localCubic,card_map_of_injective (starEmbedding_injective h data)]
  exact data.cubic_card

theorem range_normalizes_local : (starEmbedding h data).range≤
    normalizer (localCubic h data:Set BinaryFourPlus.Wreath) := by
  let : (D.L₁.subgroupOf D.H).Normal := data.normal
  let : (Section08.Source.starImage D.H D.L₁).Normal :=
    Normal.map data.normal (QuotientGroup.mk' (pCore 2 D.H)) (QuotientGroup.mk'_surjective _)
  simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,localCubic] using
    (Section08.Source.starImage D.H D.L₁).le_normalizer_map (starEmbedding h data)

theorem module_actor_centralizes_local (v : D.V) :
    starEmbedding h data (QuotientGroup.mk' (pCore 2 D.H) (inclusion h.V_le_H v))∈
      centralizer (localCubic h data:Set BinaryFourPlus.Wreath) := by
  rintro _ ⟨_,⟨l,hl,rfl⟩,rfl⟩
  let vH := inclusion h.V_le_H v
  have hc : ⁅vH,l⁆∈pCore 2 D.H := by
    have hm : (⁅vH,l⁆:D.H).val∈D.QH :=
      h.UH_le_QH (le_conjugateSpanBy _ _ (data.seed_commutator.symm ▸ commutator_mem_commutator v.property hl))
    exact (show D.QH.subgroupOf D.H=pCore 2 D.H from
      comap_map_eq_self_of_injective D.H.subtype_injective _) ▸ hm
  let π := QuotientGroup.mk' (pCore 2 D.H)
  have hh : π vH * π l=π l * π vH := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr hc
  simpa only [map_mul] using (congrArg (starEmbedding h data) hh).symm

include h data in
theorem exists_original_cubic_normalizer_witness :
    let f := starEmbedding h data
    let A := localCubic h data
    Function.Injective f ∧ Nat.card A=3 ∧ f.range≤normalizer (A:Set BinaryFourPlus.Wreath) ∧
    ∃s:BinaryFourPlus.Wreath,s∈f.range ∧ s≠1 ∧ s^2=1 ∧
      BinaryFourPlus.SingularDisplacements s ∧ s∈centralizer (A:Set BinaryFourPlus.Wreath) := by
  dsimp only
  have hvn := module_not_le_core h data
  obtain ⟨v,hv,hvq⟩ := Set.not_subset.mp hvn
  let vV : D.V := ⟨v,hv⟩
  let vH := inclusion h.V_le_H vV
  let f := starEmbedding h data
  let x := QuotientGroup.mk' (pCore 2 D.H) vH
  have hx : x≠1 := by
    intro he
    exact hvq (mem_map_of_mem D.H.subtype ((QuotientGroup.eq_one_iff vH).mp he))
  have hs : f x≠1 := fun he=>hx ((starEmbedding_injective h data) (he.trans f.map_one.symm))
  have hv2 : vH^2=1 := by
    apply Subtype.ext
    let := h.elementary
    exact elemPow_eq_one_of_isElementaryAbelian v hv
  refine ⟨starEmbedding_injective h data,localCubic_card h data,
    range_normalizes_local h data,f x,⟨x,rfl⟩,hs,?_,
    module_actor_singular h data vV,module_actor_centralizes_local h data vV⟩
  rw [←map_pow]
  change f (QuotientGroup.mk' (pCore 2 D.H) vH^2)=1
  rw [←map_pow,hv2,map_one,map_one]

theorem original_star_card_dvd : Nat.card (Section08.Source.Hstar D.H)∣36 := by
  let f := starEmbedding h data
  let A := localCubic h data
  have hr : f.range≤normalizer (A:Set BinaryFourPlus.Wreath) := range_normalizes_local h data
  let j : Section08.Source.Hstar D.H→*normalizer (A:Set BinaryFourPlus.Wreath) :=
    f.codRestrict _ (fun x=>hr ⟨x,rfl⟩)
  have hj : Function.Injective j := fun x y he=>(starEmbedding_injective h data)
    (congrArg (fun z => (z.val : BinaryFourPlus.Wreath)) he)
  exact (card_dvd_of_injective j hj).trans (by
    obtain ⟨_,hA,_,s,_,hs,_,hss,hc⟩ := exists_original_cubic_normalizer_witness h data
    exact (BinaryFourPlus.CubicNormalizer.normalizer_centralizer_card _ hA s hs hss hc).1 ▸ dvd_rfl)

noncomputable def actor : D.H→*BinaryFourPlus.Wreath :=
  (starEmbedding h data).comp (QuotientGroup.mk' (pCore 2 D.H))

omit h data in
theorem pair_le (h : D.Hypothesis) {r:G} (hr:r∈D.H) :
    D.V⊔D.V.map (MulAut.conj r).toMonoidHom≤D.H :=
  sup_le h.V_le_H (by
    rintro _ ⟨v,hv,rfl⟩
    exact D.H.mul_mem (D.H.mul_mem hr (h.V_le_H hv)) (D.H.inv_mem hr))

theorem actor_range_normalizes :
    (actor h data).range≤normalizer (localCubic h data:Set BinaryFourPlus.Wreath) := by
  rintro _ ⟨x,rfl⟩
  exact range_normalizes_local h data ⟨_,rfl⟩

theorem module_image_centralizes :
    (D.V.subgroupOf D.H).map (actor h data)≤
      centralizer (localCubic h data:Set BinaryFourPlus.Wreath) := by
  rintro _ ⟨v,hv,rfl⟩
  exact module_actor_centralizes_local h data ⟨v.val,hv⟩

theorem pair_image_centralizes (r:G) (hr:r∈D.H) :
    ((D.V⊔D.V.map (MulAut.conj r).toMonoidHom).subgroupOf D.H).map
      (actor h data)≤
      centralizer (localCubic h data:Set BinaryFourPlus.Wreath) := by
  let α := actor h data
  let A := localCubic h data
  have hv := module_image_centralizes h data
  rw [subgroupOf_sup h.V_le_H (show D.V.map (MulAut.conj r).toMonoidHom≤D.H from
    le_sup_right.trans (pair_le h hr)),Subgroup.map_sup]
  refine sup_le hv ?_
  rintro _ ⟨x,⟨v,hvV,he⟩,rfl⟩
  let rH:D.H := ⟨r,hr⟩
  let vH:D.H := ⟨v,h.V_le_H hvV⟩
  have hx : x=rH*vH*rH⁻¹ := Subtype.ext he.symm
  rw [hx,map_mul,map_mul,map_inv]
  exact (mem_normalizer_iff.mp
    ((normalizer_le_normalizer_centralizer A) (actor_range_normalizes h data ⟨rH,rfl⟩))
    (α vH)).mp (hv (mem_map_of_mem α hvV))

theorem pair_image_eq_action_range (r:G) (hr:r∈D.H) :
    ((D.V⊔D.V.map (MulAut.conj r).toMonoidHom).subgroupOf D.H).map
      (actor h data)=
      (closureOrthogonalAction (D.V⊔D.V.map (MulAut.conj r).toMonoidHom)
        (pair_le h hr) data.q).range := by
  let I := D.V⊔D.V.map (MulAut.conj r).toMonoidHom
  let α := actor h data
  have hc : α.comp (inclusion (pair_le h hr))=
      closureOrthogonalAction I (pair_le h hr) data.q := rfl
  rw [←hc,MonoidHom.range_comp,inclusion_range]

theorem pair_image_structure (r:G) (hr:r∈D.H)
    (hj:Nonempty ((Section08.Source.starImage D.H
      (D.V⊔D.V.map (MulAut.conj r).toMonoidHom))≃*Equiv.Perm (Fin 3))) :
    let A:=localCubic h data
    let J:=((D.V⊔D.V.map (MulAut.conj r).toMonoidHom).subgroupOf D.H).map
      (actor h data)
    normalizer (A:Set BinaryFourPlus.Wreath)≤normalizer (J:Set BinaryFourPlus.Wreath) ∧
      centralizer (A:Set BinaryFourPlus.Wreath)=A⊔J ∧ Disjoint A J ∧ Nat.card (A⊔J:Subgroup BinaryFourPlus.Wreath)=18 := by
  dsimp only
  let I:=D.V⊔D.V.map (MulAut.conj r).toMonoidHom
  let A:=localCubic h data
  let J:=(I.subgroupOf D.H).map (actor h data)
  obtain ⟨_,hA,_,s,_,hs,_,hss,hc⟩:=exists_original_cubic_normalizer_witness h data
  have hJ:Nat.card J=6 := by
    change Nat.card ((I.subgroupOf D.H).map ((starEmbedding h data).comp
      (QuotientGroup.mk' (pCore 2 D.H))))=6
    rw [←map_map]
    rw [card_map_of_injective (starEmbedding_injective h data)]
    obtain ⟨f⟩:=hj
    change Nat.card (Section08.Source.starImage D.H I)=6
    rw [Nat.card_congr f.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  obtain ⟨a,b,ha,hb,_,_,he⟩:=h.closure_pair_orthogonal_generators data.seed_index
    (module_not_le_core h data) r hr data.q
    data.center_map (pair_le h hr)
  apply BinaryFourPlus.CubicNormalizer.symmetric_factor_normalizer A J hA s hs hss hc
    (pair_image_centralizes h data r hr) hJ
  exact ⟨a,b,ha,hb,(pair_image_eq_action_range h data r hr).trans he⟩

include h data

/-- The selected pair together with the original local residual and Sylow
subgroup generates H; the quotient order bound is proved from its marked action. -/
theorem whole_generated (r:G) (hr:r∈D.H)
    (hj:Nonempty ((Section08.Source.starImage D.H
      (D.V⊔D.V.map (MulAut.conj r).toMonoidHom))≃*Equiv.Perm (Fin 3))) :
    D.H=D.L₁⊔(D.V⊔D.V.map (MulAut.conj r).toMonoidHom)⊔(D.T:Subgroup G) := by
  let I:=D.V⊔D.V.map (MulAut.conj r).toMonoidHom
  let Z:=D.L₁⊔I⊔(D.T:Subgroup G)
  let π:=QuotientGroup.mk' (pCore 2 D.H)
  let f:=starEmbedding h data
  let A:=localCubic h data
  let J:=(I.subgroupOf D.H).map (actor h data)
  let B:=Section08.Source.starImage D.H Z
  have hLH:D.L₁≤D.H:=le_sup_left.trans h.local_le
  have hIH:I≤D.H:=pair_le h hr
  have hZH:Z≤D.H:=sup_le (sup_le hLH hIH) h.T_le_H
  have hAB:A⊔J≤B.map f:=by
    apply sup_le
    · exact map_mono (map_mono (subgroupOf_mono D.H
        (show D.L₁≤Z from le_sup_left.trans le_sup_left)))
    · change (I.subgroupOf D.H).map (f.comp π)≤B.map f
      rw [←map_map]
      exact map_mono (map_mono (subgroupOf_mono D.H
        (show I≤Z from le_sup_right.trans le_sup_left)))
  have h18:18∣Nat.card B:=by
    have hd:=card_dvd_of_le hAB
    rw [(pair_image_structure h data r hr hj).2.2.2,
      card_map_of_injective (starEmbedding_injective h data)] at hd
    exact hd
  have hmul:18*B.index∣18*2:=
    (Nat.mul_dvd_mul_right h18 B.index).trans
      (B.card_mul_index ▸ original_star_card_dvd h data)
  have hi:B.index∣2:=Nat.dvd_of_mul_dvd_mul_left (by decide) hmul
  let S: Sylow 2 (Section08.Source.Hstar D.H):=
    (D.T.subtype h.T_le_H).mapSurjective (QuotientGroup.mk'_surjective _)
  have hSB:(S:Subgroup (Section08.Source.Hstar D.H))≤B:=by
    change ((D.T:Subgroup G).subgroupOf D.H).map π≤B
    exact map_mono (subgroupOf_mono D.H le_sup_right)
  have hodd:¬2∣B.index:=fun hd=>S.not_dvd_index (hd.trans (index_dvd_of_le hSB))
  have ht:B=⊤:=index_eq_one.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.prime_two.coprime_iff_not_dvd.mpr hodd) hi dvd_rfl)
  have he:=congrArg (Subgroup.comap π) ht
  change ((Z.subgroupOf D.H).map π).comap π=⊤ at he
  rw [comap_map_eq,QuotientGroup.ker_mk'] at he
  have hk:pCore 2 D.H≤Z.subgroupOf D.H:=by
    intro x hx
    exact (show (D.T:Subgroup G)≤Z from le_sup_right)
      (h.QH_le_T (mem_map_of_mem D.H.subtype hx))
  rw [sup_of_le_left hk] at he
  apply le_antisymm ?_ hZH
  intro x hx
  change (⟨x,hx⟩:D.H)∈Z.subgroupOf D.H
  rw [he]
  trivial

/-- The actual pair with the original two-core is normal in H. -/
theorem whole_normalizes_pair_core (r:G) (hr:r∈D.H)
    (hj:Nonempty ((Section08.Source.starImage D.H
      (D.V⊔D.V.map (MulAut.conj r).toMonoidHom))≃*Equiv.Perm (Fin 3))) :
    D.H≤normalizer ((D.V⊔D.V.map (MulAut.conj r).toMonoidHom⊔D.QH:Subgroup G):Set G) := by
  let I:=D.V⊔D.V.map (MulAut.conj r).toMonoidHom
  let α:=actor h data
  let J:=(I.subgroupOf D.H).map α
  have hk:α.ker=pCore 2 D.H:=by
    ext x
    change starEmbedding h data (QuotientGroup.mk' (pCore 2 D.H) x)=1↔_
    rw [show (1:BinaryFourPlus.Wreath)=starEmbedding h data 1 from
      (starEmbedding h data).map_one.symm,
      (starEmbedding_injective h data).eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hnorm:α.range≤normalizer (J:Set BinaryFourPlus.Wreath):=
    (actor_range_normalizes h data).trans
      (pair_image_structure h data r hr hj).1
  have hpre:(J.comap α).Normal:={
    conj_mem:=by
      intro x hx y
      change α (y*x*y⁻¹)∈J
      rw [map_mul,map_mul,map_inv]
      exact (mem_normalizer_iff.mp (hnorm ⟨y,rfl⟩) (α x)).mp hx }
  have he:(J.comap α).map D.H.subtype=I⊔D.QH:=by
    rw [comap_map_eq,hk,Subgroup.map_sup,map_subgroupOf_eq_of_le (pair_le h hr)]
    rfl
  rw [←he]
  let := hpre
  simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
    (J.comap α).le_normalizer_map D.H.subtype



theorem twoCore_normalizes_pair (g : G) (hg : g ∈ D.H) :
    D.QH ≤ normalizer ((D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  let f := (MulAut.conj g).toMonoidHom
  have hc := h.core_module_commutator_le_seed data.seed_index (module_not_le_core h data)
  have hcg : ⁅D.QH,D.V.map f⁆ ≤ D.Vplus.map f := by
    have hh := map_mono (f := f) hc
    have he : D.QH.map f = D.QH := mem_normalizer_iff_map_conj_eq.mp (H_normalizes_QH hg)
    rwa [map_commutator,he] at hh
  exact (le_inf (h.QH_le_T.trans h.T_normalizes_V)
    (le_normalizer_iff_commutator_le_right.mpr (hcg.trans (map_mono h.plus_le)))).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

theorem whole_normalizes_pair_residual (v r : G) (hv : v ∈ D.V) (hv2 : v ^ 2 = 1)
    (hr : orderOf r = 3) (hrH : r ∈ D.H) (hinv : v * r * v⁻¹ = r⁻¹)
    (hj : Nonempty (Section08.Source.starImage D.H
      (D.V ⊔ D.V.map (MulAut.conj r).toMonoidHom) ≃* Equiv.Perm (Fin 3))) :
    let I := D.V ⊔ D.V.map (MulAut.conj r).toMonoidHom
    D.H ≤ normalizer ((pResidual 2 I).map I.subtype : Set G) := by
  dsimp only
  let I := D.V ⊔ D.V.map (MulAut.conj r).toMonoidHom
  let R := (pResidual 2 I).map I.subtype
  let P := D.V ⊔ D.QH
  have hIQ := whole_normalizes_pair_core h data r hrH hj
  have hQR : D.QH ≤ normalizer (R : Set G) :=
    (twoCore_normalizes_pair h data r hrH).trans
      (normalizer_le_normalizer_characteristic_image I (pResidual 2 I))
  have hVR : D.V ≤ normalizer (R : Set G) :=
    (le_sup_left.trans I.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image I (pResidual 2 I))
  have hP : IsPGroup 2 P := D.T.isPGroup'.to_le (sup_le h.V_le_T h.QH_le_T)
  have he := embedded_pResidual_join_pGroup R P (isPPerfect_embedded_pResidual 2 I)
    hP (sup_le hVR hQR)
  have hjoin : R ⊔ P = I ⊔ D.QH := by
    change R ⊔ (D.V ⊔ D.QH) = I ⊔ D.QH
    rw [←sup_assoc,←NormalBranch.SourcePairResidualNormal.pair_eq_residual_sup_module v r hv hv2 hr hinv]
  rw [hjoin] at he
  have hnorm := hIQ.trans (normalizer_le_normalizer_characteristic_image
    (I ⊔ D.QH) (pResidual 2 (I ⊔ D.QH : Subgroup G)))
  rwa [he] at hnorm

theorem whole_normalizes_pair (v r : G) (hv : v ∈ D.V) (hv2 : v ^ 2 = 1)
    (hr : orderOf r = 3) (hrH : r ∈ D.H) (hinv : v * r * v⁻¹ = r⁻¹)
    (hj : Nonempty (Section08.Source.starImage D.H
      (D.V ⊔ D.V.map (MulAut.conj r).toMonoidHom) ≃* Equiv.Perm (Fin 3))) :
    D.H ≤ normalizer ((D.V ⊔ D.V.map (MulAut.conj r).toMonoidHom : Subgroup G) : Set G) := by
  let I := D.V ⊔ D.V.map (MulAut.conj r).toMonoidHom
  let R := (pResidual 2 I).map I.subtype
  have hR := whole_normalizes_pair_residual h data v r hv hv2 hr hrH hinv hj
  have he : I = R ⊔ D.V :=
    NormalBranch.SourcePairResidualNormal.pair_eq_residual_sup_module v r hv hv2 hr hinv
  have hlocal : D.L₁ ⊔ (D.T : Subgroup G) ≤ normalizer (I : Set G) := by
    rw [he]
    apply (le_inf (h.local_le.trans hR) ?_).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    exact (sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl).trans
      ((normal_subgroupOf_iff_le_normalizer h.V_le_LT).mp h.reduced.normal)
  rw [whole_generated h data r hrH hj]
  exact sup_le (sup_le (le_sup_left.trans hlocal) I.le_normalizer) (le_sup_right.trans hlocal)

end CFSG.Quasithin.Chapter13.Section05.A5Source.PairNormalGeometry

public section

namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ChapterF.Section09.Setup.Hypothesis
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn

private noncomputable def normal_pair_geometry :
    PairNormalGeometry.Data (source13_5_7 d hA312 hH).f9Hypothesis := by
  let q := (normal_quaternion_with_center d hA312 hH hU hn).choose
  have hq := (normal_quaternion_with_center d hA312 hH hU hn).choose_spec
  refine ⟨q,hq,d.third_index,d.third_eq_commutator,hn,hU,?_⟩
  change Nat.card (Source.starImage H (residualCentralizer L V₁)) = 3
  rw [Nat.card_congr (normal_residual_star_cubic d hA312 hH hU hn).toEquiv]
  simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]

/-- The original normal pair and the generation used in 13.5.15(7). -/
theorem source_normal_pair_normal :
    ∃ r ∈ H, orderOf r = 3 ∧
      let I := V ⊔ V.map (MulAut.conj r).toMonoidHom
      I.pCoreIn 2 = Source.UH H V₃ ∧
      H = residualCentralizer L V₁ ⊔ I ⊔ (T : Subgroup G) ∧
      H ≤ normalizer (I : Set G) ∧
      I = (pResidual 2 I).map I.subtype ⊔ V := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  let data := normal_pair_geometry d hA312 hH hU hn
  obtain ⟨v,hv,hvq,hv2,r,hrH,hr,hi,hcore,hj⟩ := source_normal_pair_core d hA312 hH hU hn
  exact ⟨r,hrH,hr,hcore,PairNormalGeometry.whole_generated hf data r hrH hj,
    PairNormalGeometry.whole_normalizes_pair hf data v r hv hv2 hr hrH hi hj,
    NormalBranch.SourcePairResidualNormal.pair_eq_residual_sup_module (D := D) v r hv hv2 hr hi⟩

/-- The pair centralizes its quaternion core only on the original point line. -/
theorem normal_pair_centralizer_eq_point (I : Subgroup G) (hIH : I ≤ H)
    (hcore : I.pCoreIn 2 = Source.UH H V₃) :
    I ⊓ centralizer (Source.UH H V₃ : Set G) = V₁ := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  have hUI : D.UH ≤ I := hcore.ge.trans (pCoreIn_le 2 I)
  obtain ⟨_,hz⟩ := normal_quaternion_with_center d hA312 hH hU hn
  apply le_antisymm
  · intro x hx
    have hxQ : x ∈ D.QH := by
      rw [←hf.kernel_UH_eq_QH]
      apply (hf.mem_kernel_iff hf.UH_le_H).mpr
      refine ⟨hIH hx.1,?_⟩
      intro u hu
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hx.2 u hu)]
      exact D.V₁.one_mem
    have hxU : x ∈ D.UH := hcore.le (inf_pCoreIn_le_of_le 2 hIH ⟨hx.1,hxQ⟩)
    have hc : (⟨x,hxU⟩ : D.UH) ∈ center D.UH := by
      rw [mem_center_iff]
      intro u
      exact Subtype.ext (hx.2 u u.property)
    exact hz.le (mem_map_of_mem D.UH.subtype hc)
  · exact le_inf ((hf.point_lt.le.trans (le_conjugateSpanBy _ _)).trans hUI)
      (le_centralizer_iff.mp (hf.UH_le_H.trans hf.H_centralizes))

/-- Coprime action on the two-layer commutator kills the residual action. -/
theorem normal_pair_residual_centralizes (I : Subgroup G) (hIH : I ≤ H)
    (hcore : I.pCoreIn 2 = Source.UH H V₃) (hI : H ≤ normalizer (I : Set G)) :
    (pResidual 2 I).map I.subtype ≤ centralizer
      (((T : Subgroup G) ⊓ centralizer (residualCentralizer L V₁ : Set G) : Subgroup G) : Set G) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  let C := (T : Subgroup G) ⊓ centralizer (D.L₁ : Set G)
  have hCU : C ≤ centralizer (D.UH : Set G) :=
    inf_le_right.trans (centralizer_le ((NormalBranch.closure_reduction hf d.third_eq_commutator hn).2.1.trans (pCoreIn_le 2 D.L₁)))
  have hIC : I ≤ normalizer (centralizer (D.UH : Set G) : Set G) :=
    (hIH.trans (le_normalizer_conjugateSpanBy V₃ H)).trans
      (normalizer_le_normalizer_centralizer D.UH)
  have hc : ⁅I,C⁆ ≤ V₁ := by
    rw [←normal_pair_centralizer_eq_point d hA312 hH hU hn I hIH hcore]
    exact le_inf
      (le_normalizer_iff_commutator_le_left.mp ((inf_le_left.trans hf.T_le_H).trans hI))
      ((commutator_mono le_rfl hCU).trans (le_normalizer_iff_commutator_le_right.mp hIC))
  exact residual_centralizes_of_two_layer I C V₁
    (T.isPGroup'.to_le ((hf.point_lt.le.trans hf.plus_le).trans hf.V_le_T))
    (hIH.trans hf.H_centralizes) hc

/-- The F.9 generated-core hypothesis eliminates the local Sylow centralizer. -/
theorem normal_sylow_local_centralizer_eq_bot :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  let C := (T : Subgroup G) ⊓ centralizer (L : Set G)
  have hLC : L ≤ centralizer (C : Set G) :=
    le_centralizer_iff.mp (show C ≤ centralizer (L : Set G) from inf_le_right)
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      (d.normalizes_L.trans (normalizer_le_normalizer_centralizer L))).trans
        inf_normalizer_le_normalizer_inf
  obtain ⟨r,hrH,_,hcore,hgen,hI,hres⟩ := source_normal_pair_normal d hA312 hH hU hn
  let I := V ⊔ V.map (MulAut.conj r).toMonoidHom
  change I = (pResidual 2 I).map I.subtype ⊔ V at hres
  have hsub : C ≤ (T : Subgroup G) ⊓ centralizer (D.L₁ : Set G) :=
    inf_le_inf_left _ (centralizer_le ((map_subtype_le _).trans inf_le_left))
  have hRC : (pResidual 2 I).map I.subtype ≤ centralizer (C : Set G) :=
    (normal_pair_residual_centralizes d hA312 hH hU hn I
      (PairNormalGeometry.pair_le hf hrH) hcore hI).trans (centralizer_le hsub)
  have hVL : V ≤ L := by
    obtain ⟨g,hg,hg₁⟩ := d.exists_block_conjugator
    exact (normal_block_consequences d hA312 hH hU hg hg₁ hn).2.1.ge.trans (pCoreIn_le 2 L)
  have hIC : I ≤ centralizer (C : Set G) := by
    rw [hres]
    exact sup_le hRC (hVL.trans hLC)
  have hHC : H ≤ normalizer (C : Set G) := by
    rw [hgen]
    exact sup_le (sup_le
      (((map_subtype_le _).trans inf_le_left).trans
        (hLC.trans (centralizer_le_normalizer C)))
      (hIC.trans (centralizer_le_normalizer C))) hTC
  have hcoreC : C ≤ (D.LT ⊔ H : Subgroup G).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
      (inf_le_left.trans (le_sup_right.trans le_sup_left))
      (sup_le (sup_le (hLC.trans (centralizer_le_normalizer C)) hTC) hHC)
  apply bot_unique
  change C ≤ (D.LT ⊔ D.H : Subgroup G).pCoreIn 2 at hcoreC
  simpa only [pCoreIn,hf.generated_core,Subgroup.map_bot] using hcoreC

/-- The A₅ block centralizer formula identifies the original local two-core. -/
theorem normal_local_core_eq_module : (L ⊔ (T : Subgroup G)).pCoreIn 2 = V := by
  obtain ⟨g,hg,hg₁⟩ := d.exists_block_conjugator
  obtain ⟨hb,hLV,-⟩ := normal_block_consequences d hA312 hH hU hg hg₁ hn
  have hs := hb.normalizer_twoCore_eq_module_sup_centralizer
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer d.normalizes_L)
  have hz : (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (L : Set G) = ⊥ :=
    bot_unique ((inf_le_inf d.core_le_sylow le_rfl).trans
      (normal_sylow_local_centralizer_eq_bot d hA312 hH hU hn).le)
  rw [hz,sup_bot_eq] at hs
  apply le_antisymm
  · rw [hs]
    exact (map_mono (ChapterC.blockU_le_core (L := L))).trans hLV.le
  · exact d.chosen.le_core

/-- The maximal-core clause of 13.5.15(7), with its ambient normalizer and centralizer. -/
theorem normal_maximal_core_eq_module :
    (normalizer (L : Set G)).pCoreIn 2 = V ∧
      normalizer (V : Set G) = normalizer (L : Set G) ∧ centralizer (V : Set G) = V := by
  let M := normalizer (L : Set G)
  have hLM : L ≤ M := L.le_normalizer
  have hJM : L ⊔ (T : Subgroup G) ≤ M := sup_le hLM d.normalizes_L
  obtain ⟨N,hN,hJN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
    (L ⊔ (T : Subgroup G)) d.hypothesis.local_component.1.2
  have he : N = M := d.unique_maximal_overgroup N hN hJN
  have hmax : IsMaximalTwoLocal M := he ▸ hN
  have hchar := d.hypothesis.qtke.evenCharacteristic T M hmax (le_sup_right.trans hJM)
  have hc := Chapter3.Section02.lemma_3_2_11_of_core_containment T L
    (L ⊔ (T : Subgroup G)) M V le_sup_right hJM hLM rfl hmax hchar
    (normal_local_core_eq_module d hA312 hH hU hn).symm
    (by
      obtain ⟨g,hg,hg₁⟩ := d.exists_block_conjugator
      exact (normal_block_consequences d hA312 hH hU hg hg₁ hn).2.1.ge)
    d.chosen.ne_bot
  exact ⟨hc.1,hc.2.1,hc.2.2.1⟩

end CFSG.Quasithin.Chapter13.Section05.A5Source
