module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceNinePlanes

/-!
# The original Sylow action on the two Nine planes

The same marked point stabilizer has order two in the cyclic-four action of
T. Its faithful action on the fixed plane, and exchange of the two planes
by every remaining actor, lift through the literal conjugation homomorphism.
Thus S=C_T(Z1) has index two in T, normalizes both original planes, and has
centralizer index two on V1. Every element of T outside S exchanges V1 and V2.

The chosen-component application retains the original marker and movement
packet. It adds no mathematical premise beyond the genuine earlier15.1.14(1)
residual centralization. These are the exact Nine-row action inputs to the
later component and centralizer exclusions, without a model-recognition claim.

Source: Aschbacher--Smith,15.1.16(b),15.1.25(4),(6), printed pp.1092,1102.
-/

public section

open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem cyclic_four_two_torsion {D : Type*} [Group D] [Finite D]
    (S H : Subgroup D) [IsCyclic S] (hHS : H ≤ S)
    (hS : Nat.card S = 4) (hH : Nat.card H = 2) :
    ∀ a ∈ S, a ^ 2 = 1 → a ∈ H := by
  classical
  obtain ⟨r,hrgen⟩ := IsCyclic.exists_generator (α := S)
  have hr : orderOf r = 4 := (orderOf_eq_card_of_forall_mem_zpowers hrgen).trans hS
  have hindex : (H.subgroupOf S).index = 2 := by
    have hc : Nat.card (H.subgroupOf S) = 2 :=
      (Nat.card_congr (subgroupOfEquivOfLe hHS).toEquiv).trans hH
    have hh := (H.subgroupOf S).index_mul_card
    rw [hc,hS] at hh
    omega
  have hr2 : (r : D) ^ 2 ∈ H := (H.subgroupOf S).sq_mem_of_index_two hindex r
  intro a ha ha2
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp (hrgen ⟨a,ha⟩))
  have hn4 : n < 4 := by simpa [hr] using Finset.mem_range.mp hn
  have hapow : r ^ (n * 2) = 1 := by
    rw [pow_mul,he]
    exact Subtype.ext ha2
  have hd : 4 ∣ n * 2 := by simpa [hr] using orderOf_dvd_of_pow_eq_one hapow
  have hn02 : n = 0 ∨ n = 2 := by omega
  rcases hn02 with rfl | rfl
  · have he' : a = 1 := by simpa using (congrArg Subtype.val he).symm
    rw [he']
    exact H.one_mem
  · have he' : (r : D) ^ 2 = a := congrArg Subtype.val he
    simpa only [he'] using hr2

/-- The actual image stabilizer preserves both planes and acts faithfully on
the fixed plane; the remaining Sylow actors exchange the two planes. -/
theorem source_nine_image_plane_action
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (h9 : SourceCases.Nine (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict))
    (v : Additive V) (K : Subgroup (internalActionImage M V hn))
    (hv : v ≠ 0) (hK : ∀ d, d ∈ K ↔ imageRepresentation M V hn d v = v)
    (hc : Nat.card K = 6)
    (hSyl : ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype =
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict) ⊓ K) :
    let D := ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict
    let R := (pResidual 2 K).map K.subtype
    let W1 := fixedSpace (imageRepresentation M V hn) R
    let W2 := subspaceCommutator (imageRepresentation M V hn) ⊤ R
    let H := D ⊓ K
    Nat.card H = 2 ∧ H.relIndex D = 2 ∧
      H ≤ subspaceStabilizer (imageRepresentation M V hn) W1 ∧
      H ≤ subspaceStabilizer (imageRepresentation M V hn) W2 ∧
      subspaceKernel (imageRepresentation M V hn) W1 H = ⊥ ∧
      ∀ t ∈ D, t ∉ H →
        W1.map ((imageRepresentation M V hn) t) = W2 ∧
        W2.map ((imageRepresentation M V hn) t) = W1 := by
  let ρ := imageRepresentation M V hn
  let D : Subgroup (internalActionImage M V hn) :=
    ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict
  let H : Subgroup (internalActionImage M V hn) := D ⊓ K
  obtain ⟨l, _, _, _, _, _, hD, x, φ, hφ, hcoord⟩ := h9
  let : IsCyclic D := hD.1
  let σ := OrthogonalFourBinary.naturalRepresentation.comp φ
  have hcoord' : ∀ a w, x (ρ a w) = σ a (x w) := hcoord
  let z := x v
  have hz : z ≠ 0 := fun he => hv (x.injective (he.trans (map_zero x).symm))
  have hK' : K = OrthogonalFourBinary.MarkedNine.pointStabilizer φ z := by
    ext d
    rw [hK]
    change ρ d v = v ↔ (φ d).val (x v) = x v
    rw [←hcoord d v]
    exact x.injective.eq_iff.symm
  have hHcard : Nat.card H = 2 := by
    obtain ⟨P,hP⟩ := hSyl
    rw [show H = (P : Subgroup K).map K.subtype from hP.symm,
      card_map_of_injective K.subtype_injective,P.card_eq_multiplicity,hc]
    decide +kernel
  have hfix : ∀ a ∈ D, a ^ 2 = 1 → (φ a).val z = z := by
    intro a ha ha2
    have hh := cyclic_four_two_torsion D H inf_le_left hD.2 hHcard a ha ha2
    have haK := (hK a).mp hh.2
    change (φ a).val (x v) = x v
    rw [←hcoord a v,haK]
  have hp := OrthogonalFourBinary.MarkedNine.marked_vector_plane_action
    φ hφ D hD.2 z hz hfix (hK' ▸ hc)
  rw [←hK'] at hp
  let R := (pResidual 2 K).map K.subtype
  let W1 := fixedSpace ρ R
  let W2 := subspaceCommutator ρ ⊤ R
  have hf : W1.map x.toLinearMap = fixedSpace σ R := by
    simpa only [Subgroup.map_id] using
      fixedSpace_map_equivariant ρ σ (MonoidHom.id _) x hcoord R
  have hm : W2.map x.toLinearMap = subspaceCommutator σ ⊤ R := by
    have hh := subspaceCommutator_map_embedding σ ρ (MonoidHom.id _) x.toLinearMap
      (fun d w => (hcoord d w).symm) R ⊤
    simpa only [Subgroup.map_id,Submodule.map_top,LinearEquiv.range] using hh.symm
  have hmem (W : Submodule (ZMod 2) (Additive V)) (w : Additive V) :
      x w ∈ W.map x.toLinearMap ↔ w ∈ W := by
    constructor
    · rintro ⟨u,hu,he⟩
      exact x.injective he ▸ hu
    · exact fun hw => Submodule.mem_map_of_mem hw
  have hstab (W : Submodule (ZMod 2) (Additive V))
      (hs : H ≤ subspaceStabilizer σ (W.map x.toLinearMap)) :
      H ≤ subspaceStabilizer ρ W := by
    intro a ha w
    rw [←hmem W (ρ a w),←hmem W w,hcoord']
    exact hs ha (x w)
  refine ⟨hp.1,hp.2.1,hstab W1 ?_,hstab W2 ?_,?_,?_⟩
  · rw [hf]; exact hp.2.2.1
  · rw [hm]; exact hp.2.2.2.1
  · apply bot_unique
    intro a ha
    have hak : a ∈ subspaceKernel σ (fixedSpace σ R) H := by
      refine ⟨ha.1,?_⟩
      intro w hw
      obtain ⟨u,rfl⟩ := x.surjective w
      rw [←hf] at hw
      rw [←hcoord',ha.2 u ((hmem W1 u).mp hw)]
    rwa [hp.2.2.2.2.1] at hak
  · intro t ht htn
    obtain ⟨h1,h2⟩ := hp.2.2.2.2.2.2 t ht htn
    have hmap (W : Submodule (ZMod 2) (Additive V)) :
        (W.map (ρ t)).map x.toLinearMap = (W.map x.toLinearMap).map (σ t) := by
      rw [←Submodule.map_comp,←Submodule.map_comp]
      congr 1
      apply LinearMap.ext
      intro w
      exact hcoord' t w
    constructor
    · apply Submodule.map_injective_of_injective x.injective
      rw [hmap,hf,hm]
      exact h1
    · apply Submodule.map_injective_of_injective x.injective
      rw [hmap,hf,hm]
      exact h2


/-- The original Sylow centralizer has index two, acts nontrivially on the
fixed plane, and every other Sylow element exchanges the two actual planes. -/
theorem source_nine_plane_action
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (h9 : SourceCases.Nine (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict))
    (v : Additive V) (K : Subgroup (internalActionImage M V hn))
    (hv : v ≠ 0) (hK : ∀ d, d ∈ K ↔ imageRepresentation M V hn d v = v)
    (hc : Nat.card K = 6)
    (hSyl : ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype =
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict) ⊓ K) :
    let Z1 := zpowers (v.toMul : G)
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let C := M ⊓ centralizer (Z1 : Set G)
    let R := (pResidual 2 C).map C.subtype
    let V1 := V ⊓ centralizer (R : Set G)
    let V2 := ⁅V,R⁆
    S.relIndex (T : Subgroup G) = 2 ∧
      S ≤ normalizer (V1 : Set G) ∧ S ≤ normalizer (V2 : Set G) ∧
      (centralizer (V1 : Set G)).relIndex S = 2 ∧
      ∀ t ∈ (T : Subgroup G), t ∉ S →
        V1.map (MulAut.conj t).toMonoidHom = V2 ∧
        V2.map (MulAut.conj t).toMonoidHom = V1 := by
  intro Z1 S C R V1 V2
  let f : M →* internalActionImage M V hn := (actionHom M V hn).rangeRestrict
  let ρ := imageRepresentation M V hn
  let D : Subgroup (internalActionImage M V hn) := ((T : Subgroup G).subgroupOf M).map f
  let H : Subgroup (internalActionImage M V hn) := D ⊓ K
  let q : T →* internalActionImage M V hn := f.comp (inclusion hTM)
  let qs : S →* internalActionImage M V hn := f.comp (inclusion (inf_le_left.trans hTM))
  let Rbar := (pResidual 2 K).map K.subtype
  let W1 := fixedSpace ρ Rbar
  let W2 := subspaceCommutator ρ ⊤ Rbar
  obtain ⟨hH,hindex,hstab1,hstab2,hkernel,hex⟩ :=
    source_nine_image_plane_action T hn h9 v K hv hK hc hSyl
  change subspaceKernel ρ W1 H = ⊥ at hkernel
  have hpre := vector_stabilizer_preimage M V hn v K hK
  have hfix (m : M) : f m ∈ K ↔ (m : G) ∈ centralizer (Z1 : Set G) := by
    constructor
    · intro hm
      exact (hpre.le (mem_map_of_mem M.subtype hm)).2
    · intro hm
      obtain ⟨a,ha,he⟩ := hpre.ge ⟨m.property,hm⟩
      have he' : a = m := Subtype.ext he
      exact he' ▸ ha
  have hqr : q.range = D := by
    ext a
    constructor
    · rintro ⟨t,rfl⟩
      exact mem_map_of_mem f t.property
    · rintro ⟨m,hm,rfl⟩
      exact ⟨⟨m,hm⟩,rfl⟩
  have hqH (t : T) : q t ∈ H ↔ (t : G) ∈ S := by
    change q t ∈ D ∧ q t ∈ K ↔ (t : G) ∈ (T : Subgroup G) ∧
      (t : G) ∈ centralizer (Z1 : Set G)
    have hd : q t ∈ D := hqr ▸ (show q t ∈ q.range from ⟨t,rfl⟩)
    exact ⟨fun h => ⟨t.property,(hfix (inclusion hTM t)).mp h.2⟩,
      fun h => ⟨hd,(hfix (inclusion hTM t)).mpr h.2⟩⟩
  have hqs (s : S) : qs s ∈ H := (hqH ⟨s,s.property.1⟩).mpr s.property
  have hqsr : qs.range = H := by
    apply le_antisymm
    · rintro a ⟨s,rfl⟩
      exact hqs s
    · intro a ha
      obtain ⟨t,ht⟩ := hqr.ge ha.1
      exact ⟨⟨t,(hqH t).mp (ht.symm ▸ ha)⟩,ht⟩
  have hfixed : V1.subgroupOf V = binarySubgroup W1 :=
    marked_residual_fixed_image M V hn v K hK
  have hmoved : V2.subgroupOf V = binarySubgroup W2 :=
    marked_residual_commutator_image M V hn v K hK
  have hV2 : V2 ≤ V := (marked_residual_movement hn Z1).1
  have hmem1 (w : Additive V) : (w.toMul : G) ∈ V1 ↔ w ∈ W1 := by
    change w.toMul ∈ V1.subgroupOf V ↔ _
    rw [hfixed]
    rfl
  have hmem2 (w : Additive V) : (w.toMul : G) ∈ V2 ↔ w ∈ W2 := by
    change w.toMul ∈ V2.subgroupOf V ↔ _
    rw [hmoved]
    rfl
  have hnormal (U : Subgroup G) (hUV : U ≤ V)
      (W : Submodule (ZMod 2) (Additive V))
      (hmem : ∀ w : Additive V, (w.toMul : G) ∈ U ↔ w ∈ W)
      (hstab : H ≤ subspaceStabilizer ρ W) : S ≤ normalizer (U : Set G) := by
    apply le_normalizer_iff.mpr
    intro s hs u hu
    let w : Additive V := Additive.ofMul ⟨u,hUV hu⟩
    have hw : w ∈ W := (hmem w).mp hu
    have hh := (hstab (hqs ⟨s,hs⟩) w).mpr hw
    exact (hmem (ρ (qs ⟨s,hs⟩) w)).mpr hh
  refine ⟨?_,hnormal V1 inf_le_left W1 hmem1 hstab1,
    hnormal V2 hV2 W2 hmem2 hstab2,?_,?_⟩
  · have he : H.comap q = S.subgroupOf (T : Subgroup G) := by
      ext t
      exact hqH t
    change (S.subgroupOf (T : Subgroup G)).index = 2
    rw [←he,H.index_comap q,hqr]
    exact hindex
  · have he : qs.ker = (centralizer (V1 : Set G)).subgroupOf S := by
      ext s
      constructor
      · intro hs
        have hs' : (actionHom M V hn) (inclusion (inf_le_left.trans hTM) s) = 1 :=
          congrArg Subtype.val hs
        have ha : inclusion (inf_le_left.trans hTM) s ∈ (actionHom M V hn).ker := hs'
        rw [actionHom_ker] at ha
        exact centralizer_le (show V1 ≤ V from inf_le_left) ha
      · intro hs
        have hak : qs s ∈ subspaceKernel ρ W1 H := by
          refine ⟨hqs s,?_⟩
          intro w hw
          apply Additive.toMul.injective
          apply Subtype.ext
          change (s : G) * (w.toMul : G) * (s : G)⁻¹ = (w.toMul : G)
          have hc : (s : G) ∈ centralizer (V1 : Set G) := hs
          have he : (s : G) * (w.toMul : G) = (w.toMul : G) * s :=
            (hc _ ((hmem1 w).mpr hw)).symm
          rw [he,mul_inv_cancel_right]
        rw [hkernel] at hak
        exact mem_bot.mp hak
    change ((centralizer (V1 : Set G)).subgroupOf S).index = 2
    rw [←he,index_ker,hqsr]
    exact hH
  · intro t ht htn
    have htD : q ⟨t,ht⟩ ∈ D := hqr ▸ (show q ⟨t,ht⟩ ∈ q.range from ⟨⟨t,ht⟩,rfl⟩)
    have htH : q ⟨t,ht⟩ ∉ H := fun ha => htn ((hqH ⟨t,ht⟩).mp ha)
    obtain ⟨h1,h2⟩ := hex (q ⟨t,ht⟩) htD htH
    have hmap (U U' : Subgroup G) (hUV : U ≤ V) (hU'V : U' ≤ V)
        (W W' : Submodule (ZMod 2) (Additive V))
        (hu : ∀ w : Additive V, (w.toMul : G) ∈ U ↔ w ∈ W)
        (hu' : ∀ w : Additive V, (w.toMul : G) ∈ U' ↔ w ∈ W')
        (he : W.map (ρ (q ⟨t,ht⟩)) = W') :
        U.map (MulAut.conj t).toMonoidHom = U' := by
      ext a
      constructor
      · rintro ⟨u,huU,rfl⟩
        let w : Additive V := Additive.ofMul ⟨u,hUV huU⟩
        have hw := Submodule.mem_map_of_mem (f := ρ (q ⟨t,ht⟩)) ((hu w).mp huU)
        rw [he] at hw
        exact (hu' (ρ (q ⟨t,ht⟩) w)).mpr hw
      · intro ha
        let w' : Additive V := Additive.ofMul ⟨a,hU'V ha⟩
        have hw' := (hu' w').mp ha
        rw [←he] at hw'
        obtain ⟨w,hw,hww⟩ := hw'
        refine ⟨w.toMul,(hu w).mpr hw,?_⟩
        exact congrArg (fun w : Additive V => (w.toMul : G)) hww
    exact ⟨hmap V1 V2 inf_le_left hV2 W1 W2 hmem1 hmem2 h1,
      hmap V2 V1 hV2 inf_le_left W2 W1 hmem2 hmem1 h2⟩



/-- The original chosen component carries the index-two Sylow action on its
two complementary planes. All indices and conjugates are ambient subgroups;
only the genuine earlier residual-centralization source input remains. -/
theorem PreparedChosenModule.source_caseI_nine_component_plane_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.row = .four ∧ Nat.card d.Z1 = 2 ∧
      pPrimeCore 2 d.G1 = ⊥ ∧ IsQuasisimple (d.L ⧸ pCore 2 d.L) ∧
      d.L ∈ Chapter1.L G d.S ∧ Chapter1.IsSylowIn 2 d.SL d.L ∧
      let R := (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype
      let V1 := V ⊓ centralizer (R : Set G)
      let V2 := ⁅V,R⁆
      V2 ≤ V ∧ R ⊔ V2 ≤ normalizer (d.L : Set G) ∧ ⁅d.L,V2⁆ ≠ ⊥ ∧
      Nat.card V1 = 4 ∧ Nat.card V2 = 4 ∧ V1 ⊔ V2 = V ∧ V1 ⊓ V2 = ⊥ ∧ d.Z1 ≤ V1 ∧
      d.S.relIndex (T : Subgroup G) = 2 ∧
      d.S ≤ normalizer (V1 : Set G) ∧ d.S ≤ normalizer (V2 : Set G) ∧
      (centralizer (V1 : Set G)).relIndex d.S = 2 ∧
      ∀ t ∈ (T : Subgroup G), t ∉ d.S →
        V1.map (MulAut.conj t).toMonoidHom = V2 ∧
        V2.map (MulAut.conj t).toMonoidHom = V1 := by
  let := h.elementary
  obtain ⟨v,K,hv,hfixed,hK,hgen,hcard,hSyl,hbound⟩ :=
    chosen_nine_marked_image_with_movement T hM.1.2 h.normalized h9
  obtain ⟨d,hdZ,hdrow,hdcard,hodd,hq,hL,hSL,hV2,hn,hmove⟩ :=
    h.caseI_component_of_marked_image hG T hempty hM hmany hJ hu hne hfull h9 hres
      v K hv hfixed hK hgen hcard hSyl hbound
  refine ⟨d,hdrow,hdcard,hodd,hq,hL,hSL,hV2,?_,hmove,?_⟩
  · have he : normalizer (d.Z1 : Set G) = centralizer (d.Z1 : Set G) :=
      le_antisymm (normalizer_le_centralizer_of_card_two d.Z1 hdcard)
        (Subgroup.centralizer_le_normalizer _)
    rw [he] at hn
    exact hn
  · let P (Z : Subgroup G) : Prop :=
      let S := (T : Subgroup G) ⊓ centralizer (Z : Set G)
      let C := M ⊓ centralizer (Z : Set G)
      let R := (pResidual 2 C).map C.subtype
      let V1 := V ⊓ centralizer (R : Set G)
      let V2 := ⁅V,R⁆
      Nat.card V1 = 4 ∧ Nat.card V2 = 4 ∧ V1 ⊔ V2 = V ∧ V1 ⊓ V2 = ⊥ ∧ Z ≤ V1 ∧
      S.relIndex (T : Subgroup G) = 2 ∧
      S ≤ normalizer (V1 : Set G) ∧ S ≤ normalizer (V2 : Set G) ∧
      (centralizer (V1 : Set G)).relIndex S = 2 ∧
      ∀ t ∈ (T : Subgroup G), t ∉ S →
        V1.map (MulAut.conj t).toMonoidHom = V2 ∧
        V2.map (MulAut.conj t).toMonoidHom = V1
    have hp : P (zpowers (v.toMul : G)) := by
      obtain ⟨hc1,hc2,hs,hi,hz⟩ := source_nine_planes T h.normalized h9 v K hv hK hcard
      exact ⟨hc1,hc2,hs,hi,hz,source_nine_plane_action T hM.1.2 h.normalized
        h9 v K hv hK hcard hSyl⟩
    exact (congrArg P hdZ).mpr hp


end CFSG.Quasithin.Chapter15.Section01
