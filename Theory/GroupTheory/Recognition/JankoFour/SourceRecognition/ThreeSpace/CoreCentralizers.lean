module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.Automizer
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.PGroup.BinaryCommutatorIndex
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.ThreeKernelParity

/-!
# Core centralizers in the source three-space

For each nonzero t in the constructed three-space Z, the literal intersection
Q_t ∩ C_G(Z) is a normal two-subgroup of C_G(Z) of order 2¹¹. Two such
intersections generate a subgroup of order 2¹⁵ inside O₂(R), where
R = K ∩ C_G(Z). The commutator [K,C_G(Z)] also lies in O₂(R).

The order calculation uses distinct index-two centralizers in the original
extraspecial core and transports it by the actual normalizer action. The full
K-action on Z then proves O₂(K) = O₂(R). The final existence theorem
constructs the three-space from IsTypeJ4, retaining any supplied cubic quotient
and Sylow, rather than assuming geometric data.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), proof of (4.4), pp.597–598,
DOI 10.1007/BF01232280. This is the core-centralizer part of that proof;
the equality R = O₂(K) = O₂(S), specialness and tensor structure require
further arguments.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
namespace ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)

theorem point_type (h : IsTypeJ4 z) {t : G} (ht : t ∈ d.space) (ht1 : t ≠ 1) :
    IsTypeJ4 t := by
  obtain ⟨n,_,he⟩ := d.normalizer_transitive t ht ht1
  have hn := type_map h (MulAut.conj n)
  change IsTypeJ4 (n*z*n⁻¹) at hn
  rwa [he] at hn

theorem S_le_point_centralizer {t : G} (ht : t ∈ d.space) : d.S ≤ centralizer t := by
  intro s hs
  exact mem_centralizer_singleton_iff.mpr (hs t ht).symm

theorem S_normalized : normalizer (d.space : Set G) ≤ normalizer (d.S : Set G) :=
  normalizer_le_normalizer_centralizer d.space

theorem coreCentralizer_le_twoCore (h : IsTypeJ4 z) {t : G}
    (ht : t ∈ d.space) (ht1 : t ≠ 1) :
    ambientCore t ⊓ d.S ≤ d.S.pCoreIn 2 := by
  let := IsExtraspecial.of_mulEquiv (LocalGeometry.coreEquivAmbient t) (d.point_type h ht ht1).extraspecial
  apply le_pCoreIn_of_normalizes ((IsExtraspecial.isPGroup 2 (ambientCore t)).to_le inf_le_left)
    inf_le_right
  apply (le_inf ?_ d.S.le_normalizer).trans inf_normalizer_le_normalizer_inf
  rw [LocalGeometry.normalizer_ambientCore (d.point_type h ht ht1)]
  exact d.S_le_point_centralizer ht

theorem coreCentralizer_le_R {t : G} (ht : t ∈ d.space) (ht1 : t ≠ 1) :
    ambientCore t ⊓ d.S ≤ d.R :=
  le_inf (inf_le_left.trans (core_le_threeSpaceCores d.space ht ht1)) inf_le_right

theorem commutator_core_S_le_twoCore (h : IsTypeJ4 z) {t : G}
    (ht : t ∈ d.space) (ht1 : t ≠ 1) :
    ⁅ambientCore t,d.S⁆ ≤ d.S.pCoreIn 2 := by
  apply (le_inf ?_ ?_).trans (d.coreCentralizer_le_twoCore h ht ht1)
  · apply le_normalizer_iff_commutator_le_left.mp
    rw [LocalGeometry.normalizer_ambientCore (d.point_type h ht ht1)]
    exact d.S_le_point_centralizer ht
  · exact le_normalizer_iff_commutator_le_right.mp
      ((d.cores_normalize t ht ht1).trans d.S_normalized)

theorem commutator_K_S_le_twoCore (h : IsTypeJ4 z) : ⁅d.K,d.S⁆ ≤ d.S.pCoreIn 2 := by
  apply commutator_iSup_le_of_relative_normal (normalizer (d.space : Set G)) d.S (d.S.pCoreIn 2)
    (fun t : {t : G // t ∈ d.space ∧ t ≠ 1} => ambientCore t.val)
  · exact d.S_normalized.trans (normalizer_le_normalizer_characteristic_image d.S (pCore 2 d.S))
  · intro t
    exact d.cores_normalize t.val t.property.1 t.property.2
  · intro t
    exact d.commutator_core_S_le_twoCore h t.property.1 t.property.2

private theorem z_mem (d : ThreeSpaceData z e X) : z ∈ d.space := by
  rw [space,d.generated]
  exact subset_closure (by simp)

private theorem r_in_space (d : ThreeSpaceData z e X) : d.r ∈ d.space := by
  rw [space,d.generated]
  exact subset_closure (by simp)

private theorem s_in_space (d : ThreeSpaceData z e X) : d.s ∈ d.space := by
  rw [space,d.generated]
  exact subset_closure (by simp)

private theorem not_in_center_line (h : IsTypeJ4 z) {t : G}
    (ht : orderOf t=2) (htz : t≠z) : t ∉ zpowers z := by
  intro hm
  have hz1 : z≠1 := by intro he; have hi := h.involution; simp [he] at hi
  have ht1 : t≠1 := by intro he; simp [he] at ht
  obtain ⟨w,_,hw⟩ := (Nat.card_eq_two_iff' (1 : zpowers z)).mp
    ((Nat.card_zpowers z).trans h.involution)
  exact htz (congrArg Subtype.val ((hw ⟨t,hm⟩ (fun he => ht1 (congrArg Subtype.val he))).trans
    (hw ⟨z,mem_zpowers z⟩ (fun he => hz1 (congrArg Subtype.val he))).symm))

theorem coreCentralizer_z_card (h : IsTypeJ4 z) :
    Nat.card (ambientCore z ⊓ d.S : Subgroup G) = 2048 := by
  let Q := ambientCore z
  let z₀ : Q := ⟨z,marker_mem_ambientCore z⟩
  let r₀ : Q := ⟨d.r,d.r_mem⟩
  let s₀ : Q := ⟨d.s,d.s_mem⟩
  let := IsExtraspecial.of_mulEquiv (LocalGeometry.coreEquivAmbient z) h.extraspecial
  have hr' := d.point_type h d.r_in_space (by
    intro he
    obtain ⟨n,hn⟩ := isConj_iff.mp d.r_conj
    have hi := h.involution
    have hz1 := (MulAut.conj n).injective (hn.trans he |>.trans (map_one _).symm)
    simp [hz1] at hi)
  have hs' : IsTypeJ4 d.s := by
    obtain ⟨n,hn⟩ := isConj_iff.mp d.s_conj
    have hh := type_map h (MulAut.conj n)
    change IsTypeJ4 (n*z*n⁻¹) at hh
    rwa [hn] at hh
  have hz₀ : orderOf z₀=2 := (orderOf_coe z₀).symm.trans h.involution
  have hr₀ : orderOf r₀=2 := (orderOf_coe r₀).symm.trans hr'.involution
  have hzZ : z₀ ∈ center Q := mem_center_iff.mpr fun q =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (LocalGeometry.ambientCore_le z q.property))
  have hrZ : r₀ ∉ center Q := by
    intro hm
    apply not_in_center_line h hr'.involution d.r_ne
    rw [← LocalGeometry.ambientCore_center_image h]
    exact ⟨r₀,hm,rfl⟩
  have hsZ : s₀ ∉ center Q := by
    intro hm
    apply not_in_center_line h hs'.involution d.s_ne
    rw [← LocalGeometry.ambientCore_center_image h]
    exact ⟨s₀,hm,rfl⟩
  let C := Subgroup.centralizer ({r₀} : Set Q)
  let D := Subgroup.centralizer ({s₀} : Set Q)
  have hCD : ¬ C ≤ D := by
    intro hCD
    have hsC : s₀ ∈ Subgroup.centralizer (C : Set Q) := fun q hq =>
      mem_centralizer_singleton_iff.mp (hCD hq)
    let : IsExtraspecial 2 (⊤ : Subgroup Q) := IsExtraspecial.of_mulEquiv topEquiv.symm inferInstance
    have hd := IsExtraspecial.ambient_involution_double_centralizer_le
      (⊤ : Subgroup Q) le_top z₀ r₀ hz₀ hzZ (mem_top _) hr₀
    have hd' : (↑(⊤ : Subgroup Q) ⊓ ↑(Subgroup.centralizer ({r₀} : Set Q)) : Set Q) =
        (Subgroup.centralizer ({r₀} : Set Q) : Set Q) := by ext q; simp
    rw [hd'] at hd
    let E := closure ({z₀,r₀} : Set Q)
    have hsE : s₀ ∈ E := hd hsC
    let W := E.map Q.subtype
    have hZW : d.space ≤ W := by
      rw [space,d.generated]
      apply (closure_le W).mpr
      intro t ht
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl
      · exact ⟨z₀,subset_closure (by simp),rfl⟩
      · exact ⟨r₀,subset_closure (by simp),rfl⟩
      · exact ⟨s₀,hsE,rfl⟩
    let : IsKleinFour E := isKleinFour_closure_pair_of_orderOf z₀ r₀ hz₀ hr₀
      (fun he => d.r_ne (congrArg Subtype.val he).symm)
      (mem_center_iff.mp hzZ r₀).symm
    have hc := card_le_of_le hZW
    rw [show Nat.card d.space=8 from d.card,card_map_of_injective Q.subtype_injective,
      IsKleinFour.card_four] at hc
    omega
  have hi : (C ⊓ D).index=4 := index_inf_eq_four_of_distinct_index_two C D
    (ExtraspecialIntersection.centralizer_index_two r₀ hrZ)
    (ExtraspecialIntersection.centralizer_index_two s₀ hsZ) hCD
  have hmap : (C ⊓ D).map Q.subtype = ambientCore z ⊓ d.S := by
    ext q
    constructor
    · rintro ⟨q,hq,rfl⟩
      refine ⟨q.property,?_⟩
      change (q:G) ∈ Subgroup.centralizer (d.space : Set G)
      rw [space,d.generated,centralizer_closure]
      intro t ht
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ht
      rcases ht with ht | ht | ht
      · rw [ht]
        exact (mem_centralizer_singleton_iff.mp (LocalGeometry.ambientCore_le z q.property)).symm
      · rw [ht]
        exact (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hq.1)).symm
      · rw [ht]
        exact (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hq.2)).symm
    · rintro ⟨hq,hS⟩
      refine ⟨⟨q,hq⟩,⟨?_,?_⟩,rfl⟩
      · exact mem_centralizer_singleton_iff.mpr (Subtype.ext (hS d.r d.r_in_space).symm)
      · exact mem_centralizer_singleton_iff.mpr (Subtype.ext (hS d.s d.s_in_space).symm)
  have hc := (C ⊓ D).card_mul_index
  rw [hi] at hc
  have hQ : Nat.card Q=8192 :=
    (Nat.card_congr (LocalGeometry.coreEquivAmbient z).toEquiv).symm.trans h.core_card
  rw [hQ] at hc
  rw [← hmap,card_map_of_injective Q.subtype_injective]
  omega

theorem coreCentralizer_card (h : IsTypeJ4 z) {t : G}
    (ht : t ∈ d.space) (ht1 : t ≠ 1) :
    Nat.card (ambientCore t ⊓ d.S : Subgroup G) = 2048 := by
  obtain ⟨n,hn,he⟩ := d.normalizer_transitive t ht ht1
  have hS : d.S.map (MulAut.conj n).toMonoidHom = d.S :=
    mem_normalizer_iff_map_conj_eq.mp (d.S_normalized hn)
  have hm : (ambientCore z ⊓ d.S).map (MulAut.conj n).toMonoidHom =
      ambientCore t ⊓ d.S := by
    rw [map_inf _ _ _ (MulAut.conj n).injective,ambientCore_map,hS]
    change ambientCore (n*z*n⁻¹) ⊓ d.S = _
    rw [he]
  rw [← hm,card_map_of_injective (MulAut.conj n).injective]
  exact d.coreCentralizer_z_card h

theorem pair_core_le_S (h : IsTypeJ4 z) : ambientCore z ⊓ ambientCore d.r ≤ d.S := by
  let I := ambientCore z ⊓ ambientCore d.r
  let := returningIntersection_elementary h d.r_conj d.r_ne
  have hZI : d.space ≤ I := inf_le_left
  intro q hq t ht
  exact congrArg Subtype.val
    (mul_comm (⟨t,hZI ht⟩ : I) (⟨q,hq⟩ : I))

theorem coreCentralizer_inf (h : IsTypeJ4 z) :
    (ambientCore z ⊓ d.S) ⊓ (ambientCore d.r ⊓ d.S) = ambientCore z ⊓ ambientCore d.r := by
  apply le_antisymm (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
  exact le_inf (le_inf inf_le_left (d.pair_core_le_S h))
    (le_inf inf_le_right (d.pair_core_le_S h))

/-- The product inside the source centralizer that will fill its two-core. -/
def coreCentralizerJoin : Subgroup G := (ambientCore z ⊓ d.S) ⊔ (ambientCore d.r ⊓ d.S)

theorem coreCentralizerJoin_le_twoCore (h : IsTypeJ4 z) :
    d.coreCentralizerJoin ≤ d.S.pCoreIn 2 := by
  have hz1 : z ≠ 1 := by intro he; have hi := h.involution; simp [he] at hi
  have hr1 : d.r ≠ 1 := by
    intro he
    obtain ⟨n,hn⟩ := isConj_iff.mp d.r_conj
    exact hz1 ((MulAut.conj n).injective (hn.trans he |>.trans (map_one _).symm))
  exact sup_le (d.coreCentralizer_le_twoCore h d.z_mem hz1)
    (d.coreCentralizer_le_twoCore h d.r_in_space hr1)

theorem coreCentralizerJoin_le_R (h : IsTypeJ4 z) : d.coreCentralizerJoin ≤ d.R := by
  have hz1 : z ≠ 1 := by intro he; have hi := h.involution; simp [he] at hi
  have hr1 : d.r ≠ 1 := by
    intro he
    obtain ⟨n,hn⟩ := isConj_iff.mp d.r_conj
    exact hz1 ((MulAut.conj n).injective (hn.trans he |>.trans (map_one _).symm))
  exact sup_le (d.coreCentralizer_le_R d.z_mem hz1)
    (d.coreCentralizer_le_R d.r_in_space hr1)

theorem coreCentralizerJoin_card (h : IsTypeJ4 z) : Nat.card d.coreCentralizerJoin = 32768 := by
  have hr1 : d.r ≠ 1 := by
    intro he
    obtain ⟨n,hn⟩ := isConj_iff.mp d.r_conj
    have hi := h.involution
    have hz1 := (MulAut.conj n).injective (hn.trans he |>.trans (map_one _).symm)
    simp [hz1] at hi
  have hn : d.S ≤ normalizer ((ambientCore z ⊓ d.S : Subgroup G) : Set G) := by
    apply (le_inf ?_ d.S.le_normalizer).trans inf_normalizer_le_normalizer_inf
    rw [LocalGeometry.normalizer_ambientCore h]
    exact d.S_le_point_centralizer d.z_mem
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (ambientCore z ⊓ d.S) (ambientCore d.r ⊓ d.S) (inf_le_right.trans hn)
  rw [d.coreCentralizer_z_card h,d.coreCentralizer_card h d.r_in_space hr1,
    d.coreCentralizer_inf h,(returning_intersection_image_orders h d.r_conj d.r_mem d.r_ne).1] at hc
  change 2048 * 2048 = 128 * Nat.card d.coreCentralizerJoin at hc
  omega

theorem coreCentralizer_normalized (h : IsTypeJ4 z) {t : G}
    (ht : t ∈ d.space) (ht1 : t ≠ 1) :
    d.S ≤ normalizer ((ambientCore t ⊓ d.S : Subgroup G) : Set G) := by
  apply (le_inf ?_ d.S.le_normalizer).trans inf_normalizer_le_normalizer_inf
  rw [LocalGeometry.normalizer_ambientCore (d.point_type h ht ht1)]
  exact d.S_le_point_centralizer ht

theorem coreCentralizerJoin_normalized (h : IsTypeJ4 z) :
    d.S ≤ normalizer (d.coreCentralizerJoin : Set G) := by
  have hz1 : z ≠ 1 := by intro he; have hi := h.involution; simp [he] at hi
  have hr1 : d.r ≠ 1 := by
    intro he
    obtain ⟨n,hn⟩ := isConj_iff.mp d.r_conj
    exact hz1 ((MulAut.conj n).injective (hn.trans he |>.trans (map_one _).symm))
  exact (le_inf (d.coreCentralizer_normalized h d.z_mem hz1)
    (d.coreCentralizer_normalized h d.r_in_space hr1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

theorem coreCentralizerJoin_le_R_twoCore (h : IsTypeJ4 z) :
    d.coreCentralizerJoin ≤ d.R.pCoreIn 2 := by
  exact le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 d.S).to_le (d.coreCentralizerJoin_le_twoCore h))
    (d.coreCentralizerJoin_le_R h) (inf_le_right.trans (d.coreCentralizerJoin_normalized h))

theorem commutator_K_S_le_R_twoCore (h : IsTypeJ4 z) : ⁅d.K,d.S⁆ ≤ d.R.pCoreIn 2 := by
  have hN : d.S ≤ normalizer (d.space : Set G) := centralizer_le_normalizer _
  have hC : ⁅d.K,d.S⁆ ≤ d.R := le_inf
    (le_normalizer_iff_commutator_le_left.mp (hN.trans (threeSpaceCores_normalizer d.space)))
    (le_normalizer_iff_commutator_le_right.mp (d.K_le_normalizer.trans d.S_normalized))
  have hn : d.R ≤ normalizer ((d.R ⊓ d.S.pCoreIn 2 : Subgroup G) : Set G) := by
    apply (le_inf d.R.le_normalizer ?_).trans inf_normalizer_le_normalizer_inf
    exact inf_le_right.trans
      (d.S.le_normalizer.trans (normalizer_le_normalizer_characteristic_image d.S (pCore 2 d.S)))
  exact (le_inf hC (d.commutator_K_S_le_twoCore h)).trans
    (le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 d.S).to_le inf_le_right) inf_le_left hn)

theorem R_twoCore_card_dvd (h : IsTypeJ4 z) : 32768 ∣ Nat.card (d.R.pCoreIn 2) :=
  d.coreCentralizerJoin_card h ▸ card_dvd_of_le (d.coreCentralizerJoin_le_R_twoCore h)

theorem K_twoCore_le_R (h : IsTypeJ4 z) : d.K.pCoreIn 2 ≤ d.R := by
  let : IsElementaryAbelian 2 d.space := d.elementary
  let := Atlas.Comparisons.Exceptional.psl3Two_simple
  obtain ⟨a⟩ := MulAut.elementaryEight_equiv_PSL3 (show Nat.card d.space=8 from d.card)
  let := a.isSimpleGroup
  have hn : ((pCore 2 d.K).map d.KAction).Normal :=
    Normal.map inferInstance d.KAction (d.KAction_surjective h)
  have hb : (pCore 2 d.K).map d.KAction = ⊥ := by
    rcases hn.eq_bot_or_eq_top with hb | ht
    · exact hb
    · have hp : IsPGroup 2 ((pCore 2 d.K).map d.KAction) := pCore_isPGroup.map d.KAction
      obtain ⟨n,hn⟩ := hp.exists_card_eq
      rw [ht,Nat.card_congr (topEquiv : (⊤ : Subgroup (MulAut d.space)) ≃* MulAut d.space).toEquiv,
        card_mulAut_of_elementary_eight d.space (show Nat.card d.space=8 from d.card)] at hn
      have hthree : 3 ∣ 2^n := by rw [← hn]; decide
      have hbad := Nat.prime_three.dvd_of_dvd_pow hthree
      norm_num at hbad
  have hk : pCore 2 d.K ≤ d.KAction.ker := by
    intro k hk
    exact mem_bot.mp (hb ▸ mem_map_of_mem d.KAction hk)
  rw [d.KAction_ker] at hk
  exact (map_mono (f := d.K.subtype) hk).trans_eq (map_subgroupOf_eq_of_le inf_le_left)

theorem K_twoCore_eq_R_twoCore (h : IsTypeJ4 z) : d.K.pCoreIn 2 = d.R.pCoreIn 2 := by
  apply le_antisymm
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 d.K) (d.K_twoCore_le_R h)
      (inf_le_left.trans (d.K.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image d.K (pCore 2 d.K))))
  · exact pCoreIn_mono_of_normalizes inf_le_left
      ((normal_subgroupOf_iff_le_normalizer inf_le_left).mp d.R_normal_in_K)

end ThreeSpaceData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The literal radical seed and commutator bound are constructed from the
source hypotheses, for the specified cubic quotient and original Sylow. -/
theorem source_three_space_coreCentralizers (h : IsTypeJ4 z)
    (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
    (X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)) :
    ∃ d : ThreeSpaceData z e X,
      (∀ t ∈ d.space, t ≠ 1 →
        Nat.card (ambientCore t ⊓ d.S : Subgroup G) = 2048 ∧
        ambientCore t ⊓ d.S ≤ d.R) ∧
      Nat.card d.coreCentralizerJoin = 32768 ∧
      d.coreCentralizerJoin ≤ d.K.pCoreIn 2 ∧
      ⁅d.K,d.S⁆ ≤ d.K.pCoreIn 2 ∧
      d.K.pCoreIn 2 = d.R.pCoreIn 2 := by
  obtain ⟨d⟩ := source_three_space_data h e X
  refine ⟨d,fun t ht ht1 => ⟨d.coreCentralizer_card h ht ht1,
    d.coreCentralizer_le_R ht ht1⟩,d.coreCentralizerJoin_card h,?_,?_,
    d.K_twoCore_eq_R_twoCore h⟩
  · rw [d.K_twoCore_eq_R_twoCore h]
    exact d.coreCentralizerJoin_le_R_twoCore h
  · rw [d.K_twoCore_eq_R_twoCore h]
    exact d.commutator_K_S_le_R_twoCore h

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
