module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.JankoFour.NormalFourPlacement
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.FourGroupIrreducible
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.JankoFourExclusion
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.PlaneGeometry
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.SecondAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.OriginalSource

/-!
# The original normal four-group excludes J₄ in rank two

The faithful plane in the literal component centralizer quotient is
irreducible under its full normalizer. The concrete J₄ normal-four placement
puts its local normalizer in max1 or a specified conjugate of max4.
Characteristic-two maximality then identifies that overgroup with the local
group; each has solvable radical of order prime to nine, contradicting
the original rank-two shadow. No maximal Sylow-overgroup cover is needed.

Source: Aschbacher--Smith, 15.3.41--42, printed p.1138.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.JankoFourExclusion
open Janko4.LocalStructure.SymmetricLinear
open Janko4.LocalStructure.RankTwoRadicalBounds
open Janko4.OuterReduction.OddIndex
open Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
open MatrixNormalizerBounds
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  Janko4.Cardinality.max1Subgroup max4Subgroup

variable {X : Type*} [Group X] [Finite X]

private theorem exclude_local_overgroup {M Y S : Subgroup X}
    (d : LocalConfiguration (⊤ : Subgroup X) M Y S)
    (e : X ≃* Janko4.Model) {Q : Subgroup Janko4.Model}
    (hMQ : M.map e.toMonoidHom ≤ Q)
    {A : Type*} [Group A] [Finite A] (f : Q ≃* A)
    (hc : HasCharacteristicTwo A)
    (h9 : ¬ 9 ∣ Nat.card (solvableRadical A)) : False := by
  let R := Q.map e.symm.toMonoidHom
  have hR : R.map e.toMonoidHom = Q := by simp [R, map_map]
  let eR : R ≃* A := (e.subgroupMap R).trans ((MulEquiv.subgroupCongr hR).trans f)
  have hMR : M ≤ R := by
    simpa [R, map_map] using map_mono (f := e.symm.toMonoidHom) hMQ
  have hchar : generalizedFitting R = pCore 2 R :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      ((Theory.Quasithin.centralizer_pCore_le_iff 2 eR).mpr hc)
  have he : R = M := d.maximal R hMR hchar
  exact no_localConfiguration_of_radical_bound d
    ((MulEquiv.subgroupCongr he.symm).trans eR) h9

private noncomputable def markedSylow : Sylow 2 Janko4.Model :=
  twoSubgroup_isPGroup.toSylow (by
    rw [twoSubgroup, index_map_subtype, localTwoSubgroup_index]
    exact Nat.Prime.not_dvd_mul Nat.prime_two (by decide)
      Janko4.OuterReduction.max1_odd_index_unconditional)

/-- The genuine rank-two local configuration is incompatible with the J₄
model when its original fully moved normal four-group is supplied. -/
theorem no_localConfiguration_of_normal_four {M Y S V : Subgroup X}
    (d : LocalConfiguration (⊤ : Subgroup X) M Y S)
    (e : X ≃* Janko4.Model) (hVS : V ≤ S)
    (helem : IsElementaryAbelian 2 V) (hcard : Nat.card V = 4)
    (hMN : M ≤ normalizer (V : Set X))
    (hi : ∀ B : Subgroup X, B ≤ V →
      normalizer (V : Set X) ≤ normalizer (B : Set X) → B = ⊥ ∨ B = V) : False := by
  obtain ⟨P, hP⟩ := d.sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Janko4.Model
    (P.mapSurjective (f := e.toMonoidHom) e.surjective) markedSylow
  let eG : X ≃* Janko4.Model := e.trans (MulAut.conj g)
  have hS : S.map eG.toMonoidHom = twoSubgroup := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((P : Subgroup X).map e.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = twoSubgroup at hh
    have he : eG.toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by
      ext x
      rfl
    rw [he]
    simpa only [map_map, hP] using hh
  let A := V.map eG.toMonoidHom
  have hMNA : M.map eG.toMonoidHom ≤ normalizer (A : Set Janko4.Model) := by
    rw [← map_equiv_normalizer_eq]
    exact map_mono hMN
  have hAS : A ≤ twoSubgroup := hS ▸ map_mono hVS
  have hSN : twoSubgroup ≤ normalizer (A : Set Janko4.Model) := by
    rw [← hS]
    exact (map_mono d.sylow_le).trans hMNA
  have hAi : ClosureNormalizerIrreducible A := by
    intro B hBA hBN
    have hBV : B.map eG.symm.toMonoidHom ≤ V := by
      simpa [A, map_map] using map_mono (f := eG.symm.toMonoidHom) hBA
    have hNB : normalizer (V : Set X) ≤
        normalizer (B.map eG.symm.toMonoidHom : Set X) := by
      have hh := map_mono (f := eG.symm.toMonoidHom) hBN
      rw [map_equiv_normalizer_eq, map_equiv_normalizer_eq] at hh
      simpa [A, map_map] using hh
    rcases hi _ hBV hNB with h | h
    · left
      have hh := congrArg (Subgroup.map eG.toMonoidHom) h
      simpa [map_map] using hh
    · right
      have hh := congrArg (Subgroup.map eG.toMonoidHom) h
      simpa [A, map_map] using hh
  let : IsElementaryAbelian 2 V := helem
  have hAe : IsElementaryAbelian 2 A := IsElementaryAbelian.map eG.toMonoidHom
  have hAc : Nat.card A = 4 := (card_map_of_injective eG.injective).trans hcard
  rcases RankOne.SporadicModels.JankoFour.normal_four_normalizer_placement
      A hAS hSN hAe hAi hAc with h | h
  · exact exclude_local_overgroup d eG (hMNA.trans h) (MulEquiv.refl _)
      Janko4.LocalStructure.max1_twoCore_centralizer_le max1_radical_not_nine
  · let a := MulAut.conj ThirdConjugacy.conjugator
    exact exclude_local_overgroup d eG (hMNA.trans h)
      (a.subgroupMap max4Subgroup).symm max4_twoCore_centralizer_le
      (max4_radical_not_nine_of_quotient max4QuotientEquiv)

private theorem theta_map_eq_self {A B : Type*} [Group A] [Group B]
    (f : A →* B) (Y : Subgroup A) (hY : theta Y = Y) :
    theta (Y.map f) = Y.map f := by
  apply le_antisymm (theta_le _) ?_
  conv_lhs => rw [← hY]
  rw [theta, MonoidHom.map_closure, closure_le]
  rintro _ ⟨y, ⟨hy, ho⟩, rfl⟩
  have hd : orderOf (f y) ∣ 3 := ho ▸ orderOf_map_dvd f y
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with he | he
  · rw [orderOf_eq_one_iff.mp he]
    exact one_mem _
  · exact subset_closure ⟨mem_map_of_mem f hy, he⟩

variable {G : Type*} [Group G] [Finite G]
variable {I L M Y S V : Subgroup G} [(L.subgroupOf I).Normal]

/-- The plane is transported through the literal I/C_I(L), with the full
normalizer irreducibility derived from the original commutator action. -/
theorem exclusion_of_original_four_group
    (c : ComponentSetup I L M Y S) (e : L ⧸ pCore 2 L ≃* Janko4.Model)
    (hVS : V ≤ S) (helem : IsElementaryAbelian 2 V) (hcard : Nat.card V = 4)
    (hMV : M ⊓ I ≤ normalizer (V : Set G)) (hcomm : ⁅V,Y⁆ = V) : False := by
  let q := centralizerQuotientMap (L.subgroupOf I)
  let : IsElementaryAbelian 2 V := helem
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  let : IsKleinFour V := ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩
  have hSI : S ≤ I := c.join_eq ▸ le_sup_right
  have hVI := hVS.trans hSI
  have hYI := c.yplus_le.trans c.component_le
  have hYM : Y ≤ M ⊓ I := c.theta_eq ▸ theta_le (M ⊓ I)
  have hgen : theta Y = Y := by rw [← c.theta_eq, theta_idempotent]
  have hnY : Y ≤ normalizer (V : Set G) := hYM.trans hMV
  let f : V →* componentImage I L V := (q.subgroupMap (V.subgroupOf I)).comp
    (subgroupOfEquivOfLe hVI).symm.toMonoidHom
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    rw [MonoidHom.mem_ker, Subtype.ext_iff] at hx
    change q ⟨x,hVI x.property⟩ = 1 at hx
    have hk : (⟨(x : G),hVI x.property⟩ : I) ∈ q.ker := hx
    rw [component_kernel_eq I L c.component_le] at hk
    have hh : (x : G) ∈ V ⊓ centralizer (Y : Set G) :=
      ⟨x.property,centralizer_le c.yplus_le hk⟩
    rw [RankOne.fourGroup_centralizer_eq_bot hgen hnY hcomm] at hh
    exact Subtype.ext hh
  let eV : V ≃* componentImage I L V := MulEquiv.ofBijective f
    ⟨hf,(q.subgroupMap_surjective _).comp (subgroupOfEquivOfLe hVI).symm.surjective⟩
  let : IsElementaryAbelian 2 (V.subgroupOf I) := IsElementaryAbelian.subgroupOf hVI
  let : IsElementaryAbelian 2 (componentImage I L V) := IsElementaryAbelian.map q
  let : IsKleinFour (componentImage I L V) :=
    ⟨(Nat.card_congr eV.toEquiv).symm.trans IsKleinFour.card_four,
      (Monoid.exponent_eq_of_mulEquiv eV).symm.trans IsKleinFour.exponent_two⟩
  have hnorm : M.subgroupOf I ≤ normalizer (V.subgroupOf I : Set I) := by
    rw [← subgroupOf_normalizer_eq hVI]
    exact fun x hx => hMV ⟨hx,x.property⟩
  have hnormq : componentImage I L M ≤
      normalizer (componentImage I L V : Set (ComponentQuotient I L)) :=
    (map_mono hnorm).trans ((V.subgroupOf I).le_normalizer_map q)
  have hgenI : theta (Y.subgroupOf I) = Y.subgroupOf I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [theta_map_of_injective I.subtype I.subtype_injective,
      map_subgroupOf_eq_of_le hYI,hgen]
  have hgenq : theta (componentImage I L Y) = componentImage I L Y :=
    theta_map_eq_self q _ hgenI
  have hcommI : ⁅V.subgroupOf I,Y.subgroupOf I⁆ = V.subgroupOf I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVI,map_subgroupOf_eq_of_le hYI,hcomm]
  have hcommq : ⁅componentImage I L V,componentImage I L Y⁆ = componentImage I L V := by
    change ⁅(V.subgroupOf I).map q,(Y.subgroupOf I).map q⁆ = (V.subgroupOf I).map q
    rw [← map_commutator,hcommI]
  have dc : LocalConfiguration (⊤ : Subgroup (ComponentQuotient I L))
      (componentImage I L M) (componentImage I L Y) (componentImage I L S) := by
    simpa only [componentImage_eq_top_of_inner c e Janko4.AdequateLocal.conj_surjective]
      using c.quotient_local
  apply no_localConfiguration_of_normal_four dc
    (ambientModelOfInner c e Janko4.AdequateLocal.conj_surjective)
    (show componentImage I L V ≤ componentImage I L S from map_mono (fun _ hx => hVS hx))
    inferInstance ((Nat.card_congr eV.toEquiv).symm.trans hcard) hnormq
  exact RankOne.fourGroup_normalizer_irreducible hgenq
    ((map_mono (comap_mono (hYM.trans inf_le_left))).trans hnormq) hcommq

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.JankoFourExclusion

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.JankoFourExclusion
variable {G : Type*} [Group G] [Finite G]
open OutsideStructure.LocalBranches ChapterA.Section05To06

/-- The Sylow subgroup already fixes both plane labels. Its image is Sylow
in the two-group of label permutations, so all of M∩I fixes the labels. -/
private theorem local_normalizes_plane (d : CharacteristicTwo.LocalData G)
    {I : Subgroup G} (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (i : OrthogonalPlaneIndex) : d.M ⊓ I ≤ normalizer (d.action.plane i : Set G) := by
  have hPM : (P : Subgroup I) ≤ d.M.subgroupOf I := by
    intro x hx
    exact d.sylow_le ((hP ▸ mem_map_of_mem I.subtype hx).1)
  let P' := P.subtype hPM
  let j : d.M.subgroupOf I →* d.M :=
    { toFun x := ⟨x.val.val,x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  let f : d.M.subgroupOf I →* OrthogonalPlaneIndex :=
    RegularWreathProduct.rightHom.comp (d.action.actor.comp j)
  have hp : IsPGroup 2 OrthogonalPlaneIndex := IsPGroup.of_card (n := 1) (by
    norm_num [OrthogonalPlaneIndex,Nat.card_eq_fintype_card])
  let Q := P'.mapSurjective f.rangeRestrict_surjective
  have htop : (⊤ : Subgroup f.range) ≤ Q :=
    ((hp.to_subgroup f.range).to_subgroup ⊤).le_sylow_of_normal Q
  rintro x ⟨hxM,hxI⟩
  let xm : d.M.subgroupOf I := ⟨⟨x,hxI⟩,hxM⟩
  obtain ⟨s,hs,he⟩ := htop (show f.rangeRestrict xm ∈ (⊤ : Subgroup f.range) from trivial)
  have hsS : s.val.val ∈ d.S := hP ▸ mem_map_of_mem I.subtype hs
  have hf : f s = 1 := plane_actor_shift_eq_one d.action (j s) i
    (s_normalizes_plane d i hsS)
  have he' : f s = f xm := congrArg Subtype.val he
  have hh : (⟨x,hxM⟩ : d.M) ∈
      (normalizer (d.action.plane i : Set G)).subgroupOf d.M := by
    rw [d.action.plane_normalizer_eq_comap,OrthogonalGeometry.setwise_plane_eq_ker]
    exact he'.symm.trans hf
  exact hh

private theorem selected_plane_commutator (d : CharacteristicTwo.LocalData G)
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) : ⁅d.V₂,d.Yplus⁆ = d.V₂ := by
  rcases d.choice with he | hs
  · rw [he]
    apply le_antisymm
      (le_normalizer_iff_commutator_le_left.mp (y_normalizes_plane d _))
    have hc := (residualY_fullActionCoordinateFacts d.action h7).commutator_self
      1 (Multiplicative.ofAdd (1 : ZMod 2)) (by decide)
    exact hc.ge.trans (commutator_mono le_rfl ((map_subtype_le _).trans inf_le_left))
  · exact (second_choice_commutator d hs h7).2

/-- The J₄ exclusion on the literal original planes and component quotient.
The only remaining input record is the genuine preceding 15.3.41 output. -/
theorem exclusion_from_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I L : Subgroup G} [(L.subgroupOf I).Normal]
    (c : ComponentSetup I L d.M d.Yplus d.S)
    (e : L ⧸ pCore 2 L ≃* Janko4.Model) : False := by
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  obtain ⟨himage,_,_,_,_,_,_⟩ :=
    source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne
  obtain ⟨P,hP⟩ := c.sylow
  exact exclusion_of_original_four_group c e
    ((d.action.plane_le _).trans (v_le_s d))
    (d.action.elementary_of_le (d.action.plane_le _)) (d.action.card_plane _)
    (local_normalizes_plane d P hP _) (selected_plane_commutator d himage)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.JankoFourExclusion
