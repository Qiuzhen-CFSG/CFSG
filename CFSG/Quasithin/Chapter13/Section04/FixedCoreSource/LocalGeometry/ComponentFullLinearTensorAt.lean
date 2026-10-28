module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentFullLinearKernelAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullTensor

/-!
# Excluding the enlarged linear tensor orbit at the original G,T

If the full centralizer orbit has two natural summands, its Sylow-fixed
point identifies the original point parabolic. The intrinsic tensor
calculation makes its Baumann subgroup equal that of the full two-core.
The original augmentation alternative therefore forces a short block,
whose cubic kernel budget contradicts the two natural layers.

The argument retains the full C_G(z) orbit and its literal action kernel.
It supplies the missing full-orbit bound in ComponentFullLinearAt, using
same-G,T structural facts and the independent earlier source inputs.
Source: Aschbacher--Smith 13.4.10(7), printed p.909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

omit [Finite G] in
private theorem central_factor_point (H Q : Subgroup G) (z d : G)
    (hQH : Q ≤ H) (hnQ : H ≤ normalizer (Q : Set G))
    (hzH : z ∈ H) (hHz : H ≤ centralizer ({z} : Set G))
    (hd : d ∈ Q ⊔ zpowers z) (hdc : d ∉ centralizer (H : Set G)) :
    ∃ w : Q, w ≠ 1 ∧ H ⊓ centralizer ({d} : Set G) =
      H ⊓ centralizer ({w.val} : Set G) := by
  have hcH : zpowers z ≤ H := zpowers_le.mpr hzH
  have hc : zpowers z ≤ centralizer (H : Set G) := by
    apply le_centralizer_iff.mpr
    simpa only [zpowers_eq_closure,centralizer_closure] using hHz
  let : (Q.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hnQ
  have hdH : d ∈ H := sup_le hQH hcH hd
  have hd' : (⟨d,hdH⟩ : H) ∈ Q.subgroupOf H ⊔ (zpowers z).subgroupOf H := by
    rw [←subgroupOf_sup hQH hcH]
    exact hd
  obtain ⟨a,ha,c,hc',he⟩ := mem_sup_of_normal_left.mp hd'
  have he' : a.val*c.val = d := congrArg Subtype.val he
  refine ⟨⟨a.val,ha⟩,?_,?_⟩
  · intro hh
    have h1 : a.val = 1 := congrArg Subtype.val hh
    rw [h1,one_mul] at he'
    exact hdc (he' ▸ hc hc')
  · ext x
    have hcx (hx : x ∈ H) : x*c.val = c.val*x := hc hc' x hx
    simp only [mem_inf,mem_centralizer_singleton_iff,←he']
    constructor
    · rintro ⟨hx,he⟩
      refine ⟨hx,mul_right_cancel (b := c.val) ?_⟩
      simpa only [mul_assoc,←hcx hx] using he
    · rintro ⟨hx,he⟩
      exact ⟨hx,by rw [←mul_assoc,he,mul_assoc,hcx hx,mul_assoc]⟩

private theorem full_point_of_split
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (Q : Subgroup G)
    (hQH : Q ≤ centralizer ({z.val} : Set G))
    (hnQ : centralizer ({z.val} : Set G) ≤ normalizer (Q : Set G))
    (hsplit : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G))
      (centralizer ({z.val} : Set G)) = Q ⊔ zpowers z.val) :
    ∃ w : Q, w ≠ 1 ∧ (T : Subgroup G) ≤ centralizer ({w.val} : Set G) ∧
      (centralizer ({z.val} : Set G)) ⊓ centralizer ({w.val} : Set G) =
        Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) := by
  let H := centralizer ({z.val} : Set G)
  have hdM := fixed_generator_centralizer_at h structural D m
    ⟨m.constant.property,m.constant_fixed⟩
    (fun hh => m.constant_ne_one (Subtype.ext hh))
  have hd : m.constant.val ∈ Q ⊔ zpowers z.val := hsplit ▸
    le_conjugateSpanBy _ _ (m.constant_mem_central_four_at h structural).2
  have hdc : m.constant.val ∉ centralizer (H : Set G) := by
    intro hh
    apply hKM
    rw [←hdM]
    exact fun k hk => mem_centralizer_singleton_iff.mpr (hh k (hKz hk))
  obtain ⟨w,hw,he⟩ := central_factor_point H Q z.val m.constant.val hQH hnQ
    (mem_centralizer_singleton_iff.mpr rfl) le_rfl hd hdc
  have hTH := Solvable.original_sylow_le_centralizer hzT
  refine ⟨w,hw,?_,?_⟩
  · intro t ht
    apply (he.le ⟨hTH ht,?_⟩).2
    exact mem_centralizer_singleton_iff.mpr
      (((mem_omegaOneCenterAmbient_iff _ _).mp
        (m.constant_mem_central_four_at h structural).2).2.2 t ht)
  · rw [←he,hdM,hM,inf_comm]
    exact (ordinary_augmentation_point_parabolic D m eL z hzT hzL).symm

/-- In the enlarged doubled row, the original point radical has the Baumann
subgroup of the full centralizer two-core. Its normalizer escapes M. -/
theorem linear_full_tensor_baumann_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (q : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G))
      (centralizer ({z.val} : Set G)),K⁆ : Subgroup G) ≃*
        Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let Q := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (centralizer ({z.val} : Set G)),K⁆
      ∀ (k : K) (v : Q),
        (e (Q.normalizerMonoidHom ⟨k.val,normalizer_commutator_ge_right _ _ k.property⟩ v)).toAdd =
          (BinaryLinearThree.W.prod BinaryLinearThree.W)
            (q (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) :
    let H := centralizer ({z.val} : Set G)
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ (H.pCoreIn 2) ∧
      ChapterB.baumann R = ChapterB.baumann (H.pCoreIn 2) ∧
      ¬ normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G) := by
  let H := centralizer ({z.val} : Set G)
  let Q := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H,K⁆
  have hTH := Solvable.original_sylow_le_centralizer hzT
  obtain ⟨eL⟩ := ordinary_original_of_linear_component_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  obtain ⟨_,hrQ,_,hsplit,_,_,_,hQW,hnQ,_⟩ := component_full_orbit_at h₀ h structural
    D m hindex z hzT hzL hKz hHN hKM
  have hQH : Q ≤ H := hQW.trans (Solvable.centralizerOmegaOrbit_le hzT)
  let Ki := K.subgroupOf H
  let Qi := Q.subgroupOf H
  let : Ki.Normal := normal_subgroupOf_of_le_normalizer hHN
  let : Qi.Normal := hrQ.normal
  let : IsElementaryAbelian 2 Qi := hrQ.elementary
  let ek : Ki ≃* K := subgroupOfEquivOfLe hKz
  let eq : Qi ≃* Q := subgroupOfEquivOfLe hQH
  let qi := (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).comp ek.toMonoidHom
  have hqi : Function.Surjective qi :=
    (q.surjective.comp (QuotientGroup.mk'_surjective _)).comp ek.surjective
  have hei (k : Ki) (v : Qi) : ((eq.trans e) (MulAut.conjNormal k.val v)).toAdd =
      (BinaryLinearThree.W.prod BinaryLinearThree.W) (qi k) ((eq.trans e) v).toAdd :=
    he (ek k) (eq v)
  have hker := (linear_component_full_orbit_kernels_at hl h₀ h structural modules
    D m h1332 fixed hindex hM z hzT hzL hKz hHN hKM hfK eK).2.2.2.1
  have hC : centralizer (Qi : Set H) = pCore 2 H := by
    apply map_injective H.subtype_injective
    rw [show (centralizer (Qi : Set H)).map H.subtype = H ⊓ centralizer (Q : Set G) from ?_]
    exact hker
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,fun v hv => congrArg Subtype.val (ha ⟨v,hQH hv⟩ hv)⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,(fun v hv => Subtype.ext (hc v.val hv)),rfl⟩
  obtain ⟨w,hw,hTw,hP⟩ := full_point_of_split h structural D m eL hM z hzT hzL
    hKz hKM Q hQH hnQ hsplit
  let wi := eq.symm w
  have hwi : wi ≠ 1 := fun hh => hw (by simpa [wi] using congrArg eq hh)
  obtain ⟨S,hS⟩ := (T.subtype hTH).exists_sylow_map_eq_inf_of_normal Ki
  have hSw : (S : Subgroup Ki).map Ki.subtype ≤ centralizer ({wi.val} : Set H) := by
    rw [hS]
    intro k hk
    exact mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp (hTw hk.1)))
  let P := centralizer ({wi.val} : Set H)
  let R := P.pCoreIn 2
  have hQP : pCore 2 H ≤ P := by
    rw [←hC]
    exact fun a ha => mem_centralizer_singleton_iff.mpr (ha wi.val wi.property).symm
  have hQR : pCore 2 H ≤ R := le_pCoreIn_of_normalizes pCore_isPGroup hQP
    (by rw [normalizer_eq_top]; exact le_top)
  have hQiR : Qi ≤ R := hrQ.le_pCore.trans hQR
  have hRC : pCore 2 H = R ⊓ centralizer (Qi : Set H) := by
    rw [hC,inf_eq_right.mpr hQR]
  have hJ := ChapterB.doubled_overgroup_point_thompson Ki Qi qi hqi (eq.trans e) hei wi hwi S hSw
  have hb := ChapterB.lemma_B_2_10_centralizing Qi R hQiR hQR hRC (by
    rwa [ChapterB.thompsonJ_zero])
  have hPm : P.map H.subtype = Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) := by
    rw [←hP]
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hc)),rfl⟩
  have hj := congrArg (fun A : Subgroup H => A.map H.subtype) hb.1
  simp only [ChapterB.thompsonJ_zero] at hj
  change (elementaryAbelianMaxJ (P.pCoreIn 2)).map H.subtype =
    (elementaryAbelianMaxJ (pCore 2 H)).map H.subtype at hj
  rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
    ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
    map_pCoreIn_of_injective 2 P H.subtype H.subtype_injective,hPm] at hj
  have hm := congrArg (fun A : Subgroup H => A.map H.subtype) hb.2.1
  change (ChapterB.baumann (P.pCoreIn 2)).map H.subtype =
    (ChapterB.baumann (pCore 2 H)).map H.subtype at hm
  dsimp only [ChapterB.baumann,ChapterB.thompsonAlpha] at hm
  rw [baumann_map_injective H.subtype H.subtype_injective,
    baumann_map_injective H.subtype H.subtype_injective,
    map_pCoreIn_of_injective 2 P H.subtype H.subtype_injective,hPm] at hm
  change ChapterB.baumann ((Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2) =
    ChapterB.baumann (H.pCoreIn 2) at hm
  refine ⟨hj,hm,?_⟩
  rw [hm]
  intro hbound
  exact hKM (hKz.trans ((H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))).trans
      ((normalizer_le_normalizer_baumann (H.pCoreIn 2)).trans hbound)))

private theorem full_tensor_symmetricFour_residual :
    primeToResidual 3 (Equiv.Perm (Fin 4)) = alternatingGroup (Fin 4) := by
  rw [←twoResidual_eq_primeToResidual_three,Theory.SpecificGroups.SymmetricFourResidual.residual_eq]
  rw [IsPiGroup_iff]
  intro p hp
  rw [Nat.card_perm,Nat.card_fin] at hp
  have hh : p.val ∣ 2 ^ 3 * 3 := hp
  change p.val = 2 ∨ p.val = 3
  rcases p.property.dvd_mul.mp hh with h2 | h3
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow h2) |>.resolve_left p.property.ne_one)
  · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left p.property.ne_one)

private theorem full_tensor_residual_alternatingFour (C J Q : Subgroup G)
    (hJ : (primeToResidual 3 C).map C.subtype = J)
    (q : C →* Equiv.Perm (Fin 4)) (hq : Function.Surjective q)
    (hqk : q.ker = Q.subgroupOf C) :
    ∃ f : J →* alternatingGroup (Fin 4), Function.Surjective f ∧
      f.ker = Q.subgroupOf J := by
  let R := primeToResidual 3 C
  have hJC : J ≤ C := hJ ▸ map_subtype_le R
  have hr : R.map q = alternatingGroup (Fin 4) :=
    (map_primeToResidual_of_surjective 3 q hq).trans full_tensor_symmetricFour_residual
  let f : J →* alternatingGroup (Fin 4) :=
    (q.comp (inclusion hJC)).codRestrict _ (fun j => by
      rw [←hr]
      have hj := hJ.ge j.property
      obtain ⟨c,hc,he⟩ := hj
      have he' : c = inclusion hJC j := Subtype.ext he
      exact mem_map_of_mem q (he' ▸ hc))
  refine ⟨f,?_,?_⟩
  · intro a
    have ha : a.val ∈ R.map q := hr.symm ▸ a.property
    obtain ⟨c,hc,hca⟩ := ha
    exact ⟨⟨c.val,hJ.le (mem_map_of_mem C.subtype hc)⟩,Subtype.ext hca⟩
  · ext j
    change f j = 1 ↔ j.val ∈ Q
    rw [Subtype.ext_iff]
    change inclusion hJC j ∈ q.ker ↔ _
    rw [hqk]
    rfl

/-- The doubled natural full-centralizer orbit is impossible. -/
theorem linear_full_orbit_not_doubled_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (q : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G))
      (centralizer ({z.val} : Set G)),K⁆ : Subgroup G) ≃*
        Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let Q := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (centralizer ({z.val} : Set G)),K⁆
      ∀ (k : K) (v : Q),
        (e (Q.normalizerMonoidHom ⟨k.val,normalizer_commutator_ge_right _ _ k.property⟩ v)).toAdd =
          (BinaryLinearThree.W.prod BinaryLinearThree.W)
            (q (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) : False := by
  let H := centralizer ({z.val} : Set G)
  let Q := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H,K⁆
  obtain ⟨eL⟩ := ordinary_original_of_linear_component_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  rcases ordinary_augmentation_baumann_alternative_of_largeDistance_at hl h structural
      D m eL z hzT hzL with hbound | hshort
  · exact (linear_full_tensor_baumann_at hl h₀ h structural modules D m h1332 fixed hindex
      hM z hzT hzL hKz hHN hKM hfK eK q e he).2.2 hbound
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  obtain ⟨DK,q0,e0,he0,_,_,_,_⟩ := linear_component_marking_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  obtain ⟨hJK,hrec,_⟩ := ordinary_linear_component_residuals_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK eL
  obtain ⟨w,hw,hC⟩ := component_fixed_generator_point_at h₀ h structural m hzT hz1
    hKz ((Solvable.original_sylow_le_centralizer hzT).trans hHN) hKM
  obtain ⟨p,hp,hpk⟩ := BinaryLinearThree.natural_point_centralizer K _ DK.normalizes q0 e0 he0 w hw
  rw [Solvable.firstCentralizerResidual_eq,hC] at hrec
  obtain ⟨f,hf,hfk⟩ := full_tensor_residual_alternatingFour _ _ (K.pCoreIn 2) hrec p hp hpk
  obtain ⟨_,hQcore,hQJ,_⟩ := component_full_orbit_placement_at h₀ h structural D m hindex
    eL hM z hzT hzL hKz hHN hKM
  exact core_block_excludes_doubled_component D m hshort eL z hzL K Q hJK
    (normalizer_commutator_ge_right _ _) hQcore hQJ q e he f hf hfk

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
