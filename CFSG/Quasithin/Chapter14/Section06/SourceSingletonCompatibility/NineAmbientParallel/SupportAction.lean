module
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.NineAmbientParallel.SupportPlanes
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.NinePointSylow
public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# Actual cubic support lifts and their critical action

In the elementary-nine singleton, abelian Sylow images and minimal normality
make every quotient involution invert the odd residual. Hence the original
critical spans normalize each cubic preimage, its two-residual and its
commutator support. The two supports have order eight, meet in Z and span
[U,J] of order32, through the original quotient U → U/Z.

The opposite critical point meets neither support: the other cubic fixes
its quotient image, and original point-centralizer lifting would otherwise
put an element of order three in a two-group image. Intersecting each
support with the literal critical core denominator therefore centralizes
the opposite span. Both residual preimages and both core labels are kept.

These are ambient restrictions, not the exclusion of E₉:C₄. The remaining
ambient contradiction is not asserted here. No 14.6.13 alternative is used.
Source: Aschbacher--Smith, 14.6.2 and 14.6.12, printed pp.1021,1031;
D.2.17(3), p.188, and F.9.13--17, pp.322--324 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

open OddCriticalPair.OrthogonalSource

/-- Every involution in the same original quotient inverts its full odd residual. -/
theorem source_singleton_nine_involution_inverts
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9)
    (t : J ⧸ pCore 2 J) (ht : orderOf t = 2) :
    ∀ x ∈ pResidual 2 (J ⧸ pCore 2 J), t * x * t⁻¹ = x⁻¹ := by
  let P := pResidual 2 (J ⧸ pCore 2 J)
  obtain ⟨p,_,hE,_,_,hmin⟩ := source_solvable_minimal_elementary_residual
    hG T hempty hM hu hmany hcard e hab J hJ hs
  let := hE
  have hSyl (S : Sylow 2 (J ⧸ pCore 2 J)) : IsMulCommutative S := by
    let := (source_singleton_nine_quotient_structure
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine).2 S |>.1
    infer_instance
  have hfixed := primitive_residual_involution_fixedFree
    (pCore_quotient_pCore_eq_bot 2) hmin hSyl t ht
  have ht2 : t*t=1 := by simpa only [ht,pow_two] using pow_orderOf_eq_one t
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left ht2
  intro x hx
  have hy : t*x*t⁻¹ ∈ P := Subgroup.Normal.conj_mem inferInstance x hx t
  have hcomm : x*(t*x*t⁻¹)=(t*x*t⁻¹)*x :=
    congrArg Subtype.val (mul_comm (⟨x,hx⟩ : P) ⟨_,hy⟩)
  have hc : (t*x*t⁻¹)*x ∈ P ⊓ centralizer ({t} : Set (J ⧸ pCore 2 J)) := by
    refine ⟨P.mul_mem hy hx, mem_centralizer_singleton_iff.mpr ?_⟩
    apply mul_right_cancel (b := t⁻¹)
    calc
      ((t*x*t⁻¹)*x)*t*t⁻¹ = (t*x*t⁻¹)*x := by group
      _ = x*(t*x*t⁻¹) := hcomm.symm
      _ = t*((t*x*t⁻¹)*x)*t⁻¹ := by
        rw [hti]
        simp only [←mul_assoc,ht2,one_mul]
  exact mul_eq_one_iff_eq_inv.mp (show (t*x*t⁻¹)*x=1 from hfixed.le hc)

/-- Every original critical span preserves each cubic support and its full
residual lift. -/
theorem source_singleton_nine_critical_support_normalizers
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9)
    (B : Subgroup (J ⧸ pCore 2 J)) (hB : B ≤ pResidual 2 (J ⧸ pCore 2 J)) :
    let A := B.comap (QuotientGroup.mk' (pCore 2 J))
    let R := ((pResidual 2 A).map A.subtype).map J.subtype
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ i : h.CriticalEndpoint,
      actorImage J (i.conjugate D.UH) ≤ normalizer (B : Set (J ⧸ pCore 2 J)) ∧
      i.conjugate D.UH ≤ normalizer (A.map J.subtype : Set G) ∧
      i.conjugate D.UH ≤ normalizer (R : Set G) ∧
      i.conjugate D.UH ≤ normalizer (⁅D.UH,R⁆ : Subgroup G) := by
  let q := QuotientGroup.mk' (pCore 2 J)
  let A := B.comap q
  let R₀ := (pResidual 2 A).map A.subtype
  let R := R₀.map J.subtype
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  have hb := (source_rankTwo_critical_track_bounds
    hG T hempty hM hu hmany hcard e hab J hJ.1).1
  change ∀ i : h.CriticalEndpoint, _
  intro i
  have hI : Nat.card (actorImage J (i.conjugate D.UH)) = 2 :=
    (source_singleton_nine_critical_image
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).1
  have hn : actorImage J (i.conjugate D.UH) ≤ normalizer (B : Set (J ⧸ pCore 2 J)) := by
    intro x hx
    by_cases hx1 : x=1
    · exact hx1 ▸ one_mem _
    have hx2 : x^2=1 := by
      have hh := pow_card_eq_one' (x := (⟨x,hx⟩ : actorImage J (i.conjugate D.UH)))
      rw [hI] at hh
      exact congrArg Subtype.val hh
    have hinv := source_singleton_nine_involution_inverts
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine x
      (orderOf_eq_prime hx2 hx1)
    apply mem_normalizer_iff.mpr
    intro y
    constructor
    · intro hy
      rw [hinv y (hB hy)]
      exact B.inv_mem hy
    · intro hy
      have hxP : x ∈ normalizer (pResidual 2 (J ⧸ pCore 2 J) : Set _) :=
        le_normalizer_of_normal (mem_top x)
      have hyP := (mem_normalizer_iff.mp hxP y).mpr (hB hy)
      rw [hinv y hyP] at hy
      exact B.inv_mem_iff.mp hy
  have hnA : (i.conjugate D.UH).subgroupOf J ≤ normalizer (A : Set J) :=
    (map_le_iff_le_comap.mp hn).trans (B.le_normalizer_comap q)
  have hnR : (i.conjugate D.UH).subgroupOf J ≤ normalizer (R₀ : Set J) :=
    hnA.trans (normalizer_le_normalizer_characteristic_image A (pResidual 2 A))
  have hlift : i.conjugate D.UH ≤ normalizer (A.map J.subtype : Set G) := by
    have hh := (map_mono (f := J.subtype) hnA).trans (A.le_normalizer_map J.subtype)
    rwa [map_subgroupOf_eq_of_le (show i.conjugate D.UH ≤ J from i.large_le hb)] at hh
  have hres : i.conjugate D.UH ≤ normalizer (R : Set G) := by
    have hh := (map_mono (f := J.subtype) hnR).trans (R₀.le_normalizer_map J.subtype)
    rwa [map_subgroupOf_eq_of_le (show i.conjugate D.UH ≤ J from i.large_le hb)] at hh
  refine ⟨hn,hlift,hres,?_⟩
  intro x hx
  have hnU : x ∈ normalizer (D.UH : Set G) :=
    a.normalizes (i.large_le hb hx)
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (⁅D.UH,R⁆ : Subgroup G).map (MulAut.conj x).toMonoidHom = ⁅D.UH,R⁆
  rw [map_commutator]
  exact congrArg₂ (fun X Y : Subgroup G => ⁅X,Y⁆)
    (mem_normalizer_iff_map_conj_eq.mp hnU)
    (mem_normalizer_iff_map_conj_eq.mp (hres hx))


omit hG T hempty hM hu hmany hcard e hab [Finite G] in
private theorem moved_support_image
    {J U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction J U Z)
    (hspan : movedSpace a ⊔ fixedSpace a.representation ⊤ = ⊤)
    (B : Subgroup (J ⧸ pCore 2 J)) :
    (subspaceCommutator (movedRepresentation a) ⊤ B).map (movedSpace a).subtype =
      subspaceCommutator a.representation ⊤ B := by
  have hh := subspaceCommutator_map_embedding a.representation (movedRepresentation a)
    (MonoidHom.id _) (movedSpace a).subtype (fun _ _ => rfl) B ⊤
  rw [Submodule.map_top,Submodule.range_subtype,Subgroup.map_id] at hh
  rw [←hh]
  apply le_antisymm (subspaceCommutator_mono_left _ le_top _)
  apply Submodule.span_le.mpr
  rintro _ ⟨b,hb,v,_,rfl⟩
  obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ movedSpace a ⊔ fixedSpace a.representation ⊤ by rw [hspan]; trivial)
  have hf : a.representation b w = w := hw ⟨b,mem_top b⟩
  have heq : a.representation b (u+w)-(u+w)=a.representation b u-u := by
    rw [map_add,hf]; abel
  rw [heq]
  exact Submodule.subset_span ⟨b,hb,u,hu,rfl⟩

omit hG T hempty hM hu hmany hcard e hab in
private theorem residual_lift_support
    {J U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction J U Z)
    (B : Subgroup (J ⧸ pCore 2 J)) (hodd : Odd (Nat.card B))
    (hZ : let A := B.comap (QuotientGroup.mk' (pCore 2 J))
      Z ≤ ⁅U,((pResidual 2 A).map A.subtype).map J.subtype⁆) :
    let A := B.comap (QuotientGroup.mk' (pCore 2 J))
    ⁅U,((pResidual 2 A).map A.subtype).map J.subtype⁆ =
      OddNormalizer.supportPreimage a (subspaceCommutator a.representation ⊤ B) := by
  let q := QuotientGroup.mk' (pCore 2 J)
  let A := B.comap q
  let R₀ := (pResidual 2 A).map A.subtype
  let R := R₀.map J.subtype
  have hRJ : R ≤ J := map_subtype_le _
  have hRN : R ≤ normalizer (U : Set G) := hRJ.trans a.normalizes
  have hRU : ⁅U,R⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp hRN
  have hBres : pResidual 2 B = ⊤ := by
    apply top_unique
    intro x _
    exact mem_pResidual_of_orderOf_coprime
      (hodd.coprime_two_left.of_dvd_right (orderOf_dvd_natCard x))
  have hRimage : (R.subgroupOf J).map q = B := by
    rw [show R.subgroupOf J = R₀ from comap_map_eq_self_of_injective J.subtype_injective _]
    rw [map_embedded_pResidual,
      show A.map q = B from map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) B,
      hBres,←MonoidHom.range_eq_map,range_subtype]
  let r := q.comp (inclusion hRJ)
  have hr : r.range = B := by
    rw [MonoidHom.range_comp,inclusion_range]
    exact hRimage
  let π := QuotientGroup.mk' (Z.subgroupOf U)
  have he := commutator_image_eq a.representation U U R hRN le_rfl r π
    (fun x u => a.conjugation (inclusion hRJ x) u) ⊤ (by
      rw [subgroupOf_self,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
      rfl)
  rw [hr] at he
  change ⁅U,R⁆ = _
  unfold OddNormalizer.supportPreimage
  rw [←he,comap_map_eq,sup_eq_left.mpr]
  · exact (map_subgroupOf_eq_of_le hRU).symm
  · rw [QuotientGroup.ker_mk']
    exact fun _ hz => hZ hz


omit hG T hempty hM hu hmany hcard e hab [Group G] [Finite G] in
private theorem binary_sup {Q : Type*} [Group Q] [IsMulCommutative Q]
    [Module (ZMod 2) (Additive Q)]
    (A B : Submodule (ZMod 2) (Additive Q)) :
    binarySubgroup (A ⊔ B) = binarySubgroup A ⊔ binarySubgroup B :=
  ((AddSubgroup.toZModSubmodule 2).symm.trans Subgroup.toAddSubgroup.symm).map_sup A B

omit hG T hempty hM hu hmany hcard e hab in
private theorem support_card
    {J U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction J U Z)
    (W : Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U))) :
    Nat.card (OddNormalizer.supportPreimage a W) =
      Nat.card Z * 2 ^ Module.finrank (ZMod 2) W := by
  let π := QuotientGroup.mk' (Z.subgroupOf U)
  let C := (binarySubgroup W).comap π
  have hker : π.ker ≤ C := (binarySubgroup W).ker_le_comap π
  have hc := IsElementaryAbelian.card_inf_ker_mul_card_map C π
  rw [inf_eq_right.mpr hker,QuotientGroup.ker_mk',
    show C.map π = binarySubgroup W from
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _,
    Nat.card_congr (subgroupOfEquivOfLe a.kernel_le).toEquiv,
    binarySubgroup_card,Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W),Nat.card_zmod] at hc
  exact (card_map_of_injective U.subtype_injective).trans hc.symm

/-- The two cubic supports lift to actual elementary groups of order eight.
They meet in the original point and retain all residual preimages. -/
theorem source_singleton_nine_lifted_supports
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (s : ChapterD.FittingConfigurations.SupportFactors (movedRepresentation a)
      (pResidual 2 (J ⧸ pCore 2 J)) 2) :
    let U := conjugateSpanBy (localModule T M) J
    let Z := centralInvolutions T
    let A := fun k => (s.ambient k).comap (QuotientGroup.mk' (pCore 2 J))
    let R := fun k => ((pResidual 2 (A k)).map (A k).subtype).map J.subtype
    let W := fun k => ⁅U,R k⁆
    (∀ k, W k = OddNormalizer.supportPreimage a
      (subspaceCommutator a.representation ⊤ (s.ambient k))) ∧
    (∀ k, Nat.card (W k) = 8) ∧ W 0 ⊓ W 1 = Z ∧
    W 0 ⊔ W 1 = ⁅U,J⁆ ∧ Nat.card (⁅U,J⁆ : Subgroup G) = 32 := by
  let U := conjugateSpanBy (localModule T M) J
  let Z := centralInvolutions T
  let A := fun k => (s.ambient k).comap (QuotientGroup.mk' (pCore 2 J))
  let R := fun k => ((pResidual 2 (A k)).map (A k).subtype).map J.subtype
  let W := fun k => ⁅U,R k⁆
  let V := fun k => subspaceCommutator a.representation ⊤ (s.ambient k)
  let V₀ := fun k => subspaceCommutator (movedRepresentation a) ⊤ (s.ambient k)
  have hspan : movedSpace a ⊔ fixedSpace a.representation ⊤ = ⊤ := by
    rw [movedSpace,source_rankTwo_whole_moved_eq_residual
      hG T hempty hM hu hmany hcard e hab J hJ.1 a]
    exact source_rankTwo_span_decomposition hG T hempty hM hu hmany hcard e hab J hJ.1 a
  have hv (k : Fin 2) : (V₀ k).map (movedSpace a).subtype = V k :=
    moved_support_image a hspan _
  have hdim (k : Fin 2) : Module.finrank (ZMod 2) (V k) = 2 := by
    rw [←hv,Submodule.finrank_map_subtype_eq]
    exact s.support_dim k
  have hc (k : Fin 2) : Nat.card (s.ambient k) = 3 :=
    (card_map_of_injective (pResidual 2 (J ⧸ pCore 2 J)).subtype_injective).trans (s.card_factor k)
  have hZ (k : Fin 2) : Z ≤ W k := by
    apply source_point_le_lifted_odd_factor hG T hempty hM hu hmany hcard e hab
      J hJ hs (s.ambient k) (map_subtype_le _)
    intro hb
    have hh := hc k
    rw [hb,card_bot] at hh
    omega
  have hw (k : Fin 2) : W k = OddNormalizer.supportPreimage a (V k) :=
    residual_lift_support a (s.ambient k) ((hc k) ▸ (by decide : Odd 3)) (hZ k)
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  have hzcard : Nat.card Z = 2 :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1).point_card
  have hwcard (k : Fin 2) : Nat.card (W k) = 8 := by
    rw [hw,support_card a,hzcard,hdim]
    norm_num
  have hvdis : Disjoint (V 0) (V 1) := by
    rw [←hv,←hv]
    exact Submodule.disjoint_map (movedSpace a).subtype_injective
      (s.support_disjoint (movedRepresentation a) (by decide : (0 : Fin 2) ≠ 1))
  have hinf : W 0 ⊓ W 1 = Z := by
    apply le_antisymm ?_ (le_inf (hZ 0) (hZ 1))
    rw [hw,hw]
    exact OddNormalizer.supportPreimage_disjoint_modulo a _ _ hvdis
  have hjoin : W 0 ⊔ W 1 = ⁅U,J⁆ := by
    have hVsum : V 0 ⊔ V 1 = movedSpace a := by
      rw [←hv,←hv,←Submodule.map_sup]
      have hsum : V₀ 0 ⊔ V₀ 1 = ⊤ := by
        apply top_unique
        intro v _
        obtain ⟨w,hw⟩ := s.add_bijective.2 v
        apply Submodule.mem_sup.mpr
        exact ⟨w 0,(w 0).property,w 1,(w 1).property,
          by simpa only [Fin.sum_univ_two] using hw⟩
      rw [hsum,Submodule.map_top,Submodule.range_subtype]
    have hsupp : OddNormalizer.supportPreimage a (movedSpace a) = ⁅U,J⁆ := by
      unfold OddNormalizer.supportPreimage
      rw [←moved_image a,comap_map_eq,sup_eq_left.mpr]
      · exact map_subgroupOf_eq_of_le (moved_le a)
      · rw [QuotientGroup.ker_mk']
        exact fun _ hz => (hZ 0).trans (commutator_mono le_rfl (map_subtype_le _)) hz
    rw [hw,hw,←hsupp,←hVsum]
    unfold OddNormalizer.supportPreimage
    rw [←Subgroup.map_sup,comap_sup_eq _ _ _ (QuotientGroup.mk'_surjective _)]
    rw [binary_sup]
  have hW0 : W 0 ≤ U := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans a.normalizes)
  have hW1 : W 1 ≤ U := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans a.normalizes)
  have hnorm : W 1 ≤ normalizer (W 0 : Set G) :=
    (hW1.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hW0))).trans (Subgroup.centralizer_le_normalizer _)
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes (W 0) (W 1) hnorm
  rw [hwcard,hwcard,hinf,hzcard,hjoin] at hh
  refine ⟨hw,hwcard,hinf,hjoin,?_⟩
  change Nat.card (⁅U,J⁆ : Subgroup G) = 32
  omega

/-- Every opposite critical point is diagonal across the two actual lifted
cubic supports: it meets neither one. -/
theorem source_singleton_nine_critical_point_support_disjoint
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9)
    (s : ChapterD.FittingConfigurations.SupportFactors (movedRepresentation a)
      (pResidual 2 (J ⧸ pCore 2 J)) 2) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ (i : h.CriticalEndpoint) (k : Fin 2),
      let A := (s.ambient k).comap (QuotientGroup.mk' (pCore 2 J))
      i.conjugate D.V₁ ⊓ ⁅D.UH,((pResidual 2 A).map A.subtype).map J.subtype⁆ = ⊥ := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  have hspan : movedSpace a ⊔ fixedSpace a.representation ⊤ = ⊤ := by
    rw [movedSpace,source_rankTwo_whole_moved_eq_residual
      hG T hempty hM hu hmany hcard e hab J hJ.1 a]
    exact source_rankTwo_span_decomposition hG T hempty hM hu hmany hcard e hab J hJ.1 a
  let V : Subrepresentation a.representation := {
    toSubmodule := movedSpace a
    apply_mem_toSubmodule := fun g _ hv => (movedSpace_invariant a (mem_top g) _).mpr hv }
  have hf : Function.Injective (movedRepresentation a) :=
    ChapterD.SourceReduction.subrepresentation_faithful_of_fixed_complement
      a.representation a.faithful V hspan
  have hE : IsElementaryAbelian 3 (pResidual 2 (J ⧸ pCore 2 J)) := by
    obtain ⟨p,hp,hE,_,_,_⟩ := source_solvable_minimal_elementary_residual
      hG T hempty hM hu hmany hcard e hab J hJ hs
    rcases hp with rfl | rfl
    · exact hE
    · let := hE
      have hh := (IsElementaryAbelian.isPGroup 5 (pResidual 2 (J ⧸ pCore 2 J))).card_eq_or_dvd
      rw [hnine] at hh
      norm_num at hh
  let := hE
  change ∀ (i : h.CriticalEndpoint) (k : Fin 2), _
  intro i k
  let A := (s.ambient k).comap (QuotientGroup.mk' (pCore 2 J))
  let R := ((pResidual 2 A).map A.subtype).map J.subtype
  have hw : ⁅D.UH,R⁆ = OddNormalizer.supportPreimage a
      (subspaceCommutator a.representation ⊤ (s.ambient k)) :=
    (source_singleton_nine_lifted_supports
      hG T hempty hM hu hmany hcard e hab J hJ hs a s).1 k
  have hsep := (source_singleton_nine_paired_point_lines
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).2.2.2.1
  obtain ⟨j,hjk⟩ := exists_ne k
  have hkj : k ≠ j := Ne.symm hjk
  have hBcard : Nat.card (s.ambient j) = 3 :=
    (card_map_of_injective (pResidual 2 (J ⧸ pCore 2 J)).subtype_injective).trans (s.card_factor j)
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := s.ambient j) 3 (by rw [hBcard])
  have hbo : orderOf (b : J ⧸ pCore 2 J) = 3 := (Subgroup.orderOf_coe b).trans hb
  have hp := (source_singleton_nine_point_centralizers
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).2.2
  apply bot_unique
  rintro z ⟨hz,hzw⟩
  change z ∈ ⁅D.UH,R⁆ at hzw
  change z = 1
  by_contra hz1
  have hzU : z ∈ D.UH := (le_normalizer_iff_commutator_le_left.mp
    ((show R ≤ J from map_subtype_le _).trans a.normalizes)) hzw
  have hzmove : z ∈ ⁅D.UH,J⁆ := (commutator_mono le_rfl (map_subtype_le _)) hzw
  have hzZ : z ∉ D.V₁ := fun hh => hz1 (hsep.le ⟨hh,hz⟩)
  let u : D.UH := ⟨z,hzU⟩
  have hv : Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u) ∈
      subspaceCommutator a.representation ⊤ (s.ambient k) :=
    (OddNormalizer.mem_supportPreimage a _ u).mp (hw ▸ hzw)
  rw [←moved_support_image a hspan (s.ambient k)] at hv
  obtain ⟨v,hv,he⟩ := hv
  have ht : a.representation (b : J ⧸ pCore 2 J)
      (Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u)) =
      Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u) := by
    have hh := congrArg Subtype.val (s.cross_fixed (movedRepresentation a) hf hkj hv b)
    change a.representation (b : J ⧸ pCore 2 J) v.val = v.val at hh
    exact (congrArg (a.representation (b : J ⧸ pCore 2 J)) he).symm.trans (hh.trans he)
  obtain ⟨x,hx,hxz⟩ := source_solvable_moved_point_centralizer_lifts
    hG T hempty hM hu hmany hcard e hab J hJ hs a u hzmove hzZ b ht
  have hc : Nat.card (i.conjugate D.V₁) = 2 :=
    (card_map_of_injective (MulAut.conj i.representative).injective).trans h.point_card
  have hzpow : zpowers z = i.conjugate D.V₁ := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr hz)
    rw [hc]
    exact Nat.succ_le_of_lt ((zpowers z).one_lt_card_iff_ne_bot.mpr
      (fun hb => hz1 (Subgroup.zpowers_eq_bot.mp hb)))
  have hec : centralizer ({z} : Set G) = centralizer (i.conjugate D.V₁ : Set G) := by
    rw [←centralizer_closure,←zpowers_eq_closure,hzpow]
  rw [hec] at hxz
  let C := ((J ⊓ centralizer (i.conjugate D.V₁ : Set G)).subgroupOf J).map
    (QuotientGroup.mk' (pCore 2 J))
  have hbC : (b : J ⧸ pCore 2 J) ∈ C := ⟨x,⟨x.property,hxz⟩,hx⟩
  have hdvd := orderOf_dvd_natCard (⟨b,hbC⟩ : C)
  have horder : orderOf (⟨b,hbC⟩ : C) = 3 :=
    (Subgroup.orderOf_coe _).symm.trans hbo
  rcases hp with htwo | hfour
  · rw [horder,htwo] at hdvd
    norm_num at hdvd
  · rw [horder,hfour] at hdvd
    norm_num at hdvd

/-- Each lifted cubic support meets the literal critical denominator in a
subgroup centralizing the entire opposite span. -/
theorem source_singleton_nine_denominator_support_centralizes
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9)
    (s : ChapterD.FittingConfigurations.SupportFactors (movedRepresentation a)
      (pResidual 2 (J ⧸ pCore 2 J)) 2) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ (i : h.CriticalEndpoint) (k : Fin 2),
      let A := (s.ambient k).comap (QuotientGroup.mk' (pCore 2 J))
      let W := ⁅D.UH,((pResidual 2 A).map A.subtype).map J.subtype⁆
      ⁅(D.UH ⊓ i.conjugate D.QH) ⊓ W,i.conjugate D.UH⁆ = ⊥ := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  change ∀ (i : h.CriticalEndpoint) (k : Fin 2), _
  intro i k
  let A := (s.ambient k).comap (QuotientGroup.mk' (pCore 2 J))
  let W := ⁅D.UH,((pResidual 2 A).map A.subtype).map J.subtype⁆
  have hn : i.conjugate D.UH ≤ normalizer (W : Set G) :=
    (source_singleton_nine_critical_support_normalizers
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine
      (s.ambient k) (map_subtype_le _) i).2.2.2
  have hp := source_singleton_nine_core_commutator_point
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i
  have hdis : i.conjugate D.V₁ ⊓ W = ⊥ :=
    source_singleton_nine_critical_point_support_disjoint
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine s i k
  apply bot_unique
  rw [←hdis]
  exact le_inf ((commutator_mono inf_le_left le_rfl).trans hp.le)
    ((commutator_mono inf_le_right le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hn))

end CFSG.Quasithin.Chapter14.Section06
