module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedOddLinearTwo.Source
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Involution.SmallPrimePower
public import Theory.GroupTheory.PResidual.NormalSubgroup
import all CFSG.Quasithin.ChapterE.Section02.Witnesses.Involution.Basic

/-!
# Odd residuals of the paired odd-linear witness

The order-two component projection supplies an inverted odd rotation. Retaining
its literal cyclic subgroup in the witness makes that subgroup normal with
a two-group quotient, so the full pair has odd two-residual. The original
component coordinates produce this witness without projection assumptions.

Source: Aschbacher–Smith E.2.17, printed p.230, paired odd-linear case.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
private theorem odd_residual_cyclic_join (V : Subgroup H) [IsElementaryAbelian 2 V]
    (r : H) (ho : Odd (orderOf r))
    (hsign : ∀z∈V,z*r*z⁻¹=r ∨ z*r*z⁻¹=r⁻¹) :
    Odd (Nat.card (pResidual 2 (zpowers r ⊔ V : Subgroup H))) := by
  let I := zpowers r ⊔ V
  let R := (zpowers r).subgroupOf I
  have hR : zpowers r ≤ I := le_sup_left
  have hn := normalizes_cyclic_of_identity_or_inversion V r hsign
  let : R.Normal := (normal_subgroupOf_iff_le_normalizer hR).mpr (sup_le
    (zpowers r).le_normalizer hn)
  have hgen : R ⊔ V.subgroupOf I = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hR,
      map_subgroupOf_eq_of_le (show V≤I from le_sup_right),
      ← MonoidHom.range_eq_map,range_subtype]
  have hquot := isPGroup_quotient_of_sup_eq_top R (V.subgroupOf I)
    (IsElementaryAbelian.isPGroup 2 V).comap_subtype hgen
  have hle : pResidual 2 I ≤ R := sInf_le ⟨inferInstance,hquot⟩
  have hodd : Odd (Nat.card R) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hR).toEquiv,Nat.card_zpowers]
    exact ho
  exact hodd.of_dvd_nat (card_dvd_of_le hle)

omit [Finite H] in
private theorem pair_of_coreFree_odd (T : Sylow 2 H) (M V : Subgroup H)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (w : Solvable.CoreFreeWitness M V p)
    (ho : Odd (Nat.card (pResidual 2 w.subgroup))) :
    ∃ u : DihedralWitness T M V, Odd (Nat.card (pResidual 2 u.subgroup)) := by
  have hTS : (T : Subgroup H).subgroupOf w.subgroup = w.sylow := by
    apply w.sylow.is_maximal' T.isPGroup'.comap_subtype
    intro x hx
    have hv := mem_map_of_mem w.subgroup.subtype hx
    rw [w.sylow_eq] at hv
    exact hVT hv
  have htwo : IsPGroup 2 (M.subgroupOf w.subgroup).normalCore := by
    rw [w.maximal_eq]
    exact ((IsElementaryAbelian.isPGroup 2 V).comap_subtype).to_le (normalCore_le _)
  have hclosed : ∃S : Sylow 2 (M.subgroupOf w.subgroup).normalCore,
      (S : Subgroup (M.subgroupOf w.subgroup).normalCore).Normal := by
    refine ⟨(htwo.to_subgroup ⊤).toSylow (by simp),?_⟩
    exact inferInstanceAs (⊤ : Subgroup (M.subgroupOf w.subgroup).normalCore).Normal
  obtain ⟨e⟩ := w.dihedral
  let u : QuotientLift.Pair T M V :=
    ⟨w.subgroup,w.le,w.conjugator,w.generate,w.sylow,by
      rw [← hTS,subgroupOf_map_subtype],hclosed⟩
  exact ⟨⟨u,p,hp,hp2,w.exponent,w.positive,e⟩,ho⟩

theorem exists_dihedral_product_odd_residual
    {G A : Type*} [Group G] [Finite G] [Group A] (W : Subgroup (G × A)) [IsElementaryAbelian 2 W]
    (hc : Nat.card (W.map (MonoidHom.fst G A)) = 2)
    (hcoreG : pCore 2 G = ⊥) (T : Sylow 2 H) (M : Subgroup H)
    (f : G × A →* H) (hf : Function.Injective f)
    (hVT : W.map f ≤ T) (hVM : W.map f ≤ M.pCoreIn 2) :
    ∃u : DihedralWitness T M (W.map f), Odd (Nat.card (pResidual 2 u.subgroup)) := by
  let U := W.map (MonoidHom.fst G A)
  let V := W.map f
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  have hUn : U ≠ ⊥ := by
    intro he
    have hh := card_eq_one.mpr he
    change Nat.card U=2 at hc
    omega
  obtain ⟨v,hv,hv1⟩ := U.bot_or_exists_ne_one.resolve_left hUn
  obtain ⟨w,hw,hwv⟩ := hv
  have hvU : v∈U := ⟨w,hw,hwv⟩
  have hv2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) v hvU
  have hinv : BenderSuzuki.PFAppendixIII.IsInvolution v := ⟨hv1,hv2⟩
  have hvout : v ∉ pCore 2 G := by rw [hcoreG,mem_bot]; exact hv1
  obtain ⟨p,hp,hp2,r,hr,hi⟩ := BenderSuzuki.involution_outside_twoCore_inverts_odd_prime v hinv hvout
  let : Fact p.Prime := ⟨hp⟩
  let rr : H := f (r,1)
  let vv : H := f w
  have hiG : v*r*v⁻¹ = r⁻¹ := by
    simpa only [BenderSuzuki.PFAppendixIII.rightConjugateElem,hinv.inv_eq_self] using hi
  have hiv : vv*rr*vv⁻¹ = rr⁻¹ := by
    change f w * f (r,1) * (f w)⁻¹ = (f (r,1))⁻¹
    rw [← map_inv,← map_mul,← map_mul,← map_inv]
    apply congrArg f
    apply Prod.ext
    · change w.1*r*w.1⁻¹=r⁻¹
      change w.1=v at hwv
      rwa [hwv]
    · simp
  have hrr : orderOf rr=p := by
    rw [orderOf_injective f hf]
    have hh := orderOf_injective (MonoidHom.inl G A) (by intro x y h; exact congrArg Prod.fst h) r
    exact hh.trans hr
  have hvV : vv ∈ V := mem_map_of_mem f hw
  have hrrM : rr ∉ M := Involution.rotation_not_mem_of_inverter_in_core M vv rr hp2
    (hVM hvV) hrr hiv
  have hdM : Disjoint (zpowers rr) M := (M.disjoint_zpowers_of_prime_order_not_mem rr hrr hrrM).symm
  have hsign : ∀z∈V,z*rr*z⁻¹=rr ∨ z*rr*z⁻¹=rr⁻¹ := by
    rintro z ⟨a,ha,rfl⟩
    have haU : a.1∈U := mem_map_of_mem (MonoidHom.fst G A) ha
    have ha1 : a.1=1 ∨ a.1=v := by
      by_cases h:a.1=1
      · exact Or.inl h
      · right
        obtain ⟨b,hb,hu⟩ := (Nat.card_eq_two_iff' (1:U)).mp hc
        exact congrArg Subtype.val ((hu ⟨a.1,haU⟩ (fun he=>h (congrArg Subtype.val he))).trans
          (hu ⟨v,hvU⟩ (fun he=>hv1 (congrArg Subtype.val he))).symm)
    have heq : f a * rr * (f a)⁻¹ = f (a.1*r*a.1⁻¹,1) := by
      change f a*f (r,1)*(f a)⁻¹ = _
      rw [← map_inv,← map_mul,← map_mul]
      apply congrArg f
      apply Prod.ext
      · rfl
      · simp
    rw [heq]
    rcases ha1 with ha1 | hav
    · left
      simp only [ha1,one_mul,inv_one,mul_one]
      rfl
    · right
      rw [hav,hiG]
      change f (r⁻¹,1) = (f (r,1))⁻¹
      simpa using map_inv f (r,1)
  obtain ⟨w,_,hjoin⟩ := Involution.exists_witness_of_inverted_prime_power_line M V (hVM.trans (pCoreIn_le 2 M))
    rr vv 1 hvV (by decide) (by simpa only [pow_one] using hrr)
    (hrr ▸ hp.odd_of_ne_two hp2) (fun h=>hp.ne_one (hrr.symm.trans (h ▸ orderOf_one)))
    hiv hsign hdM
  have hodd : Odd (Nat.card (pResidual 2 w.subgroup)) := by
    rw [hjoin]
    exact odd_residual_cyclic_join V rr (hrr ▸ hp.odd_of_ne_two hp2) hsign
  exact pair_of_coreFree_odd T M V hVT hp hp2 w hodd


theorem exists_dihedral_of_projection_cards_odd_residual
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    (W : Subgroup (G × A)) [IsElementaryAbelian 2 W] (hW : W ≠ ⊥)
    (hfirst : Nat.card (W.map (MonoidHom.fst G A)) ≤ 2)
    (hsecond : Nat.card (W.map (MonoidHom.snd G A)) ≤ 2)
    (hG : pCore 2 G = ⊥) (hA : pCore 2 A = ⊥)
    (T : Sylow 2 H) (M : Subgroup H) (f : G × A →* H) (hf : Function.Injective f)
    (hVT : W.map f ≤ T) (hVM : W.map f ≤ M.pCoreIn 2) :
    ∃w : DihedralWitness T M (W.map f), Odd (Nat.card (pResidual 2 w.subgroup)) := by
  have hc (B : Subgroup (G × A)) [IsElementaryAbelian 2 B]
      (hB : B.map (MonoidHom.fst G A) ≠ ⊥)
      (hcard : Nat.card (B.map (MonoidHom.fst G A)) ≤ 2) :
      Nat.card (B.map (MonoidHom.fst G A)) = 2 := by
    let : IsElementaryAbelian 2 (B.map (MonoidHom.fst G A)) := IsElementaryAbelian.map _
    obtain h | h := two_or_four_of_elementary_ne_bot _ hB
    · exact h
    · omega
  rcases fst_ne_bot_or_snd_ne_bot W hW with h | h
  · obtain ⟨w,hodd⟩ :=
      exists_dihedral_product_odd_residual W (hc W h hfirst) hG T M f hf hVT hVM
    exact ⟨w,hodd⟩
  · let z : A × G ≃* G × A := MulEquiv.prodComm
    let W' := W.comap z.toMonoidHom
    let f' := f.comp z.toMonoidHom
    have hz : W'.map z.toMonoidHom = W := map_comap_eq_self_of_surjective z.surjective W
    let : IsElementaryAbelian 2 W' := IsElementaryAbelian.of_injective
      ((z.toMonoidHom.comp W'.subtype).codRestrict W (fun x => x.property))
      (by intro x y he; apply Subtype.ext; exact z.injective (congrArg Subtype.val he))
    have hproj : W'.map (MonoidHom.fst A G) = W.map (MonoidHom.snd G A) := by
      rw [← hz,map_map]
      rfl
    have hcard : Nat.card (W'.map (MonoidHom.fst A G)) = 2 := by
      rw [hproj]
      let : IsElementaryAbelian 2 (W.map (MonoidHom.snd G A)) := IsElementaryAbelian.map _
      obtain hh | hh := two_or_four_of_elementary_ne_bot _ h
      · exact hh
      · omega
    have hi : W'.map f' = W.map f := by rw [← map_map,hz]
    obtain ⟨w,hodd⟩ := exists_dihedral_product_odd_residual W' hcard hA
      T M f' (hf.comp z.injective) (by rwa [hi]) (by rwa [hi])
    have hw : ∃w : DihedralWitness T M (W'.map f'), Odd (Nat.card (pResidual 2 w.subgroup)) := ⟨w,hodd⟩
    rwa [hi] at hw


theorem source_pair_odd_residual
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : p = 7 ∨ 9 < p)
    (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬Group.IsSolvable H)
    (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    {K : Subgroup H} (hK : IsComponent H K) (hC : K.IsCComponent)
    [IsSimpleGroup K] (hgen : K ⊔ (T : Subgroup H) = ⊤) (hnot : ¬K.Normal)
    (e : K ≃* PSL(2,F)) (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hVT : V ≤ T) (hVN : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2) (hV : V ≠ ⊥) :
    ∃w : DihedralWitness T (ChapterB.minimalParabolicMax T hP) V, Odd (Nat.card (pResidual 2 w.subgroup)) := by
  have hrad : solvableRadical H = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
  obtain ⟨t,hne,hDsimple,hD,hR,⟨d,hd⟩,_,_⟩ :=
    Structure.source_pair_coordinates hH T hP hs hJ hK hC hgen hnot
  let D := K.map (MulAut.conj (t:H)).toMonoidHom
  let : IsSimpleGroup D := hDsimple
  let : IsQuasisimple D := hD.2
  have hDC : D.IsCComponent := isCComponent_of_isSimpleGroup_of_isPerfect hD.1
  let eD : D ≃* PSL(2,F) := ((MulAut.conj (t:H)).subgroupMap K).symm.trans e
  have hDT : D ⊔ (T : Subgroup H) = ⊤ := by
    have he := congrArg (Subgroup.map (MulAut.conj (t:H)).toMonoidHom) hgen
    rw [Subgroup.map_sup,map_top_of_surjective _ (MulAut.conj (t:H)).surjective] at he
    have ht : (T : Subgroup H).map (MulAut.conj (t:H)).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup H).le_normalizer t.property)
    rwa [ht] at he
  have hKdata := source_component_placement ho hF hp hH T hP hK hC hrad hgen e V hVT hVN
  have hDdata := source_component_placement ho hF hp hH T hP hD hDC hrad hDT eD V hVT hVN
  have hc : ⁅K,D⁆ = ⊥ := hK.commutator_eq_bot_of_ne hD hne.symm
  have hKD : K ≤ centralizer (D : Set H) := commutator_eq_bot_iff_le_centralizer.mp hc
  have hDK : D ≤ centralizer (K : Set H) := le_centralizer_iff.mp hKD
  have hnormal : (K ⊔ D).Normal := by rw [← hR]; infer_instance
  let := hnormal
  have hRT : (K ⊔ D : Subgroup H) ⊔ (T : Subgroup H) = ⊤ := top_unique (by
    rw [← hgen]
    exact sup_le_sup le_sup_left le_rfl)
  have hZ : center (K ⊔ D : Subgroup H) = ⊥ :=
    center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hrad hnormal.isSubnormal
  have hCR : centralizer ((K ⊔ D : Subgroup H) : Set H) = ⊥ := by
    have hcT := centralizer_le_sylow_of_centerless_supplement (K ⊔ D) T hRT hZ
    have hcO : centralizer ((K ⊔ D : Subgroup H) : Set H) ≤ pCore 2 H :=
      le_sSup ⟨inferInstance,T.isPGroup'.to_le hcT⟩
    exact le_bot_iff.mp (hcO.trans ((ChapterB.minimalParabolicTwoCore_le_core T hP).trans hJ.le))
  have hVR : V ≤ K ⊔ D := (le_inf hKdata.2.1 hDdata.2.1).trans
    (inf_inner_centralizer_supplements_le_sup K D hc hCR)
  let f : K × D →* H := (K ⊔ D : Subgroup H).subtype.comp d.toMonoidHom
  have hf : Function.Injective f := (K ⊔ D : Subgroup H).subtype_injective.comp d.injective
  have hmul : ∀ k a, f (k,a) = (k:H)*(a:H) := hd
  have hfr : f.range = K ⊔ D := by
    change ((K ⊔ D : Subgroup H).subtype.comp d.toMonoidHom).range = _
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr d.surjective,
      ← MonoidHom.range_eq_map,range_subtype]
  let W := V.comap f
  have him : W.map f = V := by rw [map_comap_eq,hfr]; exact inf_eq_right.mpr hVR
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    ((f.comp W.subtype).codRestrict V (fun x => x.property))
    (by
      intro x y he
      apply Subtype.ext
      exact hf (show f (x : K × D) = f (y : K × D) from congrArg (fun v : V => (v:H)) he))
  have hW : W ≠ ⊥ := by intro he; apply hV; rw [← him,he,Subgroup.map_bot]
  have hfirst : Nat.card (W.map (MonoidHom.fst K D)) ≤ 2 := by
    have hh := congrArg (fun A : Subgroup (NormalizerAction.Star K) => Nat.card A)
      (NormalizerAction.componentMap_projection_eq K D V hDK f hmul him)
    rw [card_map_of_injective (NormalizerAction.componentMap_injective_of_center_eq_bot K
      (center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hrad hK.1))] at hh
    exact hh.le.trans hKdata.2.2
  have hsecond : Nat.card (W.map (MonoidHom.snd K D)) ≤ 2 := by
    let z : D × K ≃* K × D := MulEquiv.prodComm
    let f' := f.comp z.toMonoidHom
    have hmul' : ∀ a k, f' (a,k) = (a:H)*(k:H) := by
      intro a k
      change f (k,a) = _
      rw [hmul]
      exact (hKD k.property a a.property).symm
    have him' : (V.comap f').map f' = V := by
      rw [show f' = f.comp z.toMonoidHom from rfl,← comap_comap,← map_map,
        map_comap_eq_self_of_surjective z.surjective,him]
    have hproj : (V.comap f').map (MonoidHom.fst D K) = W.map (MonoidHom.snd K D) := by
      have hz : (V.comap f').map z.toMonoidHom = W := by
        change (W.comap z.toMonoidHom).map z.toMonoidHom = W
        exact map_comap_eq_self_of_surjective z.surjective W
      rw [← hz,map_map]
      rfl
    have hh := congrArg (fun A : Subgroup (NormalizerAction.Star D) => Nat.card A)
      (NormalizerAction.componentMap_projection_eq D K V hKD f' hmul' him')
    rw [card_map_of_injective (NormalizerAction.componentMap_injective_of_center_eq_bot D
      (center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hrad hD.1)),hproj] at hh
    exact hh.le.trans hDdata.2.2
  have hKcore : pCore 2 K = ⊥ := SimpleSocle.pCore_eq_bot
    (solvableRadical_eq_bot_of_isSubnormal hrad hK.1) 2
  have hDcore : pCore 2 D = ⊥ := SimpleSocle.pCore_eq_bot
    (solvableRadical_eq_bot_of_isSubnormal hrad hD.1) 2
  have hw := exists_dihedral_of_projection_cards_odd_residual W hW hfirst hsecond hKcore hDcore T
    (ChapterB.minimalParabolicMax T hP) f hf (by rwa [him]) (by rwa [him])
  rwa [him] at hw


end CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
