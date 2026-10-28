module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalPairedJankoCubics
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.AbelianOddNormalizer

/-!
# Exclusion of the original paired J₁ Cartan row

In the literal quotient Y/O₂(Y), the two containing J₁ factors have an
index-two normalizer. This aligns the independently constructed Hall-plane
exchanger and Cartan-normalizing exchanger. The same cyclic Cartan image D
therefore has equal kernels on the same two factors R and U.

Each factor is centerless and centralizes the other, so D meets both trivially.
Since the original Hall plane E normalizes D and splits into its intersections
with R and U, D centralizes E. The mixed action on either J₁ factor is abelian.
Its order divides 21, and faithfulness on the Sylow eight bounds its order by
eight. The existing factor cubic forces this image to have order three, hence
to equal the action of that original Hall cubic.

For each element of D, choose elements of the two Hall cubics inducing its
two factor actions. The remaining difference centralizes both containing
factors and hence the original residual image. The Hall plane lies in that
residual, so D normalizes it. Perfect-residual lifting through the actual
two-core quotient contradicts the original Cartan escape.

The source seed reduction consequently has a normal containing C-component,
with all preceding exclusions preserved. This closes the paired J₁ row;
the remaining normal rows, module alternatives and relocation are still needed
for SourceLocalCartanEscape.

Source: Aschbacher--Smith 5.1.12--13, printed pp.635--637, especially the
paired J₁ paragraph on p.636 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]
private def jankoInnerEquiv : Janko1.Model ≃* MulAut Janko1.Model := by
  have hc : center Janko1.Model = ⊥ :=
    (inferInstance : (center Janko1.Model).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative Janko1.Model (center_eq_top_iff.mp he))
  exact MulEquiv.ofBijective _ ⟨conj_injective_of_center_eq_bot hc,Janko1.OuterCertificate.aut_inner⟩

omit [Finite G] in
private theorem odd_le_index_two (E N : Subgroup G)
    (ho : Odd (Nat.card E)) (hi : N.index = 2) : E ≤ N := by
  let : N.Normal := N.normal_of_index_eq_two hi
  rw [←relIndex_eq_one]
  apply Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr ho)
  · simpa only [hi] using N.relIndex_dvd_index_of_normal E
  · exact N.relIndex_dvd_card E

private theorem janko_abelian_factor_bound (S : Sylow 2 G) (C J E : Subgroup G)
    (e : C ≃* Janko1.Model) (hi : (normalizer (C : Set G)).index = 2)
    [Group.IsSolvable J] (hSJ : (S : Subgroup G) ≤ J) (hEJ : E ≤ J)
    [IsMulCommutative E] (ho : Odd (Nat.card E)) :
    E ≤ normalizer (C : Set G) ∧
      Nat.card ((E.subgroupOf (normalizer (C : Set G))).map C.normalizerMonoidHom) ≤ 8 ∧
      Nat.card ((E.subgroupOf (normalizer (C : Set G))).map C.normalizerMonoidHom) ∣ 21 := by
  let N := normalizer (C : Set G)
  let a : MulAut C ≃* Janko1.Model := (MulAut.congr e).trans jankoInnerEquiv.symm
  let f := C.normalizerMonoidHom
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨c,hc⟩ := Janko1.OuterCertificate.aut_inner (MulAut.congr e z)
    refine ⟨⟨e.symm c,C.le_normalizer (e.symm c).property⟩,?_⟩
    apply (MulAut.congr e).injective
    have he : f ⟨e.symm c,C.le_normalizer (e.symm c).property⟩ = MulAut.conj (e.symm c) := by
      ext x
      rfl
    rw [he,MulAut.congr_conj,e.apply_symm_apply]
    exact hc
  let : N.Normal := N.normal_of_index_eq_two hi
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal N
  let Q := P.mapSurjective hf
  let U := Q.mapSurjective (f := a.toMonoidHom) a.surjective
  let JN := J.subgroupOf N
  let EN := E.subgroupOf N
  let g := a.toMonoidHom.comp f
  let : Group.IsSolvable JN := Group.isSolvable_of_isSolvable_injective
    (f := N.subtype.subgroupComap J) (by
      intro x y hh
      exact Subtype.ext (Subtype.ext (congrArg (fun z : J => (z : G)) hh)))
  let : Group.IsSolvable (JN.map g) := Group.isSolvable_of_surjective (g.subgroupMap_surjective JN)
  have hUN : (U : Subgroup Janko1.Model) ≤ JN.map g := by
    change ((P : Subgroup N).map f).map a.toMonoidHom ≤ _
    rw [map_map,hP]
    exact map_mono (comap_mono hSJ)
  have hEN := odd_le_index_two E N ho hi
  have hodd : Odd (Nat.card (EN.map g)) :=
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv]; exact ho : Odd (Nat.card EN)).of_dvd_nat
      (card_map_dvd _ _)
  obtain ⟨hn,hcard⟩ := Janko1.LocalStructure.odd_solvable_overgroup_card_dvd_twenty_one
    U (JN.map g) (EN.map g) hUN (map_mono (comap_mono hEJ)) hodd
  have hsmall := Janko1.LocalStructure.abelian_odd_normalizer_card_le_eight U (EN.map g)
    hodd ((map_mono (comap_mono hEJ)).trans hn)
  rw [←map_map,card_map_of_injective a.injective] at hcard hsmall
  exact ⟨hEN,hsmall,hcard⟩


omit [Finite G] in
private theorem equal_kernels_disjoint (D R U : Subgroup G)
    (hZ : center R = ⊥) (hRU : R ≤ centralizer (U : Set G))
    (hk : D ⊓ centralizer (R : Set G) = D ⊓ centralizer (U : Set G)) :
    Disjoint D R := by
  apply disjoint_def.mpr
  intro x hxD hxR
  have hxC : x ∈ centralizer (R : Set G) := (hk ▸ (show x ∈ D ⊓ centralizer (U : Set G) from
    ⟨hxD,hRU hxR⟩)).2
  have hz : (⟨x,hxR⟩ : R) ∈ center R := mem_center_iff.mpr fun y =>
    Subtype.ext (hxC y y.property)
  rw [hZ] at hz
  exact congrArg Subtype.val (mem_bot.mp hz)

omit [Finite G] in
private theorem equal_kernels_centralize_plane (D E R U : Subgroup G)
    (hR : center R = ⊥) (hU : center U = ⊥)
    (hRU : R ≤ centralizer (U : Set G))
    (hDR : D ≤ normalizer (R : Set G)) (hDU : D ≤ normalizer (U : Set G))
    (hED : E ≤ normalizer (D : Set G))
    (hsplit : E = (E ⊓ R) ⊔ (E ⊓ U))
    (hk : D ⊓ centralizer (R : Set G) = D ⊓ centralizer (U : Set G)) :
    D ≤ centralizer (E : Set G) := by
  have hdisR := equal_kernels_disjoint D R U hR hRU hk
  have hdisU := equal_kernels_disjoint D U R hU (le_centralizer_iff.mp hRU) hk.symm
  have hc (V : Subgroup G) (hDV : D ≤ normalizer (V : Set G)) (hd : Disjoint D V) :
      E ⊓ V ≤ centralizer (D : Set G) := by
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply eq_bot_iff.mpr
    apply (le_inf ?_ ?_).trans hd.eq_bot.le
    · exact le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans hED)
    · exact (commutator_mono le_rfl inf_le_right).trans
        (le_normalizer_iff_commutator_le_right.mp hDV)
  apply le_centralizer_iff.mpr
  rw [hsplit]
  exact sup_le (hc R hDR hdisR) (hc U hDU hdisU)

omit [Finite G] in
private theorem commuting_sup_abelian (D E : Subgroup G) [IsMulCommutative D]
    [IsMulCommutative E] (hc : D ≤ centralizer (E : Set G)) : IsMulCommutative (D ⊔ E : Subgroup G) := by
  apply le_centralizer_iff_isMulCommutative.mp
  apply sup_le
  · apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff_isMulCommutative.mpr inferInstance) (le_centralizer_iff.mp hc)
  · apply le_centralizer_iff.mpr
    exact sup_le hc (le_centralizer_iff_isMulCommutative.mpr inferInstance)

omit [Finite G] in
private theorem janko_center_bot (R : Subgroup G) (a : R ≃* Janko1.Model) : center R = ⊥ := by
  let : IsSimpleGroup R := a.isSimpleGroup
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  exact (inferInstance : (center R).Normal).eq_bot_or_eq_top.resolve_right
    (fun he => Group.IsPerfect.not_isMulCommutative R (center_eq_top_iff.mp he))

omit [Finite G] in
private theorem centerfree_action_card (R E : Subgroup G)
    (hZ : center R = ⊥) (hER : E ≤ R) :
    Nat.card ((E.subgroupOf (normalizer (R : Set G))).map R.normalizerMonoidHom) = Nat.card E := by
  let N := normalizer (R : Set G)
  let E' := E.subgroupOf N
  let f := R.normalizerMonoidHom.comp E'.subtype
  have hi : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro x hx
    have hc : (x.val : G) ∈ centralizer (R : Set G) := by
      have hh : x.val ∈ R.normalizerMonoidHom.ker := hx
      rwa [normalizerMonoidHom_ker] at hh
    have hz : (⟨(x.val : G),hER x.property⟩ : R) ∈ center R :=
      mem_center_iff.mpr fun y => Subtype.ext (hc y y.property)
    rw [hZ] at hz
    exact Subtype.ext (Subtype.ext (congrArg (fun z : R => (z : G)) (mem_bot.mp hz)))
  have he := Nat.card_congr (MonoidHom.ofInjective hi).toEquiv
  change Nat.card E' = Nat.card f.range at he
  rw [MonoidHom.range_comp,range_subtype] at he
  rw [←he,Nat.card_congr (subgroupOfEquivOfLe (hER.trans R.le_normalizer)).toEquiv]

private theorem janko_abelian_action_eq_cubic (S : Sylow 2 G) (R J F E : Subgroup G)
    (a : R ≃* Janko1.Model) (hi : (normalizer (R : Set G)).index = 2)
    [Group.IsSolvable J] [IsMulCommutative F]
    (hSJ : (S : Subgroup G) ≤ J) (hFJ : F ≤ J) (ho : Odd (Nat.card F))
    (hEF : E ≤ F) (hER : E ≤ R) (hE : Nat.card E = 3) :
    (F.subgroupOf (normalizer (R : Set G))).map R.normalizerMonoidHom =
      (E.subgroupOf (normalizer (R : Set G))).map R.normalizerMonoidHom := by
  obtain ⟨_,hsmall,hcard⟩ := janko_abelian_factor_bound S R J F a hi hSJ hFJ ho
  have h3 : Nat.card ((E.subgroupOf (normalizer (R : Set G))).map R.normalizerMonoidHom) = 3 :=
    (centerfree_action_card R E (janko_center_bot R a) hER).trans hE
  have hle := map_mono (f := R.normalizerMonoidHom) (comap_mono (f := (normalizer (R : Set G)).subtype) hEF)
  have hd : 3 ∣ Nat.card ((F.subgroupOf (normalizer (R : Set G))).map R.normalizerMonoidHom) :=
    h3 ▸ card_dvd_of_le hle
  have he : Nat.card ((F.subgroupOf (normalizer (R : Set G))).map R.normalizerMonoidHom) = 3 := by
    have arith : ∀ m : ℕ, m ≤ 8 → m ∣ 21 → 3 ∣ m → m = 3 := by
      intro m hm h21 hd3
      interval_cases m <;> norm_num at *
    exact arith _ hsmall hcard hd
  exact (eq_of_le_of_card_ge hle (le_of_eq (he.trans h3.symm))).symm

private theorem paired_janko_normalizes (S : Sylow 2 G) (R U J D E K : Subgroup G)
    (a : R ≃* Janko1.Model) (b : U ≃* Janko1.Model)
    (hiR : (normalizer (R : Set G)).index = 2)
    (hiU : (normalizer (U : Set G)).index = 2)
    [Group.IsSolvable J] [IsCyclic D] [IsMulCommutative E]
    (hSJ : (S : Subgroup G) ≤ J) (hFJ : D ⊔ E ≤ J)
    (ho : Odd (Nat.card (D ⊔ E : Subgroup G)))
    (hED : E ≤ normalizer (D : Set G)) (hRU : R ≤ centralizer (U : Set G))
    (h1 : Nat.card (E ⊓ R : Subgroup G) = 3) (h2 : Nat.card (E ⊓ U : Subgroup G) = 3)
    (hsplit : E = (E ⊓ R) ⊔ (E ⊓ U))
    (hk : D ⊓ centralizer (R : Set G) = D ⊓ centralizer (U : Set G))
    (hEK : E ≤ K) (hKP : K ≤ R ⊔ U) : D ≤ normalizer (K : Set G) := by
  let F := D ⊔ E
  let NR := normalizer (R : Set G)
  let NU := normalizer (U : Set G)
  have hFR : F ≤ NR := odd_le_index_two F NR ho hiR
  have hFU : F ≤ NU := odd_le_index_two F NU ho hiU
  have hc := equal_kernels_centralize_plane D E R U (janko_center_bot R a)
    (janko_center_bot U b) hRU (le_sup_left.trans hFR) (le_sup_left.trans hFU) hED hsplit hk
  let : IsMulCommutative F := commuting_sup_abelian D E hc
  have hR := janko_abelian_action_eq_cubic S R J F (E ⊓ R) a hiR hSJ hFJ ho
    (inf_le_left.trans le_sup_right) inf_le_right h1
  have hU := janko_abelian_action_eq_cubic S U J F (E ⊓ U) b hiU hSJ hFJ ho
    (inf_le_left.trans le_sup_right) inf_le_right h2
  intro d hd
  let dR : NR := ⟨d,hFR ((show D ≤ F from le_sup_left) hd)⟩
  let dU : NU := ⟨d,hFU ((show D ≤ F from le_sup_left) hd)⟩
  have hdR : R.normalizerMonoidHom dR ∈ (F.subgroupOf NR).map R.normalizerMonoidHom :=
    mem_map_of_mem _ (show dR ∈ F.subgroupOf NR from (show D ≤ F from le_sup_left) hd)
  have hdU : U.normalizerMonoidHom dU ∈ (F.subgroupOf NU).map U.normalizerMonoidHom :=
    mem_map_of_mem _ (show dU ∈ F.subgroupOf NU from (show D ≤ F from le_sup_left) hd)
  rw [hR] at hdR
  rw [hU] at hdU
  obtain ⟨r,hr,her⟩ := hdR
  obtain ⟨u,hu,heu⟩ := hdU
  have hrd : (r : G)⁻¹ * d ∈ centralizer (R : Set G) := by
    have hh : r⁻¹ * dR ∈ R.normalizerMonoidHom.ker := by
      change R.normalizerMonoidHom (r⁻¹ * dR) = 1
      rw [map_mul,map_inv,her,inv_mul_cancel]
    rwa [normalizerMonoidHom_ker] at hh
  have hdu : d * (u : G)⁻¹ ∈ centralizer (U : Set G) := by
    have hh : dU * u⁻¹ ∈ U.normalizerMonoidHom.ker := by
      change U.normalizerMonoidHom (dU * u⁻¹) = 1
      rw [map_mul,map_inv,heu,mul_inv_cancel]
    rwa [normalizerMonoidHom_ker] at hh
  let z := (r : G)⁻¹ * d * (u : G)⁻¹
  have hzR : z ∈ centralizer (R : Set G) :=
    (centralizer (R : Set G)).mul_mem hrd
      ((centralizer (R : Set G)).inv_mem (le_centralizer_iff.mp hRU hu.2))
  have hzU : z ∈ centralizer (U : Set G) := by
    dsimp [z]
    rw [mul_assoc]
    exact (centralizer (U : Set G)).mul_mem
      ((centralizer (U : Set G)).inv_mem (hRU hr.2)) hdu
  have hzP : z ∈ centralizer ((R ⊔ U : Subgroup G) : Set G) := by
    have hle : R ⊔ U ≤ centralizer ({z} : Set G) := sup_le
      (fun x hx => mem_centralizer_singleton_iff.mpr (hzR x hx))
      (fun x hx => mem_centralizer_singleton_iff.mpr (hzU x hx))
    intro x hx
    exact (mem_centralizer_singleton_iff.mp (hle hx))
  have hzK : z ∈ normalizer (K : Set G) :=
    Subgroup.centralizer_le_normalizer _ (centralizer_le hKP hzP)
  have hrK : (r : G) ∈ normalizer (K : Set G) := K.le_normalizer (hEK hr.1)
  have huK : (u : G) ∈ normalizer (K : Set G) := K.le_normalizer (hEK hu.1)
  have hh := (normalizer (K : Set G)).mul_mem ((normalizer (K : Set G)).mul_mem hrK hzK) huK
  simpa only [z,mul_assoc,mul_inv_cancel_left,inv_mul_cancel_left,mul_inv_cancel,inv_mul_cancel,mul_one,one_mul] using hh

omit [Finite G] in
private theorem conjugate_normalizer_index (R : Subgroup G) (t : G) :
    (normalizer (R.conjBy t : Set G)).index = (normalizer (R : Set G)).index := by
  change (normalizer (R.map (MulAut.conj t).toMonoidHom : Set G)).index = _
  rw [←map_equiv_normalizer_eq]
  exact (normalizer (R : Set G)).index_map_equiv (MulAut.conj t)

/-- The original escape cannot have a nonnormal genuine J₁ containing component.
Both Hall subgroups and the original residual and quotient maps are retained. -/
theorem not_nonnormal_janko_container
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hKT : K ⊔ (T : Subgroup G) = H) (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hCn : ¬ C.Normal)
    (hKC : K ≤ C.map Y.subtype) (a : (C ⧸ pCore 2 C) ≃* Janko1.Model) :
    False := by
  have hmoved := nonnormal_container_seed_moved h.qtke hKH hH.1.1.2 hKL hY C hC hKC hCn
  have hlin := moved_seed_linear_four_of_escape h.qtke hKL hKT horbit hmoved hY hescape
  obtain ⟨hB,hBc⟩ := moved_seed_right_hall_plane h hH hgen c hKH hK hqs hKT horbit hmoved hlin
  have hTY := hH.1.1.2.trans hY.2
  have hBY := (c.right_le.trans inf_le_right).trans hY.2
  have hiC := (nonnormal_container_models h.qtke hKH hH.1.1.2 hKL horbit
    hY hescape C hC hKC hCn).1
  obtain ⟨t,ht,_,⟨aR⟩,⟨aU⟩,_,hcomm,hout,_,e,he⟩ :=
    nonnormal_janko_quotient_pair hTY C hC hiC a
  let q := QuotientGroup.mk' (pCore 2 Y)
  let R := C.map q
  let U := R.conjBy (q t)
  let D := (A.subgroupOf Y).map q
  let E := (B.subgroupOf Y).map q
  let P := (T.subtype hTY).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  let O := componentOrbit C ((T : Subgroup G).subgroupOf Y)
  let Kbar := ((residual H).subgroupOf Y).map q
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  have hiR : (normalizer (R : Set (Y ⧸ pCore 2 Y))).index = 2 := by
    rw [cComponent_normalizer_index_quotient hC]
    exact hiC
  have hiU : (normalizer (U : Set (Y ⧸ pCore 2 Y))).index = 2 :=
    (conjugate_normalizer_index R (q t)).trans hiR
  have hmove : R.conjBy (q t) ≠ R := fun hh => hout (mem_normalizer_iff_map_conj_eq.mpr hh)
  obtain ⟨s,_,_,_,_,hE,h1,h2,hsplit,_,_,_,_⟩ :=
    nonnormal_janko_hall_plane h hH hgen c hKH hK hqs hKT hKL horbit hY hescape C hC hCn hKC a
  change Nat.card E = 9 at hE
  change Nat.card (E ⊓ R : Subgroup _) = 3 at h1
  change Nat.card (E ⊓ R.conjBy (q s) : Subgroup _) = 3 at h2
  change E = (E ⊓ R) ⊔ (E ⊓ R.conjBy (q s)) at hsplit
  have hsmove : R.conjBy (q s) ≠ R := by
    intro hh
    have hEs : E = E ⊓ R := by simpa only [hh,sup_idem] using hsplit
    have hc := congrArg (fun V : Subgroup (Y ⧸ pCore 2 Y) => Nat.card V) hEs
    rw [hE,h1] at hc
    norm_num at hc
  have hsu : R.conjBy (q s) = U :=
    (NormPair.conjugate_eq_or_eq_of_normalizer_index_two hiR hmove (q s)).resolve_left hsmove
  rw [hsu] at h2 hsplit
  obtain ⟨v,_,hvout,_,hker⟩ :=
    nonnormal_janko_cartan_exchanger h hH hgen c hKH hK hqs hKT hKL horbit hY hescape C hC hCn hKC a
  have hvU : R.conjBy (q v) = U :=
    (NormPair.conjugate_eq_or_eq_of_normalizer_index_two hiR hmove (q v)).resolve_left
      (fun hh => hvout (mem_normalizer_iff_map_conj_eq.mpr hh))
  change D ⊓ centralizer (R : Set _) = D ⊓ centralizer (R.conjBy (q v) : Set _) at hker
  rw [hvU] at hker
  let : IsCyclic A := (c.left_cyclic_and_card h.sylow_normalizes h.linear).1
  let i : A.subgroupOf Y →* A := {
    toFun x := ⟨x.val,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hii : Function.Injective i := by
    intro x y hh
    exact Subtype.ext (Subtype.ext (congrArg (fun z : A => (z : G)) hh))
  let : IsCyclic (A.subgroupOf Y) := isCyclic_of_injective i hii
  let : IsCyclic D := isCyclic_of_surjective (q.subgroupMap _) (q.subgroupMap_surjective _)
  let := hB
  let : IsMulCommutative (B.subgroupOf Y) := inferInstance
  let : IsMulCommutative E := inferInstance
  have hoddD : Odd (Nat.card D) := by
    have hoA : Odd (Nat.card A) := by
      rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
      exact OddHall.odd_hall_odd c.left_hall
    have hoAY : Odd (Nat.card (A.subgroupOf Y)) := by
      rw [←inf_subgroupOf_right A Y,Nat.card_congr
        (subgroupOfEquivOfLe (show A ⊓ Y ≤ Y from inf_le_right)).toEquiv]
      exact hoA.of_dvd_nat (card_dvd_of_le (show A ⊓ Y ≤ A from inf_le_left))
    exact hoAY.of_dvd_nat (card_map_dvd _ q)
  have hED : E ≤ normalizer (D : Set (Y ⧸ pCore 2 Y)) := by
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    intro b hb
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (c.right_normalizes_left hb) (a : G)
  have hodd : Odd (Nat.card (D ⊔ E : Subgroup (Y ⧸ pCore 2 Y))) := by
    have hh := hoddD.mul (show Odd (Nat.card E) by rw [hE]; decide)
    rw [card_mul_eq_card_inf_mul_card_sup_of_normalizes D E hED] at hh
    exact hh.of_dvd_nat (dvd_mul_left _ _)
  let JY := (A.subgroupOf Y ⊔ (T : Subgroup G).subgroupOf Y) ⊔ B.subgroupOf Y
  let J := JY.map q
  have hLH : ¬ L ≤ H := by
    intro hh
    exact hescape (inf_le_left.trans ((c.left_le.trans (inf_le_left.trans hh)).trans
      (le_normalizer_residual H)))
  have prep := cartanPreparation_of_not_le h hH hgen hLH
  let M := normalizer (L : Set G) ⊓ H
  let V := localBorel T L ⊔ M
  let : Group.IsSolvable (localBorel T L) := prep.borel_solvable
  let : Group.IsSolvable M := prep.intersection_solvable
  let : Group.IsSolvable V := Group.isSolvable_sup_of_normalizes _ _ prep.intersection_normalizes
  have hJV : JY.map Y.subtype ≤ V := by
    rw [Subgroup.map_sup,Subgroup.map_sup,subgroupOf_map_subtype,map_subgroupOf_eq_of_le hTY,
      map_subgroupOf_eq_of_le hBY]
    exact sup_le (sup_le ((inf_le_left.trans c.left_le).trans le_sup_left)
      ((le_inf h.sylow_normalizes hH.1.1.2).trans le_sup_right))
      (c.right_le.trans le_sup_right)
  let : Group.IsSolvable JY := Group.isSolvable_of_isSolvable_injective
    (f := (inclusion hJV).comp
      (JY.equivMapOfInjective Y.subtype Y.subtype_injective).toMonoidHom)
    ((inclusion_injective hJV).comp (JY.equivMapOfInjective Y.subtype Y.subtype_injective).injective)
  let : Group.IsSolvable J := Group.isSolvable_of_surjective (q.subgroupMap_surjective JY)
  have hO : O.map q = R ⊔ U := by
    apply le_antisymm
    · intro x hx
      obtain ⟨⟨r,u⟩,hxru⟩ := e.surjective ⟨x,hx⟩
      have heq : x = (r : Y ⧸ pCore 2 Y) * u :=
        (congrArg Subtype.val hxru).symm.trans (he r u)
      rw [heq]
      exact mul_mem_sup r.property u.property
    · apply sup_le
      · intro r hr
        have hval := he ⟨r,hr⟩ 1
        simpa only [OneMemClass.coe_one,mul_one,hval] using (e (⟨r,hr⟩,1)).property
      · intro u hu
        have hval := he 1 ⟨u,hu⟩
        simpa only [OneMemClass.coe_one,one_mul,hval] using (e (1,⟨u,hu⟩)).property
  have hRO : residual H ≤ O.map Y.subtype := by
    dsimp only [O]
    rw [map_componentOrbit,map_subgroupOf_eq_of_le hTY,←horbit]
    exact iSup_mono fun _ => map_mono hKC
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hROY : (residual H).subgroupOf Y ≤ O := by
    apply (map_le_map_iff_of_injective Y.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hRY]
    exact hRO
  have hKP : Kbar ≤ R ⊔ U := (map_mono (f := q) hROY).trans_eq hO
  have hEK : E ≤ Kbar := map_mono (comap_mono (Global.right_cartan_le_residual c))
  have hn := paired_janko_normalizes P R U J D E Kbar aR aU hiR hiU
    (map_mono (show (T : Subgroup G).subgroupOf Y ≤ JY from le_sup_right.trans le_sup_left))
    (sup_le (map_mono (le_sup_left.trans le_sup_left)) (map_mono le_sup_right))
    hodd hED (commutator_eq_bot_iff_le_centralizer.mp hcomm) h1 h2 hsplit hker hEK hKP
  exact hescape ((residual_escape_twoCore_iff h.qtke h.sylow_normalizes hH hgen hY.2).mp hn)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
open Chapter1.Section02.LocalModels
/-- The original escape has a normal containing C-component: the paired J₁ row is excluded.
All preceding sieve alternatives and the literal original quotients are retained. -/
theorem localCartan_escape_seed_normalContainer_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        C.Normal := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hcase⟩ :=
    localCartan_escape_seed_pairedPrime_reduction h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,?_⟩
  by_contra hCn
  obtain ⟨_,_,_,_,_,⟨e⟩⟩ := hcase.resolve_left hCn
  exact LocalSieve.not_nonnormal_janko_container h hH hgen c hKH hK hqs hKT hKL hR
    hY hescape C hC hCn hKC e

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
