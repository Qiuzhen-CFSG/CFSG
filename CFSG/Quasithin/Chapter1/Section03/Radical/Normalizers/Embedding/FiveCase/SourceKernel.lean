module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.FiveCase.Source
public import Theory.GroupTheory.SolvableLayersEmbeddingConstructions
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.SpecificGroups.SL3.InvolutionConjugacy

/-!
# The actual prime and marked kernel in case (10)

The solvable, two-perfect group Ξ has trivial normal image in SL₂(s).
Its image in the case-(10) extension therefore lies in the elementary
kernel. The quotient by its two-core retains its prescribed order, forcing
p = s and equality with that kernel. Every chosen Sylow p-subgroup maps
onto this same image.

Removing the solvable layers of L makes PSL₂(s) a section of SL₂(5).
The order bound forces s = 5. Finally the actual containing component
embeds in SL₃(5). Its involution centralizers have order |GL₂(5)| = 480,
which cannot contain the order-25 kernel. Since a normal two-subgroup
centralizes this kernel, the actual Y-image has trivial two-core.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 1.3.8, printed pp.512–513; A.3.12(10), printed p.47.
The involution-centralizer model is A.3.21(a), printed p.55.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
open Section02 LocalModels

private theorem sl_quasisimple {s : ℕ} (hs : s.Prime) (hs3 : 3 < s) :
    IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (ZMod s)) := by
  let : Fact s.Prime := ⟨hs⟩
  have h2 : (2 : ZMod s) ≠ 0 := by
    intro h
    have hd : s ∣ 2 := (ZMod.natCast_eq_zero_iff 2 s).mp h
    have := Nat.le_of_dvd (by decide) hd
    omega
  have hsq : (2 : ZMod s) ^ 2 ≠ 1 := by
    intro h
    have hz : (3 : ZMod s) = 0 := by linear_combination h
    have hd : s ∣ 3 := (ZMod.natCast_eq_zero_iff 3 s).mp hz
    have := Nat.le_of_dvd (by decide) hd
    omega
  exact { toIsPerfect := ⟨Matrix.SL2.commutator_eq_top h2 hsq⟩
          simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
            (by simpa using (show 4 ≤ s by omega)) }

private theorem solvable_twoPerfect_sl_bot {s : ℕ} (hs : s.Prime) (hs3 : 3 < s)
    (D : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod s))) [D.Normal]
    [Group.IsSolvable D] (hp : IsPPerfect 2 D) : D = ⊥ := by
  let : Fact s.Prime := ⟨hs⟩
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (ZMod s)) :=
    sl_quasisimple hs hs3
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s)) := IsQuasisimple.simple
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod s)) := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center _))
  have hc : D ≤ center (Matrix.SpecialLinearGroup (Fin 2) (ZMod s)) := by
    rcases IsQuasisimple.normal_le_center_or_eq_top D with hc | ht
    · exact hc
    · have hsol : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod s)) := by
        let : Group.IsSolvable (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod s))) := ht ▸ inferInstance
        exact Group.isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod s))) ≃* _).toMonoidHom) topEquiv.surjective
      exact (Group.IsPerfect.not_isSolvable _ hsol).elim
  have hd2 : IsPGroup 2 D := by
    intro d
    refine ⟨1, ?_⟩
    apply Subtype.ext
    obtain ⟨a, ha, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hc d.property)
    simp only [Fintype.card_fin] at ha
    rcases sq_eq_one_iff.mp ha with rfl | rfl
    · have hd : d.val = 1 := by apply Subtype.ext; simpa using he.symm
      simp [hd]
    · have hd : d.val = -1 := by
        apply Subtype.ext
        simpa [← Matrix.diagonal_neg] using he.symm
      simp [hd]
  have hb : (⊥ : Subgroup D) = ⊤ := hp ⊥ inferInstance
    (hd2.of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective ⊥))
  apply D.eq_bot_iff_forall.mpr
  intro d hd
  have he : (⟨d, hd⟩ : D) = 1 := by
    apply mem_bot.mp
    rw [hb]
    trivial
  exact congrArg Subtype.val he

private theorem solvable_twoPerfect_le_kernel {B : Type*} [Group B] [Finite B]
    {s : ℕ} (hs : s.Prime) (hs3 : 3 < s) (U D : Subgroup B) [U.Normal] [D.Normal]
    [Group.IsSolvable D] (hp : IsPPerfect 2 D)
    (e : B ⧸ U ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod s)) : D ≤ U := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' U)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective U)
  let : (D.map f).Normal := (inferInstance : D.Normal).map f hf
  let : Group.IsSolvable (D.map f) :=
    Group.isSolvable_of_surjective (f.subgroupMap_surjective D)
  have hbot := solvable_twoPerfect_sl_bot hs hs3 (D.map f)
    (hp.of_surjective (f.subgroupMap D) (f.subgroupMap_surjective D))
  intro x hx
  have he : f x = 1 := (D.map_eq_bot_iff.mp hbot) hx
  exact (QuotientGroup.eq_one_iff x).mp (e.injective (by simpa [f] using he))

private theorem xi_image_kernel {A B : Type*} [Group A] [Finite A]
    [Group B] [Finite B] [Group.IsSolvable A]
    {p s : ℕ} (hp : p.Prime) (hpodd : Odd p) (hs : s.Prime) (hs3 : 3 < s)
    (hA : IsPPerfect 2 A) (hshape : XiOddQuotient p (A ⧸ pCore 2 A))
    (f : A →* B) (hk : IsPGroup 2 f.ker) [f.range.Normal]
    (U : Subgroup B) [U.Normal] (hU : LocalModels.ElementaryModel s 2 U)
    (e : B ⧸ U ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod s)) :
    p = s ∧ f.range = U := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact s.Prime := ⟨hs⟩
  let : Group.IsSolvable f.range := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hle : f.range ≤ U := solvable_twoPerfect_le_kernel hs hs3 U f.range
    (hA.of_surjective f.rangeRestrict f.rangeRestrict_surjective) e
  have hodd : Odd (Nat.card f.range) := by
    apply (hs.odd_of_ne_two (by omega)).pow.of_dvd_nat
    exact (elementary_card hU) ▸ card_dvd_of_le hle
  have hbot : pCore 2 f.range = ⊥ := by
    apply disjoint_top.mp
    apply disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := 2) (G := f.range))
    simpa only [hn, card_top] using (Nat.coprime_two_left.mpr hodd).pow_left n
  have he := f.rangeRestrict.comap_pCore_of_ker_isPGroup f.rangeRestrict_surjective
    (hk.of_equiv (MulEquiv.subgroupCongr (MonoidHom.ker_rangeRestrict f)).symm)
  rw [hbot, MonoidHom.comap_bot, MonoidHom.ker_rangeRestrict] at he
  let eqv := (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  exact normal_xi_eq_kernel hp hpodd hs hs3 U f.range hU e (hshape.of_mulEquiv eqv)

variable {G : Type*} [Group G]

private def imageMap {D N : Subgroup G} (hDN : D ≤ N) : D →* quotientImage D N :=
  ((QuotientGroup.mk' (pCore 2 N)).subgroupMap (D.subgroupOf N)).comp
    (subgroupOfEquivOfLe hDN).symm.toMonoidHom

private theorem imageMap_surjective {D N : Subgroup G} (hDN : D ≤ N) :
    Function.Surjective (imageMap hDN) :=
  ((QuotientGroup.mk' (pCore 2 N)).subgroupMap_surjective (D.subgroupOf N)).comp
    (subgroupOfEquivOfLe hDN).symm.surjective

private theorem imageMap_range {X Y N : Subgroup G} (hXY : X ≤ Y) (hYN : Y ≤ N) :
    ((imageMap hYN).comp (inclusion hXY)).range =
      (quotientImage X N).subgroupOf (quotientImage Y N) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y, hYN (hXY y.property)⟩, y.property, rfl⟩
  · rintro ⟨y, hy, he⟩
    exact ⟨⟨y, hy⟩, Subtype.ext he⟩

private theorem imageMap_ker {X Y N : Subgroup G} (hXY : X ≤ Y) (hYN : Y ≤ N) :
    IsPGroup 2 ((imageMap hYN).comp (inclusion hXY)).ker := by
  have he : ((imageMap hYN).comp (inclusion hXY)).ker =
      (pCore 2 N).comap (inclusion (hXY.trans hYN)) := by
    ext x
    change (imageMap hYN (inclusion hXY x) = 1) ↔ _
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  rw [he]
  exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)

variable [Finite G]

/-- The actual Ξ-image is the specified case-(10) kernel, and the primes agree. -/
theorem SourceData.xi_image_eq_kernel {𝒦 : GroupClass} {p r s : ℕ} {L : Subgroup G}
    {T : Sylow 2 G} {C : Subgroup (radicalCore p L T)} {K : Subgroup G}
    (h : SourceData 𝒦 p r L T C K) (hs : s.Prime) (hs3 : 3 < s)
    (U : Subgroup (quotientImage (normalizerResidual L (radicalCore p L T))
      (normalizer (C.map (radicalCore p L T).subtype : Set G)))) [U.Normal]
    (hU : ElementaryModel s 2 U)
    (e : (quotientImage (normalizerResidual L (radicalCore p L T))
      (normalizer (C.map (radicalCore p L T).subtype : Set G))) ⧸ U ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod s)) :
    p = s ∧ (quotientImage (XiP p L)
      (normalizer (C.map (radicalCore p L T).subtype : Set G))).subgroupOf
        (quotientImage (normalizerResidual L (radicalCore p L T))
          (normalizer (C.map (radicalCore p L T).subtype : Set G))) = U := by
  let X := XiP p L
  let Y := normalizerResidual L (radicalCore p L T)
  let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
  have hXY : X ≤ Y := h.contains_xi
  have hYN : Y ≤ N := h.contains_Y.trans h.component.1
  let f := (imageMap hYN).comp (inclusion hXY)
  let : (X.subgroupOf Y).Normal := xi_normal_in_intermediate p (normalizerResidual_le _ _)
  let : f.range.Normal := by
    rw [show f.range = (X.subgroupOf Y).map (imageMap hYN) by
      rw [MonoidHom.range_comp, inclusion_range]]
    exact (inferInstance : (X.subgroupOf Y).Normal).map _ (imageMap_surjective hYN)
  let : Group.IsSolvable X := h.xi.isSolvable
  have hx := xi_image_kernel h.prime (h.prime.odd_of_ne_two (by have := h.large; omega))
    hs hs3 h.xi.perfect h.xi_shape f (imageMap_ker hXY hYN) U hU e
  exact ⟨hx.1, (imageMap_range hXY hYN).symm.trans hx.2⟩


private theorem prime_of_projective_section {A : Type*} [Group A] [Finite A]
    {s : ℕ} (hs : s.Prime) (hs3 : 3 < s) (hA : Nat.card A = 120)
    (W : Subgroup A) (f : W →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s))
    (hf : Function.Surjective f) : s = 5 := by
  let : Fact s.Prime := ⟨hs⟩
  have hc : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s)) ≤ 120 := by
    rw [← hA]
    exact (Nat.card_le_card_of_surjective f hf).trans (Nat.card_le_card_of_injective
      W.subtype W.subtype_injective)
  have he := card_eq_card_quotient_mul_card_subgroup
    (center (Matrix.SpecialLinearGroup (Fin 2) (ZMod s)))
  rw [Atlas.card_sl_two, Nat.card_zmod, Atlas.ExceptionalSupport.card_sl_center,
    Fintype.card_fin, Nat.card_zmod] at he
  have hsmall : s * (s ^ 2 - 1) ≤ 240 := by
    rw [he]
    exact (Nat.mul_le_mul hc (Nat.gcd_le_left _ (by decide))).trans (by decide)
  have hsq : 1 ≤ s ^ 2 := by nlinarith
  have hadd := Nat.sub_add_cancel hsq
  have hs7 : s < 7 := by nlinarith
  by_contra h
  have hd : s = 4 ∨ s = 6 := by omega
  rcases hd with rfl | rfl <;> norm_num at hs

/-- Removing the solvable layers of L bounds the actual case-(10) prime. -/
theorem SourceData.caseTen_parameter_eq_five {𝒦 : GroupClass} {p r s : ℕ} {L : Subgroup G}
    {T : Sylow 2 G} {C : Subgroup (radicalCore p L T)} {K : Subgroup G}
    (h : SourceData 𝒦 p r L T C K)
    (ht : CaseTen
      (quotientImage (normalizerResidual L (radicalCore p L T))
        (normalizer (C.map (radicalCore p L T).subtype : Set G)))
      (quotientImage K (normalizer (C.map (radicalCore p L T).subtype : Set G))) s) : s = 5 := by
  let : Fact s.Prime := ⟨ht.prime⟩
  let Y := normalizerResidual L (radicalCore p L T)
  let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
  have hYL : Y ≤ L := normalizerResidual_le _ _
  have hYN : Y ≤ N := h.contains_Y.trans h.component.1
  obtain ⟨U, hn, _, hquot⟩ := ht.small
  let := hn
  obtain ⟨e⟩ := (isSL_prime_iff ht.prime).mp hquot
  let f : Y →* Matrix.SpecialLinearGroup (Fin 2) (ZMod s) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' U).comp (imageMap hYN))
  have hf : Function.Surjective f :=
    e.surjective.comp ((QuotientGroup.mk'_surjective U).comp (imageMap_surjective hYN))
  let z := QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 2) (ZMod s)))
  let g := (z.comp f).comp (subgroupOfEquivOfLe hYL).toMonoidHom
  have hg : Function.Surjective g :=
    ((QuotientGroup.mk'_surjective _).comp hf).comp (subgroupOfEquivOfLe hYL).surjective
  let q := QuotientGroup.mk' (pCore 2 L)
  let j := (QuotientGroup.mk' (fittingSubgroup (XiQuotient L))).comp q
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    let := pCore_isNilpotent (p := 2) (G := L)
    infer_instance
  let : Group.IsSolvable j.ker := by
    change Group.IsSolvable (((QuotientGroup.mk' (fittingSubgroup (XiQuotient L))).comp q).ker)
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact isSolvable_comap_of_solvable_ker q _
  have hj := SolvableLayersEmbedding.of_solvable_ker j
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (ZMod s)) :=
    sl_quasisimple ht.prime ht.large
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s)) :=
    IsQuasisimple.simple
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s)) :=
    inferInstance
  rcases hj.simpleSection (Y.subgroupOf L) g hg with hsol | ⟨W, a, ha⟩
  · exact (Group.IsPerfect.not_isSolvable _ hsol).elim
  · have hr : r = 5 := parameter_eq_five h.prime_r L h.nilpotent h.quotient_r
    have hc : Nat.card (fittingQuotient L) = 120 := by
      have hm := isSL_two_card h.quotient_r
      simpa [hr] using hm
    exact prime_of_projective_section ht.prime ht.large hc W a ha


private theorem sylow_quotientImage_eq {p : ℕ} [Fact p.Prime]
    {X N : Subgroup G} (hXN : X ≤ N) (hi : IsPGroup p (quotientImage X N))
    (P : Sylow p X) :
    quotientImage ((P : Subgroup X).map X.subtype) N = quotientImage X N := by
  let f := (quotientImage X N).subtype.comp (imageMap hXN)
  have hr : f.range = quotientImage X N := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (imageMap_surjective hXN),
      ← MonoidHom.range_eq_map, range_subtype]
  have hm := sylow_map_eq_range f (hr.symm ▸ hi) P
  have he : (P : Subgroup X).map f =
      quotientImage ((P : Subgroup X).map X.subtype) N := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hXN x.property⟩, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨y, hy, hyx⟩, rfl⟩
      refine ⟨y, hy, ?_⟩
      change QuotientGroup.mk' (pCore 2 N) ⟨y, hXN y.property⟩ =
        QuotientGroup.mk' (pCore 2 N) x
      congr 1
      exact Subtype.ext hyx
  exact he.symm.trans (hm.trans hr)

/-- Both primes and every chosen Sylow image are forced by the source data. -/
theorem SourceData.caseTen_primes_and_marking {𝒦 : GroupClass} {p r s : ℕ} {L : Subgroup G}
    {T : Sylow 2 G} {C : Subgroup (radicalCore p L T)} {K : Subgroup G}
    (h : SourceData 𝒦 p r L T C K)
    (ht : CaseTen
      (quotientImage (normalizerResidual L (radicalCore p L T))
        (normalizer (C.map (radicalCore p L T).subtype : Set G)))
      (quotientImage K (normalizer (C.map (radicalCore p L T).subtype : Set G))) s) :
    p = 5 ∧ s = 5 ∧ ∀ P : Sylow p (XiP p L),
      MarkedFiveExtension (quotientImage (normalizerResidual L (radicalCore p L T)) K)
        (quotientImage ((P : Subgroup (XiP p L)).map (XiP p L).subtype) K) := by
  have hs : s = 5 := h.caseTen_parameter_eq_five ht
  subst s
  let X := XiP p L
  let Y := normalizerResidual L (radicalCore p L T)
  let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
  have hXY : X ≤ Y := h.contains_xi
  have hXN : X ≤ N := hXY.trans (h.contains_Y.trans h.component.1)
  have hle : quotientImage X N ≤ quotientImage Y N := map_mono (comap_mono hXY)
  obtain ⟨U, hn, hU, hquot⟩ := ht.small
  let := hn
  obtain ⟨e⟩ := (isSL_prime_iff (by decide : Nat.Prime 5)).mp hquot
  obtain ⟨hp, heq⟩ := h.xi_image_eq_kernel (by decide) (by decide) U hU e
  have hXi : ElementaryModel 5 2 (quotientImage X N) := by
    obtain ⟨eu⟩ := hU
    exact ⟨(subgroupOfEquivOfLe hle).symm.trans ((MulEquiv.subgroupCongr heq).trans eu)⟩
  have hmark : MarkedFiveExtension (quotientImage Y N) (quotientImage X N) := by
    let : ((quotientImage X N).subgroupOf (quotientImage Y N)).Normal := heq.symm ▸ hn
    exact ⟨hle, hXi, inferInstance, ⟨(QuotientGroup.quotientMulEquivOfEq heq).trans e⟩⟩
  refine ⟨hp, rfl, ?_⟩
  intro P
  let : Fact p.Prime := ⟨h.prime⟩
  have hi : IsPGroup p (quotientImage X N) := by
    rw [hp]
    exact IsPGroup.of_card (elementary_card hXi)
  have he : quotientImage ((P : Subgroup X).map X.subtype) N = quotientImage X N :=
    sylow_quotientImage_eq hXN hi P
  apply (markedFiveExtension_componentQuotient_iff h.contains_Y
    ((map_subtype_le _).trans (hXY.trans h.contains_Y)) h.component.1 h.component.2).mpr
  change MarkedFiveExtension (quotientImage Y N)
    (quotientImage ((P : Subgroup X).map X.subtype) N)
  rw [he]
  exact hmark

private theorem twoCore_eq_bot_of_slThreeFive_embedding
    {B : Type*} [Group B] [Finite B] (U : Subgroup B) [U.Normal]
    (hU : Nat.card U = 25)
    (j : B →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 5)) (hj : Function.Injective j) :
    pCore 2 B = ⊥ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hup : IsPGroup 5 U := IsPGroup.of_card (n := 2) hU
  have hd : Disjoint (pCore 2 B) U :=
    IsPGroup.disjoint_of_ne 2 5 (by decide) _ _ pCore_isPGroup hup
  have hc : pCore 2 B ≤ centralizer (U : Set B) :=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hd)
  rcases (pCore_isPGroup (p := 2) (G := B)).card_eq_or_dvd with hcard | htwo
  · exact card_eq_one.mp hcard
  · obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 htwo
    have hzj : orderOf (j z) = 2 :=
      (orderOf_injective j hj z).trans ((orderOf_coe z).trans hz)
    let f : U →* centralizer ({j z} : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod 5))) :=
      (j.comp U.subtype).codRestrict _ (fun u => by
        apply mem_centralizer_singleton_iff.mpr
        change j (u : B) * j (z : B) = j (z : B) * j (u : B)
        rw [← map_mul, ← map_mul]
        exact congrArg j (mem_centralizer_iff.mp (hc z.property) u u.property))
    have hf : Function.Injective f := by
      intro a b hab
      exact Subtype.ext (hj (congrArg Subtype.val hab))
    let e : centralizer ({j z} : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod 5))) ≃*
        GL (Fin 2) (ZMod 5) :=
      Matrix.SL3.involutionCentralizerEquiv (ZMod 5) (j z) hzj (by decide)
    have hdiv := card_dvd_of_injective (e.toMonoidHom.comp f) (e.injective.comp hf)
    have hGL : Nat.card (GL (Fin 2) (ZMod 5)) = 480 := by
      simpa [Nat.card_eq_fintype_card, Fin.prod_univ_two] using
        (Matrix.card_GL_field (𝔽 := ZMod 5) 2)
    rw [hU, hGL] at hdiv
    norm_num at hdiv

/-- The actual Y-image has trivial two-core; the large model is essential here. -/
theorem SourceData.caseTen_twoCore_eq_bot {𝒦 : GroupClass} {p r s : ℕ} {L : Subgroup G}
    {T : Sylow 2 G} {C : Subgroup (radicalCore p L T)} {K : Subgroup G}
    (h : SourceData 𝒦 p r L T C K)
    (ht : CaseTen
      (quotientImage (normalizerResidual L (radicalCore p L T))
        (normalizer (C.map (radicalCore p L T).subtype : Set G)))
      (quotientImage K (normalizer (C.map (radicalCore p L T).subtype : Set G))) s) :
    pCore 2 (quotientImage (normalizerResidual L (radicalCore p L T))
      (normalizer (C.map (radicalCore p L T).subtype : Set G))) = ⊥ := by
  have hs := h.caseTen_parameter_eq_five ht
  subst s
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let Y := normalizerResidual L (radicalCore p L T)
  let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
  have hYK : quotientImage Y N ≤ quotientImage K N :=
    map_mono (comap_mono h.contains_Y)
  obtain ⟨eK⟩ := large_five_model ht.large_model
  have hcenter : center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 5)) = ⊥ := by
    apply card_eq_one.mp
    rw [Atlas.ExceptionalSupport.card_sl_center]
    norm_num
  let eSL : Matrix.SpecialLinearGroup (Fin 3) (ZMod 5) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 5) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hcenter.symm)
  let j := (eK.trans eSL.symm).toMonoidHom.comp (inclusion hYK)
  have hj : Function.Injective j := (eK.trans eSL.symm).injective.comp (inclusion_injective hYK)
  obtain ⟨U, hn, hU, _⟩ := ht.small
  let := hn
  exact twoCore_eq_bot_of_slThreeFive_embedding U (elementary_card hU) j hj

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
