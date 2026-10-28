module
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.SourceMany
public import CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity.Source
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.PrimaryRadicalNormalizer
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Residual

/-!
# Characteristic-normalizer control from the active full primary radical

Let R=O₂(Ξ_p(L)T), I=O^{p′}(O∞(L)), and Y=N_L(R)^∞. In the actual
homocyclic case, the natural power map identifies the Frattini quotient of
I/O₂(I) with the omega quotient of O_p(L/O₂(L)). This identification respects
the original conjugation action. The proved irreducibility of Y on Ξ_p(L)
therefore gives [I,Y]=I. Coprime omega detection already makes I normalize
R, so I normalizes Y and the commutator identity gives I≤Y.

If I has nonzero intrinsic module, A.4.10 makes Y faithful. The established
residual structure makes Y a nonquasisimple local component. Under the
original Hypothesis13.1.1 and multiple-overgroup assumption,13.1.4 gives a
unique maximal two-local above YT. Since N_G(L) is one such overgroup, every
normalizer of a nontrivial characteristic subgroup of R lies in N_G(L).

This proves the bound for the literal original R. It needs no single-prime
condition, universal A.3.12 premise, or replacement of R by O₂(IT).
Source: Aschbacher--Smith1.3.8, pp.512--514; A.4.10, p.60;
3.2.14, p.585;13.1.4(2),(5), p.867.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
open Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate Chapter1.RadicalNormalizers
open Chapter1.RadicalActions Chapter12.Section02 ChapterA.Section04
open Chapter3.RadicalCentralization
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem isCyclic_of_all_subgroups_trivial
    {V : Type*} [Group V]
    (h : ∀ A : Subgroup V, A = ⊥ ∨ A = ⊤) : IsCyclic V := by
  classical
  by_cases hs : Subsingleton V
  · let := hs
    infer_instance
  · let : Nontrivial V := not_subsingleton_iff_nontrivial.mp hs
    obtain ⟨v, hv⟩ := exists_ne (1 : V)
    rcases h (zpowers v) with hb | ht
    · exact (hv (Subgroup.mem_bot.mp (hb ▸ mem_zpowers v))).elim
    · exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨v, ht⟩

private theorem commutator_eq_of_xiFrattini_irreducible
    {G : Type*} [Group G] [Finite G] (X S : Subgroup G)
    (hn : S ≤ normalizer (X : Set G)) (hX : IsPPerfect 2 X)
    (hnc : ¬ IsCyclic (XiFrattiniQuotient X))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ s : S, ∀ a ∈ A, xiFrattiniAction S X hn s a ∈ A) →
        A = ⊥ ∨ A = ⊤) : ⁅X,S⁆ = X := by
  let D := ⁅X,S⁆.subgroupOf X
  let q := QuotientGroup.mk' (pCore 2 X)
  let f := (QuotientGroup.mk' (frattini (XiQuotient X))).comp q
  let _ := conjMulDistribMulActionOfLeNormalizer S X hn
  have he (s : S) (x : X) :
      xiFrattiniAction S X hn s (f x) = f (s • x) := by
    simp only [xiFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk, f, q]
    rfl
  have hstable : ∀ s : S, ∀ a ∈ D.map f, xiFrattiniAction S X hn s a ∈ D.map f := by
    rintro s a ⟨x, hx, rfl⟩
    refine ⟨s • x, ?_, (he s x).symm⟩
    exact (mem_normalizer_iff.mp (normalizer_commutator_ge_right X S s.property) x).mp hx
  have himage : D.map f = ⊤ := by
    rcases hirr (D.map f) hstable with hb | ht
    · have hfix (s : S) (a : XiFrattiniQuotient X) : xiFrattiniAction S X hn s a = a := by
        obtain ⟨x, rfl⟩ := ((QuotientGroup.mk'_surjective _).comp
          (QuotientGroup.mk'_surjective _)) a
        change xiFrattiniAction S X hn s (f x) = f x
        rw [he]
        have hd : (s • x) * x⁻¹ ∈ D := by
          change ⁅(s : G), (x : G)⁆ ∈ ⁅X,S⁆
          rw [commutator_comm]
          exact commutator_mem_commutator s.property x.property
        have hz : f ((s • x) * x⁻¹) = 1 :=
          Subgroup.mem_bot.mp (hb ▸ mem_map_of_mem f hd)
        rw [map_mul, map_inv] at hz
        exact mul_inv_eq_one.mp hz
      exact (hnc (isCyclic_of_all_subgroups_trivial (fun A =>
        hirr A (by intro s a ha; rw [hfix]; exact ha)))).elim
    · exact ht
  have hqimage : D.map q = ⊤ := by
    apply frattini_nongenerating
    have hm := congrArg (comap (QuotientGroup.mk' (frattini (XiQuotient X)))) himage
    rw [← map_map, comap_map_eq, QuotientGroup.ker_mk', comap_top] at hm
    exact hm
  have hsup : D ⊔ pCore 2 X = ⊤ := by
    have hm := congrArg (comap q) hqimage
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hm
  let : D.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left X S)
  have hD : D = ⊤ := hX D inferInstance
    (isPGroup_quotient_of_sup_eq_top D (pCore 2 X) pCore_isPGroup hsup)
  have hm := congrArg (map X.subtype) hD
  simpa only [D, map_subgroupOf_eq_of_le (le_normalizer_iff_commutator_le_left.mp hn),
    ← MonoidHom.range_eq_map, range_subtype] using hm


private def primaryFrattiniEquiv
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    XiFrattiniQuotient (primaryRadical p L) ≃*
      (pCore p (XiQuotient L) ⧸ frattini (pCore p (XiQuotient L))) :=
  QuotientGroup.congr _ _ (primaryRadicalQuotientEquiv hG T hL ho) (frattini_map_equiv _)

private theorem primaryFrattiniEquiv_equivariant
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (l : L)
    (z : XiFrattiniQuotient (primaryRadical p L)) :
    primaryFrattiniEquiv hG T hL ho
      (xiFrattiniAction L (primaryRadical p L)
        (L.le_normalizer.trans (normalizer_le_normalizer_primaryRadical L p)) l z) =
      FittingActions.coreFrattiniAction p (XiQuotient L) (QuotientGroup.mk' _ l)
        (primaryFrattiniEquiv hG T hL ho z) := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective _ z
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective _ x
  simp only [xiFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk]
  change QuotientGroup.mk' _ (primaryRadicalQuotientEquiv hG T hL ho
    (QuotientGroup.mk' _ _)) = quotientAut _ _
      (QuotientGroup.mk' _ (primaryRadicalQuotientEquiv hG T hL ho (QuotientGroup.mk' _ x)))
  rw [quotientAut_apply_mk]
  apply congrArg (QuotientGroup.mk' _)
  apply Subtype.ext
  rw [primaryRadicalQuotientEquiv_apply_mk, FittingActions.coreAction_apply,
    primaryRadicalQuotientEquiv_apply_mk, ← map_mul, ← map_inv, ← map_mul]
  rfl

private def primaryXiFrattiniEquiv
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    {p a : ℕ} [Fact p.Prime] (ho : Odd p) (ha : 1 ≤ a)
    (e : XiQuotient (primaryRadical p L) ≃* Multiplicative (Fin 2 → ZMod (p^a))) :
    XiFrattiniQuotient (primaryRadical p L) ≃* XiFrattiniQuotient (XiP p L) :=
  (primaryFrattiniEquiv hG T hL ho).trans
    (((HomocyclicOmegaFrattini.quotientEquiv ha
      ((primaryRadicalQuotientEquiv hG T hL ho).symm.trans e)).trans
      (FittingActions.embeddedOmegaFrattiniEquiv p (XiQuotient L))).trans
      (xiPFrattiniEquivCore ho L).symm)

private theorem primaryXiFrattiniEquiv_equivariant
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    {p a : ℕ} [Fact p.Prime] (ho : Odd p) (ha : 1 ≤ a)
    (e : XiQuotient (primaryRadical p L) ≃* Multiplicative (Fin 2 → ZMod (p^a)))
    (l : L) (z : XiFrattiniQuotient (primaryRadical p L)) :
    primaryXiFrattiniEquiv hG T hL ho ha e
      (xiFrattiniAction L (primaryRadical p L)
        (L.le_normalizer.trans (normalizer_le_normalizer_primaryRadical L p)) l z) =
      xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer) l
        (primaryXiFrattiniEquiv hG T hL ho ha e z) := by
  apply (xiPFrattiniEquivCore ho L).injective
  rw [xiPFrattiniEquivCore_equivariant]
  simp only [primaryXiFrattiniEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rw [primaryFrattiniEquiv_equivariant]
  change FittingActions.embeddedOmegaFrattiniEquiv p (XiQuotient L)
    (HomocyclicOmegaFrattini.quotientEquiv ha _
      (quotientAut _ (FittingActions.coreAction p _ (QuotientGroup.mk' _ l)) _)) = _
  rw [HomocyclicOmegaFrattini.quotientEquiv_equivariant,
    FittingActions.embeddedOmegaFrattiniEquiv_equivariant]

/-- The full primary radical is generated by its commutators with the
canonical radical-normalizer residual, including the higher homocyclic case. -/
theorem primaryRadical_commutator_normalizerResidual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p a : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (ha : 1 ≤ a)
    (e : XiQuotient (primaryRadical p L) ≃* Multiplicative (Fin 2 → ZMod (p^a))) :
    ⁅primaryRadical p L, normalizerResidual L (radicalCore p L T)⁆ = primaryRadical p L := by
  let h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  have h38 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ → ∀ B : Subgroup A,
      B.IsCComponent → B.Normal ∨ IsQuasisimple B :=
    fun _ _ _ hA hO _ hB => ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hA hO hB
  have hQ := uniqueness_local_quotient_sqtk hG hL.1.2.2
  have hr := residual_normalizer_data_of_source h36 h38 hL hQ hn ho hd
  let I := primaryRadical p L
  let Y := normalizerResidual L (radicalCore p L T)
  have hYI : Y ≤ normalizer (I : Set G) :=
    (normalizerResidual_le _ _).trans
      (L.le_normalizer.trans (normalizer_le_normalizer_primaryRadical L p))
  let v := primaryXiFrattiniEquiv hG T hL.1 ho ha e
  have hev (y : Y) (z : XiFrattiniQuotient I) :
      v (xiFrattiniAction Y I hYI y z) =
        xiFrattiniAction Y (XiP p L) (Y_normalizes_XiP p p L T) y (v z) := by
    exact primaryXiFrattiniEquiv_equivariant hG T hL.1 ho ha e
      (inclusion (normalizerResidual_le _ _) y) z
  have hi : ∀ A : Subgroup (XiFrattiniQuotient I),
      (∀ y : Y, ∀ z ∈ A, xiFrattiniAction Y I hYI y z ∈ A) → A = ⊥ ∨ A = ⊤ := by
    exact GroupActionTransport.equivariant_irreducible
      (xiFrattiniAction Y I hYI)
      (xiFrattiniAction Y (XiP p L) (Y_normalizes_XiP p p L T)) v hev
      (fun A hh => (hr.actions p Fact.out ho hd).2 A (fun y z hz => hh y z hz))
  have hnc : ¬ IsCyclic (XiFrattiniQuotient I) := by
    intro hc
    let := hc
    have hshape := (XiP_oddQuotient_of_A36 h36 hL.1 hQ hn ho hd).2
    exact (OddInvolutionFrattini.noncyclic_frattini_quotient hshape.not_isCyclic)
      (isCyclic_of_surjective v.toMonoidHom v.surjective)
  exact commutator_eq_of_xiFrattini_irreducible I Y hYI
    (primaryRadical_twoPerfect L ho) hnc hi

/-- The same original residual contains the full higher primary radical. -/
theorem primaryRadical_le_normalizerResidual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p a : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (ha : 1 ≤ a)
    (e : Nonempty (XiQuotient (primaryRadical p L) ≃* Multiplicative (Fin 2 → ZMod (p^a)))) :
    primaryRadical p L ≤ normalizerResidual L (radicalCore p L T) := by
  rw [← primaryRadical_commutator_normalizerResidual hG T hL hn ho hd ha e.some]
  exact le_normalizer_iff_commutator_le_right.mp
    (le_normalizer_normalizerResidual
      ((map_subtype_le _).trans L.le_normalizer)
      (primaryRadical_normalizes_radicalCore_of_homocyclic hG T hL.1 hn ho e))

/-- Activity of the full higher primary radical makes the actual normalizer
residual a nonquasisimple faithful local component. -/
theorem active_primary_normalizerResidual_faithful
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p a : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (ha : 1 ≤ a)
    (e : Nonempty (XiQuotient (primaryRadical p L) ≃* Multiplicative (Fin 2 → ZMod (p^a))))
    (hi : intrinsicSignalizerModule (primaryRadical p L) ≠ ⊥) :
    normalizerResidual L (radicalCore p L T) ∈ nonquasisimpleFaithful T := by
  let h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  have h38 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ → ∀ B : Subgroup A,
      B.IsCComponent → B.Normal ∨ IsQuasisimple B :=
    fun _ _ _ hA hO _ hB => ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hA hO hB
  have hr := residual_normalizer_data_of_source h36 h38 hL
    (uniqueness_local_quotient_sqtk hG hL.1.2.2) hn ho hd
  let I := primaryRadical p L
  let Y := normalizerResidual L (radicalCore p L T)
  have hIY : I ≤ Y := primaryRadical_le_normalizerResidual hG T hL hn ho hd ha e
  have hIL : I ≤ L := map_subtype_le _
  have hLI : L ≤ normalizer (I : Set G) :=
    L.le_normalizer.trans (normalizer_le_normalizer_primaryRadical L p)
  have hTI : (T : Subgroup G) ≤ normalizer (I : Set G) :=
    hr.t_normalizes.trans (normalizer_le_normalizer_primaryRadical L p)
  have hJY : Y ⊔ (T : Subgroup G) ≤ normalizer (I : Set G) :=
    sup_le ((normalizerResidual_le _ _).trans hLI) hTI
  have hIne : I ≠ ⊥ := by
    intro hz
    exact hi (bot_unique ((intrinsicModule_le_self I).trans_eq hz))
  have hTjoin : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) := le_sup_right
  have hJHe : L ⊔ (T : Subgroup G) ∈ He G :=
    lemma_1_1_4_6 T (hG.evenCharacteristic T) ⟨hL.1.2.2,hTjoin⟩
  have hIHe : I ∈ He G := lemma_1_1_3_1 hJHe hIne (hIL.trans le_sup_left)
    (normal_subgroupOf_of_le_normalizer
      (sup_le hLI hTI)).isSubnormal
  have hIt : IsSignalizerType I := ⟨hIne,primaryRadical_twoPerfect L ho,
    generalizedFitting_eq_pCore_of_selfCentralizing 2 (mem_He_iff.mp hIHe)⟩
  have hYt := mem_L_isSignalizerType T (hG.evenCharacteristic T) hr.Y_mem_L
  have hSyl : IsSylowIn 2 (T : Subgroup G) (Y ⊔ (T : Subgroup G)) := hr.Y_mem_L.2.1
  have hcore : (Y ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      (T : Subgroup G) ⊓ normalizer (I : Set G) := by
    apply le_inf _ ((pCoreIn_le 2 _).trans hJY)
    have hh := pCoreIn_le_sylow (Y ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using hh
  have hSylI : IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (I : Set G))
      ((Y ⊔ (T : Subgroup G)) ⊓ normalizer (I : Set G)) := by
    simpa only [inf_eq_left.mpr hTI,inf_eq_left.mpr hJY] using hSyl
  have hf := (SourceChains.source_A410 I Y (T : Subgroup G) hIY hIt hYt
    hr.t_normalizes_Y hSyl hcore hSylI).2.2 ⟨hIt,hi⟩
  exact ⟨(mem_faithfulLocalComponents_iff T Y).mpr ⟨hr.Y_mem_L,hf⟩,hr.Y_not_quasisimple⟩

/-- The actual active higher primary radical supplies characteristic-normalizer
control for R=O₂(Ξ_p(L)T), through the faithful residual's unique maximal local. -/
theorem active_higher_primary_characteristic_control
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p a : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hi : intrinsicSignalizerModule (primaryRadical p L) ≠ ⊥) (ha : 1 ≤ a)
    (e : Nonempty (XiQuotient (primaryRadical p L) ≃* Multiplicative (Fin 2 → ZMod (p^a)))) :
    ((XiP p L ⊔ (T : Subgroup G)).pCoreIn 2).characteristicNormalizerClosure ≤
      normalizer (L : Set G) := by
  let Y := normalizerResidual L (radicalCore p L T)
  have hY := active_primary_normalizerResidual_faithful h.simpleQTKE T hL hn ho hd ha e hi
  obtain ⟨B,hB,hYB,hf,hbn,hmax,hjoin,hu,_⟩ := h.maximal_counterexample_of_many hmany hY
  obtain ⟨_,_,hM⟩ := RadicalConjugateRigidity.maximal_radical_structure h.simpleQTKE T hL hn ho hd
  have hTL := radicalLocal_invariant_source hL.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.2.2) hn
  have hYM : Y ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le ((normalizerResidual_le _ _).trans L.le_normalizer) hTL
  have he := hu (normalizer (L : Set G)) hM hYM
  apply characteristicNormalizerClosure_le_of_unique_twoLocal
    (radicalCore_isTwoGroup p L T)
    (sup_le (normalizerResidual_le_normalizer _ _) (t_le_normalizer_radicalCore p L T))
  intro N hN hYN
  exact (hu N hN hYN).trans he.symm

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
