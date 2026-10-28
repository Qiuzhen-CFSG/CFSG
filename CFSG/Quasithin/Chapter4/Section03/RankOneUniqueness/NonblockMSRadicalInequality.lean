module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSConstruction
public import Theory.SpecificGroups.PSL3.LinearThreeRootFixed
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.FixedCubic

/-!
# The original natural-center radical inequality

Write R=O₂(I) and J=KR, with all subgroups embedded in the original G.
If R were O₂(C_J(Ω₁Z(P))) for an eligible Sylow P, its characteristic
normalizer control would make C_K(C_U(P)) normalize L and hence W=[U,L].
Align the same natural action with P∩K. The vector stabilizer fixes the
Sylow-fixed vectors and therefore preserves W. Every proper invariant
additive subgroup of that stabilizer has order at most |F|, whereas the
original line action puts a plane of order |F|² inside W. This contradiction
proves the literal C.1.34 radical inequality for every eligible P.

The resulting constructor supplies MSData and both simultaneous original
markings from the whole natural-center and doubled-dual sections. Its
secondary-component application retains the original embeddings and orbit.
The whole-core classification and third-row selection still require the
existing qt-c134-nonbinary-linear-three-source input and this owner's final
discharge. Strict secondary-core enlargement remains with
qt-d-1222-rankone-uniqueness-nonblock; no full nonblock exclusion is asserted.

Source: Aschbacher--Smith C.1.34(3), pp.136--137; C.2.8--10, pp.147--148;
and original 4.3.8--10, pp.616--617. The proof uses the original ambient
normalizer hypotheses, rather than a universal MS classification premise.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L}

private theorem point_invariant_card {F : Type*} [Field F] [Finite F]
    (A : AddSubgroup (Fin 3 → F)) (ha : A ≠ ⊤)
    (hinv : ∀ g ∈ pointLocalSL F, ∀ v ∈ A, g.val.mulVec v ∈ A) :
    Nat.card A ≤ Nat.card F := by
  have hfix := Representation.SL3ParabolicNatural.point_invariant_fixed A ha hinv
  let f : A → F := fun v => v.val 0
  apply Nat.card_le_card_of_injective f
  intro v w he
  have hv := (pointRadicalSL_fixed_iff F v.val).mp (fun g hg => hfix g g.property v v.property)
  have hw := (pointRadicalSL_fixed_iff F w.val).mp (fun g hg => hfix g g.property w w.property)
  obtain ⟨a,ha⟩ := hv
  obtain ⟨b,hb⟩ := hw
  have hab : a = b := by
    change v.val 0 = w.val 0 at he
    simpa only [ha,hb,Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,mul_one] using he
  exact Subtype.ext (ha.trans ((hab ▸ hb).symm))


omit [Finite G] in
private theorem coordinates_of_natural {F : Type*} [Field F]
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3)) :
    ∃ f : U c ≃* Multiplicative (Fin 3 → F),
      ∀ (k : K c) (u v : U c), (v : G) = k * (u : G) * (k : G)⁻¹ →
        (f v).toAdd = (linearThreeActor e k).val.mulVec (f u).toAdd := by
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,f,hf⟩ := hm
  let := hn
  exact ⟨QuotientGroup.quotientBot.symm.trans f,hf⟩

omit [Finite G] in
private theorem center_normalized : c.H ≤ normalizer (U c : Set G) :=
  (core_normalized c).trans (normalizer_le_normalizer_characteristic_image (Q c) (center (Q c)))

private abbrev fullImage {F : Type*} [Field F]
    (f : U c ≃* Multiplicative (Fin 3 → F)) : AddSubgroup (Fin 3 → F) :=
  (((W c).subgroupOf (U c)).map f.toMonoidHom).toAddSubgroup'

private theorem fullImage_card {F : Type*} [Field F]
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (f : U c ≃* Multiplicative (Fin 3 → F)) :
    Nat.card (fullImage f) = Nat.card (W c) := by
  change Nat.card (((W c).subgroupOf (U c)).map f.toMonoidHom) = _
  rw [card_map_of_injective f.injective,
    Nat.card_congr (subgroupOfEquivOfLe (fullModule_le_coreCenter hf)).toEquiv]

private theorem fullImage_ne_bot {F : Type*} [Field F]
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (f : U c ≃* Multiplicative (Fin 3 → F)) : fullImage f ≠ ⊥ := by
  intro hz
  apply c.c28.module_nontrivial
  apply bot_unique
  intro w hw
  let u : U c := ⟨w,fullModule_le_coreCenter hf hw⟩
  have hh : (f u).toAdd ∈ fullImage f := ⟨u,hw,rfl⟩
  rw [hz] at hh
  exact mem_bot.mpr (congrArg Subtype.val
    (f.map_eq_one_iff.mp (Multiplicative.toAdd.injective hh)))

private theorem fullImage_ne_top {F : Type*} [Field F]
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (f : U c ≃* Multiplicative (Fin 3 → F)) : fullImage f ≠ ⊤ := by
  intro ht
  apply (fullModule_lt_coreCenter hf).not_ge
  intro u hu
  have hh : (f ⟨u,hu⟩).toAdd ∈ fullImage f := ht ▸ trivial
  obtain ⟨v,hv,hvu⟩ := hh
  have he : v = ⟨u,hu⟩ := f.injective hvu
  change (v : G) ∈ W c at hv
  simpa only [he] using hv

omit [Finite G] in
private theorem fullImage_invariant {F : Type*} [Field F]
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (f : U c ≃* Multiplicative (Fin 3 → F))
    (he : ∀ (k : K c) (u v : U c), (v : G) = k * (u : G) * (k : G)⁻¹ →
      (f v).toAdd = (linearThreeActor e k).val.mulVec (f u).toAdd)
    (B : Subgroup G) (_hBK : B ≤ K c) (hBW : B ≤ normalizer (W c : Set G)) :
    ∀ g ∈ (B.subgroupOf (K c)).map (linearThreeActor e),
      ∀ v ∈ fullImage f, g.val.mulVec v ∈ fullImage f := by
  rintro _ ⟨k,hk,rfl⟩ _ ⟨u,hu,rfl⟩
  let v : U c := (U c).normalizerMonoidHom
    ⟨k,center_normalized ((map_subtype_le _) k.property)⟩ u
  have hv : (v : G) = k * (u : G) * (k : G)⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
  refine ⟨v,?_,Multiplicative.toAdd.injective (he k u v hv)⟩
  change (v : G) ∈ W c
  rw [hv]
  exact (mem_normalizer_iff.mp (hBW hk) u).mp hu

private theorem natural_fullModule_large {F : Type} [Field F] [Finite F]
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3))
    (hL : (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F)
    (hfull : ⁅U c,L⁆ = W c) : Nat.card F < Nat.card (W c) := by
  obtain ⟨f,he⟩ := coordinates_of_natural e hm
  have hnL : L ≤ normalizer (W c : Set G) := by
    rw [←hfull]
    exact normalizer_commutator_ge_right _ _
  have hinv := fullImage_invariant e f he L c.le_component hnL
  rw [hL] at hinv
  have hplane := Representation.SL3ParabolicNatural.line_plane_le _
    (fullImage_ne_bot hf f) hinv
  let i : (Fin 2 → F) → fullImage f := fun v => ⟨![v 0,v 1,0],hplane _ rfl⟩
  have hi : Function.Injective i := by
    intro v w hvw
    have hval := congrArg Subtype.val hvw
    ext j
    fin_cases j
    · exact congrFun hval 0
    · exact congrFun hval 1
  have hc := Nat.card_le_card_of_injective i hi
  rw [Nat.card_fun,Nat.card_fin,fullImage_card hf f] at hc
  have hlt : Nat.card F < Nat.card F ^ 2 := by
    simpa only [pow_one] using
      (Nat.pow_lt_pow_right (Finite.one_lt_card (α := F)) (show 1 < 2 by decide))
  exact hlt.trans_le hc

private theorem marked_radical_inequality {F : Type} [Field F] [Finite F] [CharP F 2]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3))
    (hfull : ⁅U c,L⁆ = W c) (hlarge : Nat.card F < Nat.card (W c))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P)
    (hmark : ((P ⊓ K c).subgroupOf (K c)).map (linearThreeActor e) = unipotentSL F) :
    MSNotCentralizerCore (K c) (c.I.pCoreIn 2) P := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  intro hbad
  let C := (K c ⊔ c.I.pCoreIn 2) ⊓ centralizer (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn P : Set G)
  have hR : c.I.pCoreIn 2 = C.pCoreIn 2 := hbad
  have hCH : C ≤ c.H := inf_le_left.trans (sup_le (map_subtype_le _)
    ((pCoreIn_le 2 _).trans c.I_le_H))
  have hCL : C ≤ normalizer (L : Set G) := by
    apply (le_inf hCH ?_).trans (c.c28.normalizer_le.trans inf_le_right)
    rw [hR]
    exact C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  let B := K c ⊓ centralizer ((U c ⊓ centralizer (P : Set G) : Subgroup G) : Set G)
  have hBC : B ≤ C := by
    have hh := ms_natural_center_sylow_centralizer c D hf n hn hF e P hP hRP hm
    change C = B ⊔ c.I.pCoreIn 2 at hh
    exact le_sup_left.trans_eq hh.symm
  have hBW : B ≤ normalizer (W c : Set G) := by
    rw [←hfull]
    intro b hb
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (center_normalized ((map_subtype_le _) hb.1)),
      mem_normalizer_iff_map_conj_eq.mp (hCL (hBC hb))]
  obtain ⟨f,he⟩ := coordinates_of_natural e hm
  have hpoint : pointLocalSL F ≤ (B.subgroupOf (K c)).map (linearThreeActor e) := by
    intro g hg
    obtain ⟨k,hk⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _)) g
    change linearThreeActor e k = g at hk
    refine ⟨k,⟨k.property,?_⟩,hk⟩
    apply mem_centralizer_iff.mpr
    intro z hz
    let u : U c := ⟨z,hz.1⟩
    have hfix : ∀ a : unipotentSL F, a.val.val.mulVec (f u).toAdd = (f u).toAdd := by
      intro a
      obtain ⟨p,hp,hpa⟩ := hmark.ge a.property
      have hc := mem_centralizer_iff.mp hz.2 p hp.1
      have hh := he p u u (by
        change z = (p : G)*z*(p : G)⁻¹
        rw [hc,mul_inv_cancel_right])
      rw [hpa] at hh
      exact hh.symm
    let v : U c := (U c).normalizerMonoidHom
      ⟨k,center_normalized ((map_subtype_le _) k.property)⟩ u
    have hv : (v : G) = k * (u : G) * (k : G)⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
    have hh := he k u v hv
    rw [hk] at hh
    have hgfix : g.val.mulVec (f u).toAdd = (f u).toAdd :=
      pointLocalSL_fixes_unipotent_fixed_space g hg _ hfix
    have hvu : v = u := f.injective (Multiplicative.toAdd.injective (hh.trans hgfix))
    have hc : (k : G)*z*(k : G)⁻¹ = z := hv.symm.trans (congrArg Subtype.val hvu)
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  have hinv := fullImage_invariant e f he B inf_le_left hBW
  have hcard := point_invariant_card (fullImage f) (fullImage_ne_top hf f)
    (fun g hg => hinv g (hpoint hg))
  rw [fullImage_card hf f] at hcard
  exact hlarge.not_ge hcard

private theorem component_sylow_image {F : Type} [Field F] [Finite F]
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2)) :
    ∃ A : Sylow 2 SL(3,F),
      ((P ⊓ K c).subgroupOf (K c)).map (linearThreeActor e) = A := by
  let J := K c ⊔ c.I.pCoreIn 2
  let K₀ := (K c).subgroupOf J
  let eK : K₀ ≃* K c := subgroupOfEquivOfLe le_sup_left
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (K c).le_normalizer c.block_radical_normalizes)
  obtain ⟨P₀,hP₀⟩ := hP
  obtain ⟨A,hA⟩ := P₀.exists_sylow_map_eq_inf_of_normal K₀
  let A' := A.mapSurjective (f := eK.toMonoidHom) eK.surjective
  have hA' : (A' : Subgroup (K c)).map (K c).subtype = P ⊓ K c := by
    change ((A : Subgroup K₀).map eK.toMonoidHom).map (K c).subtype = _
    rw [map_map]
    have he : (K c).subtype.comp eK.toMonoidHom = J.subtype.comp K₀.subtype := rfl
    rw [he,←map_map,hA,Subgroup.map_inf _ _ _ J.subtype_injective,
      hP₀,map_subgroupOf_eq_of_le (show K c ≤ J from le_sup_left)]
  have hAs : (A' : Subgroup (K c)) = (P ⊓ K c).subgroupOf (K c) := by
    apply map_injective (K c).subtype_injective
    rw [hA',map_subgroupOf_eq_of_le inf_le_right]
  exact ⟨A'.mapSurjective (f := linearThreeActor e)
    (e.surjective.comp (QuotientGroup.mk'_surjective _)),by
      change _ = (A' : Subgroup (K c)).map _
      rw [hAs]⟩

/-- Original radical-normalizer control proves the third-row inequality for
all eligible Sylows once the original natural center has the line marking. -/
theorem natural_center_radical_inequality {F : Type} [Field F] [Finite F] [CharP F 2]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3))
    (hL : (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F)
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P) :
    MSNotCentralizerCore (K c) (c.I.pCoreIn 2) P := by
  have hfull := (natural_center_line_and_fullModule hf e hm (Or.inr hL)).2
  have hlarge := natural_fullModule_large hf e hm hL hfull
  obtain ⟨A,hA⟩ := component_sylow_image e P hP
  obtain ⟨g,hg,_⟩ := Matrix.PSL3.CartanActions.BorelQuotient.sylowSL_normalizer_conjugate
    F (by omega : 0 < n) hF A
  let e' := e.trans (MulAut.conj g⁻¹)
  have hm' : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e')
      (Representation.specialLinearNatural (k := F) 3) := by
    let ρ := Representation.specialLinearNatural (k := F) 3
    let a := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g⁻¹)
    apply hm.transport a.toAddEquiv
    intro x v
    change ρ g⁻¹ (ρ (linearThreeActor e x) v) =
      ρ (g⁻¹ * linearThreeActor e x * (g⁻¹)⁻¹) (ρ g⁻¹ v)
    simp only [←Module.End.mul_apply,←map_mul]
    simp
  have hp' : ((P ⊓ K c).subgroupOf (K c)).map (linearThreeActor e') = unipotentSL F := by
    have he : linearThreeActor e' = (MulAut.conj g⁻¹).toMonoidHom.comp (linearThreeActor e) := rfl
    rw [he,←map_map,hA,←hg,map_map]
    have hec : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id SL(3,F) := by
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rw [hec,map_id]
  exact marked_radical_inequality D hf n hn hF e' hm' hfull hlarge P hP hRP hp'

/-- Construct the original MS witness and simultaneous markings from the
whole natural and doubled-dual sections. The original radical inequalities
are proved internally, including at field four. -/
theorem exists_msData_of_whole_caseThree
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (n : ℕ) (hn : 1 < n)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hdegree : F.degree = n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier))
    (hnat : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F.Carrier) 3))
    (hdual : HasSectionModel (K c) (Q c) (U c) (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F.Carrier) 3).dual.prod
        (Representation.specialLinearNatural (k := F.Carrier) 3).dual)) :
    ∃ d : MSData c n, d.field = F ∧
      (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier ∧
      ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier := by
  have hF : Nat.card F.Carrier = 2^n := F.card_eq.trans (congrArg (2^·) hdegree)
  obtain ⟨e',hnat',hdual',hpar⟩ := exists_reframed_natural_center_sections D hf hn hF e hnat hdual
  have hL := (natural_center_line_and_fullModule hf e' hnat' hpar).1
  apply exists_msData_of_natural_center_sections D hf n hn F hdegree e' hnat' hdual' hpar
  intro P hRP
  exact natural_center_radical_inequality D hf n hn hF e' hnat' hL
    ((P : Subgroup (K c ⊔ c.I.pCoreIn 2 : Subgroup G)).map
      (K c ⊔ c.I.pCoreIn 2 : Subgroup G).subtype) ⟨P,rfl⟩ hRP

/-- Apply the same constructed MS data to the original secondary component.
Only the whole section models remain as classification inputs; the radical
inequality is no longer an independent premise. Strict core enlargement and
final discharge of the whole-core classification stay with this owner. -/
theorem exists_sourceComponent_of_whole_caseThree
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (n : ℕ) (hn : 1 < n)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hdegree : F.degree = n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier))
    (hnat : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F.Carrier) 3))
    (hdual : HasSectionModel (K c) (Q c) (U c) (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F.Carrier) 3).dual.prod
        (Representation.specialLinearNatural (k := F.Carrier) 3).dual)) :
    ∃ B : Subgroup (rootNormalizer c),
      B.IsCComponent ∧ B.Normal ∧ IsQuasisimple (B ⧸ pCore 2 B) ∧
      secondary c < B.map (rootNormalizer c).subtype ∧
      B.map (rootNormalizer c).subtype ≤ Subgroup.centralizer (root c : Set G) ∧
      U c < rootCoreLayer c ∧
      rootCoreLayer c ≤ (B.map (rootNormalizer c).subtype).pCoreIn 2 ∧
      (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c ∧
      (frattini (rootCoreLayer c)).map (rootCoreLayer c).subtype ≤ root c ∧
      ⁅rootCoreLayer c,rootCoreLayer c⁆ ≤ root c := by
  obtain ⟨d,_,hL,_⟩ := exists_msData_of_whole_caseThree D hf n hn F hdegree e hnat hdual
  exact d.exists_sourceComponent_of_line_marking hn D h hL

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
