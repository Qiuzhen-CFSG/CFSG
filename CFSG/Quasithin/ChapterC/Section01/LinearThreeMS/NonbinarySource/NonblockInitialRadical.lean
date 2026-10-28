module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockInitialFixed
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.FixedCubic

/-!
# Original nonblock radical inequalities on the initial moved layer

The original source module W lies properly in the initial moved group A.
When A is natural, its proved line marking identifies [A,L] with W and
puts a plane of order |F|² inside W. If the original radical R were the
two-core of the centralizer of an eligible Sylow's central omega, the
source normalizer control and the initial-layer centralizer formula would
make the corresponding point local preserve W. A proper invariant additive
subgroup of the natural point local has order at most |F|, a contradiction.

The doubled initial branch already has the intrinsic radical inequality.
Combining both branches therefore supplies every original eligible Sylow
inequality from the configuration and its full SL₃ quotient, including
field four, with no whole-center or upper-section premise. This adapts the
whole-center argument of NonblockMSRadicalInequality to the literal initial
layer; the whole center is never substituted for that layer without proof.

The final original-source application also conjugates the actual S∩L
Sylow inside the line local. One common quotient marking retains the
natural/doubled initial alternatives, the line and upper-unipotent images,
C_S(K)=C_Q(K)=1, and all radical inequalities. The Sylow transport adapts
NonblockMSMarking and does not require MSData or its unproved whole sections.
The universal C.1.34 classification and whole-section recognition remain open.
Source: Aschbacher--Smith C.1.34, pp.136--137; C.2.8--10, pp.147--148;
and original 4.3.8--10 and the choices after 4.3.10, pp.616--617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.InitialRadical
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
    (hm : HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3)) :
    ∃ f : movedCoreOmega c ≃* Multiplicative (Fin 3 → F),
      ∀ (k : K c) (u v : movedCoreOmega c), (v : G) = k * (u : G) * (k : G)⁻¹ →
        (f v).toAdd = (linearThreeActor e k).val.mulVec (f u).toAdd := by
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,f,hf⟩ := hm
  let := hn
  exact ⟨QuotientGroup.quotientBot.symm.trans f,hf⟩

omit [Finite G] in
private theorem initial_normalized : K c ≤ normalizer (movedCoreOmega c : Set G) :=
  normalizer_commutator_ge_right _ _

omit [Finite G] in
private theorem fullModule_moved : ⁅W c,L⁆ = W c := by
  have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
    le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
  exact (show W c = ⁅W c,L⁆ from by simpa only [hs] using c.c28.module_commutator).symm

private theorem fullModule_lt_initial (hf : generalizedFitting c.K = pCore 2 c.K) :
    W c < movedCoreOmega c := by
  apply lt_of_le_of_ne (InitialCenter.fullModule_le_initial hf)
  intro he
  have hn : K c ≤ normalizer (W c : Set G) := by
    rw [he]
    exact initial_normalized
  exact c.component_outside ((le_inf (map_subtype_le _) hn).trans
    (c.c28.module_normalizer.trans inf_le_right))

private abbrev fullImage {F : Type*} [Field F]
    (f : movedCoreOmega c ≃* Multiplicative (Fin 3 → F)) : AddSubgroup (Fin 3 → F) :=
  (((W c).subgroupOf (movedCoreOmega c)).map f.toMonoidHom).toAddSubgroup'

private theorem fullImage_card {F : Type*} [Field F]
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (f : movedCoreOmega c ≃* Multiplicative (Fin 3 → F)) :
    Nat.card (fullImage f) = Nat.card (W c) := by
  change Nat.card (((W c).subgroupOf (movedCoreOmega c)).map f.toMonoidHom) = _
  rw [card_map_of_injective f.injective,
    Nat.card_congr (subgroupOfEquivOfLe (InitialCenter.fullModule_le_initial hf)).toEquiv]

private theorem fullImage_ne_bot {F : Type*} [Field F]
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (f : movedCoreOmega c ≃* Multiplicative (Fin 3 → F)) : fullImage f ≠ ⊥ := by
  intro hz
  apply c.c28.module_nontrivial
  apply bot_unique
  intro w hw
  let u : movedCoreOmega c := ⟨w,InitialCenter.fullModule_le_initial hf hw⟩
  have hh : (f u).toAdd ∈ fullImage f := ⟨u,hw,rfl⟩
  rw [hz] at hh
  exact mem_bot.mpr (congrArg Subtype.val
    (f.map_eq_one_iff.mp (Multiplicative.toAdd.injective hh)))

private theorem fullImage_ne_top {F : Type*} [Field F]
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (f : movedCoreOmega c ≃* Multiplicative (Fin 3 → F)) : fullImage f ≠ ⊤ := by
  intro ht
  apply (fullModule_lt_initial hf).not_ge
  intro u hu
  have hh : (f ⟨u,hu⟩).toAdd ∈ fullImage f := ht ▸ trivial
  obtain ⟨v,hv,hvu⟩ := hh
  have he : v = ⟨u,hu⟩ := f.injective hvu
  change (v : G) ∈ W c at hv
  simpa only [he] using hv

omit [Finite G] in
private theorem fullImage_invariant {F : Type*} [Field F]
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (f : movedCoreOmega c ≃* Multiplicative (Fin 3 → F))
    (he : ∀ (k : K c) (u v : movedCoreOmega c), (v : G) = k * (u : G) * (k : G)⁻¹ →
      (f v).toAdd = (linearThreeActor e k).val.mulVec (f u).toAdd)
    (B : Subgroup G) (_hBK : B ≤ K c) (hBW : B ≤ normalizer (W c : Set G)) :
    ∀ g ∈ (B.subgroupOf (K c)).map (linearThreeActor e),
      ∀ v ∈ fullImage f, g.val.mulVec v ∈ fullImage f := by
  rintro _ ⟨k,hk,rfl⟩ _ ⟨u,hu,rfl⟩
  let v : movedCoreOmega c := (movedCoreOmega c).normalizerMonoidHom
    ⟨k,initial_normalized k.property⟩ u
  have hv : (v : G) = k * (u : G) * (k : G)⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
  refine ⟨v,?_,Multiplicative.toAdd.injective (he k u v hv)⟩
  change (v : G) ∈ W c
  rw [hv]
  exact (mem_normalizer_iff.mp (hBW hk) u).mp hu

private theorem initial_fullModule_commutator {F : Type} [Field F]
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3))
    (hL : (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F) :
    ⁅movedCoreOmega c,L⁆ = W c := by
  obtain ⟨f,he⟩ := coordinates_of_natural e hm
  have hnL : L ≤ normalizer (W c : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    rw [commutator_comm,fullModule_moved]
  have hinv := fullImage_invariant e f he L c.le_component hnL
  have hmoved : ∀ A : AddSubgroup (Fin 3 → F),
      (∀ g ∈ (L.subgroupOf (K c)).map (linearThreeActor e),
        ∀ v ∈ fullImage f, g.val.mulVec v - v ∈ A) → fullImage f ≤ A := by
    intro A hA
    let B := (A.toSubgroup.comap f.toMonoidHom).map (movedCoreOmega c).subtype
    have hc : ⁅L,W c⁆ ≤ B := by
      apply commutator_le.mpr
      intro l hl w hw
      let k : K c := ⟨l,c.le_component hl⟩
      let u : movedCoreOmega c := ⟨w,InitialCenter.fullModule_le_initial hf hw⟩
      let v : movedCoreOmega c := (movedCoreOmega c).normalizerMonoidHom
        ⟨k,initial_normalized k.property⟩ u
      have hv : (v : G) = k * (u : G) * (k : G)⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
      refine ⟨v*u⁻¹,?_,rfl⟩
      change (f (v*u⁻¹)).toAdd ∈ A
      rw [map_mul,map_inv,toAdd_mul,toAdd_inv,
        he k u v hv,←sub_eq_add_neg]
      exact hA _ (mem_map_of_mem _ hl) _ ⟨u,hw,rfl⟩
    rw [commutator_comm,fullModule_moved] at hc
    rintro a ⟨u,hu,rfl⟩
    obtain ⟨v,hv,hvu⟩ := hc hu
    have hvu : v = u := Subtype.ext hvu
    subst v
    exact hv
  apply le_antisymm
  · rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl u hu
    let k : K c := ⟨l,c.le_component hl⟩
    let x : movedCoreOmega c := ⟨u,hu⟩
    let y : movedCoreOmega c := (movedCoreOmega c).normalizerMonoidHom
      ⟨k,initial_normalized k.property⟩ x
    have hy : (y : G) = k * (x : G) * (k : G)⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
    have hd : (f (y*x⁻¹)).toAdd ∈ fullImage f := by
      rw [map_mul,map_inv,toAdd_mul,toAdd_inv,
        he k x y hy,←sub_eq_add_neg]
      exact Representation.SL3ParabolicNatural.displacement_mem_of_moved _ (Or.inr hL) _
        (fullImage_ne_bot hf f) hinv hmoved _ (mem_map_of_mem _ hl) _
    obtain ⟨z,hz,hzy⟩ := hd
    have hzy : z = y*x⁻¹ := f.injective hzy
    have hz' : ((y*x⁻¹ : movedCoreOmega c) : G) ∈ W c := hzy ▸ hz
    simpa only [Subgroup.coe_mul,Subgroup.coe_inv,hy,commutatorElement_def] using hz'
  · rw [←fullModule_moved (c := c)]
    exact commutator_mono (InitialCenter.fullModule_le_initial hf) le_rfl

private theorem natural_fullModule_large {F : Type} [Field F] [Finite F]
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3))
    (hL : (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F)
    (hfull : ⁅movedCoreOmega c,L⁆ = W c) : Nat.card F < Nat.card (W c) := by
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
    (hm : HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3))
    (hfull : ⁅movedCoreOmega c,L⁆ = W c) (hlarge : Nat.card F < Nat.card (W c))
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
  let B := K c ⊓ centralizer ((movedCoreOmega c ⊓ centralizer (P : Set G) : Subgroup G) : Set G)
  have hBC : B ≤ C := by
    have hh := ms_initial_sylow_centralizer c D hf n hn hF e P hP hRP
    change C = B ⊔ c.I.pCoreIn 2 at hh
    exact le_sup_left.trans_eq hh.symm
  have hBW : B ≤ normalizer (W c : Set G) := by
    rw [←hfull]
    intro b hb
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (initial_normalized hb.1),
      mem_normalizer_iff_map_conj_eq.mp (hCL (hBC hb))]
  obtain ⟨f,he⟩ := coordinates_of_natural e hm
  have hpoint : pointLocalSL F ≤ (B.subgroupOf (K c)).map (linearThreeActor e) := by
    intro g hg
    obtain ⟨k,hk⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _)) g
    change linearThreeActor e k = g at hk
    refine ⟨k,⟨k.property,?_⟩,hk⟩
    apply mem_centralizer_iff.mpr
    intro z hz
    let u : movedCoreOmega c := ⟨z,hz.1⟩
    have hfix : ∀ a : unipotentSL F, a.val.val.mulVec (f u).toAdd = (f u).toAdd := by
      intro a
      obtain ⟨p,hp,hpa⟩ := hmark.ge a.property
      have hc := mem_centralizer_iff.mp hz.2 p hp.1
      have hh := he p u u (by
        change z = (p : G)*z*(p : G)⁻¹
        rw [hc,mul_inv_cancel_right])
      rw [hpa] at hh
      exact hh.symm
    let v : movedCoreOmega c := (movedCoreOmega c).normalizerMonoidHom
      ⟨k,initial_normalized k.property⟩ u
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

/-- The natural initial layer and its line marking suffice for every original
Sylow radical inequality, including when the whole core is nonabelian. -/
theorem natural_initial_radical_inequality {F : Type} [Field F] [Finite F] [CharP F 2]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3))
    (hL : (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F)
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P) :
    MSNotCentralizerCore (K c) (c.I.pCoreIn 2) P := by
  have hfull := initial_fullModule_commutator hf e hm hL
  have hlarge := natural_fullModule_large hf e hm hL hfull
  obtain ⟨A,hA⟩ := component_sylow_image e P hP
  obtain ⟨g,hg,_⟩ := Matrix.PSL3.CartanActions.BorelQuotient.sylowSL_normalizer_conjugate
    F (by omega : 0 < n) hF A
  let e' := e.trans (MulAut.conj g⁻¹)
  have hm' : HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e')
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

/-- Every eligible Sylow has the source radical inequality. The initial
natural/doubled alternatives and their original line marking are proved
internally; no whole-center or upper-section model is a premise. -/
theorem source_radical_inequalities {F : Type} [Field F] [Finite F] [CharP F 2]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P) :
    MSNotCentralizerCore (K c) (c.I.pCoreIn 2) P := by
  obtain ⟨mark,hm,hline,_,_⟩ := InitialFixed.exists_initial_line_and_fixed D hf hn hF e
  rcases hm with hm | hm
  · exact natural_initial_radical_inequality D hf n hn hF mark hm hline P hP hRP
  · apply ChapterC.LinearThreeMS.NonbinarySource.RadicalInitial.notCentralizerCore_of_initial_doubled
      (msPair_of_quotient c D hf n (by omega) hF e) hn mark _ hP hRP
    simpa only [ms_initialMoved_eq] using hm

omit [Finite G] in
private theorem section_conjugate {B A F : Type*} [Group B] [AddCommGroup A]
    [Field F] [Module F A] {J P C : Subgroup G} {a : J →* B}
    {rho : Representation F B A} (hm : HasSectionModel J P C a rho) (g : B) :
    HasSectionModel J P C ((MulAut.conj g).toMonoidHom.comp a) rho := by
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (rho.asGroupHom g)
  apply hm.transport e.toAddEquiv
  intro x v
  change rho g (rho (a x) v) = rho (g * a x * g⁻¹) (rho g v)
  simp only [← Module.End.mul_apply,← map_mul]
  simp

private theorem original_sylow (D : Chapter12.Section02.ChosenModule T L V) :
    ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = S c ⊓ L := by
  let N := normalizer (L : Set G)
  let A := L.subgroupOf N
  let e : A ≃* L := subgroupOfEquivOfLe L.le_normalizer
  let : A.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨P,hP⟩ := (T.subtype D.sylow_normalizes_component).exists_sylow_map_eq_inf_of_normal A
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((P : Subgroup A).map e.toMonoidHom).map L.subtype = _
  have hf : L.subtype.comp e.toMonoidHom = N.subtype.comp A.subtype := rfl
  rw [map_map,hf,←map_map,hP]
  rw [Subgroup.map_inf _ _ _ N.subtype_injective,map_subgroupOf_eq_of_le L.le_normalizer]
  change ((T : Subgroup G).subgroupOf N).map N.subtype ⊓ L = _
  rw [map_subgroupOf_eq_of_le D.sylow_normalizes_component]
  change (T : Subgroup G) ⊓ L = ((T : Subgroup G) ⊓ c.H) ⊓ L
  rw [inf_assoc,inf_eq_right.mpr (c.le_component.trans (map_subtype_le _))]

private theorem unipotent_le_line (F : Type*) [Field F] :
    unipotentSL F ≤ lineLocalSL F := inf_le_right

private theorem line_image_sylow {F : Type} [Field F] [Finite F]
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (D : Chapter12.Section02.ChosenModule T L V)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F) :
    ∃ P : Sylow 2 (lineLocalSL F),
      (P : Subgroup (lineLocalSL F)).map (lineLocalSL F).subtype =
        ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor e) := by
  let f := (linearThreeActor e).comp (inclusion c.le_component)
  have hfr : f.range = lineLocalSL F := by
    rw [MonoidHom.range_comp]
    have hi : (inclusion c.le_component).range = L.subgroupOf (K c) := by
      ext x
      constructor
      · rintro ⟨y,rfl⟩; exact y.property
      · intro hx; exact ⟨⟨x,hx⟩,rfl⟩
    rw [hi,hL]
  let f' : L →* lineLocalSL F := f.codRestrict _ (fun x => hfr.le ⟨x,rfl⟩)
  have hs : Function.Surjective f' := by
    intro y
    obtain ⟨x,hx⟩ := hfr.ge y.property
    exact ⟨x,Subtype.ext hx⟩
  obtain ⟨P,hP⟩ := original_sylow (c := c) D
  refine ⟨P.mapSurjective (f := f') hs,?_⟩
  change ((P : Subgroup L).map f').map (lineLocalSL F).subtype = _
  rw [map_map]
  change (P : Subgroup L).map f = _
  rw [←map_map]
  congr 1
  apply map_injective (K c).subtype_injective
  rw [map_map,map_subgroupOf_eq_of_le (inf_le_right.trans c.le_component)]
  exact hP

/-- Align the original Sylow and line images by one inner change of marking. -/
private theorem initial_simultaneous_marking {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (D : Chapter12.Section02.ChosenModule T L V)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F) :
    ∃ g : lineLocalSL F,
      let e' := e.trans (MulAut.conj g.val)
      (L.subgroupOf (K c)).map (linearThreeActor e') = lineLocalSL F ∧
      ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor e') = unipotentSL F := by
  obtain ⟨P,hP⟩ := line_image_sylow e D hL
  let P₀ := (Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow F
    (show 0 < n by omega) hF).subtype (unipotent_le_line F)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (lineLocalSL F) P P₀
  have hh := congrArg (fun Q : Sylow 2 (lineLocalSL F) =>
    (Q : Subgroup (lineLocalSL F)).map (lineLocalSL F).subtype) hg
  have he : (((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor e)).map
      (MulAut.conj g.val).toMonoidHom = unipotentSL F := by
    change ((P : Subgroup (lineLocalSL F)).map
      (MulAut.conj g).toMonoidHom).map (lineLocalSL F).subtype = _ at hh
    have hf : (lineLocalSL F).subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj g.val).toMonoidHom.comp (lineLocalSL F).subtype := rfl
    rw [map_map,hf,←map_map,hP] at hh
    change _ = ((unipotentSL F).subgroupOf (lineLocalSL F)).map
      (lineLocalSL F).subtype at hh
    rwa [map_subgroupOf_eq_of_le (unipotent_le_line F)] at hh
  refine ⟨g,?_,?_⟩
  · change (L.subgroupOf (K c)).map
      ((MulAut.conj g.val).toMonoidHom.comp (linearThreeActor e)) = _
    rw [←map_map,hL]
    exact mem_normalizer_iff_map_conj_eq.mp ((lineLocalSL F).le_normalizer g.property)
  · change ((S c ⊓ L).subgroupOf (K c)).map
      ((MulAut.conj g.val).toMonoidHom.comp (linearThreeActor e)) = _
    rwa [←map_map]

/-- The original configuration supplies both initial alternatives, the common
line/Sylow marking, both fixed-factor exclusions, and every eligible radical
inequality. The whole core and its upper sections are not identified here. -/
theorem exists_marked_initial_source {F : Type} [Field F] [Finite F] [CharP F 2]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      (HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor mark)
        (Representation.specialLinearNatural (k := F) 3) ∨
       HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor mark)
        ((Representation.specialLinearNatural (k := F) 3).prod
          (Representation.specialLinearNatural (k := F) 3))) ∧
      (L.subgroupOf (K c)).map (linearThreeActor mark) = lineLocalSL F ∧
      ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor mark) = unipotentSL F ∧
      S c ⊓ centralizer (K c : Set G) = ⊥ ∧
      Q c ⊓ centralizer (K c : Set G) = ⊥ ∧
      ∀ P : Subgroup G, Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2) →
        c.I.pCoreIn 2 ≤ P → MSNotCentralizerCore (K c) (c.I.pCoreIn 2) P := by
  obtain ⟨mark,hm,hline,hS,hQ⟩ := InitialFixed.exists_initial_line_and_fixed D hf hn hF e
  obtain ⟨g,hline',hSL⟩ := initial_simultaneous_marking hn hF mark D hline
  refine ⟨mark.trans (MulAut.conj g.val),?_,hline',hSL,hS,hQ,?_⟩
  · rcases hm with hm | hm
    · left
      exact section_conjugate (B := SL(3,F)) (A := Fin 3 → F) (F := F)
        (J := K c) (P := movedCoreOmega c) (C := ⊥) (a := linearThreeActor mark)
        (rho := Representation.specialLinearNatural (k := F) 3) hm g.val
    · right
      exact section_conjugate (B := SL(3,F)) (A := (Fin 3 → F) × (Fin 3 → F)) (F := F)
        (J := K c) (P := movedCoreOmega c) (C := ⊥) (a := linearThreeActor mark)
        (rho := (Representation.specialLinearNatural (k := F) 3).prod
          (Representation.specialLinearNatural (k := F) 3)) hm g.val
  · exact fun P hP hRP => source_radical_inequalities D hf hn hF e P hP hRP

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.InitialRadical
