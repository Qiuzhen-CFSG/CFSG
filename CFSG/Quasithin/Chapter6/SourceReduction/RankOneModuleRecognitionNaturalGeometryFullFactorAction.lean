module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryResidualNormalization
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The original two-residual acting on full transvection factors

A full marked factor is centerless, and every nontrivial normal quotient
of its S₃, L₃(2), or S₅ model is a two-group. Projection onto its direct
product coordinates therefore makes any automorphic image either equal
to it or centralize it. Three distinct images would contribute three
independent cubic ranks. Thus in three-rank at most two, the orbit of a
factor has at most two members and every two-perfect actor fixes it.

Apply this to the original conjugation action of I on P/O₂(P), transported
through the same faithful W/Z_S action map. Its two-residual normalizes
each literal full factor preimage in P and its image in N_G(Z_S)/O₂.
The escape application retains all earlier action and covering equations,
product coordinates, and cubic residual normalization on this witness.

This discharges the O²(I) full-factor action assertion in Aschbacher–Smith
6.1.19, printed p.675, using the marked factors from G.6.4. Cubic action
on the full factors, the parabolic/amalgam contradiction, initial 6.1.4–5,
and the remaining escape geometry stay with the natural-reduction owner
qt-d-1222-rankone-recognition-natural. Unconditional 6.1.27 is not asserted.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterG.Section06
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace NaturalFullFactor
private theorem quotient_two_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B)
    (h : ∀ (N : Subgroup B) [N.Normal], N ≠ ⊥ → IsPGroup 2 (B ⧸ N))
    (N : Subgroup A) [N.Normal] (hn : N ≠ ⊥) : IsPGroup 2 (A ⧸ N) := by
  let D := N.map e.toMonoidHom
  let : D.Normal := Normal.map inferInstance _ e.surjective
  have hd : D ≠ ⊥ := by
    intro hd
    exact hn ((N.map_eq_bot_iff_of_injective e.injective).mp hd)
  exact (h D hd).of_equiv (QuotientGroup.congr N D e rfl).symm

private theorem small_quotient_two {B V : Type*} [Group B] [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) B V}
    {K : Subgroup B} {U : Submodule (ZMod 2) V} (h : SmallFactorModel ρ K U)
    (N : Subgroup K) [N.Normal] (hn : N ≠ ⊥) : IsPGroup 2 (K ⧸ N) := by
  rcases h with ⟨e,_,_⟩ | ⟨e,_,_⟩ | ⟨e,_,_⟩
  · exact quotient_two_transport
      (e.trans ((BinaryLinear.OuterCyclic.slEquivLinear 2).symm.trans
        (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three)))
      symmetric_three_normal_quotient_two N hn
  · let E := e.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 3)).symm
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
      Atlas.psl_simple_high_rank 3 (by decide)
    let : IsSimpleGroup K := E.isSimpleGroup
    exact simple_normal_quotient_two N hn
  · exact quotient_two_transport e (symmetric_normal_quotient_two (by decide : 5 ≤ 5)) N hn

private theorem small_three_dvd {B V : Type*} [Group B] [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) B V}
    {K : Subgroup B} {U : Submodule (ZMod 2) V} (h : SmallFactorModel ρ K U) :
    3 ∣ Nat.card K := by
  rcases h with ⟨e,_,_⟩ | ⟨e,_,_⟩ | ⟨e,_,_⟩
  · let E := e.trans ((BinaryLinear.OuterCyclic.slEquivLinear 2).symm.trans
        (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))
    rw [Nat.card_congr E.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  · let E := e.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
    rw [Nat.card_congr E.toEquiv,Matrix.PSL3Two.card_SL]
    decide
  · rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide

private theorem normal_coordinate {H A B : Type*} [Group H] [Group A] [Group B]
    (hH : ∀ (N : Subgroup H) [N.Normal], N ≠ ⊥ → IsPGroup 2 (H ⧸ N))
    (hz : center H = ⊥) (hA : pCore 2 A = ⊥) (hB : pCore 2 B = ⊥)
    (f : H →* A × B) [f.range.Normal] :
    (∀ h, (f h).2 = 1) ∨ (∀ h, (f h).1 = 1) := by
  let p := (MonoidHom.fst A B).comp f
  let q := (MonoidHom.snd A B).comp f
  let : p.range.Normal := by
    rw [MonoidHom.range_comp]
    exact (inferInstance : f.range.Normal).map _ (fun a => ⟨(a,1),rfl⟩)
  let : q.range.Normal := by
    rw [MonoidHom.range_comp]
    exact (inferInstance : f.range.Normal).map _ (fun b => ⟨(1,b),rfl⟩)
  rcases normal_hom_injective_or_trivial hH hA p with hp | hp
  · left
    have hc (h : H) : (f h).2 ∈ center B := by
      apply mem_center_iff.mpr
      intro b
      obtain ⟨k,hk⟩ := (inferInstance : f.range.Normal).conj_mem (f h) ⟨h,rfl⟩ (1,b)
      have he : k = h := hp (by
        change (f k).1 = (f h).1
        simpa using congrArg Prod.fst hk)
      subst k
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Prod.snd hk).symm
    rcases normal_hom_injective_or_trivial hH hB q with hq | hq
    · intro h
      have hh : h ∈ center H := mem_center_iff.mpr fun k => hq (by
        rw [map_mul,map_mul]
        exact mem_center_iff.mp (hc h) (q k))
      rw [show h = 1 from hz.le hh,map_one]
      rfl
    · intro h
      exact congrArg (fun q : H →* B => q h) hq
  · right
    intro h
    exact congrArg (fun p : H →* A => p h) hp

universe v
variable {B V : Type v} [Group B] [Finite B] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) B V}

omit [Finite B] in
private theorem center_bot {t : B} (d : TransvectionFactorModel ρ t) :
    center (normalClosure ({t} : Set B)) = ⊥ := by
  apply (eq_bot_iff_forall _).mpr
  intro x hx
  apply Subtype.ext
  exact d.disjoint.le_bot ⟨x.property,mem_centralizer_iff.mpr fun y hy =>
    congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)⟩

omit [Finite B] in
private theorem map_center_bot {K : Subgroup B} (hz : center K = ⊥) (e : MulAut B) :
    center (K.map e.toMonoidHom) = ⊥ := by
  let E := e.subgroupMap K
  apply (eq_bot_iff_forall _).mpr
  intro x hx
  have hh : E.symm x ∈ center K := mem_center_iff.mpr fun y => E.injective (by
    rw [map_mul,map_mul,E.apply_symm_apply]
    exact mem_center_iff.mp hx (E y))
  exact E.symm.injective ((hz.le hh).trans E.symm.map_one.symm)

private theorem image_eq_or_centralizes {t : B} (d : TransvectionFactorModel ρ t)
    {U : Submodule (ZMod 2) V} (hm : SmallFactorModel ρ (normalClosure ({t} : Set B)) U)
    (hcore : pCore 2 B = ⊥) (e : MulAut B) :
    (normalClosure ({t} : Set B)).map e.toMonoidHom = normalClosure ({t} : Set B) ∨
    (normalClosure ({t} : Set B)).map e.toMonoidHom ≤
      centralizer (normalClosure ({t} : Set B) : Set B) := by
  let K := normalClosure ({t} : Set B)
  let C := centralizer (K : Set B)
  let H := K.map e.toMonoidHom
  let E := e.subgroupMap K
  let : H.Normal := Normal.map inferInstance _ e.surjective
  let f := d.productEquiv.symm.toMonoidHom.comp H.subtype
  let : f.range.Normal := by
    rw [MonoidHom.range_comp,range_subtype]
    exact Normal.map inferInstance _ d.productEquiv.symm.surjective
  have hc (X : Subgroup B) [X.Normal] : pCore 2 X = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : X.Normal).isSubnormal,hcore]
    exact (MonoidHom.ker_eq_bot_iff X.subtype).mpr X.subtype_injective
  rcases normal_coordinate (quotient_two_transport E.symm (small_quotient_two hm))
    (map_center_bot (center_bot d) e) (hc K) (hc C) f with hh | hh
  · left
    apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective e.injective])
    intro x hx
    have he := d.productEquiv.apply_symm_apply x
    change d.productEquiv ((f ⟨x,hx⟩).1,(f ⟨x,hx⟩).2) = x at he
    have hhx := hh (⟨x,hx⟩ : H)
    change (f (⟨x,hx⟩ : H)).2 = 1 at hhx
    rw [hhx,d.productEquiv_apply] at he
    simp only [OneMemClass.coe_one,mul_one] at he
    exact he ▸ (f ⟨x,hx⟩).1.property
  · right
    intro x hx
    have he := d.productEquiv.apply_symm_apply x
    change d.productEquiv ((f ⟨x,hx⟩).1,(f ⟨x,hx⟩).2) = x at he
    have hhx := hh (⟨x,hx⟩ : H)
    change (f (⟨x,hx⟩ : H)).1 = 1 at hhx
    rw [hhx,d.productEquiv_apply] at he
    simp only [OneMemClass.coe_one,one_mul] at he
    exact he ▸ (f ⟨x,hx⟩).2.property

private theorem images_eq_or_centralizes {t : B} (d : TransvectionFactorModel ρ t)
    {U : Submodule (ZMod 2) V} (hm : SmallFactorModel ρ (normalClosure ({t} : Set B)) U)
    (hcore : pCore 2 B = ⊥) (e f : MulAut B) :
    (normalClosure ({t} : Set B)).map e.toMonoidHom =
      (normalClosure ({t} : Set B)).map f.toMonoidHom ∨
    (normalClosure ({t} : Set B)).map e.toMonoidHom ≤
      centralizer ((normalClosure ({t} : Set B)).map f.toMonoidHom : Set B) := by
  let K := normalClosure ({t} : Set B)
  have hcomp : (K.map (e.trans f.symm).toMonoidHom).map f.toMonoidHom =
      K.map e.toMonoidHom := by
    rw [map_map]
    congr 1
    ext x
    exact f.apply_symm_apply (e x)
  rcases image_eq_or_centralizes d hm hcore (e.trans f.symm) with he | hc
  · left
    exact hcomp.symm.trans (congrArg (map f.toMonoidHom) he)
  · right
    rw [←hcomp]
    rintro _ ⟨x,hx,rfl⟩ y ⟨z,hz,rfl⟩
    change f z * f x = f x * f z
    rw [←map_mul,←map_mul,hc hx z hz]

omit [Finite B] in
private theorem disjoint_of_center_bot {K H : Subgroup B}
    (hz : center K = ⊥) (hc : H ≤ centralizer (K : Set B)) : Disjoint K H := by
  apply disjoint_iff_inf_le.mpr
  rintro x ⟨hx,hxh⟩
  have hh : (⟨x,hx⟩ : K) ∈ center K := mem_center_iff.mpr fun y =>
    Subtype.ext (hc hxh y y.property)
  exact congrArg Subtype.val (hz.le hh)

private theorem three_images_impossible {t : B} (d : TransvectionFactorModel ρ t)
    {U : Submodule (ZMod 2) V} (hm : SmallFactorModel ρ (normalClosure ({t} : Set B)) U)
    (hcore : pCore 2 B = ⊥) (hr : primeRank 3 B ≤ 2)
    (e f g : MulAut B)
    (hef : (normalClosure ({t} : Set B)).map e.toMonoidHom ≠
      (normalClosure ({t} : Set B)).map f.toMonoidHom)
    (heg : (normalClosure ({t} : Set B)).map e.toMonoidHom ≠
      (normalClosure ({t} : Set B)).map g.toMonoidHom)
    (hfg : (normalClosure ({t} : Set B)).map f.toMonoidHom ≠
      (normalClosure ({t} : Set B)).map g.toMonoidHom) : False := by
  let K := normalClosure ({t} : Set B)
  let E := K.map e.toMonoidHom
  let F := K.map f.toMonoidHom
  let J := K.map g.toMonoidHom
  have hef' : E ≤ centralizer (F : Set B) :=
    (images_eq_or_centralizes d hm hcore e f).resolve_left hef
  have heg' : E ≤ centralizer (J : Set B) :=
    (images_eq_or_centralizes d hm hcore e g).resolve_left heg
  have hfg' : F ≤ centralizer (J : Set B) :=
    (images_eq_or_centralizes d hm hcore f g).resolve_left hfg
  have hEF : Disjoint E F := disjoint_of_center_bot (map_center_bot (center_bot d) e)
    (le_centralizer_iff.mp hef')
  have hEJ : Disjoint (E ⊔ F) J :=
    (disjoint_of_center_bot (map_center_bot (center_bot d) g) (sup_le heg' hfg')).symm
  have hlow (a : MulAut B) : 1 ≤ primeRank 3 (K.map a.toMonoidHom) := by
    have hd : 3 ∣ Nat.card (K.map a.toMonoidHom) := by
      rw [card_map_of_injective a.injective]
      exact small_three_dvd hm
    exact Nat.one_le_iff_ne_zero.mpr (fun hz =>
      PrimeRank.eq_zero_iff_not_dvd_card.mp hz hd)
  have hh := (primeRank_subgroup_le 3 ((E ⊔ F) ⊔ J : Subgroup B)).trans hr
  rw [primeRank_sup_eq_add_of_disjoint_commuting _ _ hEJ (sup_le heg' hfg'),
    primeRank_sup_eq_add_of_disjoint_commuting _ _ hEF hef'] at hh
  have he : 1 ≤ primeRank 3 E := hlow e
  have hf : 1 ≤ primeRank 3 F := hlow f
  have hg : 1 ≤ primeRank 3 J := hlow g
  omega

/-- The original two-residual fixes every full marked factor under any
actual automorphism action in three-rank at most two. -/
theorem residual_fixes_factor {I : Type*} [Group I] [Finite I]
    (α : I →* MulAut B) (product : SmallTransvectionProductModel ρ)
    (hcore : pCore 2 B = ⊥) (hr : primeRank 3 B ≤ 2)
    (K : Subgroup B) (hK : K ∈ product.factors) :
    ∀ x ∈ pResidual 2 I, K.map (α x).toMonoidHom = K := by
  classical
  obtain ⟨t,ht,rfl,⟨d⟩⟩ := product.marked K hK
  let K := normalClosure ({t} : Set B)
  obtain ⟨U,hm⟩ := product.small K hK
  let : MulAction I (Subgroup B) := MulAction.compHom (Subgroup B) α
  let S := MulAction.stabilizer I K
  have hindex : S.index ≤ 2 := by
    rw [show S = MulAction.stabilizer I K from rfl,MulAction.index_stabilizer]
    by_cases hh : ∀ x : I, K.map (α x).toMonoidHom = K
    · have hs : MulAction.orbit I K ⊆ {K} := by
        rintro _ ⟨x,rfl⟩
        exact hh x
      exact (Set.ncard_le_ncard hs).trans (by simp)
    · push Not at hh
      obtain ⟨x,hx⟩ := hh
      have hs : MulAction.orbit I K ⊆ {K,K.map (α x).toMonoidHom} := by
        rintro _ ⟨y,rfl⟩
        change K.map (α y).toMonoidHom ∈ _
        by_cases hy : K.map (α y).toMonoidHom = K
        · exact Set.mem_insert_iff.mpr (Or.inl hy)
        by_cases hyx : K.map (α y).toMonoidHom = K.map (α x).toMonoidHom
        · exact Set.mem_insert_iff.mpr (Or.inr hyx)
        exfalso
        apply three_images_impossible d hm hcore hr (α y) (α x) (MulEquiv.refl B) hyx
        · change K.map (α y).toMonoidHom ≠ K.map (MonoidHom.id B)
          simpa only [map_id] using hy
        · change K.map (α x).toMonoidHom ≠ K.map (MonoidHom.id B)
          simpa only [map_id] using hx
      exact (Set.ncard_le_ncard hs).trans_eq (Set.ncard_pair hx.symm)
  have hres : pResidual 2 I ≤ S := by
    by_cases hs : S = ⊤
    · rw [hs]; exact le_top
    have hi : S.index = 2 := by have := S.one_lt_index_of_ne_top hs; omega
    let : S.Normal := normal_of_index_eq_two hi
    apply (pResidual_le_iff_isPGroup_quotient 2 S).mpr
    exact IsPGroup.of_card (n := 1) (by simpa only [←index_eq_card,pow_one] using hi)
  intro x hx
  exact hres hx

/-- Transport the residual action through the original covering and ambient
quotient maps. The subgroup normalized is the full factor preimage. -/
theorem residual_normalizes_full_preimages
    {G : Type*} [Group G] [Finite G]
    (I P N : Subgroup G) (hPN : P ≤ N) (hIN : I ≤ N)
    (hIP : I ≤ normalizer (P : Set G))
    (φ : (P ⧸ pCore 2 P) →* B) (hφ : Function.Bijective φ)
    (j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N))
    (he : ∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
      QuotientGroup.mk' (pCore 2 N) (inclusion hPN p))
    (product : SmallTransvectionProductModel ρ)
    (hcore : pCore 2 B = ⊥) (hr : primeRank 3 B ≤ 2) :
    ∀ K ∈ product.factors,
      ((pResidual 2 I).map (inclusion hIN)).map (QuotientGroup.mk' (pCore 2 N)) ≤
        normalizer ((K.comap φ).map j : Set (N ⧸ pCore 2 N)) ∧
      (pResidual 2 I).map I.subtype ≤
        normalizer ((((K.comap φ).comap (QuotientGroup.mk' (pCore 2 P))).map
          P.subtype) : Set G) := by
  let α₀ := P.normalizerMonoidHom.comp (inclusion hIP)
  let α := (quotientAut (pCore 2 P)).comp α₀
  let e := MulEquiv.ofBijective φ hφ
  let β := (MulAut.congr e).toMonoidHom.comp α
  let q := QuotientGroup.mk' (pCore 2 N)
  have heq (i : I) (a : P ⧸ pCore 2 P) :
      j (α i a) = q (inclusion hIN i) * j a * (q (inclusion hIN i))⁻¹ := by
    obtain ⟨p,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 P) a
    change j (quotientAut (pCore 2 P) (α₀ i) (QuotientGroup.mk' (pCore 2 P) p)) = _
    rw [quotientAut_apply_mk,he,he,←map_inv,←map_mul,←map_mul]
    congr 1
  intro K hK
  have hstable (i : I) (hi : i ∈ pResidual 2 I) (b : P ⧸ pCore 2 P)
      (hb : b ∈ K.comap φ) : α i b ∈ K.comap φ := by
    have hfix := residual_fixes_factor β product hcore hr K hK i hi
    have hm := mem_map_of_mem (β i).toMonoidHom hb
    rw [hfix] at hm
    change e (α i (e.symm (e b))) ∈ K at hm
    rwa [e.symm_apply_apply] at hm
  constructor
  · rintro _ ⟨y,⟨i,hi,rfl⟩,rfl⟩
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge ?_ (Nat.card_congr
      ((MulAut.conj (q (inclusion hIN i))).subgroupMap ((K.comap φ).map j)).toEquiv).le
    rintro _ ⟨a,⟨b,hb,rfl⟩,rfl⟩
    exact ⟨α i b,hstable i hi b hb,heq i b⟩
  · rintro _ ⟨i,hi,rfl⟩
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge ?_ (Nat.card_congr
      ((MulAut.conj (i : G)).subgroupMap (((K.comap φ).comap
        (QuotientGroup.mk' (pCore 2 P))).map P.subtype)).toEquiv).le
    rintro _ ⟨a,⟨b,hb,rfl⟩,rfl⟩
    refine ⟨α₀ i b,?_,rfl⟩
    have hh := hstable i hi (QuotientGroup.mk' (pCore 2 P) b) hb
    change quotientAut (pCore 2 P) (α₀ i) (QuotientGroup.mk' (pCore 2 P) b) ∈ K.comap φ at hh
    rwa [quotientAut_apply_mk] at hh

end NaturalFullFactor
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Classical
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe v
open CFSG.Quasithin.ChapterE
variable {G : Type v} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
namespace NaturalEscapeGraph.OddConfiguration
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d

/-- The original two-residual normalizes each full factor, both before and
after the ambient two-core quotient. Cubic residual normalization and all
marked actions and product coordinates retain this same original witness. -/
theorem exists_ambient_full_factor_action
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let N := Escape.H (T : Subgroup G) L R
      let Z := ZS (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧
      ∃ (hPI : P ≤ I) (hPN : P ≤ N) (hIN : I ≤ N)
        (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hZ : (Z.subgroupOf W).Normal),
      let := hZ
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
      ∃ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        let := hX
        IsElementaryAbelian 2 ((E.subgroupOf I).map σ) ∧
        1 < Nat.card ((E.subgroupOf I).map σ) ∧
        Nat.card ((E.subgroupOf I).map σ) ≤ 4 ∧
        let g := σ.comp (inclusion hPI)
        ∃ (φ : (P ⧸ pCore 2 P) →* g.range)
          (j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N)),
          Function.Bijective φ ∧ φ.ker ≤ center (P ⧸ pCore 2 P) ∧
          Function.Injective j ∧ j.range.IsSubnormal ∧
          (∀ p, φ (QuotientGroup.mk' (pCore 2 P) p) = g.rangeRestrict p) ∧
          (∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
            QuotientGroup.mk' (pCore 2 N) (inclusion hPN p)) ∧
          pCore 2 g.range = ⊥ ∧ g.ker = pCore 2 P ∧
          closure {x : P ⧸ pCore 2 P | x ^ 2 = 1} = ⊤ ∧
          let θ := Representation.ofElementaryAbelianAction
            (A := g.range) (G := W ⧸ Z.subgroupOf W) (p := 2)
          ∃ product : SmallTransvectionProductModel θ,
            (∀ K ∈ product.factors, FactorResidualLift φ j
              ((I.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))) K ∧
              ∀ c : N ⧸ pCore 2 N, c^3=1 →
                c ∈ Subgroup.normalizer ((((pResidual 2 (K.comap φ)).map
                  (K.comap φ).subtype).map j) : Set (N ⧸ pCore 2 N))) ∧
            (∀ K ∈ product.factors,
              ((pResidual 2 I).map (inclusion hIN)).map (QuotientGroup.mk' (pCore 2 N)) ≤
                Subgroup.normalizer ((K.comap φ).map j : Set (N ⧸ pCore 2 N)) ∧
              (pResidual 2 I).map I.subtype ≤ Subgroup.normalizer
                ((((K.comap φ).comap (QuotientGroup.mk' (pCore 2 P))).map P.subtype) : Set G)) ∧
            ∃ e : (∀ K : {K // K ∈ product.factors}, K.val) ≃* (P ⧸ pCore 2 P),
              (∀ x, φ (e x) = product.productEquiv x) ∧
              (∀ K : {K // K ∈ product.factors}, ∀ a : P ⧸ pCore 2 P,
                a ∈ K.val.comap φ ↔ ∃ x : K.val,
                  e (Function.update 1 K x) = a) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hgen,product,hres,e,he,hcoords⟩ :=
    d.exists_ambient_cubic_residual_product h hnat hE hs hNS hab
  let I := Escape.I (T : Subgroup G) L R
  let N := Escape.H (T : Subgroup G) L R
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let P := conjugateSpanBy E I
  have hIN : I ≤ N := Subgroup.centralizer_le_normalizer _
  have hsq : IsSQTK KnownSimple.IsKnownSimple N := h.simpleQTKE.twoLocal_sqtk
    ⟨ZS (T : Subgroup G) L R,h.ZS_ne_bot,T.isPGroup'.to_le h.ZS_le_T,rfl⟩
  have hrN : primeRank 3 (N ⧸ pCore 2 N) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans
      (hsq.stronglyQuasithin 3 (by decide) (by decide))
  let := hZ
  let := hX
  let g := σ.comp (inclusion hPI)
  have hr : primeRank 3 g.range ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 (j.comp (MulEquiv.ofBijective φ hφ).symm.toMonoidHom)
      (hj.comp (MulEquiv.ofBijective φ hφ).symm.injective)).trans hrN
  refine ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hgen,product,hres,?_,e,he,hcoords⟩
  exact NaturalFullFactor.residual_normalizes_full_preimages I P N hPN hIN
    (le_normalizer_conjugateSpanBy E I) φ hφ j hje product hred hr

end NaturalEscapeGraph.OddConfiguration
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
