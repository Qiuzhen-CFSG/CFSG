module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedNaturalNormalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterJankoThree
public import Theory.GroupTheory.LocalCoreFromPrimeCentralizers
public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Theory.SpecificGroups.Janko4.Model.ElementarySylowFixers
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupAction.PrimeFixedQuotient
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.CoprimeCentralizerDecomposition.CubicQuotient

/-!
# The elementary radical center and involution class of the original module

The literal component projection is faithful on the original V. Consequently
its residual centralizer on that image is contained in the residual two-core.
Let P be the radical of the full residual normalizer and E = Ω₁(Z(P)). The
previous module-normalizer result places the original order-64 image U in E.

J₄'s two-rank bound leaves at most five binary dimensions in E/U. Every action
of the perfect full SL₃(4) cover on such a small elementary group is trivial.
The cubic center splits the action on E: its fixed subgroup is disjoint from
U by transitivity and faithfulness, hence has order at most 32. It too is fixed
by the residual, whose odd centralizer makes it trivial. Coprime fixed-point
lifting through U now forces E/U = 1. Thus U is exactly Ω₁(Z(P)).

The intrinsic characteristic-two property makes P self-centralizing. The
center of any ambient Sylow containing P therefore lies in Z(P), and its
involution belongs to U. The native J₄ Sylow-center calculation identifies
that involution as 2A. Residual transitivity makes all 63 nonidentity vectors
2A, excluding the previous 2B-pure alternative. No full Sylow is asserted to
normalize P, U, or the residual.

Source applies these results to the original failure and literal Hall kernel.
The remaining exclusion of this particular 2A-pure, even-index normalizer stays
with qt-d-1222-natural-odd-kernel-normalizer. The independent ordinary C.2.8
branch stays with qt-d-1222-natural-point-fixed-summand.
Source: Aschbacher--Smith, proof of 4.4.3, printed pp.620--622; GLS3 Table5.3i
for the native involution centralizers and Sylow geometry. Imported model
certificates retain their original ATLAS attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

private theorem full_linear_four_small_action_trivial
    (F : BinaryField) (hF : F.degree = 2)
    {X E : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    [IsQuasisimple (X ⧸ pCore 2 X)] [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (e : (X ⧸ pCore 2 X) ≃* SL(3,F.Carrier)) (hE : Nat.card E ≤ 32)
    (f : X →* MulAut E) : f = 1 := by
  by_contra hne
  let q := QuotientGroup.mk' (pCore 2 X)
  have hproper : f.ker ≠ ⊤ := fun ht => hne (MonoidHom.ker_eq_top_iff.mp ht)
  have hc : f.ker.map q ≤ center (X ⧸ pCore 2 X) := by
    rcases IsQuasisimple.normal_le_center_or_eq_top (f.ker.map q) with hc | ht
    · exact hc
    · have hsup : f.ker ⊔ pCore 2 X = ⊤ := by
        have hm := congrArg (Subgroup.comap q) ht
        simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hm
      have hp := isPGroup_quotient_of_sup_eq_top f.ker (pCore 2 X) pCore_isPGroup hsup
      let : Group.IsNilpotent (X ⧸ f.ker) := hp.isNilpotent
      exact (hproper (top_unique (by simpa only [solvableResidual_eq_top] using
        solvableResidual_le_of_solvable_quotient f.ker))).elim
  let R := (X ⧸ pCore 2 X) ⧸ center (X ⧸ pCore 2 X)
  let : IsSimpleGroup R := IsQuasisimple.simple
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center (X ⧸ pCore 2 X))) (QuotientGroup.mk'_surjective _)
  let c : X →* R := (QuotientGroup.mk' (center (X ⧸ pCore 2 X))).comp q
  have hk : f.ker ≤ c.ker := by
    intro x hx
    exact (QuotientGroup.eq_one_iff (q x)).mpr (hc (mem_map_of_mem q hx))
  let g := QuotientGroup.lift f.ker c hk
  have hg : Function.Surjective g := QuotientGroup.lift_surjective_of_surjective f.ker c
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)) hk
  let a := QuotientGroup.quotientKerEquivRange f
  let er : R ≃* PSL(3,F.Carrier) := QuotientGroup.congr _ _ e (FixedElementary.map_center e)
  have hquot : Nat.card R = 20160 := by
    have hcard := card_eq_card_quotient_mul_card_subgroup (center (X ⧸ pCore 2 X))
    have hz : Nat.card (center (X ⧸ pCore 2 X)) = 3 := by
      rw [Nat.card_congr (centerCongr e).toEquiv,Atlas.ExceptionalSupport.card_sl_center]
      norm_num [F.card_eq,hF]
    rw [hz,Nat.card_congr e.toEquiv,linear_three_order,F.card_eq,hF] at hcard
    change Nat.card ((X ⧸ pCore 2 X) ⧸ center (X ⧸ pCore 2 X)) = 20160
    omega
  apply no_projective_four_section_of_frattini_le_thirtytwo
    (show Nat.card F.Carrier = 4 by rw [F.card_eq,hF]; decide) er hquot
    (IsElementaryAbelian.isPGroup 2 E)
    ((Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (frattini E))).trans hE)
    f.range (g.comp a.symm.toMonoidHom) (hg.comp a.symm.surjective)



private theorem transitive_invariant_center
    {Q : Type*} [Group Q] (X U B : Subgroup Q)
    (ht : ∀ u ∈ U, ∀ v ∈ U, u ≠ 1 → v ≠ 1 → ∃ x ∈ X, x * u * x⁻¹ = v)
    (hBU : B ≤ U) (hn : X ≤ normalizer (B : Set Q)) : B = ⊥ ∨ B = U := by
  by_cases hb : B = ⊥
  · exact Or.inl hb
  · obtain ⟨u,hu1⟩ := ne_bot_iff_exists_ne_one.mp hb
    exact Or.inr (le_antisymm hBU (by
      intro v hv
      by_cases hv1 : v = 1
      · exact hv1 ▸ B.one_mem
      · obtain ⟨x,hx,he⟩ := ht u (hBU u.property) v hv (fun h => hu1 (Subtype.ext h)) hv1
        exact he ▸ (mem_normalizer_iff.mp (hn hx) u).mp u.property))

private theorem no_small_binary_enlargement
    {Q : Type*} [Group Q] [Finite Q]
    (F : BinaryField) (hF : F.degree = 2) (X U E : Subgroup Q)
    [Group.IsPerfect X] [IsQuasisimple (X ⧸ pCore 2 X)]
    (e : (X ⧸ pCore 2 X) ≃* SL(3,F.Carrier))
    (hE : IsElementaryAbelian 2 E) (hUE : U ≤ E)
    (hU : Nat.card U = 64) (hsize : Nat.card E ≤ 2048)
    (hnE : X ≤ normalizer (E : Set Q)) (hnU : X ≤ normalizer (U : Set Q))
    (hcore : X.pCoreIn 2 ≤ centralizer (E : Set Q))
    (hfaith : X ⊓ centralizer (U : Set Q) ≤ X.pCoreIn 2)
    (ht : ∀ u ∈ U, ∀ v ∈ U, u ≠ 1 → v ≠ 1 → ∃ x ∈ X, x * u * x⁻¹ = v)
    (ho : Odd (Nat.card (centralizer (X : Set Q)))) : E = U := by
  let := hE
  let Z := centralPreimage (pCore 2 X)
  let B := Z.map X.subtype
  let C := E ⊓ centralizer (B : Set Q)
  let q := QuotientGroup.mk' (pCore 2 X)
  have hzcard : Nat.card (center (X ⧸ pCore 2 X)) = 3 := by
    rw [Nat.card_congr (centerCongr e).toEquiv,Atlas.ExceptionalSupport.card_sl_center]
    norm_num [F.card_eq,hF]
  have hZn : X ≤ normalizer (B : Set Q) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (Z.le_normalizer_map X.subtype : (normalizer (Z : Set X)).map X.subtype ≤ _)
  have hnC : X ≤ normalizer (C : Set Q) :=
    (le_inf hnE (hZn.trans (normalizer_le_normalizer_centralizer B))).trans
      inf_normalizer_le_normalizer_inf
  have hne : U ≠ ⊥ := by intro h; simp [h] at hU
  have hdis : U ⊓ C = ⊥ := by
    rcases transitive_invariant_center X U (U ⊓ C) ht inf_le_left
      ((le_inf hnU hnC).trans inf_normalizer_le_normalizer_inf) with h | h
    · exact h
    · have hBU : B ≤ centralizer (U : Set Q) :=
        le_centralizer_iff.mp (h.ge.trans inf_le_right |>.trans inf_le_right)
      have hBc : B ≤ X.pCoreIn 2 := (le_inf (map_subtype_le _) hBU).trans hfaith
      have hZc : Z ≤ pCore 2 X := by
        apply (map_le_map_iff_of_injective X.subtype_injective).mp hBc
      have hcz := map_mono (f := q) hZc
      rw [map_centralPreimage,QuotientGroup.map_mk'_self] at hcz
      have hz : center (X ⧸ pCore 2 X) = ⊥ := bot_unique hcz
      simp [hz] at hzcard
  have hCsize : Nat.card C ≤ 32 := by
    have hCE : C ≤ E := inf_le_left
    have hCU : C ≤ centralizer (U : Set Q) :=
      hCE.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (centralizer_le hUE))
    have hprod := card_sup_eq_mul_of_normalizes_of_disjoint U C
      (hCU.trans (Subgroup.centralizer_le_normalizer _)) (disjoint_iff.mpr hdis)
    have hle := card_le_of_le (sup_le hUE hCE)
    rw [hprod,hU] at hle
    omega
  have hCbot : C = ⊥ := by
    let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le (show C ≤ E from inf_le_left)
    let f := C.normalizerMonoidHom.comp (inclusion hnC)
    have hf := full_linear_four_small_action_trivial F hF e hCsize f
    have hXC : X ≤ centralizer (C : Set Q) := by
      intro x hx
      have hk : inclusion hnC ⟨x,hx⟩ ∈ C.normalizerMonoidHom.ker := by
        change f ⟨x,hx⟩ = 1
        rw [hf]
        rfl
      rwa [normalizerMonoidHom_ker] at hk
    have hcodd := ho.of_dvd_nat (card_dvd_of_le (le_centralizer_iff.mp hXC))
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 C).exists_card_eq
    apply C.eq_bot_of_card_eq
    have hn0 : n = 0 := by
      by_contra hn0
      exact (Nat.not_even_iff_odd.mpr hcodd) (even_iff_two_dvd.mpr
        (hn ▸ dvd_pow_self 2 hn0))
    simpa [hn0] using hn
  let N := U.subgroupOf E
  have hNcard : Nat.card N = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUE).toEquiv).trans hU
  have hquot : Nat.card (E ⧸ N) ≤ 32 := by
    have hc := card_eq_card_quotient_mul_card_subgroup N
    rw [hNcard] at hc
    omega
  obtain ⟨f,hf⟩ := exists_quotient_conjugation_action X E U hnE hnU
    (inferInstance : N.Normal)
  have hf1 := full_linear_four_small_action_trivial F hF e hquot f
  have hmove : ∀ x ∈ X, ∀ w ∈ E, x * w * x⁻¹ * w⁻¹ ∈ U := by
    intro x hx w hw
    have hh := hf ⟨x,hx⟩ ⟨w,hw⟩
    rw [hf1] at hh
    have hm := QuotientGroup.eq_iff_div_mem.mp hh.symm
    simpa only [mem_subgroupOf, Subgroup.coe_div, Subgroup.coe_mk, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv] using hm
  have hdiv : 3 ∣ Nat.card Z := hzcard ▸
    card_dvd_of_surjective (q.subgroupComap (center (X ⧸ pCore 2 X)))
      (q.subgroupComap_surjective_of_surjective _ (QuotientGroup.mk'_surjective _))
  obtain ⟨c,hc⟩ := exists_prime_orderOf_dvd_card' (G := Z) 3 hdiv
  have hc3 : orderOf (c : X) = 3 := (orderOf_coe c).trans hc
  have hcq : q (c : X) ≠ 1 := by
    intro hh
    have hcP : (c : X) ∈ pCore 2 X := (QuotientGroup.eq_one_iff _).mp hh
    have hoP := (pCore_isPGroup (p := 2) (G := X)).orderOf_coprime (by decide : Nat.Coprime 2 3)
      (⟨c,hcP⟩ : pCore 2 X)
    rw [orderOf_mk,hc3] at hoP
    norm_num at hoP
  have hgen : pCore 2 X ⊔ zpowers (c : X) = Z := by
    have hz : (zpowers (c : X)).map q = center (X ⧸ pCore 2 X) := by
      rw [MonoidHom.map_zpowers]
      let cq : center (X ⧸ pCore 2 X) := ⟨q c,c.property⟩
      have hh := zpowers_eq_top_of_prime_card hzcard
        (show cq ≠ 1 from fun h => hcq (congrArg Subtype.val h))
      have hm := congrArg (Subgroup.map (center (X ⧸ pCore 2 X)).subtype) hh
      simpa only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype, cq, Subgroup.subtype_apply] using hm
    have hh := congrArg (Subgroup.comap q) hz
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk',sup_comm,Z,centralPreimage] using hh
  let R := zpowers (c.val.val : Q)
  have hR3 : IsPGroup 3 R := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,orderOf_coe,hc3,pow_one])
  have hRX : R ≤ X := zpowers_le.mpr c.val.property
  have hfixed : E ⊓ centralizer (R : Set Q) = ⊥ := by
    apply bot_unique
    intro x hx
    apply hCbot.le
    refine ⟨hx.1,?_⟩
    have hbgen : X.pCoreIn 2 ⊔ R = B := by
      have hh := congrArg (Subgroup.map X.subtype) hgen
      simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,pCoreIn,R,B,Subgroup.subtype_apply] using hh
    have hcenter : B ≤ centralizer ({x} : Set Q) := by
      rw [←hbgen]
      apply sup_le
      · intro k hk
        exact mem_centralizer_singleton_iff.mpr (hcore hk x hx.1).symm
      · intro k hk
        exact mem_centralizer_singleton_iff.mpr (hx.2 k hk)
    intro b hb
    exact mem_centralizer_singleton_iff.mp (hcenter hb)
  have hcop : ¬ 3 ∣ Nat.card N := by rw [hNcard]; decide
  have hsur := centralizer_quotient_surjective_of_prime_fixed E R N hR3
    (hRX.trans hnE) hcop (by
      intro r hr w hw
      rw [map_subgroupOf_eq_of_le hUE]
      exact hmove r (hRX hr) w hw)
  apply le_antisymm ?_ hUE
  intro w hw
  obtain ⟨a,ha⟩ := hsur (QuotientGroup.mk' N ⟨w,hw⟩)
  have ha1 : a = 1 := Subtype.ext (mem_bot.mp (hfixed ▸ a.property))
  rw [ha1,map_one] at ha
  have hwN : (⟨w,hw⟩ : E) ∈ N := (QuotientGroup.eq_one_iff _).mp ha.symm
  exact hwN


open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal residual action on the original image has two-group kernel. -/
theorem moved_projected_module_centralizer
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (hf : S.field.degree = 2) (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) :
    let q := QuotientGroup.mk' (center K)
    let X := (movedComponentSubgroup A (oddActorResidual L A) K).map q
    let U := (movedComponentSubgroup A V K).map q
    X ⊓ centralizer (U : Set (K ⧸ center K)) ≤ X.pCoreIn 2 := by
  let q := QuotientGroup.mk' (center K)
  let Y := movedComponentSubgroup A (oddActorResidual L A) K
  let W := movedComponentSubgroup A V K
  let X := Y.map q
  let U := W.map q
  let C := Y ⊓ centralizer (W : Set K)
  let j : K →* G := (normalizer (A : Set G)).subtype.comp K.subtype
  have hj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  have hVF : V ≤ oddActorResidual L A :=
    (actor_cover D S hA hodd).2.2.1.trans (pCoreIn_le 2 _)
  have hVK : V ≤ K.map (normalizer (A : Set G)).subtype := hVF.trans hFK
  have hYW : Y ≤ normalizer (W : Set K) := by
    intro y hy
    apply mem_normalizer_iff.mpr
    intro w
    change (w.val.val : G) ∈ V ↔ (y.val.val : G) * w.val.val * (y.val.val : G)⁻¹ ∈ V
    exact mem_normalizer_iff.mp (D.normalizes ((oddActorResidual_le L A).trans inf_le_left hy)) _
  have hC : IsPGroup 2 C := by
    have hmap : C.map j ≤ L.pCoreIn 2 := by
      rintro _ ⟨x,hx,rfl⟩
      apply (centralizer_eq_core D S).le
      refine ⟨(oddActorResidual_le L A).trans inf_le_left hx.1,?_⟩
      intro v hv
      obtain ⟨v',hv',hv'eq⟩ := hVK hv
      have hvW : (⟨v',hv'⟩ : K) ∈ W := by
        change (v' : G) ∈ V
        change (v' : G) = v at hv'eq
        rwa [hv'eq]
      have hh := congrArg j (hx.2 ⟨v',hv'⟩ hvW)
      change (v' : G) * j x = j x * (v' : G) at hh
      change (v' : G) = v at hv'eq
      simpa only [hv'eq] using hh
    exact ((isPGroup_pCoreIn 2 L).to_le hmap).of_equiv
      (equivMapOfInjective C j hj).symm
  have hnC : Y ≤ normalizer (C : Set K) :=
    (le_inf Y.le_normalizer (hYW.trans (normalizer_le_normalizer_centralizer W))).trans
      inf_normalizer_le_normalizer_inf
  have hmapC : C.map q = X ⊓ centralizer (U : Set (K ⧸ center K)) := by
    apply le_antisymm
    · exact le_inf (map_mono inf_le_left)
        ((map_mono inf_le_right).trans (map_centralizer_le_centralizer_image _ q))
    · rintro x ⟨⟨y,hy,rfl⟩,hc⟩
      refine ⟨y,⟨hy,?_⟩,rfl⟩
      exact (centralizer_image_mem_iff_of_injective_on_subgroup q W
        (fun a b hab => moved_module_projection_injective D S hA hodd K hFK hf e
          (Subtype.ext hab)) (hYW hy)).mp hc
  change X ⊓ centralizer (U : Set (K ⧸ center K)) ≤ X.pCoreIn 2
  rw [←hmapC]
  exact le_pCoreIn_of_normalizes (hC.map q) (map_mono inf_le_left)
    ((map_mono hnC).trans (C.le_normalizer_map q))

private theorem janko_radical_selfCentralizing (P : Subgroup Janko4.Model)
    (hP : IsPRadical 2 P) : centralizer (P : Set Janko4.Model) ≤ P := by
  have hc := normalizer_core_selfCentralizing_of_prime_centralizers
    Janko4.InvolutionCentralizers.centralizer_characteristic_two P hP.isPGroup hP.1
  have hh := (inf_centralizer_pCoreIn_le_iff 2 (normalizer (P : Set Janko4.Model))).mpr hc
  change normalizer (P : Set Janko4.Model) ⊓ centralizer
    (((pCore 2 (normalizer (P : Set Janko4.Model))).map
      (normalizer (P : Set Janko4.Model)).subtype) : Set Janko4.Model) ≤
    (pCore 2 (normalizer (P : Set Janko4.Model))).map
      (normalizer (P : Set Janko4.Model)).subtype at hh
  rw [hP.2] at hh
  exact (le_inf (Subgroup.centralizer_le_normalizer _) le_rfl).trans hh

/-- The unchanged original module is the entire elementary center of the
radical of its full normalizer. -/
theorem moved_projected_module_eq_omega_center
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (hf : S.field.degree = 2) (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (ek : (K ⧸ center K) ≃* Janko4.Model) :
    let q := QuotientGroup.mk' (center K)
    let X := (movedComponentSubgroup A (oddActorResidual L A) K).map q
    let U := (movedComponentSubgroup A V K).map q
    U = omegaCenterIn ((normalizer (X : Set (K ⧸ center K))).pCoreIn 2) := by
  let q := QuotientGroup.mk' (center K)
  let X := (movedComponentSubgroup A (oddActorResidual L A) K).map q
  let U := (movedComponentSubgroup A V K).map q
  let M := normalizer (X : Set (K ⧸ center K))
  let P := M.pCoreIn 2
  let E := omegaCenterIn P
  obtain ⟨hperfect,⟨a⟩⟩ := moved_projected_cover D S hA hodd K hFK
  let := hperfect
  let := S.source.toHypothesis1221.quasisimple
  let : IsQuasisimple (X ⧸ pCore 2 X) := IsQuasisimple.of_mulEquiv a.symm
  obtain ⟨hU,hUne,_,hm⟩ := moved_projected_module D S hA hodd K hFK
  let := hU
  have hUc := moved_projected_module_central_radical D S hA hodd hu K hFK hf e ek
  have hUE : U ≤ E := by
    intro u hu
    exact (mem_omegaCenterIn_iff P u).mpr
      ⟨(hUc hu).1,(hUc hu).2,elemPow_eq_one_of_isElementaryAbelian u hu⟩
  have hnP : X ≤ normalizer (P : Set (K ⧸ center K)) :=
    X.le_normalizer.trans (M.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image M (pCore 2 M)))
  have hnE := hnP.trans (normalizer_le_normalizer_omegaCenterIn P)
  have hnU : X ≤ normalizer (U : Set (K ⧸ center K)) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    rw [commutator_comm,←hm]
  have hEc : E ≤ centralizer (P : Set (K ⧸ center K)) := by
    intro z hz
    exact ((mem_omegaCenterIn_iff P z).mp hz).2.1
  have hcore : X.pCoreIn 2 ≤ centralizer (E : Set (K ⧸ center K)) :=
    (pCoreIn_mono_of_normalizes X.le_normalizer le_rfl).trans
      (le_centralizer_iff.mp hEc)
  have hr : primeRank 2 (K ⧸ center K) ≤ 11 := by
    rw [primeRank_equiv 2 ek]
    exact Janko4.TwoRank.model_twoRank_le_eleven
  have hsize : Nat.card E ≤ 2048 :=
    (primeRank_le_iff_elementary_card_le _).mp hr E inferInstance
  exact (no_small_binary_enlargement S.field hf X U E (a.trans e) inferInstance hUE
    (moved_projected_module_card D S hA hodd K hFK hf e) hsize hnE hnU hcore
    (moved_projected_module_centralizer D S hA hodd K hFK hf e)
    (moved_projected_module_transitive D S hA hodd K hFK hf e)
    (moved_janko_residual_centralizer_odd D S hA hodd hu K hFK hf e ek)).symm

private theorem janko_sylow_center_contains_first_class (R : Sylow 2 Janko4.Model) :
    ∃ z : Janko4.Model, z ∈ centerIn (R : Subgroup Janko4.Model) ∧
      orderOf z = 2 ∧ IsConj Janko4.a z := by
  obtain ⟨T⟩ := Sylow.nonempty (p := 2)
    (G := centralizer ({Janko4.a} : Set Janko4.Model))
  obtain ⟨S,hS⟩ := Janko4.OuterReduction.OddIndex.centralizer_sylow_is_ambient T
  have hcenter : centerIn (S : Subgroup Janko4.Model) = zpowers Janko4.a := by
    rw [centerIn_eq_map_center,hS]
    exact Janko4.OuterReduction.OddIndex.centralizer_sylow_center T
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Janko4.Model S R
  let f := MulAut.conj g
  have hmap : (S : Subgroup Janko4.Model).map f.toMonoidHom = R :=
    congrArg Sylow.toSubgroup hg
  have hmem : f Janko4.a ∈ centerIn (R : Subgroup Janko4.Model) := by
    rw [←hmap,←centerIn_map_equiv,hcenter]
    exact mem_map_of_mem f.toMonoidHom (mem_zpowers _)
  exact ⟨f Janko4.a,hmem,
    (orderOf_injective f.toMonoidHom f.injective _).trans Janko4.orderOf_a,
    isConj_iff.mpr ⟨g,rfl⟩⟩

/-- The original pure order-64 image is necessarily in the first involution
class. Its radical contains the center of an ambient Sylow, without being
assumed normal in that Sylow. -/
theorem moved_janko_module_first_class
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (hf : S.field.degree = 2) (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (ek : (K ⧸ center K) ≃* Janko4.Model) :
    let q := QuotientGroup.mk' (center K)
    let U := ((movedComponentSubgroup A V K).map q).map ek.toMonoidHom
    ∀ u ∈ U, u ≠ 1 → IsConj Janko4.a u := by
  let q := QuotientGroup.mk' (center K)
  let X := (movedComponentSubgroup A (oddActorResidual L A) K).map q
  let U := (movedComponentSubgroup A V K).map q
  let P := (normalizer (X : Set (K ⧸ center K))).pCoreIn 2
  let PJ := P.map ek.toMonoidHom
  have hPJ : IsPGroup 2 PJ := (isPGroup_pCoreIn 2 _).map ek.toMonoidHom
  obtain ⟨R,hR⟩ := hPJ.exists_le_sylow
  obtain ⟨z,hz,hz2,haz⟩ := janko_sylow_center_contains_first_class R
  have hzc : z ∈ centralizer (PJ : Set Janko4.Model) := centralizer_le hR hz.2
  have hsc : centralizer (PJ : Set Janko4.Model) ≤ PJ :=
    janko_radical_selfCentralizing PJ
      ((moved_projected_radical D S hA hodd hu K hFK).1.map_equiv ek)
  obtain ⟨v,hv,hvz⟩ := hsc hzc
  change ek v = z at hvz
  have hvc : v ∈ centralizer (P : Set (K ⧸ center K)) := by
    intro p hp
    apply ek.injective
    simpa only [map_mul,hvz] using hzc (ek p) (mem_map_of_mem ek.toMonoidHom hp)
  have hv2 : v ^ 2 = 1 := by
    apply ek.injective
    rw [map_pow,map_one,hvz,←hz2,pow_orderOf_eq_one]
  have hvU : v ∈ U := by
    have hU : U = omegaCenterIn P :=
      moved_projected_module_eq_omega_center D S hA hodd hu K hFK hf e ek
    rw [hU]
    exact (mem_omegaCenterIn_iff P v).mpr ⟨hv,hvc,hv2⟩
  have hzU : z ∈ U.map ek.toMonoidHom := ⟨v,hvU,hvz⟩
  obtain ⟨_,_,ht,_⟩ := moved_janko_module_pure D S hA hodd K hFK hf e ek
  change ∀ u ∈ U.map ek.toMonoidHom, u ≠ 1 → IsConj Janko4.a u
  intro u hu' hune
  obtain ⟨x,_,he⟩ := ht z hzU u hu'
    (by intro he; simp [he] at hz2) hune
  exact haz.trans (isConj_iff.mpr ⟨x,he⟩)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
