module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.EnlargedSwapping
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.FixedKernel

/-!
# The enlarged elementary subgroup in the remaining swapping branch at the original G,T

Let A=⟨s,[U,s]⟩ and D=C_G(L). In the remaining original swapping case,
B=AD=A C_G(U) is elementary of order 64, with A∩D=1 and B∩L=A.
The original T normalizes B. The split parabolic lies in L, so its action
on D is trivial and its existing coordinates on A retain the flag point.

This extension specializes the existing source argument to the actual
`HigherRankHypothesis` and to `Structural1222At` and `Theorem12213At`.
The universal interfaces remain unchanged. Earlier Chapter 12 inputs keep
their original producers; final recognition still requires I.4.5.
Source: Aschbacher–Smith, 14.4.3–5, printed pp.1006–1008.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry DimensionFour.SplitImage
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgL : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hswap : (q.left.map F.U.subtype).map (MulAut.conj (s : G)).toMonoidHom =
      q.right.map F.U.subtype)
include d setup structural alternatives hne hZ hcard g hgL hgP hgH q hsX hs hout hswap

omit g hgL hgP hgH hsX hout in
/-- A genuine cubic whose action on the original core commutes with the swap. -/
theorem source_swapping_corrected_cubic :
    ∃ c : F.H, c ^ 3 = 1 ∧ QuotientGroup.mk' (pCore 2 F.H) c ≠ 1 ∧
      Commute (F.uAction c) (F.uAction s) := by
  let := setup.chosen.elementary
  let f := F.uAction
  let π := QuotientGroup.mk' (pCore 2 F.H)
  have hk : ((quotientAut (center F.U)).comp f).ker = pCore 2 F.H :=
    source_uhat_kernel d setup structural alternatives F hZ
  have hswap' : q.left.map (f s).toMonoidHom = q.right := by
    apply map_injective F.U.subtype_injective
    rw [map_map] at hswap ⊢
    exact hswap
  obtain ⟨k,hkK,hkn,hk3,hks⟩ := q.fixed_cubic_in_residual_quotient_of_swap f (pCore 2 F.H)
    hk (source_residual_nine d setup structural alternatives F hne hZ hcard).2 s hs hswap'
  let α := f s
  let β := f k * α * (f k)⁻¹
  have hα : α ^ 2 = 1 := by dsimp [α]; rw [←map_pow,hs,map_one]
  have hβ : β ^ 2 = 1 := by
    change (MulAut.conj (f k) α) ^ 2 = 1
    rw [←map_pow,hα,map_one]
  have hquot : quotientAut (center F.U) β = quotientAut (center F.U) α := by
    let σ := (quotientAut (center F.U)).comp f
    have he : σ (k*s*k⁻¹) = σ s := by
      rw [σ.eq_iff, hk]
      have hp : π (k*s*k⁻¹) = π s := by
        rw [map_mul,map_mul,map_inv,hks.symm.eq,mul_inv_cancel_right]
      rw [π.eq_iff,QuotientGroup.ker_mk'] at hp
      exact hp
    simpa only [σ,β,α,MonoidHom.comp_apply,map_mul,map_inv] using he
  obtain ⟨v,hv⟩ := q.swap_inner_correction α β hα hβ hswap' hquot
  let vH : F.H := ⟨v,F.U_le_H v.property⟩
  let b := vH*k
  have hvQ : vH ∈ pCore 2 F.H := by
    have hm := source_closure_le_twoCore d setup structural
      alternatives F hne v.property
    obtain ⟨w,hw,he⟩ := hm
    exact (Subtype.ext he : w=vH) ▸ hw
  have hbπ : π b = π k := by
    dsimp [b]
    rw [map_mul,show π vH=1 from (QuotientGroup.eq_one_iff _).mpr hvQ,one_mul]
  have hbcomm : Commute (f b) α := by
    apply mul_inv_eq_iff_eq_mul.mp
    have hfv : f vH = MulAut.conj v := MulEquiv.ext (fun _ => rfl)
    dsimp [b]
    rw [map_mul,hfv]
    calc
      _ = MulAut.conj v * β * (MulAut.conj v)⁻¹ := by dsimp [β]; group
      _ = α := hv
  have hb3 : b ^ 3 ∈ pCore 2 F.H := by
    apply (QuotientGroup.eq_one_iff _).mp
    change π (b^3)=1
    rw [map_pow,hbπ]
    exact hk3
  obtain ⟨n,hn⟩ := pCore_isPGroup.exists_pow_pow_eq_one (⟨b^3,hb3⟩ : pCore 2 F.H)
  have hn' : (b^3)^(2^n)=1 := congrArg Subtype.val hn
  let c := b^(4^n)
  have hc3 : c^3=1 := by
    calc
      c^3=((b^3)^(2^n))^(2^n) := by
        simp only [c,←pow_mul]
        congr 1
        rw [show 4=2*2 from rfl,mul_pow]
        ring
      _=1 := by rw [hn',one_pow]
  have hcπ : π c = π k := by
    rw [map_pow,hbπ]
    have hp : (π k)^4=π k := by rw [show 4=3+1 from rfl,pow_succ,hk3,one_mul]
    have hpower (m : ℕ) : (π k)^(4^m)=π k := by
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ,pow_mul,ih,hp]
    exact hpower n
  refine ⟨c,hc3,?_,?_⟩
  · rw [hcπ]
    exact hkn
  · change Commute (f (b^(4^n))) α
    rw [map_pow]
    exact hbcomm.pow_left _

omit hgL q hswap in
/-- The literal swapping sixteen lies inside the original block Sylow. -/
theorem source_swapping_sixteen_le_sylow_inter :
    zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆ ≤ (T : Subgroup G) ⊓ L := by
  rw [(source_involution_sylow d setup structural
    alternatives F hne hZ hcard g s hgP hgH hsX
    (congrArg Subtype.val hs) hout).1]
  exact sup_le le_sup_right (Subgroup.commutator_le_sup F.U (zpowers (s : G)))

/-- The centralizer enlargement is the direct product with the actual block kernel. -/
theorem source_swapping_enlargement_geometry :
    let A := zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆
    let D := centralizer (L : Set G)
    A ⊔ centralizer (F.U : Set G) = A ⊔ D ∧
      Disjoint L D ∧ (A ⊔ D) ⊓ L = A ∧
      IsElementaryAbelian 2 (A ⊔ D : Subgroup G) ∧
      Nat.card (A ⊔ D : Subgroup G) = 64 ∧
      (T : Subgroup G) ≤ normalizer ((A ⊔ D : Subgroup G) : Set G) := by
  let := setup.chosen.elementary
  let A := zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆
  let D := centralizer (L : Set G)
  have hAL : A ≤ L := (source_swapping_sixteen_le_sylow_inter d setup structural alternatives
    F hne hZ hcard g hgP hgH s hsX hs hout).trans inf_le_right
  obtain ⟨hW,hAe,hAc⟩ := q.elementary_sixteen_of_swap F.U (s : G)
    (congrArg Subtype.val hs) hout hswap
  let : IsElementaryAbelian 2 A := hAe
  let := source_block_centralizer_elementary d setup structural alternatives F hne hZ hcard
  have hAD : D ≤ centralizer (A : Set G) := centralizer_le hAL
  have hADn := hAD.trans (Subgroup.centralizer_le_normalizer _)
  have hZD : F.ZU ≤ A := by
    apply le_trans ?_ (show ⁅F.U,zpowers (s : G)⁆ ≤ A from le_sup_right)
    rw [hW]
    apply le_inf (map_subtype_le _) ?_
    intro z hz
    exact mem_centralizer_singleton_iff.mpr ((point_centralizer F hZ).le s.property z hz)
  have hjoin : A ⊔ centralizer (F.U : Set G) = A ⊔ D := by
    rw [source_core_centralizer_eq_center_join d setup structural alternatives F hne hZ hcard,
      ←sup_assoc,sup_eq_left.mpr hZD]
  have hdis : Disjoint L D := by
    apply disjoint_def.mpr
    intro x hxL hxD
    have hxV : x ∈ V :=
      (source_block_core d setup structural alternatives
        F hne hZ hcard).1.ge ((setup).centralizer_L.le
          ⟨hxL,centralizer_le setup.chosen.le_component hxD⟩)
    exact disjoint_def.mp (source_block_centralizer_disjoint_closure d setup
      structural alternatives F hne hZ hcard) (le_conjugateSpanBy V F.H hxV) hxD
  have hinf : (A ⊔ D) ⊓ L = A := by
    apply le_antisymm _ (le_inf le_sup_left hAL)
    intro x hx
    have hx' : x ∈ (A : Set G) * (D : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left A D hADn]
      exact hx.1
    obtain ⟨a,ha,b,hb,he⟩ := hx'
    have hbL : b ∈ L := by
      have hh := L.mul_mem (L.inv_mem (hAL ha)) hx.2
      rw [←he,inv_mul_cancel_left] at hh
      exact hh
    have hb1 := disjoint_def.mp hdis hbL hb
    have hax : a = x := by simpa only [hb1,mul_one] using he
    exact hax ▸ ha
  have h36 := source_quotient_card_thirty_six_of_swapping d setup structural alternatives
    F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap
  have hDn := source_block_centralizer_ne_bot_of_swapping d setup structural alternatives
    F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap
  refine ⟨hjoin,hdis,hinf,IsElementaryAbelian.sup_of_le_centralizer hAD,?_,?_⟩
  · rw [card_sup_of_disjoint_of_normalizes A D (hdis.mono_left hAL) hADn,hAc,
      source_block_centralizer_card_four d setup structural alternatives F hne hZ hcard h36 hDn]
  · exact (le_inf (source_swapping_thompson d setup structural alternatives F hne hZ hcard
        g hgP hgH q s hsX hs hout hswap).2
      (((setup).sylow_normalizes_at structural).trans
        (normalizer_le_normalizer_centralizer L))).trans (normalizer_inf_normalizer_le_normalizer_sup A D)


/-- Commutation of the two actions on U suffices to normalize the enlarged
sixteen; the cubic may move the original sixteen through the central kernel. -/
theorem source_swapping_cubic_normalizes_enlargement
    (c : F.H) (hcs : Commute (F.uAction c) (F.uAction s)) :
    (c : G) ∈ normalizer
      (((zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆) ⊔
        centralizer (L : Set G) : Subgroup G) : Set G) := by
  let A := zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆
  let C := centralizer (F.U : Set G)
  let B := A ⊔ C
  have hjoin := (source_swapping_enlargement_geometry d setup structural alternatives
    F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap).1
  rw [←hjoin]
  change (c : G) ∈ normalizer (B : Set G)
  have hCN : F.H ≤ normalizer (C : Set G) := (le_normalizer_conjugateSpanBy V F.H).trans
    (normalizer_le_normalizer_centralizer F.U)
  have hcC : C.map (MulAut.conj (c : G)).toMonoidHom = C :=
    mem_normalizer_iff_map_conj_eq.mp (hCN c.property)
  have hW := (q.elementary_sixteen_of_swap F.U (s : G)
    (congrArg Subtype.val hs) hout hswap).1
  have hcW : (⁅F.U,zpowers (s : G)⁆).map (MulAut.conj (c : G)).toMonoidHom ≤
      ⁅F.U,zpowers (s : G)⁆ := by
    rw [hW]
    rintro _ ⟨u,hu,rfl⟩
    let v : F.U := ⟨u,hu.1⟩
    have hsv : F.uAction s v = v := by
      apply Subtype.ext
      change (s : G)*u*(s : G)⁻¹=u
      rw [←mem_centralizer_singleton_iff.mp hu.2,mul_inv_cancel_right]
    have hsimage : F.uAction s (F.uAction c v) = F.uAction c v := by
      rw [←MulAut.mul_apply,←hcs.eq,MulAut.mul_apply,hsv]
    refine ⟨(F.uAction c v).property,mem_centralizer_singleton_iff.mpr ?_⟩
    have he := congrArg Subtype.val hsimage
    change (s : G)*((c : G)*u*(c : G)⁻¹)*(s : G)⁻¹ =
      (c : G)*u*(c : G)⁻¹ at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hshift : (c : G)*(s : G)*(c : G)⁻¹*(s : G)⁻¹ ∈ C := by
    have he : F.uAction (c*s*c⁻¹*s⁻¹) = 1 := by
      rw [map_mul,map_mul,map_mul,map_inv,map_inv,hcs.eq]
      group
    intro u hu
    have hu' := congrArg Subtype.val (DFunLike.congr_fun he (⟨u,hu⟩ : F.U))
    change ((c : G)*(s : G)*(c : G)⁻¹*(s : G)⁻¹)*u*
      ((c : G)*(s : G)*(c : G)⁻¹*(s : G)⁻¹)⁻¹ = u at hu'
    exact (mul_inv_eq_iff_eq_mul.mp hu').symm
  rw [mem_normalizer_iff_map_conj_eq]
  apply eq_of_le_of_card_ge
  · change (A ⊔ C).map (MulAut.conj (c : G)).toMonoidHom ≤ B
    rw [Subgroup.map_sup,hcC]
    apply sup_le _ le_sup_right
    change (zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆).map _ ≤ B
    rw [Subgroup.map_sup,MonoidHom.map_zpowers]
    apply sup_le _ (hcW.trans (le_sup_right.trans le_sup_left))
    apply zpowers_le.mpr
    change (c : G)*(s : G)*(c : G)⁻¹ ∈ B
    have hh := B.mul_mem (mem_sup_right hshift)
      (mem_sup_left (mem_sup_left (mem_zpowers (s : G))))
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
  · rw [card_map_of_injective (MulAut.conj (c : G)).injective]


/-- The enlarged subgroup has a cubic normalizer escaping both marked factors.
All three subgroups are the original ambient ones. -/
theorem source_swapping_enlarged_cubic :
    let A := zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆
    let D := centralizer (L : Set G)
    ∃ c : F.H, c ^ 3 = 1 ∧ QuotientGroup.mk' (pCore 2 F.H) c ≠ 1 ∧
      c ∈ pResidual 2 F.H ∧ Commute (F.uAction c) (F.uAction s) ∧
      (c : G) ∈ normalizer ((A ⊔ D : Subgroup G) : Set G) ∧
      (c : G) ∉ normalizer (A : Set G) ∧ (c : G) ∉ normalizer (D : Set G) := by
  let A := zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆
  let D := centralizer (L : Set G)
  obtain ⟨c,hc3,hcQ,hcs⟩ := source_swapping_corrected_cubic d setup structural alternatives
    F hne hZ hcard q s hs hswap
  have hcB := source_swapping_cubic_normalizes_enlargement d setup structural alternatives
    F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap c hcs
  have hcA : (c : G) ∉ normalizer (A : Set G) := by
    intro hn
    have hcT : (c : G) ∈ (T : Subgroup G) :=
      (source_swapping_normalizer_eq_sylow d setup structural alternatives F hne hZ hcard
        g hgL hgP hgH q s hsX hs hout hswap) ▸ ⟨c.property,hn⟩
    have ho := T.isPGroup'.orderOf_coprime (by decide : Nat.Coprime 2 3)
      (⟨c,hcT⟩ : T)
    have hd : orderOf (⟨c,hcT⟩ : T) ∣ 3 := orderOf_dvd_of_pow_eq_one
      (show (⟨c,hcT⟩ : T)^3=1 from Subtype.ext (congrArg (fun x : F.H => (x : G)) hc3))
    have he : c=1 := Subtype.ext (congrArg (fun x : T => (x : G))
      (orderOf_eq_one_iff.mp (ho.eq_one_of_dvd hd)))
    exact hcQ (by rw [he,map_one])
  refine ⟨c,hc3,hcQ,mem_pResidual_of_orderOf_coprime
    ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hc3)),hcs,hcB,hcA,?_⟩
  intro hcD
  have hnD := source_block_centralizer_ne_bot_of_swapping d setup structural alternatives
    F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap
  have hcL : (c : G) ∈ normalizer (L : Set G) :=
    (source_block_centralizer_normalizer_of_ne_bot d setup structural alternatives
      F hne hZ hcard hnD) ▸ hcD
  have hh : (c : G) ∈ normalizer (((A ⊔ D) ⊓ L : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hcB,hcL⟩
  have hinf := (source_swapping_enlargement_geometry d setup structural alternatives
    F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap).2.2.1
  change (A ⊔ D) ⊓ L = A at hinf
  rw [hinf] at hh
  exact hcA hh

omit d setup structural alternatives hne hZ hcard g hgL hgP hgH q hsX hs hout hswap in
private def transportEnlargedParabolic {B C P S R : Subgroup G}
    (hBC : B=C) (hSR : S=R) (z : B) (w : C) (hz : (z : G)=(w : G))
    (p : ParabolicGenerators C P R w) : ParabolicGenerators B P S z := by
  subst C R
  have he : z=w := Subtype.ext hz
  subst w
  exact p

omit hgL in
/-- Retain the parabolic inside L, so that its action on the actual D is trivial. -/
theorem source_swapping_parabolic_inside :
    ∃ (P : Subgroup G) (z : (zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆ : Subgroup G)),
      P ≤ L ∧ F.Vi 1 = zpowers (z : G) ∧
      Nonempty (ParabolicGenerators (zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆)
        P ((T : Subgroup G) ⊓ L) z) := by
  let := setup.chosen.elementary
  have hV := (source_block_core d setup structural
    alternatives F hne hZ hcard).1
  let : (V.subgroupOf L).Normal := by
    rw [hV]
    change (Subgroup.comap L.subtype ((pCore 2 L).map L.subtype)).Normal
    rw [comap_map_eq_self_of_injective L.subtype_injective]
    infer_instance
  obtain ⟨data,i,hi,hiL,hTL⟩ := source_aligned_natural_data_of_swapping d setup
    structural alternatives F hne hZ hcard g hgP hgH q s hsX hs hout hswap
  obtain ⟨z,hz,hpoint⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hzTL : z ∈ DimensionFour.SplitImage.SplitParabolic.Natural.TL data i := by
    rw [hTL]
    have hzV : z ∈ V := F.le_seed 1 (hpoint ▸ mem_zpowers z)
    exact ⟨setup.chosen.le_sylow hzV,(hV.le.trans (L.pCoreIn_le 2)) hzV⟩
  have hzC : ∀ t ∈ DimensionFour.SplitImage.SplitParabolic.Natural.TL data i, z*t=t*z := by
    intro t ht
    rw [hTL] at ht
    have htH : t ∈ F.H := F.invariant 1 ht.1
    rw [F.H_eq_centralizer (by decide) z hpoint] at htH
    exact htH z (Set.mem_singleton z)
  let w := DimensionFour.SplitImage.SplitParabolic.Natural.sourcePoint data i hi z hzTL hz hzC
  have hA : Stellmacher.elementaryAbelianMaxJ
      (DimensionFour.SplitImage.SplitParabolic.Natural.TL data i) =
        zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆ := by
    rw [hTL]
    exact (source_swapping_thompson d setup structural alternatives F hne hZ hcard
      g hgP hgH q s hsX hs hout hswap).1
  let zA : (zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆ : Subgroup G) := ⟨z,hA ▸ w.property⟩
  refine ⟨DimensionFour.SplitImage.SplitParabolic.Natural.secondParabolic data i,zA,?_,hpoint,?_⟩
  · exact (map_le_range i _).trans hiL.le
  · exact ⟨transportEnlargedParabolic hA.symm hTL.symm zA w rfl
    (DimensionFour.SplitImage.SplitParabolic.Natural.sourceGenerators data i hi z hzTL hz hzC)⟩


/-- Enlarging A by D preserves the literal common four-group induced by U
and T∩L. The cubic acts on this same quotient subgroup. -/
theorem source_swapping_enlarged_common_image :
    let B := (zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆) ⊔ centralizer (L : Set G)
    quotientImage B ((T : Subgroup G) ⊓ L) = quotientImage B F.U ∧
      Nat.card (quotientImage B F.U) = 4 ∧
      quotientImage B F.H ≤ normalizer (quotientImage B F.U : Set (NormalizerAction.Star B)) := by
  let A := zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆
  let D := centralizer (L : Set G)
  let B := A ⊔ D
  obtain ⟨_,_,_,hBe,_,hTN⟩ := source_swapping_enlargement_geometry d setup structural alternatives
    F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap
  let : IsElementaryAbelian 2 B := hBe
  have hUT := source_closure_le_sylow d setup structural alternatives F
  have hUN : F.U ≤ normalizer (B : Set G) := hUT.trans hTN
  have hUL := (source_block_core d setup structural alternatives
    F hne hZ hcard).2
  have hTL := (source_involution_sylow d setup structural
    alternatives F hne hZ hcard g s hgP hgH hsX (congrArg Subtype.val hs) hout).1
  have hker : F.U ⊓ centralizer (B : Set G) = F.U ⊓ centralizer (A : Set G) := by
    apply le_antisymm (inf_le_inf_left _ (centralizer_le (show A ≤ B from le_sup_left)))
    intro u hu
    refine ⟨hu.1,le_centralizer_iff.mp (show B ≤ centralizer (F.U ⊓ centralizer (A : Set G) : Set G) from ?_) hu⟩
    apply sup_le (le_centralizer_iff.mp inf_le_right)
    exact (centralizer_le hUL).trans (centralizer_le inf_le_left)
  have hc := QuaternionResidual.card_image_mul_centralizer B F.U hUN
  rw [hker,(QuaternionResidual.core_centralizer_of_swap F.U A q (s : G)
    (congrArg Subtype.val hs) hout hswap rfl).2,hcard] at hc
  have he : quotientImage B ((T : Subgroup G) ⊓ L) = quotientImage B F.U := by
    apply le_antisymm
    · apply (QuaternionResidual.image_mono B (show (T : Subgroup G) ⊓ L ≤ F.U ⊔ B from ?_)).trans
        (QuaternionResidual.image_sup_self B F.U hUN).le
      rw [hTL]
      exact sup_le le_sup_left (le_sup_left.trans (le_sup_left.trans le_sup_right))
    · exact QuaternionResidual.image_mono B (le_inf hUT hUL)
  refine ⟨he,by change Nat.card (QuaternionResidual.image B F.U) = 4; omega,?_⟩
  exact QuaternionResidual.image_le_normalizer B F.U F.H hUN
    (le_normalizer_conjugateSpanBy V F.H)

/-- The corrected cubic acts nontrivially on the common four-group.
Three subgroups would otherwise make it fix the quaternion diagonal pointwise,
forcing its action on U to have both order dividing two and order dividing three. -/
theorem source_swapping_enlarged_cubic_noncentral
    (c : F.H) (hc3 : c ^ 3 = 1) (hcQ : QuotientGroup.mk' (pCore 2 F.H) c ≠ 1)
    (hcs : Commute (F.uAction c) (F.uAction s))
    (hcB : (c : G) ∈ normalizer
      (((zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆) ⊔ centralizer (L : Set G) : Subgroup G) : Set G)) :
    let B := (zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆) ⊔ centralizer (L : Set G)
    NormalizerAction.quotient B ⟨c,hcB⟩ ∉
      centralizer (quotientImage B F.U : Set (NormalizerAction.Star B)) := by
  let A := zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆
  let B := A ⊔ centralizer (L : Set G)
  let W := ⁅F.U,zpowers (s : G)⁆
  let n : normalizer (B : Set G) := ⟨c,hcB⟩
  let b := NormalizerAction.quotient B n
  change b ∉ centralizer (quotientImage B F.U : Set (NormalizerAction.Star B))
  intro hb
  have hTN := (source_swapping_enlargement_geometry d setup structural alternatives
    F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap).2.2.2.2.2
  have hUN : F.U ≤ normalizer (B : Set G) :=
    (source_closure_le_sylow d setup structural alternatives F).trans hTN
  have hCUC : ⁅zpowers (c : G),F.U⁆ ≤ centralizer (B : Set G) := by
    apply commutator_le.mpr
    intro x hx u hu
    obtain ⟨m,rfl⟩ := mem_zpowers_iff.mp hx
    let uN : normalizer (B : Set G) := ⟨u,hUN hu⟩
    have huim : NormalizerAction.quotient B uN ∈ quotientImage B F.U := ⟨uN,hu,rfl⟩
    have hbu : Commute b (NormalizerAction.quotient B uN) := (hb _ huim).symm
    have he : NormalizerAction.quotient B ⁅n^m,uN⁆ = 1 := by
      rw [map_commutatorElement,map_zpow]
      exact (hbu.zpow_left m).commutator_eq
    exact (NormalizerAction.quotient_eq_one_iff B ⁅n^m,uN⁆).mp he
  have hSCU : ⁅zpowers (s : G),zpowers (c : G)⁆ ≤ centralizer (F.U : Set G) := by
    apply commutator_le.mpr
    intro x hx y hy
    obtain ⟨m,rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨k,rfl⟩ := mem_zpowers_iff.mp hy
    have he : F.uAction ⁅s^m,c^k⁆ = 1 := by
      rw [map_commutatorElement,map_zpow,map_zpow]
      exact (hcs.symm.zpow_zpow m k).commutator_eq
    intro u hu
    have hh := congrArg Subtype.val (DFunLike.congr_fun he (⟨u,hu⟩ : F.U))
    change ⁅(s : G)^m,(c : G)^k⁆ * u * ⁅(s : G)^m,(c : G)^k⁆⁻¹ = u at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hWc : ⁅W,zpowers (c : G)⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · exact commutator_eq_bot_iff_le_centralizer.mpr hSCU
    · apply commutator_eq_bot_iff_le_centralizer.mpr
      exact hCUC.trans (centralizer_le (show zpowers (s : G) ≤ B from
        le_sup_left.trans le_sup_left))
  have hWC := commutator_eq_bot_iff_le_centralizer.mp hWc
  obtain ⟨hW,hAe,_⟩ := q.elementary_sixteen_of_swap F.U (s : G)
    (congrArg Subtype.val hs) hout hswap
  have hWU : W ≤ F.U := by
    change ⁅F.U,zpowers (s : G)⁆ ≤ F.U
    rw [hW]
    exact inf_le_left
  let : IsElementaryAbelian 2 A := hAe
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (show W ≤ A from le_sup_right)
  let E := W.subgroupOf F.U
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hWU
  have hWc8 : Nat.card W = 8 := by
    have hh := QuaternionResidual.core_centralizer_of_swap F.U A q (s : G)
      (congrArg Subtype.val hs) hout hswap rfl
    simpa only [hh.1] using hh.2
  have hE : Nat.card E = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWU).toEquiv]
    exact hWc8
  have hfix : ∀ u ∈ E, F.uAction c u = u := by
    intro u hu
    apply Subtype.ext
    change (c : G)*(u : G)*(c : G)⁻¹=u
    exact mul_inv_eq_iff_eq_mul.mpr (hWC hu c (mem_zpowers (c : G)))
  have h2 := q.square_eq_one_of_fixes_eight E hE (F.uAction c) hfix
  have h3 : (F.uAction c)^3=1 := by rw [←map_pow,hc3,map_one]
  have hone : F.uAction c=1 := by
    rw [pow_succ,h2,one_mul] at h3
    exact h3
  apply hcQ
  apply (QuotientGroup.eq_one_iff _).mpr
  rw [←source_uhat_kernel d setup structural alternatives F hZ]
  change quotientAut (center F.U) (F.uAction c)=1
  rw [hone,map_one]


/-- Assemble the actual parabolic and rotating cubic on the original enlarged
subgroup, retaining the original normalizer quotient and flag marking. -/
theorem source_enlarged_swapping_case : EnlargedSwappingCase L F := by
  let A := zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆
  let D := centralizer (L : Set G)
  let B := A ⊔ D
  obtain ⟨_,hdis,hinf,hBe,hBcard,hTN⟩ := source_swapping_enlargement_geometry d setup structural alternatives
    F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap
  have hAL : A ≤ L := (source_swapping_sixteen_le_sylow_inter d setup structural alternatives
    F hne hZ hcard g hgP hgH s hsX hs hout).trans inf_le_right
  have hDn := source_block_centralizer_ne_bot_of_swapping d setup structural alternatives
    F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap
  have h36 := source_quotient_card_thirty_six_of_swapping d setup structural alternatives
    F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap
  have hDcard := source_block_centralizer_card_four d setup structural alternatives F hne hZ hcard h36 hDn
  have hHcard := (source_kernel_four_local_orders d setup structural alternatives F hne hZ hcard h36 hDn).2.2.1
  obtain ⟨hcommon,hfour,hHN⟩ := source_swapping_enlarged_common_image d setup structural alternatives
    F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap
  obtain ⟨P,z,hPL,hpoint,⟨parabolic⟩⟩ := source_swapping_parabolic_inside d setup structural alternatives
    F hne hZ hcard g hgP hgH q s hsX hs hout hswap
  have hactorC : P ⊔ ((T : Subgroup G) ⊓ L) ≤ centralizer (D : Set G) :=
    (sup_le hPL inf_le_right).trans (le_centralizer_iff.mp le_rfl)
  have hactorN : P ⊔ ((T : Subgroup G) ⊓ L) ≤ normalizer (B : Set G) :=
    (le_inf parabolic.normalizes (hactorC.trans (Subgroup.centralizer_le_normalizer _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup A D)
  obtain ⟨c,hc3,hcQ,_,hcs,hcB,hcA,hcD⟩ := source_swapping_enlarged_cubic d setup structural alternatives
    F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap
  refine ⟨s,hBe,hBcard,hDcard,hdis.mono_left hAL,hinf,hTN,hcommon,hfour,hHcard,
    P,z,hPL,hpoint,⟨parabolic⟩,hactorN,hactorC,c,hcB,hc3,hcQ,hcs,hcA,hcD,?_,?_⟩
  · rw [hcommon]
    exact hHN ⟨⟨c,hcB⟩,c.property,rfl⟩
  · rw [hcommon]
    exact source_swapping_enlarged_cubic_noncentral d setup structural alternatives F hne hZ hcard
      g hgL hgP hgH q s hsX hs hout hswap c hc3 hcQ hcs hcB

omit g hgL hgP hgH q hsX hs hout hswap in
/-- The original selected-counterexample assumptions now reduce the local-data
constructor to the specified enlarged swapping action, with no extra input. -/
theorem source_localData_or_enlarged_swapping :
    Nonempty (SourceLocalData L F) ∨ EnlargedSwappingCase L F := by
  obtain ⟨q⟩ := source_quaternion d setup structural
    alternatives F hne hZ hcard
  obtain ⟨g,s,hgL,hgP,hgH,hsX,hs,hout,_hTL⟩ := source_involution_sylow_exists
    d setup structural alternatives F hne hZ hcard
  rcases source_involution_action_dichotomy d setup structural alternatives F hne hZ hcard
    g hgP hgH q s hsX hs hout with hc2 | hswap
  · exact Or.inl (source_localData_of_c2 d setup structural alternatives F hne hZ hcard
      g hgP hgH q s hsX hs hout hc2)
  · exact Or.inr (source_enlarged_swapping_case d setup structural alternatives F hne hZ hcard
      g hgL hgP hgH q s hsX hs hout hswap)

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
