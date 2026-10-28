module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallInnerQuotientAction

/-!
# Agreement on the original module-core span

Let U be the image of the original V intersect O₂(K) in W=O₂(K)/Φ(O₂(K)).
The span of its K-translates is an actual invariant subgroup of W. The inner
quotient implementer of each original module actor belongs to the original
Sylow centralizer of the cubic, hence lifts into O₂(L₀T) intersect K. That
lift centralizes V. Consequently the centralizer correction fixes U and all
its K-translates: the two actions agree on this actual span.

No equality of the span with W, nontriviality of the module action, or
placement of the whole Frattini image inside the quotient image is asserted.
Source: Aschbacher--Smith 10.2.4--5, printed pp.747--748.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H P I : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

/-- The image of the original module-core intersection in the same Frattini section. -/
def moduleCoreImage (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (H : Subgroup G) :
    Subgroup (CoreFrattiniSection T L H) :=
  (D.fullModule.subgroupOf ((enlargedResidual T L H).pCoreIn 2)).map (QuotientGroup.mk' _)

/-- The span of the original intersection image under the actual containing quotient. -/
def Data.moduleCoreSpan (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Subgroup (CoreFrattiniSection T L H) :=
  ⨆ x : XiQuotient (enlargedResidual T L H),
    (moduleCoreImage D H).map (h.coreQuotientFrattiniAction hn x).toMonoidHom

/-- The original module-core image is contained in its actual quotient span. -/
theorem Data.moduleCoreImage_le_span (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    moduleCoreImage D H ≤ h.moduleCoreSpan hn := by
  intro u hu
  have hh := le_iSup (fun x : XiQuotient (enlargedResidual T L H) =>
    (moduleCoreImage D H).map (h.coreQuotientFrattiniAction hn x).toMonoidHom) 1
      (mem_map_of_mem (h.coreQuotientFrattiniAction hn 1).toMonoidHom hu)
  change h.coreQuotientFrattiniAction hn 1 u ∈ h.moduleCoreSpan hn at hh
  simpa only [map_one,MulAut.one_apply] using hh

/-- The actual span is invariant under the original faithful quotient action. -/
theorem Data.moduleCoreSpan_invariant (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (x : XiQuotient (enlargedResidual T L H)) :
    (h.moduleCoreSpan hn).map (h.coreQuotientFrattiniAction hn x).toMonoidHom =
      h.moduleCoreSpan hn := by
  let b := h.coreQuotientFrattiniAction hn
  have hle (x : XiQuotient (enlargedResidual T L H)) :
      h.moduleCoreSpan hn ≤ (h.moduleCoreSpan hn).comap (b x).toMonoidHom := by
    apply iSup_le
    intro y
    rintro _ ⟨u,hu,rfl⟩
    change b x (b y u) ∈ h.moduleCoreSpan hn
    have hh : b x (b y u) = b (x*y) u := by rw [map_mul]; rfl
    rw [hh]
    exact le_iSup (fun z => (moduleCoreImage D H).map (b z).toMonoidHom) (x*y)
      (mem_map_of_mem _ hu)
  exact eq_of_le_of_card_ge (map_le_iff_le_comap.mpr (hle x)) (by
    rw [card_map_of_injective (b x).injective])

private theorem Data.quotient_center_eq_bot (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p) :
    center (XiQuotient (enlargedResidual T L H)) = ⊥ := by
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  obtain ⟨F,_,_,_,⟨eF⟩⟩ := hm
  let j := e.trans (eF.prodCongr eF)
  apply card_eq_one.mp
  rw [Nat.card_congr (centerCongr j).toEquiv,Subgroup.center_prod,
    GorensteinWalter.psl2_center_eq_bot F,bot_prod_bot,card_bot]

private theorem Data.module_actor_normalizes_quotient_sylow_image (h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (a : moduleFrattiniImage D H) :
    (a : MulAut (CoreFrattiniSection T L H)) ∈ normalizer
      (((quotientImage (enlargedResidual T L H) (T : Subgroup G)).map
        (h.coreQuotientFrattiniAction hn)) : Set _) := by
  let E := enlargement T L H
  let K := enlargedResidual T L H
  have hVT : D.fullModule ≤ (T : Subgroup G) :=
    hfull.symm ▸ D.module_le_core.trans ((join_core_le_stabilizer D).trans inf_le_left)
  have hTK : (T : Subgroup G) ⊓ K ≤ E := inf_le_right.trans h.enlargedResidual_le_enlargement
  have hnorm : D.fullModule ≤ normalizer ((T : Subgroup G) ⊓ K : Set G) :=
    (le_inf (hVT.trans (T : Subgroup G).le_normalizer)
      ((h.fullModule_le_enlargement hfull).trans (le_normalizer_conjugateSpanBy _ _))).trans
      inf_normalizer_le_normalizer_inf
  have hsub : D.fullModule.subgroupOf E ≤ normalizer (((T : Subgroup G) ⊓ K).subgroupOf E : Set E) := by
    rw [←subgroupOf_normalizer_eq hTK]
    exact subgroupOf_mono E hnorm
  rw [h.quotientImage_frattini_map hn]
  exact ((map_mono hsub).trans (le_normalizer_map (coreFrattiniAction T L H))) a.property

private theorem Data.exists_inner_implementer_in_join_core (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (a : moduleFrattiniImage D H) :
    ∃ k : enlargedResidual T L H, (k:G) ∈ (localJoin T L).pCoreIn 2 ∧
      (QuotientGroup.mk' (pCore 2 (enlargedResidual T L H)) k) ^ 2 = 1 ∧
      QuotientGroup.mk' (pCore 2 (enlargedResidual T L H)) k ∈
        centralizer (quotientImage (enlargedResidual T L H) P : Set _) ∧
      ∀ x, (a : MulAut (CoreFrattiniSection T L H)) * h.coreQuotientFrattiniAction hn x *
          (a : MulAut (CoreFrattiniSection T L H))⁻¹ =
        h.coreQuotientFrattiniAction hn (QuotientGroup.mk' _ k) *
          h.coreQuotientFrattiniAction hn x * (h.coreQuotientFrattiniAction hn (QuotientGroup.mk' _ k))⁻¹ := by
  let b := h.coreQuotientFrattiniAction hn
  let : IsElementaryAbelian 2 (moduleFrattiniImage D H) := h.moduleFrattiniImage_elementary s.full_eq_local
  obtain ⟨φ,_,hi,hmark,hfix⟩ := h.exists_faithful_inner_moduleQuotientAction f hn hs hK hp ho hm hmod hP hc
  obtain ⟨k,hk⟩ := hi ⟨a,rfl⟩
  have hconj (x) : (a : MulAut (CoreFrattiniSection T L H)) * b x *
      (a : MulAut (CoreFrattiniSection T L H))⁻¹ = b k * b x * (b k)⁻¹ := by
    change _ = h.coreQuotientFrattiniAction hn k * h.coreQuotientFrattiniAction hn x *
      (h.coreQuotientFrattiniAction hn k)⁻¹
    rw [←hmark,←hk]
    simp only [MulAut.conj_apply,map_mul,map_inv]
  have ha2 : a ^ 2 = 1 := by
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (a : MulAut (CoreFrattiniSection T L H)) a.property
  have hk2 : k ^ 2 = 1 := MulAut.conj_injective_of_center_eq_bot
    (h.quotient_center_eq_bot hn hs hK hm) (by
      rw [map_pow,hk,←map_pow,ha2,map_one,map_one])
  have hkC : k ∈ centralizer (quotientImage (enlargedResidual T L H) P : Set _) := by
    intro x hx
    have he := hfix a x hx
    rw [←hk] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  obtain ⟨S,hS⟩ := h.quotient_sylow
  have hkN : k ∈ normalizer (S : Set _) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      have haN := h.module_actor_normalizes_quotient_sylow_image s.full_eq_local hn a
      rw [←hS] at haN
      have hh := (mem_normalizer_iff.mp haN (b x)).mp (mem_map_of_mem b hx)
      rw [hconj] at hh
      obtain ⟨y,hy,he⟩ := hh
      have he' : y = k*x*k⁻¹ := h.coreQuotientFrattiniAction_injective hn (by
        simpa only [map_mul,map_inv] using he)
      change k*x*k⁻¹ ∈ (S : Subgroup _)
      exact he' ▸ hy
    · rw [card_map_of_injective (MulAut.conj k).injective]
  have hkS : k ∈ (S : Subgroup _) := by
    have htwo : IsPGroup 2 (zpowers k) := by
      let : IsElementaryAbelian 2 (zpowers k) := IsElementaryAbelian.zpowers_of_pow_eq_one hk2
      exact IsElementaryAbelian.isPGroup 2 _
    have hh : k ∈ zpowers k ⊓ normalizer (S : Set _) := ⟨mem_zpowers k,hkN⟩
    rw [htwo.inf_normalizer_sylow S] at hh
    exact hh.2
  have hkR : k ∈ quotientImage (enlargedResidual T L H) ((localJoin T L).pCoreIn 2) := by
    rw [h.collapsed_join_core_image f hs.toLocalInput hP hc,
      h.collapsed_quotient_core_centralizer hs.toLocalInput hc,←hS]
    exact ⟨hkS,hkC⟩
  obtain ⟨k₀,hk₀,rfl⟩ := hkR
  exact ⟨k₀,hk₀,hk2,hkC,hconj⟩

/-- Every original module actor agrees on the actual invariant span with
a quotient element lifted from the original join core, retaining its cubic mark. -/
theorem Data.exists_module_actor_agrees_on_core_span (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (a : moduleFrattiniImage D H) :
    ∃ k : enlargedResidual T L H, (k:G) ∈ (localJoin T L).pCoreIn 2 ∧
      (QuotientGroup.mk' (pCore 2 (enlargedResidual T L H)) k) ^ 2 = 1 ∧
      QuotientGroup.mk' (pCore 2 (enlargedResidual T L H)) k ∈
        centralizer (quotientImage (enlargedResidual T L H) P : Set _) ∧
      (∀ x, (a : MulAut (CoreFrattiniSection T L H)) * h.coreQuotientFrattiniAction hn x *
          (a : MulAut (CoreFrattiniSection T L H))⁻¹ =
        h.coreQuotientFrattiniAction hn (QuotientGroup.mk' _ k) *
          h.coreQuotientFrattiniAction hn x * (h.coreQuotientFrattiniAction hn (QuotientGroup.mk' _ k))⁻¹) ∧
      ∀ w ∈ h.moduleCoreSpan hn, (a : MulAut (CoreFrattiniSection T L H)) w =
        h.coreQuotientFrattiniAction hn (QuotientGroup.mk' _ k) w := by
  obtain ⟨k,hkR,hk2,hkP,hconj⟩ := h.exists_inner_implementer_in_join_core f hn hs hK hp ho hm hmod hP hc a
  let b := h.coreQuotientFrattiniAction hn
  let t := b (QuotientGroup.mk' _ k)
  let c := t⁻¹ * (a : MulAut (CoreFrattiniSection T L H))
  have ht (u) (hu : u ∈ moduleCoreImage D H) : t u = u := by
    obtain ⟨q,hq,rfl⟩ := hu
    dsimp only [t,b]
    rw [h.coreQuotientFrattiniAction_mk,coreFrattiniAction_mk]
    apply congrArg (QuotientGroup.mk' _)
    apply Subtype.ext
    change (k:G) * (q:G) * (k:G)⁻¹ = (q:G)
    have he := D.core_centralizes_module hkR q (s.full_eq_local ▸ hq)
    rw [←he,mul_inv_cancel_right]
  have hcU (u) (hu : u ∈ moduleCoreImage D H) : c u = u := by
    have ha := h.moduleFrattiniImage_fixes_module_image s.full_eq_local hu a
    change (a : MulAut (CoreFrattiniSection T L H)) u = u at ha
    change t.symm ((a : MulAut (CoreFrattiniSection T L H)) u) = u
    exact t.symm_apply_eq.mpr (ha.trans (ht u hu).symm)
  have hcB (x) : c * b x = b x * c := by
    calc
      c * b x = t⁻¹ * ((a : MulAut (CoreFrattiniSection T L H)) * b x *
          (a : MulAut (CoreFrattiniSection T L H))⁻¹) * (a : MulAut (CoreFrattiniSection T L H)) := by
        dsimp [c]; group
      _ = t⁻¹ * (t * b x * t⁻¹) * (a : MulAut (CoreFrattiniSection T L H)) := by rw [hconj]
      _ = b x * c := by dsimp [c]; group
  have hcM : h.moduleCoreSpan hn ≤ c.toMonoidHom.eqLocus (MonoidHom.id _) := by
    apply iSup_le
    intro x
    rintro _ ⟨u,hu,rfl⟩
    change c (b x u) = b x u
    have he := DFunLike.congr_fun (hcB x) u
    change c (b x u) = b x (c u) at he
    rw [he,hcU u hu]
  refine ⟨k,hkR,hk2,hkP,hconj,?_⟩
  intro w hw
  have hh := hcM hw
  change t.symm ((a : MulAut (CoreFrattiniSection T L H)) w) = w at hh
  exact t.symm_apply_eq.mp hh

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding BinaryThreeAction BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The unchanged collapsed source supplies agreement on its actual invariant
module-core span, including a lift in the original join core and the same cubic. -/
theorem SourceCubicNormalizerEnlargement.exists_module_core_span_agreement
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ H P : Subgroup G, ∃ h : Data D H,
      ∃ hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G),
      LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H) ∧
      (moduleFrattiniImage D H = ⊥ ∨ Nat.card (moduleFrattiniImage D H) = 4) ∧
      ∀ a : moduleFrattiniImage D H,
        ∃ k : enlargedResidual T L H, (k:G) ∈ (localJoin T L).pCoreIn 2 ∧
          (QuotientGroup.mk' (pCore 2 (enlargedResidual T L H)) k) ^ 2 = 1 ∧
          QuotientGroup.mk' (pCore 2 (enlargedResidual T L H)) k ∈
            centralizer (quotientImage (enlargedResidual T L H) P : Set _) ∧
          (∀ x, (a : MulAut (CoreFrattiniSection T L H)) * h.coreQuotientFrattiniAction hn x *
              (a : MulAut (CoreFrattiniSection T L H))⁻¹ =
            h.coreQuotientFrattiniAction hn (QuotientGroup.mk' _ k) *
              h.coreQuotientFrattiniAction hn x * (h.coreQuotientFrattiniAction hn (QuotientGroup.mk' _ k))⁻¹) ∧
          ∀ w ∈ h.moduleCoreSpan hn, (a : MulAut (CoreFrattiniSection T L H)) w =
            h.coreQuotientFrattiniAction hn (QuotientGroup.mk' _ k) w := by
  obtain ⟨_,_,hfull,hn,_,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,_,h24,_,_,_,hcollapse⟩ := hc
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hcross := Selection.ModuleChoice.crossed_of_local_thompson D (hfull ▸ hJ) ht htn
  obtain ⟨s,_⟩ := exists_naturalData D hmodel hzero hfull ht htn hcross
  let f := originalLift s s.fixed_zero
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hP := (hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))).2
  exact ⟨H,P,h,hn,hs.toLocalInput,
    h.collapsed_moduleFrattiniImage_bot_or_four f hn hs.toLocalInput hP hcollapse,
    h.exists_module_actor_agrees_on_core_span f hn hs hK hp ho hm h24 hP hcollapse⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
