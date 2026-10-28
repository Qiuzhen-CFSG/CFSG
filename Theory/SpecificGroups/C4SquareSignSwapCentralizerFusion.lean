module
public import Theory.SpecificGroups.C4SquareSignSwapCentric
public import Theory.SpecificGroups.C4SquareSignSwapSmallGeometry
public import Theory.SpecificGroups.C4SquareSignSwapFusionGeometry
public import Theory.GroupTheory.ElementaryEightCentralizerNormalizer
public import ABG.ChapterII.Section1.CentricFusionRelation
public import ABG.ChapterII.Section1.ExtremalNormalizerCore
public import Theory.GroupTheory.InvolutionTransfer
public import Theory.ElementaryAbelian.Injective
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Fusion exclusion from a binary G₂ point centralizer

Let a finite group have a Sylow two-subgroup marked by the sign-and-swap
model. Suppose the centralizer of a central involution has order 192 and
preserves the marked transfer subgroup. Assume also the concrete local
geometry of its centric elementary eights: each is self-centralizing and
is not normalized by the whole point centralizer. Then all ambient fusion
preserves the transfer subgroup, and Thompson transfer excludes simplicity.

The centric catalogue reduces normalizer steps to two-group automizers,
the characteristic square of the inverter core, unique central involutions,
and elementary eights. The last case enlarges to a normalizer two-core of
order at least 32, where the small exceptions disappear. No solvability
hypothesis on other two-local subgroups is used.

Source: Aschbacher--Smith, source 14.2.22, full binary G₂ alternative;
the centric-fusion method also occurs in Stellmacher (8.6)(a).
-/

@[expose] public noncomputable section
namespace C4SquareSignSwap
open Subgroup BenderSuzuki.External
variable {G : Type*} [Group G] [Finite G]

private theorem normal_mem_iff_of_isConj
    {H : Type*} [Group H] (U : Subgroup H) [hU : U.Normal]
    {x y : H} (hxy : IsConj x y) : x ∈ U ↔ y ∈ U := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
  constructor
  · exact fun hx => hU.conj_mem x hx g
  · intro hy
    simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using
      hU.conj_mem' (g * x * g⁻¹) hy g

private def Step (T : Sylow 2 G) (e : T ≃* Model) (X : Subgroup G) : Prop :=
  ∀ g : G, g ∈ normalizer (X : Set G) → ∀ x y : T,
    (x : G) ∈ X → g⁻¹ * (x : G) * g = (y : G) →
      (e x ∈ transfer ↔ e y ∈ transfer)

omit [Finite G] in
private theorem step_of_le (T : Sylow 2 G) (e : T ≃* Model)
    (X : Subgroup G) (hle : X.subgroupOf (T : Subgroup G) ≤ transfer.comap e.toMonoidHom) :
    Step T e X := by
  intro g hg x y hx hxy
  have hy : (y : G) ∈ X := hxy ▸ ((mem_normalizer_iff''.mp hg) _).mp hx
  exact iff_of_true (hle hx) (hle hy)

private theorem step_of_aut (T : Sylow 2 G) (e : T ≃* Model)
    (X : Subgroup G) (hX : HuppertExtremal T X) (hAut : IsPGroup 2 (MulAut X)) :
    Step T e X := by
  intro g hg x y hx hxy
  have hconj := ABG.extremal_normalizer_fusion_control T X hX hAut g hg x y hx hxy
  obtain ⟨s,hs⟩ := isConj_iff.mp hconj
  apply normal_mem_iff_of_isConj transfer
  apply isConj_iff.mpr
  exact ⟨e s, by simpa only [map_mul,map_inv] using congrArg e hs⟩

omit [Finite G] in
private theorem marked_candidate (T : Sylow 2 G) (e : T ≃* Model)
    (X : Subgroup G) (hXT : X ≤ (T : Subgroup G))
    (hc : subgroupCentralizerIn (T : Subgroup G) X ≤ X)
    (hout : ¬ X.subgroupOf (T : Subgroup G) ≤ transfer.comap e.toMonoidHom) :
    ∃ (f : T ≃* Model) (i : Fin 32),
      (∀ x : T, f x ∈ transfer ↔ e x ∈ transfer) ∧
      (X.subgroupOf (T : Subgroup G)).map f.toMonoidHom = centricCandidate i := by
  let Y := (X.subgroupOf (T : Subgroup G)).map e.toMonoidHom
  have hcY : centralizer (Y : Set Model) ≤ Y := by
    intro y hy
    have hx : (e.symm y : G) ∈ X := by
      apply hc
      refine ⟨(e.symm y).property, ?_⟩
      intro x hx
      have h := hy (e ⟨x, hXT hx⟩) (mem_map_of_mem e.toMonoidHom hx)
      have h' := congrArg (fun z => (e.symm z : G)) h
      simpa using h'
    exact ⟨e.symm y, hx, e.apply_symm_apply y⟩
  have houtY : ¬ Y ≤ transfer := by
    intro h
    apply hout
    intro x hx
    exact h (mem_map_of_mem e.toMonoidHom hx)
  obtain ⟨i,g,hY⟩ := centricCandidate_complete Y hcY houtY
  refine ⟨e.trans (MulAut.conj g), i, ?_, ?_⟩
  · intro x
    exact (normal_mem_iff_of_isConj transfer (isConj_iff.mpr ⟨g,rfl⟩)).symm
  · rw [show (e.trans (MulAut.conj g)).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp e.toMonoidHom from rfl, ← map_map]
    exact hY

private def candidateEquiv (T : Sylow 2 G) (f : T ≃* Model)
    (X : Subgroup G) (hXT : X ≤ (T : Subgroup G)) (i : Fin 32)
    (hmap : (X.subgroupOf (T : Subgroup G)).map f.toMonoidHom = centricCandidate i) :
    X ≃* centricCandidate i :=
  ((subgroupOfEquivOfLe hXT).symm.trans
    ((X.subgroupOf (T : Subgroup G)).equivMapOfInjective f.toMonoidHom f.injective)).trans
    (MulEquiv.subgroupCongr hmap)

omit [Finite G] in
private theorem candidate_normalizer_card (T : Sylow 2 G) (f : T ≃* Model)
    (X : Subgroup G) (hXT : X ≤ (T : Subgroup G)) (i : Fin 32)
    (hmap : (X.subgroupOf (T : Subgroup G)).map f.toMonoidHom = centricCandidate i)
    (hi : i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 29 ∨ i = 30) :
    32 ≤ Nat.card ((T : Subgroup G) ⊓ normalizer (X : Set G) : Subgroup G) := by
  have hbound := smallCandidate_normalizer_card i (by rcases hi with rfl|rfl|rfl|rfl|rfl <;> simp)
  rw [← hmap, ← map_equiv_normalizer_eq,
    card_map_of_injective f.injective, ← subgroupOf_normalizer_eq hXT] at hbound
  rw [← inf_subgroupOf_left,
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at hbound
  exact hbound

omit [Finite G] in
private theorem central_mem_centric (T : Sylow 2 G) (z : T)
    (hz : z ∈ center T) (X : Subgroup G) (hXT : X ≤ (T : Subgroup G))
    (hc : subgroupCentralizerIn (T : Subgroup G) X ≤ X) : (z : G) ∈ X := by
  apply hc
  refine ⟨z.property, ?_⟩
  intro x hx
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨x,hXT hx⟩)

private theorem elementary_core_large (T : Sylow 2 G) (e : T ≃* Model)
    (z : T) (hz : z ∈ center T) (hz2 : orderOf z = 2)
    (hcard : Nat.card (centralizer ({(z:G)} : Set G)) = 192)
    (X : Subgroup G) (hX : HuppertExtremal T X)
    (hc : subgroupCentralizerIn (T : Subgroup G) X ≤ X)
    (hEA : IsElementaryAbelian 2 X) (h8 : Nat.card X = 8)
    (hcent : centralizer (X : Set G) = X)
    (hn : ¬ centralizer ({(z:G)} : Set G) ≤ normalizer (X : Set G))
    (hbound : 32 ≤ Nat.card ((T : Subgroup G) ⊓ normalizer (X : Set G) : Subgroup G)) :
    32 ≤ Nat.card (ABG.normalizerPCore 2 X) := by
  let := hEA
  let N := normalizer (X : Set G)
  let M := (T : Subgroup G) ⊓ N
  have hker : Nat.card X.normalizerMonoidHom.ker = 8 := by
    rw [normalizerMonoidHom_ker, hcent,
      Nat.card_congr (subgroupOfEquivOfLe X.le_normalizer).toEquiv,h8]
  have hT : Nat.card T = 64 := (Nat.card_congr e.toEquiv).trans card_model
  have hMdiv : Nat.card M ∣ 2 ^ 6 := by
    have h := card_dvd_of_le (show M ≤ (T : Subgroup G) from inf_le_left)
    simpa [hT] using h
  have h32M : 32 ∣ Nat.card M := by
    obtain ⟨k,hk,hMk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hMdiv
    interval_cases k <;> rw [hMk] at hbound ⊢ <;> norm_num at *
  have h32N : 32 ∣ Nat.card N := h32M.trans (card_dvd_of_le (show M ≤ N from inf_le_right))
  have hcount := X.normalizerMonoidHom.ker.card_mul_index
  rw [index_ker,hker] at hcount
  have hfour : 4 ∣ Nat.card X.normalizerMonoidHom.range := by
    rw [← hcount] at h32N
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 8)).mp h32N
  have hzX := central_mem_centric T z hz X hX.1 hc
  have hz' : (⟨(z:G),hzX⟩ : X) ≠ 1 := by
    intro h
    have hzone : z = 1 := Subtype.ext (congrArg (fun t : X => (t : G)) h)
    rw [hzone,orderOf_one] at hz2
    omega
  have hlarge := elementary_eight_normalizer_core_card_of_centralizer192
    X h8 hcent ⟨(z:G),hzX⟩ hz' hcard hn hfour
  simpa only [ABG.normalizerPCore,card_map_of_injective (normalizer (X:Set G)).subtype_injective]
    using hlarge


omit [Finite G] in
private theorem step_of_unique_central_involution (T : Sylow 2 G) (e : T ≃* Model)
    (z : T) (hz : z ∈ center T) (hz2 : orderOf z = 2)
    (hH : ∀ g ∈ centralizer ({(z:G)} : Set G), ∀ x y:T,
      g⁻¹*(x:G)*g=(y:G) → (e x∈transfer ↔ e y∈transfer))
    (X : Subgroup G) (hXT : X ≤ (T : Subgroup G))
    (hc : subgroupCentralizerIn (T : Subgroup G) X ≤ X)
    (i : Fin 32) (hi : i=17 ∨ i=26 ∨ i=28 ∨ i=31)
    (q : X ≃* centricCandidate i) : Step T e X := by
  have hzX := central_mem_centric T z hz X hXT hc
  let zX : X := ⟨(z:G),hzX⟩
  have hzc : zX ∈ center X := by
    rw [mem_center_iff]
    intro x
    apply Subtype.ext
    exact congrArg (fun t : T => (t:G)) (mem_center_iff.mp hz ⟨x,hXT x.property⟩)
  have hzp : zX ^ 2 = 1 := by
    apply Subtype.ext
    exact congrArg (fun t : T => (t:G)) (hz2 ▸ pow_orderOf_eq_one z)
  have hzne : zX ≠ 1 := by
    intro h
    have hzone : z = 1 := Subtype.ext (congrArg (fun t : X => (t:G)) h)
    rw [hzone,orderOf_one] at hz2
    omega
  have hpoint (w:X) (hwc:w∈center X) (hwp:w^2=1) (hwne:w≠1) :
      (q w : Model) = coordinateElement 10 := by
    apply candidate_central_involution_eq i hi (q w) (q w).property
    · intro a ha
      obtain ⟨v,hv⟩ := q.surjective ⟨a,ha⟩
      have h := congrArg q (mem_center_iff.mp hwc v)
      have h' := congrArg (fun t : centricCandidate i => (t:Model)) h
      simpa only [map_mul,hv,coe_mul] using h'
    · have hp : (q w)^2=1 := by rw [← map_pow,hwp,map_one]
      exact congrArg (fun t : centricCandidate i => (t:Model)) hp
    · intro h
      apply hwne
      apply q.injective
      apply Subtype.ext
      simpa only [map_one,coe_one] using h
  intro g hg x y hx hxy
  apply hH g ?_ x y hxy
  let a : MulAut X := X.normalizerMonoidHom ⟨g,hg⟩
  have hac : a zX ∈ center X := by
    rw [mem_center_iff]
    intro w
    obtain ⟨v,rfl⟩ := a.surjective w
    simpa only [map_mul] using congrArg a (mem_center_iff.mp hzc v)
  have hap : (a zX)^2=1 := by rw [← map_pow,hzp,map_one]
  have hane : a zX ≠ 1 := by
    intro h
    exact hzne (a.injective (h.trans (map_one a).symm))
  have haz : a zX = zX := by
    apply q.injective
    apply Subtype.ext
    exact (hpoint _ hac hap hane).trans (hpoint _ hzc hzp hzne).symm
  apply mem_centralizer_singleton_iff.mpr
  have h : g * (z:G) * g⁻¹ = (z:G) := congrArg (fun t : X => (t:G)) haz
  exact mul_inv_eq_iff_eq_mul.mp h

omit [Finite G] in
private theorem step_of_inverter (T : Sylow 2 G) (e f : T ≃* Model)
    (hfe : ∀ x:T, f x∈transfer ↔ e x∈transfer)
    (X : Subgroup G) (hXT : X ≤ (T : Subgroup G))
    (hmap : (X.subgroupOf (T : Subgroup G)).map f.toMonoidHom = inverterCore) :
    Step T e X := by
  let q : X ≃* inverterCore :=
    ((subgroupOfEquivOfLe hXT).symm.trans
      ((X.subgroupOf (T : Subgroup G)).equivMapOfInjective f.toMonoidHom f.injective)).trans
      (MulEquiv.subgroupCongr hmap)
  intro g hg x y hx hxy
  have hy : (y:G)∈X := hxy ▸ ((mem_normalizer_iff''.mp hg) _).mp hx
  let a : MulAut X := X.normalizerMonoidHom ⟨g⁻¹,(normalizer (X:Set G)).inv_mem hg⟩
  have haxy : a ⟨x,hx⟩ = ⟨y,hy⟩ := by
    apply Subtype.ext
    change g⁻¹ * (x:G) * (g⁻¹)⁻¹ = (y:G)
    simpa only [inv_inv] using hxy
  have h := inverterCore_automorphism_preserves_transfer
    (q.symm.trans (a.trans q)) (q ⟨x,hx⟩)
  have h' : f y ∈ transfer ↔ f x ∈ transfer := by
    simp only [MulEquiv.trans_apply,MulEquiv.symm_apply_apply,haxy] at h
    exact h
  exact (hfe x).symm.trans (h'.symm.trans (hfe y))

private theorem step_or_elementary (T : Sylow 2 G) (e : T ≃* Model)
    (z : T) (hz : z ∈ center T) (hz2 : orderOf z = 2)
    (hH : ∀ g ∈ centralizer ({(z:G)} : Set G), ∀ x y:T,
      g⁻¹*(x:G)*g=(y:G) → (e x∈transfer ↔ e y∈transfer))
    (X : Subgroup G) (hX : HuppertExtremal T X)
    (hc : subgroupCentralizerIn (T : Subgroup G) X ≤ X) :
    Step T e X ∨ (IsElementaryAbelian 2 X ∧ Nat.card X=8 ∧
      32 ≤ Nat.card ((T : Subgroup G) ⊓ normalizer (X : Set G) : Subgroup G)) := by
  by_cases hout : X.subgroupOf (T : Subgroup G) ≤ transfer.comap e.toMonoidHom
  · exact Or.inl (step_of_le T e X hout)
  obtain ⟨f,i,hfe,hmap⟩ := marked_candidate T e X hX.1 hc hout
  let q := candidateEquiv T f X hX.1 i hmap
  by_cases hi : centricExceptionalIndex i
  · have hcases : i=11 ∨ (i=17 ∨ i=26 ∨ i=28 ∨ i=31) ∨
        (i=18 ∨ i=19 ∨ i=20 ∨ i=29 ∨ i=30) := by
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
    rcases hcases with rfl | hi | hi
    · left
      apply step_of_inverter T e f hfe X hX.1
      exact hmap.trans centricCandidate_eleven
    · exact Or.inl (step_of_unique_central_involution T e z hz hz2 hH X hX.1 hc i hi q)
    · right
      obtain ⟨hEA,h8⟩ := centricCandidate_elementary i hi
      have hEA' : IsElementaryAbelian 2 X := by
        let := hEA
        exact IsElementaryAbelian.of_injective q.toMonoidHom q.injective
      exact ⟨hEA', (Nat.card_congr q.toEquiv).trans h8,
        candidate_normalizer_card T f X hX.1 i hmap hi⟩
  · left
    apply step_of_aut T e X hX
    exact (centricCandidate_isPGroup_mulAut i hi).of_equiv (MulAut.congr q).symm

private theorem step_of_large_core (T : Sylow 2 G) (e : T ≃* Model)
    (z : T) (hz : z ∈ center T) (hz2 : orderOf z = 2)
    (hH : ∀ g ∈ centralizer ({(z:G)} : Set G), ∀ x y:T,
      g⁻¹*(x:G)*g=(y:G) → (e x∈transfer ↔ e y∈transfer))
    (X : Subgroup G) (hX : HuppertExtremal T X)
    (hc : subgroupCentralizerIn (T : Subgroup G) X ≤ X)
    (hlarge : 32 ≤ Nat.card (ABG.normalizerPCore 2 X)) : Step T e X := by
  let R := ABG.normalizerPCore 2 X
  have hRT := ABG.normalizerPCore_le_sylow T X hX
  have hcR := ABG.normalizerPCore_centric T X hX hc
  let V := R.subgroupOf (T : Subgroup G)
  have hVcard : Nat.card V = Nat.card R :=
    Nat.card_congr (subgroupOfEquivOfLe hRT).toEquiv
  have hT : Nat.card T = 64 := (Nat.card_congr e.toEquiv).trans card_model
  have hcount : Nat.card V * V.index = 64 := by simpa only [hT] using V.card_mul_index
  have hi0 : V.index ≠ 0 := index_ne_zero_of_finite
  have hlargeV : 32 ≤ Nat.card V := hVcard.symm ▸ hlarge
  have hi : V.index=1 ∨ V.index=2 := by
    have : V.index≤2 := by nlinarith
    omega
  have hVN : V.Normal := by
    rcases hi with hi|hi
    · rw [index_eq_one.mp hi]; infer_instance
    · exact normal_of_index_eq_two hi
  have hTN : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hRT).mp hVN
  have hRext := ABG.extremal_of_sylow_le_normalizer T R hRT hTN
  have hRstep : Step T e R := by
    rcases step_or_elementary T e z hz hz2 hH R hRext hcR with hstep | hEA
    · exact hstep
    · have h8 := hEA.2.1
      change 32 ≤ Nat.card R at hlarge
      omega
  exact ABG.normalizer_relation_of_normalizerPCore T X hX
    (fun x y => e x∈transfer ↔ e y∈transfer) hRstep

/-- A point centralizer of order 192 controls all fusion in the marked Sylow
provided its centric elementary eights have the concrete model centralizers. -/
theorem fusion_preserves_transfer_of_centralizer192
    (T : Sylow 2 G) (e : T ≃* Model) (z : T)
    (hz : z ∈ center T) (hz2 : orderOf z=2)
    (hcard : Nat.card (centralizer ({(z:G)} : Set G))=192)
    (hH : ∀ g ∈ centralizer ({(z:G)} : Set G), ∀ x y:T,
      g⁻¹*(x:G)*g=(y:G) → (e x∈transfer ↔ e y∈transfer))
    (hE : ∀ E : Subgroup G, E≤(T:Subgroup G) →
      ((T:Subgroup G) ⊓ centralizer (E:Set G) ≤ E) →
      IsElementaryAbelian 2 E → Nat.card E=8 →
      centralizer (E:Set G)=E ∧ ¬centralizer ({(z:G)}:Set G)≤normalizer (E:Set G))
    (x y : T) (hxy : IsConj (x:G) (y:G)) : e x∈transfer ↔ e y∈transfer := by
  apply ABG.centric_fusion_relation T (fun x y => e x∈transfer ↔ e y∈transfer)
    (fun _ => Iff.rfl) (fun h₁ h₂ => h₁.trans h₂) ?_ hxy
  intro X hX hc
  rcases step_or_elementary T e z hz hz2 hH X hX hc with hstep | ⟨hEA,h8,hbound⟩
  · exact hstep
  obtain ⟨hcent,hn⟩ := hE X hX.1 hc hEA h8
  exact step_of_large_core T e z hz hz2 hH X hX hc
    (elementary_core_large T e z hz hz2 hcard X hX hc hEA h8 hcent hn hbound)

/-- Thompson transfer excludes a simple ambient group with this full binary
G₂ point-centralizer geometry. -/
theorem simple_exclusion_of_centralizer192 [IsSimpleGroup G]
    (T : Sylow 2 G) (e : T ≃* Model) (z : T)
    (hz : z ∈ center T) (hz2 : orderOf z=2)
    (hcard : Nat.card (centralizer ({(z:G)} : Set G))=192)
    (hH : ∀ g ∈ centralizer ({(z:G)} : Set G), ∀ x y:T,
      g⁻¹*(x:G)*g=(y:G) → (e x∈transfer ↔ e y∈transfer))
    (hE : ∀ E : Subgroup G, E≤(T:Subgroup G) →
      ((T:Subgroup G) ⊓ centralizer (E:Set G) ≤ E) →
      IsElementaryAbelian 2 E → Nat.card E=8 →
      centralizer (E:Set G)=E ∧ ¬centralizer ({(z:G)}:Set G)≤normalizer (E:Set G)) : False := by
  have hT : Nat.card T = 64 := (Nat.card_congr e.toEquiv).trans card_model
  have hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2 := by
    intro K hK hi
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K hK with hb | ht
    · have hbound : 64 ≤ Nat.card G := hT ▸ (T : Subgroup G).card_le_card_group
      rw [hb,index_bot] at hi
      omega
    · simp [ht] at hi
  let U := transfer.comap e.toMonoidHom
  have hU : U.index=2 := by
    change (transfer.comap e.toMonoidHom).index=2
    rw [Subgroup.index_comap_of_surjective _ e.surjective]
    exact transfer_index
  let t : T := e.symm inverter
  have ht : orderOf t=2 := by
    rw [show orderOf t=orderOf inverter from e.symm.orderOf_eq inverter]
    apply orderOf_eq_prime_iff.mpr
    constructor
    · decide +kernel
    · decide +kernel
  have htout : e t∉transfer := by
    change e (e.symm inverter)∉transfer
    rw [e.apply_symm_apply]
    decide +kernel
  obtain ⟨u,hconj,hu⟩ := T.exists_isConj_mem_of_index_two hno U hU t ht
  exact htout ((fusion_preserves_transfer_of_centralizer192 T e z hz hz2 hcard hH hE t u hconj).mpr hu)

end C4SquareSignSwap
