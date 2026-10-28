module

public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.IntrinsicModels.Quotients
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.FFG2DerivedCenter
public import Theory.SpecificGroups.G2Even.MarkedCover

/-!
# The intrinsic component above the original binary G₂ plus image

A.3.6 excludes its two nonquasisimple radical alternatives: their perfect
SL₂(p) quotient cannot map onto the group of order 6048. The original
component modulo its two-core is therefore quasisimple. Its marked central
cover of G₂(2)′ has two-group kernel, which vanishes in the two-core-free
quotient. The conclusion retains the exact original action map and identifies
its kernel with O₂(K), without a minimal replacement or a block assumption.

This is the intrinsic quotient step needed before C.1.32 in the proof of
13.6.22; reconstruction of the whole commutator core remains separate.
Source: Aschbacher--Smith A.3.6 and 13.6.22, printed pp.43--45 and 932.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.G2Selection.Intrinsic
open ComponentSelection SourceOrthogonal.Selection
universe u

variable [IsQuasisimple (commutator (Atlas.G2.Model (ZMod 2)))]

private instance derived_simple : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) := by
  let : IsSimpleGroup ((commutator (Atlas.G2.Model (ZMod 2))) ⧸
      center (commutator (Atlas.G2.Model (ZMod 2)))) := IsQuasisimple.simple
  exact ((QuotientGroup.quotientMulEquivOfEq
    Theory.SpecificGroups.g2_derived_two_center_eq_bot).trans QuotientGroup.quotientBot).symm.isSimpleGroup

private theorem surjective_ker_ne_top {H : Type*} [Group H]
    (f : H →* commutator (Atlas.G2.Model (ZMod 2))) (hf : Function.Surjective f) : f.ker ≠ ⊤ := by
  intro h
  obtain ⟨y, hy⟩ := exists_ne (1 : commutator (Atlas.G2.Model (ZMod 2)))
  obtain ⟨x, rfl⟩ := hf y
  exact hy (h.ge (mem_top x))

/-- A quasisimple epimorphism onto G₂(2)′ has exactly the central kernel. -/
theorem quasisimple_kernel_eq_center {H : Type*} [Group H] [IsQuasisimple H]
    (f : H →* commutator (Atlas.G2.Model (ZMod 2))) (hf : Function.Surjective f) :
    f.ker = center H := by
  apply le_antisymm
  · exact (IsQuasisimple.normal_le_center_or_eq_top f.ker).resolve_right
      (surjective_ker_ne_top f hf)
  · intro x hx
    have hz : f x ∈ center (commutator (Atlas.G2.Model (ZMod 2))) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := hf y
      simpa only [map_mul] using congrArg f (mem_center_iff.mp hx y)
    simpa only [Theory.SpecificGroups.g2_derived_two_center_eq_bot,
      mem_bot, MonoidHom.mem_ker] using hz

/-- The central quotient identification retains the specified epimorphism. -/
noncomputable def centralQuotientEquiv {H : Type*} [Group H] [IsQuasisimple H]
    (f : H →* commutator (Atlas.G2.Model (ZMod 2))) (hf : Function.Surjective f) :
    (H ⧸ center H) ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
  (QuotientGroup.quotientMulEquivOfEq (quasisimple_kernel_eq_center f hf).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- The central identification uses the specified epimorphism. -/
theorem centralQuotientEquiv_mk {H : Type*} [Group H] [IsQuasisimple H]
    (f : H →* commutator (Atlas.G2.Model (ZMod 2))) (hf : Function.Surjective f) (h : H) :
    centralQuotientEquiv f hf (QuotientGroup.mk h) = f h := by
  unfold centralQuotientEquiv
  rfl

private noncomputable def centerQuotientCongr {H J : Type*} [Group H] [Group J] (e : H ≃* J) :
    (H ⧸ center H) ≃* (J ⧸ center J) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (centerCongr e ⟨x, hx⟩).property
    · intro y hy
      exact ⟨e.symm y, (centerCongr e.symm ⟨y, hy⟩).property, e.apply_symm_apply y⟩)

private theorem solvable_le_ker {H : Type*} [Group H] [Group.IsPerfect H]
    (N : Subgroup H) [N.Normal] [Group.IsSolvable N]
    (f : H →* commutator (Atlas.G2.Model (ZMod 2))) (hf : Function.Surjective f) : N ≤ f.ker := by
  let : Group.IsPerfect (commutator (Atlas.G2.Model (ZMod 2))) := Group.IsPerfect.ofSurjective hf
  let : (N.map f).Normal := (inferInstance : N.Normal).map f hf
  have he : N.map f = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map f) inferInstance with h | h
    · exact h
    · let : Group.IsSolvable (N.map f) := Group.isSolvable_of_surjective
        (f := f.subgroupMap N) (f.subgroupMap_surjective N)
      have ht : Group.IsSolvable (⊤ : Subgroup (commutator (Atlas.G2.Model (ZMod 2)))) := h ▸ inferInstance
      let := ht
      let : Group.IsSolvable (commutator (Atlas.G2.Model (ZMod 2))) :=
        Group.isSolvable_of_surjective (f := (topEquiv :
          (⊤ : Subgroup (commutator (Atlas.G2.Model (ZMod 2)))) ≃* commutator (Atlas.G2.Model (ZMod 2))).toMonoidHom)
          topEquiv.surjective
      exact (Group.IsPerfect.not_isSolvable (commutator (Atlas.G2.Model (ZMod 2))) inferInstance).elim
  exact (Subgroup.map_eq_bot_iff _).mp he

private theorem not_sl2_surjection {H : Type*} [Group H] [IsQuasisimple H]
    {p : ℕ} (hp : p.Prime) (hlarge : 3 < p) (hm : IsSL H 2 p)
    (f : H →* commutator (Atlas.G2.Model (ZMod 2))) (hf : Function.Surjective f) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let d := (centerQuotientCongr e).symm.trans (centralQuotientEquiv f hf)
  have hseven : Nat.card (commutator (Atlas.G2.Model (ZMod 2))) = 6048 :=
    Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)
  have hcard : Nat.card (SL(2, F) ⧸ center SL(2, F)) = 6048 :=
    (Nat.card_congr d.toEquiv).trans hseven
  have hc := (center SL(2, F)).card_eq_card_quotient_mul_card_subgroup
  rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,
    hcard, Atlas.ExceptionalSupport.card_sl_center, hF] at hc
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hg : Nat.gcd 2 (p - 1) = 2 :=
    Nat.gcd_eq_left_iff_dvd.mpr (by obtain ⟨k, hk⟩ := hodd; exact ⟨k, by omega⟩)
  simp only [Fintype.card_fin, hg] at hc
  by_cases h : p ≤ 22
  · have hs : p ^ 2 ≤ 22 ^ 2 := Nat.pow_le_pow_left h 2
    have hm := Nat.mul_le_mul h (Nat.sub_le_sub_right hs 1)
    norm_num at hm
    omega
  · have hl : 23 ≤ p := by omega
    have hs : 23 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hl 2
    have hm := Nat.mul_le_mul hl (Nat.sub_le_sub_right hs 1)
    norm_num at hm
    omega

private theorem radical_alternative_impossible {H : Type*} [Group H] [Finite H]
    [Group.IsPerfect H] (hcommon : A36Common H)
    (heq : generalizedFitting H = fittingSubgroup H)
    {p : ℕ} (hp : p.Prime) (hlarge : 3 < p)
    (hm : IsSL (H ⧸ generalizedFitting H) 2 p)
    (f : H →* commutator (Atlas.G2.Model (ZMod 2))) (hf : Function.Surjective f) : False := by
  obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ := hm
  have hmodel : IsSL (H ⧸ fittingSubgroup H) 2 p :=
    ⟨F, hfield, hfinite, hF,
      ⟨(QuotientGroup.quotientMulEquivOfEq heq).symm.trans e⟩⟩
  let : IsQuasisimple (H ⧸ fittingSubgroup H) := hcommon.2.1
  let q := QuotientGroup.lift (fittingSubgroup H) f
    (solvable_le_ker (fittingSubgroup H) f hf)
  exact not_sl2_surjection hp hlarge hmodel q
    (QuotientGroup.lift_surjective_of_surjective _ _ hf _)

/-- A C-component in the A.3.6 catalogue mapping onto G₂(2)′ is quasisimple. -/
theorem quasisimple_of_a36 {X : Type u} [Group X] [Finite X]
    (B : Subgroup X) (hB : B.IsCComponent) (hA : A36Conclusion B)
    (f : B →* commutator (Atlas.G2.Model (ZMod 2))) (hf : Function.Surjective f) : IsQuasisimple B := by
  let : Group.IsPerfect B := hB.perfect
  rcases hA with ⟨halt, hcommon⟩
  cases halt with
  | simple hc _ _ => exact hc.2
  | cover hc _ _ => exact hc.2
  | natural h =>
    obtain ⟨p, hp, hlarge, F, hfield, hfinite, hF, v, e, haction⟩ := h.2
    exact (radical_alternative_impossible hcommon h.1 hp hlarge
      ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ f hf).elim
  | nilpotent h =>
    exact (radical_alternative_impossible hcommon h.1 (by decide : Nat.Prime 5)
      (by decide) h.2.2.1 f hf).elim


omit [IsQuasisimple (commutator (Atlas.G2.Model (ZMod 2)))] in
private theorem twoCore_le_ker {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) (hB : pCore 2 B = ⊥) :
    pCore 2 A ≤ f.ker := by
  have hm : (pCore 2 A).map f ≤ pCore 2 B :=
    le_sSup ⟨(inferInstance : (pCore 2 A).Normal).map f hf, pCore_isPGroup.map f⟩
  exact (Subgroup.map_eq_bot_iff _).mp (bot_unique (hm.trans hB.le))

/-- A.3.6 applies to the image in the ambient two-core quotient and proves
quasisimplicity of the intrinsic quotient above any given G₂(2)′ epimorphism. -/
theorem cComponent_quotient_quasisimple {G : Type u} [Group G] [Finite G]
    {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → A36Conclusion B)
    (hG : IsSQTK 𝒦 G) (B : Subgroup G) (hB : B.IsCComponent)
    (f : B →* commutator (Atlas.G2.Model (ZMod 2))) (hf : Function.Surjective f)
    (hcore : pCore 2 (commutator (Atlas.G2.Model (ZMod 2))) = ⊥) :
    IsQuasisimple (B ⧸ pCore 2 B) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G) := by
    refine ⟨?_, hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  let := pCore_isNilpotent (p := 2) (G := G)
  have hBq : (B.map q).IsCComponent := hB.map_quotient _
  let fQ := QuotientGroup.lift (pCore 2 B) f (twoCore_le_ker f hf hcore)
  have hfQ : Function.Surjective fQ := QuotientGroup.lift_surjective_of_surjective _ _ hf _
  let eB := cComponentTwoCoreQuotientEquiv hB
  let g := fQ.comp eB.symm.toMonoidHom
  let : IsQuasisimple (B.map q) := quasisimple_of_a36 (B.map q) hBq
    (hA36 _ hQ (pCore_quotient_pCore_eq_bot 2) _ hBq) g
      (hfQ.comp eB.symm.surjective)
  exact IsQuasisimple.of_mulEquiv eB.symm

/-- The original plus-G₂(2)′ component has quasisimple intrinsic two-core
quotient and exactly the G₂(2)′ central quotient. No minimal replacement or short-block hypothesis is required. -/
theorem intrinsic_quasisimple_and_central_quotient {G : Type u} [Group G] [Finite G]
    {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → A36Conclusion B)
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK 𝒦 (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (e : plusImage K L T z v hL hz K ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    IsQuasisimple (K ⧸ pCore 2 K) ∧
      Nonempty (((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃*
        commutator (Atlas.G2.Model (ZMod 2))) := by
  let H := K ⊔ Tv T v
  let B := K.subgroupOf H
  have hHG : H ≤ Gv v := sup_le hK.1.1 inf_le_right
  have hH : IsSQTK 𝒦 H := (IsSQTK.equiv (subgroupOfEquivOfLe hHG)).mp
    (hlocal.subgroup (H.subgroupOf (Gv v)))
  let eB : B ≃* K := subgroupOfEquivOfLe le_sup_left
  let f := e.toMonoidHom.comp (intrinsicToPlus K L T z v hK.1.1 hL hz)
  have hf : Function.Surjective f := e.surjective.comp
    (intrinsicToPlus_surjective K L T z v hK.1.1 hL hz)
  have hplus : pCore 2 (plusImage K L T z v hL hz K) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (plusImage_K_subnormal K L T z v hL hz hK), hR]
    exact (plusImage K L T z v hL hz K).ker_subtype
  have hseven : pCore 2 (commutator (Atlas.G2.Model (ZMod 2))) = ⊥ := by
    rw [← pCore_map_iso 2 e, hplus, Subgroup.map_bot]
  let : IsQuasisimple (B ⧸ pCore 2 B) := cComponent_quotient_quasisimple
    hA36 hH B hK.1.2.1 (f.comp eB.toMonoidHom) (hf.comp eB.surjective) hseven
  let c := QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv c
  let fQ := QuotientGroup.lift (pCore 2 K) f (twoCore_le_ker f hf hseven)
  exact ⟨inferInstance,
    ⟨centralQuotientEquiv fQ (QuotientGroup.lift_surjective_of_surjective _ _ hf _)⟩⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.G2Selection.Intrinsic
