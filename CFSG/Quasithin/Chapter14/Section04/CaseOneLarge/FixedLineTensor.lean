module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineActions
public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients

/-!
# Whole-group recognition of the original deleted tensor row

The actual elementary actor has rank at least three, so its projection to S₅
has nontrivial kernel. A resulting pure involution in the S₃ factor cannot
centralize the whole image because the original two-core is trivial. Its
conjugates therefore fill S₃. Removing this factor identifies the whole image
as A₅ × S₃ or S₅ × S₃. The original tensor coordinates, with factors reversed,
then construct the literal marked action alternative on H/O₂(H).

This discharges the ambient-image gap for the deleted five-point constituent.
The natural SL₂(4), six-point and exchanged rows remain separate obligations.
Source: Aschbacher--Smith G.11.8 and 14.4.2(5), printed pp.368,1006;
refs/quasithin.pdf. The only finite check is generation by two transpositions
in the six-element group S₃.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative TensorProduct
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineTensor
open LargerDimension.Tensor

private theorem pure_second_factor
    {D : Type*} [Group D] [Finite D]
    (j : D →* Five × Three) (hj : Function.Injective j)
    (hcore : pCore 2 D = ⊥)
    (X : Subgroup D) [IsElementaryAbelian 2 X] (hr : 3 ≤ Group.rank X) :
    ∀ s : Three, (1,s) ∈ j.range := by
  let f : X →* Five := (MonoidHom.fst Five Three).comp (j.comp X.subtype)
  have hni : ¬ Function.Injective f := by
    intro hi
    let : IsElementaryAbelian 2 f.range :=
      IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    have hle := f.range.rank_le_primeRank 2 (IsElementaryAbelian.isPGroup 2 f.range)
    rw [← Group.rank_congr (MonoidHom.ofInjective hi)] at hle
    have hb : primeRank 2 Five ≤ 2 :=
      Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
    omega
  have hker : f.ker ≠ ⊥ := fun he => hni (f.ker_eq_bot_iff.mp he)
  have hex : ∃ x : X, x ∈ f.ker ∧ x ≠ 1 := by
    by_contra! hh
    apply hker
    apply le_bot_iff.mp
    intro x hx
    exact hh x hx
  obtain ⟨x,hxf,hx1⟩ := hex
  have hxf : (j x).1 = 1 := hxf
  let t := (j x).2
  have ht1 : t ≠ 1 := by
    intro he
    exact hx1 (Subtype.ext (hj ((Prod.ext hxf he).trans j.map_one.symm)))
  have ht2 : t ^ 2 = 1 := by
    have hh := congrArg (fun a => (j a).2)
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : D) x.property)
    simpa [t] using hh
  have hxt : j x = (1,t) := Prod.ext hxf rfl
  have hnotcentral : ¬ ∀ a : D, (j a).2 * t = t * (j a).2 := by
    intro he
    have hxcenter : (x : D) ∈ center D := by
      apply mem_center_iff.mpr
      intro a
      apply hj
      rw [map_mul,map_mul,hxt]
      exact Prod.ext (by simp) (he a)
    have hzc : zpowers (x : D) ≤ center D := zpowers_le.mpr hxcenter
    let : (zpowers (x : D)).Normal := ⟨by
      intro a ha g
      have hcomm := mem_center_iff.mp (hzc ha) g
      simpa only [hcomm,mul_assoc,mul_inv_cancel,mul_one] using ha⟩
    have hpow : (x : D) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (x : D) x.property
    have htwo : IsPGroup 2 (zpowers (x : D)) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers,orderOf_eq_prime hpow (fun he => hx1 (Subtype.ext he)),pow_one]
    have hle : zpowers (x : D) ≤ pCore 2 D := le_sSup ⟨inferInstance,htwo⟩
    exact hx1 (Subtype.ext (mem_bot.mp (hcore ▸ hle (mem_zpowers (x : D)))))
  push Not at hnotcentral
  obtain ⟨a,ha⟩ := hnotcentral
  let u := (j a).2 * t * (j a).2⁻¹
  have hu : (1,u) ∈ j.range := by
    refine ⟨a * x * a⁻¹,?_⟩
    rw [map_mul,map_mul,map_inv,hxt]
    exact Prod.ext (by simp) rfl
  have ht : (1,t) ∈ j.range := ⟨x,hxt⟩
  have hgen : ∀ t a : Three, t ^ 2 = 1 → t ≠ 1 → a*t ≠ t*a →
      ∀ s : Three, s = 1 ∨ s = t ∨ s = a*t*a⁻¹ ∨
        s = t*(a*t*a⁻¹) ∨ s = (a*t*a⁻¹)*t ∨ s = t*(a*t*a⁻¹)*t := by
    decide +kernel
  intro s
  rcases hgen t (j a).2 ht2 ht1 ha s with rfl | rfl | rfl | rfl | rfl | rfl
  · exact j.range.one_mem
  · exact ht
  · exact hu
  · exact j.range.mul_mem ht hu
  · exact j.range.mul_mem hu ht
  · exact j.range.mul_mem (j.range.mul_mem ht hu) ht

private theorem tensor_image
    {D : Type*} [Group D] [Finite D]
    (j : D →* Five × Three) (hj : Function.Injective j)
    (hA : ∀ s ∈ AltFive, (s,1) ∈ j.range)
    (hcore : pCore 2 D = ⊥)
    (X : Subgroup D) [IsElementaryAbelian 2 X] (hr : 3 ≤ Group.rank X) :
    ∃ A : Subgroup Five, ∃ _hA : AltFive ≤ A, (A = ⊤ ∨ A = AltFive) ∧
      ∃ e : D ≃* Three × A, ∀ a, ((e a).2 : Five) = (j a).1 ∧ (e a).1 = (j a).2 := by
  let A := ((MonoidHom.fst Five Three).comp j).range
  have hAA : AltFive ≤ A := by
    intro s hs
    obtain ⟨a,ha⟩ := hA s hs
    exact ⟨a,congrArg Prod.fst ha⟩
  have hcases : A = ⊤ ∨ A = AltFive := by
    by_cases hle : A ≤ AltFive
    · exact Or.inr (le_antisymm hle hAA)
    · obtain ⟨a,ha,hn⟩ := SetLike.not_le_iff_exists.mp hle
      have has : a.sign = -1 := (Int.units_eq_one_or a.sign).resolve_left
        (fun he => hn (Equiv.Perm.mem_alternatingGroup.mpr he))
      left
      apply top_unique
      intro s _
      rcases Int.units_eq_one_or s.sign with hs | hs
      · exact hAA (Equiv.Perm.mem_alternatingGroup.mpr hs)
      · have hh : s*a⁻¹ ∈ AltFive := by
          rw [Equiv.Perm.mem_alternatingGroup,map_mul,map_inv,hs,has]
          decide
        simpa only [inv_mul_cancel_right] using A.mul_mem (hAA hh) ha
  have hpure := pure_second_factor j hj hcore X hr
  let k : D →* Three × A := ((MonoidHom.snd Five Three).comp j).prod
    (((MonoidHom.fst Five Three).comp j).rangeRestrict)
  have hki : Function.Injective k := by
    intro a b he
    apply hj
    exact Prod.ext (congrArg (fun z : Three × A => (z.2 : Five)) he) (congrArg Prod.fst he)
  have hks : Function.Surjective k := by
    rintro ⟨s,b⟩
    obtain ⟨a,ha⟩ := b.property
    change (j a).1 = b.val at ha
    obtain ⟨c,hc⟩ := hpure ((j a).2⁻¹*s)
    refine ⟨a*c,?_⟩
    apply Prod.ext
    · change (j (a*c)).2 = s
      rw [map_mul,hc]
      exact mul_inv_cancel_left _ _
    · apply Subtype.ext
      change (j (a*c)).1 = b.val
      rw [map_mul,hc]
      simpa only [Prod.fst_mul,mul_one] using ha
  exact ⟨A,hAA,hcases,MulEquiv.ofBijective k ⟨hki,hks⟩,fun _ => ⟨rfl,rfl⟩⟩
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- Full tensor coordinates from the actual five-letter normalizer embedding. -/
theorem five_tensor_coordinates
    (ρ : Representation (ZMod 2) D W)
    {B : LinearMap.BilinForm (ZMod 2) W} {v : W} {E : Submodule (ZMod 2) W}
    {X : Subgroup D} [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (hyp : ChapterG.Section10.Hypothesis ρ B v E X X₀)
    (H : Subgroup D)
    (hm : FixedLineActions.PermutationTensorEmbedding ρ H
      (BinaryPermutation.coreRepresentation (Fin 5))) :
    ∃ A : Subgroup Five, ∃ _hA : AltFive ≤ A, (A = ⊤ ∨ A = AltFive) ∧
      ∃ e : D ≃* Three × A,
      ∃ f : W ≃ₗ[ZMod 2] (BinaryPermutation.core (Fin 3) ⊗[ZMod 2]
        BinaryPermutation.core (Fin 5)),
        ∀ a w, f (ρ a w) = sourceTensorAction
          ((BinaryPermutation.coreRepresentation (Fin 5)).comp A.subtype) (e a) (f w) := by
  obtain ⟨h,j,t,hj,ht,hmark⟩ := hm
  have hd : finrank (ZMod 2) W = 8 := by
    rw [t.finrank_eq,Module.finrank_tensorProduct,BinaryPermutation.finrank_core,
      BinaryPermutation.finrank_core]
    norm_num
  have hr : 3 ≤ Group.rank X := by
    have hb := hyp.dimension_bound.1
    have hh := Group.rank_le_of_surjective (QuotientGroup.mk' X₀)
      (QuotientGroup.mk'_surjective X₀)
    rw [hd] at hb
    omega
  have hA (s : Five) (hs : s ∈ AltFive) : (s,1) ∈ j.range := by
    obtain ⟨a,ha⟩ := h.surjective ⟨s,hs⟩
    exact ⟨a,(hmark a).trans (by rw [ha])⟩
  obtain ⟨A,hAA,hcases,e,he⟩ := tensor_image j hj hA hyp.twoCore_eq_bot X hr
  let c := TensorProduct.comm (ZMod 2) (BinaryPermutation.core (Fin 5))
    (BinaryPermutation.core (Fin 3))
  refine ⟨A,hAA,hcases,e,t.trans c,?_⟩
  intro a w
  change c (t (ρ a w)) = _
  rw [ht]
  have hs (z : BinaryPermutation.core (Fin 5) ⊗[ZMod 2] BinaryPermutation.core (Fin 3)) :
      c (BinaryPermutation.ThreeTensor.action
        (BinaryPermutation.coreRepresentation (Fin 5)) (j a) z) =
      sourceTensorAction ((BinaryPermutation.coreRepresentation (Fin 5)).comp A.subtype)
        (e a) (c z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x y =>
      change (BinaryPermutation.coreRepresentation (Fin 3) (j a).2 y) ⊗ₜ[ZMod 2]
        (BinaryPermutation.coreRepresentation (Fin 5) (j a).1 x) =
        (BinaryPermutation.coreRepresentation (Fin 3) (e a).1 y) ⊗ₜ[ZMod 2]
        (BinaryPermutation.coreRepresentation (Fin 5) (e a).2.val x)
      rw [(he a).1,(he a).2]
  exact hs (t w)
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineTensor

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor CoreGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Identify the literal two-core quotient action in the deleted tensor row. -/
theorem source_deleted_tensor_catalogue (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (H : Subgroup F.TerminalHdot)
    (hm : FixedLineActions.PermutationTensorEmbedding F.terminalRepresentation H
      (BinaryPermutation.coreRepresentation (Fin 5))) :
    letI := chosen.elementary
    letI := F.U_normal
    RankCore.ActionAlternative.{0} (sourceAction F
      (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)) := by
  let := chosen.elementary
  let := F.U_normal
  let hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  obtain ⟨A,hAA,hA,e,f,hf⟩ := FixedLineTensor.five_tensor_coordinates
    F.terminalRepresentation hyp H hm
  let σ := (BinaryPermutation.coreRepresentation (Fin 5)).comp A.subtype
  have hσ : IsSourceConstituent hAA σ :=
    Or.inr ⟨LinearEquiv.refl (ZMod 2) _,fun _ _ => rfl⟩
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  exact .tensor A hAA σ hA hσ (q.trans e) f (fun a w => hf (q a) w)
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
