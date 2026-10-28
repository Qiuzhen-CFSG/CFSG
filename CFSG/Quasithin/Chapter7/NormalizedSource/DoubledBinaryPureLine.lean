module
public import CFSG.Quasithin.Chapter7.Section01To05.FixedSpaceSpan
public import Theory.ElementaryAbelian.Injective
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.PSL3Two.FourGroupGeometry.Normalizers.FourGroupCoverage
public import Theory.Representation.PSL3Two.NaturalDualNormalizer

/-!
# The pure line of a binary doubled offender

An inner four-group can be carried to the point translation group by an
actual automorphism of SL₃(2). Its nonidentity element fixed spaces lie in
the sum of the natural three-space and the dual annihilator plane. Every
point translation displaces this hyperplane into the pure natural line.
The natural–dual implementation of an automorphism preserves or exchanges
the two factors, so transporting back retains a single pure-factor line.

The ambient commutator lemma applies this bound to the literal normalizer
homomorphism and fixed-space span. `NonFFSourceDoubledBinaryPureLine` uses
the existing nontrivial shared commutator to prove equality with that line,
for the same offender pair and the two original marked seed subgroups.
Source: Aschbacher–Smith H.4.3(2) and the proof of 7.6.1, printed pp.380,702,
refs/quasithin.pdf. Characteristic two of its centralizer is a separate
ambient source argument.
-/

public noncomputable section
open Representation Representation.BinaryOffender Subgroup
open scoped Matrix IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureLine
open BinaryLinearThree BinaryLinearThree.NaturalDual
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms

private def v₀ : Vector := ![1,0,0]
private def line : Submodule (ZMod 2) Space :=
  Submodule.span (ZMod 2) {(v₀,0)}
private def hyperplane : Submodule (ZMod 2) Space :=
  (⊤ : Submodule (ZMod 2) Vector).prod (LinearMap.ker (Module.Dual.eval (ZMod 2) Vector v₀))

private theorem point_displacement : ∀ g : SL, g ∈ pointV → ∀ v : Vector,
    ∃ c : ZMod 2, g.val *ᵥ v - v = c • v₀ := by decide +kernel
private theorem point_hits : ∀ g : SL, g ∈ pointV → g ≠ 1 →
    ∃ v : Vector, g.val *ᵥ v - v = v₀ := by decide +kernel

private theorem point_dual_fixed (g : SL) (hg : g ∈ pointV)
    (f : Module.Dual (ZMod 2) Vector) (hf : f v₀ = 0) : W.dual g f = f := by
  apply LinearMap.ext
  intro v
  obtain ⟨c,hc⟩ := point_displacement g⁻¹ (pointV.inv_mem hg) v
  have hh := congrArg f hc
  simp only [map_sub, map_smul, hf, smul_zero, sub_eq_zero] at hh
  exact hh

private theorem point_fixed_le (g : SL) (hg : g ∈ pointV) (hne : g ≠ 1) :
    fixedSpace action (zpowers g) ≤ hyperplane := by
  intro v hv
  have hh := congrArg Prod.snd ((mem_fixedSpace_zpowers_iff action g v).mp hv)
  change W.dual g v.2 = v.2 at hh
  obtain ⟨x,hx⟩ := point_hits g⁻¹ (pointV.inv_mem hg) (inv_ne_one.mpr hne)
  have hx' := congrArg v.2 hx
  have hf := LinearMap.congr_fun hh x
  change v.2 (g⁻¹.val *ᵥ x) = v.2 x at hf
  refine ⟨Submodule.mem_top, ?_⟩
  change v.2 v₀ = 0
  rw [←hx',map_sub,hf,sub_self]

private theorem point_moves (g : SL) (hg : g ∈ pointV) (v : Space)
    (hv : v ∈ hyperplane) : action g v - v ∈ line := by
  obtain ⟨c,hc⟩ := point_displacement g hg v.1
  apply Submodule.mem_span_singleton.mpr
  refine ⟨c,?_⟩
  apply Prod.ext
  · exact hc.symm
  · change c • (0 : Module.Dual (ZMod 2) Vector) = W.dual g v.2 - v.2
    rw [smul_zero,point_dual_fixed g hg v.2 hv.2,sub_self]

private theorem card_line : Nat.card line = 2 := by
  have hn : (v₀, (0 : Module.Dual (ZMod 2) Vector)) ≠ 0 := by
    intro he
    exact (by decide : v₀ ≠ 0) (congrArg Prod.fst he)
  have hd : Module.finrank (ZMod 2) line = 1 := by
    exact finrank_span_singleton hn
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
  rfl

private theorem implementer (α : MulAut Group) :
    ∃ d : Space ≃ₗ[ZMod 2] Space,
      (∀ g v, d (action g v) = action (α g) (d v)) ∧
      ((∀ v, (d v).2 = 0 → v.2 = 0) ∨ (∀ v, (d v).2 = 0 → v.1 = 0)) := by
  by_cases hi : α ∈ MulAut.innerSubgroup Group
  · obtain ⟨g,rfl⟩ := hi
    refine ⟨innerOperator g,innerOperator_covariance g,Or.inl ?_⟩
    intro v hv
    exact (W.dual.apply_bijective g).injective (hv.trans (map_zero _).symm)
  · obtain ⟨g,hg⟩ := AutomorphismAction.outer_eq_inner_graph α hi
    refine ⟨graphSwap.trans (innerOperator g),?_,Or.inr ?_⟩
    · intro k v
      change innerOperator g (graphSwap (action k v)) = _
      rw [graphSwap_covariance,innerOperator_covariance,hg]
      rfl
    · intro v hv
      have hh : AutomorphismAction.graphNaturalDual v.1 = 0 :=
        (W.dual.apply_bijective g).injective (hv.trans (map_zero _).symm)
      exact AutomorphismAction.graphNaturalDual.toLinearEquiv.map_eq_zero_iff.mp hh

private theorem span_displacement
    {H U : Type*} [_root_.Group H] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (A : Subgroup H)
    (e : A ≃* pointV) (E : U ≃ₗ[ZMod 2] Space)
    (hE : ∀ a : A, ∀ v, E (ρ a v) = action (e a) (E v)) :
    ∀ a ∈ A, ∀ v ∈ fixedSpaceSpan ρ A, E (ρ a v - v) ∈ line := by
  have hspan : fixedSpaceSpan ρ A ≤ hyperplane.comap E.toLinearMap := by
    apply fixedSpaceSpan_le
    intro a ha hne v hv
    apply point_fixed_le (e ⟨a,ha⟩) (e ⟨a,ha⟩).property
      (fun he => hne (congrArg Subtype.val (e.injective ((Subtype.ext he).trans e.map_one.symm))))
    rw [mem_fixedSpace_zpowers_iff]
    exact (hE ⟨a,ha⟩ v).symm.trans (congrArg E ((mem_fixedSpace_zpowers_iff ρ a v).mp hv))
  intro a ha v hv
  rw [map_sub,hE ⟨a,ha⟩]
  exact point_moves (e ⟨a,ha⟩) (e ⟨a,ha⟩).property (E v) (hspan hv)

/-- The displacement of the entire fixed-space span of an inner four-group
lies in a single line in one of the two original coordinate factors. -/
theorem four_span_line
    {H J U : Type*} [_root_.Group H] [_root_.Group J]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (i : J →* H)
    (q : J →* Group) (hq : Function.Surjective q)
    (E : U ≃ₗ[ZMod 2] Space)
    (hE : ∀ j v, E (ρ (i j) v) = action (q j) (E v))
    (f : H ≃* MulAut Group) (hf : ∀ j, f (i j) = MulAut.conj (q j))
    (A : Subgroup H) (hAI : ∀ a ∈ A, f a ∈ MulAut.innerSubgroup Group)
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 4) :
    ∃ P : Submodule (ZMod 2) U, Nat.card P = 2 ∧
      (∀ a ∈ A, ∀ v ∈ fixedSpaceSpan ρ A, ρ a v - v ∈ P) ∧
      ((∀ v ∈ P, (E v).2 = 0) ∨ (∀ v ∈ P, (E v).1 = 0)) := by
  let j : Group →* H := f.symm.toMonoidHom.comp MulAut.conj
  have hj : Function.Injective j := f.symm.injective.comp
    (MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot)
  have hact (g : Group) (v : U) : E (ρ (j g) v) = action g (E v) := by
    obtain ⟨x,rfl⟩ := hq g
    change E (ρ (f.symm (MulAut.conj (q x))) v) = _
    rw [← hf x,f.symm_apply_apply]
    exact hE x v
  let C := A.comap j
  have hm : C.map j = A := map_comap_eq_self (by
    intro a ha
    obtain ⟨g,hg⟩ := hAI a ha
    exact ⟨g,by change f.symm (MulAut.conj g) = a; rw [hg,f.symm_apply_apply]⟩)
  let c : C ≃* A := (C.equivMapOfInjective j hj).trans (MulEquiv.subgroupCongr hm)
  let : IsElementaryAbelian 2 A := hA
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.comap_of_injective j hj A
  have hC : Nat.card C = 4 := (Nat.card_congr c.toEquiv).trans hc
  obtain ⟨α,hα⟩ := BinaryLinearThree.FourGroupGeometry.Normalizers.fourGroup_map_point C hC
  obtain ⟨d,hd,hdaxis⟩ := implementer α
  let eC : C ≃* pointV := (α.subgroupMap C).trans (MulEquiv.subgroupCongr hα)
  let e : A ≃* pointV := c.symm.trans eC
  let E' := E.trans d
  have hE' (a : A) (v : U) : E' (ρ a v) = action (e a) (E' v) := by
    obtain ⟨x,rfl⟩ := c.surjective a
    change E' (ρ (c x) v) = action (eC (c.symm (c x))) (E' v)
    rw [c.symm_apply_apply]
    change d (E (ρ (j x) v)) = action (α x) (d (E v))
    rw [hact,hd]
  let P := line.comap E'.toLinearMap
  have hcard : Nat.card P = 2 :=
    (Nat.card_congr (E'.toEquiv.subtypeEquiv (fun _ => Iff.rfl))).trans card_line
  have haxis (v : U) (hv : v ∈ P) : (d (E v)).2 = 0 := by
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hv
    change a • (v₀,0) = E' v at ha
    change (E' v).2 = 0
    rw [←ha]
    simp
  refine ⟨P,hcard,span_displacement ρ A e E' hE',?_⟩
  rcases hdaxis with hn | hd
  · exact Or.inl (fun v hv => hn (E v) (haxis v hv))
  · exact Or.inr (fun v hv => hd (E v) (haxis v hv))

open Chapter7 ChapterE
open scoped commutatorElement

/-- The model displacement bound controls the literal ambient group commutator. -/
theorem ambient_span_commutator_le
    {G : Type*} [_root_.Group G] (W A : Subgroup G) [IsElementaryAbelian 2 W]
    (hAN : A ≤ normalizer (W : Set G))
    (P : Submodule (ZMod 2) (Additive W))
    (hP : ∀ a ∈ inducedAutomizer W A,
      ∀ v ∈ fixedSpaceSpan (automizerRepresentation W) (inducedAutomizer W A),
      automizerRepresentation W a v - v ∈ P) :
    ⁅A,ambientSubmodule W (fixedSpaceSpan (automizerRepresentation W) (inducedAutomizer W A))⁆ ≤
      ambientSubmodule W P := by
  apply commutator_le.mpr
  intro a ha b hb
  obtain ⟨v,hv,rfl⟩ := hb
  let k : Automizer W := W.normalizerMonoidHom.rangeRestrict ⟨a,hAN ha⟩
  have hk : k ∈ inducedAutomizer W A := ⟨⟨a,hAN ha⟩,ha,rfl⟩
  let u : Additive W := automizerRepresentation W k (Additive.ofMul v) - Additive.ofMul v
  have hu : u ∈ P := hP k hk _ hv
  refine ⟨u.toMul,hu,?_⟩
  change (a * (v : G) * a⁻¹) / v = ⁅a,(v : G)⁆
  rw [div_eq_mul_inv,commutatorElement_def]

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureLine
