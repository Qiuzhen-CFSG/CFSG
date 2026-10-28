module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.DualQuotient
public import Theory.Representation.NormalElementaryQuotient.Thompson
public import Theory.Representation.PSL3Two.NaturalDualSections
public import Theory.GroupTheory.NormalClosureCentralizerCore
/-!
# Thompson normality in the contrary-center branch

The original natural subgroup V and involution span Ve form a reduced
LT-module. The literal action on V identifies LT/O₂(LT) with SL₃(2), and
the reducedness and natural centralizer identify the same kernel on VVe.
The dual quotient of Ve then extends across VVe, even when V meets Ve.
The natural/dual fixed-codimension bound excludes every FF offender.
Maximum elementary replacement and Thompson heredity give J(T) normal in LT.

The final application gives J(T) ≤ O₂(I₂T), the precise input used in the
Goldschmidt paragraph of 14.3.31. Both applications extract their involution
from the original nontrivial parabolic center. The explicit seed exclusion
is 14.3.25, still owned by qt-d-hs-centerless-source; this module does not
prove that exclusion or the remaining centerlessness contradictions.
Final local-structure assembly stays with qt-d-hs-local-structure.

Source: Aschbacher--Smith 14.3.29(2) and 14.3.31, printed pp.1002--1003,
refs/quasithin.pdf; B.2.5--8 and the binary natural/dual case of B.5.6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open BinaryLinearThree Representation.BinaryConjugacyOrbit


universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Source 14.3.29(2), retaining the original involution and relative normality. -/
theorem source_involution_thompson_normal (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (e : G) (he : orderOf e = 2)
    (heI : e ∈ Chapter12.Section08.centerIn (F.I₂ L)) (heT : e ∈ sylowOmega T) :
    ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf
      (L ⊔ (T : Subgroup G))).Normal := by
  let := chosen.elementary
  let A := L ⊔ (T : Subgroup G)
  let S : Sylow 2 A := T.subtype le_sup_right
  let X := Span A e
  let E := (V ⊔ X).subgroupOf A
  let D := X.subgroupOf A
  have hXA : X ≤ A := conjugateSpanBy_le_self (zpowers_le.mpr
    (mem_sup_right ((source_center_location d earlier hq chosen structural alternatives F hne).2.1 heI)))
  have hVA : V ≤ A := chosen.le_sylow.trans le_sup_right
  have hEA : V ⊔ X ≤ A := sup_le hVA hXA
  have hspan := source_involution_span_eq d earlier hq chosen structural e heT
  have hE : IsPReduced 2 E := by
    change IsPReduced 2 ((V ⊔ Span A e).subgroupOf A)
    rw [hspan]
    exact source_seed_sup_involution_orbit_reduced d earlier hq chosen structural F e he heT
  have hD : IsPReduced 2 D := by
    change IsPReduced 2 ((Span A e).subgroupOf A)
    rw [hspan]
    exact source_involution_orbit_reduced d earlier hq chosen structural F e he heT
  let := hE.normal
  let := hE.elementary
  let := hD.normal
  let := hD.elementary
  obtain ⟨hX, _, r, hr⟩ := source_involution_dual_quotient d earlier hq chosen structural alternatives F hne hseed e he heI heT
  let := hX
  obtain ⟨β,f,hf,hβ,_,_⟩ := source_marked_plane_action d earlier hq chosen F
  let ν := elementaryRepresentation (p := 2) (F.naturalFlagAction L chosen.normalizes)
  have hfker : f.ker = (F.naturalFlagAction L chosen.normalizes).ker := by
    ext a
    change f a = 1 ↔ F.naturalFlagAction L chosen.normalizes a = 1
    constructor
    · intro ha
      apply MulEquiv.ext
      intro v
      apply Additive.ofMul.injective
      apply β.injective
      have hh := hβ a (Additive.ofMul v)
      rw [ha,map_one] at hh
      exact hh.symm
    · intro ha
      apply natural_injective
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := β.surjective v
      rw [hβ, map_one]
      change β (Additive.ofMul ((F.naturalFlagAction L chosen.normalizes a) w.toMul)) = β w
      rw [ha]
      rfl
  have hkV : f.ker = (centralizer (V : Set G)).subgroupOf A := by
    rw [hfker]
    exact setupSeedAction_ker A V (sup_le chosen.normalizes (by simpa only [F.last] using F.invariant 3))
  have hkcore : f.ker = pCore 2 A := by
    apply map_injective A.subtype_injective
    rw [hkV,subgroupOf_map_subtype,inf_comm]
    exact (higherRankHypothesis d earlier hq chosen).centralizer_LT structural
  have hkE : f.ker = centralizer (E : Set A) := by
    apply le_antisymm
    · rw [hkcore]
      exact le_centralizer_iff.mp hE.le_centralizer_pCore
    · intro a ha
      rw [hkV]
      intro v hv
      exact congrArg Subtype.val (ha ⟨v,hVA hv⟩ (mem_sup_left hv))
  have hkD : f.ker = centralizer (D : Set A) := by
    apply map_injective A.subtype_injective
    rw [hkcore, map_centralizer_subtype, map_subgroupOf_eq_of_le hXA]
    change A.pCoreIn 2 = A ⊓ centralizer (X : Set G)
    rw [show X = conjugateSpanBy (zpowers e) L from hspan]
    exact (source_involution_orbit_centralizer d earlier hq chosen structural alternatives F hne hseed e he heI heT).symm
  let σ := NormalElementaryQuotient.representation E f hf hkE
  let τ := NormalElementaryQuotient.representation D f hf hkD
  let b : Additive D ≃ₗ[ZMod 2] Additive X :=
    LinearEquiv.ofBijective ((subgroupOfEquivOfLe hXA).toMonoidHom.toAdditive.toZModLinearMap 2)
      (subgroupOfEquivOfLe hXA).toAdditive.bijective
  have hb (a : A) (w : Additive D) : b (τ (f a) w) = representation A e a (b w) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((τ (f a) w).toMul : A).val = (a : G) * ((w.toMul : A) : G) * (a : G)⁻¹
    exact congrArg Subtype.val (NormalElementaryQuotient.representation_apply D f hf hkD a w)
  let vmap : V →* E := (subgroupOfEquivOfLe hEA).symm.toMonoidHom.comp (inclusion le_sup_left)
  let vlin := vmap.toAdditive.toZModLinearMap 2
  let il := vlin.comp β.symm.toLinearMap
  have hi : Function.Injective il := by
    intro x y h
    apply β.symm.injective
    exact Additive.toMul.injective (Subtype.ext (congrArg (fun z : Additive E => (z.toMul : A).val) h))
  have hiv (a : A) (v : Additive V) : σ (f a) (vlin v) = vlin (ν a v) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val (NormalElementaryQuotient.representation_apply E f hf hkE a (vlin v))
  let i : W.IntertwiningMap σ := ⟨il, by
    intro g
    obtain ⟨a,rfl⟩ := hf g
    apply LinearMap.ext
    intro v
    change vlin (β.symm (W (f a) v)) = σ (f a) (vlin (β.symm v))
    rw [hiv]
    congr 1
    apply β.injective
    rw [β.apply_symm_apply, ←hβ, β.apply_symm_apply]⟩
  let jl := (inclusion (show D ≤ E from subgroupOf_mono A le_sup_right)).toAdditive.toZModLinearMap 2
  let j : τ.IntertwiningMap σ := ⟨jl, by
    intro g
    obtain ⟨a,rfl⟩ := hf g
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    change (τ (f a) w).toMul.val = (σ (f a) (jl w)).toMul.val
    rw [NormalElementaryQuotient.representation_apply,NormalElementaryQuotient.representation_apply]
    rfl⟩
  have hj : Function.Injective j := by
    intro x y h
    exact Additive.toMul.injective (Subtype.ext (congrArg (fun z : Additive E => (z.toMul : A)) h))
  let pl := β.symm.dualMap.toLinearMap.comp (r.toLinearMap.comp b.toLinearMap)
  let p : τ.IntertwiningMap W.dual := ⟨pl, by
    intro g
    obtain ⟨a,rfl⟩ := hf g
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro v
    change r (b (τ (f a) w)) (β.symm v) = r (b w) (β.symm (W (f a)⁻¹ v))
    rw [hb]
    have hrr := LinearMap.congr_fun (r.isIntertwining' a) (b w)
    have ht := congrArg (fun φ : Module.Dual (ZMod 2) (Additive V) => φ (β.symm v)) hrr
    change r (representation A e a (b w)) (β.symm v) = r (b w) (ν a⁻¹ (β.symm v)) at ht
    rw [ht]
    congr 1
    apply β.injective
    rw [β.apply_symm_apply, ←hβ, map_inv, β.apply_symm_apply]⟩
  have hp : Function.Surjective p := β.symm.dualMap.surjective.comp (hr.comp b.surjective)
  have hs : Function.Surjective (i.toLinearMap.coprod j.toLinearMap) := by
    intro x
    have hx : (x.toMul : A).val ∈ V ⊔ X := x.toMul.property
    let : IsElementaryAbelian 2 (V ⊔ X : Subgroup G) := by
      rw [←map_subgroupOf_eq_of_le hEA]
      exact IsElementaryAbelian.map_subtype
    have hc : X ≤ centralizer (V : Set G) := by
      intro w hw v hv
      exact congrArg Subtype.val (mul_comm (⟨v,mem_sup_left hv⟩ : ↥(V ⊔ X)) ⟨w,mem_sup_right hw⟩)
    change (x.toMul : A).val ∈ ((V ⊔ X : Subgroup G) : Set G) at hx
    rw [coe_mul_of_right_le_normalizer_left V X (hc.trans (Subgroup.centralizer_le_normalizer _))] at hx
    obtain ⟨v,hv,w,hw,heq⟩ := hx
    refine ⟨(β (Additive.ofMul ⟨v,hv⟩),Additive.ofMul ⟨⟨w,hXA hw⟩,hw⟩), ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (β.symm (β (Additive.ofMul ⟨v,hv⟩))).toMul.val * w = _
    rw [β.symm_apply_apply]
    exact heq
  have hn := NaturalDualSections.not_ff_of_spanning_sum σ τ i hi j hj p hp hs
  have hJ := NormalElementaryQuotient.thompson_normal_of_nonFF S E f hf hkE (hkcore ▸ pCore_isPGroup)
    (hE.le_pCore.trans ((pCore_isPGroup (p := 2) (G := A)).le_sylow_of_normal S)) hn
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) := sSup_le fun _ hA => hA.1
  have hjmap : (elementaryAbelianMaxJ (S : Subgroup A)).map A.subtype = elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective A.subtype A.subtype_injective]
    rw [show (S : Subgroup A).map A.subtype = (T : Subgroup G) from map_subgroupOf_eq_of_le le_sup_right]
  have hjeq : elementaryAbelianMaxJ (S : Subgroup A) = (elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [hjmap,map_subgroupOf_eq_of_le (hJT.trans le_sup_right)]
  exact hjeq ▸ hJ

/-- Source 14.3.29(2), applied to the actual nontrivial parabolic center. -/
theorem source_contrary_thompson_normal (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf
      (L ⊔ (T : Subgroup G))).Normal := by
  obtain ⟨e,he,heI,heT,_,_⟩ :=
    source_center_involution d earlier hq chosen structural alternatives F hne hI
  exact source_involution_thompson_normal d earlier hq chosen structural alternatives F hne hseed e he heI heT

/-- The literal Thompson containment used in the Goldschmidt paragraph of 14.3.31. -/
theorem source_contrary_thompson_le_plane_core (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ (F.I₂ L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hn := source_contrary_thompson_normal d earlier hq chosen structural alternatives F hne hseed hI
  have hnorm := (normal_subgroupOf_iff_le_normalizer (hJT.trans le_sup_right)).mp hn
  rw [←source_parabolic_eq_I₂_sylow d earlier hq chosen structural alternatives F hne]
  exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le hJT)
    (hJT.trans (F.binary_sylow_le_P L)) (inf_le_left.trans hnorm)

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
