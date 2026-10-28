module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureRepresentation
public import Theory.Representation.ConjugateSpanOrbit
import Theory.ElementaryAbelian.EightQuotientRank

/-!
# The original central point generates the closure representation

The original four-group V1 has a two-element image in W/<z>. Its nonzero
vector generates the whole quotient under the literal H-conjugation action,
because the already constructed W is exactly the H-conjugate span of V1.

Source: Aschbacher--Smith 12.7.15--16, printed pp.843--844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual central-closure representation contains the original binary
point V1/<z>, whose nonzero vector has an orbit spanning all of W/<z>. -/
theorem original_tripleSix_central_closure_orbit
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2) :
    let C := centralizer ({(z:G)} : Set G)
    let J := tripleSixWeightFourResidual K z
    let R := conjugateSpanBy U C
    let H := R ⊔ J ⊔ (T : Subgroup G)
    let V1 := tripleSixPoint D a z
    let W := conjugateSpanBy V1 R
    let Z := zpowers (z:G)
    ∃ (hHW : H ≤ normalizer (W : Set G)) (hZN : (Z.subgroupOf W).Normal),
      letI := hZN
      ∃ he : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        letI := he
        ∃ φ : H →* (Additive (W ⧸ Z.subgroupOf W) ≃ₗ[ZMod 2]
          Additive (W ⧸ Z.subgroupOf W)),
          (∀ (g : H) (w : W), φ g (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w)) =
            Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(g:G)*w*(g:G)⁻¹,(mem_normalizer_iff.mp (hHW g.property) w).mp w.property⟩)) ∧
          (∀ g : H, g ∈ φ.ker ↔ ∀ w ∈ W, ⁅w,(g:G)⁆ ∈ Z) ∧
          pCore 2 φ.range = ⊥ ∧
          ∃ x : Additive (W ⧸ Z.subgroupOf W), x ≠ 0 ∧
            Submodule.span (ZMod 2) {x} = AddSubgroup.toZModSubmodule 2
              (Subgroup.toAddSubgroup
                ((V1.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W)))) ∧
            Submodule.span (ZMod 2) (Set.range (fun g : φ.range => g.val x)) = ⊤ := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let Z := zpowers (z:G)
  obtain ⟨hHW,hZN,hrest⟩ :=
    original_tripleSix_central_closure_representation h structural D a z hz hzT hnot
  let : (Z.subgroupOf W).Normal := hZN
  obtain ⟨he,φ,hformula,hker,hcore⟩ := hrest
  let := he
  refine ⟨hHW,hZN,he,φ,hformula,hker,hcore,?_⟩
  let q := QuotientGroup.mk' (Z.subgroupOf W)
  let B := (V1.subgroupOf W).map q
  let P := AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup B)
  have hp := tripleSixPoint_properties D a z hz
  have hZV : Z ≤ V1 := zpowers_le.mpr hp.1
  have hVW : V1 ≤ W := le_conjugateSpanBy V1 R
  have hZW : Z ≤ W := hZV.trans hVW
  have hcardV : Nat.card (V1.subgroupOf W) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVW).toEquiv).trans hp.2.2.1
  have hcardZ : Nat.card (Z.subgroupOf W) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZW).toEquiv]
    let := D.elementary
    have hz1 : (z:G) ≠ 1 := fun he => hz (Subtype.ext he)
    have ho : orderOf (z:G) = 2 :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (z:G) z.property) hz1
    rw [Nat.card_zpowers,ho]
  have hBcard : Nat.card B = 2 := by
    have hm := IsElementaryAbelian.card_inf_ker_mul_card_map (V1.subgroupOf W) q
    have hi : V1.subgroupOf W ⊓ q.ker = Z.subgroupOf W := by
      rw [QuotientGroup.ker_mk',inf_eq_right]
      exact subgroupOf_mono W hZV
    rw [hi,hcardZ,hcardV] at hm
    change 2 * Nat.card B = 4 at hm
    omega
  obtain ⟨b,hb,hunique⟩ := (Nat.card_eq_two_iff' (1 : B)).mp hBcard
  let x := Additive.ofMul (b : W ⧸ Z.subgroupOf W)
  have hx : x ≠ 0 := fun hx => hb (Subtype.ext hx)
  have hcases (y : W ⧸ Z.subgroupOf W) (hy : y ∈ B) : y = 1 ∨ y = b := by
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · exact Or.inr (congrArg Subtype.val (hunique ⟨y,hy⟩
        (fun he => hy1 (congrArg Subtype.val he))))
  have hspan : Submodule.span (ZMod 2) {x} = P := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro y (rfl : y = x)
      exact b.property
    · intro y hy
      rcases hcases y.toMul hy with hy0 | hyx
      · have hy0' : y = 0 := hy0
        rw [hy0']
        exact Submodule.zero_mem _
      · have hyx' : y = x := hyx
        rw [hyx']
        exact Submodule.mem_span_singleton_self x
  have hc := original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot
  have hW : W = conjugateSpanBy V1 H := hc.2.1
  let actor : H →* MulAut (W ⧸ Z.subgroupOf W) :=
    BinaryFixedLine.linearAutEquiv.symm.toMonoidHom.comp φ
  have hequiv (g : H) (w : W) (hw) :
      q ⟨g.val*w.val*g.val⁻¹,hw⟩ = actor g (q w) := by
    have hh := hformula g w
    exact (congrArg Additive.toMul hh).symm
  have hseed (v : V1) : q (inclusion hVW v) = 1 ∨ q (inclusion hVW v) = b :=
    hcases _ (mem_map.mpr ⟨inclusion hVW v,v.property,rfl⟩)
  have ho := conjugateSpan_binary_orbit_span V1 H W hVW hW q
    (QuotientGroup.mk'_surjective _) actor hequiv b hseed
  have horbit : Set.range (fun g : H =>
      elementaryRepresentation (p := 2) actor g (Additive.ofMul (b : W ⧸ Z.subgroupOf W))) =
      Set.range (fun g : φ.range => g.val x) := by
    ext y
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨⟨φ g,MonoidHom.mem_range.mpr ⟨g,rfl⟩⟩,rfl⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨g,hg⟩ := g.property
      exact ⟨g,congrArg (fun f => f x) hg⟩
  rw [horbit] at ho
  exact ⟨x,hx,hspan,ho⟩

end CFSG.Quasithin.Chapter12.Section07
