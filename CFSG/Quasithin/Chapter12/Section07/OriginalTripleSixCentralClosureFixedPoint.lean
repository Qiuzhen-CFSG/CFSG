module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOrbit
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixContainedCubicResidual
import Theory.Representation.BinaryConjugationSection.PlaneResidual

/-!
# The original residual and Sylow fix the generating point

The literal four-group V1 is normalized by the original T and centralized
by the original non-scalar cubic residual. Its image in W/<z> is the
binary point that generates the whole closure module. Normalization of
this actual point therefore gives pointwise fixation in the same faithful
representation, with its complete commutator kernel retained.

Source: Aschbacher--Smith12.7.18, printed p.845.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The same original point spans the closure and is fixed by J*T. -/
theorem original_tripleSix_central_closure_fixed_point
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
        ∃ φ : H →* (Additive (W ⧸ Z.subgroupOf W) ≃ₗ[ZMod 2] Additive (W ⧸ Z.subgroupOf W)),
          (∀ (g : H) (w : W), φ g (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w)) =
            Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(g:G)*w*(g:G)⁻¹,(mem_normalizer_iff.mp (hHW g.property) w).mp w.property⟩)) ∧
          (∀ g : H, g ∈ φ.ker ↔ ∀ w ∈ W, ⁅w,(g:G)⁆ ∈ Z) ∧ pCore 2 φ.range = ⊥ ∧
          ∃ x : Additive (W ⧸ Z.subgroupOf W), x ≠ 0 ∧
            Submodule.span (ZMod 2) {x} = AddSubgroup.toZModSubmodule 2
              (Subgroup.toAddSubgroup ((V1.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W)))) ∧
            Submodule.span (ZMod 2) (Set.range (fun g : φ.range => g.val x)) = ⊤ ∧
            ∀ g : H, (g:G) ∈ J ⊔ (T : Subgroup G) → φ g x = x := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let Z := zpowers (z:G)
  obtain ⟨hHW,hZN,hrest⟩ := original_tripleSix_central_closure_orbit h structural D a z hz hzT hnot
  let : (Z.subgroupOf W).Normal := hZN
  obtain ⟨he,φ,hformula,hker,hcore,x,hx,hspan,horbit⟩ := hrest
  let := he
  refine ⟨hHW,hZN,he,φ,hformula,hker,hcore,x,hx,hspan,horbit,?_⟩
  have hc := original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot
  have hWH : W ≤ H := hc.2.2.1.trans (pCoreIn_le 2 H)
  have hp := tripleSixPoint_properties D a z hz
  have hZV : Z ≤ V1 := zpowers_le.mpr hp.1
  have hVW : V1 ≤ W := le_conjugateSpanBy V1 R
  let V := Additive (W ⧸ Z.subgroupOf W)
  let ρ : Representation (ZMod 2) H V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp φ
  let c : BinaryConjugationSection H W Z ρ :=
    { section_le := hWH
      kernel_le := hZV.trans hVW
      normalized := hHW
      coordinates := QuotientGroup.mk' (Z.subgroupOf W)
      onto := QuotientGroup.mk'_surjective _
      kernel_eq := QuotientGroup.ker_mk' _
      equivariant := fun g w => (hformula g w).symm }
  have hspan' : Submodule.span (ZMod 2) {x} = c.imageSpace V1 := hspan
  have hcard : Nat.card (c.imageSpace V1) = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,←hspan',finrank_span_singleton hx]
    norm_num
  have hJV : J ≤ normalizer (V1 : Set G) :=
    ((original_tripleSix_weightFour_cubic_residual D a z hz hzT).1.trans inf_le_right).trans
      (Subgroup.centralizer_le_normalizer _)
  have hTV : (T : Subgroup G) ≤ normalizer (V1 : Set G) :=
    (original_tripleSix_central_point_g21 h D a z hz hzT).T_normalizes_V
  intro g hg
  exact (c.mem_normalizer_iff_fixed_of_image_card_two V1 hVW hZV hcard x
    (hspan' ▸ Submodule.mem_span_singleton_self x) hx g).mp ((sup_le hJV hTV) hg)

end CFSG.Quasithin.Chapter12.Section07
