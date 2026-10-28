module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureAction
public import Theory.GroupAction.BinaryFixedLineQuotient
import Theory.GroupAction.SubgroupQuotientFullAction
import Theory.GroupTheory.CommutatorPreimageFrattini

/-!
# The literal binary representation on W/<z>

The original central closure is a two-group with Frattini subgroup in <z>.
Its quotient is therefore a binary vector space. Conjugation by the actual
H gives the linear representation with exactly the previously constructed
centralizer kernel; its faithful image has trivial two-core.

Source: Aschbacher--Smith12.7.15--16, printed pp.843--844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual closure quotient carries its literal linear conjugation
action, whose faithful image has trivial two-core. -/
theorem original_tripleSix_central_closure_representation
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
    let W := conjugateSpanBy (tripleSixPoint D a z) R
    let Z := zpowers (z:G)
    ∃ (hHW : H ≤ normalizer (W : Set G)) (hZN : (Z.subgroupOf W).Normal),
      letI := hZN
      ∃ he : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        letI := he
        ∃ φ : H →* (Additive (W ⧸ Z.subgroupOf W) ≃ₗ[ZMod 2]
          Additive (W ⧸ Z.subgroupOf W)),
          (∀ (x : H) (w : W), φ x (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w)) =
            Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(x:G)*w*(x:G)⁻¹,(mem_normalizer_iff.mp (hHW x.property) w).mp w.property⟩)) ∧
          (∀ x : H, x ∈ φ.ker ↔ ∀ w ∈ W, ⁅w,(x:G)⁆ ∈ Z) ∧
          pCore 2 φ.range = ⊥ := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let W := conjugateSpanBy (tripleSixPoint D a z) R
  let Z := zpowers (z:G)
  have hc := original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot
  change H ≤ C ∧ W = conjugateSpanBy (tripleSixPoint D a z) H ∧
    W ≤ H.pCoreIn 2 ∧ (frattini W).map W.subtype ≤ Z ∧
    ⁅W,H.pCoreIn 2⁆ ≤ Z ∧ ¬ U ≤ H.pCoreIn 2 ∧ ¬ ⁅U,W⁆ ≤ Z at hc
  have hHW : H ≤ normalizer (W : Set G) := by
    rw [hc.2.1]
    exact le_normalizer_conjugateSpanBy _ _
  have hWH : W ≤ H := hc.2.2.1.trans (pCoreIn_le 2 H)
  have hs := original_tripleSix_central_point_g21_at h D a z hz hzT H le_sup_right hc.1
  have hHZ : H ≤ normalizer (Z : Set G) := hs.H_le
  let hZN : (Z.subgroupOf W).Normal :=
    normal_subgroupOf_of_le_normalizer (hWH.trans hHZ)
  let : (Z.subgroupOf W).Normal := hZN
  have he : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W) :=
    elementary_quotient_of_frattini_le ((isPGroup_pCoreIn 2 H).to_le hc.2.2.1) _
      (map_le_iff_le_comap.mp hc.2.2.2.1)
  let := he
  obtain ⟨β,hβ⟩ := exists_quotient_conjugation_action H W Z hHW hHZ hZN
  let φ := BinaryFixedLine.linearAutEquiv.toMonoidHom.comp β
  have hformula (x : H) (w : W) :
      φ x (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w)) =
        Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W)
          ⟨(x:G)*w*(x:G)⁻¹,(mem_normalizer_iff.mp (hHW x.property) w).mp w.property⟩) :=
    congrArg Additive.ofMul (hβ x w)
  have hk (x : H) : x ∈ φ.ker ↔ ∀ w ∈ W, ⁅w,(x:G)⁆ ∈ Z := by
    have hlin : x ∈ φ.ker ↔ β x = 1 := by
      change BinaryFixedLine.linearAutEquiv (β x) = 1 ↔ β x = 1
      rw [←map_one BinaryFixedLine.linearAutEquiv]
      exact BinaryFixedLine.linearAutEquiv.injective.eq_iff
    rw [hlin]
    constructor
    · intro hx w hw
      have hh := hβ x ⟨w,hw⟩
      rw [hx] at hh
      have hm := QuotientGroup.eq_iff_div_mem.mp hh.symm
      have hm' : ⁅(x:G),w⁆ ∈ Z := by
        simpa only [mem_subgroupOf,commutatorElement_def,div_eq_mul_inv,
          coe_mul,coe_inv] using hm
      simpa only [commutatorElement_inv] using Z.inv_mem hm'
    · intro hx
      ext v
      obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf W) v
      rw [hβ]
      apply QuotientGroup.eq_iff_div_mem.mpr
      have hm : ⁅(x:G),(w:G)⁆ ∈ Z := by
        simpa only [commutatorElement_inv] using Z.inv_mem (hx w w.property)
      simpa only [mem_subgroupOf,commutatorElement_def,div_eq_mul_inv,
        coe_mul,coe_inv] using hm
  obtain ⟨N,hN,hmem,hcore,_⟩ :=
    original_tripleSix_central_closure_action h structural D a z hz hzT hnot
  let : N.Normal := hN
  have hker : φ.ker = N := by ext x; exact (hk x).trans (hmem x).symm
  let e : (H ⧸ N) ≃* φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)
  have hcore' : pCore 2 φ.range = ⊥ := by
    rw [←pCore_map_iso 2 e,hcore,Subgroup.map_bot]
  exact ⟨hHW,hZN,he,φ,hformula,hk,hcore'⟩

end CFSG.Quasithin.Chapter12.Section07
