module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOuterFixed
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOuterSize
public import Theory.GroupTheory.DihedralCentralProductThree
import Theory.Representation.BinaryConjugationSection.NoTransvection
import Theory.Representation.HexacodeAction.NoTransvections

/-!
# The actual outer closure is extraspecial of plus type

Its Sylow centralizer normalizes the chosen U and has displacement in
C_U(W)=<z>. Absence of hexacode transvections forces this centralizer into
C_G(U)=U, hence it equals <z>. Thus the actual center of W is <z>.
The already proved elementary central quotient and original elementary
intersection of order16 identify W as the threefold dihedral product.

Source: Aschbacher--Smith, conclusion following12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource ChapterE Atlas.Codes
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The whole original W has center <z>, is Sylow centric, and is extraspecial
of plus type through its actual elementary intersection with U. -/
theorem original_tripleSix_central_closure_outer_extraspecial
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧ RankOneModule.SmallExit T (localResidual H))
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let C := centralizer ({(z:G)} : Set G)
    let J := tripleSixWeightFourResidual K z
    let R := conjugateSpanBy U C
    let H := R ⊔ J ⊔ (T : Subgroup G)
    let W := conjugateSpanBy (tripleSixPoint D a z) R
    let Z := zpowers (z:G)
    W ≤ (T : Subgroup G) ∧ H ≤ normalizer (W : Set G) ∧
      Nat.card W = 128 ∧ Nat.card (U ⊓ W : Subgroup G) = 16 ∧
      (T : Subgroup G) ⊓ centralizer (W : Set G) = Z ∧
      (center W).map W.subtype = Z ∧ IsExtraspecial 2 W ∧
      Nonempty (W ≃* DihedralCentralProductThree.Model) := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let Z := zpowers (z:G)
  obtain ⟨hI, hWcard, hHW, hZN, he, hquot, _⟩ :=
    original_tripleSix_central_closure_outer_size
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  let : (Z.subgroupOf W).Normal := hZN
  let := he
  have hCU : centralizer (U : Set G) = U :=
    (original_tripleSix_central_closure_core_recovery
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter).2.2.2.2.1
  have hfix : U ⊓ centralizer (W : Set G) = Z :=
    original_tripleSix_central_closure_outer_fixed h structural D a z hz hzT hnot houter
  obtain ⟨hWT, f, _, _, _, hchart, _⟩ :=
    original_tripleSix_central_closure_outer_model h structural D a z hz hzT hnot houter
  have hTN : (T : Subgroup G) ≤ normalizer (U : Set G) := ((structural K h).2.2 U D).1
  have hUH : U ≤ H := D.le_sylow.trans le_sup_right
  have hUC : U ≤ normalizer (centralizer (W : Set G) : Set G) :=
    (hUH.trans hHW).trans (normalizer_le_normalizer_centralizer _)
  let B := (T : Subgroup G) ⊓ centralizer (W : Set G)
  have hc : ⁅B,U⁆ ≤ Z := by
    rw [←hfix]
    apply le_inf
    · rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans hTN)
    · exact (commutator_mono inf_le_right le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hUC)
  let c := tripleSixPointCoordinates D a
  let N := normalizer (U : Set G)
  let q := U.normalizerMonoidHom.rangeRestrict
  let ρ := Hexacode.action.comp (f.comp q)
  let d : BinaryConjugationSection N U ⊥ ρ := {
    section_le := U.le_normalizer
    kernel_le := bot_le
    normalized := le_rfl
    coordinates := c.toMonoidHom
    onto := c.surjective
    kernel_eq := by
      rw [bot_subgroupOf]
      exact c.toMonoidHom.ker_eq_bot_iff.mpr c.injective
    equivariant := fun n u => hchart (q n) u }
  have hno (x : N) : fixedCodim ρ (zpowers x) ≠ 1 := by
    change fixedCodim (Hexacode.action.comp (f.comp q)) (zpowers x) ≠ 1
    unfold fixedCodim
    rw [fixedSpace_comp_map, MonoidHom.map_zpowers]
    exact Hexacode.no_transvections (f (q x))
  let := D.elementary
  have ho : orderOf (z:G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (z:G) z.property)
    (fun hh => hz (Subtype.ext hh))
  have hZcard : Nat.card Z = 2 := by rw [Nat.card_zpowers, ho]
  have hBCU : B ≤ centralizer (U : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    exact bot_unique (d.commutator_le_kernel_of_card_two_of_no_transvections hno B Z
      (inf_le_left.trans hTN) hZcard hc)
  have hB : B = Z := by
    apply le_antisymm
    · exact (le_inf (hBCU.trans_eq hCU) inf_le_right).trans_eq hfix
    · rw [←hfix]
      exact inf_le_inf_right _ D.le_sylow
  have hp := tripleSixPoint_properties D a z hz
  have hZW : Z ≤ W := (zpowers_le.mpr hp.1).trans (le_conjugateSpanBy V1 R)
  have hcenter : (center W).map W.subtype = Z := by
    apply le_antisymm
    · rintro x ⟨w, hw, rfl⟩
      apply hB.le
      refine ⟨hWT w.property, ?_⟩
      intro y hy
      exact congrArg Subtype.val (mem_center_iff.mp hw ⟨y, hy⟩)
    · intro x hx
      refine ⟨⟨x, hZW hx⟩, ?_, rfl⟩
      apply mem_center_iff.mpr
      intro w
      exact Subtype.ext ((hB.ge hx).2 w w.property)
  have hcenter' : center W = Z.subgroupOf W := by
    apply map_injective W.subtype_injective
    rw [hcenter, map_subgroupOf_eq_of_le hZW]
  have hcentercard : Nat.card (center W) = 2 := by
    rw [hcenter', Nat.card_congr (subgroupOfEquivOfLe hZW).toEquiv, hZcard]
  have hnon : Nontrivial (W ⧸ center W) := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [hcenter', hquot]
    decide
  have hecenter : IsElementaryAbelian 2 (W ⧸ center W) :=
    IsElementaryAbelian.of_injective
      (QuotientGroup.quotientMulEquivOfEq hcenter').toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq hcenter').injective
  let hex : IsExtraspecial 2 W := ⟨hcentercard, hecenter, hnon⟩
  let I := (U ⊓ W : Subgroup G).subgroupOf W
  let : IsElementaryAbelian 2 (U ⊓ W : Subgroup G) := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 I := IsElementaryAbelian.subgroupOf inf_le_right
  have hIc : Nat.card I = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show U ⊓ W ≤ W from inf_le_right)).toEquiv).trans hI
  have hZI : center W ≤ I := by
    rw [hcenter']
    exact subgroupOf_mono W (le_inf (zpowers_le.mpr z.property) hZW)
  exact ⟨hWT, hHW, hWcard, hI, hB, hcenter, hex,
    DihedralCentralProductThree.exists_mulEquiv_of_elementary_sixteen hWcard I hIc hZI⟩

end CFSG.Quasithin.Chapter12.Section07
