module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSpanSize
import all CFSG.Quasithin.Chapter14.Section06.SourceQuinticKernelRadicals

/-!
# The actual elementary span has a one-dimensional full-kernel image

The reciprocal intersection moves the original central line, so the whole
elementary span has the same nonzero commutator. Its intersection with the
original span is a hyperplane and is fixed pointwise. The binary commutator
row therefore gives index two over the literal full centralizer kernel.

The internal import reuses the two generic hyperplane calculations already
used for the original critical pair. No bound on the full kernel is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The selected elementary middle span has exactly a line as its image
over the full centralizer of the original quintic span. -/
theorem source_quintic_second_kernel_span_line
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (localModule T M) H
    let C := H ⊓ centralizer (U : Set G)
    ∃ g ∈ X,
      let Ustar := U.map (MulAut.conj g).toMonoidHom
      let Qstar := (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom
      let R := U ⊓ Qstar
      let Rstar := Ustar ⊓ H.pCoreIn 2
      let W := conjugateSpanBy R X
      IsElementaryAbelian 2 W ∧ W ≤ H.pCoreIn 2 ⊓ X.pCoreIn 2 ∧
        X ≤ normalizer (W : Set G) ∧ W ⊓ U = R ∧ W ⊓ Ustar = Rstar ∧
        Nat.card R = 16 ∧ Nat.card Rstar = 16 ∧ 32 ≤ Nat.card W ∧
        ⁅W,U⁆ = centralInvolutions T ∧ U ⊓ centralizer (W : Set G) = R ∧
        (W ⊓ C).relIndex W = 2 ∧ 2 * Nat.card (W ⊓ C : Subgroup G) = Nat.card W ∧
        (Nat.card W ≤ 32 → W ⊓ C = R ∧ ⁅W,H.pCoreIn 2⁆ ≤ U) := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  let Z := centralInvolutions T
  obtain ⟨g,hg,hWel,hWQ,hXW,hWU,hWUstar,hRW,hmove,hRcard,hRstarcard,hWcard⟩ :=
    source_quintic_second_kernel_span_size hG T hempty hM hu hmany hcard e H hH hi
  let Ustar := U.map (MulAut.conj g).toMonoidHom
  let Qstar := Q.map (MulAut.conj g).toMonoidHom
  let R := U ⊓ Qstar
  let Rstar := Ustar ⊓ Q
  let W := conjugateSpanBy R X
  let : IsElementaryAbelian 2 W := hWel
  have hUQ : U ≤ Q := by
    obtain ⟨he,F,hp,_,_,hloc⟩ := Section02.source_lemma_14_2_6
      hG T hempty hM hu hmany hcard e
    let := he
    obtain ⟨_,hl,_,_,_,_⟩ := hloc H hH.1
    have hh := hl.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [Section02.rankTwoSeed_eq_localModule] using hh
  have hQT : Q ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow H (T.subtype hH.1.1.2)).trans_eq
      (map_subgroupOf_eq_of_le hH.1.1.2)
  have hcomm : ⁅U,Q⁆ = Z :=
    (source_quintic_core_commutators hG T hempty hM hu hmany hcard e H hH hi).2
  have hWZ : ⁅W,U⁆ ≤ Z := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl (hWQ.trans inf_le_left)).trans hcomm.le
  have hnonzero : ⁅W,U⁆ ≠ ⊥ := by
    intro hz
    exact hmove (bot_unique ((commutator_mono hRW le_rfl).trans hz.le))
  have hZcard : Nat.card Z = 2 := plane_centralInvolutions_card T M hM.1.2 hcard e
  have hWcomm : ⁅W,U⁆ = Z := by
    apply eq_of_le_of_card_ge hWZ
    rw [hZcard]
    have hp : 0 < Nat.card (⁅W,U⁆ : Subgroup G) := Nat.card_pos
    have hn : Nat.card (⁅W,U⁆ : Subgroup G) ≠ 1 :=
      fun h => hnonzero (card_eq_one.mp h)
    omega
  have hZW : Z ≤ W := hWcomm ▸
    le_normalizer_iff_commutator_le_left.mp ((hUQ.trans (hQT.trans le_sup_right)).trans hXW)
  have hRle : R ≤ W := le_conjugateSpanBy _ _
  have hWR : ⁅W,R⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    ((le_centralizer W).trans (centralizer_le hRle))
  have hRindex : R.relIndex U = 2 := by
    have hh := relIndex_mul_card_of_le (show R ≤ U from inf_le_left)
    rw [hRcard,
      (source_quintic_span_card_and_core_radical hG T hempty hM hu hmany hcard e H hH hi).1] at hh
    omega
  have hUC : U ⊓ centralizer (W : Set G) = R :=
    centralizer_hyperplane_eq U R W Z inf_le_left hRindex
      ((commutator_comm R W).trans hWR) ((commutator_comm U W).trans hWcomm) hZcard
  have hrow : (centralizer (U : Set G)).relIndex W = 2 :=
    binary_row_index_two W U R Z inf_le_left hRindex hWR hWcomm hZW hZcard
  have hWC : W ⊓ C = W ⊓ centralizer (U : Set G) := by
    change W ⊓ (H ⊓ centralizer (U : Set G)) = _
    rw [←inf_assoc,inf_eq_left.mpr ((hWQ.trans inf_le_left).trans (pCoreIn_le 2 H))]
  have hindex : (W ⊓ C).relIndex W = 2 := by
    rw [hWC,inf_relIndex_left]
    exact hrow
  have hkernelcard : 2 * Nat.card (W ⊓ C : Subgroup G) = Nat.card W := by
    have hh := relIndex_mul_card_of_le (show W ⊓ C ≤ W from inf_le_left)
    rwa [hindex] at hh
  have hsmall (hsize : Nat.card W ≤ 32) : W ⊓ C = R ∧ ⁅W,Q⁆ ≤ U := by
    let : IsElementaryAbelian 2 U :=
      (Section02.SolvableAmalgam.source_index_five_closure_structure
        hG T hempty hM hu hmany hcard e H hH.1 hi).1
    have hUCle : U ≤ C := le_inf (hUQ.trans (pCoreIn_le 2 H)) (le_centralizer U)
    have hRWC : R ≤ W ⊓ C := le_inf hRle (inf_le_left.trans hUCle)
    have hRsize : Nat.card R = 16 := hRcard
    have hWCeq : W ⊓ C = R :=
      (eq_of_le_of_card_ge hRWC (by rw [hRsize]; omega)).symm
    obtain ⟨_,hN,hE,_⟩ := source_quintic_full_kernel_elementary_quotient
      hG T hempty hM hu hmany hcard e H hH hi
    let := hN
    let := hE
    have hQQ : ⁅Q,Q⁆ ≤ C := by
      have hh : _root_.commutator Q ≤ C.subgroupOf Q :=
        (Subgroup.Normal.quotient_commutative_iff_commutator_le
          (N := C.subgroupOf Q)).mp inferInstance
      have hm := map_mono (f := Q.subtype) hh
      rw [map_subtype_commutator,subgroupOf_map_subtype] at hm
      exact hm.trans inf_le_left
    refine ⟨hWCeq,?_⟩
    calc
      ⁅W,Q⁆ ≤ W ⊓ C := le_inf
        (le_normalizer_iff_commutator_le_left.mp ((hQT.trans le_sup_right).trans hXW))
        ((commutator_mono (hWQ.trans inf_le_left) le_rfl).trans hQQ)
      _ = R := hWCeq
      _ ≤ U := inf_le_left
  exact ⟨g,hg,hWel,hWQ,hXW,hWU,hWUstar,hRcard,hRstarcard,hWcard,
    hWcomm,hUC,hindex,hkernelcard,hsmall⟩

end CFSG.Quasithin.Chapter14.Section06
