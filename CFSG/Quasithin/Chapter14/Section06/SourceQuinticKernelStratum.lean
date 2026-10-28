module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticKernelOrbit
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# The literal kernel stratum at a reciprocal quintic pair

The canonical orbit support has a concrete central elementary layer.  This
leaf records that layer without imposing a faithful action or an upper bound
on the full radius-two kernel.  The full-Ree branch is therefore retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem span_kernel_normalCore (C W : Subgroup G) :
    C ⊓ centralizer (conjugateSpanBy W C : Set G) =
      (((C ⊓ centralizer (W : Set G)).subgroupOf C).normalCore).map C.subtype := by
  let R := conjugateSpanBy W C
  let K := C ⊓ centralizer (R : Set G)
  let A := (C ⊓ centralizer (W : Set G)).subgroupOf C
  have hCK : C ≤ normalizer (K : Set G) :=
    (le_inf C.le_normalizer ((le_normalizer_conjugateSpanBy W C).trans
      (normalizer_le_normalizer_centralizer R))).trans inf_normalizer_le_normalizer_inf
  let : (K.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer hCK
  have hKA : K.subgroupOf C ≤ A := by
    intro x hx
    exact ⟨hx.1,(centralizer_le (le_conjugateSpanBy W C)) hx.2⟩
  apply le_antisymm
  · have hh := map_mono (f := C.subtype) (normal_le_normalCore.mpr hKA)
    rwa [map_subgroupOf_eq_of_le (show K ≤ C from inf_le_left)] at hh
  · let N := A.normalCore.map C.subtype
    have hNC : N ≤ C := map_subtype_le _
    have hNW : N ≤ centralizer (W : Set G) := by
      rintro _ ⟨x,hx,rfl⟩
      exact (A.normalCore_le hx).2
    have hCN : C ≤ normalizer (N : Set G) := by
      have hh := A.normalCore.le_normalizer_map C.subtype
      simpa only [normalizer_eq_top, ←MonoidHom.range_eq_map, C.range_subtype] using hh
    exact le_inf hNC (le_centralizer_conjugateSpanBy_of_normalizes N W C hCN hNW)

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

/-- The opposite reciprocal module supplies an exact central kernel layer.
The normal-core clause is relative to the literal centralizer `C`; no
faithfulness of the full action on `R` is asserted. -/
theorem source_quintic_full_kernel_stratum
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH.1
    let C := H ⊓ centralizer (D.UH : Set G)
    ∀ i : h.CriticalEndpoint,
      let W := i.conjugate D.UH
      let R := conjugateSpanBy W C
      let S := C ⊔ W
      let K := C ⊓ centralizer (R : Set G)
      let B := D.UH ⊓ centralizer (W : Set G)
      S ≤ normalizer (K : Set G) ∧
      B = D.UH ⊓ K ∧
      B = D.UH ⊓ i.conjugate C ∧
      B ≤ S ⊓ centralizer (S : Set G) ∧
      B.relIndex D.UH = 4 ∧
      (Nat.card B = 8 ∨ Nat.card B = 16) ∧
      C ⊓ R ≤ K ∧
      K = (((C ⊓ centralizer (W : Set G)).subgroupOf C).normalCore).map C.subtype := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH.1
  let C := H ⊓ centralizer (D.UH : Set G)
  change ∀ i : h.CriticalEndpoint, _
  intro i
  let U := D.UH
  let W := i.conjugate U
  let R := conjugateSpanBy W C
  let S := C ⊔ W
  let K := C ⊓ centralizer (R : Set G)
  let B := U ⊓ centralizer (W : Set G)
  obtain ⟨hRe,hWR,hRH,hRL,hSR,hSN,hjoin,hSp,hcomm,hquad,hiS,hsize,hphi⟩ :=
    source_quintic_full_kernel_orbit_support hG T hempty hM hu hmany hcard e hab H hH hi i
  have hUelem : IsElementaryAbelian 2 U :=
    (Section02.SolvableAmalgam.source_index_five_closure_structure
      hG T hempty hM hu hmany hcard e H hH.1 hi).1
  let _ : IsElementaryAbelian 2 U := hUelem
  have hUC : U ≤ C := by
    exact le_inf h.UH_le_H (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hBC : B ≤ centralizer (C : Set G) := by
    exact inf_le_left.trans (le_centralizer_iff.mp
      (show C ≤ centralizer (U : Set G) from inf_le_right))
  have hBW : B ≤ centralizer (W : Set G) := inf_le_right
  have hBspan : B ≤ centralizer (R : Set G) := by
    exact le_centralizer_conjugateSpanBy_of_normalizes B W C
      ((le_centralizer_iff.mp hBC).trans (Subgroup.centralizer_le_normalizer _)) hBW
  have hBUK : B ≤ K := le_inf (inf_le_left.trans hUC) hBspan
  have hUKB : U ⊓ K ≤ B := by
    apply le_inf inf_le_left
    exact (inf_le_right.trans inf_le_right).trans (centralizer_le hWR)
  have hB_eq : B = U ⊓ K := le_antisymm (le_inf inf_le_left hBUK) hUKB
  obtain ⟨hb,_,_,_⟩ := source_quintic_reciprocal_core_hyperplanes
    hG T hempty hM hu hmany hcard e hab H hH hi
  have hUiH : U ≤ i.conjugate H := by
    exact i.reverse_le hb
  have hB_eq_iC : B = U ⊓ i.conjugate C := by
    have hmap : i.conjugate C = i.conjugate H ⊓ centralizer (W : Set G) :=
      (map_inf_centralizer_of_injective (MulAut.conj i.representative).toMonoidHom
        (MulAut.conj i.representative).injective H U).symm
    rw [hmap, ←inf_assoc, inf_eq_left.mpr hUiH]
  obtain ⟨_,_,_,hidx,hor⟩ := source_quintic_full_kernel_radicals
    hG T hempty hM hu hmany hcard e hab H hH hi i
  have hBidx : B.relIndex U = 4 := by
    rw [hB_eq_iC, inf_comm]
    exact hidx
  have hBcard : Nat.card B = 8 ∨ Nat.card B = 16 := by
    rw [hB_eq_iC, inf_comm]
    rcases hor with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
  have hBcentral : B ≤ centralizer (S : Set G) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp hBC) (le_centralizer_iff.mp hBW)
  have hKnorm : S ≤ normalizer (K : Set G) := by
    exact (le_inf hSN (hSR.trans (normalizer_le_normalizer_centralizer R))).trans
      inf_normalizer_le_normalizer_inf
  have hCRK : C ⊓ R ≤ K := by
    let _ : IsElementaryAbelian 2 R := hRe
    exact le_inf inf_le_left (inf_le_right.trans (le_centralizer R))
  exact ⟨hKnorm,hB_eq,hB_eq_iC,
    le_inf ((inf_le_left.trans hUC).trans le_sup_left) hBcentral,
    hBidx,hBcard,hCRK,span_kernel_normalCore C W⟩

end CFSG.Quasithin.Chapter14.Section06
