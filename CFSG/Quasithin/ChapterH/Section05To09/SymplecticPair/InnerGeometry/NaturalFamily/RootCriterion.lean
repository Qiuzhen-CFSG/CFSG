module
public import CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair.InnerGeometry.NaturalFamily.Paired

/-!
# Reduction of the natural family to long-root geometry

Two geometric inputs suffice: every long-root subgroup in the standard
Sylow lies in the plane radical and fixes more than the plane; and any
subgroup of that radical fixing an extra vector lies in such a root.
These inputs give the exact relative-corank criterion, the attaining plane
radical, emptiness of the next family, and the natural parameter 2n.

The two inputs are explicit hypotheses throughout this module. These are
conditional reductions, not yet the unconditional natural-module assertion
in H.7. Their discharge belongs to the concrete long-root geometry and the
final assembly in the parent module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.7,
printed pp.388–389.
-/

public section
namespace CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
open Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

variable
  (hroot : ∀ R : Subgroup (Sp F), IsSylowTransvectionRoot R →
    R ≤ planeRadical ∧ (plane F).restrictScalars (ZMod 2) < fixedSpace (binaryNatural (F := F)) R)
  (hdetect : ∀ D : Subgroup (Sp F), D ≤ planeRadical →
    fixedSpace (binaryNatural (F := F)) D ≠ (plane F).restrictScalars (ZMod 2) →
    ∃ R : Subgroup (Sp F), IsSylowTransvectionRoot R ∧ D ≤ R)

include hdetect in
theorem natural_family_fixedSpace_of_root_detection {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 0 < n)
    {A : Subgroup (Sp F)} (hAU : A ≤ unipotent)
    (hA : A ∈ ChapterE.fixedSpaceFamily (binaryNatural (F := F)) (2*n)) :
    fixedSpace (binaryNatural (F := F)) A = (plane F).restrictScalars (ZMod 2) := by
  by_contra hne
  obtain ⟨R,hR,hAR⟩ := hdetect A
    (natural_family_le_planeRadical hF (by omega) hAU hA) hne
  have hlow := ChapterE.parameter_le_rank_of_mem_fixedSpaceFamily (binaryNatural (F := F))
    (natural_injective (F := F)) hA
  have hupp := hR.rank_le hF hAR
  omega

include hroot hdetect in
theorem natural_mem_iff_of_root_geometry {n : ℕ} (hF : Nat.card F = 2^n)
    (hn : 0 < n) {A : Subgroup (Sp F)} (hAU : A ≤ unipotent) :
    A ∈ ChapterE.fixedSpaceFamily (binaryNatural (F := F)) (2*n) ↔
      IsElementaryTwo A ∧ A ≤ planeRadical ∧
        ∀ R : Subgroup (Sp F), IsSylowTransvectionRoot R →
          Nat.log 2 ((A ⊓ R).relIndex A) = 2*n := by
  constructor
  · intro hA
    have hAP := natural_family_le_planeRadical hF (by omega) hAU hA
    have hfix := natural_family_fixedSpace_of_root_detection hdetect hF hn hAU hA
    refine ⟨hA.2.1,hAP,?_⟩
    intro R hR
    have hupper := Nat.log_mono_right (b := 2)
      (Subgroup.relIndex_le_of_le_right (H := R) hAP (by
        rw [hR.relIndex_planeRadical (hroot R hR).1]
        exact (pow_pos (Nat.card_pos (α := F)) 2).ne'))
    rw [hR.log_relIndex_planeRadical hF (hroot R hR).1] at hupper
    apply le_antisymm (by simpa only [Subgroup.inf_relIndex_left] using hupper)
    by_contra hc
    have he := hA.2.2 (A ⊓ R) inf_le_left (Nat.lt_of_not_ge hc)
    have hle : fixedSpace (binaryNatural (F := F)) R ≤ (plane F).restrictScalars (ZMod 2) := by
      rw [← hfix,he]
      exact ChapterE.fixedSpace_antitone _ inf_le_right
    exact (not_le_of_gt (hroot R hR).2) hle
  · rintro ⟨hAe,hAP,hquot⟩
    have hfix (D : Subgroup (Sp F)) (hDA : D ≤ A)
        (hD : Nat.log 2 (D.relIndex A) < 2*n) :
        fixedSpace (binaryNatural (F := F)) D = (plane F).restrictScalars (ZMod 2) := by
      by_contra hne
      obtain ⟨R,hR,hDR⟩ := hdetect D (hDA.trans hAP) hne
      have hle := Nat.log_mono_right (b := 2)
        (Subgroup.relIndex_le_of_le_left (L := A) hDR (by
          intro hz
          have hh := D.relIndex_dvd_card A
          rw [hz,zero_dvd_iff] at hh
          exact Nat.card_pos.ne' hh))
      have he := hquot R hR
      rw [Subgroup.inf_relIndex_left] at he
      omega
    refine ⟨by omega,hAe,?_⟩
    intro D hDA hD
    exact (hfix A le_rfl (by simp; omega)).trans (hfix D hDA hD).symm

include hroot hdetect in
theorem planeRadical_mem_natural_family_of_root_geometry {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 0 < n) :
    planeRadical (F := F) ∈ ChapterE.fixedSpaceFamily (binaryNatural (F := F)) (2*n) := by
  apply (natural_mem_iff_of_root_geometry hroot hdetect hF hn planeRadical_le_unipotent).mpr
  refine ⟨⟨?_,planeRadical_elementary⟩,le_rfl,?_⟩
  · intro h
    have hr := rank_planeRadical hF
    rw [h,Representation.BinaryOffender.rank_bot] at hr
    omega
  · intro R hR
    rw [Subgroup.inf_relIndex_left]
    exact hR.log_relIndex_planeRadical hF (hroot R hR).1

include hroot hdetect in
theorem natural_next_family_empty_of_root_geometry {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 0 < n) :
    ChapterE.fixedSpaceFamily (binaryNatural (F := F)) (2*n+1) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro A hA
  let : IsElementaryAbelian 2 A := hA.2.1.2
  obtain ⟨S,hS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp F) S (unipotentSylow hF hn)
  have hs : (S : Subgroup (Sp F)).map (MulAut.conj g).toMonoidHom = unipotent :=
    congrArg (fun T : Sylow 2 (Sp F) => (T : Subgroup (Sp F))) hg
  let B := A.map (MulAut.conj g).toMonoidHom
  have hBU : B ≤ unipotent := hs ▸ Subgroup.map_mono hS
  have hB := ChapterE.ValueBound.fixedSpaceFamily_conjugationInvariant
    (binaryNatural (F := F)) (2*n+1) A hA g
  have hB' := ChapterE.fixedSpaceFamily_mono (binaryNatural (F := F))
    (by omega : 0 < 2*n) (by omega : 2*n ≤ 2*n+1) hB
  have hf := natural_family_fixedSpace_of_root_detection hdetect hF hn hBU hB'
  have hroot0 := root_zero_isSylowTransvectionRoot (F := F)
  have hi := ((natural_mem_iff_of_root_geometry hroot hdetect hF hn hBU).mp hB').2.2
    _ hroot0
  have he := hB.2.2 (B ⊓ RootSubgroup.group 0) inf_le_left (by rw [hi]; omega)
  have hle : fixedSpace (binaryNatural (F := F)) (RootSubgroup.group (F := F) 0) ≤
      (plane F).restrictScalars (ZMod 2) := by
    rw [← hf,he]
    exact ChapterE.fixedSpace_antitone _ inf_le_right
  exact (not_le_of_gt (hroot _ hroot0).2) hle

include hroot hdetect in
theorem natural_moduleA_eq_of_root_geometry {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 0 < n) :
    ChapterE.moduleA (binaryNatural (F := F)) = (2*n : ℕ) := by
  apply le_antisymm
  · exact (ChapterE.moduleA_le_iff_next_family_empty (binaryNatural (F := F)) (2*n)).mpr
      (natural_next_family_empty_of_root_geometry hroot hdetect hF hn)
  · exact ChapterE.le_moduleA_of_mem (binaryNatural (F := F))
      (planeRadical_mem_natural_family_of_root_geometry hroot hdetect hF hn)

end CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
