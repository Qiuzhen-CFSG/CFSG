module
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.NaturalFamily
public import CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair.InnerGeometry.LocalCalculations
public import CFSG.Quasithin.ChapterE.Section04.GenerationSetup

/-!
# The native paired fixed-space bound in H.7

A natural-family member with parameter greater than n fixes the natural
plane, because its intersection with the plane radical has corank at most n.
The first and graph-conjugate summands give the two pointwise stabilizers
for a paired-family member. Their intersection is the actual Sylow center,
where a coordinate root contradicts membership at parameter 2n.

Sylow conjugacy gives emptiness in the full symplectic group. The genuine
commutator inclusion transports the family and its bound to the derived
representation, including the binary case. No full-group witness is put
inside the derived group. The natural parameter equality additionally
requires the classification of extra fixed vectors by long-root subgroups.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.7,
printed pp.388–389.
-/

public section
namespace CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
open Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

theorem natural_family_le_planeRadical {n k : ℕ} (hF : Nat.card F = 2^n)
    (hk : n < k) {A : Subgroup (Sp F)} (hAU : A ≤ unipotent)
    (hA : A ∈ ChapterE.fixedSpaceFamily binaryNatural k) : A ≤ planeRadical := by
  apply (le_planeRadical_iff_plane_fixed hAU).mpr
  have he := hA.2.2 (A ⊓ planeRadical) inf_le_left (by
    rw [Subgroup.inf_relIndex_left]
    exact (log_relIndex_radical_le hF hAU true).trans_lt hk)
  rw [he]
  exact (le_planeRadical_iff_plane_fixed (inf_le_left.trans hAU)).mp inf_le_right

theorem natural_mem_of_pair_mem {k : ℕ} {A : Subgroup (Sp F)}
    (hA : A ∈ ChapterE.fixedSpaceFamily (graphPair (F := F)) k) :
    A ∈ ChapterE.fixedSpaceFamily binaryNatural k := by
  refine ⟨hA.1,hA.2.1,?_⟩
  intro B hBA hB
  ext v
  rw [mem_binaryNatural_fixedSpace_iff,mem_binaryNatural_fixedSpace_iff,hA.2.2 B hBA hB]

theorem conjugate_natural_mem_of_pair_mem {k : ℕ} {A : Subgroup (Sp F)}
    (hA : A ∈ ChapterE.fixedSpaceFamily (graphPair (F := F)) k) :
    A.map (graphAut (F := F)).toMonoidHom ∈ ChapterE.fixedSpaceFamily binaryNatural k := by
  have hc : A ∈ ChapterE.fixedSpaceFamily
      (binaryNatural.comp (graphAut (F := F)).toMonoidHom) k := by
    refine ⟨hA.1,hA.2.1,?_⟩
    intro B hBA hB
    ext v
    rw [fixedSpace_comp_map,fixedSpace_comp_map,mem_conjugateNatural_fixedSpace_iff,
      mem_conjugateNatural_fixedSpace_iff,hA.2.2 B hBA hB]
  exact ChapterE.fixedSpaceFamily_map_of_equivariant _ _ graphAut.toMonoidHom
    graphAut.injective (LinearEquiv.refl (ZMod 2) (Vector F)) (fun _ _ => rfl) hc

theorem pair_family_le_sylowCenter {n k : ℕ} (hF : Nat.card F = 2^n)
    (hk : n < k) {A : Subgroup (Sp F)} (hAU : A ≤ unipotent)
    (hA : A ∈ ChapterE.fixedSpaceFamily (graphPair (F := F)) k) : A ≤ sylowCenter := by
  rw [sylowCenter_eq_radical_inf]
  refine le_inf ?_ (natural_family_le_planeRadical hF hk hAU (natural_mem_of_pair_mem hA))
  apply (le_pointRadical_iff_conjugate_plane_fixed hAU).mpr
  have he := hA.2.2 (A ⊓ SymplecticConjugatePair.pointRadical) inf_le_left (by
    rw [Subgroup.inf_relIndex_left]
    exact (log_relIndex_radical_le hF hAU false).trans_lt hk)
  intro v hv
  apply (mem_conjugateNatural_fixedSpace_iff A v).mpr
  rw [he]
  have hf := (le_pointRadical_iff_conjugate_plane_fixed
    (inf_le_left.trans hAU)).mp (show A ⊓ SymplecticConjugatePair.pointRadical ≤
      SymplecticConjugatePair.pointRadical from inf_le_right) hv
  exact (mem_conjugateNatural_fixedSpace_iff _ v).mp hf

theorem pair_fixedSpaceFamily_empty {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n) :
    ChapterE.fixedSpaceFamily (graphPair (F := F)) (2*n) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro A hA
  let : IsElementaryAbelian 2 A := hA.2.1.2
  obtain ⟨S,hS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp F) S (unipotentSylow hF hn)
  have hs : (S : Subgroup (Sp F)).map (MulAut.conj g).toMonoidHom = unipotent :=
    congrArg (fun T : Sylow 2 (Sp F) => (T : Subgroup (Sp F))) hg
  have hAU : A.map (MulAut.conj g).toMonoidHom ≤ unipotent :=
    hs ▸ Subgroup.map_mono hS
  have hAc := ChapterE.ValueBound.fixedSpaceFamily_conjugationInvariant
    (graphPair (F := F)) (2*n) A hA g
  exact central_not_mem_fixedSpaceFamily hF hn
    (pair_family_le_sylowCenter hF (by omega) hAU hAc) hAc

theorem pair_moduleA_lt {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n) :
    ChapterE.moduleA (graphPair (F := F)) < (2*n : ℕ) := by
  have h := (ChapterE.moduleA_le_iff_next_family_empty
    (graphPair (F := F)) (2*n-1)).mpr (by
      rw [show 2*n-1+1 = 2*n by omega]
      exact pair_fixedSpaceFamily_empty hF hn)
  exact h.trans_lt (ENat.natCast_lt_natCast.mpr (by omega))

theorem derived_pair_fixedSpaceFamily_empty {n : ℕ} (hF : Nat.card F = 2^n)
    (hn : 0 < n) :
    ChapterE.fixedSpaceFamily (derivedPair (graphAut (F := F))) (2*n) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro A hA
  have hmap := ChapterE.fixedSpaceFamily_map_of_equivariant
    (derivedPair (graphAut (F := F))) graphPair (commutator (Sp F)).subtype
    Subtype.val_injective (LinearEquiv.refl (ZMod 2) (Space F)) (fun _ _ => rfl) hA
  rw [pair_fixedSpaceFamily_empty hF hn] at hmap
  exact hmap

theorem derived_pair_moduleA_lt {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n) :
    ChapterE.moduleA (derivedPair (graphAut (F := F))) < (2*n : ℕ) :=
  (ChapterE.moduleA_comp_le (graphPair (F := F)) (commutator (Sp F)).subtype
    Subtype.val_injective).trans_lt (pair_moduleA_lt hF hn)

end CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
