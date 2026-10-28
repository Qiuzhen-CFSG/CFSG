module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.GenerationSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.WeakContainmentSource
public import Theory.GroupTheory.ConjugateSubgroupClosure

/-!
# The actual distinguished weak closure

The original L-conjugates generate U, and the outside involution
interchanges the two elementary factors of R. Thus R lies in the whole
conjugate-subgroup closure. The containment theorem gives equality with
precisely the preceding TI and C_S(Z)=R source inputs.
Source: Aschbacher–Smith, 2.4.16(3),2.4.19, printed pp.533–534.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The module is the closure of the whole ambient conjugates of Z that it contains. -/
theorem source_distinguished_module_closure
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    conjugateSubgroupClosure (distinguishedZ d) (sourceModule (d.block.map d.H.subtype)) =
      sourceModule (d.block.map d.H.subtype) := by
  let L := d.block.map d.H.subtype
  let U := sourceModule L
  obtain ⟨x,hxT,hxS⟩ := SetLike.exists_of_lt hST
  have hgen := source_distinguished_generates_module d hG T hST hsingle hL hM hTM hunique x hxT hxS
  have hEU : (distinguishedZ d).map (MulAut.conj x⁻¹).toMonoidHom ≤ U :=
    (le_conjugateSpanBy _ _).trans_eq hgen
  have hLU : L ≤ normalizer (U : Set G) :=
    L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L))
  exact le_antisymm (conjugateSubgroupClosure_le_self _ _)
    (hgen.symm.le.trans (conjugateSpanBy_le_conjugateSubgroupClosure _ x⁻¹ hEU hLU))

/-- The generation half of original 2.4.19 has no TI or centralizer premise. -/
theorem source_thompson_le_distinguished_closure
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ≤
      conjugateSubgroupClosure (distinguishedZ d) (T : Subgroup G) := by
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let U := sourceModule L
  let W := conjugateSubgroupClosure (distinguishedZ d) (T : Subgroup G)
  obtain ⟨x,hxT,hxS⟩ := SetLike.exists_of_lt hST
  have hpair := (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).2.2.2 x hxT hxS
  have hRT : R ≤ (T : Subgroup G) := (sSup_le fun _ h => h.1).trans hST.le
  have hUR : U ≤ R := le_sup_left.trans_eq hpair.1.symm
  have hUW : U ≤ W :=
    (source_distinguished_module_closure d hG T hST hsingle hL hM hTM hunique).symm.le.trans
      (conjugateSubgroupClosure_mono (hUR.trans hRT))
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) := le_normalizer_conjugateSubgroupClosure _ _
  have hUxW : U.map (MulAut.conj x⁻¹).toMonoidHom ≤ W :=
    (map_mono hUW).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hTW (T.inv_mem hxT)))
  exact hpair.1.le.trans (sup_le hUW hUxW)

/-- Original 2.4.19 assembled from the earlier TI and centralizer results.
Every closure and conjugation is in the original ambient group. -/
theorem source_distinguished_weak_closure
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hTI : ChapterI.Section06To08.IsTISubgroup (distinguishedZ d))
    (hCS : ((d.S : Subgroup d.H).map d.H.subtype) ⊓ centralizer (distinguishedZ d : Set G) =
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    conjugateSubgroupClosure (distinguishedZ d) (T : Subgroup G) =
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  exact le_antisymm (conjugateSubgroupClosure_le
    (source_distinguished_conjugate_le_of_sylow_centralizer d hG T hST hsingle hL hM hTM hunique hTI hCS))
      (source_thompson_le_distinguished_closure d hG T hST hsingle hL hM hTM hunique)
end CFSG.Quasithin.Chapter2.LinearShadows.Single
