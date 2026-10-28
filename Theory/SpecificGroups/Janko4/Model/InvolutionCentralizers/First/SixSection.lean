module

public import Theory.Mathieu.M22.TripleCover.AbelianSylowObstruction
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The full A₆ two-core section is absent from the first J₄ centralizer

A perfect subgroup whose full two-core quotient is A₆ has Sylow
three-subgroups of order nine. In the genuine triple cover of M₂₂ these
subgroups miss the central subgroup of order three: their intersection
lies in the solvable radical, which is the two-core. Their commuting join
would therefore be an abelian Sylow subgroup of order 27. Central transfer
in the native perfect triple cover excludes this.

A perfect subgroup of the first J₄ involution centralizer lies in its
actual index-two cover preimage. The literal projection to 3.M₂₂ has a
two-group kernel, so the full A₆ quotient survives and the preceding
contradiction applies. No quotient by an unproved odd kernel is taken.
Source: Aschbacher–Smith A.3.12 and 8.2.13, pp.47–48,722–723;
GLS3 Table 5.3i for the actual first-centralizer structure.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.InvolutionCentralizers.First
open Sporadic.Mathieu
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem sylow_three_card {B : Type*} [Group B] [Finite B]
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) (T : Sylow 3 B) :
    Nat.card T = 9 := by
  let q := eB.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))
  have hq : Function.Surjective q := eB.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 B := by
    rw [MonoidHom.ker_comp_of_injective _ _ eB.injective,QuotientGroup.ker_mk']
  have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
    rw [hk,hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hi := injective_comp_subtype_of_coprime_ker q hcop (T : Subgroup B) T.isPGroup'
  let d : T ≃* (T : Subgroup B).map q := MulEquiv.ofBijective
    (q.subgroupMap (T : Subgroup B)) ⟨fun x y hh => hi (congrArg Subtype.val hh),
      q.subgroupMap_surjective _⟩
  rw [Nat.card_congr d.toEquiv]
  change Nat.card (T.mapSurjective hq) = 9
  rw [Sylow.card_eq_multiplicity,nat_card_alternatingGroup,Nat.card_fin]
  decide +kernel

/-- The genuine triple Mathieu cover has no perfect subgroup with full
A6 quotient by its two-core. Central transfer detects the retained cubic kernel. -/
theorem tripleCover_not_six_section (B : Subgroup M22TripleCover)
    [Group.IsPerfect B]
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := eB.isSimpleGroup
  let T : Sylow 3 B := default
  let P := (T : Subgroup B).map B.subtype
  let Z := center M22TripleCover
  have hP : Nat.card P = 9 := by
    rw [card_map_of_injective B.subtype_injective]
    exact sylow_three_card eB T
  have hZ : Nat.card Z = 3 := M22TripleCover.center_card
  have hZB : center B ≤ pCore 2 B := by
    rw [←PerfectCoreTwoExtension.radical_eq_core]
    exact le_solvableRadical (center B) inferInstance inferInstance
  have hd : Disjoint P Z := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    obtain ⟨b,hb,rfl⟩ := hx.1
    have hbZ : b ∈ center B := mem_center_iff.mpr fun y =>
      Subtype.ext (mem_center_iff.mp hx.2 y)
    exact congrArg B.subtype ((IsPGroup.disjoint_of_ne 3 2 (by decide)
      (T : Subgroup B) (pCore 2 B) T.isPGroup' pCore_isPGroup).le_bot ⟨hb,hZB hbZ⟩)
  have hcomm : Z ≤ Subgroup.centralizer (P : Set M22TripleCover) := by
    intro z hz p _
    exact mem_center_iff.mp hz p
  have hjoin : Nat.card (P ⊔ Z : Subgroup M22TripleCover) = 27 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint P Z
      (hcomm.trans (Subgroup.centralizer_le_normalizer _)) hd,hP,hZ]
  let : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq
    (p := 3) (by simpa using hP)
  let : IsMulCommutative (P ⊔ Z : Subgroup M22TripleCover) := by
    apply le_centralizer_iff_isMulCommutative.mp
    apply sup_le
    · exact le_centralizer_iff.mpr (sup_le P.le_centralizer hcomm)
    · exact le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hcomm) Z.le_centralizer)
  let S : Sylow 3 M22TripleCover := Sylow.ofCard (P ⊔ Z) (by
    rw [hjoin,M22TripleCover.card]
    decide +kernel)
  let : IsMulCommutative S := inferInstanceAs (IsMulCommutative (P ⊔ Z : Subgroup M22TripleCover))
  apply M22TripleCover.not_hasAbelianSylow_three
  intro R
  let d := R.equiv S
  exact .of_comm fun a b => d.injective (by
    rw [map_mul,map_mul]
    exact mul_comm _ _)

open QuotientExtension

/-- The full first J4 involution centralizer has no perfect A6 two-core section. -/
theorem not_six_section (B : Subgroup centralizer) [Group.IsPerfect B]
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  let : Group.IsSolvable (centralizer ⧸ H) :=
    Group.isSolvable_of_surjective (f := centralizerQuotientEquivC2.symm.toMonoidHom)
      centralizerQuotientEquivC2.symm.surjective
  have hBH : B ≤ H := le_of_isPerfect_of_solvable_quotient B H
  let A := B.subgroupOf H
  let d := subgroupOfEquivOfLe hBH
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := d.symm.toMonoidHom) d.symm.surjective
  let a := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  let W := A.map coverProjection
  let f := coverProjection.subgroupMap A
  let : Group.IsPerfect W := Group.IsPerfect.ofSurjective (coverProjection.subgroupMap_surjective A)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (coverProjection.subgroupMap A).ker
    rw [ker_subgroupMap,coverProjection_ker]
    exact pCore_isPGroup.comap_subtype.comap_subtype
  let b := f.pCoreQuotientEquiv (coverProjection.subgroupMap_surjective A) hk
  exact tripleCover_not_six_section W (b.symm.trans (a.trans eB))

end Janko4.InvolutionCentralizers.First
