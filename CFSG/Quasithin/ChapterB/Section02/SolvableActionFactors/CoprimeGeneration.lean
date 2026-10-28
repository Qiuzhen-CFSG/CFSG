module
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.SmallAction
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.FixedComplement
public import CFSG.Quasithin.ChapterB.Section02.SolvableActionFactors
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Coprime generation excludes a single solvable Thompson factor

If nine does not divide the order of a solvable reduced action, its
nonempty family of binary SL₂(2) offender factors has exactly one member.
The factor-permutation action is then trivial, and the quotient by the
centralizer of the offender subgroup has order dividing six. Hence a
subgroup of order coprime to six centralizes the offender subgroup.

The canonical fixed complement puts its moved space in the offender
fixed space. If those moved vectors normally generate the original
module, faithfulness contradicts the nontrivial offender factor.
Consequently the original Sylow Thompson subgroup centralizes the module.
The result retains the actual quotient action and subgroup commutator.

Source: Aschbacher–Smith B.1.8 and B.2.16, printed pp.70 and78;
application to the point-fusion step of 5.1.17, printed p.640
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)
omit [Finite G] in
/-- At most one factor fits in an action whose order is not divisible by nine. -/
theorem count_eq_one_of_nine_free (h9 : ¬ 9 ∣ Nat.card G) : d.count = 1 := by
  have hc := d.count_pos
  by_contra hn
  have h2 : 2 ≤ d.count := by omega
  apply h9
  apply dvd_trans _ (card_subgroup_dvd_card (offenderSubgroup ρ))
  rw [d.offenderSubgroup_card]
  exact (by decide : 9 ∣ 6^2).trans (pow_dvd_pow 6 h2)

include d in
omit [Finite G] in
/-- Coprime actors centralize the sole offender factor. -/
theorem coprime_six_centralizes (h9 : ¬ 9 ∣ Nat.card G)
    (A : Subgroup G) (hA : Nat.Coprime (Nat.card A) 6) :
    A ≤ centralizer (offenderSubgroup ρ : Set G) := by
  have hn := d.count_eq_one_of_nine_free h9
  let : Subsingleton (Fin d.count) := by rw [hn]; infer_instance
  let K := offenderSubgroup ρ
  let : K.Normal := offenderSubgroup_normal ρ
  let C := centralizer (K : Set G)
  have hgen : K ⊔ C = ⊤ := by
    apply top_unique
    intro g _
    exact d.factorConjugation_kernel_le (show g ∈ d.factorConjugation.ker from Subsingleton.elim _ _)
  have hk : Nat.card K = 6 := by simpa only [hn,pow_one] using d.offenderSubgroup_card
  have hq : Nat.card (G ⧸ C) ∣ 6 := by
    rw [← index_eq_card,←relIndex_top_right C,←hgen,relIndex_sup_right]
    exact hk ▸ relIndex_dvd_card C K
  let f := (QuotientGroup.mk' C).comp A.subtype
  intro a ha
  have hd : orderOf (f ⟨a,ha⟩) ∣ Nat.card A :=
    (orderOf_map_dvd f ⟨a,ha⟩).trans (orderOf_dvd_natCard _)
  have hd6 := (orderOf_dvd_natCard (f ⟨a,ha⟩)).trans hq
  exact (QuotientGroup.eq_one_iff a).mp
    (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hA hd hd6))

include d in
omit [Finite G] in
/-- Coprime displacements lie in the canonical offender fixed space. -/
theorem coprime_six_moved_le_fixed (h9 : ¬ 9 ∣ Nat.card G)
    (A : Subgroup G) (hA : Nat.Coprime (Nat.card A) 6) :
    subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ (offenderSubgroup ρ) := by
  let K := offenderSubgroup ρ
  let : K.Normal := offenderSubgroup_normal ρ
  have hc := d.coprime_six_centralizes h9 A hA
  have hm : subspaceCommutator ρ ⊤ K ≤ fixedSpace ρ A := by
    intro v hv a
    exact d.centralizer_fixes_moved a (hc a.property) hv
  apply subspaceCommutator_le_of_le_sup_fixedSpace ρ
    (le_top.trans (fixedSpace_stable_of_normal ρ K))
  rw [← d.moved_complement.sup_eq_top]
  exact sup_le (hm.trans le_sup_right) le_sup_left
end CFSG.Quasithin.ChapterB.SolvableFFFactors

namespace CFSG.Quasithin.ChapterB
open Representation NormalElementaryQuotient
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
/-- Normal generation by coprime displacements rules out every Thompson factor. -/
theorem thompson_centralizes_of_coprime_moved_generation
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* Q) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hsol : Group.IsSolvable Q) (h9 : ¬ 9 ∣ Nat.card Q) (hcore : pCore 2 Q = ⊥)
    (A : Subgroup G) (hA : Nat.Coprime (Nat.card A) 6)
    (hgen : U ≤ conjugateSpanBy ⁅U,A⁆ ⊤) (T : Sylow 2 G) :
    Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G) := by
  by_contra hn
  obtain ⟨d,_,_,_,_⟩ := thompson_factors_of_solvable_action U q hq hker T hn hsol hcore
  let ρ := representation U q hq hker
  let K := offenderSubgroup ρ
  let : K.Normal := offenderSubgroup_normal ρ
  let B := K.comap q
  have hm : ⁅U,A⁆ ≤ centralizer (B : Set G) := by
    intro x hx
    let v : Additive U := Additive.ofMul ⟨x,(commutator_le_left U A) hx⟩
    have hv : v ∈ subspaceCommutator ρ ⊤ (A.map q) := by
      rw [← commutatorSpace_eq U q hq hker A]
      exact hx
    have hc := d.toSolvableFFFactors.coprime_six_moved_le_fixed h9 (A.map q)
      (hA.of_dvd_left (card_map_dvd _ _)) hv
    have hBK : B.map q = K := map_comap_eq_self_of_surjective hq _
    apply (mem_fixedSpace_image U q hq hker B v).mp
    rw [hBK]
    exact hc
  have hu : U ≤ centralizer (B : Set G) := hgen.trans
    (conjugateSpanBy_le hm le_normalizer_of_normal)
  have hkbot : K = ⊥ := by
    apply bot_unique
    intro k hk
    obtain ⟨g,rfl⟩ := hq k
    have hg : g ∈ centralizer (U : Set G) :=
      (le_centralizer_iff.mp hu) (show g ∈ B from hk)
    exact hker.ge hg
  have hcard := d.toSolvableFFFactors.offenderSubgroup_card
  change Nat.card K = 6^d.count at hcard
  rw [hkbot,card_bot] at hcard
  have hlt : 1 < 6^d.count := Nat.one_lt_pow (Nat.ne_of_gt d.count_pos) (by decide)
  omega
end CFSG.Quasithin.ChapterB
