module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveResidual
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# The center of the original order-512 five-residual

The residual R and its full five-centralizer B generate the order-1024
core. Their intersection is the original central line. Since R meets the
full kernel C in U and RC is the whole core, the centralizer of R in U
is the original radical, again the central line. Every central element of
R belongs to U, giving the exact center of R.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original residual has the marked central line as its center and
as its five-fixed subgroup, while the full core retains order 1024. -/
theorem source_quintic_large_five_residual_center
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    let U := conjugateSpanBy (localModule T M) H
    let Q := H.pCoreIn 2
    let B := Q ⊓ centralizer (A : Set G)
    let R := ⁅Q,A⁆
    R ⊔ B = Q ∧ R ⊓ B = centralInvolutions T ∧
      U ⊓ centralizer (R : Set G) = centralInvolutions T ∧
      (center R).map R.subtype = centralInvolutions T ∧
      Q ≤ normalizer (R : Set G) ∧ A ≤ normalizer (R : Set G) := by
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  let B := Q ⊓ centralizer (A : Set G)
  let R := ⁅Q,A⁆
  let Z := centralInvolutions T
  obtain ⟨_, _, _, _, _, hUR, hRC, hcap⟩ := source_quintic_large_five_residual
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
  change U ≤ R at hUR
  change R ⊔ C = Q at hRC
  change R ⊓ C = U at hcap
  have hAQ : A ≤ normalizer (Q : Set G) := hAH.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hRQ : R ≤ Q := le_normalizer_iff_commutator_le_left.mp hAQ
  let : Group.IsNilpotent Q := (isPGroup_pCoreIn 2 H).isNilpotent
  have hRB : R ⊔ B = Q :=
    (eq_commutator_sup_centralizer_of_solvable_coprime Q A hAQ
      (inferInstance : Group.IsSolvable Q) (by rw [hA, hlarge]; decide)).symm
  obtain ⟨hUfixed, hQfixed⟩ := source_quintic_five_centralizers
    hG T hempty hM hu hmany hcard e H hH hi A hAH hA
  have hB : B = C ⊓ centralizer (A : Set G) := hQfixed
  have hcapB : R ⊓ B = Z := by
    rw [hB, ← inf_assoc, hcap]
    exact hUfixed
  have hrad : U ⊓ centralizer (Q : Set G) = Z :=
    (source_quintic_span_card_and_core_radical hG T hempty hM hu hmany hcard e H hH hi).2
  have hURfix : U ⊓ centralizer (R : Set G) = Z := by
    apply le_antisymm
    · intro u hu
      apply hrad.le
      refine ⟨hu.1, ?_⟩
      have hQfix : Q ≤ centralizer ({u} : Set G) := by
        rw [← hRC]
        apply sup_le
        · intro r hr
          exact mem_centralizer_singleton_iff.mpr (hu.2 r hr)
        · intro c hc
          exact mem_centralizer_singleton_iff.mpr ((hc.2 u hu.1).symm)
      intro q hq
      exact mem_centralizer_singleton_iff.mp (hQfix hq)
    · exact hrad.ge.trans (inf_le_inf_left _ (centralizer_le hRQ))
  have hcenter : (center R).map R.subtype = Z := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hzR : (z : G) ∈ centralizer (R : Set G) := by
        intro r hr
        exact congrArg R.subtype (mem_center_iff.mp hz ⟨r,hr⟩)
      have hzU : (z : G) ∈ U := hcap.le ⟨z.property,
        hRQ.trans (pCoreIn_le 2 H) z.property, (centralizer_le hUR) hzR⟩
      exact hURfix.le ⟨hzU, hzR⟩
    · intro z hz
      have hzU := hURfix.ge hz
      refine ⟨⟨z,hUR hzU.1⟩, ?_, rfl⟩
      exact mem_center_iff.mpr (fun r => Subtype.ext (hzU.2 r r.property))
  exact ⟨hRB, hcapB, hURfix, hcenter,
    normalizer_commutator_ge_left Q A, normalizer_commutator_ge_right Q A⟩

end CFSG.Quasithin.Chapter14.Section06
