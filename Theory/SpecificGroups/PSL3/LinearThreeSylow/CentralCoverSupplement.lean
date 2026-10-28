module
public import Theory.GroupTheory.PerfectCentralQuotientEmbedding
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.OddSupplement

/-!
# The odd-supplement obstruction for linear-three central covers

Quotient the ambient group by the embedded center of its normal perfect
component. The actual Sylow, smaller component and odd actor descend;
properness and nonsolvability survive the central kernel. The existing
projective linear-three obstruction therefore applies. Specializing the
central-quotient equivalence gives the source SL₃ row, including its
nontrivial scalar center, with no parabolic or action premise added.

Source: Aschbacher--Smith 5.1.13 and 5.2.2, printed pp.636 and 648.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree.OddSupplement
variable {F : Type*} [Field F] [Finite F]
variable {G : Type*} [Group G] [Finite G]

/-- A perfect central cover of a nonbinary projective linear-three component
has the same obstruction to generation by an odd solvable supplement. -/
theorem no_odd_solvable_supplement_of_center_quotient
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 2 ≤ n)
    (S : Sylow 2 G) (K R D : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (e : (K ⧸ center K) ≃* PSL(3,F)) (hRK : R < K) (hRns : ¬ Group.IsSolvable R)
    (hSR : (S : Subgroup G) ≤ normalizer (R : Set G))
    (ho : Odd (Nat.card D)) (hsol : Group.IsSolvable ((S : Subgroup G) ⊔ D : Subgroup G))
    (hgen : R ⊔ (S : Subgroup G) ⊔ D = ⊤) : False := by
  let Z := (center K).map K.subtype
  let : Z.Normal := normalizer_eq_top_iff.mp (top_unique
    (le_normalizer_of_normal.trans (normalizer_le_normalizer_characteristic_image K (center K))))
  let q := QuotientGroup.mk' Z
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective Z)
  let Kbar := K.map q
  let Rbar := R.map q
  let Dbar := D.map q
  let : Kbar.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective Z)
  have hker : (q.subgroupMap K).ker = center K := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    exact comap_map_eq_self_of_injective K.subtype_injective _
  let a : Kbar ≃* (K ⧸ center K) :=
    (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap K)
      (q.subgroupMap_surjective K)).symm.trans (QuotientGroup.quotientMulEquivOfEq hker)
  apply no_odd_solvable_supplement hF hn Sbar Kbar Rbar Dbar (a.trans e)
  · exact map_lt_of_perfect_of_kernel_le_center q K R hRK (by rw [QuotientGroup.ker_mk'])
  · exact not_isSolvable_map_of_kernel_le_center q K R hRK.le
      (by rw [QuotientGroup.ker_mk']) hRns
  · exact (map_mono (f := q) hSR).trans (le_normalizer_map q)
  · exact ho.of_dvd_nat (card_map_dvd D q)
  · let := hsol
    have hsol' := Group.isSolvable_of_surjective (q.subgroupMap_surjective ((S : Subgroup G) ⊔ D))
    rw [Subgroup.map_sup] at hsol'
    exact hsol'
  · change R.map q ⊔ (S : Subgroup G).map q ⊔ D.map q = ⊤
    rw [←Subgroup.map_sup, ←Subgroup.map_sup, hgen,
      map_top_of_surjective q (QuotientGroup.mk'_surjective Z)]
/-- The special-linear covering row follows through its actual scalar quotient. -/
theorem no_odd_solvable_supplement_specialLinear
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 2 ≤ n)
    (S : Sylow 2 G) (K R D : Subgroup G) [K.Normal]
    (e : K ≃* SL(3,F)) (hRK : R < K) (hRns : ¬ Group.IsSolvable R)
    (hSR : (S : Subgroup G) ≤ normalizer (R : Set G))
    (ho : Odd (Nat.card D)) (hsol : Group.IsSolvable ((S : Subgroup G) ⊔ D : Subgroup G))
    (hgen : R ⊔ (S : Subgroup G) ⊔ D = ⊤) : False := by
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let a : (K ⧸ center K) ≃* PSL(3,F) :=
    QuotientGroup.congr (center K) (center SL(3,F)) e (by
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact (Subgroup.centerCongr e ⟨x,hx⟩).property
      · intro hy
        exact ⟨e.symm y,(Subgroup.centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)
  exact no_odd_solvable_supplement_of_center_quotient hF hn S K R D a hRK hRns hSR ho hsol hgen
end Matrix.PSL3.LinearThree.OddSupplement
