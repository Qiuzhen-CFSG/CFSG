module

public import Theory.GroupTheory.CoreCentralNormalizerAction
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.PPerfectHom
public import Theory.Alternating.Aut
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.SpecificGroups.Alternating.SmallSolvableFive

/-!
# A five-divisible solvable actor excludes small alternating central quotients

The actual two-perfect actor has trivial outer action on A₅, A₆, A₇ and
A₈ because their outer groups are two-groups. Pulling its whole image back
through faithful inner conjugation preserves solvability and divisibility
by five. The supplied component Sylow maps through the literal core-central
projection and normalizes that same pulled-back subgroup. The small
alternating solvable-overgroup theorem gives the contradiction.

No inner-placement, quotient-kernel, or subgroup-normalization conclusion
is assumed separately. Source: Aschbacher--Smith A.3.15 and the original
component exclusion in 6.1.4, printed pp.50--51 and 665--666.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory

private theorem alternating_outer_two (n : ℕ) (hn : 5 ≤ n) :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin n))) := by
  by_cases he : n = 6
  · subst n
    exact IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card
  let A := alternatingGroup (Fin n)
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcard : Nat.card (Equiv.Perm (Fin n) ⧸ A) = 2 ^ 1 := by
    rw [← A.index_eq_card]
    exact alternatingGroup.index_eq_two
  apply (IsPGroup.of_card hcard).of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨s, rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn he).surjective a
  exact ⟨QuotientGroup.mk' A s, rfl⟩

/-- The whole original solvable two-perfect actor, retaining its five
part and supplied component Sylow, excludes the four small alternating models. -/
theorem coreCentral_no_small_alternating_quintic
    {G : Type*} [Group G] [Finite G]
    (K X : Subgroup G) (U : Sylow 2 K)
    (hUX : (U : Subgroup K).map K.subtype ≤ normalizer (X : Set G))
    (hXN : X ≤ normalizer (K : Set G))
    (hXp : IsPPerfect 2 X) (hsolv : Group.IsSolvable X)
    (hfive : 5 ∣ Nat.card (coreCentralActorImage K X))
    (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (e : coreCentralQuotient K ≃* alternatingGroup (Fin n)) : False := by
  let C := coreCentralQuotient K
  let q := coreCentralProjection K
  let a := normalizerCoreCentralAction K
  let Y := coreCentralActorImage K X
  have hn5 : 5 ≤ n := by rcases hn with h | h | h | h <;> omega
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have ha (k : K) : a ⟨k, K.le_normalizer k.property⟩ = MulAut.conj (q k) := by
    ext y
    obtain ⟨x, rfl⟩ := hq y
    rw [normalizerCoreCentralAction_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl
  let ex := (subgroupOfEquivOfLe hXN).symm
  let f : X →* Y := (a.subgroupMap (X.subgroupOf (normalizer (K : Set G)))).comp ex.toMonoidHom
  have hf : Function.Surjective f := (a.subgroupMap_surjective _).comp ex.surjective
  have hYp : IsPPerfect 2 Y := hXp.of_surjective f hf
  let : Group.IsSolvable X := hsolv
  let : Group.IsSolvable Y := Group.isSolvable_of_surjective (f := f) hf
  have houter : IsPGroup 2 (MulAut.Outer C) := (alternating_outer_two n hn5).of_injective
    (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective
  have hinner : Y ≤ MulAut.innerSubgroup C := by
    let r : Y →* MulAut.Outer C := (QuotientGroup.mk' (MulAut.innerSubgroup C)).comp Y.subtype
    have hr := hYp.hom_eq_one_of_isPGroup houter r
    intro y hy
    exact (QuotientGroup.eq_one_iff _).mp (DFunLike.congr_fun hr ⟨y, hy⟩)
  have hz : center C = ⊥ := by
    apply bot_unique
    intro x hx
    have he := (centerCongr e ⟨x, hx⟩).property
    change e x ∈ center (alternatingGroup (Fin n)) at he
    rw [alternatingGroup.center_eq_bot (by simpa only [Nat.card_fin] using (show 4 ≤ n by omega)),
      mem_bot] at he
    exact e.injective (he.trans e.map_one.symm)
  let c : C →* MulAut C := MulAut.conj
  have hc : Function.Injective c := conj_injective_of_center_eq_bot hz
  let R := Y.comap c
  have hRY : R.map c = Y := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr hinner
  have hRfive : 5 ∣ Nat.card R := by
    rw [← card_map_of_injective hc, hRY]
    exact hfive
  let cr : R →* Y := c.subgroupComap Y
  have hcri : Function.Injective cr := fun _ _ he => Subtype.ext (hc (congrArg Subtype.val he))
  let : Group.IsSolvable R := Group.isSolvable_of_isSolvable_injective hcri
  let S := U.mapSurjective (f := q) hq
  have hSR : (S : Subgroup C) ≤ normalizer (R : Set C) := by
    rintro z ⟨u, hu, rfl⟩
    apply R.mem_normalizer_iff.mpr
    intro y
    change c y ∈ Y ↔ c (q u * y * (q u)⁻¹) ∈ Y
    rw [map_mul, map_mul, map_inv]
    have hnorm : a ⟨u, K.le_normalizer u.property⟩ ∈ normalizer (Y : Set (MulAut C)) := by
      apply (X.subgroupOf (normalizer (K : Set G))).le_normalizer_map a
      apply mem_map_of_mem
      apply mem_normalizer_iff.mpr
      intro x
      exact mem_normalizer_iff.mp (hUX (mem_map_of_mem K.subtype hu)) (x : G)
    rw [ha] at hnorm
    exact mem_normalizer_iff.mp hnorm (c y)
  let Sm := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let Rm := R.map e.toMonoidHom
  have hSm : (Sm : Subgroup (alternatingGroup (Fin n))) ≤ normalizer (Rm : Set (alternatingGroup (Fin n))) :=
    (map_mono hSR).trans (R.le_normalizer_map e.toMonoidHom)
  have hRm : 5 ∣ Nat.card Rm := by
    rw [card_map_of_injective e.injective]
    exact hRfive
  have hsolvRm : Group.IsSolvable Rm := Group.isSolvable_of_surjective
    (f := e.toMonoidHom.subgroupMap R) (e.toMonoidHom.subgroupMap_surjective R)
  exact Theory.SpecificGroups.Alternating.SmallSolvableFive.not_five_dvd_of_sylow_normalizes
    hn Rm hsolvRm Sm hSm hRm

end Theory.GroupTheory
