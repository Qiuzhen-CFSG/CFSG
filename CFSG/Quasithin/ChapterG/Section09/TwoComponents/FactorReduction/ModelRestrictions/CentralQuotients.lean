module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.ModelRestrictions.Source
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.Rank
public import Theory.GroupTheory.PerfectCentralCoverRank

/-!
# Odd ranks of the two central quotients

Multiplication presents the join of two commuting components as a central
product. Its kernel is killed by the product of the central-quotient maps,
so the product of the two simple quotients is an actual section of the
ambient group, and therefore of its SQTK cover. Under A.2.1(2), this section
is strongly quasithin. Isomorphism of the factors and additivity of prime
rank give odd rank at most one in each simple quotient.

The already proved I.1.2 transfer theorem then excludes every odd prime from
the center of the perfect covering component. No multiplier table is used.
The A.2.1 witness remains explicit and must be discharged by its source owner.

Source: Aschbacher--Smith, A.2.1(2), printed p.33; I.1.2, p.407;
the two-component reduction in G.9.3, p.356.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.ModelRestrictions
universe u

private theorem semisimple_prod {S D : Type u} [Group S] [Group D]
    [IsQuasisimple S] [IsQuasisimple D] : ChapterA.Section02.IsSemisimple (S × D) := by
  let U := (MonoidHom.snd S D).ker
  let W := (MonoidHom.fst S D).ker
  let eu : S ≃* U := {
    toFun := fun x => ⟨(x, 1), rfl⟩
    invFun := fun x => x.val.1
    left_inv := fun _ => rfl
    right_inv := fun x => Subtype.ext (Prod.ext rfl x.property.symm)
    map_mul' := fun _ _ => Subtype.ext (Prod.ext rfl (one_mul 1).symm) }
  let ew : D ≃* W := {
    toFun := fun x => ⟨(1, x), rfl⟩
    invFun := fun x => x.val.2
    left_inv := fun _ => rfl
    right_inv := fun x => Subtype.ext (Prod.ext x.property.symm rfl)
    map_mul' := fun _ _ => Subtype.ext (Prod.ext (one_mul 1).symm rfl) }
  have hu : IsComponent (S × D) U :=
    ⟨(inferInstance : U.Normal).isSubnormal, IsQuasisimple.of_mulEquiv eu⟩
  have hw : IsComponent (S × D) W :=
    ⟨(inferInstance : W.Normal).isSubnormal, IsQuasisimple.of_mulEquiv ew⟩
  apply top_unique
  intro x _
  have hu' : U ≤ componentLayer (S × D) := le_sSup hu
  have hw' : W ≤ componentLayer (S × D) := le_sSup hw
  have hx : (x.1, (1 : D)) ∈ componentLayer (S × D) := hu' rfl
  have hy : ((1 : S), x.2) ∈ componentLayer (S × D) := hw' rfl
  simpa using (componentLayer (S × D)).mul_mem hx hy

/-- A central product maps onto the product of its central quotients.
The section is constructed from the actual multiplication homomorphism. -/
theorem quotient_product_isSection {G : Type u} [Group G] (L M : Subgroup G)
    (hc : L ≤ centralizer (M : Set G)) :
    ChapterA.Section02.IsSectionOf ((L ⧸ center L) × (M ⧸ center M)) G := by
  classical
  have hcomm : ∀ l : L, ∀ m : M, Commute (l : G) (m : G) :=
    fun l m => (hc l.property m m.property).symm
  let f : L × M →* G := L.subtype.noncommCoprod M.subtype hcomm
  let q := (QuotientGroup.mk' (center L)).prodMap (QuotientGroup.mk' (center M))
  have hker : f.rangeRestrict.ker ≤ q.ker := by
    rintro ⟨l, m⟩ h
    have he : (l : G) * (m : G) = 1 := congrArg Subtype.val h
    have hlm : (l : G) = (m : G)⁻¹ := eq_inv_of_mul_eq_one_left he
    have hml : (m : G) = (l : G)⁻¹ := eq_inv_of_mul_eq_one_right he
    have hl : l ∈ center L := by
      apply mem_center_iff.mpr
      intro x
      apply Subtype.ext
      change (x : G) * (l : G) = (l : G) * (x : G)
      rw [hlm]
      exact (hcomm x m).inv_right.eq
    have hm : m ∈ center M := by
      apply mem_center_iff.mpr
      intro x
      apply Subtype.ext
      change (x : G) * (m : G) = (m : G) * (x : G)
      rw [hml]
      exact (hcomm l x).symm.inv_right.eq
    exact Prod.ext ((QuotientGroup.eq_one_iff l).mpr hl)
      ((QuotientGroup.eq_one_iff m).mpr hm)
  let g := f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨q, hker⟩
  have hgf (x : L × M) : g (f.rangeRestrict x) = q x :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  have hg : Function.Surjective g := by
    rintro ⟨x, y⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (center L) x
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (center M) y
    exact ⟨f.rangeRestrict (l, m), hgf (l, m)⟩
  exact ⟨f.range, g, hg⟩

/-- A.2.1 bounds the odd rank of each simple quotient before any assumption
about the component centers. -/
theorem quotient_odd_rank_le_one {G : Type u} [Group G] [Finite G]
    {K : GroupClass.{u}} (hA : SemisimpleSectionRankTheorem K)
    (c : SQTKCover K G) {L M : Subgroup G}
    (hL : IsComponent G L) (hM : IsComponent G M) (hne : L ≠ M)
    (e : (L ⧸ center L) ≃* (M ⧸ center M))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) : primeRank p (L ⧸ center L) ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsQuasisimple L := hL.2
  let : IsQuasisimple M := hM.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup (M ⧸ center M) := IsQuasisimple.simple
  let : IsQuasisimple (L ⧸ center L) :=
    IsQuasisimple.of_surjective (QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple (M ⧸ center M) :=
    IsQuasisimple.of_surjective (QuotientGroup.mk' (center M)) (QuotientGroup.mk'_surjective _)
  have hsec := quotient_product_isSection L M
    (commutator_eq_bot_iff_le_centralizer.mp (hL.commutator_eq_bot_of_ne hM hne))
  have hqt := hA c.Cover c.sqtk _ (hsec.ambient_surjective c.projection c.surjective)
    semisimple_prod
  have hr := hqt p hp ho
  rw [primeRank_prod_eq_add, ← primeRank_equiv p e] at hr
  omega

/-- Transfer at each odd prime makes the center a two-group. This uses
I.1.2, already proved for arbitrary perfect covers, without multiplier tables. -/
theorem center_isTwoGroup_of_quotient_odd_rank {E : Type u} [Group E] [Finite E]
    [Group.IsPerfect E]
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p (E ⧸ center E) ≤ 1) :
    IsPGroup 2 (center E) := by
  let f : PerfectCentralCovering.Cover E (E ⧸ center E) := {
    toMonoidHom := QuotientGroup.mk' (center E)
    surjective := QuotientGroup.mk'_surjective _
    isPerfect := inferInstance
    ker_le_center := (QuotientGroup.ker_mk' _).le }
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  let : Fact p.Prime := ⟨hprime⟩
  have heq : p = 2 := by
    by_contra hn
    have ho := hprime.odd_of_ne_two hn
    have he := f.not_dvd_card_multiplier_of_odd_of_primeRank_le_one ho (hr p hprime ho)
    apply he
    change p ∣ Nat.card (QuotientGroup.mk' (center E)).ker
    rw [QuotientGroup.ker_mk']
    exact Nat.dvd_of_mem_primeFactors hp
  simp [heq, Nat.prime_two]

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.ModelRestrictions
