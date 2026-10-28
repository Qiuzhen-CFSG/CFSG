module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PerfectCentralCoverRank
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The rank-one image comparison in 15.3.12

A finite two-perfect group whose two-core quotient has exponent dividing
three has the same image as any nontrivial normal two-perfect subgroup
with two-group action kernel, provided the full image has three-rank at
most one. Its Sylow three-subgroups are cyclic, so its two-core quotient
has order at most three. The normal subgroup covers that quotient;
two-perfectness removes the remaining two-group quotient.

Transfer also excludes central three-torsion in a finite perfect group
of three-rank one. This replaces the unnecessary claim of a trivial
center when applying the comparison to a C-component.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the inner-action
comparison in the proof of 15.3.12(2), printed p.1125 (PDF p.1142).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.ComponentIntersection.InnerSplitting

private theorem pPerfect_subgroup_ne_pGroup {H : Type*} [Group H]
    (A : Subgroup H) (ha : A ≠ ⊥) (hp : IsPPerfect 2 A) : ¬ IsPGroup 2 A := by
  intro htwo
  have hi := hp.hom_eq_one_of_isPGroup htwo (MonoidHom.id A)
  apply ha
  apply (eq_bot_iff_forall A).mpr
  intro x hx
  exact congrArg Subtype.val (DFunLike.congr_fun hi (⟨x, hx⟩ : A))

private theorem rankOne_quotient_card_dvd_three
    {H : Type*} [Group H] [Finite H]
    (hr : primeRank 3 H ≤ 1)
    (hq : IsPGroup 3 (H ⧸ pCore 2 H))
    (he : Monoid.exponent (H ⧸ pCore 2 H) ∣ 3) :
    Nat.card (H ⧸ pCore 2 H) ∣ 3 := by
  let P : Sylow 3 H := Sylow.nonempty.some
  let : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  let q := QuotientGroup.mk' (pCore 2 H)
  have htop : (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H)) :
      Subgroup (H ⧸ pCore 2 H)) = ⊤ := by
    apply top_unique
    exact (hq.to_subgroup ⊤).le_sylow_of_normal _
  have hs : Function.Surjective (q.comp (P : Subgroup H).subtype) := by
    apply MonoidHom.range_eq_top.mp
    simpa only [MonoidHom.range_comp, range_subtype, Sylow.coe_mapSurjective] using htop
  let : IsCyclic (H ⧸ pCore 2 H) := isCyclic_of_surjective _ hs
  rwa [← IsCyclic.exponent_eq_card]

private theorem normal_eq_top_of_rankOne
    {H : Type*} [Group H] [Finite H]
    (hH : IsPPerfect 2 H) (hr : primeRank 3 H ≤ 1)
    (hq : IsPGroup 3 (H ⧸ pCore 2 H))
    (he : Monoid.exponent (H ⧸ pCore 2 H) ∣ 3)
    (D : Subgroup H) [D.Normal] (hD : IsPPerfect 2 D) (hne : D ≠ ⊥) : D = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hDq : D.map q ≠ ⊥ := by
    intro hz
    have hle : D ≤ pCore 2 H := by
      simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff D).mp hz
    exact pPerfect_subgroup_ne_pGroup D hne hD (pCore_isPGroup.to_le hle)
  have hc : Nat.card (H ⧸ pCore 2 H) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (rankOne_quotient_card_dvd_three hr hq he) with h | h
    · have hzero : pCore 2 H = ⊤ := index_eq_one.mp h
      have hle : D ≤ pCore 2 H := hzero ▸ le_top
      exact (pPerfect_subgroup_ne_pGroup D hne hD (pCore_isPGroup.to_le hle)).elim
    · exact h
  let : Fact (Nat.card (H ⧸ pCore 2 H)).Prime := ⟨hc ▸ Nat.prime_three⟩
  have htop : D.map q = ⊤ := (D.map q).eq_bot_or_eq_top_of_prime_card.resolve_left hDq
  have hsup : D ⊔ pCore 2 H = ⊤ := by
    have hh := congrArg (Subgroup.comap q) htop
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
  let r := QuotientGroup.mk' D
  have hrange : (pCore 2 H).map r = ⊤ := by
    have hh := congrArg (Subgroup.map r) hsup
    rw [Subgroup.map_sup, show D.map r = ⊥ from (map_eq_bot_iff D).mpr (by
      simp only [r, QuotientGroup.ker_mk', le_refl]), bot_sup_eq,
      map_top_of_surjective r (QuotientGroup.mk'_surjective D)] at hh
    exact hh
  have htwo : IsPGroup 2 (H ⧸ D) := by
    have h := (pCore_isPGroup (p := 2) (G := H)).map r
    rw [hrange] at h
    exact h.of_equiv topEquiv
  exact hH D inferInstance htwo

/-- A rank-one image of a two-perfect group is already the image of any
nontrivial normal two-perfect subgroup on which the kernel is a two-group. -/
theorem rankOne_image_surjective
    {Y H : Type*} [Group Y] [Finite Y] [Group H] [Finite H]
    (f : Y →* H) (hf : Function.Surjective f)
    (hY : IsPPerfect 2 Y) (hr : primeRank 3 H ≤ 1)
    (hq : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (he : Monoid.exponent (Y ⧸ pCore 2 Y) ∣ 3)
    (A : Subgroup Y) [A.Normal] (hA : IsPPerfect 2 A) (hne : A ≠ ⊥)
    (hk : IsPGroup 2 (f.comp A.subtype).ker) :
    Function.Surjective (f.comp A.subtype) := by
  have hcore : (pCore 2 Y).map f ≤ pCore 2 H := by
    let := Subgroup.Normal.map (inferInstance : (pCore 2 Y).Normal) f hf
    exact le_sSup ⟨inferInstance, pCore_isPGroup.map f⟩
  let q : (Y ⧸ pCore 2 Y) →* (H ⧸ pCore 2 H) :=
    QuotientGroup.map _ _ f ((map_le_iff_le_comap).mp hcore)
  have hqs : Function.Surjective q :=
    QuotientGroup.map_surjective_of_surjective _ _ f
      (QuotientGroup.mk_surjective.comp hf) ((map_le_iff_le_comap).mp hcore)
  have hHq : IsPGroup 3 (H ⧸ pCore 2 H) := hq.of_surjective q hqs
  have hHe : Monoid.exponent (H ⧸ pCore 2 H) ∣ 3 := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    obtain ⟨y, rfl⟩ := hqs x
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp he y, map_one]
  let D := A.map f
  let : D.Normal := Subgroup.Normal.map inferInstance f hf
  have hD : IsPPerfect 2 D := hA.of_surjective (f.subgroupMap A) (f.subgroupMap_surjective A)
  have hDne : D ≠ ⊥ := by
    intro hbot
    have hker : (f.comp A.subtype).ker = ⊤ := by
      apply top_unique
      intro a _
      exact mem_bot.mp (hbot ▸ mem_map_of_mem f a.property)
    rw [hker] at hk
    exact pPerfect_subgroup_ne_pGroup A hne hA (hk.of_equiv topEquiv)
  have htop := normal_eq_top_of_rankOne (hY.of_surjective f hf) hr hHq hHe D hD hDne
  apply MonoidHom.range_eq_top.mp
  simpa only [MonoidHom.range_comp, range_subtype] using htop

/-- Transfer excludes central three-torsion in any finite perfect group of
three-rank at most one; no classification of simple quotients is needed. -/
theorem three_not_dvd_center_of_perfect_rankOne
    {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    (hr : primeRank 3 H ≤ 1) : ¬ 3 ∣ Nat.card (center H) := by
  let P : Sylow 3 H := Sylow.nonempty.some
  have hP : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  let q := QuotientGroup.mk' (center H)
  have hqr : primeRank 3 (H ⧸ center H) ≤ 1 := P.primeRank_quotient_le_one hP _
  have hh := PerfectCentralCovering.not_dvd_card_kernel_of_isCyclic_sylow q
    (QuotientGroup.mk'_surjective _) (by simp only [q, QuotientGroup.ker_mk', le_refl])
    (fun Q => Q.isCyclic_of_odd_of_primeRank_le_one (by decide) hqr)
  simpa only [q, QuotientGroup.ker_mk'] using hh

private theorem two_group_of_three_prime {A : Type*} [Group A] [Finite A]
    (hc : Nat.card (A ⧸ pCore 2 A) = 3) (D : Subgroup A)
    (hd : ¬ 3 ∣ Nat.card D) : IsPGroup 2 D := by
  let q := QuotientGroup.mk' (pCore 2 A)
  have hdiv : Nat.card (D.map q) ∣ 3 := hc ▸ (D.map q).card_subgroup_dvd_card
  have hsize : Nat.card (D.map q) = 1 :=
    ((Nat.dvd_prime Nat.prime_three).mp hdiv).resolve_right (fun h =>
      hd (h ▸ D.card_map_dvd q))
  have hle : D ≤ pCore 2 A := by
    have hh := (map_eq_bot_iff D).mp (Subgroup.card_eq_one.mp hsize)
    simpa only [q, QuotientGroup.ker_mk'] using hh
  exact pCore_isPGroup.to_le hle

/-- A subgroup of a two-by-three group whose image lies in a three-prime
center has two-group conjugation kernel. -/
theorem inner_kernel_isTwoGroup
    {A Q : Type*} [Group A] [Finite A] [Group Q] [Finite Q]
    (f : A →* Q) (hk : IsPGroup 2 f.ker)
    (ha : Nat.card (A ⧸ pCore 2 A) = 3)
    (hz : ¬ 3 ∣ Nat.card (center Q)) :
    IsPGroup 2 ((MulAut.conj : Q →* MulAut Q).comp f).ker := by
  let k := ((MulAut.conj : Q →* MulAut Q).comp f).ker
  apply two_group_of_three_prime ha k
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
  have hxA : orderOf (x : A) = 3 := (Subgroup.orderOf_coe x).trans hx
  have hfz : f (x : A) ∈ center Q := by
    apply mem_center_iff.mpr
    intro q
    have he := DFunLike.congr_fun (show MulAut.conj (f (x : A)) = 1 from x.property) q
    change f (x : A) * q * (f (x : A))⁻¹ = q at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  let z : center Q := ⟨f (x : A), hfz⟩
  have hzdvd : orderOf z ∣ 3 := by
    rw [← Subgroup.orderOf_coe z]
    exact hxA ▸ orderOf_map_dvd f (x : A)
  have hz1 : orderOf z = 1 :=
    ((Nat.dvd_prime Nat.prime_three).mp hzdvd).resolve_right (fun h =>
      hz (h ▸ orderOf_dvd_natCard z))
  have hfx : f (x : A) = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp hz1)
  let y : f.ker := ⟨x, hfx⟩
  have hy : orderOf y = 3 := (Subgroup.orderOf_coe y).symm.trans hxA
  have ho := hk.orderOf_coprime (by decide : Nat.Coprime 2 3) y
  rw [hy] at ho
  norm_num at ho

end CFSG.Quasithin.Chapter15.Section03.ComponentIntersection.InnerSplitting

end
