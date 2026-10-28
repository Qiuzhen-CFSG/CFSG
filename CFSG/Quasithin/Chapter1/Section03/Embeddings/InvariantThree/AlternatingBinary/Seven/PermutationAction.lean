module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.AlternatingBinary.Seven.Reduction
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Theory.GroupTheory.PResidual.SubnormalSupplement

/-!
# An invariant line for a permutable Sylow pair in A₇

Let D have order nine and permute with a Sylow two-subgroup P of A₇.
Their join H has order 72. It cannot fix a point: restriction to the other
six points would give an index-five subgroup of the simple group A₆.
Consequently its orbits have size at most four. Sylow conjugacy puts a
conjugate of (0123)(45) in P, forcing a four-point orbit. That orbit is unique
on seven points, so every permutation normalizing H preserves it.

The kernel C of D's action on this orbit acts only on the complementary
three points, and hence has order dividing three. It is nontrivial, since
otherwise D would embed in S₄, whose order is not divisible by nine.
Uniqueness of the orbit makes C invariant under every permutation normalizing
both P and D, including odd permutations. This proves the exact input to the
central-cover reduction without an additional hypothesis.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.4, printed p.511 (PDF p.528).
-/

@[expose] public section

open Subgroup Equiv MulAction
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.AlternatingBinary
namespace SevenAction
private abbrev A := alternatingGroup (Fin 7)

private theorem no_fixed_point (H : Subgroup A) (hc : Nat.card H = 72) (a : Fin 7)
    (ha : ∀ g ∈ H, (g : Perm (Fin 7)) a = a) : False := by
  classical
  let s : Finset (Fin 7) := Finset.univ.erase a
  have hs : Nat.card s = 6 := by simp [s]
  have hs' : Nontrivial s := by
    apply (Fintype.one_lt_card_iff_nontrivial).mp
    simpa only [Nat.card_eq_fintype_card] using (show 1 < Nat.card s by omega)
  let f := alternatingGroup.ofSubtype s
  have hf : Function.Injective f := alternatingGroup.ofSubtype_injective
  have hH : H ≤ f.range := by
    intro g hg
    apply (alternatingGroup.mem_range_ofSubtype_iff s g).mpr
    intro b hb
    simp only [s, Finset.mem_erase, Finset.mem_univ, and_true]
    intro he
    subst b
    exact (Perm.mem_support.mp hb) (ha g hg)
  let K := H.comap f
  have hK : Nat.card K = 72 := by
    rw [← card_map_of_injective hf, map_comap_eq_self hH, hc]
  have hA : Nat.card (alternatingGroup s) = 360 := by
    rw [nat_card_alternatingGroup, hs]
    norm_num
  have hi : K.index = 5 := by
    have h := K.card_mul_index
    rw [hK, hA] at h
    omega
  let _ : IsSimpleGroup (alternatingGroup s) := alternatingGroup.isSimpleGroup (by simpa only [← Nat.card_eq_fintype_card, hs] using (by decide : 5 ≤ 6))
  have ht : K = ⊤ := Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt K (by
    rw [hi, hA]
    decide)
  rw [ht, card_top, hA] at hK
  omega

private theorem orbit_card_le_four (H : Subgroup A) (hc : Nat.card H = 72) (a : Fin 7) :
    Nat.card (orbit H a) ≤ 4 := by
  classical
  have hle : Nat.card (orbit H a) ≤ 7 := (Set.ncard_le_card _).trans_eq (by simp)
  have hd : Nat.card (orbit H a) ∣ 72 := by
    rw [Nat.card_congr (orbitEquivQuotientStabilizer H a)]
    exact hc ▸ (stabilizer H a).index_dvd_card
  have hn : Nat.card (orbit H a) ≠ 6 := by
    intro hn
    have hcomp : (orbit H a)ᶜ.ncard = 1 := by
      rw [Set.ncard_compl]
      change Nat.card (Fin 7) - Nat.card (orbit H a) = 1
      rw [hn]
      norm_num
    obtain ⟨b, hb⟩ := Set.ncard_eq_one.mp hcomp
    have hb' : b ∉ orbit H a := by
      change b ∈ (orbit H a)ᶜ
      simp [hb]
    apply no_fixed_point H hc b
    intro g hg
    have hgb : (⟨g, hg⟩ : H) • b ∉ orbit H a := by
      intro h
      have h' := mapsTo_smul_orbit (⟨g, hg⟩ : H)⁻¹ a h
      apply hb'
      change (⟨g, hg⟩ : H)⁻¹ • ((⟨g, hg⟩ : H) • b) ∈ orbit H a at h'
      simpa only [inv_smul_smul] using h'
    have : (g : Perm (Fin 7)) b ∈ (orbit H a)ᶜ := hgb
    simpa [hb] using this
  interval_cases hc' : Nat.card (orbit H a) <;> norm_num at *

private def fourCycle : A :=
  ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5, by
    simp only [Perm.mem_alternatingGroup, map_mul]
    decide⟩

private theorem fourCycle_order : orderOf fourCycle = 4 := by
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)

private theorem large_orbit (P : Sylow 2 A) (H : Subgroup A) (hPH : (P : Subgroup A) ≤ H) :
    ∃ a : Fin 7, 4 ≤ Nat.card (orbit H a) := by
  have hp : IsPGroup 2 (zpowers fourCycle) := IsPGroup.of_card (by
    rw [Nat.card_zpowers, fourCycle_order]
    rfl : Nat.card (zpowers fourCycle) = 2 ^ 2)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_smul_eq A Q P
  have hq : MulAut.conj g fourCycle ∈ P := by
    rw [← hg]
    exact Subgroup.smul_mem_pointwise_smul fourCycle (MulAut.conj g) (Q : Subgroup A)
      (hQ (mem_zpowers fourCycle))
  let p : H := ⟨MulAut.conj g fourCycle, hPH hq⟩
  have ht : ∀ i : Fin 4, ((fourCycle ^ i.val : A) : Perm (Fin 7)) 0 = i.castLE (by decide) := by
    decide
  let f : Fin 4 → orbit H ((g : Perm (Fin 7)) 0) := fun i =>
    ⟨(g : Perm (Fin 7)) (i.castLE (by decide)), by
      refine ⟨p ^ i.val, ?_⟩
      change ((MulAut.conj g fourCycle) ^ i.val : A).val ((g : Perm (Fin 7)) 0) = _
      rw [← map_pow]
      change (g.val * (fourCycle ^ i.val).val * g.val⁻¹) (g.val 0) = _
      simp only [Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_apply, ht]⟩
  refine ⟨g.val 0, ?_⟩
  have hf : Function.Injective f := by
    intro i j he
    have hij := g.val.injective (congrArg Subtype.val he)
    exact Fin.ext (congrArg (fun x : Fin 7 => x.val) hij)
  simpa using Nat.card_le_card_of_injective f hf

private theorem four_orbit_unique (H : Subgroup A) {a b : Fin 7}
    (ha : Nat.card (orbit H a) = 4) (hb : Nat.card (orbit H b) = 4) :
    orbit H a = orbit H b := by
  by_contra hn
  have hd : Disjoint (orbit H a) (orbit H b) := by
    apply Set.disjoint_left.mpr
    intro c hca hcb
    exact hn ((orbit_eq_iff.mpr hca).symm.trans (orbit_eq_iff.mpr hcb))
  have hle := Set.ncard_le_card (orbit H a ∪ orbit H b)
  rw [Set.ncard_union_eq hd] at hle
  change Nat.card (orbit H a) + Nat.card (orbit H b) ≤ Nat.card (Fin 7) at hle
  rw [ha, hb] at hle
  norm_num at hle

private theorem conjugate_apply (σ : Perm (Fin 7)) (g : A) (a : Fin 7) :
    ((MulAut.conjNormal σ g : A) : Perm (Fin 7)) (σ a) = σ (g.val a) := by
  rw [MulAut.conjNormal_apply]
  simp only [Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_apply]

private theorem orbit_image (H : Subgroup A) (σ : Perm (Fin 7))
    (hσ : ∀ x : A, MulAut.conjNormal σ x ∈ H ↔ x ∈ H) (a : Fin 7) :
    σ '' orbit H a = orbit H (σ a) := by
  ext b
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    refine ⟨⟨MulAut.conjNormal σ g.val, (hσ g).mpr g.property⟩, ?_⟩
    exact conjugate_apply σ g a
  · rintro ⟨g, rfl⟩
    let u : A := (MulAut.conjNormal σ).symm g.val
    have hu : u ∈ H := (hσ u).mp (by
      dsimp [u]
      rw [MulEquiv.apply_symm_apply]
      exact g.property)
    refine ⟨u.val a, ⟨⟨u, hu⟩, rfl⟩, ?_⟩
    have he := conjugate_apply σ u a
    rw [show MulAut.conjNormal σ u = g.val from (MulAut.conjNormal σ).apply_symm_apply g.val] at he
    exact he.symm

private theorem preserves_four_orbit (H : Subgroup A) {a : Fin 7}
    (ha : Nat.card (orbit H a) = 4) (σ : Perm (Fin 7))
    (hσ : ∀ x : A, MulAut.conjNormal σ x ∈ H ↔ x ∈ H) :
    σ '' orbit H a = orbit H a := by
  have hc : Nat.card (orbit H (σ a)) = 4 := by
    change (orbit H (σ a)).ncard = 4
    rw [← orbit_image H σ hσ a, Set.ncard_image_of_injective _ σ.injective]
    exact ha
  rw [orbit_image H σ hσ a, four_orbit_unique H hc ha]

private theorem kernel_line (H D : Subgroup A) (hDH : D ≤ H)
    (hD : Nat.card D = 9) (a : Fin 7) (ha : Nat.card (orbit H a) = 4) :
    ∃ C : Subgroup A, C ≤ D ∧ Nat.card C = 3 ∧
      ∀ σ : Perm (Fin 7),
        (∀ x : A, MulAut.conjNormal σ x ∈ H ↔ x ∈ H) →
        (∀ x : A, MulAut.conjNormal σ x ∈ D ↔ x ∈ D) →
        ∀ x ∈ C, MulAut.conjNormal σ x ∈ C := by
  classical
  let f : D →* Perm (orbit H a) := (toPermHom H (orbit H a)).comp (inclusion hDH)
  let C := f.ker.map D.subtype
  have hC : Nat.card C = Nat.card f.ker := card_map_of_injective D.subtype_injective
  have hfix (x : A) : x ∈ C ↔ x ∈ D ∧ ∀ b ∈ orbit H a, x.val b = b := by
    constructor
    · rintro ⟨d, hd, rfl⟩
      refine ⟨d.property, ?_⟩
      intro b hb
      exact congrArg Subtype.val (congrArg (fun q : Perm (orbit H a) => q ⟨b, hb⟩) hd)
    · rintro ⟨hx, h⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      apply Perm.ext
      intro b
      exact Subtype.ext (h b b.property)
  let s : Finset (Fin 7) := (orbit H a).toFinsetᶜ
  have hs : Nat.card s = 3 := by
    simp only [s, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl,
      Fintype.card_fin]
    rw [← Set.ncard_eq_toFinset_card']
    change 7 - Nat.card (orbit H a) = 3
    omega
  let j := alternatingGroup.ofSubtype s
  have hj : Nat.card j.range = 3 := by
    have hn : Nontrivial s := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    rw [Nat.card_eq_fintype_card, Fintype.card_coeSort_range alternatingGroup.ofSubtype_injective,
      ← Nat.card_eq_fintype_card, nat_card_alternatingGroup, hs]
    norm_num
  have hCj : C ≤ j.range := by
    intro x hx
    apply (alternatingGroup.mem_range_ofSubtype_iff s x).mpr
    intro b hb
    change b ∈ (orbit H a).toFinsetᶜ
    simp only [Finset.mem_compl, Set.mem_toFinset]
    intro hba
    exact (Perm.mem_support.mp hb) (((hfix x).mp hx).2 b hba)
  have hdiv : Nat.card C ∣ 3 := hj ▸ card_dvd_of_le hCj
  have hcard : Nat.card C = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h | h
    · have hk : Nat.card f.ker = 1 := hC ▸ h
      have he := f.ker.card_mul_index
      rw [hk, one_mul, index_ker, hD] at he
      have hi := f.range.card_subgroup_dvd_card
      rw [he, Nat.card_perm, ha] at hi
      norm_num at hi
    · exact h
  refine ⟨C, map_subtype_le _, hcard, ?_⟩
  intro σ hHσ hDσ x hx
  have hx' := (hfix x).mp hx
  apply (hfix _).mpr
  refine ⟨(hDσ x).mpr hx'.1, ?_⟩
  intro b hb
  have he := preserves_four_orbit H ha σ hHσ
  have hb' : σ⁻¹ b ∈ orbit H a := by
    have : b ∈ σ '' orbit H a := he.symm ▸ hb
    obtain ⟨c, hc, rfl⟩ := this
    simpa only [Perm.inv_def, Equiv.symm_apply_apply] using hc
  rw [MulAut.conjNormal_apply]
  change σ (x.val (σ⁻¹ b)) = b
  rw [hx'.2 _ hb']
  exact σ.apply_symm_apply b

private theorem sylow_two_card (P : Sylow 2 A) : Nat.card P = 8 := by
  rw [P.card_eq_multiplicity, nat_card_alternatingGroup]
  norm_num [Nat.factorial]
  rw [show 2520 = 2 ^ 3 * 315 by decide,
    Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)]
  rfl

private theorem pair_card (P : Sylow 2 A) (D : Subgroup A) (hc : Nat.card D = 9)
    (hp : (D : Set A) * (P : Set A) = (P : Set A) * (D : Set A)) :
    Nat.card ↥(D ⊔ (P : Subgroup A)) = 72 := by
  let H : Subgroup A := D ⊔ (P : Subgroup A)
  have hd : Disjoint D (P : Subgroup A) := disjoint_of_coprime_natCard
    (by rw [hc, sylow_two_card]; decide)
  let m : D × P → H := fun p =>
    ⟨(p.1 : A) * (p.2 : A), mul_mem_sup p.1.property p.2.property⟩
  have hi : Function.Injective m := fun _ _ h =>
    mul_injective_of_disjoint hd (congrArg Subtype.val h)
  have hs : Function.Surjective m := by
    intro x
    have hx : (x : A) ∈ (D : Set A) * (P : Set A) := by
      change (x : A) ∈ (D : Set A) * ((P : Subgroup A) : Set A)
      rw [← Subgroup.coe_sup_of_set_mul_comm D (P : Subgroup A) hp]
      exact x.property
    obtain ⟨d, hd, p, hp, he⟩ := hx
    exact ⟨(⟨d, hd⟩, ⟨p, hp⟩), Subtype.ext he⟩
  change Nat.card H = 72
  rw [← Nat.card_congr (Equiv.ofBijective m ⟨hi, hs⟩), Nat.card_prod, hc, sylow_two_card]

private theorem map_eq_self (K : Subgroup A) (e : MulAut A)
    (h : ∀ x, e x ∈ K ↔ x ∈ K) : K.map e.toMonoidHom = K := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).mpr hx
  · intro hy
    exact ⟨e.symm y, (h _).mp (by simpa using hy), e.apply_symm_apply y⟩

private theorem preserves_sup (P D : Subgroup A) (e : MulAut A)
    (hP : ∀ x, e x ∈ P ↔ x ∈ P) (hD : ∀ x, e x ∈ D ↔ x ∈ D) :
    ∀ x, e x ∈ D ⊔ P ↔ x ∈ D ⊔ P := by
  have he : (D ⊔ P).map e.toMonoidHom = D ⊔ P := by
    rw [Subgroup.map_sup, map_eq_self D e hD, map_eq_self P e hP]
  intro x
  have hx : e x ∈ (D ⊔ P).map e.toMonoidHom ↔ x ∈ D ⊔ P := by
    rw [mem_map_equiv]
    simp
  simpa only [he] using hx

end SevenAction

/-- The order-nine member of a permutable Sylow pair in A₇ has a subgroup of
order three preserved by all permutation conjugations preserving the pair. -/
theorem seven_permutationLine : SevenPermutationLine := by
  intro P D hD hp
  let H : Subgroup (alternatingGroup (Fin 7)) := D ⊔ (P : Subgroup (alternatingGroup (Fin 7)))
  have hH : Nat.card H = 72 := SevenAction.pair_card P D hD hp
  obtain ⟨a, ha⟩ := SevenAction.large_orbit P H le_sup_right
  have ha' : Nat.card (orbit H a) = 4 := le_antisymm (SevenAction.orbit_card_le_four H hH a) ha
  obtain ⟨C, hCD, hCcard, hC⟩ := SevenAction.kernel_line H D le_sup_left hD a ha'
  refine ⟨C, hCD, hCcard, ?_⟩
  intro σ hPσ hDσ
  exact hC σ (SevenAction.preserves_sup _ _ (MulAut.conjNormal σ) hPσ hDσ) hDσ

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.AlternatingBinary
