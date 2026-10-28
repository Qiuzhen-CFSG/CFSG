module

public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Theory.GroupTheory.RankOneSylowExtension.Overgroups

/-!
# Sylow overgroups of two-group extensions of A₅ and S₅

The standard Sylow four-group in A₅ fixes one letter and is transitive on the
other four. If a proper overgroup moved the fixed letter, it would be transitive
on all five, so its order would be divisible by twenty. Simplicity of A₅
excludes the resulting index at most three. Thus every proper Sylow overgroup
lies in the A₄ normalizer.

The rank-one extension theorem applies to every subgroup of S₅ containing A₅:
the index-two bound makes A₅ supplement its Sylow two-subgroup. It supplies a
proper normalizer containing every proper Sylow overgroup. A normal Sylow would
make its intersection with A₅ normal, contradicting that normalizer's
properness. Finally a normal two-group kernel lies in every Sylow two-subgroup,
so inverse images transport the unique maximal overgroup and nonnormality.

The four-word construction follows `Alternating.FiveBorelOvergroups`; its
published normalizer calculation is reused. The finite checks concern only
four words acting on five letters, never arbitrary subgroups.
Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.6.1, p.112; C.1.26, p.132; proof of 14.7.68(2), pp.1071–1072.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.SpecificGroups.FivePointSylowParabolic
private abbrev S5 := Equiv.Perm (Fin 5)
private abbrev A5 := alternatingGroup (Fin 5)
private def a : A5 := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def b : A5 := ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def word : Fin 4 → A5 := ![1, a, b, a * b]
private def four : Subgroup A5 where
  carrier := Set.range word
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    have hc : ∀ i j, ∃ k, word i * word j = word k := by decide +kernel
    rintro x y ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hc i j
    exact ⟨k, hk.symm⟩
  inv_mem' := by
    have hc : ∀ i, ∃ j, (word i)⁻¹ = word j := by decide +kernel
    rintro x ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hc i
    exact ⟨j, hj.symm⟩
private lemma four_card : Nat.card four = 4 := by
  have hi : Function.Injective word := by decide +kernel
  change Nat.card (Set.range word) = 4
  rw [← Nat.card_congr (Equiv.ofInjective _ hi)]
  simp
private noncomputable def fourSylow : Sylow 2 A5 := Sylow.ofCard four (by
  rw [four_card, nat_card_alternatingGroup]
  norm_num [Nat.factorial]
  rw [show 60 = 2 ^ 2 * 15 by decide, Nat.factorization_mul (by decide) (by decide),
    Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)]
  rfl)

private lemma normalizer_four : normalizer (four : Set A5) = MulAction.stabilizer A5 (4 : Fin 5) := by
  obtain ⟨i, hi⟩ := Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer fourSylow
  have hfix : ∀ j : Fin 5, (∀ k, (word k).val j = j) → j = 4 := by decide +kernel
  have he : i = 4 := hfix i (fun k => by
    have hk := four.le_normalizer (show word k ∈ four from ⟨k, rfl⟩)
    change word k ∈ normalizer (fourSylow : Set A5) at hk
    rw [hi] at hk
    exact hk)
  exact he ▸ hi

private lemma standard_overgroup (M : Subgroup A5) (hPM : four ≤ M) (hM : M ≠ ⊤) :
    M ≤ normalizer (four : Set A5) := by
  classical
  rw [normalizer_four]
  intro g hg
  change g.val 4 = 4
  by_contra hmove
  have horb : MulAction.orbit M (4 : Fin 5) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro j
    by_cases hj : j = 4
    · subst j
      exact MulAction.mem_orbit_self _
    · have hc : ∀ i j : Fin 5, i ≠ 4 → j ≠ 4 → ∃ k, (word k).val i = j := by decide +kernel
      obtain ⟨k, hk⟩ := hc (g.val 4) j hmove hj
      exact ⟨⟨word k * g, M.mul_mem (hPM ⟨k, rfl⟩) hg⟩, hk⟩
  have hfive : 5 ∣ Nat.card M := by
    have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup M (4 : Fin 5))
    rw [Nat.card_prod, horb, Nat.card_univ, Nat.card_fin] at hc
    exact ⟨_, hc.symm⟩
  have hfour : 4 ∣ Nat.card M := four_card ▸ card_dvd_of_le hPM
  have htwenty : 20 ∣ Nat.card M := (by decide : Nat.Coprime 4 5).mul_dvd_of_dvd_of_dvd hfour hfive
  have hbound := Nat.le_of_dvd (Nat.card_pos (α := M)) htwenty
  have hmul := M.card_mul_index
  have hcard : Nat.card A5 = 60 := by rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
  rw [hcard] at hmul
  have hi : M.index ≤ 3 := by nlinarith
  apply hM
  apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
  have hfac := Nat.factorial_le hi
  rw [hcard]
  norm_num [Nat.factorial] at hfac ⊢
  omega

/-- The A₅ Sylow normalizer contains every proper overgroup of that Sylow. -/
theorem alternating_sylow_overgroups (P : Sylow 2 (alternatingGroup (Fin 5))) :
    normalizer (P : Set (alternatingGroup (Fin 5))) ≠ ⊤ ∧
      ∀ M : Subgroup (alternatingGroup (Fin 5)),
        (P : Subgroup (alternatingGroup (Fin 5))) ≤ M → M ≠ ⊤ →
          M ≤ normalizer (P : Set (alternatingGroup (Fin 5))) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A5 P fourSylow
  let e := MulAut.conj g
  have hP : (P : Subgroup A5).map e.toMonoidHom = four := by
    have h := congrArg (fun Q : Sylow 2 A5 => (Q : Subgroup A5)) hg
    rwa [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  have hN : (normalizer (P : Set A5)).map e.toMonoidHom = normalizer (four : Set A5) := by
    change (normalizer ((P : Subgroup A5) : Set A5)).map e.toMonoidHom = _
    rw [map_equiv_normalizer_eq, hP]
  have hn : normalizer (four : Set A5) ≠ ⊤ := by
    rw [normalizer_four]
    intro ht
    have h := ht ▸ mem_top (⟨Equiv.swap 0 1 * Equiv.swap 2 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ : A5)
    change ((Equiv.swap 0 1 * Equiv.swap 2 4 : S5) (4 : Fin 5)) = 4 at h
    contradiction
  constructor
  · intro ht
    apply hn
    rw [← hN, ht, map_top_of_surjective e.toMonoidHom e.surjective]
  · intro M hPM hM
    have hm : M.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hM
      apply map_injective (f := e.toMonoidHom) e.injective
      simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using ht
    have hh := standard_overgroup (M.map e.toMonoidHom) (hP ▸ map_mono hPM) hm
    rw [← hN] at hh
    exact (map_le_map_iff_of_injective e.injective).mp hh

private lemma sylow_overgroups_of_equiv {H : Type*} [Group H] [Finite H]
    (e : H ≃* A5) (P : Sylow 2 H) :
    normalizer (P : Set H) ≠ ⊤ ∧
      ∀ M : Subgroup H, (P : Subgroup H) ≤ M → M ≠ ⊤ →
        M ≤ normalizer (P : Set H) := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ := alternating_sylow_overgroups Q
  have hN : (normalizer (P : Set H)).map e.toMonoidHom = normalizer (Q : Set A5) :=
    map_equiv_normalizer_eq _ e
  constructor
  · intro ht
    apply hQ.1
    rw [← hN, ht, map_top_of_surjective e.toMonoidHom e.surjective]
  · intro M hPM hM
    have hm : M.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hM
      apply map_injective (f := e.toMonoidHom) e.injective
      simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using ht
    have hh := hQ.2 (M.map e.toMonoidHom) (map_mono hPM) hm
    rw [← hN] at hh
    exact (map_le_map_iff_of_injective e.injective).mp hh

private lemma image_overgroup_bound (R : Subgroup S5) (hA : A5 ≤ R)
    (P : Sylow 2 R) :
    ∃ B : Subgroup R, B ≠ ⊤ ∧ (P : Subgroup R) ≤ B ∧
      (∀ M : Subgroup R, (P : Subgroup R) ≤ M → M ≠ ⊤ → M ≤ B) ∧
      ¬ (P : Subgroup R).Normal := by
  let L : Subgroup R := A5.subgroupOf R
  let e : L ≃* A5 := subgroupOfEquivOfLe hA
  have hidx : L.index ∣ 2 := by
    change A5.relIndex R ∣ 2
    rw [← alternatingGroup.index_eq_two (α := Fin 5)]
    exact A5.relIndex_dvd_index_of_normal R
  have hgen : L ⊔ (P : Subgroup R) = ⊤ := by
    have hd : (L ⊔ (P : Subgroup R)).index ∣ 2 :=
      (index_dvd_of_le (show L ≤ L ⊔ (P : Subgroup R) from le_sup_left)).trans hidx
    have hn : ¬ 2 ∣ (L ⊔ (P : Subgroup R)).index := fun h =>
      P.not_dvd_index (h.trans (index_dvd_of_le (show (P : Subgroup R) ≤ L ⊔ P from le_sup_right)))
    apply index_eq_one.mp
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_right (fun h => hn (by rw [h]))
  obtain ⟨hb, hp, hm⟩ := RankOneSylowExtension.ambient_normalizer_properties L P hgen
    (fun Q => (sylow_overgroups_of_equiv e Q).1)
    (fun Q => (sylow_overgroups_of_equiv e Q).2)
  refine ⟨_, hb, hp, hm, ?_⟩
  intro hn
  let := hn
  exact hb (normalizer_eq_top _)

/-- A five-point image containing A₅ and a two-group kernel force a unique
maximal Sylow overgroup, and the Sylow subgroup is not normal. -/
theorem unique_maximal_of_five_point_map {E : Type*} [Group E] [Finite E]
    (f : E →* Equiv.Perm (Fin 5)) (hker : IsPGroup 2 f.ker)
    (hA : alternatingGroup (Fin 5) ≤ f.range) (P : Sylow 2 E) :
    (∃! M : Subgroup E, IsCoatom M ∧ (P : Subgroup E) ≤ M) ∧
      ¬ (P : Subgroup E).Normal := by
  let q : E →* f.range := f.rangeRestrict
  have hq : Function.Surjective q := f.rangeRestrict_surjective
  have hk : q.ker ≤ (P : Subgroup E) := by
    rw [show q.ker = f.ker from f.ker_rangeRestrict]
    exact hker.le_sylow_of_normal P
  let Q := P.mapSurjective hq
  obtain ⟨B, hB, hQB, hbound, hnQ⟩ := image_overgroup_bound f.range hA Q
  have hproper : B.comap q ≠ ⊤ := by
    intro ht
    apply hB
    apply comap_injective hq
    simpa only [comap_top] using ht
  have hPB : (P : Subgroup E) ≤ B.comap q := map_le_iff_le_comap.mp hQB
  have hmax (M : Subgroup E) (hPM : (P : Subgroup E) ≤ M) (hM : M ≠ ⊤) :
      M ≤ B.comap q := by
    apply map_le_iff_le_comap.mp
    apply hbound (M.map q) (map_mono hPM)
    intro ht
    apply hM
    have hc := congrArg (Subgroup.comap q) ht
    simpa only [comap_map_eq_self (hk.trans hPM), comap_top] using hc
  have hcoat : IsCoatom (B.comap q) := by
    refine ⟨hproper, ?_⟩
    intro M hBM
    by_contra hM
    exact hBM.not_ge (hmax M (hPB.trans hBM.le) hM)
  refine ⟨⟨B.comap q, ⟨hcoat, hPB⟩, ?_⟩, ?_⟩
  · intro M hM
    exact ((hM.1.le_iff.mp (hmax M hM.2 hM.1.ne_top)).resolve_left hproper).symm
  · intro hn
    let := hn
    exact hnQ (Subgroup.Normal.map inferInstance q hq)

end Theory.SpecificGroups.FivePointSylowParabolic
