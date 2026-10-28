module

public import Theory.SpecificGroups.Alternating.FiveExtensionAction
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Five-point coordinates for Borel overgroups

An A₅ Borel is the normalizer of a Sylow four-group and hence an even point
stabilizer A₄. Its index five makes it maximal in A₅. A proper subgroup of
S₅ containing this Borel and an odd element therefore normalizes that A₄;
two double transpositions show that its normalizer fixes the same point.
Orbit-stabilizer then gives the actual equivariant coset coordinates.

The construction keeps an arbitrary prescribed S₅ equivalence and its
restriction to A₅. It never replaces them by an unrelated coset action.
Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.20, printed p.955 (PDF p.972).
-/

public section
namespace Theory.SpecificGroups.Alternating.FiveBorelOvergroups


open Subgroup
private abbrev S5 := Equiv.Perm (Fin 5)
private abbrev A5 := alternatingGroup (Fin 5)

private def evenStabilizer (i : Fin 5) : Subgroup A5 := MulAction.stabilizer A5 i
private instance (i : Fin 5) : DecidablePred (· ∈ evenStabilizer i) := fun x => inferInstanceAs (Decidable (x.val i = i))

private lemma evenStabilizer_card (i : Fin 5) : Nat.card (evenStabilizer i) = 12 := by
  rw [Nat.card_eq_fintype_card]
  revert i
  decide +kernel

private lemma evenStabilizer_coatom (i : Fin 5) : IsCoatom (evenStabilizer i) := by
  have hi : (evenStabilizer i).index = 5 := by
    have h := (evenStabilizer i).card_mul_index
    rw [evenStabilizer_card, nat_card_alternatingGroup] at h
    norm_num [Nat.factorial] at h
    omega
  refine ⟨?_, ?_⟩
  · intro h
    simp [h] at hi
  · intro D hD
    have hd := index_dvd_of_le hD.le
    rw [hi] at hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h | h
    · exact index_eq_one.mp h
    · have := index_strictAnti hD
      omega

private lemma evenStabilizer_map (i : Fin 5) :
    (evenStabilizer i).map A5.subtype = A5 ⊓ MulAction.stabilizer S5 i := by
  ext g
  simp only [mem_map, mem_inf, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.property, hg⟩
  · rintro ⟨hg, hi⟩
    exact ⟨⟨g, hg⟩, hi, rfl⟩

private lemma evenStabilizer_normalizer (i : Fin 5) :
    normalizer ((A5 ⊓ MulAction.stabilizer S5 i : Subgroup S5) : Set S5) =
      MulAction.stabilizer S5 i := by
  let a (j : Fin 5) : S5 :=
    Equiv.swap 4 j * (Equiv.swap 0 1 * Equiv.swap 2 3) * Equiv.swap 4 j
  let b (j : Fin 5) : S5 :=
    Equiv.swap 4 j * (Equiv.swap 0 2 * Equiv.swap 1 3) * Equiv.swap 4 j
  have ha : ∀ j, (a j).sign = 1 ∧ a j j = j := by decide +kernel
  have hb : ∀ j, (b j).sign = 1 ∧ b j j = j := by decide +kernel
  have hfix : ∀ i j, a i j = j → b i j = j → j = i := by decide +kernel
  ext g
  constructor
  · intro hg
    have fix (x : S5) (hx : x.sign = 1 ∧ x i = i) : x (g⁻¹ i) = g⁻¹ i := by
      have hxi : x ∈ A5 ⊓ MulAction.stabilizer S5 i :=
        ⟨Equiv.Perm.mem_alternatingGroup.mpr hx.1, hx.2⟩
      have hconj := ((mem_normalizer_iff.mp hg x).mp hxi).2
      change g (x (g⁻¹ i)) = i at hconj
      exact g.injective (by simpa using hconj)
    have hi := hfix i (g⁻¹ i) (fix (a i) (ha i)) (fix (b i) (hb i))
    change g i = i
    simpa using congrArg g hi.symm
  · intro hg x
    change g i = i at hg
    have hginv : g⁻¹ i = i := g.injective (by simpa using hg.symm)
    have hA : x ∈ A5 ↔ g * x * g⁻¹ ∈ A5 :=
      (show g ∈ normalizer (A5 : Set S5) by rw [normalizer_eq_top]; trivial) x
    change (x ∈ A5 ∧ x i = i) ↔ (g * x * g⁻¹ ∈ A5 ∧ (g * x * g⁻¹) i = i)
    rw [← hA]
    apply and_congr_right
    intro _
    change x i = i ↔ g (x (g⁻¹ i)) = i
    rw [hginv]
    exact ⟨fun h => by rw [h, hg], fun h => g.injective (h.trans hg.symm)⟩

private lemma overlap_eq_stabilizer (J : Subgroup S5) (i : Fin 5)
    (hB : A5 ⊓ MulAction.stabilizer S5 i ≤ J) (hJ : J ≠ ⊤)
    (t : S5) (ht : t ∈ J) (htodd : t ∉ A5) :
    J = MulAction.stabilizer S5 i := by
  let D : Subgroup A5 := J.subgroupOf A5
  have hBD : evenStabilizer i ≤ D := by
    intro x hx
    exact hB ⟨x.property, hx⟩
  have hD : D = evenStabilizer i := by
    rcases (evenStabilizer_coatom i).le_iff.mp hBD with htop | heq
    · exfalso
      apply hJ
      apply top_unique
      intro x _
      have heven (a : S5) (ha : a ∈ A5) : a ∈ J := by
        have : (⟨a, ha⟩ : A5) ∈ D := by rw [htop]; trivial
        exact this
      by_cases hx : x ∈ A5
      · exact heven x hx
      · have hx' : x * t⁻¹ ∈ A5 := by
          rw [mul_mem_iff_of_index_two alternatingGroup.index_eq_two, inv_mem_iff]
          exact iff_of_false hx htodd
        simpa only [inv_mul_cancel_right] using J.mul_mem (heven _ hx') ht
    · exact heq
  have hJA : J ⊓ A5 = A5 ⊓ MulAction.stabilizer S5 i := by
    have h := congrArg (Subgroup.map A5.subtype) hD
    rw [subgroupOf_map_subtype, evenStabilizer_map] at h
    exact h
  have hn : J ≤ normalizer ((J ⊓ A5 : Subgroup S5) : Set S5) := by
    intro j hj x
    constructor
    · rintro ⟨hxJ, hxA⟩
      exact ⟨J.mul_mem (J.mul_mem hj hxJ) (J.inv_mem hj),
        (inferInstance : A5.Normal).conj_mem x hxA j⟩
    · rintro ⟨hxJ, hxA⟩
      constructor
      · have := J.mul_mem (J.mul_mem (J.inv_mem hj) hxJ) hj
        simpa [mul_assoc] using this
      · have := (inferInstance : A5.Normal).conj_mem (j * x * j⁻¹) hxA j⁻¹
        simpa [mul_assoc] using this
  rw [hJA, evenStabilizer_normalizer] at hn
  apply le_antisymm hn
  intro x hx
  by_cases ha : x ∈ A5
  · exact hB ⟨ha, hx⟩
  · have hxt : x * t⁻¹ ∈ A5 ⊓ MulAction.stabilizer S5 i := by
      constructor
      · change x * t⁻¹ ∈ (alternatingGroup (Fin 5) : Subgroup S5)
        rw [mul_mem_iff_of_index_two alternatingGroup.index_eq_two, inv_mem_iff]
        exact iff_of_false ha htodd
      · exact (MulAction.stabilizer S5 i).mul_mem hx ((MulAction.stabilizer S5 i).inv_mem (hn ht))
    simpa only [inv_mul_cancel_right] using J.mul_mem (hB hxt) ht



open Subgroup
variable {H : Type*} [Group H]

private theorem quotient_coordinates (e : H ≃* Equiv.Perm (Fin 5)) (J : Subgroup H) (i : Fin 5)
    (hJ : J.map e.toMonoidHom = MulAction.stabilizer (Equiv.Perm (Fin 5)) i) :
    ∃ d : (H ⧸ J) ≃ Fin 5, ∀ h ω, d (h • ω) = e h (d ω) := by
  let : MulAction H (Fin 5) := MulAction.compHom (Fin 5) e.toMonoidHom
  have hs : J = MulAction.stabilizer H i := by
    ext h
    change h ∈ J ↔ e h i = i
    change h ∈ J ↔ e h ∈ MulAction.stabilizer (Equiv.Perm (Fin 5)) i
    rw [← hJ, Subgroup.mem_map_equiv]
    simp
  let a := Subgroup.quotientEquivOfEq hs
  have hsurj : Function.Surjective (MulAction.ofQuotientStabilizer H i) := by
    intro j
    refine ⟨QuotientGroup.mk (e.symm (Equiv.swap i j)), ?_⟩
    change e (e.symm (Equiv.swap i j)) i = j
    simp
  let b : (H ⧸ MulAction.stabilizer H i) ≃ Fin 5 :=
    Equiv.ofBijective _ ⟨MulAction.injective_ofQuotientStabilizer H i, hsurj⟩
  refine ⟨a.trans b, ?_⟩
  intro h ω
  induction ω using Quotient.inductionOn with
  | h x =>
    change e (h * x) i = e h (e x i)
    rw [map_mul]
    rfl



open Subgroup
open scoped Pointwise
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

private theorem normalizer_four : normalizer (four : Set A5) = MulAction.stabilizer A5 (4 : Fin 5) := by
  have hc : ∀ g : A5, (∀ i, ∃ j, g * word i * g⁻¹ = word j) ↔ g.val 4 = 4 := by
    decide +kernel
  ext g
  constructor
  · intro hg
    apply (hc g).mp
    intro i
    obtain ⟨j, hj⟩ := (hg (word i)).mp ⟨i, rfl⟩
    exact ⟨j, hj.symm⟩
  · intro hg x
    change g.val 4 = 4 at hg
    have hg' : g⁻¹.val 4 = 4 := g.val.injective (by simpa using hg.symm)
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := (hc g).mpr hg i
      exact ⟨j, hj.symm⟩
    · rintro ⟨i, hi⟩
      obtain ⟨j, hj⟩ := (hc g⁻¹).mpr hg' i
      refine ⟨j, ?_⟩
      rw [← hj, hi]
      simp [mul_assoc]

/-- Each Sylow four-group in A₅ has a point stabilizer as its normalizer. -/
theorem sylow_normalizer_eq_stabilizer (P : Sylow 2 (alternatingGroup (Fin 5))) :
    ∃ i : Fin 5, normalizer (P : Set (alternatingGroup (Fin 5))) =
      MulAction.stabilizer (alternatingGroup (Fin 5)) i := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A5 P fourSylow
  have hP : (P : Subgroup A5).map (MulAut.conj g).toMonoidHom = four := by
    have h := congrArg (fun Q : Sylow 2 A5 => (Q : Subgroup A5)) hg
    rwa [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  have hN : (normalizer (P : Set A5)).map (MulAut.conj g).toMonoidHom =
      MulAction.stabilizer A5 (4 : Fin 5) := by
    change (normalizer ((P : Subgroup A5) : Set A5)).map (MulAut.conj g).toMonoidHom = _
    rw [map_equiv_normalizer_eq, hP, normalizer_four]
  refine ⟨g⁻¹.val 4, ?_⟩
  ext x
  have hm : x ∈ normalizer (P : Set A5) ↔
      MulAut.conj g x ∈ MulAction.stabilizer A5 (4 : Fin 5) := by
    rw [← hN, mem_map_equiv]
    simp [MulAut.conj_apply, mul_assoc]
  rw [hm]
  change g.val (x.val (g⁻¹.val 4)) = 4 ↔ x.val (g⁻¹.val 4) = g⁻¹.val 4
  exact ⟨fun h => g.val.injective (by simpa using h), fun h => by rw [h]; simp⟩

variable {H : Type*} [Group H]
/-- A proper overgroup of an A₅ Borel containing an odd permutation is
the point stabilizer in the prescribed compatible five-point action. -/
theorem exists_stabilizer_of_borel (K J : Subgroup H)
    (e : H ≃* Equiv.Perm (Fin 5)) (eK : K ≃* alternatingGroup (Fin 5))
    (he : ∀ k : K, e k = eK k) (P : Sylow 2 K)
    (hB : (normalizer (P : Set K)).map K.subtype ≤ J)
    (hJ : J ≠ ⊤) (t : H) (ht : t ∈ J) (htK : t ∉ K) :
    ∃ i : Fin 5, J.map e.toMonoidHom =
      MulAction.stabilizer (Equiv.Perm (Fin 5)) i := by
  let : Finite H := Finite.of_equiv S5 e.symm.toEquiv
  let P' := P.mapSurjective (f := eK.toMonoidHom) eK.surjective
  obtain ⟨i, hi⟩ := sylow_normalizer_eq_stabilizer P'
  have hhom : e.toMonoidHom.comp K.subtype =
      (alternatingGroup (Fin 5)).subtype.comp eK.toMonoidHom := by
    apply MonoidHom.ext
    exact he
  have hBmap : ((normalizer (P : Set K)).map K.subtype).map e.toMonoidHom =
      A5 ⊓ MulAction.stabilizer S5 i := by
    rw [map_map, hhom, ← map_map]
    change ((normalizer ((P : Subgroup K) : Set K)).map eK.toMonoidHom).map _ = _
    rw [map_equiv_normalizer_eq]
    change (normalizer (P' : Set A5)).map A5.subtype = _
    rw [hi]
    exact evenStabilizer_map i
  have hBJ : A5 ⊓ MulAction.stabilizer S5 i ≤ J.map e.toMonoidHom := by
    rw [← hBmap]
    exact map_mono hB
  have hJ' : J.map e.toMonoidHom ≠ ⊤ := by
    intro h
    apply hJ
    apply (map_injective (f := e.toMonoidHom) e.injective)
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using h
  have htodd : e t ∉ A5 := by
    intro h
    obtain ⟨k, hk⟩ := eK.surjective ⟨e t, h⟩
    have hkt : k.val = t := e.injective ((he k).trans (congrArg Subtype.val hk))
    exact htK (hkt ▸ k.property)
  exact ⟨i, overlap_eq_stabilizer (J.map e.toMonoidHom) i hBJ hJ' (e t)
      (mem_map.mpr ⟨t, ht, rfl⟩) htodd⟩

/-- Equivariant coset coordinates for the actual Borel overgroup. -/
theorem coordinates_of_borel (K J : Subgroup H)
    (e : H ≃* Equiv.Perm (Fin 5)) (eK : K ≃* alternatingGroup (Fin 5))
    (he : ∀ k : K, e k = eK k) (P : Sylow 2 K)
    (hB : (normalizer (P : Set K)).map K.subtype ≤ J)
    (hJ : J ≠ ⊤) (t : H) (ht : t ∈ J) (htK : t ∉ K) :
    ∃ d : (H ⧸ J) ≃ Fin 5, ∀ h ω, d (h • ω) = e h (d ω) := by
  obtain ⟨i, hi⟩ := exists_stabilizer_of_borel K J e eK he P hB hJ t ht htK
  exact quotient_coordinates e J i hi

end Theory.SpecificGroups.Alternating.FiveBorelOvergroups
