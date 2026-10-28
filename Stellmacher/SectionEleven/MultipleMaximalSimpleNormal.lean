module

public import Stellmacher.MainDefs
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.GroupAction.MinimalNormal
public import FeitThompson.BGsection1.PLengthLemmas
public import FeitThompson.BGsection6.Defs

/-!
# A simple normal subgroup in the reduced N2 group

The N2 condition and trivial odd and two cores force a finite nonsolvable
group to have a nonsolvable simple normal subgroup with trivial centralizer.
This is an independent structural reduction for the Section 11 setup of
Stellmacher's N-group paper, not an invocation of its final classification
or of the proposed Sylow Baumann equality.

The cores inherit to normal subgroups. Solvable Fitting-centralizer control
therefore excludes nontrivial solvable normal subgroups. Cauchy's theorem
and the solvability of involution centralizers show that a nonsolvable
normal subgroup has trivial centralizer. A minimal nontrivial normal
subgroup consequently meets every other nontrivial normal subgroup, so it
is unique and characteristic. Apply this inside a minimal ambient normal
subgroup: characteristic-in-normal normality makes it the whole subgroup,
proving simplicity without any odd-order classification.
-/

namespace Stellmacher.SectionEleven

private theorem nTwo_subgroup
    {H : Type*} [Group H] [Finite H] (hN2 : IsNTwoGroup H)
    (N : Subgroup H) : IsNTwoGroup N := by
  rintro U ⟨Q, hQ, hQtwo, rfl⟩
  have hmap : Q.map N.subtype ≠ ⊥ := by
    exact fun heq => hQ ((Subgroup.map_eq_bot_iff_of_injective Q N.subtype_injective).mp heq)
  have hlocal : IsTwoLocal (Subgroup.normalizer (Q.map N.subtype : Set H)) :=
    ⟨Q.map N.subtype, hmap, hQtwo.map N.subtype, rfl⟩
  let := hN2 _ hlocal
  let embed := N.subtype.comp (Subgroup.normalizer (Q : Set N)).subtype
  have hle : (Subgroup.normalizer (Q : Set N)).map N.subtype ≤
      Subgroup.normalizer (Q.map N.subtype : Set H) := Q.le_normalizer_map N.subtype
  exact Group.isSolvable_of_isSolvable_injective
    (f := embed.codRestrict _ (fun element => hle ⟨element, element.property, rfl⟩))
    (fun left right heq => by
      have hval : ((left : N) : H) = ((right : N) : H) :=
        congrArg (fun value : Subgroup.normalizer (Q.map N.subtype : Set H) =>
          (value : H)) heq
      exact Subtype.ext (Subtype.ext hval))

private theorem trivial_cores_normal
    {H : Type*} [Group H] [Finite H]
    (hodd : pPrimeCore 2 H = ⊥) (htwo : pCore 2 H = ⊥)
    (N : Subgroup H) [N.Normal] : pPrimeCore 2 N = ⊥ ∧ pCore 2 N = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · apply (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp
    exact le_bot_iff.mp ((pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 N).trans_eq hodd)
  · have hle : (pCore 2 N).map N.subtype ≤ pCore 2 H :=
      le_sSup ⟨inferInstance, (pCore_isPGroup (p := 2) (G := N)).map N.subtype⟩
    exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp
      (le_bot_iff.mp (hle.trans_eq htwo))

private theorem nonsolvable_of_trivial_cores
    {H : Type*} [Group H] [Finite H] [Nontrivial H]
    (hodd : pPrimeCore 2 H = ⊥) (htwo : pCore 2 H = ⊥) : ¬ Group.IsSolvable H := by
  intro hsolv
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot hsolv hodd
  rw [htwo] at hle
  have hbad : (⊤ : Subgroup H) ≤ ⊥ := by
    apply le_trans (show (⊤ : Subgroup H) ≤ Subgroup.centralizer (⊥ : Subgroup H) from ?_) hle
    intro element _
    rw [Subgroup.mem_centralizer_iff]
    intro other hother
    have : other = 1 := hother
    simp [this]
  exact top_ne_bot (le_antisymm hbad bot_le)

private theorem solvable_of_centralized_by_even_subgroup
    {H : Type*} [Group H] [Finite H] (hN2 : IsNTwoGroup H)
    (A B : Subgroup H) (heven : Even (Nat.card A))
    (hcomm : A ≤ Subgroup.centralizer (B : Set H)) : Group.IsSolvable B := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨element, horder⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 heven.two_dvd
  have horderH : orderOf (element : H) = 2 := by
    simpa only [Subgroup.orderOf_coe] using horder
  have hcentral : Group.IsSolvable (Subgroup.centralizer ({(element : H)} : Set H)) := by
    by_contra hnsolv
    obtain ⟨U, hU, hbad⟩ :=
      Theory.GroupTheory.exists_nonsolvable_twoLocal_of_involution_centralizer horderH hnsolv
    exact hbad (hN2 U hU)
  have hle : B ≤ Subgroup.centralizer ({(element : H)} : Set H) := by
    intro other hother
    rw [Subgroup.mem_centralizer_iff]
    intro singleton hsingleton
    have heq : singleton = (element : H) := hsingleton
    subst singleton
    exact (Subgroup.mem_centralizer_iff.mp (hcomm element.property) other hother).symm
  let := hcentral
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

private theorem odd_centralizer_of_nonsolvable
    {H : Type*} [Group H] [Finite H] (hN2 : IsNTwoGroup H)
    (B : Subgroup H) (hB : ¬ Group.IsSolvable B) :
    Odd (Nat.card (Subgroup.centralizer (B : Set H))) := by
  by_contra hodd
  have heven : Even (Nat.card (Subgroup.centralizer (B : Set H))) :=
    Nat.not_odd_iff_even.mp hodd
  exact hB (solvable_of_centralized_by_even_subgroup hN2 _ B heven le_rfl)

private theorem centralizer_eq_bot_of_normal_nonsolvable
    {H : Type*} [Group H] [Finite H] (hN2 : IsNTwoGroup H)
    (hodd : pPrimeCore 2 H = ⊥)
    (B : Subgroup H) [B.Normal] (hB : ¬ Group.IsSolvable B) :
    Subgroup.centralizer (B : Set H) = ⊥ := by
  have hle : Subgroup.centralizer (B : Set H) ≤ pPrimeCore 2 H := by
    apply le_sSup
    exact ⟨inferInstance, Nat.coprime_two_left.mpr (odd_centralizer_of_nonsolvable hN2 B hB)⟩
  exact le_bot_iff.mp (hle.trans_eq hodd)

private theorem minimal_normal_characteristic
    {H : Type*} [Group H] [Finite H] (hN2 : IsNTwoGroup H)
    (hodd : pPrimeCore 2 H = ⊥) (htwo : pCore 2 H = ⊥)
    (K : Subgroup H) [K.Normal] (hK : K ≠ ⊥)
    (hmin : ∀ L : Subgroup H, L.Normal ∧ L ≠ ⊥ → L ≤ K → L = K) :
    K.Characteristic := by
  let : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK
  obtain ⟨hoddK, htwoK⟩ := trivial_cores_normal hodd htwo K
  have hcent := centralizer_eq_bot_of_normal_nonsolvable hN2 hodd K
    (nonsolvable_of_trivial_cores hoddK htwoK)
  have hleast : ∀ L : Subgroup H, L.Normal → L ≠ ⊥ → K ≤ L := by
    intro L hnormal hnontriv
    let := hnormal
    have hinter : K ⊓ L ≠ ⊥ := by
      intro heq
      have hcomm := Subgroup.commutator_eq_bot_of_disjoint (H₁ := L) (H₂ := K)
        ((disjoint_iff.mpr heq).symm)
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      exact hnontriv (le_bot_iff.mp (hle.trans_eq hcent))
    exact (hmin (K ⊓ L) ⟨inferInstance, hinter⟩ inf_le_left).symm.le.trans inf_le_right
  apply Subgroup.characteristic_iff_le_map.mpr
  intro automorphism
  apply hleast
  · exact Subgroup.Normal.map inferInstance automorphism.toMonoidHom automorphism.surjective
  · exact fun heq => hK
      ((Subgroup.map_eq_bot_iff_of_injective K automorphism.injective).mp heq)

/-- The reduced nonsolvable N2 group has a self-centralizing nonsolvable
simple normal subgroup. -/
public theorem exists_simple_normal_of_nTwo_of_trivial_cores
    {H : Type*} [Group H] [Finite H] (hN2 : IsNTwoGroup H)
    (hodd : pPrimeCore 2 H = ⊥) (htwo : pCore 2 H = ⊥)
    (hnsolv : ¬ Group.IsSolvable H) :
    ∃ N : Subgroup H, N.Normal ∧ IsSimpleGroup N ∧ ¬ Group.IsSolvable N ∧
      Subgroup.centralizer (N : Set H) = ⊥ := by
  classical
  have : Nontrivial H := not_subsingleton_iff_nontrivial.mp
    (fun htriv => hnsolv (by let := htriv; infer_instance))
  obtain ⟨N, ⟨hNnorm, hNne⟩, hNmin⟩ := exists_minimal_subgroup_of_mem_top
    (fun L : Subgroup H => L.Normal ∧ L ≠ ⊥) ⟨inferInstance, top_ne_bot⟩
  let := hNnorm
  let : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNne
  obtain ⟨hoddN, htwoN⟩ := trivial_cores_normal hodd htwo N
  have hnsolvN := nonsolvable_of_trivial_cores hoddN htwoN
  obtain ⟨K, ⟨hKnorm, hKne⟩, hKmin⟩ := exists_minimal_subgroup_of_mem_top
    (fun L : Subgroup N => L.Normal ∧ L ≠ ⊥) ⟨inferInstance, top_ne_bot⟩
  let := hKnorm
  let : K.Characteristic :=
    minimal_normal_characteristic (nTwo_subgroup hN2 N) hoddN htwoN K hKne hKmin
  have hmapne : K.map N.subtype ≠ ⊥ := fun heq => hKne
    ((Subgroup.map_eq_bot_iff_of_injective K N.subtype_injective).mp heq)
  have hmap : K.map N.subtype = N :=
    hNmin _ ⟨inferInstance, hmapne⟩ (Subgroup.map_subtype_le K)
  have hKtop : K = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    simpa only [← MonoidHom.range_eq_map, N.range_subtype] using hmap
  have hsimple : IsSimpleGroup N := by
    constructor
    intro L hnormal
    by_cases hL : L = ⊥
    · exact Or.inl hL
    · exact Or.inr ((hKmin L ⟨hnormal, hL⟩ (by rw [hKtop]; exact le_top)).trans hKtop)
  exact ⟨N, hNnorm, hsimple, hnsolvN,
    centralizer_eq_bot_of_normal_nonsolvable hN2 hodd N hnsolvN⟩

end Stellmacher.SectionEleven
