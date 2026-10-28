module

public import Theory.Quasithin.EmbeddedNormalTwoLocalRank
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-!
# The E₉ × A₄ two-local obstruction

The product has an elementary abelian subgroup E₉ × C₃ of order 27 and a
nontrivial normal two-subgroup 1 × V₄. Any embedding therefore gives
m₂,₃(G) ≥ 3 and rules out quasithinness. Both witnesses are constructed here;
no ordinary or local rank inequality is assumed.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma A.2.19, printed p. 41, in its O'Nan case.
-/

public section
namespace Theory.Quasithin

local notation "E₉" => Multiplicative (ZMod 3 × ZMod 3)
local notation "A₄" => alternatingGroup (Fin 4)

/-- The elementary subgroup E₉ × C₃ witnesses ordinary rank at least three. -/
theorem three_le_primeRank_e9_prod_a4 : 3 ≤ primeRank 3 (E₉ × A₄) := by
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := A₄) 3
    (by rw [alternatingGroup.card_of_card_eq_four (by simp)]; decide)
  let C := Subgroup.zpowers z
  let : CommGroup C := IsCyclic.commGroup
  have hc : Nat.card C = 3 := (Nat.card_zpowers z).trans hz
  let f : E₉ × C →* E₉ × A₄ := (MonoidHom.id E₉).prodMap C.subtype
  apply primeRank_ge_of_elementary_embedding (p := 3) (e := 3) (A := E₉ × C) ?_ ?_ f
  · intro a b h
    change (a.1, (a.2 : A₄)) = (b.1, (b.2 : A₄)) at h
    apply Prod.ext
    · exact congrArg (fun x : E₉ × A₄ => x.1) h
    · exact Subtype.ext (congrArg (fun x : E₉ × A₄ => x.2) h)
  · intro a
    apply Prod.ext
    · change (3 • a.1.toAdd) = 0
      apply Prod.ext
      · change 3 • a.1.toAdd.1 = (0 : ZMod 3)
        simp only [nsmul_eq_mul]
        exact zero_mul _
      · change 3 • a.1.toAdd.2 = (0 : ZMod 3)
        simp only [nsmul_eq_mul]
        exact zero_mul _
    · change a.2 ^ 3 = 1
      simpa only [hc] using (pow_card_eq_one' (x := a.2))
  · rw [Nat.card_prod, hc, Nat.card_congr Multiplicative.toAdd, Nat.card_prod]
    norm_num [Nat.card_zmod]

/-- The subgroup 1 × V₄ is normal, nontrivial and a two-group. -/
theorem e9_prod_a4_normal_two : ∃ Q : Subgroup (E₉ × A₄),
    Q.Normal ∧ Q ≠ ⊥ ∧ IsPGroup 2 Q := by
  let K := alternatingGroup.kleinFour (Fin 4)
  let : K.Normal := alternatingGroup.normal_kleinFour (by simp)
  let Q : Subgroup (E₉ × A₄) := (⊥ : Subgroup E₉).prod K
  have hc : Nat.card Q = 4 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      Subgroup.card_bot, one_mul]
    exact alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
  refine ⟨Q, inferInstance, ?_, IsPGroup.of_card (n := 2) hc⟩
  intro h
  rw [h, Subgroup.card_bot] at hc
  contradiction

/-- An actual E₉ × A₄ embedding supplies local, rather than just ordinary, rank. -/
theorem three_le_twoLocalPrimeRank_of_e9_prod_a4_embedding
    {G : Type*} [Group G] [Finite G]
    (f : E₉ × A₄ →* G) (hf : Function.Injective f) :
    3 ≤ twoLocalPrimeRank 3 G := by
  obtain ⟨Q, hnormal, hne, hp⟩ := e9_prod_a4_normal_two
  exact three_le_primeRank_e9_prod_a4.trans
    (primeRank_le_twoLocalPrimeRank_of_embedding f hf Q hne hp 3)

/-- The two-local witness prevents the ambient group from being quasithin. -/
theorem not_quasithin_of_e9_prod_a4_embedding
    {G : Type*} [Group G] [Finite G]
    (f : E₉ × A₄ →* G) (hf : Function.Injective f) :
    ¬ IsQuasithin G := by
  intro h
  have hle := isQuasithin_iff_twoLocalPrimeRank.mp h 3 (by decide) (by decide)
  have hge := three_le_twoLocalPrimeRank_of_e9_prod_a4_embedding f hf
  omega

end Theory.Quasithin
