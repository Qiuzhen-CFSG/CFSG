module

public import Theory.SpecificGroups.ReeG2.DefiningLocalRank
public import Theory.SpecificGroups.G2.DefiningRank
public import Theory.SpecificGroups.SymplecticSix.ThreeRank
public import CFSG.Quasithin.Defs

/-!
# Concrete exceptional-family rank obstructions for A.2.17

The Ree torus involution centralizes its faithful beta root group, which
excludes the entire large Ree family from quasithin groups. In odd G₂,
the orthogonal root pair forces the defining field to have degree one;
the independent root triple excludes strong quasithinness. All statements
transport through explicit injective maps from the actual matrix models.

The cubic rotations in Sp₆ contradict the source complementary-centralizer
bound once that subgroup is constructed in the literal residual centralizer.
The full C₂ × PSL₂ Ree subgroup, the fundamental residual centralizers in
F₄, G₂ and triality, and the proper exceptional subsystem inclusions remain
separate structural obligations. No family elimination or centralizer
identification is assumed by the concrete Ree and G₂ conclusions here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), Lemma A.2.17, printed pp.38–39
of `refs/quasithin.pdf`. The small derived group ²G₂(3)′ is kept separate.
-/

public section

namespace CFSG.Quasithin.ChapterA.Section02
variable {F G : Type*} [Field F] [Finite F] [Group G] [Finite G]

/-- The beta root group excludes every embedded large Ree model from a quasithin group. -/
theorem not_quasithin_of_ree_embedding [CharP F 3] (m : ℕ) (hm : 1 ≤ m)
    (hcard : Nat.card F = 3^(2*m+1))
    (f : Atlas.ReeG2.Model F m →* G) (hf : Function.Injective f) : ¬ IsQuasithin G := by
  intro hqt
  obtain ⟨z, hz, hz2, hr⟩ := Atlas.ReeG2.exists_involution_primeRank_ge m hcard f hf
  have ho : orderOf z = 2 := orderOf_eq_prime hz2 hz
  have hloc := Theory.GroupTheory.isTwoLocal_involution_centralizer ho
  have hu := (Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hqt) _ hloc 3
    (by decide) (by decide)
  omega

/-- The concrete Ree groups of field order at least 27 are not quasithin. -/
theorem ree_not_quasithin [CharP F 3] (m : ℕ) (hm : 1 ≤ m)
    (hcard : Nat.card F = 3^(2*m+1)) : ¬ IsQuasithin (Atlas.ReeG2.Model F m) :=
  not_quasithin_of_ree_embedding m hm hcard (MonoidHom.id _) Function.injective_id

/-- Ordinary defining-characteristic rank excludes every odd G₂ model from strong quasithinness. -/
theorem g2_not_stronglyQuasithin {p e : ℕ} [Fact p.Prime] [CharP F p]
    (hp : Odd p) (he : 1 ≤ e) (hcard : Nat.card F = p^e)
    (f : Atlas.G2.Model F →* G) (hf : Function.Injective f) :
    ¬ IsStronglyQuasithin G := by
  intro hsq
  have hr := (Atlas.G2.three_mul_fieldExponent_le_primeRank hcard).trans
    (Theory.GroupTheory.primeRank_le_of_injective p f hf)
  have hu := hsq p Fact.out hp
  omega

/-- The actual block SL₂ supplies the initial degree bound from involution centralizers. -/
theorem g2_fieldExponent_le_two {p e : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (hcard : Nat.card F = p^e)
    (f : Atlas.G2.Model F →* G) (hf : Function.Injective f)
    (hlocal : ∀ z : G, z ≠ 1 → z^2 = 1 →
      primeRank p (Subgroup.centralizer ({z} : Set G)) ≤ 2) : e ≤ 2 := by
  let : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩
  let j := f.comp (Atlas.G2.PairStabilizer.blockHom (F := F))
  have hj : Function.Injective j := hf.comp Atlas.G2.blockSL2_injective
  obtain ⟨hz, hz2⟩ := Matrix.SpecialLinearGroup.map_neg_one_isInvolution hp j hj
  exact (Matrix.SpecialLinearGroup.fieldExponent_le_primeRank_centralizer hcard j hj).trans
    (hlocal (j (-1)) hz hz2)

/-- The source bound m₃(J*) ≤ 1 excludes an actual embedded Sp₆ in J*. -/
theorem not_injective_sp6_of_three_rank_le_one
    (hrank : primeRank 3 G ≤ 1)
    (f : Matrix.symplecticGroup (Fin 3) F →* G) : ¬ Function.Injective f := by
  intro hf
  have hr := (Theory.SpecificGroups.SymplecticSix.ThreeRank.three_le_primeRank (F := F)).trans
    (Theory.GroupTheory.primeRank_le_of_injective 3 f hf)
  omega
end CFSG.Quasithin.ChapterA.Section02

namespace CFSG.Quasithin.ChapterA.Section02
variable {F G : Type*} [Field F] [Finite F] [Group G] [Finite G]

/-- The two orthogonal root groups force q to be prime in the quasithin G₂ branch. -/
theorem g2_fieldExponent_eq_one_of_quasithin {p e : ℕ} [Fact p.Prime] [CharP F p]
    (hp : Odd p) (he : 1 ≤ e) (hcard : Nat.card F = p^e)
    (f : Atlas.G2.Model F →* G) (hf : Function.Injective f) (hqt : IsQuasithin G) : e = 1 := by
  have hp2 : p ≠ 2 := by intro h; exact (by decide : ¬ Odd 2) (h ▸ hp)
  obtain ⟨z, hz, hz2, hr⟩ :=
    Atlas.G2.exists_involution_two_mul_fieldExponent_le_primeRank hp2 hcard f hf
  have ho : orderOf z = 2 := orderOf_eq_prime hz2 hz
  have hloc := Theory.GroupTheory.isTwoLocal_involution_centralizer ho
  have hu := (Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hqt) _ hloc p Fact.out hp
  omega
end CFSG.Quasithin.ChapterA.Section02
