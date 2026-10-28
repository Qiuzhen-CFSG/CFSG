module
public import Theory.GroupTheory.AutomorphismSylowNormalizer
public import Theory.GroupTheory.AutomorphismSquareOuterTwo
public import Theory.SpecificGroups.PSL2.PrimeCardInnerIndex
public import GorensteinWalter.GWLemma21
public import GorensteinWalter.PSL2KleinFourCentralizerEqSelf

/-!
# Sylow-preserving actions on a square of odd prime PSL₂ groups

A nonabelian dihedral two-group has two-group automorphism group. The
self-centralizing four-group inside an odd PSL₂ Sylow therefore makes
that Sylow self-normalizing. Prime-field outer automorphisms have order
two, and the direct-square outer group is also a two-group. Consequently
any action preserving a full Sylow of the square has two-group image.

The actual source application detects this image on the original ambient
Sylow, which already normalizes the parabolic residual. This gives the
full-intersection case of Aschbacher--Smith 10.2.5, printed p.748, without
requiring a choice of either S₄ overgroup. The index-two intersection and
abelian-Sylow congruence cases are separate.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SylowNormalizerAction
open scoped MatrixGroups
namespace Theory.PSL2
variable {Q A : Type*} [Group Q] [Group A]
variable {F : Type} [Field F] [Finite F]

/-- Every nonabelian Sylow two-subgroup of odd PSL₂ is self-normalizing. -/
theorem large_sylow_normalizer (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h8 : 8 ∣ Nat.card PSL(2,F)) (S : Sylow 2 PSL(2,F)) :
    normalizer (S : Set PSL(2,F)) = (S : Subgroup PSL(2,F)) := by
  obtain ⟨m,hm,⟨e⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hF S
  have hm2 : 2 ≤ m := by
    have hd := S.pow_dvd_card_of_pow_dvd_card (n := 3) h8
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card] at hd
    by_contra hn
    have he : m = 1 := by omega
    norm_num [he] at hd
  have hAut : IsPGroup 2 (MulAut S) :=
    (GorensteinWalter.dihedral_mulAut_is_twoGroup hm2).of_equiv (MulAut.congr e).symm
  obtain ⟨V,hVS,hV⟩ := GorensteinWalter.exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (S : Subgroup PSL(2,F)) hm e
  have hc : centralizer (S : Set PSL(2,F)) ≤ (S : Subgroup PSL(2,F)) := by
    exact (centralizer_le hVS).trans ((GorensteinWalter.psl2_kleinFour_centralizer_eq_self F hF V hV).le.trans hVS)
  change normalizer ((S : Subgroup PSL(2,F)) : Set PSL(2,F)) = (S : Subgroup PSL(2,F))
  apply le_antisymm _ (S : Subgroup PSL(2,F)).le_normalizer
  intro x hx
  obtain ⟨s,hs,c,hc',rfl⟩ := GorensteinWalter.normalizer_decomp_of_aut_isPGroup S hAut hx
  exact mul_mem hs (hc hc')

/-- A Sylow-preserving action on an actual prime-PSL₂ square has two-group image
when the factor Sylows are nonabelian. The product equivalence is arbitrary. -/
theorem prime_pair_action [Finite Q] [IsQuasisimple Q]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hl : 3 < p) (hF : Nat.card F = p)
    (h8 : 8 ∣ Nat.card PSL(2,F)) (e : Q ≃* PSL(2,F))
    {B : Type*} [Group B] [Finite B] (eB : B ≃* Q × Q)
    (S : Sylow 2 B) (f : A →* MulAut B)
    (hf : ∀ a, (S : Subgroup B).map (f a).toMonoidHom = S) :
    IsPGroup 2 f.range := by
  have hoF : IsPGroup 2 (MulAut.Outer PSL(2,F)) := by
    apply IsPGroup.of_card (n := 1)
    change Nat.card (MulAut PSL(2,F) ⧸ MulAut.innerSubgroup PSL(2,F)) = 2^1
    rw [← index_eq_card,Theory.PSL2.prime_card_inner_index F hp hl hF]
    rfl
  have ho : IsPGroup 2 (MulAut.Outer Q) := hoF.of_equiv (MulAut.outerCongr e).symm
  have hz : center Q = ⊥ := by
    apply bot_unique
    intro x hx
    have he : e x ∈ center PSL(2,F) := (centerCongr e ⟨x,hx⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot F,mem_bot] at he
    exact e.injective (he.trans e.map_one.symm)
  have hn (U : Sylow 2 Q) : normalizer (U : Set Q) = (U : Subgroup Q) := by
    apply map_injective (f := e.toMonoidHom) e.injective
    change (normalizer ((U : Subgroup Q) : Set Q)).map e.toMonoidHom = _
    rw [map_equiv_normalizer_eq]
    exact large_sylow_normalizer ⟨p,1,Fact.out,hp,by decide,by simpa using hF⟩ h8
      (U.mapSurjective (f := e.toMonoidHom) e.surjective)
  have hnB : normalizer (S : Set B) = (S : Subgroup B) := by
    apply map_injective (f := eB.toMonoidHom) eB.injective
    change (normalizer ((S : Subgroup B) : Set B)).map eB.toMonoidHom = _
    rw [map_equiv_normalizer_eq]
    exact product_sylow_self_normalizing hn (S.mapSurjective (f := eB.toMonoidHom) eB.surjective)
  exact action_two_of_self_normalizing_sylow S hnB
    ((AutomorphismSquare.outer_isPGroup_two hz ho).of_equiv (MulAut.outerCongr eB).symm) f hf

end Theory.PSL2
