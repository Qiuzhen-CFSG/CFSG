module
public import Theory.GroupTheory.SwappedSylowNormalizer
public import Theory.SpecificGroups.PSL2.NonabelianSylowNormalizer

/-!
# The exchanged index-two normalizer in odd prime PSL₂ squares

The literal intersection has index at most two in a full Sylow and is
preserved by an actual factor-exchanging automorphism. Both projections
are consequently full Sylows. Their self-normalization bounds the
intersection normalizer by the product Sylow. The prime-field outer
automorphism group then gives a two-group image for every action preserving
this intersection. The full- and half-Sylow cases use the same argument.

Source: Aschbacher--Smith 10.2.5, printed p.748, the p ≡ ±1 mod 8 branch.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SylowNormalizerAction
open scoped MatrixGroups
namespace Theory.PSL2
variable {Q A : Type*} [Group Q] [Group A]
variable {F : Type} [Field F] [Finite F]

/-- The actual exchanged subgroup of index at most two determines a two-group action. -/
theorem prime_pair_intersection_action [Finite Q] [IsQuasisimple Q]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hl : 3 < p) (hF : Nat.card F = p)
    (h8 : 8 ∣ Nat.card PSL(2,F)) (e : Q ≃* PSL(2,F))
    {B : Type*} [Group B] [Finite B] (eB : B ≃* Q × Q)
    (S : Sylow 2 B) (U : Subgroup B) (hUS : U ≤ (S : Subgroup B))
    (hi : U.relIndex (S : Subgroup B) ≤ 2) (a b : MulAut Q)
    (hswap : (U.map eB.toMonoidHom).map
      (a.prodCongr b * (MulEquiv.prodComm : MulAut (Q × Q))).toMonoidHom = U.map eB.toMonoidHom)
    (f : A →* MulAut B) (hf : ∀ g, U.map (f g).toMonoidHom = U) :
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
  have hn (V : Sylow 2 Q) : normalizer (V : Set Q) = (V : Subgroup Q) := by
    apply map_injective (f := e.toMonoidHom) e.injective
    change (normalizer ((V : Subgroup Q) : Set Q)).map e.toMonoidHom = _
    rw [map_equiv_normalizer_eq]
    exact large_sylow_normalizer ⟨p,1,Fact.out,hp,by decide,by simpa using hF⟩ h8
      (V.mapSurjective (f := e.toMonoidHom) e.surjective)
  let S' := S.mapSurjective (f := eB.toMonoidHom) eB.surjective
  have hi' : (U.map eB.toMonoidHom).relIndex (S' : Subgroup (Q × Q)) ≤ 2 := by
    change (U.map eB.toMonoidHom).relIndex ((S : Subgroup B).map eB.toMonoidHom) ≤ 2
    rw [relIndex_map_map_of_injective _ _ eB.injective]
    exact hi
  have hnU : normalizer (U : Set B) ≤ (S : Subgroup B) := by
    apply (map_le_map_iff_of_injective (f := eB.toMonoidHom) eB.injective).mp
    rw [map_equiv_normalizer_eq]
    exact normalizer_le_of_projections_full hn S' (U.map eB.toMonoidHom)
      (map_mono hUS) hi' (projection_card_eq_of_swapped _ a b hswap)
  exact action_two_of_normalizer_two U (S.isPGroup'.to_le hnU)
    ((AutomorphismSquare.outer_isPGroup_two hz ho).of_equiv (MulAut.outerCongr eB).symm) f hf
end Theory.PSL2
