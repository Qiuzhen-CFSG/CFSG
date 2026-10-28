module
public import Theory.SpecificGroups.PSL2.SmallSylowRadical

/-!
# Self-centralization in small-congruence PSL₂ squares

The full Sylow of a direct product is the product of its two projections.
Each projection is Klein four and self-centralizing in odd PSL₂ when
eight does not divide the group order. The same property therefore holds
in the square and transports through an actual group isomorphism.

Source application: Aschbacher--Smith 10.2.5, printed p.748, through the
original containing-component quotient in OddSmallCoreInterval.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Theory.PSL2
variable {F : Type} [Field F] [Finite F]

/-- The full Sylow in the actual PSL₂ square is self-centralizing. -/
theorem small_pair_self_centralizing
    (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h8 : ¬ 8 ∣ Nat.card PSL(2,F))
    (S : Sylow 2 (PSL(2,F) × PSL(2,F))) :
    centralizer (S : Set (PSL(2,F) × PSL(2,F))) = (S : Subgroup _) := by
  let A := S.mapSurjective (f := MonoidHom.fst _ _) (fun x => ⟨(x,1),rfl⟩)
  let B := S.mapSurjective (f := MonoidHom.snd _ _) (fun x => ⟨(1,x),rfl⟩)
  have hab : (S : Subgroup (PSL(2,F) × PSL(2,F))) = (A : Subgroup PSL(2,F)).prod (B : Subgroup PSL(2,F)) := by
    symm
    apply S.is_maximal'
    · obtain ⟨a,ha⟩ := A.isPGroup'.exists_card_eq
      obtain ⟨b,hb⟩ := B.isPGroup'.exists_card_eq
      apply IsPGroup.of_card (n := a+b)
      rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,ha,hb,pow_add]
    · intro x hx
      exact ⟨mem_map_of_mem _ hx,mem_map_of_mem _ hx⟩
  have ha := GorensteinWalter.psl2_kleinFour_centralizer_eq_self F hF
    (A : Subgroup _) (Theory.PSL2.small_sylow_kleinFour hF h8 A)
  have hb := GorensteinWalter.psl2_kleinFour_centralizer_eq_self F hF
    (B : Subgroup _) (Theory.PSL2.small_sylow_kleinFour hF h8 B)
  change centralizer ((S : Subgroup (PSL(2,F) × PSL(2,F))) : Set (PSL(2,F) × PSL(2,F))) = (S : Subgroup (PSL(2,F) × PSL(2,F)))
  rw [hab]
  ext x
  constructor
  · intro hx
    constructor
    · rw [←ha]
      intro a ha'
      exact congrArg Prod.fst (hx (a,1) ⟨ha',B.one_mem⟩)
    · rw [←hb]
      intro b hb'
      exact congrArg Prod.snd (hx (1,b) ⟨A.one_mem,hb'⟩)
  · intro hx y hy
    exact Prod.ext ((ha.symm ▸ hx.1) y.1 hy.1) ((hb.symm ▸ hx.2) y.2 hy.2)

/-- Transport self-centralization through the supplied square isomorphism. -/
theorem small_pair_self_centralizing_of_equiv
    {B : Type*} [_root_.Group B] [Finite B] (e : B ≃* PSL(2,F) × PSL(2,F))
    (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h8 : ¬ 8 ∣ Nat.card PSL(2,F)) (S : Sylow 2 B) :
    centralizer (S : Set B) = (S : Subgroup B) := by
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hc := small_pair_self_centralizing hF h8 S'
  apply le_antisymm
  · intro x hx
    have hm : e x ∈ centralizer (S' : Set (PSL(2,F) × PSL(2,F))) := by
      rintro y ⟨z,hz,rfl⟩
      exact (e.map_mul z x).symm.trans ((congrArg e (hx z hz)).trans (e.map_mul x z))
    rw [hc] at hm
    exact (mem_map_iff_mem e.injective).mp hm
  · intro x hx y hy
    apply e.injective
    rw [map_mul,map_mul]
    have hex : e x ∈ centralizer (S' : Set (PSL(2,F) × PSL(2,F))) := by
      rw [hc]
      exact mem_map_of_mem e.toMonoidHom hx
    exact hex _ (mem_map_of_mem e.toMonoidHom hy)
end Theory.PSL2
