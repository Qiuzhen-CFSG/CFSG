module
public import Theory.SpecificGroups.PSL2.SmallSylowNormalizer
public import Theory.GroupTheory.FourProductRadical
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Full Sylow intersections in small-congruence PSL₂ squares

A self-centralizing Klein-four Sylow has normalizer order at most twelve:
its automizer embeds in S₃, and the ambient two-part excludes the factor
of eight. In the direct square the bound is 144. A cubic plane normalizing
the full Sylow fills this normalizer by the product-order formula.

The exchanged cubic-generated radical is either trivial or full, by the
faithful automizer argument for two four-groups. Actual quotient maps and
product isomorphisms are retained. This supplies the model identities for
Aschbacher--Smith 10.2.5, printed p.748; the source must exclude collapse of
the original radical before using the nontrivial branch.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2
variable {F : Type} [Field F] [Finite F]

/-- The Sylow normalizer has order at most twelve in the small congruences. -/
theorem small_sylow_normalizer_card_le (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h8 : ¬ 8 ∣ Nat.card PSL(2,F)) (S : Sylow 2 PSL(2,F)) :
    Nat.card (normalizer (S : Set PSL(2,F))) ≤ 12 := by
  let := small_sylow_kleinFour hF h8 S
  let V : Subgroup PSL(2,F) := S
  have hc : centralizer (V : Set PSL(2,F)) = V :=
    GorensteinWalter.psl2_kleinFour_centralizer_eq_self F hF V inferInstance
  have hk : Nat.card V.normalizerMonoidHom.ker = 4 := by
    rw [normalizerMonoidHom_ker,hc,
      Nat.card_congr (subgroupOfEquivOfLe V.le_normalizer).toEquiv]
    exact IsKleinFour.card_four
  have hd : Nat.card V.normalizerMonoidHom.range ∣ 6 := by
    simpa only [IsKleinFour.card_mulAut] using
      V.normalizerMonoidHom.range.card_subgroup_dvd_card
  have hh := V.normalizerMonoidHom.ker.card_mul_index
  rw [index_ker,hk] at hh
  have hr := Nat.le_of_dvd (by decide : 0 < 6) hd
  have hn : ¬ 8 ∣ Nat.card (normalizer (V : Set PSL(2,F))) :=
    fun hn => h8 (hn.trans (normalizer (V : Set PSL(2,F))).card_subgroup_dvd_card)
  have hl : Nat.card V.normalizerMonoidHom.range ≤ 3 := by
    by_contra he
    have hr' : Nat.card V.normalizerMonoidHom.range = 4 ∨
      Nat.card V.normalizerMonoidHom.range = 5 ∨ Nat.card V.normalizerMonoidHom.range = 6 := by omega
    rcases hr' with he | he | he
    · rw [he] at hd; norm_num at hd
    · rw [he] at hd; norm_num at hd
    · rw [he] at hh
      exact hn (by rw [←hh]; decide)
  change Nat.card (normalizer (V : Set PSL(2,F))) ≤ 12
  omega

private theorem sylow_product (S : Sylow 2 (PSL(2,F) × PSL(2,F))) :
    (S : Subgroup (PSL(2,F) × PSL(2,F))) =
      ((S : Subgroup (PSL(2,F) × PSL(2,F))).map (MonoidHom.fst PSL(2,F) PSL(2,F))).prod
      ((S : Subgroup (PSL(2,F) × PSL(2,F))).map (MonoidHom.snd PSL(2,F) PSL(2,F))) := by
  let A := S.mapSurjective (f := MonoidHom.fst _ _) (fun q => ⟨(q,1),rfl⟩)
  let B := S.mapSurjective (f := MonoidHom.snd _ _) (fun q => ⟨(1,q),rfl⟩)
  symm
  apply S.is_maximal'
  · obtain ⟨a,ha⟩ := A.isPGroup'.exists_card_eq
    obtain ⟨b,hb⟩ := B.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := a+b)
    rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod]
    change Nat.card A * Nat.card B = 2^(a+b)
    rw [ha,hb,pow_add]
  · intro x hx
    exact ⟨mem_map_of_mem _ hx,mem_map_of_mem _ hx⟩

/-- The full Sylow of the actual direct square has order sixteen. -/
theorem small_pair_sylow_card (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h8 : ¬ 8 ∣ Nat.card PSL(2,F)) (S : Sylow 2 (PSL(2,F) × PSL(2,F))) :
    Nat.card S = 16 := by
  let A := S.mapSurjective (f := MonoidHom.fst _ _) (fun q => ⟨(q,1),rfl⟩)
  let B := S.mapSurjective (f := MonoidHom.snd _ _) (fun q => ⟨(1,q),rfl⟩)
  let := small_sylow_kleinFour hF h8 A
  let := small_sylow_kleinFour hF h8 B
  rw [sylow_product S,Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod]
  change Nat.card A * Nat.card B = 16
  rw [IsKleinFour.card_four,IsKleinFour.card_four]

/-- Both projection bounds give order at most 144 for the full normalizer. -/
theorem small_pair_normalizer_card_le (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h8 : ¬ 8 ∣ Nat.card PSL(2,F)) (S : Sylow 2 (PSL(2,F) × PSL(2,F))) :
    Nat.card (normalizer (S : Set (PSL(2,F) × PSL(2,F)))) ≤ 144 := by
  let A := S.mapSurjective (f := MonoidHom.fst _ _) (fun q => ⟨(q,1),rfl⟩)
  let B := S.mapSurjective (f := MonoidHom.snd _ _) (fun q => ⟨(1,q),rfl⟩)
  have hn : normalizer (S : Set (PSL(2,F) × PSL(2,F))) ≤
      (normalizer (A : Set PSL(2,F))).prod (normalizer (B : Set PSL(2,F))) := by
    intro x hx
    exact ⟨le_normalizer_map (MonoidHom.fst _ _) (mem_map_of_mem _ hx),
      le_normalizer_map (MonoidHom.snd _ _) (mem_map_of_mem _ hx)⟩
  have hh := card_le_of_le hn
  rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod] at hh
  exact hh.trans (Nat.mul_le_mul (small_sylow_normalizer_card_le hF h8 A)
    (small_sylow_normalizer_card_le hF h8 B))

/-- A normalizing cubic plane fills the actual Sylow normalizer. -/
theorem small_pair_normalizer_eq_join
    {B : Type*} [_root_.Group B] [Finite B] (e : B ≃* PSL(2,F) × PSL(2,F))
    (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h8 : ¬ 8 ∣ Nat.card PSL(2,F)) (S : Sylow 2 B) (P : Subgroup B)
    (hp : IsPGroup 3 P) (hc : Nat.card P = 9)
    (hn : P ≤ normalizer (S : Set B)) :
    normalizer (S : Set B) = P ⊔ (S : Subgroup B) := by
  have hS : Nat.card S = 16 := by
    have hh := small_pair_sylow_card hF h8 (S.mapSurjective (f := e.toMonoidHom) e.surjective)
    exact (Nat.card_congr (e.subgroupMap S).toEquiv).trans hh
  have hN : Nat.card (normalizer (S : Set B)) ≤ 144 := by
    have hh := small_pair_normalizer_card_le hF h8
      (S.mapSurjective (f := e.toMonoidHom) e.surjective)
    change Nat.card (normalizer ((S : Subgroup B).map e.toMonoidHom : Set (PSL(2,F) × PSL(2,F)))) ≤ 144 at hh
    rw [←map_equiv_normalizer_eq,card_map_of_injective e.injective] at hh
    exact hh
  symm
  apply eq_of_le_of_card_ge (sup_le hn (S : Subgroup B).le_normalizer)
  rw [sup_comm,card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn
    (S.isPGroup'.disjoint_of_coprime hp (by decide)),hS,hc]
  exact hN

end Theory.PSL2

namespace Theory.PSL2
open Theory.GroupTheory.SylowNormalizerAction
variable {F : Type} [Field F] [Finite F]

/-- In a small-congruence PSL₂ square the exchanged cubic-generated radical
is either trivial or the full Sylow subgroup. -/
theorem small_pair_radical_eq_or_bot
    {Q B : Type*} [_root_.Group Q] [Finite Q] [_root_.Group B] [Finite B]
    (eQ : Q ≃* PSL(2,F)) (eB : B ≃* Q × Q)
    (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h8 : ¬ 8 ∣ Nat.card PSL(2,F)) (S : Sylow 2 B) (U P : Subgroup B)
    (hUS : U ≤ (S : Subgroup B)) (hp : IsPGroup 3 P) (hP : Nat.card P = 9)
    (hc : ⁅U,P⁆ = U)
    (he : Nat.card ((U.map eB.toMonoidHom).map (MonoidHom.fst Q Q)) =
      Nat.card ((U.map eB.toMonoidHom).map (MonoidHom.snd Q Q))) :
    U = ⊥ ∨ U = (S : Subgroup B) := by
  have hfour (V : Sylow 2 Q) : IsKleinFour V := by
    let W := V.mapSurjective (f := eQ.toMonoidHom) eQ.surjective
    let := small_sylow_kleinFour hF h8 W
    let c : V ≃* W := eQ.subgroupMap V
    exact ⟨(Nat.card_congr c.toEquiv).trans IsKleinFour.card_four,
      (Monoid.exponent_eq_of_mulEquiv c).trans IsKleinFour.exponent_two⟩
  have hself (V : Subgroup Q) (hV : IsKleinFour V) : centralizer (V : Set Q) = V := by
    let W := V.map eQ.toMonoidHom
    let c : V ≃* W := eQ.subgroupMap V
    have hW : IsKleinFour W :=
      ⟨(Nat.card_congr c.toEquiv).symm.trans hV.card_four,
        (Monoid.exponent_eq_of_mulEquiv c).symm.trans hV.exponent_two⟩
    apply le_antisymm
    · intro x hx
      have hh : eQ x ∈ centralizer (W : Set PSL(2,F)) := by
        rintro y ⟨z,hz,rfl⟩
        exact (eQ.map_mul z x).symm.trans ((congrArg eQ (hx z hz)).trans (eQ.map_mul x z))
      rw [GorensteinWalter.psl2_kleinFour_centralizer_eq_self F hF W hW] at hh
      exact (mem_map_iff_mem eQ.injective).mp hh
    · let := hV
      let : IsMulCommutative V := IsKleinFour.isMulCommutative
      exact V.le_centralizer
  let S' := S.mapSurjective (f := eB.toMonoidHom) eB.surjective
  let V := S'.mapSurjective (f := MonoidHom.fst Q Q) (fun q => ⟨(q,1),rfl⟩)
  let W := S'.mapSurjective (f := MonoidHom.snd Q Q) (fun q => ⟨(1,q),rfl⟩)
  have hprod : (S' : Subgroup (Q × Q)) = (V : Subgroup Q).prod (W : Subgroup Q) := by
    symm
    apply S'.is_maximal'
    · obtain ⟨a,ha⟩ := V.isPGroup'.exists_card_eq
      obtain ⟨b,hb⟩ := W.isPGroup'.exists_card_eq
      apply IsPGroup.of_card (n := a+b)
      rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod]
      rw [ha,hb,pow_add]
    · intro x hx
      exact ⟨mem_map_of_mem _ hx,mem_map_of_mem _ hx⟩
  let := hfour V
  let := hfour W
  have hc' : ⁅U.map eB.toMonoidHom,P.map eB.toMonoidHom⁆ = U.map eB.toMonoidHom := by
    rw [←map_commutator,hc]
  have hnorm : P.map eB.toMonoidHom ≤ normalizer (U.map eB.toMonoidHom : Set (Q × Q)) :=
    le_normalizer_iff_commutator_le_left.mpr hc'.le
  have hh := four_product_radical_eq_or_bot (V : Subgroup Q) (W : Subgroup Q)
    (hself _ inferInstance) (hself _ inferInstance)
    (U.map eB.toMonoidHom) (P.map eB.toMonoidHom)
    (hprod ▸ map_mono hUS) (hp.map eB.toMonoidHom)
    (by rw [card_map_of_injective eB.injective]; exact hP) hnorm hc' he
  rcases hh with hh | hh
  · exact Or.inl (map_injective eB.injective (hh.trans (Subgroup.map_bot _).symm))
  · exact Or.inr (map_injective eB.injective (hh.trans hprod.symm))
end Theory.PSL2
