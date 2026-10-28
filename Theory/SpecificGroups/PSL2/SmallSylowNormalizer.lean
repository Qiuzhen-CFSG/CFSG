module
public import Theory.GroupTheory.SwappedFourNormalizer
public import Theory.SpecificGroups.PSL2.SwappedSylowNormalizer
public import Theory.SpecificGroups.PSL2.PrimeNonsolvableSubgroups

/-!
# Half-Sylow normalizers in small-congruence prime PSL₂ squares

For an odd field of order three or five modulo eight, its PSL₂ Sylow
two-subgroups are Klein four-groups. An exchanged subgroup of index two
in a Sylow of the direct square has order eight and full coordinate
projections. The self-centralizing four-groups and the abstract kernel-line
argument give a two-group inner normalizer. The prime-field outer group
is also a two-group, so every action preserving this intersection has
two-group image.

This is the index-two branch used on the actual normal-closure quotient in
Aschbacher--Smith 10.2.5, printed p.748. The full intersection is separate;
no self-normalization of a Klein four Sylow is asserted.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SylowNormalizerAction
open scoped MatrixGroups
namespace Theory.PSL2
variable {F : Type} [Field F] [Finite F]

/-- The small congruences give exactly the missing factor of two in the order. -/
theorem not_eight_dvd_card_of_small_mod_eight (ho : Odd (Nat.card F))
    (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) :
    ¬ 8 ∣ Nat.card PSL(2,F) := by
  intro hd
  have h := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice ho
  have hh : 16 ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [←h]
    exact Nat.mul_dvd_mul hd (dvd_refl 2)
  have hq := Finite.one_lt_card (α := F)
  have hs : 1 ≤ Nat.card F ^ 2 := by nlinarith
  have hsub : (Nat.card F ^ 2 - 1) % 16 = (Nat.card F ^ 2 + 15) % 16 := by omega
  have hr : Nat.card F % 16 = 3 ∨ Nat.card F % 16 = 5 ∨
      Nat.card F % 16 = 11 ∨ Nat.card F % 16 = 13 := by omega
  have hm := Nat.mod_eq_zero_of_dvd hh
  rcases hr with hh | hh | hh | hh <;>
    norm_num [Nat.mul_mod,hsub,Nat.add_mod,Nat.pow_mod,hh] at hm

/-- An odd PSL₂ Sylow is a four-group when eight does not divide the group order. -/
theorem small_sylow_kleinFour (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h8 : ¬ 8 ∣ Nat.card PSL(2,F)) (S : Sylow 2 PSL(2,F)) : IsKleinFour S := by
  obtain ⟨m,hm,⟨e⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hF S
  have hc : Nat.card S = 2 ^ (m+1) := by
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card,pow_succ']
  have hm1 : m = 1 := by
    by_contra hn
    have hle : 3 ≤ m+1 := by omega
    have hd : 8 ∣ Nat.card S := by
      rw [hc]
      exact Nat.pow_dvd_pow 2 hle
    exact h8 (hd.trans (S : Subgroup PSL(2,F)).card_subgroup_dvd_card)
  subst m
  change S ≃* DihedralGroup 2 at e
  exact ⟨(Nat.card_congr e.toEquiv).trans IsKleinFour.card_four,
    (Monoid.exponent_eq_of_mulEquiv e).trans IsKleinFour.exponent_two⟩

variable {Q A : Type*} [Group Q] [Group A]

/-- The literal exchanged half-Sylow determines a two-group action image. -/
theorem prime_pair_half_action [Finite Q] [IsQuasisimple Q]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hl : 3 < p) (hF : Nat.card F = p)
    (h8 : ¬ 8 ∣ Nat.card PSL(2,F)) (e : Q ≃* PSL(2,F))
    {B : Type*} [Group B] [Finite B] (eB : B ≃* Q × Q)
    (S : Sylow 2 B) (U : Subgroup B) (hUS : U ≤ (S : Subgroup B))
    (hi : U.relIndex (S : Subgroup B) = 2) (a b : MulAut Q)
    (hswap : (U.map eB.toMonoidHom).map
      (a.prodCongr b * (MulEquiv.prodComm : MulAut (Q × Q))).toMonoidHom = U.map eB.toMonoidHom)
    (f : A →* MulAut B) (hf : ∀ g, U.map (f g).toMonoidHom = U) :
    IsPGroup 2 f.range := by
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p,1,Fact.out,hp,by decide,by simpa using hF⟩
  have hoF : IsPGroup 2 (MulAut.Outer PSL(2,F)) := by
    apply IsPGroup.of_card (n := 1)
    change Nat.card (MulAut PSL(2,F) ⧸ MulAut.innerSubgroup PSL(2,F)) = 2^1
    rw [←index_eq_card,prime_card_inner_index F hp hl hF]
    rfl
  have ho : IsPGroup 2 (MulAut.Outer Q) := hoF.of_equiv (MulAut.outerCongr e).symm
  have hz : center Q = ⊥ := by
    apply bot_unique
    intro x hx
    have he : e x ∈ center PSL(2,F) := (centerCongr e ⟨x,hx⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot F,mem_bot] at he
    exact e.injective (he.trans e.map_one.symm)
  have hfour (V : Sylow 2 Q) : IsKleinFour V := by
    let W := V.mapSurjective (f := e.toMonoidHom) e.surjective
    let := small_sylow_kleinFour hodd h8 W
    let c : V ≃* W := e.subgroupMap V
    exact ⟨(Nat.card_congr c.toEquiv).trans IsKleinFour.card_four,
      (Monoid.exponent_eq_of_mulEquiv c).trans IsKleinFour.exponent_two⟩
  have hself (V : Subgroup Q) (hV : IsKleinFour V) : centralizer (V : Set Q) = V := by
    let W := V.map e.toMonoidHom
    let c : V ≃* W := e.subgroupMap V
    have hW : IsKleinFour W :=
      ⟨(Nat.card_congr c.toEquiv).symm.trans hV.card_four,
        (Monoid.exponent_eq_of_mulEquiv c).symm.trans hV.exponent_two⟩
    apply le_antisymm
    · intro x hx
      have hh : e x ∈ centralizer (W : Set PSL(2,F)) := by
        rintro y ⟨z,hz,rfl⟩
        exact (e.map_mul z x).symm.trans ((congrArg e (hx z hz)).trans (e.map_mul x z))
      rw [GorensteinWalter.psl2_kleinFour_centralizer_eq_self F hodd W hW] at hh
      exact (mem_map_iff_mem e.injective).mp hh
    · let := hV
      let : IsMulCommutative V := IsKleinFour.isMulCommutative
      exact V.le_centralizer
  let S' := S.mapSurjective (f := eB.toMonoidHom) eB.surjective
  let U' := U.map eB.toMonoidHom
  have hi' : U'.relIndex (S' : Subgroup (Q × Q)) = 2 := by
    change (U.map eB.toMonoidHom).relIndex ((S : Subgroup B).map eB.toMonoidHom) = 2
    rw [relIndex_map_map_of_injective _ _ eB.injective]
    exact hi
  obtain ⟨hfirst,hsecond⟩ := projections_full S' U' (map_mono hUS) hi'.le
    (projection_card_eq_of_swapped _ a b hswap)
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
  let : IsKleinFour (U'.map (MonoidHom.fst Q Q)) := hfirst.symm ▸ hfour V
  let : IsKleinFour (U'.map (MonoidHom.snd Q Q)) := hsecond.symm ▸ hfour W
  have hcard : Nat.card U' = 8 := by
    have hh : Nat.card U' * 2 = Nat.card S' := by
      have h := relIndex_mul_relIndex (⊥ : Subgroup (Q × Q)) U' (S' : Subgroup _)
        bot_le (map_mono hUS)
      simpa only [relIndex_bot_left,hi'] using h
    have hS : Nat.card S' = 16 := by
      rw [hprod,Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod]
      rw [IsKleinFour.card_four,IsKleinFour.card_four]
    omega
  have hn : IsPGroup 2 (normalizer (U : Set B)) := by
    have hh := four_product_half_normalizer U' hcard (hself _ inferInstance) (hself _ inferInstance)
    rw [←map_equiv_normalizer_eq U eB] at hh
    exact hh.of_equiv (eB.subgroupMap (normalizer (U : Set B))).symm
  exact action_two_of_normalizer_two U hn
    ((AutomorphismSquare.outer_isPGroup_two hz ho).of_equiv (MulAut.outerCongr eB).symm) f hf
end Theory.PSL2
