module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveCentralTransport
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison

/-!
# Linear and alternating exclusions through the actual star map

The quotient in C.2.7 is a central image of the original two-core quotient.
These exclusions use the actual surjection from the component, with its
solvable kernel and its order prime to five. Local-component membership and
full Sylow normalization pass through that map. The same parabolic and Borel
arguments therefore apply without identifying the central cover with its
star image. The central triple-A₆ case is kept as a central quotient.
Source: Aschbacher--Smith, original15.2.4, printed pp.1106--1107.
-/
public section
open Subgroup Theory.GroupTheory BenderSuzuki.Converse
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterB.QuasisimpleSource
namespace WreathFiveStarLinear
variable {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
omit [Finite X] in
private theorem degree_of_proper_linearThree_join
    (hc : Nat.card (X ⧸ pCore 2 X) = 60) (F : BinaryField)
    (P : Sylow 2 SL(3,F.Carrier)) (f : X →* SL(3,F.Carrier))
    (hlocal : f.range ∈ ChapterA.Section03.localCComponents P)
    (hproper : f.range ⊔ (P : Subgroup SL(3,F.Carrier)) ≠ ⊤) : F.degree ≤ 2 := by
  by_contra hn
  have hcard : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
  let U := Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow
    F.Carrier F.degree_pos F.card_eq
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(3,F.Carrier) P U
  let a := MulAut.conj g
  let f' := a.toMonoidHom.comp f
  let P' := P.mapSurjective (f := a.toMonoidHom) a.surjective
  have hP : (P : Subgroup SL(3,F.Carrier)).map a.toMonoidHom =
      Matrix.PSL3.LinearThree.unipotentSL F.Carrier := congrArg Sylow.toSubgroup hg
  have hP' : (P' : Subgroup SL(3,F.Carrier)) =
      Matrix.PSL3.LinearThree.unipotentSL F.Carrier := hP
  let : Group.IsSolvable a.toMonoidHom.ker := by
    have he : a.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff a.toMonoidHom).mpr a.injective
    rw [he]
    infer_instance
  have hl := Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal a.toMonoidHom
  have hl' : f'.range ∈ ChapterA.Section03.localCComponents P' := by
    rw [hP',←hP]
    simpa only [f',MonoidHom.range_comp] using hl
  have hj : f'.range ⊔ (P' : Subgroup SL(3,F.Carrier)) ≠ ⊤ := by
    intro hh
    apply hproper
    apply (map_injective (f := a.toMonoidHom) a.injective)
    dsimp only [f'] at hh
    rw [MonoidHom.range_comp,hP',←hP] at hh
    simpa only [Subgroup.map_sup,map_top_of_surjective a.toMonoidHom a.surjective,
      MonoidHom.range_comp] using hh
  have hp := Matrix.PSL3.LinearThree.UnipotentOvergroups.overgroup_unipotentSL F.Carrier
    (f'.range ⊔ (P' : Subgroup SL(3,F.Carrier))) (hP' ▸ le_sup_right) hj
  let : Group.IsPerfect f'.range := Group.IsPerfect.range f'
  rcases hp with hp | hp
  · have hd : f'.range ≤ Matrix.PSL3.LinearThree.pointLocalSL F.Carrier := by
      rw [←Matrix.PSL3.LinearThree.pointParabolicSL_residual F.Carrier hcard]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hp)
    let D := Matrix.PSL3.LinearThree.pointLocalSL F.Carrier
    let q := (Matrix.PSL3.LinearThree.pointLocalSLCoreQuotientEquiv F.Carrier).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 D))
    have hq : Function.Surjective q :=
      (Matrix.PSL3.LinearThree.pointLocalSLCoreQuotientEquiv F.Carrier).surjective.comp
        (QuotientGroup.mk'_surjective _)
    let : Group.IsSolvable q.ker := by
      have he : q.ker = pCore 2 D := by ext x; simp [q]
      rw [he]
      let := pCore_isNilpotent (p := 2) (G := D)
      infer_instance
    exact hn (local_five_degree_of_projection hc F P' f' hl' D hd
      (hP' ▸ inf_le_left) q hq)
  · have hd : f'.range ≤ Matrix.PSL3.LinearThree.lineLocalSL F.Carrier := by
      rw [←Matrix.PSL3.LinearThree.lineParabolicSL_residual F.Carrier hcard]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hp)
    let D := Matrix.PSL3.LinearThree.lineLocalSL F.Carrier
    let q := (Matrix.PSL3.LinearThree.lineLocalSLCoreQuotientEquiv F.Carrier).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 D))
    have hq : Function.Surjective q :=
      (Matrix.PSL3.LinearThree.lineLocalSLCoreQuotientEquiv F.Carrier).surjective.comp
        (QuotientGroup.mk'_surjective _)
    let : Group.IsSolvable q.ker := by
      have he : q.ker = pCore 2 D := by ext x; simp [q]
      rw [he]
      let := pCore_isNilpotent (p := 2) (G := D)
      infer_instance
    exact hn (local_five_degree_of_projection hc F P' f' hl' D hd
      (hP' ▸ inf_le_right) q hq)

private theorem rankOne_normalizer_card (F : BinaryField) (P : Sylow 2 SL(2,F.Carrier)) :
    Nat.card (normalizer ((P : Subgroup SL(2,F.Carrier)) : Set SL(2,F.Carrier))) =
      2 ^ F.degree * (2 ^ F.degree - 1) := by
  let Q := P.mapSurjective (f := pi F.Carrier)
    (pi_surjective (F := F.Carrier))
  rw [Nat.card_congr (equivMapOfInjective
    (normalizer ((P : Subgroup SL(2,F.Carrier)) : Set SL(2,F.Carrier)))
    (pi F.Carrier)
    (pi_injective (F := F.Carrier))).toEquiv]
  rw [map_normalizer_eq_of_bijective (P : Subgroup SL(2,F.Carrier))
    ⟨pi_injective (F := F.Carrier),
      pi_surjective (F := F.Carrier)⟩]
  change Nat.card (normalizer ((Q : Subgroup PSL(2,F.Carrier)) : Set PSL(2,F.Carrier))) = _
  simpa only [Sylow.coe_coe,F.card_eq] using
    (Nat.card_congr (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.sylowNormalizerEquiv F.Carrier Q).toEquiv).trans
      (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.card_borel F.Carrier)

private theorem rankOne_small_solvable_overgroup_five_free
    (F : BinaryField) (hF : F.degree ≤ 2) (P : Sylow 2 SL(2,F.Carrier))
    (D : Subgroup SL(2,F.Carrier)) [Group.IsSolvable D]
    (hPD : (P : Subgroup SL(2,F.Carrier)) ≤ D) : ¬ 5 ∣ Nat.card D := by
  intro hd
  by_cases h1 : F.degree = 1
  · have hh := hd.trans D.card_subgroup_dvd_card
    rw [GorensteinWalter.sl2_card_formula,F.card_eq,h1] at hh
    norm_num at hh
  have h2 : F.degree = 2 := by have := F.degree_pos; omega
  have hl : 3 < Nat.card F.Carrier := by rw [F.card_eq,h2]; decide
  let : IsQuasisimple SL(2,F.Carrier) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv hl (.refl _)
  let : IsSimpleGroup (SL(2,F.Carrier) ⧸ center SL(2,F.Carrier)) := IsQuasisimple.simple
  let : Nontrivial SL(2,F.Carrier) := (QuotientGroup.mk'_surjective (center SL(2,F.Carrier))).nontrivial
  have hn : D ≠ ⊤ := by
    intro ht
    let : Group.IsSolvable (⊤ : Subgroup SL(2,F.Carrier)) := ht ▸ inferInstance
    exact Group.IsPerfect.not_isSolvable SL(2,F.Carrier)
      (Group.isSolvable_of_surjective (f := (topEquiv (G := SL(2,F.Carrier))).toMonoidHom)
        (topEquiv (G := SL(2,F.Carrier))).surjective)
  have hle := Matrix.SpecialLinearGroup.overgroup_le_sylowNormalizer P hPD hn
  have hh := hd.trans (card_dvd_of_le hle)
  change 5 ∣ Nat.card (normalizer ((P : Subgroup SL(2,F.Carrier)) : Set SL(2,F.Carrier))) at hh
  rw [rankOne_normalizer_card,h2] at hh
  norm_num at hh


private theorem solvable_normalized_sup {A : Type*} [Group A]
    (B S : Subgroup A) [Group.IsSolvable B] [Group.IsSolvable S]
    (hn : S ≤ normalizer (B : Set A)) : Group.IsSolvable (B ⊔ S : Subgroup A) := by
  let D := B ⊔ S
  let : (B.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le B.le_normalizer hn)
  let : Group.IsSolvable (B.subgroupOf D) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show B ≤ D from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show B ≤ D from le_sup_left)).injective
  let : Group.IsSolvable (S.subgroupOf D) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show S ≤ D from le_sup_right)).toMonoidHom)
      (subgroupOfEquivOfLe (show S ≤ D from le_sup_right)).injective
  exact Group.isSolvable_of_normal_sup_eq_top (B.subgroupOf D) (S.subgroupOf D)
    (by rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self])

private theorem no_small_rankOne_normalized_five
    (F : BinaryField) (hF : F.degree ≤ 2) (P : Sylow 2 SL(2,F.Carrier))
    (B : Subgroup SL(2,F.Carrier)) [Group.IsSolvable B]
    (hPB : (P : Subgroup SL(2,F.Carrier)) ≤ normalizer (B : Set SL(2,F.Carrier)))
    (hfive : 5 ∣ Nat.card B) : False := by
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  let : Group.IsSolvable (B ⊔ (P : Subgroup SL(2,F.Carrier)) : Subgroup SL(2,F.Carrier)) :=
    solvable_normalized_sup B P hPB
  exact rankOne_small_solvable_overgroup_five_free F hF P _ le_sup_right
    (hfive.trans (card_dvd_of_le (show B ≤ B ⊔ (P : Subgroup SL(2,F.Carrier)) from le_sup_left)))


private theorem linearThree_small_solvable_overgroup_five_free
    (F : BinaryField) (hF : F.degree ≤ 2) (P : Sylow 2 SL(3,F.Carrier))
    (D : Subgroup SL(3,F.Carrier)) [Group.IsSolvable D]
    (hPD : (P : Subgroup SL(3,F.Carrier)) ≤ D) : ¬ 5 ∣ Nat.card D := by
  intro hd
  by_cases h1 : F.degree = 1
  · have hh := hd.trans D.card_subgroup_dvd_card
    rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,F.card_eq,h1] at hh
    norm_num at hh
  have h2 : F.degree = 2 := by have := F.degree_pos; omega
  have hl : 4 ≤ Nat.card F.Carrier := by rw [F.card_eq,h2]; decide
  let U := Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow
    F.Carrier F.degree_pos F.card_eq
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(3,F.Carrier) P U
  let a := MulAut.conj g
  have hP : (P : Subgroup SL(3,F.Carrier)).map a.toMonoidHom =
      Matrix.PSL3.LinearThree.unipotentSL F.Carrier := congrArg Sylow.toSubgroup hg
  let D' := D.map a.toMonoidHom
  let : Group.IsSolvable D' :=
    Group.isSolvable_of_surjective (a.toMonoidHom.subgroupMap_surjective D)
  have hle := Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_le_borelSL
    F.Carrier hl D' (hP ▸ map_mono hPD)
  have hc : Nat.card D = Nat.card D' :=
    Nat.card_congr (equivMapOfInjective D a.toMonoidHom a.injective).toEquiv
  have hd' : 5 ∣ Nat.card D' := hc ▸ hd
  have hh := hd'.trans (card_dvd_of_le hle)
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_borelSL,F.card_eq,h2] at hh
  norm_num at hh

private theorem no_small_linearThree_normalized_five
    (F : BinaryField) (hF : F.degree ≤ 2) (P : Sylow 2 SL(3,F.Carrier))
    (B : Subgroup SL(3,F.Carrier)) [Group.IsSolvable B]
    (hPB : (P : Subgroup SL(3,F.Carrier)) ≤ normalizer (B : Set SL(3,F.Carrier)))
    (hfive : 5 ∣ Nat.card B) : False := by
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  let : Group.IsSolvable (B ⊔ (P : Subgroup SL(3,F.Carrier)) : Subgroup SL(3,F.Carrier)) :=
    solvable_normalized_sup B P hPB
  exact linearThree_small_solvable_overgroup_five_free F hF P _ le_sup_right
    (hfive.trans (card_dvd_of_le (show B ≤ B ⊔ (P : Subgroup SL(3,F.Carrier)) from le_sup_left)))


private theorem linearThree_twoCore (F : BinaryField) : pCore 2 SL(3,F.Carrier) = ⊥ := by
  have hle := IsQuasisimple.pCore_le_center (G := SL(3,F.Carrier)) 2
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := SL(3,F.Carrier))).exists_card_eq
  have hd := card_dvd_of_le hle
  rw [hn] at hd
  have ho : Odd (2 ^ n) := (Matrix.SL3.odd_card_center F.Carrier).of_dvd_nat hd
  have hzero : n = 0 := by
    by_contra hn
    have hh := dvd_pow_self 2 hn
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hh)
  apply (eq_bot_iff_card _).mpr
  rw [hn,hzero,pow_zero]

private theorem linearThree_card_not_dvd (F : BinaryField) : ¬ Nat.card SL(3,F.Carrier) ∣ 60 := by
  intro hc
  have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card.trans hc
  rw [Matrix.PSL3.LinearThree.card_unipotentSL,F.card_eq,←pow_mul] at hd
  have h3 : 3 ≤ F.degree * 3 := by have := F.degree_pos; omega
  have hh : 8 ∣ 60 := (Nat.pow_dvd_pow 2 h3).trans hd
  norm_num at hh

end WreathFiveStarLinear
open WreathFiveStarLinear
variable {G : Type*} [Group G] [Finite G]

/-- A rank-one star image is incompatible with the actual local A₅ and
normalized five-section, even when the star map has a central odd kernel. -/
theorem source_local_component_star_rankOne_exclusion
    {H K S W L Y : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn H) (hSH : S ≤ H)
    (heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hSyl : Chapter1.IsSylowIn 2 S W)
    (hL : L ∈ Chapter1.cComponentsIn W) (hKL : K ≤ L)
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (F : BinaryField) (q : L →* SL(2,F.Carrier)) (hq : Function.Surjective q)
    [Group.IsSolvable q.ker] (hk : ¬ 5 ∣ Nat.card q.ker) : False := by
  obtain ⟨_,P,f,hl⟩ := source_local_component_surjective_data hK hSH hSyl hL hKL q hq
  let : Group.IsPerfect K := source_component_perfect hK
  have hcK : Nat.card (K ⧸ pCore 2 K) = 60 := by
    rw [Nat.card_congr heK.some.toEquiv,nat_card_alternatingGroup]; norm_num
  let r := (topEquiv (G := SL(2,F.Carrier))).toMonoidHom
  let : Group.IsSolvable r.ker := by
    have he : r.ker = ⊥ := r.ker_eq_bot_iff.mpr topEquiv.injective
    rw [he]; infer_instance
  have hd := local_five_degree_of_projection hcK F P f hl ⊤ le_top le_top r topEquiv.surjective
  obtain ⟨P,B,hs,hn,hfive⟩ := source_normalized_five_image_of_surjective hSyl hL hYL hSN hc q hq hk
  let := hs
  exact no_small_rankOne_normalized_five F hd P B hn hfive

/-- The linear-three star row is excluded while retaining its literal central cover map. -/
theorem source_local_component_star_linearThree_exclusion
    {H K S W L Y : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn H) (hSH : S ≤ H)
    (heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hSyl : Chapter1.IsSylowIn 2 S W)
    (hL : L ∈ Chapter1.cComponentsIn W) (hKL : K ≤ L)
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (F : BinaryField) (q : L →* SL(3,F.Carrier)) (hq : Function.Surjective q)
    [Group.IsSolvable q.ker] (hk : ¬ 5 ∣ Nat.card q.ker) : False := by
  obtain ⟨hD,P,f,hl⟩ := source_local_component_surjective_data hK hSH hSyl hL hKL q hq
  let : Group.IsPerfect K := source_component_perfect hK
  have hcK : Nat.card (K ⧸ pCore 2 K) = 60 := by
    rw [Nat.card_congr heK.some.toEquiv,nat_card_alternatingGroup]; norm_num
  have hp := local_five_join_proper_of_card hcK hD (linearThree_twoCore F)
    (linearThree_card_not_dvd F) P f hl
  have hd := degree_of_proper_linearThree_join hcK F P f hl hp
  obtain ⟨P,B,hs,hn,hfive⟩ := source_normalized_five_image_of_surjective hSyl hL hYL hSN hc q hq hk
  let := hs
  exact no_small_linearThree_normalized_five F hd P B hn hfive

/-- The alternating star rows do not require the local A₅ hypothesis. -/
theorem source_local_component_star_alternating_exclusion
    {S W L Y : Subgroup G}
    (hSyl : Chapter1.IsSylowIn 2 S W) (hL : L ∈ Chapter1.cComponentsIn W)
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (q : L →* alternatingGroup (Fin n)) (hq : Function.Surjective q)
    (hk : ¬ 5 ∣ Nat.card q.ker) : False := by
  obtain ⟨P,B,hs,hPB,hfive⟩ := source_normalized_five_image_of_surjective hSyl hL hYL hSN hc q hq hk
  exact Theory.SpecificGroups.Alternating.SmallSolvableFive.not_five_dvd_of_sylow_normalizes
    hn B hs P hPB hfive

/-- A triple-A₆ star image is excluded through its actual central quotient. -/
theorem source_local_component_star_tripleSix_exclusion
    {S W L Y : Subgroup G}
    (hSyl : Chapter1.IsSylowIn 2 S W) (hL : L ∈ Chapter1.cComponentsIn W)
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    {D : Type*} [Group D] [Finite D]
    (q : L →* D) (hq : Function.Surjective q) (hk : ¬ 5 ∣ Nat.card q.ker)
    (ez : center D ≃* Multiplicative (ZMod 3))
    (e : (D ⧸ center D) ≃* alternatingGroup (Fin 6)) : False := by
  let r := e.toMonoidHom.comp (QuotientGroup.mk' (center D))
  have hr : Function.Surjective r := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hrker : r.ker = center D := by ext x; simp [r]
  have hker : ¬ 5 ∣ Nat.card (r.comp q).ker := by
    rw [kernel_card_eq_mul_of_surjective_factor (r.comp q) r q hr hq rfl,hrker]
    intro hh
    rcases (by decide : Nat.Prime 5).dvd_mul.mp hh with hh | hh
    · exact hk hh
    · rw [Nat.card_congr ez.toEquiv] at hh
      norm_num at hh
  exact source_local_component_star_alternating_exclusion hSyl hL hYL hSN hc 6
    (Or.inr (Or.inl rfl)) (r.comp q) (hr.comp hq) hker

end CFSG.Quasithin.Chapter15.Section02
