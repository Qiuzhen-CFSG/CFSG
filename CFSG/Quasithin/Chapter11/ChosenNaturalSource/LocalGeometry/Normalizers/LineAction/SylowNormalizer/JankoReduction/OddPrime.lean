module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.RankTwo
public import Theory.SpecificGroups.PSL2.FourNormalizer
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeTwoGroup
public import Theory.SpecificGroups.PSL2.PrimeNonsolvableSubgroups
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import Theory.SpecificGroups.Alternating.FiveSylowNormalizerCard
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients.Five
public import Theory.GroupTheory.AbelianSylowAutomizer

/-!
# The odd prime-field exclusion in the moved-component quotient

Dickson's theorem makes the proper nonsolvable join of the residual image
and its Sylow A₅. The residual is already nonsolvable, so it equals this
join. The self-centralizing four Sylow then has normalizer of order twelve;
the A₅ normalizer has the same order, hence contains the full normalizer.
Every odd automorphism preserving this Sylow is inner, represented in that
normalizer, and therefore fixes the residual image. This contradicts the
literal escaping complement action.

The final application retains the original quotient and supplement.
J₁ recognition and terminal assembly remain with qt-d-1222-natural-line-action.
Source: Aschbacher--Smith 3.3.12, case (8) of A.3.12.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer

private theorem odd_psl2_five_sylow_normalizer_le
    {F : Type*} [Field F] [Finite F]
    (ho : GorensteinWalter.IsOddPrimePower (Nat.card F)) (P : Sylow 2 PSL(2,F))
    (B : Subgroup PSL(2,F)) (eB : B ≃* alternatingGroup (Fin 5))
    (hPB : (P : Subgroup PSL(2,F)) ≤ B) :
    normalizer (P : Set PSL(2,F)) ≤ B := by
  let PB := P.subtype hPB
  let P5 := PB.mapSurjective (f := eB.toMonoidHom) eB.surjective
  have h4 : Nat.card P = 4 := by
    calc
      Nat.card P = Nat.card PB := (Nat.card_congr (subgroupOfEquivOfLe hPB).toEquiv).symm
      _ = Nat.card P5 := Nat.card_congr
        ((PB : Subgroup B).equivMapOfInjective eB.toMonoidHom eB.injective).toEquiv
      _ = 4 := Theory.PSL2.SylowFixedQuotients.alternating_sylow_card P5
  obtain ⟨m,hm,⟨e⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F ho P
  obtain ⟨C,hCP,hC⟩ := GorensteinWalter.exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (P : Subgroup PSL(2,F)) hm e
  have heCP : C = (P : Subgroup PSL(2,F)) := eq_of_le_of_card_ge hCP (by
    rw [h4,hC.card_four])
  have hP : IsKleinFour P := by rw [← heCP]; exact hC
  let := hP
  let : IsMulCommutative P := IsKleinFour.isMulCommutative
  have hc := Theory.PSL2.FourNormalizer.four_centralizer ho (P : Subgroup PSL(2,F))
  have hk : Nat.card (P : Subgroup PSL(2,F)).normalizerMonoidHom.ker = 4 := by
    rw [normalizerMonoidHom_ker,hc,
      Nat.card_congr (subgroupOfEquivOfLe (P : Subgroup PSL(2,F)).le_normalizer).toEquiv,h4]
  have hr : Nat.card (P : Subgroup PSL(2,F)).normalizerMonoidHom.range ≤ 3 := by
    have hd : Nat.card (P : Subgroup PSL(2,F)).normalizerMonoidHom.range ∣ 6 := by
      simpa only [IsKleinFour.card_mulAut] using
        (P : Subgroup PSL(2,F)).normalizerMonoidHom.range.card_subgroup_dvd_card
    have hh := Nat.le_of_dvd (by decide : 0 < 6) hd
    have hod := Nat.odd_iff.mp (P.odd_card_normalizer_action)
    interval_cases h : Nat.card (P : Subgroup PSL(2,F)).normalizerMonoidHom.range <;>
      norm_num at *
  have hN : Nat.card (normalizer (P : Set PSL(2,F))) ≤ 12 := by
    have hh := (P : Subgroup PSL(2,F)).normalizerMonoidHom.ker.card_mul_index
    rw [index_ker,hk] at hh
    have he : 4 * Nat.card (P : Subgroup PSL(2,F)).normalizerMonoidHom.range =
        Nat.card (normalizer (P : Set PSL(2,F))) := hh
    omega
  let NB := (normalizer (PB : Set B)).map B.subtype
  have hNB : Nat.card NB = 12 := by
    rw [card_map_of_injective B.subtype_injective]
    have he : (normalizer (PB : Set B)).map eB.toMonoidHom = normalizer (P5 : Set _) :=
      map_normalizer_eq_of_bijective _ eB.bijective
    have hh := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_card P5
    rw [←he,card_map_of_injective eB.injective] at hh
    exact hh
  have hmPB : (PB : Subgroup B).map B.subtype = (P : Subgroup PSL(2,F)) :=
    map_subgroupOf_eq_of_le hPB
  have hle : NB ≤ normalizer (P : Set PSL(2,F)) := by
    change NB ≤ normalizer ((P : Subgroup PSL(2,F)) : Set _)
    rw [← hmPB]
    exact le_normalizer_map B.subtype
  have heN : NB = normalizer (P : Set PSL(2,F)) :=
    eq_of_le_of_card_ge hle (by rw [hNB]; exact hN)
  rw [← heN]
  exact map_subtype_le _

private theorem prime_psl2_normalizer_le_nonsolvable
    {F : Type*} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p) (B : Subgroup PSL(2,F)) (P : Sylow 2 PSL(2,F))
    (hne : B ⊔ (P : Subgroup PSL(2,F)) ≠ ⊤) (hns : ¬ Group.IsSolvable B) :
    normalizer (P : Set PSL(2,F)) ≤ B := by
  let : Fact p.Prime := ⟨hp⟩
  let J := B ⊔ (P : Subgroup PSL(2,F))
  have hJns : ¬ Group.IsSolvable J := by
    intro hsol
    let := hsol
    exact hns (Group.isSolvable_of_isSolvable_injective (inclusion_injective (show B ≤ J from le_sup_left)))
  obtain ⟨_,_,⟨eJ⟩⟩ := Theory.PSL2.prime_nonsolvable_proper_is_alternating_five ho hF J hne hJns
  have hBJ : B = J := by
    apply le_antisymm le_sup_left
    apply subgroupOf_eq_top.mp
    by_contra hh
    let := alternatingGroup.isSolvable_subgroup_of_equiv_five eJ (B.subgroupOf J) hh
    exact hns (Group.isSolvable_of_surjective
      (f := (subgroupOfEquivOfLe (show B ≤ J from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show B ≤ J from le_sup_left)).surjective)
  have hPB : (P : Subgroup PSL(2,F)) ≤ B := hBJ ▸ (show (P : Subgroup PSL(2,F)) ≤ J from le_sup_right)
  have heB : Nonempty (B ≃* alternatingGroup (Fin 5)) := by rw [hBJ]; exact ⟨eJ⟩
  exact odd_psl2_five_sylow_normalizer_le ⟨p,1,hp,ho,by decide,by simpa using hF⟩
    P B heB.some hPB

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}
namespace MovedComponent
variable (E : MovedComponent S f A)

/-- An odd inner Sylow action represented in the residual cannot be the escaping action. -/
theorem false_of_sylow_normalizer_le_residual
    (hout : IsPGroup 2 (MulAut.Outer (E.component ⧸ pCore 2 E.component)))
    (hN : normalizer (E.quotientSylow : Set _) ≤ E.residualImage) : False := by
  apply E.oddAction_moves
  rintro _ ⟨a,rfl⟩
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (E.component ⧸ pCore 2 E.component))
  have ha : q (E.oddAction a) = 1 :=
    (hout.powEquiv (Nat.coprime_two_left.mpr A.odd)).injective (by
      simp only [IsPGroup.powEquiv_apply,one_pow,←map_pow,pow_card_eq_one',map_one])
  obtain ⟨g,hg⟩ := (QuotientGroup.eq_one_iff _).mp ha
  have hgP : g ∈ normalizer (E.quotientSylow : Set _) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change MulAut.conj g • E.quotientSylow = E.quotientSylow
    rw [hg]
    exact E.oddAction_preserves_quotientSylow ⟨a,rfl⟩
  change (E.oddAction a) • E.residualImage = E.residualImage
  rw [←hg]
  exact mem_normalizer_iff_map_conj_eq.mp (E.residualImage.le_normalizer (hN hgP))

/-- The actual component quotient excludes every odd prime-field PSL₂ model. -/
theorem quotient_not_odd_prime_psl2 {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    ¬ ClassicalGroup.IsPSL (E.component ⧸ pCore 2 E.component) 2 p := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let B := E.residualImage.map e.toMonoidHom
  obtain ⟨P,hP⟩ := E.quotientSylow_isSylow
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPB : B ⊔ (P' : Subgroup PSL(2,F)) ≠ ⊤ := by
    intro hh
    apply E.residualImage_sup_quotientSylow_ne_top
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_top_of_surjective _ e.surjective,Subgroup.map_sup,←hP]
    exact hh
  have hBns : ¬ Group.IsSolvable B := by
    intro hh
    let := hh
    exact E.residualImage_not_solvable (Group.isSolvable_of_isSolvable_injective
      (f := (E.residualImage.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
      (E.residualImage.equivMapOfInjective e.toMonoidHom e.injective).injective)
  have hN := prime_psl2_normalizer_le_nonsolvable hp ho hF B P' hPB hBns
  apply E.false_of_sylow_normalizer_le_residual
  · exact (Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two
      hp ho (n := 1) (by decide) (by simpa using hF)).of_equiv (MulAut.outerCongr e).symm
  · apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [← hP,map_equiv_normalizer_eq]
    exact hN
end MovedComponent

/-- The prime-field exclusion is applied to the component supplied by the original escape. -/
theorem exists_moved_component_not_odd_prime_psl2 (f : InvariantFlag c) (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ E : MovedComponent S f A, ∀ p : ℕ, p.Prime → Odd p →
      ¬ ClassicalGroup.IsPSL (E.component ⧸ pCore 2 E.component) 2 p := by
  obtain ⟨E⟩ := exists_movedComponent f A hescape
  exact ⟨E,fun _ hp ho => E.quotient_not_odd_prime_psl2 hp ho⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
