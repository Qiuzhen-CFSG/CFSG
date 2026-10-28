module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalPairedJankoExclusion

/-!
# The original seven-subgroup in a normal J₁ Cartan container

Conjugation on the literal C/O₂(C) is onto its automorphism group, since
all J₁ automorphisms are inner. The full original solvable join of A∩Y,
T and B consequently normalizes a Sylow eight. Its odd part has order
dividing 21, and a cyclic part has order at most eight. The right Hall
subgroup injects into this action and is nontrivial by the original
minimal-parabolic source theorem. Escape and normalization exclude an
order-three left image: it would give an abelian odd group of order 21.
Thus the two images have orders seven and three, with full commutator.

Lifting that commutator through the same two-core action identifies the
actual subgroup A∩C with [A∩Y,B], proves its order is seven, and shows
that the original B moves it. The original left torus then forces 3∣n.
The normal-container sieve and its Chapter 12 consumer retain every
previous alternative. The field action, omega movement and terminal
faithful-module application are still needed to exclude this normal J₁
row; no LocalCartanSieve or SourceLocalCartanEscape inhabitant is asserted.

Source: Aschbacher--Smith 5.1.13, printed pp.636--637, refs/quasithin.pdf;
GLS3 Table 5.3f for the certified J₁ local structure.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

private def jankoInnerEquiv : Janko1.Model ≃* MulAut Janko1.Model :=
  MulEquiv.ofBijective _ ⟨conj_injective_of_center_eq_bot center_eq_bot_of_simple_perfect,
    Janko1.OuterCertificate.aut_inner⟩

omit [Finite G] in
private theorem normal_janko_surjective (C : Subgroup G) [C.Normal]
    (e : (C ⧸ pCore 2 C) ≃* Janko1.Model) :
    Function.Surjective (normalQuotientAction C (pCore 2 C)) := by
  intro z
  obtain ⟨c,hc⟩ := Janko1.OuterCertificate.aut_inner (MulAut.congr e z)
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (pCore 2 C) (e.symm c)
  refine ⟨x,?_⟩
  rw [normalQuotientAction_inner,hx]
  apply (MulAut.congr e).injective
  rw [MulAut.congr_conj,e.apply_symm_apply]
  exact hc

private theorem normal_janko_mixed_action (S : Sylow 2 G)
    (C J E D : Subgroup G) [C.Normal] [Group.IsSolvable J]
    (e : (C ⧸ pCore 2 C) ≃* Janko1.Model)
    (hSJ : (S : Subgroup G) ≤ J) (hEJ : E ≤ J) (hDE : D ≤ E)
    (ho : Odd (Nat.card E)) (hD : IsCyclic D) :
    let f := normalQuotientAction C (pCore 2 C)
    ∃ Q : Sylow 2 (MulAut (C ⧸ pCore 2 C)),
      (Q : Subgroup _) = (S : Subgroup G).map f ∧
      J.map f ≤ normalizer (Q : Set _) ∧
      Nat.card (E.map f) ∣ 21 ∧ Nat.card (D.map f) ≤ 8 := by
  let f := normalQuotientAction C (pCore 2 C)
  let a := (MulAut.congr e).trans jankoInnerEquiv.symm
  let g := a.toMonoidHom.comp f
  let Q := S.mapSurjective (normal_janko_surjective C e)
  let U := Q.mapSurjective (f := a.toMonoidHom) a.surjective
  let : Group.IsSolvable (J.map g) := Group.isSolvable_of_surjective (g.subgroupMap_surjective J)
  have hU : (U : Subgroup _) ≤ J.map g := by
    change ((S : Subgroup G).map f).map a.toMonoidHom ≤ _
    rw [map_map]
    exact map_mono hSJ
  have hoE : Odd (Nat.card (E.map g)) := ho.of_dvd_nat (card_map_dvd E g)
  obtain ⟨hn,hcard⟩ := Janko1.LocalStructure.odd_solvable_overgroup_card_dvd_twenty_one
    U (J.map g) (E.map g) hU (map_mono hEJ) hoE
  let := hD
  let : IsCyclic (D.map g) := isCyclic_of_surjective (g.subgroupMap D) (g.subgroupMap_surjective D)
  have hsmall := Janko1.LocalStructure.abelian_odd_normalizer_card_le_eight U (D.map g)
    (hoE.of_dvd_nat (card_dvd_of_le (map_mono hDE))) ((map_mono (hDE.trans hEJ)).trans hn)
  refine ⟨Q,rfl,?_,?_,?_⟩
  · apply (map_le_map_iff_of_injective (f := a.toMonoidHom) a.injective).mp
    change (J.map f).map a.toMonoidHom ≤ (normalizer (((Q : Subgroup (MulAut (C ⧸ pCore 2 C)))) : Set (MulAut (C ⧸ pCore 2 C)))).map a.toMonoidHom
    rw [map_equiv_normalizer_eq,map_map]
    exact hn
  · rw [←map_map,card_map_of_injective a.injective] at hcard
    exact hcard
  · rw [←map_map,card_map_of_injective a.injective] at hsmall
    exact hsmall

/-- The full normal Janko action retains the original solvable mixed join. -/
theorem normal_janko_action
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) [C.Normal] (hRC : (residual H).subgroupOf Y ≤ C)
    (e : (C ⧸ pCore 2 C) ≃* Janko1.Model) :
    let f := normalQuotientAction C (pCore 2 C)
    let D := (A.subgroupOf Y).map f
    let E := (B.subgroupOf Y).map f
    ∃ Q : Sylow 2 (MulAut (C ⧸ pCore 2 C)),
      (Q : Subgroup _) = ((T : Subgroup G).subgroupOf Y).map f ∧
      ((D ⊔ (Q : Subgroup _)) ⊔ E) ≤ normalizer (Q : Set _) ∧
      Nat.card (D ⊔ E : Subgroup _) ∣ 21 ∧
      (Nat.card D = 3 ∨ Nat.card D = 7) ∧
      IsCyclic D ∧ Odd (Nat.card D) ∧ E ≤ normalizer (D : Set _) ∧
      ¬ D ≤ normalizer (((residual H).subgroupOf Y).map f : Set _) ∧ ¬ D ≤ E := by
  let f := normalQuotientAction C (pCore 2 C)
  let DY := A.subgroupOf Y
  let EY := B.subgroupOf Y
  let JY := (DY ⊔ (T : Subgroup G).subgroupOf Y) ⊔ EY
  have hTY := hH.1.1.2.trans hY.2
  have hBY := (c.right_le.trans inf_le_right).trans hY.2
  obtain ⟨hcyc,hodd,hED,hout,hne,hnot⟩ := cartan_action_escape h hH hgen c hY hescape C hRC
  have hoA : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have hoD : Odd (Nat.card DY) := by
    change Odd (Nat.card (A.subgroupOf Y))
    rw [←inf_subgroupOf_right A Y,Nat.card_congr
      (subgroupOfEquivOfLe (show A ⊓ Y ≤ Y from inf_le_right)).toEquiv]
    exact hoA.of_dvd_nat (card_dvd_of_le (show A ⊓ Y ≤ A from inf_le_left))
  have hoE : Odd (Nat.card EY) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBY).toEquiv,
      ←Nat.card_congr (subgroupOfEquivOfLe c.right_le).toEquiv]
    exact OddHall.odd_hall_odd c.right_hall
  have hEDY : EY ≤ normalizer (DY : Set Y) := by
    intro b hb
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (c.right_normalizes_left hb) (a : G)
  have ho : Odd (Nat.card (DY ⊔ EY : Subgroup Y)) := by
    have hh := hoD.mul hoE
    rw [card_mul_eq_card_inf_mul_card_sup_of_normalizes DY EY hEDY] at hh
    exact hh.of_dvd_nat (dvd_mul_left _ _)
  have hLH : ¬ L ≤ H := by
    intro hh
    exact hescape (inf_le_left.trans ((c.left_le.trans (inf_le_left.trans hh)).trans
      (le_normalizer_residual H)))
  have prep := cartanPreparation_of_not_le h hH hgen hLH
  let M := normalizer (L : Set G) ⊓ H
  let V := localBorel T L ⊔ M
  let : Group.IsSolvable (localBorel T L) := prep.borel_solvable
  let : Group.IsSolvable M := prep.intersection_solvable
  let : Group.IsSolvable V := Group.isSolvable_sup_of_normalizes _ _ prep.intersection_normalizes
  have hJV : JY.map Y.subtype ≤ V := by
    rw [Subgroup.map_sup,Subgroup.map_sup,subgroupOf_map_subtype,map_subgroupOf_eq_of_le hTY,
      map_subgroupOf_eq_of_le hBY]
    exact sup_le (sup_le ((inf_le_left.trans c.left_le).trans le_sup_left)
      ((le_inf h.sylow_normalizes hH.1.1.2).trans le_sup_right))
      (c.right_le.trans le_sup_right)
  let : Group.IsSolvable JY := Group.isSolvable_of_isSolvable_injective
    (f := (inclusion hJV).comp
      (JY.equivMapOfInjective Y.subtype Y.subtype_injective).toMonoidHom)
    ((inclusion_injective hJV).comp (JY.equivMapOfInjective Y.subtype Y.subtype_injective).injective)
  let : IsCyclic A := (c.left_cyclic_and_card h.sylow_normalizes h.linear).1
  let : IsCyclic DY := isCyclic_of_injective (Y.subtype.subgroupComap A) (by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : A => (z : G)) he)))
  obtain ⟨Q,hQ,hn,hcard,hsmall⟩ := normal_janko_mixed_action (T.subtype hTY) C JY
    (DY ⊔ EY) DY e (le_sup_right.trans le_sup_left)
    (sup_le (le_sup_left.trans le_sup_left) le_sup_right) le_sup_left ho inferInstance
  have hc : Nat.card ((DY.map f) ⊔ (EY.map f) : Subgroup _) ∣ 21 := by
    rwa [Subgroup.map_sup] at hcard
  have hd : Nat.card (DY.map f) ∣ 21 := (card_dvd_of_le (show DY.map f ≤ DY.map f ⊔ EY.map f from le_sup_left)).trans hc
  have hcases : Nat.card (DY.map f) = 3 ∨ Nat.card (DY.map f) = 7 := by
    have hneq : Nat.card (DY.map f) ≠ 1 := fun he => hne (card_eq_one.mp he)
    have hmem := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    have hdivs : (21 : ℕ).divisors = {1,3,7,21} := by decide
    rw [hdivs] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hh | hh | hh | hh
    · exact (hneq hh).elim
    · exact Or.inl hh
    · exact Or.inr hh
    · have hs : Nat.card (DY.map f) ≤ 8 := hsmall
      omega
  refine ⟨Q,hQ,?_,hc,hcases,hcyc,hodd,hED,hout,hnot⟩
  rw [hQ]
  change DY.map f ⊔ ((T : Subgroup G).subgroupOf Y).map f ⊔ EY.map f ≤ _
  simpa only [JY,Subgroup.map_sup] using hn

private theorem right_hall_nontrivial
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B) :
    3 ≤ Nat.card B := by
  let M := normalizer (L : Set G)
  let S := T.subtype hH.1.1.2
  have hmin := hstar_minimalParabolic_of_generation_gt_one h.sylow_normalizes hH hgen
  have hmax : ChapterB.minimalParabolicMax S hmin = M.subgroupOf H := by
    let J := ChapterB.minimalParabolicMax S hmin
    have hJ := ChapterB.minimalParabolicMax_spec S hmin
    have hTJ : (T : Subgroup G) ≤ J.map H.subtype := by
      have hh := map_mono (f := H.subtype) hJ.2
      change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ J.map H.subtype at hh
      rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
    have hJH : J.map H.subtype < H := by
      have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hJ.1.lt_top
      simpa only [←MonoidHom.range_eq_map,range_subtype] using hh
    have hJM : J ≤ M.subgroupOf H := map_le_iff_le_comap.mp
      (Chapter3.HStar.proper_overgroup_le T hH hTJ hJH)
    have hn : M.subgroupOf H ≠ ⊤ := fun he => hH.1.2 (subgroupOf_eq_top.mp he)
    exact ((hJ.1.le_iff.mp hJM).resolve_left hn).symm
  obtain ⟨f,_,hf,d,_⟩ := ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.source_intrinsic_escape_knownSimple
    (Chapter3.sqtk_of_mem_H h.qtke hH.1.1.1) S hmin hgen
  let N := M.subgroupOf H
  let e : ChapterB.minimalParabolicMax S hmin ≃* (M ⊓ H : Subgroup G) :=
    (MulEquiv.subgroupCongr hmax).trans
      ((N.equivMapOfInjective H.subtype H.subtype_injective).trans
        (MulEquiv.subgroupCongr (subgroupOf_map_subtype M H)))
  let B' := (B.subgroupOf (M ⊓ H)).map e.symm.toMonoidHom
  have hb' : IsHallSubgroup OddHall.oddPrimes B' :=
    ⟨fun p hp => c.right_hall.p_in_pi_of_p_dvd_card p
      (hp.trans (card_map_dvd _ e.symm.toMonoidHom)),
    fun p hp => c.right_hall.p_in_pi_of_p_dvd_index p
      (hp.trans (index_map_dvd _ e.symm.surjective))⟩
  have hbc : Nat.card B' = Nat.card B := by
    change Nat.card ((B.subgroupOf (M ⊓ H)).map e.symm.toMonoidHom) = _
    rw [card_map_of_injective e.symm.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe c.right_le).toEquiv
  have hc : Nat.card d.witness.abelianGroup = Nat.card B :=
    (Nat.card_congr (subgroupOfEquivOfLe d.hall_le).toEquiv).symm.trans
      ((d.hall.card_eq hb').trans hbc)
  have hl := Nat.le_of_dvd (Nat.card_pos (α := d.witness.abelianGroup))
    (card_dvd_of_le d.witness.cyclic_le)
  rw [d.witness.card,hc] at hl
  have hf2 : 2 ≤ f := by omega
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hf2
  norm_num at hp
  omega

private theorem normal_janko_odd_injective (C E : Subgroup G) [C.Normal]
    (e : (C ⧸ pCore 2 C) ≃* Janko1.Model)
    (hEC : E ≤ C) (ho : Odd (Nat.card E)) :
    Function.Injective ((normalQuotientAction C (pCore 2 C)).comp E.subtype) := by
  let f := (normalQuotientAction C (pCore 2 C)).comp E.subtype
  let : IsSimpleGroup (C ⧸ pCore 2 C) := e.isSimpleGroup
  let : Group.IsPerfect (C ⧸ pCore 2 C) := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hi := conj_injective_of_center_eq_bot
    (center_eq_bot_of_simple_perfect (G := C ⧸ pCore 2 C))
  have hd : Disjoint E ((pCore 2 C).map C.subtype) := by
    apply disjoint_of_coprime_natCard
    rw [card_map_of_injective C.subtype_injective]
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := C)).exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_right.mpr ho).pow_right k
  apply f.ker_eq_bot_iff.mp
  apply bot_unique
  intro x hx
  have he : normalQuotientAction C (pCore 2 C) (x : G) = 1 := hx
  have he' : QuotientGroup.mk' (pCore 2 C) (inclusion hEC x) = 1 := by
    apply hi
    rw [←normalQuotientAction_inner,map_one]
    exact he
  have hmem : (x : G) ∈ (pCore 2 C).map C.subtype :=
    mem_map_of_mem C.subtype ((QuotientGroup.eq_one_iff _).mp he')
  have h1 : (x : G) = 1 := (hd.le_bot ⟨x.property,hmem⟩ : (x : G) ∈ (⊥ : Subgroup G))
  exact Subtype.ext h1

private theorem odd_normalizes_cubic_centralizes (D E : Subgroup G)
    (hD : Nat.card D = 3) (ho : Odd (Nat.card E))
    (hn : E ≤ normalizer (D : Set G)) : E ≤ centralizer (D : Set G) := by
  let : IsCyclic D := isCyclic_of_prime_card hD
  let f : E →* MulAut D := D.normalizerMonoidHom.comp (inclusion hn)
  have hd : Nat.card f.range ∣ 2 := by
    have hh := f.range.card_subgroup_dvd_card
    rwa [IsCyclic.card_mulAut,hD,Nat.totient_prime Nat.prime_three] at hh
  have hodd : Odd (Nat.card f.range) := ho.of_dvd_nat (card_dvd_of_surjective _ f.rangeRestrict_surjective)
  have hone : Nat.card f.range = 1 := Nat.eq_one_of_dvd_coprimes
    (Nat.coprime_two_right.mpr hodd) dvd_rfl hd
  have hbot : f.range = ⊥ := card_eq_one.mp hone
  intro x hx
  have hx' : f ⟨x,hx⟩ = 1 := by
    have hh : f ⟨x,hx⟩ ∈ f.range := ⟨⟨x,hx⟩,rfl⟩
    rwa [hbot,mem_bot] at hh
  have hh : (⟨x,hn hx⟩ : normalizer (D : Set G)) ∈ D.normalizerMonoidHom.ker := hx'
  rwa [normalizerMonoidHom_ker] at hh

omit [Finite G] in
private theorem commuting_sup_abelian (D E : Subgroup G) [IsMulCommutative D]
    [IsMulCommutative E] (hc : D ≤ centralizer (E : Set G)) : IsMulCommutative (D ⊔ E : Subgroup G) := by
  apply le_centralizer_iff_isMulCommutative.mp
  apply sup_le
  · apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff_isMulCommutative.mpr inferInstance) (le_centralizer_iff.mp hc)
  · apply le_centralizer_iff.mpr
    exact sup_le hc (le_centralizer_iff_isMulCommutative.mpr inferInstance)

private theorem disjoint_of_prime_card_not_le (D E : Subgroup G)
    {p : ℕ} (hp : p.Prime) (hD : Nat.card D = p) (hn : ¬ D ≤ E) : Disjoint D E := by
  have hd := card_dvd_of_le (show D ⊓ E ≤ D from inf_le_left)
  rw [hD] at hd
  rcases (Nat.dvd_prime hp).mp hd with he | he
  · exact disjoint_iff.mpr (card_eq_one.mp he)
  · have hEq : D ⊓ E = D := eq_of_le_of_card_ge inf_le_left (by rw [he,hD])
    exact (hn (hEq ▸ (show D ⊓ E ≤ E from inf_le_right))).elim

private theorem janko_seven (Q : Sylow 2 Janko1.Model) (D E : Subgroup Janko1.Model)
    (hN : D ⊔ E ≤ normalizer (Q : Set Janko1.Model))
    (hodd : Odd (Nat.card (D ⊔ E : Subgroup Janko1.Model)))
    (hcard : Nat.card (D ⊔ E : Subgroup Janko1.Model) ∣ 21)
    (hD : Nat.card D = 3 ∨ Nat.card D = 7)
    (hE : 1 < Nat.card E) (hED : E ≤ normalizer (D : Set Janko1.Model))
    (hnot : ¬ D ≤ E) :
    Nat.card D = 7 ∧ Nat.card E = 3 ∧ ⁅D,E⁆ = D := by
  have hoddE : Odd (Nat.card E) := hodd.of_dvd_nat (card_dvd_of_le (show E ≤ D ⊔ E from le_sup_right))
  have hD7 : Nat.card D = 7 := by
    rcases hD with hd3 | hd7
    · have hdis := disjoint_of_prime_card_not_le D E Nat.prime_three hd3 hnot
      have hmul := card_sup_eq_mul_of_normalizes_of_disjoint D E hED hdis
      rw [hmul,hd3] at hcard
      have he7 : Nat.card E ∣ 7 := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 3) hcard
      have heq : Nat.card E = 7 := ((Nat.dvd_prime (by decide : Nat.Prime 7)).mp he7).resolve_left (by omega)
      let : Fact (Nat.Prime 7) := ⟨by decide⟩
      let : IsCyclic D := isCyclic_of_prime_card hd3
      let : IsCyclic E := isCyclic_of_prime_card heq
      have hcomm := odd_normalizes_cubic_centralizes D E hd3 hoddE hED
      let : IsMulCommutative (D ⊔ E : Subgroup Janko1.Model) :=
        commuting_sup_abelian D E (le_centralizer_iff.mp hcomm)
      have hh := Janko1.LocalStructure.abelian_odd_normalizer_card_le_eight Q (D ⊔ E) hodd hN
      rw [hmul,hd3,heq] at hh
      omega
    · exact hd7
  have hdis := disjoint_of_prime_card_not_le D E (by decide) hD7 hnot
  have hmul := card_sup_eq_mul_of_normalizes_of_disjoint D E hED hdis
  have he3 : Nat.card E ∣ 3 := by
    rw [hmul,hD7] at hcard
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 7) hcard
  have hE3 : Nat.card E = 3 := ((Nat.dvd_prime Nat.prime_three).mp he3).resolve_left (by omega)
  have hne : ⁅D,E⁆ ≠ ⊥ := by
    intro hz
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    let : IsCyclic D := isCyclic_of_prime_card hD7
    let : IsCyclic E := isCyclic_of_prime_card hE3
    let : IsMulCommutative (D ⊔ E : Subgroup Janko1.Model) :=
      commuting_sup_abelian D E (commutator_eq_bot_iff_le_centralizer.mp hz)
    have hh := Janko1.LocalStructure.abelian_odd_normalizer_card_le_eight Q (D ⊔ E) hodd hN
    rw [hmul,hD7,hE3] at hh
    omega
  have hle : ⁅D,E⁆ ≤ D := le_normalizer_iff_commutator_le_left.mp hED
  have hd := card_dvd_of_le hle
  rw [hD7] at hd
  have heq : Nat.card (⁅D,E⁆ : Subgroup Janko1.Model) = 7 := ((Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd).resolve_left
    (fun hh => hne (card_eq_one.mp hh))
  exact ⟨hD7,hE3,eq_of_le_of_card_ge hle (by rw [heq,hD7])⟩

/-- The normal Janko row has the original right cubic and an escaping
seven-image, moved by that same cubic. The action uses the full original
containing component quotient, with no two-core discarded from the inputs. -/
theorem normal_janko_seven_action
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) [C.Normal] (hRC : (residual H).subgroupOf Y ≤ C)
    (e : (C ⧸ pCore 2 C) ≃* Janko1.Model) :
    let f := normalQuotientAction C (pCore 2 C)
    let D := (A.subgroupOf Y).map f
    let E := (B.subgroupOf Y).map f
    Nat.card B = 3 ∧ Nat.card D = 7 ∧ Nat.card E = 3 ∧ ⁅D,E⁆ = D := by
  let f := normalQuotientAction C (pCore 2 C)
  let D := (A.subgroupOf Y).map f
  let E := (B.subgroupOf Y).map f
  have hBY := (c.right_le.trans inf_le_right).trans hY.2
  have hoB : Odd (Nat.card B) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.right_le).toEquiv]
    exact OddHall.odd_hall_odd c.right_hall
  have hBC : B.subgroupOf Y ≤ C := (comap_mono (Global.right_cartan_le_residual c)).trans hRC
  have hi := normal_janko_odd_injective C (B.subgroupOf Y) e hBC
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hBY).toEquiv]; exact hoB)
  have hEc : Nat.card E = Nat.card B := by
    have hh := (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm
    rw [MonoidHom.range_comp,range_subtype] at hh
    exact hh.trans (Nat.card_congr (subgroupOfEquivOfLe hBY).toEquiv)
  obtain ⟨Q,hQ,hN,hcard,hD,hcyc,hodd,hED,hout,hnot⟩ := normal_janko_action h hH hgen c hY hescape C hRC e
  let a := (MulAut.congr e).trans jankoInnerEquiv.symm
  let U := Q.mapSurjective (f := a.toMonoidHom) a.surjective
  have hn : D ⊔ E ≤ normalizer (Q : Set _) :=
    (sup_le (le_sup_left.trans le_sup_left) le_sup_right).trans hN
  have hoddDE : Odd (Nat.card (D ⊔ E : Subgroup _)) := by
    have hh := hodd.mul (hoB.of_dvd_nat (by rw [←hEc]))
    rw [card_mul_eq_card_inf_mul_card_sup_of_normalizes D E hED] at hh
    exact hh.of_dvd_nat (dvd_mul_left _ _)
  have hN' : D.map a.toMonoidHom ⊔ E.map a.toMonoidHom ≤ normalizer (U : Set _) := by
    change _ ≤ normalizer (((Q : Subgroup (MulAut (C ⧸ pCore 2 C)))).map a.toMonoidHom : Set Janko1.Model)
    rw [←map_equiv_normalizer_eq,←Subgroup.map_sup]
    exact map_mono hn
  have hcard' : Nat.card (D.map a.toMonoidHom ⊔ E.map a.toMonoidHom : Subgroup _) =
      Nat.card (D ⊔ E : Subgroup _) := by rw [←Subgroup.map_sup,card_map_of_injective a.injective]
  have hED' := (map_mono (f := a.toMonoidHom) hED).trans (le_normalizer_map _)
  have hnot' : ¬ D.map a.toMonoidHom ≤ E.map a.toMonoidHom := fun hh =>
    hnot ((map_le_map_iff_of_injective a.injective).mp hh)
  obtain ⟨hd,he,hm⟩ := janko_seven U (D.map a.toMonoidHom) (E.map a.toMonoidHom) hN'
    (hcard' ▸ hoddDE) (hcard' ▸ hcard)
    (by rw [card_map_of_injective a.injective]; exact hD)
    (by rw [card_map_of_injective a.injective,hEc]; have := right_hall_nontrivial h hH hgen c; omega)
    hED' hnot'
  rw [card_map_of_injective a.injective] at hd he
  have hm' : ⁅D,E⁆ = D := by
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [Subgroup.map_commutator]
    exact hm
  exact ⟨hEc.symm.trans he,hd,he,hm'⟩

private theorem three_dvd_of_seven_dvd_binary_torus {n : ℕ}
    (hd : 7 ∣ 2^n-1) : 3 ∣ n := by
  have hp : 1 ≤ 2^n := Nat.one_le_pow _ _ (by decide)
  have hpow : (2 : ZMod 7)^n=1 := by
    have he := (ZMod.natCast_eq_zero_iff (2^n-1) 7).mpr hd
    rw [Nat.cast_sub hp,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,sub_eq_zero] at he
    exact he
  have hord : orderOf (2 : ZMod 7)=3 := orderOf_eq_prime (by decide) (by decide)
  exact hord ▸ orderOf_dvd_of_pow_eq_one hpow

/-- The source seven is the actual commutator of A∩Y with the original B.
It lies in the same normal containing component and survives its literal
quotient action. In particular the original left degree is divisible by three. -/
theorem normal_janko_original_seven
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) [C.Normal] (hRC : (residual H).subgroupOf Y ≤ C)
    (e : (C ⧸ pCore 2 C) ≃* Janko1.Model) :
    Nat.card B = 3 ∧ 3 ∣ n ∧
      ⁅A ⊓ Y,B⁆ = A ⊓ C.map Y.subtype ∧ Nat.card (⁅A ⊓ Y,B⁆ : Subgroup G) = 7 ∧
      ⁅⁅A ⊓ Y,B⁆,B⁆ = ⁅A ⊓ Y,B⁆ ∧
      ¬ B ≤ centralizer ((⁅A ⊓ Y,B⁆ : Subgroup G) : Set G) := by
  let f := normalQuotientAction C (pCore 2 C)
  let DY := A.subgroupOf Y
  let EY := B.subgroupOf Y
  let U := ⁅DY,EY⁆
  let D := DY.map f
  let E := EY.map f
  have hBY := (c.right_le.trans inf_le_right).trans hY.2
  obtain ⟨hB,hD,hE,hcomm⟩ := normal_janko_seven_action h hH hgen c hY hescape C hRC e
  have hEC : EY ≤ C := (comap_mono (Global.right_cartan_le_residual c)).trans hRC
  have hED : EY ≤ normalizer (DY : Set Y) := by
    intro b hb
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (c.right_normalizes_left hb) (a : G)
  have hUA : U ≤ DY := le_normalizer_iff_commutator_le_left.mp hED
  have hUC : U ≤ C := (commutator_mono le_rfl hEC).trans
    (le_normalizer_iff_commutator_le_right.mp (show DY ≤ normalizer (C : Set Y) from le_normalizer_of_normal))
  have hoA : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have hoDY : Odd (Nat.card DY) := by
    change Odd (Nat.card (A.subgroupOf Y))
    rw [←inf_subgroupOf_right A Y,Nat.card_congr
      (subgroupOfEquivOfLe (show A ⊓ Y ≤ Y from inf_le_right)).toEquiv]
    exact hoA.of_dvd_nat (card_dvd_of_le (show A ⊓ Y ≤ A from inf_le_left))
  have hi := normal_janko_odd_injective C U e hUC (hoDY.of_dvd_nat (card_dvd_of_le hUA))
  have hUm : U.map f = D := (Subgroup.map_commutator DY EY f).trans hcomm
  have hUc : Nat.card U = 7 := by
    have hh := Nat.card_congr (MonoidHom.ofInjective hi).toEquiv
    rw [MonoidHom.range_comp,range_subtype,hUm] at hh
    exact hh.trans hD
  have hUamb : U.map Y.subtype = ⁅A ⊓ Y,B⁆ := by
    rw [Subgroup.map_commutator,subgroupOf_map_subtype,map_subgroupOf_eq_of_le hBY]
  have hsub : ⁅A ⊓ Y,B⁆ ≤ A ⊓ C.map Y.subtype := by
    rw [←hUamb]
    exact le_inf ((map_mono (f := Y.subtype) hUA).trans (by rw [subgroupOf_map_subtype]; exact inf_le_left))
      (map_mono hUC)
  have hEq : ⁅A ⊓ Y,B⁆ = A ⊓ C.map Y.subtype := by
    let V := DY ⊓ C
    have hiV := normal_janko_odd_injective C V e inf_le_right
      (hoDY.of_dvd_nat (card_dvd_of_le (show V ≤ DY from inf_le_left)))
    have hVc : Nat.card V ≤ 7 := by
      have hh := Nat.card_congr (MonoidHom.ofInjective hiV).toEquiv
      rw [MonoidHom.range_comp,range_subtype] at hh
      exact hh.le.trans ((card_le_of_le (map_mono (f := f)
        (show V ≤ DY from inf_le_left))).trans_eq hD)
    have he : U = V := eq_of_le_of_card_ge (le_inf hUA hUC) (by rw [hUc]; exact hVc)
    rw [←hUamb,he,Subgroup.map_inf _ _ _ Y.subtype_injective,subgroupOf_map_subtype]
    exact inf_assoc A Y (C.map Y.subtype) |>.trans
      (congrArg (fun X : Subgroup G => A ⊓ X) (inf_eq_right.mpr (map_subtype_le C)))
  have hcard : Nat.card (⁅A ⊓ Y,B⁆ : Subgroup G) = 7 := by
    rw [←hUamb,card_map_of_injective Y.subtype_injective,hUc]
  have hnon : ⁅U,EY⁆ ≠ ⊥ := by
    intro hz
    have hh := congrArg (map f) hz
    rw [Subgroup.map_commutator,hUm,hcomm,Subgroup.map_bot] at hh
    have hhcard := card_eq_one.mpr hh
    rw [hD] at hhcard
    omega
  have hle : ⁅U,EY⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp
    (normalizer_commutator_ge_right DY EY)
  have hhdiv := card_dvd_of_le hle
  rw [hUc] at hhdiv
  have h7 : Nat.card (⁅U,EY⁆ : Subgroup Y) = 7 := ((Nat.dvd_prime (by decide : Nat.Prime 7)).mp hhdiv).resolve_left
    (fun hc => hnon (card_eq_one.mp hc))
  have heq : ⁅U,EY⁆ = U := eq_of_le_of_card_ge hle (by rw [h7,hUc])
  have hamb : ⁅⁅A ⊓ Y,B⁆,B⁆ = ⁅A ⊓ Y,B⁆ := by
    have hh := congrArg (map Y.subtype) heq
    rwa [Subgroup.map_commutator,hUamb,map_subgroupOf_eq_of_le hBY] at hh
  have hdegree : 3 ∣ n := by
    apply three_dvd_of_seven_dvd_binary_torus
    have hd := card_dvd_of_le (hsub.trans inf_le_left)
    rwa [hcard,(c.left_cyclic_and_card h.sylow_normalizes h.linear).2] at hd
  refine ⟨hB,hdegree,hEq,hcard,hamb,?_⟩
  intro hc
  have hz := commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)
  rw [hamb] at hz
  have hh := card_eq_one.mpr hz
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
/-- The original normal-container sieve retains its complete input and
adds the concrete seven-subgroup in the normal Janko branch. -/
theorem localCartan_escape_seed_normalJanko_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        C.Normal ∧
        (Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) →
          Nat.card B = 3 ∧ 3 ∣ n ∧
          ⁅A ⊓ Y,B⁆ = A ⊓ C.map Y.subtype ∧ Nat.card (⁅A ⊓ Y,B⁆ : Subgroup G) = 7 ∧
          ⁅⁅A ⊓ Y,B⁆,B⁆ = ⁅A ⊓ Y,B⁆ ∧
          ¬ B ≤ centralizer ((⁅A ⊓ Y,B⁆ : Subgroup G) : Set G)) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn⟩ :=
    localCartan_escape_seed_normalContainer_reduction h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,?_⟩
  rintro ⟨e⟩
  let := hCn
  have hYn : Y ≤ normalizer (C.map Y.subtype : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le C)).mp
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hCn
  have hRX : residual H ≤ C.map Y.subtype := by
    rw [←hR]
    exact iSup_conjugates_le_of_le_normalizer _ _ _ hKC
      (hH.1.1.2.trans (hY.2.trans hYn))
  have hRC : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRX
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  exact LocalSieve.normal_janko_original_seven h hH hgen c hY hescape C hRC e

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
