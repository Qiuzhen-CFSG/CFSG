module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicReeContainers
public import Theory.SpecificGroups.Held.SylowCyclicImages
public import Theory.SpecificGroups.PSL3Four.OuterThreeStructure.FieldTransport
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.TwoSylowSource
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.GroupTheory.PerfectCentralCoverOddSupport
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.SpecificGroups.Held.SylowOrderBound

/-!
# Held cannot contain the original diagram residual

The native Held order bound and the exact diagram quotient orders force
field four. The original hthree excludes PSL₃(4), leaving the full SL₃(4)
cover or Sp₄(4). A nontrivial intrinsic two-core puts the component and
its full normalizing Sylow in a Held two-local subgroup. The checked
63- and17-divisibility obstructions exclude those two cases.

For trivial two-core, even characteristic gives a faithful Sylow action.
Perfect central-cover descent bounds the SL₃(4) automorphism two-part by
256. For Sp₄(4), every cyclic image of the actual Held Sylow has exponent
two, so its outer image has order at most two, and its inner kernel has
order at most256. This contradicts the original Held Sylow order lower
bound1024. The whole cyclic outer group of order four is retained.

The application restricts the original full Sylow to the literal common
component, then passes through the ambient two-core map. It preserves
the original residual, hthree, both Cartans, relative normality and the
strict changed orbit. Only binary classical equality and the marked cubic
SL₃ row remain. Their changed-orbit contradiction, zero-core recognition,
higher-field generation and universal local control remain with the owner.

Source: Aschbacher–Smith A.3.12 and5.2.2, printed pp.47–48,648–649,
refs/quasithin.pdf; GLS3 Table5.3p for the native Held two-local geometry.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open Chapter1.Section02 LocalModels ChapterA.Section03.SourceEmbeddings

private theorem held_sylow_card_ge (S : Sylow 2 Held.He) : 1024 ≤ Nat.card S := by
  open Held.LocalPairs.SylowGeometry.Calculations in
  obtain ⟨P,hP⟩ := exists_representative_sylow representative_isPGroup InnerNormalizer.normalizer_eq
  rw [Nat.card_congr ((S.equiv P).trans (MulEquiv.subgroupCongr hP)).toEquiv]
  exact Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.representative_card_ge_of_orbit_labels
    Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.orbitSizeLabel_eq_card_orbit

private theorem held_not_symplectic_aut
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (S : Sylow 2 Held.He) (f : S →* MulAut (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hf : Function.Injective f) : False := by
  let B := Theory.SpecificGroups.SymplecticFour.Sp F
  let : IsCyclic (MulAut.Outer B) :=
    Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.outer_cyclic (m := 2) (by simpa using hF) (by decide)
  let π := (QuotientGroup.mk' (MulAut.innerSubgroup B)).comp f
  have hr : Nat.card π.range ≤ 2 := by
    apply Nat.le_of_dvd (by decide)
    rw [←IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    rintro ⟨y,x,rfl⟩
    exact Subtype.ext (Held.sylow_cyclic_image_square S π x)
  let j : π.ker →* MulAut.innerSubgroup B := {
    toFun x := ⟨f x.val,(QuotientGroup.eq_one_iff _).mp x.property⟩
    map_one' := Subtype.ext f.map_one
    map_mul' x y := Subtype.ext (f.map_mul x.val y.val) }
  have hj : Function.Injective j := fun x y hh => Subtype.ext (hf (congrArg Subtype.val hh))
  have hd : Nat.card π.ker ∣ 979200 := by
    apply (card_dvd_of_injective j hj).trans
    have hinner := card_range_dvd (MulAut.conj : B →* MulAut B)
    rwa [Theory.SpecificGroups.SymplecticFour.card_sp,hF] at hinner
  have hk : Nat.card π.ker ≤ 256 := by
    obtain ⟨k,hk⟩ := (S.isPGroup'.to_subgroup π.ker).exists_card_eq
    have hcop : Nat.Coprime (Nat.card π.ker) 3825 := by
      rw [hk]
      exact (by decide : Nat.Coprime 2 3825).pow_left k
    exact Nat.le_of_dvd (by decide) (hcop.dvd_mul_right.mp hd)
  have he := π.ker.card_mul_index
  rw [index_ker] at he
  have hcard : Nat.card S ≤ 512 := by
    rw [←he]
    exact (Nat.mul_le_mul hk hr).trans (by decide)
  have hlarge := held_sylow_card_ge S
  omega

private theorem held_not_sl3_aut
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (S : Sylow 2 Held.He) (f : S →* MulAut SL(3,F))
    (hf : Function.Injective f) : False := by
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  let c := PerfectCentralCovering.centerQuotientCover (MulEquiv.refl PSL(3,F))
  let j := (c.autMap (PerfectCentralCovering.centerQuotientCover_ker _)).comp f
  have hj : Function.Injective j := (c.autMap_injective _).comp hf
  have ha : Nat.card (MulAut PSL(3,F)) ∣ 241920 := by
    have hi : Nat.card (MulAut.innerSubgroup PSL(3,F)) ∣ 20160 := by
      have hh := card_range_dvd (MulAut.conj : PSL(3,F) →* MulAut PSL(3,F))
      rwa [Matrix.PSL3.LinearThree.card_projective,hF] at hh
    have ho := Matrix.PSL3Four.OuterThreeStructure.outer_card_dvd_twelve_of_card_four hF
    rw [←(MulAut.innerSubgroup PSL(3,F)).card_mul_index]
    exact Nat.mul_dvd_mul hi ho
  have hd := (card_dvd_of_injective j hj).trans ha
  have h512 : 512 ∣ Nat.card S := by
    obtain ⟨k,hk⟩ := S.isPGroup'.exists_card_eq
    have hh := held_sylow_card_ge S
    rw [hk] at hh ⊢
    have hk9 : 9 ≤ k := by
      by_contra! hlt
      have hu := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show k ≤ 8 by omega)
      omega
    exact pow_dvd_pow 2 hk9
  have hh := h512.trans hd
  norm_num at hh

private theorem held_diagram_four_core_ne_bot
    (S : Sylow 2 Held.He) (B : Subgroup Held.He)
    (hl : B ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Held.He) ≤ normalizer (B : Set Held.He))
    (hm : IsSL (B ⧸ pCore 2 B) 3 4 ∨ ClassicalGroup.IsPSp (B ⧸ pCore 2 B) 2 4) :
    pCore 2 B ≠ ⊥ := by
  intro hc
  let a : B ≃* (B ⧸ pCore 2 B) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc).symm
  have hq : IsQuasisimple B := by
    rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
    · exact IsQuasisimple.of_mulEquiv (a.trans e).symm
    · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
        (f := 2) (by simpa using hF)
      let : IsQuasisimple (Theory.SpecificGroups.SymplecticFour.Sp F) :=
        Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.isQuasisimple (by rw [hF]; decide)
      exact IsQuasisimple.of_mulEquiv
        (a.trans (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)).symm
  let := hq
  have hfaith := sylow_centralizer_eq_bot_of_evenCharacteristic S
    (MainConverse.SporadicLocal.he_evenCharacteristic S) hl hn
  let f := B.normalizerMonoidHom.comp (inclusion hn)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hfaith]
    refine ⟨x.property,?_⟩
    change inclusion hn x ∈ B.normalizerMonoidHom.ker at hx
    rw [normalizerMonoidHom_ker] at hx
    exact hx
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · let b := MulAut.congr (a.trans e)
    exact held_not_sl3_aut hF S (b.toMonoidHom.comp f) (b.injective.comp hf)
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
      (f := 2) (by simpa using hF)
    let b := MulAut.congr (a.trans (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm))
    exact held_not_symplectic_aut hF S (b.toMonoidHom.comp f) (b.injective.comp hf)

private theorem held_local_not_diagram_four
    (S : Sylow 2 Held.He) (B : Subgroup Held.He)
    (hl : B ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Held.He) ≤ normalizer (B : Set Held.He))
    (hm : IsSL (B ⧸ pCore 2 B) 3 4 ∨ ClassicalGroup.IsPSp (B ⧸ pCore 2 B) 2 4) : False := by
  have hc := held_diagram_four_core_ne_bot S B hl hn hm
  have hU : B.pCoreIn 2 ≠ ⊥ := fun he =>
    hc ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  have hN : IsTwoLocal (normalizer (B.pCoreIn 2 : Set Held.He)) :=
    ⟨B.pCoreIn 2,hU,pCore_isPGroup.map B.subtype,rfl⟩
  have hnorm := normalizer_le_normalizer_characteristic_image B (pCore 2 B)
  have hSN := hn.trans hnorm
  have hBN := B.le_normalizer.trans hnorm
  have hd := (card_quotient_dvd_card (pCore 2 B)).trans (card_dvd_of_le hBN)
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · apply Held.TwoLocalCandidates.not_sixtythree_dvd_card_twoLocal S _ hN hSN
    apply dvd_trans _ hd
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF]
    decide
  · apply Held.TwoLocalCandidates.not_seventeen_dvd_card_twoLocal S _ hN hSN
    apply dvd_trans _ hd
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
      (f := 2) (by simpa using hF)
    rw [Nat.card_congr (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm).toEquiv,
      Theory.SpecificGroups.SymplecticFour.card_sp,hF]
    decide

private theorem held_degree_arithmetic {f : ℕ} (hf : 1 < f)
    (hpart : 2^(3*f) ∣ 16121548800)
    (hd : ((2^f)^3*((2^f)^3-1)*((2^f)^2-1)) / Nat.gcd 3 (2^f-1) ∣ 16121548800 ∨
      (2^f)^3*((2^f)^3-1)*((2^f)^2-1) ∣ 16121548800 ∨
      (2^f)^4*((2^f)^2-1)*((2^f)^4-1) ∣ 16121548800) : f = 2 := by
  have hf4 : f ≤ 4 := by
    by_contra! hgt
    have hh := (pow_dvd_pow 2 (show 15 ≤ 3*f by omega)).trans hpart
    norm_num at hh
  by_contra hne
  have hf3 : 3 ≤ f := by omega
  interval_cases f <;> norm_num at hd

private theorem held_diagram_degree
    {Q : Type*} [Group Q] [Finite Q] {f : ℕ} (hf : 1 < f)
    (hd : Nat.card Q ∣ Nat.card Held.He)
    (hm : ClassicalGroup.IsPSL Q 3 (2^f) ∨ IsSL Q 3 (2^f) ∨
      ClassicalGroup.IsPSp Q 2 (2^f)) : f = 2 := by
  have hg := Held.Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup
  have hd := hd.trans (Held.OddOrderBound.card_dvd_of_graph_and_pair_bound hg
    (Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.pairStabilizer_card_dvd hg))
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · have hp := (Matrix.PSL3.LinearThree.unipotent F).card_subgroup_dvd_card
    rw [Matrix.PSL3.LinearThree.card_unipotent F,hF,←pow_mul,Nat.mul_comm f 3,
      ←Nat.card_congr e.toEquiv] at hp
    have hpart := hp.trans hd
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF] at hd
    exact held_degree_arithmetic hf hpart (.inl hd)
  · rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF] at hd
    have hp : 2^(3*f) ∣ 16121548800 := by
      rw [Nat.mul_comm 3 f,pow_mul]
      exact (dvd_mul_of_dvd_left (dvd_mul_right _ _) _).trans hd
    exact held_degree_arithmetic hf hp (.inr (.inl hd))
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let a := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
    rw [Nat.card_congr a.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,hF] at hd
    have hp : 2^(3*f) ∣ 16121548800 := by
      apply (pow_dvd_pow 2 (by omega : 3*f ≤ 4*f)).trans
      rw [Nat.mul_comm 4 f,pow_mul]
      exact (dvd_mul_of_dvd_left (dvd_mul_right _ _) _).trans hd
    exact held_degree_arithmetic hf hp (.inr (.inr hd))

variable {G : Type*} [Group G] [Finite G]

/-- The original full Sylow and original exclusion of PSL₃(4) rule out Held
as common image. The possible SL₃(4) scalar kernel is retained throughout. -/
theorem SelectedSourceModels.parabolic_common_not_held
    {T : Sylow 2 G} {H R X I : Subgroup G}
    (hs : SelectedSourceModels H R) (hn : ¬ (R.subgroupOf H).IsCComponent)
    (hTH : (T : Subgroup G) ≤ H) (hHX : H ≤ X)
    (hIX : I ≤ X) (hI : (I.subgroupOf X).IsCComponent) (hKI : residual H ≤ I)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    ¬ Nonempty (((I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) ≃* Held.He) := by
  rintro ⟨e⟩
  obtain ⟨f,hf,_,hm⟩ := hs.resolve_left hn
  have hd : Nat.card ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ∣ Nat.card Held.He := by
    rw [←Nat.card_congr e.toEquiv]
    exact original_residual_card_dvd_common_image hIX hKI
  have he := held_diagram_degree hf hd hm
  subst f
  change ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 ∨
    IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 ∨
    ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 at hm
  have hm := hm.resolve_left hthree
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  let K := residual H
  have hKH : K ≤ H := map_subtype_le _
  have hKX : K ≤ X := hKH.trans hHX
  have hKlocal : K ∈ ChapterA.Section03.localCComponents (T : Subgroup G) := by
    change (K.subgroupOf (K ⊔ (T : Subgroup G))).IsCComponent
    rw [show K ⊔ (T : Subgroup G) = H from residual_sup_sylow T H hTH]
    exact hs.residual_component_of_not_right hn
  have hTKN : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hTH.trans (le_normalizer_residual H)
  have hKN : (T.subtype (hTH.trans hHX) : Subgroup X) ≤
      normalizer (K.subgroupOf X : Set X) := by
    rw [←subgroupOf_normalizer_eq hKX]
    exact comap_mono hTKN
  obtain ⟨S,_,hl,hSN⟩ := exists_local_sylow_normalizing (T.subtype (hTH.trans hHX))
    (local_restrict hKlocal hKX) hI.subnormal (subgroupOf_mono X hKI) hKN
  let q := QuotientGroup.mk' (pCore 2 X)
  let r := q.subgroupMap (I.subgroupOf X)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let : Group.IsNilpotent r.ker := hr.isNilpotent
  let : Group.IsSolvable r.ker := inferInstance
  let V₀ := (K.subgroupOf X).subgroupOf (I.subgroupOf X)
  let V := V₀.map r
  let a : V₀ ≃* pResidual 2 H :=
    ((subgroupOfEquivOfLe (subgroupOf_mono X hKI)).trans (subgroupOfEquivOfLe hKX)).trans
      ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).symm
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hrv : IsPGroup 2 (r.subgroupMap V₀).ker := by
    rw [ker_subgroupMap]
    exact hr.comap_subtype
  let b := (r.subgroupMap V₀).quotientPCoreEquivOfSurjective (r.subgroupMap_surjective V₀) hrv
  apply held_local_not_diagram_four
    ((S.mapSurjective (q.subgroupMap_surjective _)).mapSurjective e.surjective)
    (V.map e.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker
      (Chapter1.Section02.localCComponents_map_of_solvable_ker hl r) e.toMonoidHom)
    ((map_mono ((map_mono hSN).trans (V₀.le_normalizer_map r))).trans
      (V.le_normalizer_map e.toMonoidHom))
  let ev := e.subgroupMap V
  let eqv := QuotientGroup.congr _ _ ev (pCore_map_iso 2 ev)
  rcases hm with ⟨F,_,_,hF,⟨z⟩⟩ | ⟨F,_,_,hF,⟨z⟩⟩
  · exact .inl ⟨F,inferInstance,inferInstance,hF,⟨eqv.symm.trans (b.symm.trans (aq.trans z))⟩⟩
  · exact .inr ⟨F,inferInstance,inferInstance,hF,⟨eqv.symm.trans (b.symm.trans (aq.trans z))⟩⟩

/-- All nonclassical common containers are excluded on the same original
pair. Both remaining classical alternatives equal the original residual. -/
theorem source_prime_pair_parabolic_held_exclusion
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2 ∧
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2) ∧
        ∃ P : Sylow 2 (extension T L H B D R),
          let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
          normalizingSylow T R < T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧
            ¬ (R.subgroupOf H).IsCComponent ∧
            (∃ f : ℕ, 1 < f ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) ∧
              (ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))) ∧
            let X := normalizer (normalizingSylow T R : Set G) ⊔ H
            ∃ I : Subgroup G, residual H ≤ I ∧ I ≤ X ∧
              (I.subgroupOf X).IsCComponent ∧ (I.subgroupOf X).Normal ∧
              conjugateSpanBy R (U : Subgroup G) < I ∧
              let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
              IsQuasisimple Ibar ∧
                ((IsSimpleGroup Ibar ∧
                  (∃ g : ℕ, 1 < g ∧
                    (ClassicalGroup.IsPSL Ibar 3 (2^g) ∨ ClassicalGroup.IsPSp Ibar 2 (2^g)) ∧
                    residual H = I)) ∨
                  (Nonempty (center Ibar ≃* Multiplicative (ZMod 3)) ∧
                    (∃ f : ℕ, 1 < f ∧ (2^f) % 3 = 1 ∧ IsSL Ibar 3 (2^f) ∧
                      residual H = I ∧
                      IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2^f) ∧
                      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^f) ∧
                      p = 5 ∧ ¬ n ∣ f))))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_parabolic_ree_exclusion h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hfield,I,hKI,hIX,hI,hIn,horbit,hquasi,hm⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hfield,I,hKI,hIX,hI,hIn,horbit,hquasi,?_⟩
  rcases hm with ⟨hsi,hm⟩ | hm
  · refine .inl ⟨hsi,?_⟩
    rcases hm with hclass | hheld
    · exact hclass
    · exact (hs.parabolic_common_not_held hn hH.1.1.2 le_sup_right hIX hI hKI hthree hheld).elim
  · exact .inr hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
