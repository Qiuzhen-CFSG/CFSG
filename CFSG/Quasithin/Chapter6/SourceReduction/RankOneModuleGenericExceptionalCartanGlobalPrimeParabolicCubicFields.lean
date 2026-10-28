module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicJankoMathieu
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SpecialLinearThreeLocalQuotient
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Nonabelian
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.ElementaryAbelian.PrimeRankCard

/-!
# The binary cubic common cover and the original residual

A proper local component in binary SL₃ has an SL₂ quotient over the same
field. Its Sylow two-subgroups are elementary. The original diagram
residual has PSL₃, SL₃ or Sp₄ quotient, whose Sylow two-subgroups are not
elementary. Restricting the original full Sylow to the common component
and retaining the literal two-core quotient therefore identifies that
component with the original residual. The cubic scalar kernel is retained.

The original split-torus rank argument then forces the escaping actor to
have prime order five. Its prime divides the original left Cartan order
but not the residual split-torus order, so the original left degree does
not divide this residual degree. The selected parabolic has the same
field as the residual by its actual local quotient theorem.

The final application preserves the same source pair, both Cartans,
relative normality and the strictly smaller changed orbit. It does not
identify that orbit with the original residual. Rank-two and Held common
containers, the contradiction in the cubic field row, zero-core
recognition and the universal Cartan normalization remain to be proved.

Source: Aschbacher–Smith A.3.12, 5.1.10 and 5.2.2,
printed pp.47–48,634,648–649, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open Chapter1.Section02 LocalModels ChapterA.Section03.SourceEmbeddings

private theorem sl2_two_group_elementary {Y F : Type*} [Group Y]
    [Field F] [Finite F] [CharP F 2] (hp : IsPGroup 2 Y)
    (j : Y →* SL(2,F)) (hj : Function.Injective j) : IsElementaryAbelian 2 Y := by
  let : IsElementaryAbelian 2 (Multiplicative F) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Multiplicative.toAdd.injective
      change (x^2).toAdd = 0
      rw [pow_two]
      exact CharTwo.add_self_eq_zero x.toAdd) }
  obtain ⟨P,hP⟩ := (hp.of_surjective j.rangeRestrict j.rangeRestrict_surjective).exists_le_sylow
  let a := Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 P
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.of_surjective a.toMonoidHom a.surjective
  let k : Y →* P := j.codRestrict P (fun y => hP ⟨y,rfl⟩)
  exact IsElementaryAbelian.of_injective k (by
    intro x y he
    exact hj (congrArg Subtype.val he))

private theorem diagram_not_binary_sl2
    {Y F : Type*} [Group Y] [Finite Y] [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL Y 3 (2^f) ∨ IsSL Y 3 (2^f) ∨
      ClassicalGroup.IsPSp Y 2 (2^f)) (e : Y ≃* SL(2,F)) : False := by
  rcases hm with ⟨E,_,_,hE,⟨a⟩⟩ | ⟨E,_,_,hE,⟨a⟩⟩ | ⟨E,_,_,hE,⟨a⟩⟩
  · let P : Sylow 2 PSL(3,E) := Classical.choice inferInstance
    let j := (a.symm.trans e).toMonoidHom.comp (P : Subgroup PSL(3,E)).subtype
    let : IsElementaryAbelian 2 P := sl2_two_group_elementary P.isPGroup' j
      ((a.symm.trans e).injective.comp Subtype.val_injective)
    exact Matrix.PSL3.LinearThree.sylow_not_isMulCommutative E (by omega) hE P inferInstance
  · let P : Sylow 2 SL(3,E) := Classical.choice inferInstance
    let j := (a.symm.trans e).toMonoidHom.comp (P : Subgroup SL(3,E)).subtype
    let : IsElementaryAbelian 2 P := sl2_two_group_elementary P.isPGroup' j
      ((a.symm.trans e).injective.comp Subtype.val_injective)
    let q := Matrix.PSL3.projection E
    let S := P.mapSurjective (Matrix.PSL3.projection_surjective E)
    let : IsElementaryAbelian 2 S := IsElementaryAbelian.of_surjective
      (q.subgroupMap (P : Subgroup SL(3,E))) (q.subgroupMap_surjective _)
    exact Matrix.PSL3.LinearThree.sylow_not_isMulCommutative E (by omega) hE S inferInstance
  · let : CharP E 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hE
    let b := Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.trans (a.symm.trans e)
    let P := Theory.SpecificGroups.SymplecticFour.unipotentSylow hE (by omega : 0 < f)
    let j := b.toMonoidHom.comp (P : Subgroup _).subtype
    let : IsElementaryAbelian 2 P := sl2_two_group_elementary P.isPGroup' j
      (b.injective.comp Subtype.val_injective)
    have hc := IsElementaryAbelian.card_eq_pow_primeRank (p := 2) P
    have hr : primeRank 2 P = 3*f := P.primeRank_eq.symm.trans
      (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.rank hE (by omega))
    have hcard : Nat.card P = (2^f)^4 := by
      change Nat.card (Theory.SpecificGroups.SymplecticFour.unipotent (F := E)) = _
      rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,hE]
    rw [hcard,hr,←pow_mul] at hc
    have he := (Nat.pow_right_injective (by decide : 1 < 2)) hc
    omega

private theorem eq_of_binary_sl3_diagram
    {Y Q : Type*} [Group Y] [Finite Y] [Group Q] [Finite Q]
    (S : Sylow 2 Y) {V C : Subgroup Y}
    (hl : V ∈ ChapterA.Section03.localCComponents S)
    (hC : C.IsCComponent) (hVC : V ≤ C)
    (a : (V ⧸ pCore 2 V) ≃* Q) {f g : ℕ} (hf : 1 < f) (hg : 1 < g)
    (hm : ClassicalGroup.IsPSL Q 3 (2^f) ∨ IsSL Q 3 (2^f) ∨
      ClassicalGroup.IsPSp Q 2 (2^f))
    (hmodel : IsSL (C ⧸ pCore 2 C) 3 (2^g)) : V = C := by
  by_contra hne
  obtain ⟨P,_,hV⟩ := exists_local_sylow_restriction S hl hVC hC.subnormal
  let B := V.subgroupOf C
  have ht : (⊤ : Subgroup C).IsCComponent := by
    simpa only [subgroupOf_self] using hC.subgroupOf le_rfl
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := g)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent q.ker := hk ▸ pCore_isNilpotent
  let : Group.IsSolvable q.ker := inferInstance
  have hproper : B.map q ≠ ⊤ := by
    intro he
    have hb : B = ⊤ := local_cComponent_eq_of_map_eq hV ht le_top q
      (hk ▸ pCore_isPGroup.le_sylow_of_normal P)
      (by simpa only [map_top_of_surjective q hq] using he)
    exact hne (le_antisymm hVC (subgroupOf_eq_top.mp hb))
  obtain ⟨b⟩ := special_linear_three_local_core_quotient hF hg
    (P.mapSurjective hq) (B.map q)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hV q) hproper
  let av := subgroupOfEquivOfLe hVC
  let aq := QuotientGroup.congr _ _ av (pCore_map_iso 2 av)
  have hkb : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap,hk]
    exact pCore_isPGroup.comap_subtype
  let bq := (q.subgroupMap B).quotientPCoreEquivOfSurjective (q.subgroupMap_surjective B) hkb
  exact diagram_not_binary_sl2 hf hm ((a.symm.trans aq.symm).trans (bq.trans b))

variable {G : Type*} [Group G] [Finite G]

/-- In a binary SL₃ common cover, the original diagram residual is the
whole common component, with the intrinsic quotient kernel retained. -/
theorem SelectedSourceModels.parabolic_common_binary_sl3_eq
    {T : Sylow 2 G} {H R X I : Subgroup G} {g : ℕ}
    (hs : SelectedSourceModels H R) (hn : ¬ (R.subgroupOf H).IsCComponent)
    (hTH : (T : Subgroup G) ≤ H) (hHX : H ≤ X)
    (hIX : I ≤ X) (hI : (I.subgroupOf X).IsCComponent) (hKI : residual H ≤ I)
    (hg : 1 < g)
    (hm : IsSL ((I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) 3 (2^g)) :
    residual H = I := by
  let K := residual H
  have hKH : K ≤ H := map_subtype_le _
  have hKX : K ≤ X := hKH.trans hHX
  have hKlocal : K ∈ ChapterA.Section03.localCComponents (T : Subgroup G) := by
    change (K.subgroupOf (K ⊔ (T : Subgroup G))).IsCComponent
    rw [show K ⊔ (T : Subgroup G) = H from residual_sup_sylow T H hTH]
    exact hs.residual_component_of_not_right hn
  let a : K.subgroupOf X ≃* pResidual 2 H :=
    (subgroupOfEquivOfLe hKX).trans
      ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).symm
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  obtain ⟨f,hf,_,hmodel⟩ := hs.resolve_left hn
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  have he : K.subgroupOf X = I.subgroupOf X :=
    eq_of_binary_sl3_diagram (T.subtype (hTH.trans hHX))
      (local_restrict hKlocal hKX) hI (subgroupOf_mono X hKI) aq hf hg hmodel
      ⟨F,inferInstance,inferInstance,hF,⟨(cComponentTwoCoreQuotientEquiv hI).trans e⟩⟩
  simpa only [map_subgroupOf_eq_of_le hKX,map_subgroupOf_eq_of_le hIX] using
    congrArg (map X.subtype) he

/-- The cubic binary common cover is the original residual. Its split torus
forces a quintic actor and excludes divisibility of its field degree by the
original left degree. Both fields and the cubic center remain distinct. -/
theorem LocalData.parabolic_common_cubic_sl3_fields
    {T : Sylow 2 G} {L W H A B D R X I : Subgroup G} {n p g : ℕ}
    (d : LocalData T L H B D R) (hs : SelectedSourceModels H R)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hn : ¬ (R.subgroupOf H).IsCComponent) (hHX : H ≤ X)
    (hIX : I ≤ X) (hI : (I.subgroupOf X).IsCComponent) (hKI : residual H ≤ I)
    (hg : 1 ≤ g) (hmod : (2^g) % 3 = 1)
    (hm : IsSL ((I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) 3 (2^g)) :
    residual H = I ∧ 1 < g ∧
      IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2^g) ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^g) ∧
      p = 5 ∧ ¬ n ∣ g := by
  have hg' : 1 < g := by
    by_contra! he
    have he : g = 1 := by omega
    norm_num [he] at hmod
  have he := hs.parabolic_common_binary_sl3_eq hn hH.1.1.2 hHX hIX hI hKI hg' hm
  let a : pResidual 2 H ≃* I.subgroupOf X :=
    (((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr he)).trans (subgroupOfEquivOfLe hIX).symm
  let aq := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    (cComponentTwoCoreQuotientEquiv hI)
  have hm' : IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2^g) := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact ⟨F,inferInstance,inferInstance,hF,⟨aq.trans e⟩⟩
  have hp := c.specialLinear_residual_prime_not_dvd h hd hH hg' hm'
  have hp5 : p = 5 := hd.prime.resolve_left (by
    intro hp3
    apply hp
    rw [hp3]
    omega)
  refine ⟨he,hg',hm',?_,hp5,?_⟩
  · exact d.specialLinear_residual_right_quotient hH.1.1.2
      (d.right_lt_residual hH.1.1.2 c hd hz) hg' hm'
  · intro hng
    apply hp
    apply dvd_trans _ (Nat.pow_sub_one_dvd_pow_sub_one 2 hng)
    rw [←c.left_card h.linear h.sylow_normalizes,←hd.card]
    exact card_dvd_of_le hd.le_cartan

/-- The same original pair, with the cubic binary common cover identified
with the original residual and its field and prime restrictions proved. -/
theorem source_prime_pair_parabolic_cubic_fields
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
                  (RankTwoTheoremC Ibar ∨ Nonempty (Ibar ≃* Held.He))) ∨
                  (Nonempty (center Ibar ≃* Multiplicative (ZMod 3)) ∧
                    (∃ f : ℕ, 1 < f ∧ (2^f) % 3 = 1 ∧ IsSL Ibar 3 (2^f) ∧
                      residual H = I ∧
                      IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2^f) ∧
                      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^f) ∧
                      p = 5 ∧ ¬ n ∣ f))))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_parabolic_janko_mathieu_exclusion h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hfield,I,hKI,hIX,hI,hIn,horbit,hquasi,hm⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hfield,I,hKI,hIX,hI,hIn,horbit,hquasi,?_⟩
  rcases hm with hm | ⟨hc,f,hf,hmod,hm⟩
  · exact .inl hm
  obtain ⟨he,hf',hres,hR,hp,hdegree⟩ := d.parabolic_common_cubic_sl3_fields hs h hH c hd hz hn
    le_sup_right hIX hI hKI hf hmod hm
  exact .inr ⟨hc,f,hf',hmod,hm,he,hres,hR,hp,hdegree⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
