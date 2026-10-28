module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourCharacteristic
public import Theory.SpecificGroups.HeisenbergPrime.SmallAutomorphismExclusions
public import Theory.SpecificGroups.G2.BinaryHeisenbergExclusion
public import Theory.SpecificGroups.SL2.HeisenbergAutomorphismExclusion
public import Theory.SpecificGroups.SL3.HeisenbergAutomorphismExclusion

public import Theory.SpecificGroups.HeisenbergPrime.BinaryRankTwoExclusions

/-!
# Excluding characteristic-two overgroups in the extraspecial four-group branch

For the original strict overgroups H ∩ C_G(x) < G₀ ≤ C_G(x), the genuine
C.2.7 catalogue and faithful Heisenberg action first leave only Sp₄(q) and
G₂(q), q > 2 even. The same literal action image contains the inner group,
has three-rank at most two, and contains a solvable odd-index subgroup
carrying the original faithful Heisenberg action. Cubic field-actor control
makes that action inner; solvable Sylow control then places it in a Borel
whose odd subgroups are abelian, a contradiction.

Consequently no such strict overgroup has F*(G₀) = O₂(G₀). This is the
maximality assertion (*) of 14.7.26. Applying it to the full escaping
centralizer discharges the extra characteristic-two premise in the
ordinary-component extraction and preserves the actual 1.1.5 marking.
The ordinary-component catalogue exclusions, centralizer containment and
TI conclusion remain subsequent steps.

Source: Aschbacher–Smith 14.7.26, printed p.1053, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Representation Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
/-- The faithful original action reduces the C.2.7 catalogue to the two larger rank-two families. -/
theorem extraspecial_four_characteristicTwo_lie_model
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hf : generalizedFitting G₀ = pCore 2 G₀) :
    ∃ E : Subgroup G, E ∈ cComponentsIn G₀ ∧ (E.subgroupOf G₀).Normal ∧
      F.Li L 1 ≤ E ∧ IsSimpleGroup (E ⧸ pCore 2 E) ∧
      RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
        KnownSimple.IsKnownSimple G₀ (F.H.pCoreIn 2)
          (F.H ⊓ centralizer ({x} : Set G)) E ∧
      ∃ k : ChapterB.QuasisimpleSource.BinaryField, 1 < k.degree ∧
        (Nonempty ((E ⧸ pCore 2 E) ≃* Matrix.symplecticGroup (Fin 2) k.Carrier) ∨
         Nonempty ((E ⧸ pCore 2 E) ≃* Atlas.G2.Model k.Carrier)) := by
  obtain ⟨E,hE,hnE,hLE,hs,hi,⟨es⟩,hm⟩ := extraspecial_four_characteristicTwo_source_model
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  obtain ⟨B₀,_,_,_,hu,_,_,_⟩ := extraspecial_four_characteristicTwo_component
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  have hBE (B : Subgroup G₀) (hB : B.IsCComponent) : B = E.subgroupOf G₀ :=
    (hu B hB).trans (hu _ hE.2).symm
  let eqB (B : Subgroup G₀) (hB : B.IsCComponent) : B ≃* E :=
    (MulEquiv.subgroupCongr (hBE B hB)).trans (subgroupOfEquivOfLe hE.1)
  let eqQ (B : Subgroup G₀) (hB : B.IsCComponent) :
      (B ⧸ pCore 2 B) ≃* (E ⧸ pCore 2 E) :=
    QuotientGroup.congr _ _ (eqB B hB) (pCore_map_iso 2 (eqB B hB))
  let Q := RadicalExclusions.ModelReduction.starImage E (F.H.pCoreIn 2) E
  have hfaithful : ∃ a : HeisenbergPrime 3 →* MulAut Q, Function.Injective a := by
    obtain ⟨B,hB,hn,hb⟩ := extraspecial_four_characteristicTwo_faithful_action
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
      G₀ hJG hGC hf
    let := hn
    obtain ⟨_,Y,_,_,⟨ey⟩,hYG,hinj⟩ := hb
    let a := (normalQuotientAction B (pCore 2 B)).comp (inclusion hYG)
    let e := MulAut.congr ((eqQ B hB).trans es)
    exact ⟨e.toMonoidHom.comp (a.comp ey.symm.toMonoidHom),
      e.injective.comp (hinj.comp ey.symm.injective)⟩
  obtain ⟨a,ha⟩ := hfaithful
  have h27 : 27 ∣ Nat.card (MulAut Q) := by
    have hd := card_dvd_of_injective a ha
    simpa only [HeisenbergPrime.card, Nat.reducePow] using hd
  let := hs
  let : IsQuasisimple (E ⧸ pCore 2 E) := hi.quasisimple
  let : IsSimpleGroup Q := es.symm.isSimpleGroup
  let : IsQuasisimple Q := IsQuasisimple.of_mulEquiv es
  have hzQ : center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) inferInstance with hz | hz
    · exact hz
    · let := center_eq_top_iff.mp hz
      exact (Group.IsPerfect.not_isSolvable Q inferInstance).elim
  have hG2 (e : RadicalExclusions.ModelReduction.starImage E (F.H.pCoreIn 2) E ≃*
      commutator (Atlas.G2.Model (ZMod 2))) : False := by
    obtain ⟨B,hB,hn,hb⟩ := extraspecial_four_characteristicTwo_automorphism_restrictions
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
      G₀ hJG hGC hf
    let := hn
    obtain ⟨_,hinner,hodd,hres⟩ := hb
    exact Atlas.G2.BinaryLocalResidual.no_odd_index_heisenberg
      ((eqQ B hB).trans (es.trans e)) _ hinner _ hodd hres
  refine ⟨E,hE,hnE,hLE,hs,hi,?_⟩
  cases hm with
  | linearTwo k e =>
    exact (Matrix.SL2.no_heisenberg_automorphism_action
      ((MulAut.congr e).toMonoidHom.comp a) ((MulAut.congr e).injective.comp ha)).elim
  | linearThree k e =>
    have hz : center SL(3,k.Carrier) = ⊥ := by
      apply le_bot_iff.mp
      intro z hz
      have hh := (centerCongr e.symm ⟨z,hz⟩).property
      change e.symm z ∈ center Q at hh
      rw [hzQ,mem_bot] at hh
      exact mem_bot.mpr (e.symm.map_eq_one_iff.mp hh)
    exact (Matrix.SL3.no_heisenberg_automorphism_action k.degree_pos k.card_eq hz
      ((MulAut.congr e).toMonoidHom.comp a) ((MulAut.congr e).injective.comp ha)).elim
  | symplectic k large e => exact ⟨k,large,Or.inl ⟨es.trans e⟩⟩
  | g2 k large e => exact ⟨k,large,Or.inr ⟨es.trans e⟩⟩
  | g2DerivedTwo e => exact (hG2 e).elim
  | alternating n hn e =>
    rw [Nat.card_congr (MulAut.congr e).toEquiv] at h27
    exact (HeisenbergPrime.SmallAutomorphismExclusions.alternating_not_three_cube hn h27).elim
  | linearFiveTwo e =>
    rw [Nat.card_congr (MulAut.congr e).toEquiv] at h27
    exact (HeisenbergPrime.SmallAutomorphismExclusions.binary_five_not_three_cube h27).elim
  | tripleSix ez _ =>
    have hc : Nat.card (center Q) = 3 := by
      rw [Nat.card_congr ez.toEquiv]
      simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]
    rw [hzQ,card_bot] at hc
    omega

/-- The actual local image is solvable of odd index, contains the original faithful
Heisenberg action, and retains the ambient three-rank bound. -/
theorem extraspecial_four_characteristicTwo_local_action
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hf : generalizedFitting G₀ = pCore 2 G₀) :
    ∃ B : Subgroup G₀, B.IsCComponent ∧ ∃ hn : B.Normal,
      letI := hn
      let a := normalQuotientAction B (pCore 2 B)
      let J := ((F.H ⊓ centralizer ({x} : Set G)).subgroupOf G₀).map a.rangeRestrict
      primeRank 3 a.range ≤ 2 ∧ Group.IsSolvable J ∧
      MulAut.innerSubgroup (B ⧸ pCore 2 B) ≤ a.range ∧ Odd J.index ∧
      ∃ f : HeisenbergPrime 3 →* a.range, Function.Injective f ∧ ∀ y, f y ∈ J := by
  obtain ⟨B,hB,hn,hb⟩ := extraspecial_four_characteristicTwo_automorphism_restrictions
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  let := hn
  obtain ⟨hk,hi,ho,⟨er⟩⟩ := hb
  let a := normalQuotientAction B (pCore 2 B)
  let J := ((F.H ⊓ centralizer ({x} : Set G)).subgroupOf G₀).map a.rangeRestrict
  have hr : primeRank 3 a.range ≤ 2 := by
    rw [←primeRank_equiv 3 (QuotientGroup.quotientKerEquivRange a)]
    have hC := (extraspecial_four_centralizer_source_setup
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ).1
    exact (primeRank_quotient_le_of_isTwoGroup 3 (by decide) a.ker
      (hk.symm ▸ pCore_isPGroup)).trans
        ((_root_.primeRank_le_of_injective 3 (inclusion hGC) (inclusion_injective hGC)).trans
          (hC.stronglyQuasithin 3 (by decide) (by decide)))
  have hs : Group.IsSolvable J := by
    apply isSolvable_of_prime_dvd_card_eq_two_or_three
    intro p hp hd
    rcases hp.eq_two_or_odd with h2 | hodd
    · exact Or.inl h2
    · have hh := odd_prime_dvd_twoCore_quotient_residual hp (Nat.odd_iff.mpr hodd) hd
      rw [Nat.card_congr er.toEquiv,HeisenbergPrime.card] at hh
      exact Or.inr (((Nat.dvd_prime Nat.prime_three).mp
        (hp.dvd_of_dvd_pow hh)).resolve_left hp.ne_one)
  refine ⟨B,hB,hn,hr,hs,hi,ho,?_⟩
  obtain ⟨Y,hYK,_,_,⟨e⟩,_,_⟩ := extraspecial_four_three_sylow_center
    d h hab structural previous faithful earlier he
  have hKC : K F ≤ centralizer ({x} : Set G) := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hkk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hkk)
  have hYJ : Y ≤ F.H ⊓ centralizer ({x} : Set G) := hYK.trans (le_inf (K_le_H F) hKC)
  have hYG : Y ≤ G₀ := hYJ.trans hJG.le
  have hYp : IsPGroup 3 Y := IsPGroup.of_card (n := 3)
    ((Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)))
  have hcop : Nat.Coprime 3 (Nat.card a.ker) := by
    rw [hk]
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G₀)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hinj : Function.Injective (a.comp (inclusion hYG)) :=
    (injective_comp_subtype_of_coprime_ker a hcop (Y.subgroupOf G₀) hYp.comap_subtype).comp
      (subgroupOfEquivOfLe hYG).symm.injective
  let f := (a.rangeRestrict.comp (inclusion hYG)).comp e.symm.toMonoidHom
  refine ⟨f,?_,?_⟩
  · intro y z hh
    exact e.symm.injective (hinj (congrArg Subtype.val hh))
  · intro y
    exact ⟨inclusion hYG (e.symm y),hYJ (e.symm y).property,rfl⟩

private theorem transport_rankTwo_exclusion
    {Q W : Type*} [Group Q] [Finite Q] [Group W] [Finite W] (e : Q ≃* W)
    (exclude : ∀ (A : Subgroup (MulAut W)), MulAut.innerSubgroup W ≤ A →
      primeRank 3 A ≤ 2 → ∀ J : Subgroup A, Group.IsSolvable J → Odd J.index →
      ∀ f : HeisenbergPrime 3 →* A, Function.Injective f → (∀ y, f y ∈ J) → False)
    (A : Subgroup (MulAut Q)) (hA : MulAut.innerSubgroup Q ≤ A)
    (hr : primeRank 3 A ≤ 2) (J : Subgroup A) (hs : Group.IsSolvable J) (ho : Odd J.index)
    (f : HeisenbergPrime 3 →* A) (hf : Function.Injective f) (hJ : ∀ y, f y ∈ J) : False := by
  let ea := MulAut.congr e
  let A' := A.map ea.toMonoidHom
  let eA : A ≃* A' := ea.subgroupMap A
  let J' := J.map eA.toMonoidHom
  have hA' : MulAut.innerSubgroup W ≤ A' := by
    rw [←MulAut.map_innerSubgroup_congr e]
    exact map_mono hA
  have hr' : primeRank 3 A' ≤ 2 := (primeRank_equiv 3 eA).symm ▸ hr
  let := hs
  have hs' : Group.IsSolvable J' := Group.isSolvable_of_surjective
    (eA.toMonoidHom.subgroupMap_surjective J)
  have ho' : Odd J'.index := (index_map_of_bijective (f := eA.toMonoidHom) eA.bijective J).symm ▸ ho
  exact exclude A' hA' hr' J' hs' ho' (eA.toMonoidHom.comp f) (eA.injective.comp hf)
    (fun y => mem_map_of_mem _ (hJ y))

/-- No strict overgroup of the original local intersection inside the outside
centralizer has generalized Fitting subgroup equal to its two-core. -/
theorem extraspecial_four_overgroup_not_characteristicTwo
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    :
    generalizedFitting G₀ ≠ pCore 2 G₀ := by
  intro hf
  obtain ⟨E,hE,_,_,_,_,k,hk,hm⟩ := extraspecial_four_characteristicTwo_lie_model
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  obtain ⟨B,hB,hn,hb⟩ := extraspecial_four_characteristicTwo_local_action
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  let := hn
  obtain ⟨hr,hs,hi,ho,f,hinj,hfJ⟩ := hb
  obtain ⟨B₀,_,_,_,hu,_,_,_⟩ := extraspecial_four_characteristicTwo_component
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  have hBE : B = E.subgroupOf G₀ := (hu B hB).trans (hu _ hE.2).symm
  let eB : B ≃* E := (MulEquiv.subgroupCongr hBE).trans (subgroupOfEquivOfLe hE.1)
  let eQ := QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)
  have hq : 2 < Nat.card k.Carrier := by
    rw [k.card_eq]
    exact (show 2 = 2^1 by norm_num) ▸ Nat.pow_lt_pow_right (by decide : 1 < 2) hk
  rcases hm with hsymp | hg2
  · obtain ⟨e⟩ := hsymp
    apply transport_rankTwo_exclusion (eQ.trans e) _ _ hi hr _ hs ho f hinj hfJ
    intro A hA hr J hs ho f hf hJ
    let := hs
    exact HeisenbergPrime.BinaryRankTwoExclusions.symplectic k.card_eq k.degree_pos hq
      A hA hr J ho f hf hJ
  · obtain ⟨e⟩ := hg2
    apply transport_rankTwo_exclusion (eQ.trans e) _ _ hi hr _ hs ho f hinj hfJ
    intro A hA hr J hs ho f hf hJ
    let := hs
    exact HeisenbergPrime.BinaryRankTwoExclusions.g2 hq A hA hr J ho f hf hJ

/-- An escaping original involution centralizer has an ordinary component,
with the full 1.1.5 marking, without any characteristic-two branch assumption. -/
theorem extraspecial_four_ordinary_component
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    : ∃ (B : Subgroup (centralizer ({x} : Set G))) (z : G),
      IsComponent (centralizer ({x} : Set G)) B ∧ orderOf z = 2 ∧ zpowers z = F.Vi 1 ∧
      B.map (centralizer ({x} : Set G)).subtype =
        ⁅B.map (centralizer ({x} : Set G)).subtype,zpowers z⁆ ∧
      ¬ B.map (centralizer ({x} : Set G)).subtype ≤ F.H ∧
      Chapter15.Section03.Candidates.ComponentStructure.HasModelAction115 B z := by
  have hstrict : F.H ⊓ centralizer ({x} : Set G) < centralizer ({x} : Set G) :=
    lt_of_le_of_ne inf_le_right (fun heq => hout (heq ▸ inf_le_left))
  exact extraspecial_four_ordinary_component_source
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
    (extraspecial_four_overgroup_not_characteristicTwo
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
      _ hstrict le_rfl)

/-- The original local intersection has no proper characteristic-two overgroup
inside the involution centralizer: the maximality assertion (*) on p.1053. -/
theorem extraspecial_four_characteristicTwo_overgroup_eq
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) ≤ G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hf : generalizedFitting G₀ = pCore 2 G₀) :
    G₀ = F.H ⊓ centralizer ({x} : Set G) := by
  by_contra hne
  have hlt := lt_of_le_of_ne hJG (Ne.symm hne)
  have hout : ¬ centralizer ({x} : Set G) ≤ F.H := by
    intro hCH
    exact hlt.not_ge (le_inf (hGC.trans hCH) hGC)
  exact extraspecial_four_overgroup_not_characteristicTwo
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hlt hGC hf

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
