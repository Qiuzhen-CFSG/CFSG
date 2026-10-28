module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Borel
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Catalogue
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Normalization
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Source523
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.GlobalPrimes
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.Definitions
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.ChapterE.Defs
public import Theory.GroupTheory.PResidual.Defs
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.PSL3.LinearThreeBorelOrder


/-!
# Local Suzuki obstruction for 13.6.27

For a genuine C-component D of an H_z member, 13.6.26(1) puts its literal
ambient image outside M. Given its actual Suzuki quotient and normalization
by the restricted Sylow subgroup, the Borel argument constructs ⟨D,T⟩ in
the source family HStar(T,M), using exactly 13.6.25(3).

If D has order prime to three, so does DT, and consequently so does
O²(DT)/O₂(O²(DT)). This excludes both local quotient possibilities L₂(4)
and L₃(4) in 5.2.3(1). The former comparison uses the actual PSL₂(4) = A₅
isomorphism; the latter uses a Borel of order 192 in the actual PSL₃(4).

The final lemmas combine the complete A.3.6 catalogue deduction and the
five-rank component-orbit argument. Simple QTKE supplies SQTK for C_G(z),
and passage through its actual two-core quotient supplies the catalogue's
input. Thus neither the Suzuki identification nor T-normalization is an
extra premise. The precise 13.6.25(2) input also gives n(DT) > 1.

`component_unique_or_global_alternative` applies the complete universal
5.2.3 implication from `Source523` to this actual join. Uniqueness remains
conditional on establishing its source setup under Hypothesis 13.3.1 and
excluding the two global alternatives. The older `Components.Seed.Universal523` does not
encode that statement: it omits the module clause and the global alternatives,
and puts the component in the wrong ambient group. It is not used here.
In particular nothing here uses the unresolved universal assertion of 6.2.20.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.6.27,
printed p.934 / PDF p.951; Theorem 5.2.3, printed p.649.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open ChapterF.Source
universe u
variable {G : Type*} [Group G] [Finite G]

/-- Apply 13.6.26(1) to the literal ambient image of a component in H_z,
and use 13.6.25(3) to put its actual Suzuki Borel in M. -/
theorem hz_component_join_mem_HStar (T : Sylow 2 G) (L₁ H M : Subgroup G) (z : G)
    (hz : orderOf z = 2) (hzT : z ∈ T)
    (hHz : H ∈ Section08.Source.Hz L₁ T (centralizer ({z} : Set G)) M)
    (D : Subgroup H) (hD : D.IsCComponent)
    (hn : (T : Subgroup G).subgroupOf H ≤ normalizer (D : Set H))
    {m : ℕ} (e : (D ⧸ pCore 2 D) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (h25 : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (h26 : ∀ J ∈ Section08.Source.Hz L₁ T (centralizer ({z} : Set G)) M,
      ∀ E : Subgroup J, E.IsCComponent → ¬ E.map J.subtype ≤ M) :
    D.map H.subtype ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) M := by
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hHz.1.2
  have hn' : (T : Subgroup G) ≤ normalizer (D.map H.subtype : Set G) := by
    have hm := (map_mono (f := H.subtype) hn).trans (D.le_normalizer_map H.subtype)
    rwa [map_subgroupOf_eq_of_le hTH] at hm
  let eD := D.equivMapOfInjective H.subtype H.subtype_injective
  let eQ := QuotientGroup.congr _ _ eD (pCore_map_iso 2 eD)
  exact suzuki_join_mem_HStar T (D.map H.subtype) M z hz hzT
    (hTH.trans hHz.2.1) ((map_subtype_le D).trans hHz.2.1) hn'
    (eQ.symm.trans e) (h26 H hHz D hD) h25

/-- Adjoining a normalizing two-group preserves order prime to three. -/
theorem join_coprime_three (D T : Subgroup G) (hD : Nat.Coprime 3 (Nat.card D))
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (D : Set G)) :
    Nat.Coprime 3 (Nat.card (D ⊔ T : Subgroup G)) := by
  obtain ⟨n, hc⟩ := hT.exists_card_eq
  have ht : Nat.Coprime 3 (Nat.card T) := by
    rw [hc]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hd : Nat.card (D ⊔ T : Subgroup G) ∣ Nat.card D * Nat.card T := by
    rw [card_mul_eq_card_inf_mul_card_sup_of_normalizes D T hn]
    exact dvd_mul_left _ _
  exact (hD.mul_right ht).coprime_dvd_right hd

/-- The exact two-residual/two-core quotient tested by 5.2.3 has 3′ order. -/
theorem residual_quotient_coprime_three (D T : Subgroup G)
    (hD : Nat.Coprime 3 (Nat.card D)) (hT : IsPGroup 2 T)
    (hn : T ≤ normalizer (D : Set G)) :
    Nat.Coprime 3 (Nat.card ((pResidual 2 (D ⊔ T : Subgroup G)) ⧸
      pCore 2 (pResidual 2 (D ⊔ T : Subgroup G)))) := by
  exact (join_coprime_three D T hD hT hn).coprime_dvd_right
    ((pCore 2 (pResidual 2 (D ⊔ T : Subgroup G))).card_quotient_dvd_card.trans
      (pResidual 2 (D ⊔ T : Subgroup G)).card_subgroup_dvd_card)

private theorem three_dvd_of_l2Four {Q : Type*} [Group Q]
    (h : ClassicalGroup.IsPSL Q 2 4) : 3 ∣ Nat.card Q := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  obtain ⟨e₅⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  rw [Nat.card_congr (e.trans e₅).toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

private theorem three_dvd_l3Four : 3 ∣ Nat.card L3Four := by
  have hc : Nat.card F4 = 2 ^ 2 := GaloisField.card 2 2 (by decide)
  have hb := (Matrix.PSL3.LinearThree.borel F4).card_subgroup_dvd_card
  rw [Matrix.PSL3.CartanActions.BorelQuotient.card_borel_linear_three_four F4 hc] at hb
  exact (by decide : 3 ∣ 192).trans hb

/-- Neither exceptional residual quotient in 5.2.3(1) can occur for DT.
This proves the local model incompatibility, not the global 5.2.3 application. -/
theorem residual_models_impossible (D T : Subgroup G)
    (hD : Nat.Coprime 3 (Nat.card D)) (hT : IsPGroup 2 T)
    (hn : T ≤ normalizer (D : Set G)) :
    ¬ (ClassicalGroup.IsPSL
        ((pResidual 2 (D ⊔ T : Subgroup G)) ⧸ pCore 2 (pResidual 2 (D ⊔ T : Subgroup G))) 2 4 ∨
      Nonempty (((pResidual 2 (D ⊔ T : Subgroup G)) ⧸
        pCore 2 (pResidual 2 (D ⊔ T : Subgroup G))) ≃* L3Four)) := by
  have hc := Nat.prime_three.coprime_iff_not_dvd.mp (residual_quotient_coprime_three D T hD hT hn)
  intro h
  rcases h with h | h
  · exact hc (three_dvd_of_l2Four h)
  · obtain ⟨e⟩ := h
    apply hc
    rw [Nat.card_congr e.toEquiv]
    exact three_dvd_l3Four


/-- The two local inputs for the final 5.2.3 contradiction, applied to the
actual component image in an H_z member. The full earlier classification
and its source applicability are still required for that contradiction. -/
theorem hz_component_obstruction (T : Sylow 2 G) (L₁ H M : Subgroup G) (z : G)
    (hz : orderOf z = 2) (hzT : z ∈ T)
    (hHz : H ∈ Section08.Source.Hz L₁ T (centralizer ({z} : Set G)) M)
    (D : Subgroup H) (hD : D.IsCComponent)
    (hn : (T : Subgroup G).subgroupOf H ≤ normalizer (D : Set H))
    {m : ℕ} (e : (D ⧸ pCore 2 D) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hthree : Nat.Coprime 3 (Nat.card D))
    (h25 : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (h26 : ∀ J ∈ Section08.Source.Hz L₁ T (centralizer ({z} : Set G)) M,
      ∀ E : Subgroup J, E.IsCComponent → ¬ E.map J.subtype ≤ M) :
    let J := D.map H.subtype ⊔ (T : Subgroup G)
    J ∈ Chapter3.HStar (T : Subgroup G) M ∧
      ¬ (ClassicalGroup.IsPSL ((pResidual 2 J) ⧸ pCore 2 (pResidual 2 J)) 2 4 ∨
        Nonempty (((pResidual 2 J) ⧸ pCore 2 (pResidual 2 J)) ≃* L3Four)) := by
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hHz.1.2
  have hn' : (T : Subgroup G) ≤ normalizer (D.map H.subtype : Set G) := by
    have hm := (map_mono (f := H.subtype) hn).trans (D.le_normalizer_map H.subtype)
    rwa [map_subgroupOf_eq_of_le hTH] at hm
  have hc : Nat.Coprime 3 (Nat.card (D.map H.subtype)) := by
    rw [← Nat.card_congr (D.equivMapOfInjective H.subtype H.subtype_injective).toEquiv]
    exact hthree
  exact ⟨hz_component_join_mem_HStar T L₁ H M z hz hzT hHz D hD hn e h25 h26,
    residual_models_impossible (D.map H.subtype) T hc T.isPGroup' hn'⟩

private theorem sqtk_twoCore_quotient {X : Type u} [Group X] [Finite X]
    {κ : GroupClass.{u}} (h : IsSQTK κ X) : IsSQTK κ (X ⧸ pCore 2 X) := by
  refine ⟨?_, h.isKGroup.quotient (pCore 2 X)⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho
    (pCore 2 X) pCore_isPGroup).trans (h.stronglyQuasithin p hp ho)

/-- The actual Suzuki quotient and relative normality for an additional
component of C_G(z). The universal A.3.6 implication is the sole earlier
classification input; SQTK and its quotient hypothesis follow from QTKE.
The distinguished component is supplied by the initial construction in
13.6.27, and the three-prime premise by its A.3.18 step. -/
theorem centralizer_other_component_normal_suzuki
    {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G)
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK κ X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (T : Sylow 2 G) (z : G) (hz : orderOf z = 2)
    {K D : Subgroup (centralizer ({z} : Set G))}
    (hK : K.IsCComponent) [K.Normal]
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))) K)
    (hD : D.IsCComponent) (hne : D ≠ K) (hthree : Nat.Coprime 3 (Nat.card D)) :
    D.Normal ∧ ∃ m : ℕ, 1 ≤ m ∧
      Nonempty ((D ⧸ pCore 2 D) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hH := hG.involution_centralizer_sqtk hz
  obtain ⟨m, hm, ⟨e⟩⟩ := Catalogue.component_suzuki_quotient hA36
    (sqtk_twoCore_quotient hH) hD hthree
  have hnormal := suzuki_component_normal hK hc hD hne hm e
    ((primeRank_quotient_le_of_isTwoGroup 5 (by decide)
      (pCore 2 (centralizer ({z} : Set G))) pCore_isPGroup).trans
        (hH.stronglyQuasithin 5 (by decide) (by decide)))
  exact ⟨hnormal, m, hm, ⟨e⟩⟩

/-- Every remaining component produces the exact obstruction to the local
alternative of 5.2.3: its ambient join with T belongs to HStar(T,M), has
generation parameter greater than one, and has neither permitted residual
quotient. This discharges the catalogue, orbit, Borel and parameter steps
of 13.6.27. Applying the full earlier theorem and excluding its global
alternatives are still required to conclude uniqueness. -/
theorem centralizer_other_component_obstruction
    {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G)
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK κ X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (T : Sylow 2 G) (L₁ M : Subgroup G) (z : G)
    (hz : orderOf z = 2) (hzT : z ∈ T)
    (hHz : centralizer ({z} : Set G) ∈
      Section08.Source.Hz L₁ T (centralizer ({z} : Set G)) M)
    {K : Subgroup (centralizer ({z} : Set G))}
    (hK : K.IsCComponent) [K.Normal]
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))) K)
    (hthree : ∀ D : Subgroup (centralizer ({z} : Set G)),
      D.IsCComponent → D ≠ K → Nat.Coprime 3 (Nat.card D))
    (h25n : ∀ J ∈ Chapter1.HOutside G (T : Set G) (M : Set G),
      1 < ChapterE.generationParameter J)
    (h25s : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (h26 : ∀ J ∈ Section08.Source.Hz L₁ T (centralizer ({z} : Set G)) M,
      ∀ E : Subgroup J, E.IsCComponent → ¬ E.map J.subtype ≤ M) :
    ∀ D : Subgroup (centralizer ({z} : Set G)), D.IsCComponent → D ≠ K →
      let J := D.map (centralizer ({z} : Set G)).subtype ⊔ (T : Subgroup G)
      J ∈ Chapter3.HStar (T : Subgroup G) M ∧
        1 < ChapterE.generationParameter J ∧
        ¬ (ClassicalGroup.IsPSL ((pResidual 2 J) ⧸ pCore 2 (pResidual 2 J)) 2 4 ∨
          Nonempty (((pResidual 2 J) ⧸ pCore 2 (pResidual 2 J)) ≃* L3Four)) := by
  intro D hD hne
  obtain ⟨hnormal, m, _, ⟨e⟩⟩ := centralizer_other_component_normal_suzuki
    hG hA36 T z hz hK hc hD hne (hthree D hD hne)
  let := hnormal
  have hn : (T : Subgroup G).subgroupOf (centralizer ({z} : Set G)) ≤
      normalizer (D : Set (centralizer ({z} : Set G))) := by
    rw [normalizer_eq_top]
    exact le_top
  obtain ⟨hJ, hmodels⟩ := hz_component_obstruction T L₁ _ M z hz hzT hHz
    D hD hn e (hthree D hD hne) h25s h26
  have hmin : Minimal (fun Y => Y ∈ Chapter1.HOver G (T : Set G) ∧ ¬ Y ≤ M)
      (D.map (centralizer ({z} : Set G)).subtype ⊔ (T : Subgroup G)) := hJ
  exact ⟨hJ, h25n _ hmin.prop, hmodels⟩

/-- Apply the complete universal 5.2.3 implication to the subgroup constructed
from any additional component. Its local alternative is impossible. Thus
either K is unique, or the ambient group satisfies one of the two genuine
global alternatives. The source exclusions from Hypothesis 13.3.1 must still
eliminate those alternatives in the final uniqueness theorem. -/
theorem component_unique_or_global_alternative
    {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK κ X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (h523 : Source523.EarlierTheorem κ)
    (T : Sylow 2 G) (L L₁ M V : Subgroup G) (n : ℕ)
    (hsetup : Source523.Setup κ T L M V n)
    (z : G) (hz : orderOf z = 2) (hzT : z ∈ T)
    (hHz : centralizer ({z} : Set G) ∈
      Section08.Source.Hz L₁ T (centralizer ({z} : Set G)) M)
    {K : Subgroup (centralizer ({z} : Set G))}
    (hK : K.IsCComponent) [K.Normal]
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))) K)
    (hthree : ∀ D : Subgroup (centralizer ({z} : Set G)),
      D.IsCComponent → D ≠ K → Nat.Coprime 3 (Nat.card D))
    (h25n : ∀ J ∈ Chapter1.HOutside G (T : Set G) (M : Set G),
      1 < ChapterE.generationParameter J)
    (h25s : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (h26 : ∀ J ∈ Section08.Source.Hz L₁ T (centralizer ({z} : Set G)) M,
      ∀ E : Subgroup J, E.IsCComponent → ¬ E.map J.subtype ≤ M) :
    (∀ D : Subgroup (centralizer ({z} : Set G)), D.IsCComponent → D = K) ∨
      Source523.GlobalAlternative G := by
  classical
  by_cases hu : ∀ D : Subgroup (centralizer ({z} : Set G)), D.IsCComponent → D = K
  · exact Or.inl hu
  · right
    push Not at hu
    obtain ⟨D, hD, hne⟩ := hu
    obtain ⟨hJ, hn, hmodels⟩ := centralizer_other_component_obstruction
      hsetup.qtke hA36 T L₁ M z hz hzT hHz hK hc hthree h25n h25s h26 D hD hne
    exact (Source523.residual_models_or_global h523 hsetup hJ hn).resolve_left hmodels

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
