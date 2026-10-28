module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentAlternating
public import Theory.SpecificGroups.PSL3.SylowFixedInvertedRoot

/-!
# Odd-prime linear-three component restrictions

The original V-action fixes a Sylow two-subgroup of the selected K-star.
The simple-or-cubic-cover catalogue and the original Sylow E₉ action also
show that it fixes the entire component center. On an odd-prime PSL₃(p)
central quotient, Sylow fixation forces innerness for p > 3. Its inverted
root lifts through the pointwise fixed center with order p unchanged.
The original odd-order restriction therefore gives p = 3 or p = 5.
Neither parameter permits a cubic scalar center in SL₃(p).

The final constructor retains condition (*), both rank cases, every earlier
alternating exclusion and the literal cubic A₇ action kernel. The surviving
classical covers are binary SL₃ and the original SU₃ parameter family.
Their exclusions, the A₇/M₂₂ covers, the remaining faithful rank-two cases,
the rank-one argument and the universal natural reduction remain open.
All earlier geometry and the contrary nonabelian hypothesis are retained.

Source: Aschbacher--Smith, proof of 12.6.26, printed pp.832--833.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- Restrict the original Sylow-star centrality to the actual selected component. -/
theorem SourceHypothesis.original_action_module_fixes_component_sylow
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking) :
    ∃ P : Sylow 2 (Nonabelian.Setup.star H c.K),
      ∀ t ∈ (V.subgroupOf c.localActor).map a.action,
        ∀ x ∈ P, t x = x := by
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  have hT : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  let T₀ := E.Tstar H hT
  obtain ⟨P,hP⟩ := T₀.exists_subgroupOf_eq_of_subnormal B c.component.1
  refine ⟨P,?_⟩
  rintro _ ⟨v,hv,rfl⟩ x hx
  have hxT : x.val ∈ T₀ := by
    change x ∈ (T₀ : Subgroup (Nonabelian.Setup.Hstar H)).subgroupOf B
    rw [←hP]
    exact hx
  obtain ⟨r,hr,he⟩ := hxT
  have hrC : QuotientGroup.mk' (pCore 2 H) r ∈
      centralizer (Nonabelian.Setup.star H V : Set (Nonabelian.Setup.Hstar H)) := by
    have hc := (S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn).2.2.2.2
    change r ∈ (centralizer (Nonabelian.Setup.star H V : Set (Nonabelian.Setup.Hstar H))).comap
      (QuotientGroup.mk' (pCore 2 H))
    rw [hc]
    exact hTV hr
  have hvstar : QuotientGroup.mk' (pCore 2 H) (inclusion a.local_le v) ∈ Nonabelian.Setup.star H V :=
    mem_map_of_mem _ hv
  apply Subtype.ext
  rw [a.conjugation]
  have hcomm := hrC _ hvstar
  rw [he] at hcomm
  rw [hcomm,mul_inv_cancel_right]

/-- Every original marked module action fixes the entire component center. -/
theorem SourceHypothesis.original_action_component_center_fixed
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking) :
    ∀ t ∈ (V.subgroupOf c.localActor).map a.action,
      ∀ x ∈ center (Nonabelian.Setup.star H c.K), t x = x := by
  let B := Nonabelian.Setup.star H c.K
  rcases S.original_selectedComponent_simple_or_cover D hZ z hz hH c with hs|⟨⟨ec⟩,_⟩
  · let := hs
    let := c.component.2
    have hc : center B = ⊥ := by
      rcases (inferInstance : (center B).Normal).eq_bot_or_eq_top with hc|hc
      · exact hc
      · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hc)).elim
    intro t _ x hx
    have hx1 : x = 1 := mem_bot.mp (hc ▸ hx)
    rw [hx1,map_one]
  · have hc : Nat.card (center B) = 3 := by rw [Nat.card_congr ec.toEquiv]; simp
    exact S.original_component_center_fixed D hZ z hz hTV hTz hbound hH hn c a hc

/-- The actual odd-prime PSL₃ central quotient has parameter three or five. -/
theorem SourceHypothesis.original_selectedComponent_oddLinearThree_quotient_parameter
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL
      ((Nonabelian.Setup.star H c.K) ⧸ center (Nonabelian.Setup.star H c.K)) 3 p) :
    p = 3 ∨ p = 5 := by
  by_cases hp3 : p = 3
  · exact Or.inl hp3
  obtain ⟨F,hFfield,hFfinite,hF,⟨eQ⟩⟩ := hm
  let := hFfield
  let := hFfinite
  let B := Nonabelian.Setup.star H c.K
  let := c.component.2
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  have hl : 3 < p := by
    have h2 := hp.two_le
    have hodd := Nat.odd_iff.mp ho
    omega
  let U := (V.subgroupOf c.localActor).map a.action
  have hU : Nat.card U = 2 := a.module_card
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hU])
  have hto : orderOf (t : MulAut B) = 2 :=
    (orderOf_injective U.subtype U.subtype_injective t).trans ht
  obtain ⟨P,hP⟩ := S.original_action_module_fixes_component_sylow D hZ z hz hTV hTz hbound hH hn c a
  obtain ⟨x,hx,hi⟩ := Matrix.PSL3.sylow_fixer_inverts_prime_of_fixes_center hp ho hl hF eQ
    t hto P (hP t t.property)
    (S.original_action_component_center_fixed D hZ z hz hTV hTz hbound hH hn c a t t.property)
  obtain ⟨v,hv,he⟩ := t.property
  let u := QuotientGroup.mk' (pCore 2 H) (inclusion a.local_le v)
  have hu : u ∈ Nonabelian.Setup.star H V := mem_map_of_mem _ hv
  have hxorder : orderOf (x : Nonabelian.Setup.Hstar H) = p := (Subgroup.orderOf_coe x).trans hx
  have hxne : (x : Nonabelian.Setup.Hstar H) ≠ 1 := by
    intro hh
    rw [hh,orderOf_one] at hxorder
    exact hp.ne_one hxorder.symm
  have hinv : u * x.val * u⁻¹ = x.val⁻¹ := by
    rw [←a.conjugation v x,he]
    exact congrArg Subtype.val hi
  rcases S.original_star_inverted_odd_order D hZ z hz hTV hTz hbound hns hH u hu x.val hxne
    (hxorder.symm ▸ ho) hinv with h3|h5
  · exact Or.inl (hxorder.symm.trans h3)
  · exact Or.inr (hxorder.symm.trans h5)

/-- The scalar-center formula excludes every odd-prime linear cubic cover. -/
theorem SourceHypothesis.original_selectedComponent_not_oddLinearThreeCover
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hcard : Nat.card (center (Nonabelian.Setup.star H c.K)) = 3)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    ¬ Chapter1.Section02.LocalModels.IsSL (Nonabelian.Setup.star H c.K) 3 p := by
  rintro ⟨F,hFfield,hFfinite,hF,⟨e⟩⟩
  let := hFfield
  let := hFfinite
  let B := Nonabelian.Setup.star H c.K
  let := c.component.2
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  have hscalar : Nat.gcd 3 (p - 1) = 3 := by
    have hc := (Nat.card_congr (centerCongr e).toEquiv).symm.trans hcard
    simpa only [Atlas.ExceptionalSupport.card_sl_center,Fintype.card_fin,hF] using hc
  let eQ : (B ⧸ center B) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F :=
    QuotientGroup.congr _ _ e (by
      apply le_antisymm
      · rintro _ ⟨x,hx,rfl⟩
        exact (centerCongr e ⟨x,hx⟩).property
      · intro y hy
        exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)
  rcases S.original_selectedComponent_oddLinearThree_quotient_parameter D hZ z hz hTV hTz hbound hns
    hH hn c a hp ho ⟨F,hFfield,hFfinite,hF,⟨eQ⟩⟩ with rfl|rfl <;> norm_num at hscalar

/-- The original A.3.6 cover alternatives after eliminating odd-prime SL₃. -/
theorem SourceHypothesis.original_selectedComponent_simple_or_reduced_classical_cover
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking) :
    let B := Nonabelian.Setup.star H c.K
    IsSimpleGroup B ∨
      (Nonempty (center B ≃* Multiplicative (ZMod 3)) ∧
        ((∃ f : ℕ, 1 ≤ f ∧ (2 ^ f) % 3 = 1 ∧
          Chapter1.Section02.LocalModels.IsSL B 3 (2 ^ f)) ∨
        (∃ q : ℕ, Chapter1.Section02.LocalModels.CoverParameter true q ∧
          Chapter1.Section02.LocalModels.IsSU B 3 q) ∨
        Chapter1.Section02.LocalModels.IsAlternatingCover B 7 ∨
        Chapter1.Section02.LocalModels.IsM22Cover B)) := by
  rcases S.original_selectedComponent_simple_or_remaining_cover D hZ z hz hTV hTz hbound hH hn c a
    with hs|⟨hc,hm⟩
  · exact Or.inl hs
  · right
    refine ⟨hc,?_⟩
    rcases hm with ⟨unitary,q,hq,he⟩|hm
    · cases unitary with
      | false =>
          rcases hq with ⟨f,hf,rfl,hmod⟩|⟨hp,ho⟩
          · exact Or.inl ⟨f,hf,hmod,he⟩
          · obtain ⟨ec⟩ := hc
            have hcard : Nat.card (center (Nonabelian.Setup.star H c.K)) = 3 := by
              rw [Nat.card_congr ec.toEquiv]
              simp
            exact (S.original_selectedComponent_not_oddLinearThreeCover D hZ z hz hTV hTz hbound
              hns hH hn c a hcard hp ho he).elim
      | true => exact Or.inr (Or.inl ⟨q,hq,he⟩)
    · exact Or.inr (Or.inr hm)

/-- The same selected component retains condition (*), rank alternatives and
all previous alternating exclusions, with the sharpened classical cover list. -/
theorem SourceHypothesis.original_selectedComponent_without_oddLinearCovers
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H)) :
    ∃ c : (D.fullSetup hZ T z).SelectedComponent H, ∃ a : c.ActionMarking,
      let A := (((D.fullSetup hZ T z).L₁.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
      let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
      let C := centralizer (U : Set a.action.range)
      (Nat.card U = 2 ∧ 3 ∣ Nat.card A ∧
        A.subgroupOf C ≤ (pCore 3 (C ⧸ pCore 2 C)).comap (QuotientGroup.mk' (pCore 2 C)) ∧
        ∃ R : Sylow 2 a.action.range, U ≤ (R : Subgroup a.action.range) ∧
          U ≤ centralizer (R : Set a.action.range)) ∧
      (primeRank 3 c.K = 1 ∨ (primeRank 3 c.K = 2 ∧
        ∀ P : Sylow 3 (D.fullSetup hZ T z).L₁,
          Function.Injective (a.residualSylowAction P) ∨
            (Nonempty (center (Nonabelian.Setup.star H c.K) ≃* Multiplicative (ZMod 3)) ∧
              Chapter1.Section02.LocalModels.ThreeCoverModel (Nonabelian.Setup.star H c.K)))) ∧
      (∀ n : ℕ, 6 ≤ n → n ≤ 8 →
        ¬ Chapter1.Section02.LocalModels.IsAlternating (Nonabelian.Setup.star H c.K) n) ∧
      ¬ Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 6 ∧
      (Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 7 →
        ∀ P : Sylow 3 (D.fullSetup hZ T z).L₁, Nat.card (a.residualSylowAction P).ker = 3) ∧
      (let B := Nonabelian.Setup.star H c.K
       IsSimpleGroup B ∨
         (Nonempty (center B ≃* Multiplicative (ZMod 3)) ∧
           ((∃ f : ℕ, 1 ≤ f ∧ (2 ^ f) % 3 = 1 ∧
             Chapter1.Section02.LocalModels.IsSL B 3 (2 ^ f)) ∨
           (∃ q : ℕ, Chapter1.Section02.LocalModels.CoverParameter true q ∧
             Chapter1.Section02.LocalModels.IsSU B 3 q) ∨
           Chapter1.Section02.LocalModels.IsAlternatingCover B 7 ∨
           Chapter1.Section02.LocalModels.IsM22Cover B))) := by
  obtain ⟨c,a,hc,hr,hAlt,h6,h7⟩ :=
    S.original_selectedComponent_without_alternating_rank_two D hZ z hz hTV hTz hbound hns hH hn
  exact ⟨c,a,hc,hr,hAlt,h6,h7,
    S.original_selectedComponent_simple_or_reduced_classical_cover D hZ z hz hTV hTz hbound hns hH hn c a⟩

end CFSG.Quasithin.Chapter12.Section06
