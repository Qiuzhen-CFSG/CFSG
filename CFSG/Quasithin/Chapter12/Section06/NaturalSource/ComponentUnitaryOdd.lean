module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentLinearOdd
public import Theory.SpecificGroups.PSU3.SylowFixedInvertedRoot
public import Theory.SpecificGroups.SU3.QuinticSylowFixer
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.SpecificGroups.SU3.PrimeOrderDivisibility

/-!
# Original odd-prime unitary component exclusions

The original marked involution fixes a Sylow two-subgroup of K-star and
its whole center. The inverted defining-prime root therefore restricts
an odd-prime PSU₃ quotient to parameters three and five. The literal
special-to-projective scalar map excludes SU₃(3) with cubic center.

In SU₃(5), the same involution moves an actual extraspecial exponent-five
root group of order 125. Its displacement on the original faithful binary
section U_H/V₁ is at least eight, contradicting the original upper bound
four. Consequently no odd-prime SU₃ cubic cover occurs. Combining the
preceding SL₃ exclusions leaves only the binary classical covers and
the cubic A₇ and M₂₂ covers, with condition (*), rank alternatives and
all earlier exclusions on the same selected component and action.

All original earlier-geometry hypotheses remain explicit. The remaining
component cases, abelian point span, later 12.6.27--34 and the universal
natural reduction are still obligations. Source: Aschbacher--Smith,
proof of 12.6.26, printed pp.832--833.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The actual odd-prime PSU₃ central quotient has parameter three or five. -/
theorem SourceHypothesis.original_selectedComponent_oddUnitaryThree_quotient_parameter
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
    (hm : ClassicalGroup.IsPSU
      ((Nonabelian.Setup.star H c.K) ⧸ center (Nonabelian.Setup.star H c.K)) 3 p) :
    p = 3 ∨ p = 5 := by
  obtain ⟨F,hFfield,hFfinite,J,hF,hconj,⟨eQ⟩⟩ := hm
  let := hFfield
  let := hFfinite
  let B := Nonabelian.Setup.star H c.K
  let := c.component.2
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let U := (V.subgroupOf c.localActor).map a.action
  have hU : Nat.card U = 2 := a.module_card
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hU])
  have hto : orderOf (t : MulAut B) = 2 :=
    (orderOf_injective U.subtype U.subtype_injective t).trans ht
  obtain ⟨P,hP⟩ := S.original_action_module_fixes_component_sylow D hZ z hz hTV hTz hbound hH hn c a
  obtain ⟨x,hx,hi⟩ := BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.sylow_fixer_inverts_prime_of_fixes_center
    J hp ho hF hconj eQ
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

/-- A cubic odd-prime SU₃ component can only have fixed-field order five. -/
theorem SourceHypothesis.original_selectedComponent_oddUnitaryThreeCover_parameter
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
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : Chapter1.Section02.LocalModels.IsSU (Nonabelian.Setup.star H c.K) 3 p) :
    p = 5 := by
  obtain ⟨F,hFfield,hFfinite,J,hF,hconj,⟨e⟩⟩ := hm
  let := hFfield
  let := hFfinite
  let : Fact p.Prime := ⟨hp⟩
  let B := Nonabelian.Setup.star H c.K
  let := c.component.2
  have hp2 : 2 < p := by
    have := hp.two_le
    have := Nat.odd_iff.mp ho
    omega
  have hfixed : Nat.card {x : F // J.conj x = x} = p := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1
      (by decide) (by simpa using hF) (by simpa using hconj)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J p hp2 hF hfixed
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Group.IsPerfect.ofSurjective (f := J.specialToProjective.comp e.toMonoidHom)
      (J.specialToProjective_surjective.comp e.surjective)
  have hzc : center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
    rcases (inferInstance : (center (ProjectiveSpecialUnitaryMatrixGroup J)).Normal).eq_bot_or_eq_top with hc|hc
    · exact hc
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hc)).elim
  let eqc : (B ⧸ center B) ≃* (J.specialSubgroup ⧸ center J.specialSubgroup) :=
    QuotientGroup.congr _ _ e (by
      apply le_antisymm
      · rintro _ ⟨x,hx,rfl⟩
        exact (centerCongr e ⟨x,hx⟩).property
      · intro y hy
        exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)
  let eqp : (J.specialSubgroup ⧸ center J.specialSubgroup) ≃*
      ProjectiveSpecialUnitaryMatrixGroup J :=
    (QuotientGroup.quotientMulEquivOfEq (J.specialToProjective_ker_eq_center hzc).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective J.specialToProjective_surjective)
  have hmQ : ClassicalGroup.IsPSU (B ⧸ center B) 3 p :=
    ⟨F,hFfield,hFfinite,J,hF,hconj,⟨eqc.trans eqp⟩⟩
  rcases S.original_selectedComponent_oddUnitaryThree_quotient_parameter D hZ z hz hTV hTz hbound hns
    hH hn c a hp ho hmQ with hp3|hp5
  · have hF9 : Nat.card F = 9 := by simpa [hp3] using hF
    have hk : J.specialToProjective.ker = ⊥ := J.specialToProjective.ker_eq_bot_iff.mpr
      (J.specialToProjective_injective_of_card_nine hF9)
    have hb : center J.specialSubgroup = ⊥ := (J.specialToProjective_ker_eq_center hzc).symm.trans hk
    have hc : Nat.card (center J.specialSubgroup) = 3 :=
      (Nat.card_congr (centerCongr e).toEquiv).symm.trans hcard
    rw [hb] at hc
    norm_num at hc
  · exact hp5
/-- The original rank-four section excludes SU₃(5): the same marked
involution would displace at least eight dimensions on that section. -/
theorem SourceHypothesis.original_selectedComponent_not_unitaryThreeFive
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking) :
    ¬ Chapter1.Section02.LocalModels.IsSU (Nonabelian.Setup.star H c.K) 3 5 := by
  rintro ⟨F,hFfield,hFfinite,J,hF,hconj,⟨e⟩⟩
  let := hFfield
  let := hFfinite
  let B := Nonabelian.Setup.star H c.K
  let U := (V.subgroupOf c.localActor).map a.action
  have hU : Nat.card U = 2 := a.module_card
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hU])
  have hto : orderOf (t : MulAut B) = 2 :=
    (orderOf_injective U.subtype U.subtype_injective t).trans ht
  obtain ⟨P,hP⟩ := S.original_action_module_fixes_component_sylow D hZ z hz hTV hTz hbound hH hn c a
  let α := MulAut.congr e (t : MulAut B)
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hα : orderOf α = 2 := ((MulAut.congr e).orderOf_eq _).trans hto
  have hQ : ∀ x ∈ Q, α x = x := by
    rintro _ ⟨x,hx,rfl⟩
    change e ((t : MulAut B) (e.symm (e x))) = e x
    rw [e.symm_apply_apply,hP t t.property x hx]
  obtain ⟨v,hv,he⟩ := t.property
  let u := QuotientGroup.mk' (pCore 2 H) (inclusion a.local_le v)
  have hu : u ∈ Nonabelian.Setup.star H V := mem_map_of_mem _ hv
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  let := h.point_normal_in_UH
  let := h.point_quotient_elementary
  obtain ⟨σ,f,hσ,_⟩ := h.faithful_point_quotient
  have hr := S.original_binary_displacement_bound D hZ z hz hTV hTz hbound hH hn σ f
  let j := B.subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := B.subtype_injective.comp e.symm.injective
  have heq (x : J.specialSubgroup) : j (α x) = u * j x * u⁻¹ := by
    change (e.symm (e ((t : MulAut B) (e.symm x)))).val = _
    rw [e.symm_apply_apply,←he]
    exact a.conjugation v (e.symm x)
  have hl := HermitianForm.QuinticSylowFixer.eight_le_displacement_of_sylow_fixer
    J hF hconj σ hσ j hj u α hα Q hQ heq
  have hupp := hr u hu
  omega

/-- Every odd-prime SU₃ cubic cover is excluded on the original marked component. -/
theorem SourceHypothesis.original_selectedComponent_not_oddUnitaryThreeCover
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
    ¬ Chapter1.Section02.LocalModels.IsSU (Nonabelian.Setup.star H c.K) 3 p := by
  intro hm
  have he := S.original_selectedComponent_oddUnitaryThreeCover_parameter D hZ z hz hTV hTz hbound hns
    hH hn c a hcard hp ho hm
  exact S.original_selectedComponent_not_unitaryThreeFive D hZ z hz hTV hTz hbound hH hn c a (he ▸ hm)

/-- The original A.3.6 cover alternatives after eliminating both odd-prime classical covers. -/
theorem SourceHypothesis.original_selectedComponent_simple_or_binary_classical_cover
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
        (∃ f : ℕ, 1 ≤ f ∧ (2 ^ f) % 3 = 2 ∧
          Chapter1.Section02.LocalModels.IsSU B 3 (2 ^ f)) ∨
        Chapter1.Section02.LocalModels.IsAlternatingCover B 7 ∨
        Chapter1.Section02.LocalModels.IsM22Cover B)) := by
  rcases S.original_selectedComponent_simple_or_reduced_classical_cover D hZ z hz hTV hTz hbound hns
    hH hn c a with hs|⟨hc,hm⟩
  · exact Or.inl hs
  · refine Or.inr ⟨hc,?_⟩
    rcases hm with hl|⟨q,hq,he⟩|hrest
    · exact Or.inl hl
    · rcases hq with ⟨f,hf,rfl,hmod⟩|⟨hp,ho⟩
      · exact Or.inr (Or.inl ⟨f,hf,hmod,he⟩)
      · obtain ⟨ec⟩ := hc
        have hcard : Nat.card (center (Nonabelian.Setup.star H c.K)) = 3 := by
          rw [Nat.card_congr ec.toEquiv]
          simp
        exact (S.original_selectedComponent_not_oddUnitaryThreeCover D hZ z hz hTV hTz hbound hns
          hH hn c a hcard hp ho he).elim
    · exact Or.inr (Or.inr hrest)

/-- The same selected component retains condition (*), rank alternatives and
all previous alternating exclusions, with the binary classical cover list. -/
theorem SourceHypothesis.original_selectedComponent_without_oddClassicalCovers
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
           (∃ f : ℕ, 1 ≤ f ∧ (2 ^ f) % 3 = 2 ∧
             Chapter1.Section02.LocalModels.IsSU B 3 (2 ^ f)) ∨
           Chapter1.Section02.LocalModels.IsAlternatingCover B 7 ∨
           Chapter1.Section02.LocalModels.IsM22Cover B))) := by
  obtain ⟨c,a,hc,hr,hAlt,h6,h7⟩ :=
    S.original_selectedComponent_without_alternating_rank_two D hZ z hz hTV hTz hbound hns hH hn
  exact ⟨c,a,hc,hr,hAlt,h6,h7,
    S.original_selectedComponent_simple_or_binary_classical_cover D hZ z hz hTV hTz hbound hns hH hn c a⟩

end CFSG.Quasithin.Chapter12.Section06
