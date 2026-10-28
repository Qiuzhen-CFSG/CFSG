module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentUnitaryOdd
public import Theory.SpecificGroups.SU3.BinarySylowInverter
public import Theory.SpecificGroups.SU3.FixedFieldTwo
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.NumberTheory.BinaryMersenneSmallPrimeSupport
/-!
# Binary unitary covers are excluded at the original selected component

The marked V-action fixes a Sylow two-subgroup and the full center of
K-star. On a binary PSU₃ central quotient it therefore inverts an element
of every prime order dividing 2ⁿ−1. The original odd-order restriction
leaves only primes three and five, forcing n=2 or n=4. Neither degree
satisfies the cubic-unitary-cover congruence 2ⁿ ≡ 2 mod 3. The endpoint
SU₃(2) is excluded separately by the solvability of its actual projective
image and the inherited perfectness.

Together with the odd-prime unitary exclusions this removes all SU₃
covers from the original catalogue. The selected-component constructor
retains condition (*), rank alternatives and earlier alternating
exclusions. All original earlier-geometry hypotheses remain explicit.
Binary SL₃, cubic A₇/M₂₂, the remaining rank cases, 12.6.26--34 and the
universal natural reduction remain obligations.

Source: Aschbacher--Smith, proof of 12.6.26, printed pp.832--833.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The original binary PSU₃ central quotient has degree two or four. -/
theorem SourceHypothesis.original_selectedComponent_binaryUnitary_quotient_degree
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn0 : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU
      ((Nonabelian.Setup.star H c.K) ⧸ center (Nonabelian.Setup.star H c.K)) 3 (2^n)) :
    n = 2 ∨ n = 4 := by
  obtain ⟨F,hFfield,hFfinite,J,hF,hconj,⟨eQ⟩⟩ := hm
  let := hFfield
  let := hFfinite
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2) (by
    simpa [Nat.card_eq_fintype_card,pow_mul] using hF)
  let B := Nonabelian.Setup.star H c.K
  let := c.component.2
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let U := (V.subgroupOf c.localActor).map a.action
  have hU : Nat.card U = 2 := a.module_card
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hU])
  have hto : orderOf (t : MulAut B) = 2 :=
    (orderOf_injective U.subtype U.subtype_injective t).trans ht
  obtain ⟨P,hP⟩ := S.original_action_module_fixes_component_sylow D hZ z hz hTV hTz hbound hH hn0 c a
  apply Nat.two_pow_sub_one_small_prime_support hn
  intro p hp hd
  have ho : Odd p := hp.odd_of_ne_two (by
    intro he
    subst p
    have hpar : Odd (2^n-1) := by
      have he : Even ((2:ℕ)^n) := even_two.pow_of_ne_zero (by omega)
      have hpos : 0 < (2:ℕ)^n := pow_pos (by decide) _
      exact Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)
    exact hpar.not_two_dvd_nat hd)
  obtain ⟨x,hx,hi⟩ := HermitianForm.BinarySylowInverter.sylow_fixer_inverts_split_prime_of_fixes_center
    J hn hF hconj eQ t hto P (hP t t.property)
    (S.original_action_component_center_fixed D hZ z hz hTV hTz hbound hH hn0 c a t t.property)
    hp ho hd
  obtain ⟨v,hv,he⟩ := t.property
  let u := QuotientGroup.mk' (pCore 2 H) (inclusion a.local_le v)
  have hu : u ∈ Nonabelian.Setup.star H V := mem_map_of_mem _ hv
  have hxorder : orderOf (x : Nonabelian.Setup.Hstar H) = p := (Subgroup.orderOf_coe x).trans hx
  have hxne : (x : Nonabelian.Setup.Hstar H) ≠ 1 := by
    intro hh
    rw [hh,orderOf_one] at hxorder
    exact hp.ne_one hxorder.symm
  have hinv : u*x.val*u⁻¹=x.val⁻¹ := by
    rw [←a.conjugation v x,he]
    exact congrArg Subtype.val hi
  rcases S.original_star_inverted_odd_order D hZ z hz hTV hTz hbound hns hH u hu x.val hxne
    (hxorder.symm ▸ ho) hinv with h3|h5
  · exact Or.inl (hxorder.symm.trans h3)
  · exact Or.inr (hxorder.symm.trans h5)

/-- Every binary SU₃ cubic-cover parameter is excluded on the original marked component. -/
theorem SourceHypothesis.original_selectedComponent_not_binaryUnitaryCover
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn0 : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    {n : ℕ} (hn : 1 ≤ n) (hmod : (2^n)%3=2) :
    ¬ Chapter1.Section02.LocalModels.IsSU (Nonabelian.Setup.star H c.K) 3 (2^n) := by
  rintro ⟨F,hFfield,hFfinite,J,hF,hconj,⟨e⟩⟩
  let := hFfield
  let := hFfinite
  let B := Nonabelian.Setup.star H c.K
  let := c.component.2
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Group.IsPerfect.ofSurjective (f := J.specialToProjective.comp e.toMonoidHom)
      (J.specialToProjective_surjective.comp e.surjective)
  have hn2 : 2 ≤ n := by
    by_contra! hn2
    have hn1 : n=1 := by omega
    have hF4 : Nat.card F = 2^2 := by simpa [hn1] using hF
    have hc2 : ∀ x, J.conj x=x^2 := by simpa [hn1] using hconj
    have hcard := HermitianForm.FixedFieldTwo.card_projective J hF4 hc2
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
    let : Nontrivial (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
    exact Group.IsPerfect.not_isSolvable _ (HermitianForm.FixedFieldTwo.projective_isSolvable J hF4 hc2)
  have hzc := HermitianForm.EvenProjectiveComparison.center_eq_bot J (by omega) hF hconj
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
  have hmQ : ClassicalGroup.IsPSU (B ⧸ center B) 3 (2^n) :=
    ⟨F,hFfield,hFfinite,J,hF,hconj,⟨eqc.trans eqp⟩⟩
  rcases S.original_selectedComponent_binaryUnitary_quotient_degree D hZ z hz hTV hTz hbound hns
    hH hn0 c a hn2 hmQ with rfl|rfl <;> norm_num at hmod

/-- The original non-simple catalogue now has only binary linear and the two remaining sporadic/alternating covers. -/
theorem SourceHypothesis.original_selectedComponent_simple_or_linear_cover
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
        ((∃ f : ℕ, 1 ≤ f ∧ (2^f)%3=1 ∧
          Chapter1.Section02.LocalModels.IsSL B 3 (2^f)) ∨
        Chapter1.Section02.LocalModels.IsAlternatingCover B 7 ∨
        Chapter1.Section02.LocalModels.IsM22Cover B)) := by
  rcases S.original_selectedComponent_simple_or_binary_classical_cover D hZ z hz hTV hTz hbound hns
    hH hn c a with hs|⟨hc,hl|hu|hr⟩
  · exact Or.inl hs
  · exact Or.inr ⟨hc,Or.inl hl⟩
  · obtain ⟨f,hf,hmod,hm⟩ := hu
    exact (S.original_selectedComponent_not_binaryUnitaryCover D hZ z hz hTV hTz hbound hns
      hH hn c a hf hmod hm).elim
  · exact Or.inr ⟨hc,Or.inr hr⟩

/-- The same selected component retains condition (*), rank alternatives and
all previous alternating exclusions, with every unitary cubic cover excluded. -/
theorem SourceHypothesis.original_selectedComponent_without_unitaryCovers
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
           Chapter1.Section02.LocalModels.IsAlternatingCover B 7 ∨
           Chapter1.Section02.LocalModels.IsM22Cover B))) := by
  obtain ⟨c,a,hc,hr,hAlt,h6,h7⟩ :=
    S.original_selectedComponent_without_alternating_rank_two D hZ z hz hTV hTz hbound hns hH hn
  exact ⟨c,a,hc,hr,hAlt,h6,h7,
    S.original_selectedComponent_simple_or_linear_cover D hZ z hz hTV hTz hbound hns hH hn c a⟩


end CFSG.Quasithin.Chapter12.Section06
