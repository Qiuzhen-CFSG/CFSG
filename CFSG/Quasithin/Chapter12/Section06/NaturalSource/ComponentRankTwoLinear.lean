module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankTwoCore
public import Theory.SpecificGroups.PSL3.SmallPrimeSylowCentralizers
public import Theory.SpecificGroups.SL2.PrimeFieldOddSubgroups
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360

/-!
# Excluding odd linear models on the original rank-two component

The original inverted-odd-order bound restricts the prime field to three
or five. The same V-hat involution fixes a Sylow two-subgroup of K-star.
The model calculation bounds its full automorphism centralizer by an
order indivisible by nine, whereas the original Sylow E₉ of L₁ embeds
faithfully in that very centralizer. This excludes both surviving fields
and hence the entire odd-prime linear-three row in the rank-two branch.

The linear-two rows have cyclic cubic Sylows, except PSL₂(9). Its actual
field-uniform equivalence with A₆ invokes the preceding original A₆
exclusion. Thus all linear rows of the odd-characteristic Theorem C
alternative are excluded on this component.

The TI and nonsingular-centralizer hypotheses retain their earlier source
owners. Other simple rows, the rank-one branch, 12.6.26--34 and universal
NaturalReduction remain obligations.
Source: Aschbacher–Smith, proof of 12.6.26, printed p.832.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)

include hz hTV hTz hbound hH hn a in
/-- Eliminate the original rank-two component with odd-prime linear-three model. -/
theorem SourceHypothesis.original_rank_two_not_oddLinearThree
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    ¬ ClassicalGroup.IsPSL (Nonabelian.Setup.star H c.K) 3 p := by
  classical
  rintro ⟨F,hFfield,hFfinite,hF,⟨e⟩⟩
  let := hFfield
  let := hFfinite
  let B := Nonabelian.Setup.star H c.K
  let : IsSimpleGroup B := S.original_selectedComponent_simple D hZ z hz hTV hTz
    hbound hH hn c a hTI hns
  let := c.component.2
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) := e.symm.isSimpleGroup
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hcenter : center B = ⊥ := center_eq_bot_of_simple_perfect
  let e₀ : (B ⧸ center B) ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  have hsmall : Nat.card F = 3 ∨ Nat.card F = 5 := by
    rcases S.original_selectedComponent_oddLinearThree_quotient_parameter D hZ z hz hTV hTz
      hbound hns hH hn c a hp ho ⟨F,hFfield,hFfinite,hF,⟨e₀.trans e⟩⟩ with hp|hp
    · exact Or.inl (hF.trans hp)
    · exact Or.inr (hF.trans hp)
  let U := (V.subgroupOf c.localActor).map a.action
  have hU : Nat.card U = 2 := a.module_card
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hU])
  let α := MulAut.congr e (t : MulAut B)
  have hα : orderOf α = 2 := ((MulAut.congr e).orderOf_eq _).trans
    ((orderOf_injective U.subtype U.subtype_injective t).trans ht)
  obtain ⟨R,hR⟩ := S.original_action_module_fixes_component_sylow D hZ z hz hTV hTz
    hbound hH hn c a
  let Q := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : ∀ x ∈ Q, α x = x := by
    rintro _ ⟨x,hx,rfl⟩
    change e ((t : MulAut B) (e.symm (e x))) = e x
    rw [e.symm_apply_apply,hR t t.property x hx]
  let P : Sylow 3 (D.fullSetup hZ T z).L₁ := default
  have hPc := (S.original_point_residual_sylow D hZ z hz hTz P).2
  let f := (MulAut.congr e).toMonoidHom.comp (a.residualSylowAction P)
  have hf : Function.Injective f := (MulAut.congr e).injective.comp
    (S.original_rank_two_sylow_faithful D hZ z hz hTV hTz hbound hH hn c a hTI hns hr P)
  let g : P →* centralizer ({α} : Set (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))) :=
    f.codRestrict _ (by
      intro x
      apply mem_centralizer_singleton_iff.mpr
      have hAX : (D.fullSetup hZ T z).L₁ ≤ c.localActor := le_sup_right.trans le_sup_left
      have hx : a.residualSylowAction P x ∈
          ((D.fullSetup hZ T z).L₁.subgroupOf c.localActor).map a.action :=
        ⟨⟨x.val.val,hAX x.val.property⟩,x.val.property,rfl⟩
      have hcomm := (a.residual_centralizes hx t t.property).symm
      change MulAut.congr e (a.residualSylowAction P x) * MulAut.congr e t =
        MulAut.congr e t * MulAut.congr e (a.residualSylowAction P x)
      simpa only [map_mul] using congrArg (MulAut.congr e) hcomm)
  have hg : Function.Injective g := fun x y he => hf (congrArg Subtype.val he)
  apply Matrix.PSL3.SmallPrimeSylowCentralizers.not_nine_dvd_sylow_fixer_centralizer
    hsmall Q α hα hQ
  rw [←hPc]
  exact card_dvd_of_injective g hg
include hz hTz hH a in
/-- The rank-two linear-two row reduces to PSL₂(9), already excluded as the same A₆ component. -/
theorem SourceHypothesis.original_rank_two_not_smallDegreeLinearTwo
    (hr : primeRank 3 c.K = 2) {p n : ℕ} (hp : p.Prime) (hn2 : n ≤ 2) :
    ¬ ClassicalGroup.IsPSL (Nonabelian.Setup.star H c.K) 2 (p^n) := by
  classical
  rintro ⟨F,hFfield,hFfinite,hF,⟨e⟩⟩
  let := hFfield
  let := hFfinite
  let := Fintype.ofFinite F
  let : Fact p.Prime := ⟨hp⟩
  have hn0 : n ≠ 0 := by
    intro he
    have hlt := Finite.one_lt_card (α := F)
    rw [hF,he,pow_zero] at hlt
    omega
  have hrB : primeRank 3 (Nonabelian.Setup.star H c.K) = 2 :=
    c.three_rank_eq_star.symm.trans hr
  rw [primeRank_equiv 3 e] at hrB
  by_cases hn1 : n = 1
  · have hFp : Nat.card F = p := by simpa only [hn1,pow_one] using hF
    let eF : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hFp)
    let P : Sylow 3 (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := default
    have hcyc : IsCyclic P := Matrix.SpecialLinearGroup.isCyclic_of_odd_pGroup_injective_primeField
      P.isPGroup' (by decide : 3 ≠ 2)
      (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))).subtype Subtype.val_injective
    have hlow := P.primeRank_quotient_le_one hcyc
      (center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
    rw [primeRank_equiv 3 (Atlas.fieldEquivPSL 2 eF)] at hrB
    change primeRank 3 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) ≤ 1 at hlow
    omega
  · have hn : n = 2 := by omega
    by_cases hp3 : p = 3
    · have hF9 : Nat.card F = 9 := by simpa only [hp3,hn,Nat.reducePow] using hF
      exact S.original_selectedComponent_not_alternatingSix D hZ z hz hTz hH c a
        ⟨e.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hF9)⟩
    · let : CharP F p := charP_of_card_eq_prime_pow (p := p) (f := n)
        (by simpa only [Nat.card_eq_fintype_card] using hF)
      let P : Sylow 3 (Matrix.SpecialLinearGroup (Fin 2) F) := default
      have hcyc : IsCyclic P := Matrix.SpecialLinearGroup.isCyclic_of_odd_pGroup_injective_of_ne_char
        (r := p) P.isPGroup' (by decide : 3 ≠ 2) (Ne.symm hp3)
        (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).subtype Subtype.val_injective
      have hlow := P.primeRank_quotient_le_one hcyc
        (center (Matrix.SpecialLinearGroup (Fin 2) F))
      change primeRank 3 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ≤ 1 at hlow
      omega
end CFSG.Quasithin.Chapter12.Section06
