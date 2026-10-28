module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankOneModels
public import Theory.GroupAction.InnerCentralizerRadical
public import Theory.SpecificGroups.PSL3.QuinticSylowFixerRadical

/-!
# Completing the original rank-one model inspection

For PSL3(5), the original Sylow-fixing module involution is inner. Its
fixed group is the actual GL2(5), whose radical is a two-group. The outer
automorphism quotient is a two-group as well, so the exact centralizer
inside the original X-hat has two-group radical. This contradicts the
cubic divisor forced by condition (*). Thus only odd-field PSL2 remains.

The parameter congruence is handled in the subsequent extension; the
faithful binary-section contradiction and abelian point span remain open. All original
point, quotient, action and earlier geometry hypotheses remain explicit.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.833.
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
private theorem original_model_radical_contradiction
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {B : Type*} [Group B] [Finite B] (e : Nonabelian.Setup.star H c.K ≃* B)
    (ho : IsPGroup 2 (MulAut.Outer B))
    (hf : ∀ (P : Sylow 2 B) (b : MulAut B), orderOf b = 2 →
      (∀ x ∈ P, b x = x) → IsPGroup 2 (solvableRadical b.fixedSubgroup)) : False := by
  let K := Nonabelian.Setup.star H c.K
  let : IsSimpleGroup K := S.original_selectedComponent_simple D hZ z hz hTV hTz
    hbound hH hn c a hTI hns
  let := c.component.2
  have hzK : center K = ⊥ := center_eq_bot_of_simple_perfect
  obtain ⟨b,hb,hoB,⟨P,hP⟩,_⟩ := S.original_selectedComponent_model_fixed_cubic
    D hZ z hz hTV hTz hbound hH hn c a hTI hns e
  let t : a.action.range := ⟨b,(map_le_range _ _) hb⟩
  let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
  have hU : Nat.card U = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (map_le_range _ _)).toEquiv]
    exact a.module_card
  have ht : orderOf t = 2 := (Subgroup.orderOf_coe t).symm.trans
    (((MulAut.congr e).orderOf_eq b).symm.trans hoB)
  have hgen : zpowers t = U :=
    eq_of_le_of_card_ge (zpowers_le.mpr hb) (by rw [Nat.card_zpowers,ht,hU])
  have hC : centralizer (U : Set a.action.range) = centralizer ({t} : Set a.action.range) := by
    rw [←hgen,zpowers_eq_closure,centralizer_closure]
  let j := MulAut.fixedSubgroupCongr e b
  let jR := (j.subgroupMap (solvableRadical b.fixedSubgroup)).trans
    (MulEquiv.subgroupCongr (map_solvableRadical_equiv j))
  have hfixed := (hf P (MulAut.congr e b) hoB hP).of_equiv jR.symm
  have hinner : MulAut.innerSubgroup K ≤ a.action.range := by
    rw [←a.component_image]
    exact map_le_range _ _
  have htwo := MulAut.centralizer_radical_isTwoGroup_of_fixed hzK
    (ho.of_equiv (MulAut.outerCongr e).symm) a.action.range hinner t hfixed
  have hd := S.original_action_centralizer_radical_three_dvd D hZ z hz hTV hTz
    hbound hH hn c a
  change 3 ∣ Nat.card (solvableRadical (centralizer (U : Set a.action.range))) at hd
  rw [hC] at hd
  obtain ⟨k,hk⟩ := htwo.exists_card_eq
  rw [hk] at hd
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

include hz hTV hTz hbound hH hn a in
/-- The literal condition (*) excludes the final PSL3(5) row. -/
theorem SourceHypothesis.original_selectedComponent_not_linearThreeFive
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    ¬ ClassicalGroup.IsPSL (Nonabelian.Setup.star H c.K) 3 5 := by
  rintro ⟨F,hfield,hfinite,hF,⟨e⟩⟩
  let := hfield
  let := hfinite
  let B := Nonabelian.Setup.star H c.K
  let : IsSimpleGroup B := S.original_selectedComponent_simple D hZ z hz hTV hTz
    hbound hH hn c a hTI hns
  let := c.component.2
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) := e.symm.isSimpleGroup
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact original_model_radical_contradiction S D hZ z hz hTV hTz hbound hH hn c a hTI hns e
    (IsPGroup.of_card_dvd_pow (n := 1) (by simpa only [pow_one] using
      Matrix.PSL3.SmallPrimeSylowCentralizers.outer_card_dvd_two (Or.inr hF)))
    (Matrix.PSL3.SmallPrimeSylowCentralizers.quintic_sylow_fixer_radical_two hF)

include hz hTV hTz hbound hH hn a in
/-- The original selected simple component is an actual odd-field PSL2 model. -/
theorem SourceHypothesis.original_selectedComponent_oddLinearTwo
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    ∃ p n : ℕ, p.Prime ∧ Odd p ∧ n ≤ 2 ∧
      ClassicalGroup.IsPSL (Nonabelian.Setup.star H c.K) 2 (p^n) := by
  rcases S.original_rank_one_linear_models D hZ z hz hTV hTz hbound hH hn c a hTI hns with h | h
  · exact h
  · exact (S.original_selectedComponent_not_linearThreeFive D hZ z hz hTV hTz
      hbound hH hn c a hTI hns h).elim

end CFSG.Quasithin.Chapter12.Section06
