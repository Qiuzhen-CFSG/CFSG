module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.ResidualControl
public import Theory.GroupTheory.PResidual.FixedInnerAction
public import Theory.GroupTheory.SylowSubnormalIntersection
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.OddModels.LinearTwo
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeTwoGroup

/-!
# The large rank-one component in original plane uniqueness

For a Fermat or Mersenne prime p > 7, the component Sylow two-subgroups
are maximal. Subnormal Sylow restriction identifies Mc ∩ L with such a
Sylow group. The two-group outer quotient forces the original two-perfect
K to act internally, and its commutation with z puts its inner image in
C_L(z) = Mc ∩ L. Thus K centralizes L. The proved bound C_G(K) ≤ Mc
contradicts the selected component's escape.

The proof uses only the preceding source packet and the actual PSL₂ model.
It does not assume normality of L or the different Section15.3 local setup.
Source: Aschbacher--Smith, proof of15.2.15, printed p.1118,
refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 ChapterA.Section05To06 ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)
include d

/-- Maximal component Sylows make the actual Mc intersection a two-group. -/
theorem component_intersection_two_of_maximal_sylows
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hmax : ∀ Q : Sylow 2 c.component, IsCoatom (Q : Subgroup c.component)) :
    IsPGroup 2 ((Mc.subgroupOf I).subgroupOf c.component) := by
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_subnormal c.component c.isComponent.1
  have hQMc : (Q : Subgroup c.component) ≤ (Mc.subgroupOf I).subgroupOf c.component := by
    intro x hx
    have hxP : (x : I) ∈ P := by
      rw [hQ] at hx
      exact hx
    have hxS : ((x : I) : G) ∈ planeSylow T ZS := hP ▸ mem_map_of_mem I.subtype hxP
    exact ((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_left) hxS
  have hne : (Mc.subgroupOf I).subgroupOf c.component ≠ ⊤ := by
    intro ht
    apply c.escapes
    rintro x ⟨l,hl,rfl⟩
    exact (show (⟨l,hl⟩ : c.component) ∈ (Mc.subgroupOf I).subgroupOf c.component from
      ht ▸ mem_top _)
  exact Q.isPGroup'.to_le ((isCoatom_iff_ge_of_le.mp (hmax Q)).2 _ hne hQMc)

/-- A component with maximal Sylow two-subgroups and two-group outer quotient
cannot escape Mc: its original K action is trivial. -/
theorem not_component_of_maximal_sylows_and_outer_two
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (hcenter : center c.component = ⊥)
    (hmax : ∀ Q : Sylow 2 c.component, IsCoatom (Q : Subgroup c.component))
    (houter : IsPGroup 2 (MulAut.Outer c.component)) : False := by
  let K := (pResidual 2 H).map H.subtype
  have hKI : K ≤ I :=
    (le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  have hKL := component_residual_normalizes d hI c.isComponent
  let A := K.subgroupOf I
  have hAN : A ≤ normalizer (c.component : Set I) := by
    intro k hk
    apply mem_normalizer_iff.mpr
    intro x
    have hh := mem_normalizer_iff.mp (hKL hk) (x : G)
    have hmem (y : I) : (y : G) ∈ c.component.map I.subtype ↔ y ∈ c.component := by
      exact mem_map_iff_mem (f := I.subtype) I.subtype_injective
    rw [← hmem x, ← hmem (k * x * k⁻¹)]
    exact hh
  let f : A →* MulAut c.component := c.component.normalizerMonoidHom.comp (inclusion hAN)
  obtain ⟨a,ha,_⟩ := c.model
  have hfix : a.fixedSubgroup ≤ (Mc.subgroupOf I).subgroupOf c.component := by
    intro x hx
    change ((x : I) : G) ∈ Mc
    apply (marked_centralizer d hI hz hzne).2.le
    apply mem_centralizer_singleton_iff.mpr
    have he := ha x
    rw [(MulAut.mem_fixedSubgroup _ _).mp hx] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  have hpA : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 H).of_surjective
    (subgroupOfEquivOfLe hKI).symm.toMonoidHom (subgroupOfEquivOfLe hKI).symm.surjective
  have hcomm (k : A) : a * f k = f k * a := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change ((a (f k x) : I) : G) = (((f k) (a x) : I) : G)
    rw [ha]
    change z * (((k : I) : G) * ((x : I) : G) * ((k : I) : G)⁻¹) * z⁻¹ =
      ((k : I) : G) * ((a x : I) : G) * ((k : I) : G)⁻¹
    rw [ha]
    have hkMc : ((k : I) : G) ∈ Mc :=
      ((le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_left) k.property
    have hzk : z * ((k : I) : G) = ((k : I) : G) * z := by
      have hh := hkMc
      rw [← (marked_centralizer d hI hz hzne).2] at hh
      exact (mem_centralizer_singleton_iff.mp hh).symm
    calc
      _ = (z * ((k : I) : G)) * ((x : I) : G) * (z * ((k : I) : G))⁻¹ := by group
      _ = (((k : I) : G) * z) * ((x : I) : G) * (((k : I) : G) * z)⁻¹ := by rw [hzk]
      _ = _ := by group
  have hf := perfect_action_eq_one_of_fixed_and_outer_pGroups hpA hcenter houter a
    ((component_intersection_two_of_maximal_sylows d c hI hP hmax).to_le hfix) f hcomm
  have hLK : c.component.map I.subtype ≤ centralizer (K : Set G) := by
    rintro l ⟨x,hx,rfl⟩ k hk
    let ki : A := ⟨⟨k,hKI hk⟩,hk⟩
    have he := congrArg (fun b : MulAut c.component => ((b ⟨x,hx⟩ : I) : G))
      (DFunLike.congr_fun hf ki)
    change k * (x : G) * k⁻¹ = (x : G) at he
    exact mul_inv_eq_iff_eq_mul.mp he
  exact c.escapes (hLK.trans (residual_centralizer_le d))

open scoped MatrixGroups
open ClassificationModels

/-- The complete large PSL₂(p) branch on the actual source component. -/
theorem not_linear_two_component
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hlarge : 7 < p)
    (hm : ClassicalGroup.IsPSL c.component 2 p) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : IsQuasisimple c.component := c.isComponent.2
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup c.component := e.isSimpleGroup
  have hc : center c.component = ⊥ := by
    rcases (inferInstance : (center c.component).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · exact (Group.IsPerfect.not_isMulCommutative c.component (center_eq_top_iff.mp hc)).elim
  apply not_component_of_maximal_sylows_and_outer_two d c hI hP hz hzne hc
  · let : Fact p.Prime := ⟨hp.1⟩
    let : Fintype F := Fintype.ofFinite F
    let ef : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
    let eq := e.trans (Atlas.fieldEquivPSL 2 ef)
    obtain ⟨k,hk,hpk⟩ := RankOne.OddModels.adjacent_power_of_large_fermatMersenne hp hlarge
    intro Q
    exact (OrderIso.isCoatom_iff eq.mapSubgroup _).mp
      (Matrix.ProjectiveSpecialLinearGroup.sylow_two_isCoatom_of_adjacent_power hk hpk
        (Q.mapSurjective (f := eq.toMonoidHom) eq.surjective))
  · have ho := Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two
      hp.1 (hp.1.odd_of_ne_two (by omega)) (n := 1) (by decide) (by simpa using hF)
    exact ho.of_equiv (MulAut.outerCongr e).symm
end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
