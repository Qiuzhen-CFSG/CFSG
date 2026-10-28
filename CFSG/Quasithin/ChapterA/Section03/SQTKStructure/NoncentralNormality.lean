module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation
public import Theory.GroupTheory.CommutingConjugatePlaneRank
/-!
# The normal-or-quasisimple clause of A.3.8(3)

A nonquasisimple C-component has noncentral Fitting subgroup. The genuine
noncentral A.3.6 source constructs an elementary p² subgroup outside the
component center: the elementary omega case uses its exact action kernel,
and the extraspecial case uses exponent p, order p³ and center order p.
Distinct conjugate C-components commute by the proved A.3.7. The two-plane
rank lemma then contradicts strong quasithinness. No component-model list,
normality premise or universal classification input is used.

Source: Aschbacher--Smith, proof of A.3.8(3), printed p.46.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralNormality
open Chapter1 Chapter1.Section02 Chapter1.RadicalActions
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem quasisimple_of_central_fitting {B : Subgroup G}
    (hB : B.IsCComponent) (hf : fittingSubgroup B ≤ center B) : IsQuasisimple B := by
  have hr : solvableRadical B = center B := by
    apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hf)
    exact le_solvableRadical (center B) inferInstance
      (Group.isSolvable_of_comm (fun a b => Subtype.ext
        (mem_center_iff.mp a.property b).symm))
  let := hB.perfect
  let := hB.isSimpleGroup_quotient_solvableRadical
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩

private theorem extraspecial_plane {B : Type u} [Group B] [Finite B]
    {p : ℕ} [Fact p.Prime] (R : Subgroup B) [IsExtraspecial p R]
    (hc : Nat.card R = p ^ 3) (he : Monoid.exponent R = p) :
    ∃ E : Subgroup B, IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 ∧ ¬ E ≤ center B := by
  obtain ⟨D,hD⟩ := Sylow.exists_subgroup_card_pow_prime (G := R) p (n := 2)
    (by rw [hc]; exact pow_dvd_pow p (by decide : 2 ≤ 3))
  let : IsMulCommutative D := IsPGroup.isMulCommutative_of_card_eq_prime_sq hD
  let : IsElementaryAbelian p D :=
    { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun d => by
        apply Subtype.ext
        rw [← he]
        exact Monoid.pow_exponent_eq_one (d : R) }
  let E := D.map R.subtype
  let : IsElementaryAbelian p E := IsElementaryAbelian.map _
  refine ⟨E,inferInstance,?_,?_⟩
  · rw [card_map_of_injective R.subtype_injective,hD]
  · intro hEZ
    have hDZ : D ≤ center R := by
      intro d hd
      apply mem_center_iff.mpr
      intro r
      exact Subtype.ext (mem_center_iff.mp (hEZ (mem_map_of_mem R.subtype hd)) r)
    have hle := card_le_of_le hDZ
    rw [hD,IsExtraspecial.center_order_p p R] at hle
    have hp := (Fact.out : p.Prime).two_le
    nlinarith

theorem exists_noncentral_elementary_plane
    {κ : GroupClass.{u}} (hG : IsSQTK κ G) (hO : pCore 2 G = ⊥)
    {B : Subgroup G} (hB : B.IsCComponent) (hn : ¬ IsQuasisimple B) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ E : Subgroup B,
      IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 ∧ ¬ E ≤ center B := by
  have hf : ¬ fittingSubgroup B ≤ center B := fun h => hn (quasisimple_of_central_fitting hB h)
  obtain ⟨h36,hw⟩ := NoncentralFitting.conclusion_of_noncentral hG hO hB hf
  have hcard : Nat.card (fittingSubgroup B) ≠ 1 := by
    intro hc
    apply hf
    rw [card_eq_one.mp hc]
    exact bot_le
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd hcard
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hp3,hker,_⟩ := hw.2.2 p hd
  have ho : Odd p := hp.eq_two_or_odd'.resolve_left (by omega)
  have hshape : XiOddQuotient p (omegaCore p B) :=
    (RadicalStructure.core_omega (RadicalStructure.nonsimple_radical h36 hn) hd).2.of_mulEquiv
      ((omega (pCore p B) (p := p) 1).equivMapOfInjective
        (pCore p B).subtype (pCore p B).subtype_injective)
  refine ⟨p,hp,ho,?_⟩
  rcases hshape with ⟨hE,hEc⟩ | ⟨hR,hRc,hRe⟩
  · refine ⟨omegaCore p B,hE,hEc,?_⟩
    intro hZ
    have htop : fittingSubgroup B = ⊤ := by
      apply top_unique
      intro b _
      rw [← hker]
      apply CenterFrattiniSource.omega_centralizer_le_action_ker
      exact mem_centralizer_iff.mpr fun x hx => (mem_center_iff.mp (hZ hx) b).symm
    let e : fittingSubgroup B ≃* B := (MulEquiv.subgroupCongr htop).trans topEquiv
    exact hB.not_isSolvable (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  · let := hR
    exact extraspecial_plane (omegaCore p B) hRc hRe

theorem normal_or_quasisimple
    {κ : GroupClass.{u}} (hH : IsSQTK κ G) (hO : pCore 2 G = ⊥)
    {B : Subgroup G} (hB : B.IsCComponent) : B.Normal ∨ IsQuasisimple B := by
  classical
  by_cases hn : B.Normal
  · exact Or.inl hn
  right
  by_contra hq
  have hex : ∃ g : G, B.conjBy g ≠ B := by
    by_contra! he
    exact hn (normal_iff_map_conj_eq.mpr he)
  obtain ⟨g,hg⟩ := hex
  have hC : (B.conjBy g).IsCComponent := hB.map_equiv (MulAut.conj g)
  have hc : B ≤ centralizer (B.conjBy g : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (CComponentCommutation.commutator_eq_bot hH hO hB hC hg.symm)
  obtain ⟨p,hp,ho,E,hE,hEc,hEn⟩ := exists_noncentral_elementary_plane hH hO hB hq
  let : Fact p.Prime := ⟨hp⟩
  let := hE
  have hl := B.three_le_primeRank_of_commuting_conjugate_plane g hc E hEc hEn
  have hu := hH.stronglyQuasithin p hp ho
  omega

end CFSG.Quasithin.ChapterA.Section03.NoncentralNormality
