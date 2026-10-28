module
public import Theory.GroupTheory.NormalElementaryNinePerfect
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import Theory.SpecificGroups.PrimeToFifteen.Classical.Unitary
public import Theory.SpecificGroups.ThreeDivisibility.Classical
public import Theory.SpecificGroups.ThreeDivisibility.Exceptional
public import Theory.SpecificGroups.ThreeDivisibility.Sporadic
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M23.Properties.Order
public import Theory.Mathieu.M24.Properties.Order

/-!
# Suzuki components forced by a normal elementary nine

The full Theorem C list has only the Suzuki row of order prime to three.
In the two-core-free A.3.6 alternatives, a perfect subgroup with all cubics
central is three-free: transfer handles the simple and triple-cover rows,
and the noncentral Fitting rows have three-free center. A normal elementary
nine saturates three-rank and supplies precisely that centrality condition.

The final theorem applies the proved A.3.6 classification, with both earlier
Theorems A and C discharged for the complete known-simple catalogue. Its
consumer is the normal-residual branch of original 14.6.14 in
Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.CubicNormal.

Source: Aschbacher--Smith A.3.6, pp.43--45, and 14.6.14, p.1033.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.LocalModels
open ClassificationModels
variable {G : Type*} [Group G]

private theorem linear_three {n q : ℕ} (hn : 2 ≤ n)
    (h : ClassicalGroup.IsPSL G n q) : 3 ∣ Nat.card G := by
  obtain ⟨F,_,_,_,⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact Matrix.ProjectiveSpecialLinearGroup.three_dvd_card F n hn

private theorem unitary_three {q : ℕ} (hq : IsPrimePow q)
    (h : ClassicalGroup.IsPSU G 3 q) : 3 ∣ Nat.card G := by
  obtain ⟨F,_,_,J,hF,hJ,⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact Theory.SpecificGroups.PrimeToFifteen.Classical.unitary_three_dvd J (by decide) hq hF hJ

private theorem sporadic_three (name : SporadicName) (hne : name ≠ .j3) :
    3 ∣ Nat.card name.Carrier := by
  cases name with
  | m11 => change 3 ∣ Nat.card Sporadic.Mathieu.M11; rw [Sporadic.Mathieu.m11_order]; norm_num
  | m12 => change 3 ∣ Nat.card Sporadic.Mathieu.M12; rw [Sporadic.Mathieu.m12_order]; norm_num
  | m22 => change 3 ∣ Nat.card Sporadic.Mathieu.M22; rw [Sporadic.Mathieu.m22_order]; norm_num
  | m23 => change 3 ∣ Nat.card Sporadic.Mathieu.M23; rw [Sporadic.Mathieu.m23_order]; norm_num
  | m24 => change 3 ∣ Nat.card Sporadic.Mathieu.M24; rw [Sporadic.Mathieu.m24_order]; norm_num
  | j2 => exact Theory.SpecificGroups.ThreeDivisibility.j2
  | j3 => exact (hne rfl).elim
  | j4 => exact Theory.SpecificGroups.ThreeDivisibility.j4
  | hs => exact Theory.SpecificGroups.ThreeDivisibility.hs
  | he => exact Theory.SpecificGroups.ThreeDivisibility.held
  | ru => exact Theory.SpecificGroups.ThreeDivisibility.rudvalis

/-- The only three-free model in the full Theorem C list is Suzuki. -/
theorem TheoremCModel.suzuki_of_three_free (h : TheoremCModel G)
    (h3 : ¬ 3 ∣ Nat.card G) :
    ∃ m, 1 ≤ m ∧ Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  have hp (n : ℕ) (hn : 0 < n) : IsPrimePow (2 ^ n) := Nat.prime_two.isPrimePow.pow hn.ne'
  cases h with
  | alternating n hn he =>
    obtain ⟨e⟩ := he
    apply False.elim
    apply h3
    let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    have hd : 6 ∣ n.factorial := dvd_trans (by decide : 6 ∣ (3:ℕ).factorial)
      (Nat.factorial_dvd_factorial (by omega))
    obtain ⟨k,hk⟩ := hd
    rw [hk]
    omega
  | linear_odd p r hp ho hr hs he => exact (h3 (linear_three (by decide) he)).elim
  | three_odd p hp ho unitary he =>
    cases unitary
    · exact (h3 (linear_three (by decide) he)).elim
    · exact (h3 (unitary_three hp.isPrimePow he)).elim
  | rank_one he =>
    cases he with
    | linear n hn he => exact (h3 (linear_three (by decide) he)).elim
    | unitary n hn he => exact (h3 (unitary_three (hp n (by omega)) he)).elim
    | suzuki m hm he => exact ⟨m,hm,he⟩
  | rank_two he =>
    apply False.elim
    apply h3
    cases he with
    | linear n hn he => exact linear_three (by decide) he
    | symplectic n hn he =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
      rw [Nat.card_congr e.toEquiv]
      exact Theory.SpecificGroups.ThreeDivisibility.symplectic F hF
    | g2 n hn he =>
      obtain ⟨F,_,_,_,⟨e⟩⟩ := he
      rw [Nat.card_congr e.toEquiv]
      exact Theory.SpecificGroups.ThreeDivisibility.g2 F
    | triality n hn he =>
      exact Triality.Standard.model_three_dvd_card he
    | ree m hm he =>
      obtain ⟨d,⟨e⟩⟩ := he
      rw [Nat.card_congr e.toEquiv]
      exact d.three_dvd_card
    | symplectic_derived he =>
      rw [Nat.card_congr he.some.toEquiv]
      exact Theory.SpecificGroups.ThreeDivisibility.symplectic_derived
    | g2_derived he =>
      rw [Nat.card_congr he.some.toEquiv]
      exact Theory.SpecificGroups.ThreeDivisibility.g2_derived
    | tits he =>
      rw [Nat.card_congr he.some.toEquiv]
      exact Theory.SpecificGroups.ThreeDivisibility.tits
  | binary_linear n hn he => exact (h3 (linear_three (by rcases hn with rfl | rfl <;> decide) he)).elim
  | sporadic name hne he =>
    exact (h3 (by rw [Nat.card_congr he.some.toEquiv]; exact sporadic_three name hne)).elim
  | janko_one he =>
    apply False.elim
    apply h3
    rw [Nat.card_congr he.some.toEquiv]
    exact Janko1.orderOf_b ▸ orderOf_dvd_natCard Janko1.b
end CFSG.Quasithin.Chapter1.Section02.LocalModels

namespace CFSG.Quasithin.Chapter1.Section02
open LocalModels
variable {G : Type*} [Group G] [Finite G]

private theorem center_three_free_of_fitting_three_free
    {B : Type*} [Group B] [Finite B] (hf : ¬ 3 ∣ Nat.card (fittingSubgroup B)) :
    ¬ 3 ∣ Nat.card (center B) := by
  have hz : center B ≤ fittingSubgroup B := by
    let : CommGroup (center B) := IsMulCommutative.instCommGroup
    exact le_sSup ⟨inferInstance,inferInstance⟩
  exact fun hd => hf (hd.trans (card_dvd_of_le hz))

private theorem three_free_of_cubic_central_of_center_three_free
    {B : Type*} [Group B] [Finite B] (hz : ¬ 3 ∣ Nat.card (center B))
    (hc : ∀ x : B, x ^ 3 = 1 → x ∈ center B) : ¬ 3 ∣ Nat.card B := by
  intro hd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
  let z : center B := ⟨x,hc x (hx ▸ pow_orderOf_eq_one x)⟩
  apply hz
  have hh := orderOf_dvd_natCard z
  simpa only [z, Subgroup.orderOf_mk,hx] using hh

private theorem natural_fitting_three_free {B : Type*} [Group B] [Finite B]
    (h : A36Natural B) : ¬ 3 ∣ Nat.card (fittingSubgroup B) := by
  obtain ⟨he,p,hp,hgt,F,_,_,hF,v,e,hv⟩ := h
  have hc : Nat.card (generalizedFitting B) = p^2 := by
    rw [Nat.card_congr v.toEquiv]
    change Nat.card (Fin 2 → F) = p^2
    rw [Nat.card_fun,Nat.card_fin,hF]
  rw [←he,hc]
  intro hd
  rcases (Nat.dvd_prime hp).mp (Nat.prime_three.dvd_of_dvd_pow hd) with heq | heq <;> omega

/-- In every A.3.6 case, centrality of all cubics excludes the prime three. -/
theorem A36Conclusion.three_free_of_cubic_central
    {B : Subgroup G} (hB : B.IsCComponent) (h : A36Conclusion B)
    (hc : ∀ x : B, x ^ 3 = 1 → x ∈ center B) : ¬ 3 ∣ Nat.card B := by
  let := hB.perfect
  cases h.1 with
  | simple hcomp hs hm =>
    let := hs
    have hz : center B = ⊥ := by
      rcases (inferInstance : (center B).Normal).eq_bot_or_eq_top with hz | hz
      · exact hz
      · exact (Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp hz)).elim
    exact perfect_three_free_of_cubic_central_of_small_center (by rw [hz]; simp) hc
  | cover hcomp he hm =>
    have hz : Nat.card (center B) = 3 := by
      rw [Nat.card_congr he.some.toEquiv]
      change Nat.card (ZMod 3) = 3
      simp
    exact perfect_three_free_of_cubic_central_of_small_center hz.le hc
  | natural hn =>
    exact three_free_of_cubic_central_of_center_three_free
      (center_three_free_of_fitting_three_free (natural_fitting_three_free hn)) hc
  | nilpotent hn =>
    have hf : ¬ 3 ∣ Nat.card (fittingSubgroup B) := by
      intro hd
      have hh := (hn.2.2.2 3 Nat.prime_three (hn.1.symm ▸ hd)).1
      norm_num at hh
    exact three_free_of_cubic_central_of_center_three_free
      (center_three_free_of_fitting_three_free hf) hc

private theorem sl_three {B : Type*} [Group B] {q : ℕ}
    (h : IsSL B 2 q) : 3 ∣ Nat.card B := by
  obtain ⟨F,_,_,_,⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact (Matrix.ProjectiveSpecialLinearGroup.three_dvd_card F 2 (by decide)).trans
    (center (Matrix.SpecialLinearGroup (Fin 2) F)).card_quotient_dvd_card

/-- Three-free C-components in A.3.6 are actual Suzuki groups. -/
theorem A36Conclusion.suzuki_of_three_free
    {B : Subgroup G} (h : A36Conclusion B) (h3 : ¬ 3 ∣ Nat.card B) :
    ∃ m, 1 ≤ m ∧ Nonempty (B ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  cases h.1 with
  | simple hc hs hm => exact hm.suzuki_of_three_free h3
  | cover hc he hm =>
    apply False.elim
    apply h3
    have hz : Nat.card (center B) = 3 := by
      rw [Nat.card_congr he.some.toEquiv]
      change Nat.card (ZMod 3) = 3
      simp
    exact hz ▸ (center B).card_subgroup_dvd_card
  | natural hn =>
    obtain ⟨p,hp,hgt,F,hF,hfin,hcard,v,e,hv⟩ := hn.2
    exact (h3 ((sl_three ⟨F,hF,hfin,hcard,⟨e⟩⟩).trans
      (generalizedFitting B).card_quotient_dvd_card)).elim
  | nilpotent hn =>
    exact (h3 ((sl_three hn.2.2.1).trans
      (generalizedFitting B).card_quotient_dvd_card)).elim

/-- A normal elementary nine forces every two-core-free SQTK C-component
onto the Suzuki row. All earlier A.3.6 inputs are discharged. -/
theorem cComponent_suzuki_of_normal_elementary_nine
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (E : Subgroup G) [E.Normal] [IsElementaryAbelian 3 E] (hE : Nat.card E = 9)
    {B : Subgroup G} (hB : B.IsCComponent) :
    ∃ m, 1 ≤ m ∧ Nonempty (B ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  have h := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) G hG hO B hB
  let := hB.perfect
  exact h.suzuki_of_three_free (h.three_free_of_cubic_central hB
    (normal_elementary_nine_perfect_cubic_central E hE
      (hG.stronglyQuasithin 3 (by decide) (by decide)) B))
end CFSG.Quasithin.Chapter1.Section02
