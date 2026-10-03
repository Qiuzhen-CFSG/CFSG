module
public import Stellmacher.SectionOne.NineCoreSupportDecomposition
public import Stellmacher.SectionOne.NineCoreSupportDecompositionFaithfulness
public import Theory.GroupAction.QuadraticComplementPair

/-!
# A normalized support line for the quadratic nine-core module

For a faithful binary module of order sixteen with a normal elementary
nine-subgroup, an elementary actor of order four acting quadratically
normalizes an order-three line whose fixed subgroup has order four.
The actor acts nontrivially on that fixed subgroup.

The intrinsic nine-core decomposition gives two complementary four-element
summands. The quadratic complementary-pair theorem makes the actor preserve
each one. Fixed-point transport and uniqueness of the supporting actor line
then give its normalizer containment. If the actor fixed the selected
summand pointwise, its action on the other summand would be faithful,
embedding a group of order four in SL₂(2), whose order is six.

This selects the chief-module line used for D* in Stellmacher (9.1),
printed p48 of `refs/files/stellmacher-n-group.pdf`. The later comparison
with the initial-center module and the lift to the initial stabilizer are
separate steps; no chosen representation or subgroup lift is assumed here.
-/

namespace Stellmacher.SectionOne
open scoped IsMulCommutative
universe u

private theorem support_line_unique
    {X V : Type u} [Group X] [Finite X] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction X V]
    (F D E : Subgroup X) (hF : Nat.card F = 9) (hV : Nat.card V = 16)
    (hfaith : fixingSubgroup X (Set.univ : Set V) = ⊥)
    (hDF : D ≤ F) (hEF : E ≤ F) (hD : Nat.card D = 3) (hE : Nat.card E = 3)
    (hfixed : Nat.card (FixedPoints.subgroup D V) = 4)
    (heq : FixedPoints.subgroup D V = FixedPoints.subgroup E V) : D = E := by
  by_contra hne
  have hcompl := nineCoreSupportDecomposition_distinct_lines_fixed_isCompl
    F D E hF hV hfaith hDF hEF hD hE hne hfixed (heq ▸ hfixed)
  have hbot : FixedPoints.subgroup D V = ⊥ := by
    simpa only [← heq, inf_idem] using hcompl.inf_eq_bot
  rw [hbot, Subgroup.card_bot] at hfixed
  omega

public theorem nineCore_quadratic_actor_support_line
    {X V : Type u} [Group X] [Finite X] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction X V]
    (F J : Subgroup X) [F.Normal] [IsElementaryAbelian 3 F] [IsElementaryAbelian 2 J]
    (hF : Nat.card F = 9) (hV : Nat.card V = 16)
    (hfaith : fixingSubgroup X (Set.univ : Set V) = ⊥)
    (hJ : Nat.card J = 4) (hquad : commutatorAction₂ J V = ⊥) :
    ∃ D : Subgroup X, D ≤ F ∧ Nat.card D = 3 ∧
      J ≤ Subgroup.normalizer (D : Set X) ∧ Nat.card (FixedPoints.subgroup D V) = 4 ∧
      ∃ actor : J, ∃ point ∈ FixedPoints.subgroup D V, actor • point ≠ point := by
  obtain ⟨P, Q, hcompl, hpair⟩ := nineCoreSupportDecomposition_intrinsic_pair F
    inferInstance hF hV hfaith
  have hP := (hpair P).mpr (Or.inl rfl)
  have hQ := (hpair Q).mpr (Or.inr rfl)
  have hne : P ≠ Q := by
    intro heq
    have hbot : P = ⊥ := by simpa only [← heq, inf_idem] using hcompl.inf_eq_bot
    have hh := hP.1
    rw [hbot, Subgroup.card_bot] at hh
    omega
  have hperm := nineCoreSupportDecomposition_permuted_of_intrinsic_pair
    F (inferInstance : F.Normal) P Q hne hpair
  have hfaithJ : fixingSubgroup J (Set.univ : Set V) = ⊥ :=
    nineCoreSupportDecomposition_restricted_faithful J hfaith
  have hstable : ∀ a : J, (∀ v ∈ P, a • v ∈ P) ∧ (∀ v ∈ Q, a • v ∈ Q) := by
    apply quadratic_actor_preserves_complementary_pair hfaithJ (by omega) hquad P Q hcompl
    intro a
    rcases hperm a with hp | hp
    · left
      exact ⟨fun v hv => hp.1 ▸ Subgroup.mem_map_of_mem _ hv,
        fun v hv => hp.2 ▸ Subgroup.mem_map_of_mem _ hv⟩
    · right
      exact ⟨fun v hv => hp.1 ▸ Subgroup.mem_map_of_mem _ hv,
        fun v hv => hp.2 ▸ Subgroup.mem_map_of_mem _ hv⟩
  obtain ⟨D, hDF, hDcard, hDP⟩ := hP.2
  have hfixed : Nat.card (FixedPoints.subgroup D V) = 4 := hDP ▸ hP.1
  have hnormal : J ≤ Subgroup.normalizer (D : Set X) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro actor hactor member hmember
    let image := D.map (MulAut.conj actor).toMonoidHom
    have hIF : image ≤ F := by
      rintro _ ⟨d, hd, rfl⟩
      exact (inferInstance : F.Normal).conj_mem d (hDF hd) actor
    have hIcard : Nat.card image = 3 :=
      (Subgroup.card_map_of_injective (MulAut.conj actor).injective).trans hDcard
    have hmap : P.map (MulDistribMulAction.toMulAut X V actor).toMonoidHom = P := by
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨v, hv, rfl⟩
        exact (hstable ⟨actor, hactor⟩).1 v hv
      · exact (Subgroup.card_map_of_injective
          (f := (MulDistribMulAction.toMulAut X V actor).toMonoidHom)
          (MulDistribMulAction.toMulAut X V actor).injective).ge
    have hfixedEq : FixedPoints.subgroup D V = FixedPoints.subgroup image V := by
      rw [← nineCoreSupportDecomposition_map_fixedPoints, ← hDP, hmap]
    have heq : D = image := support_line_unique F D image hF hV hfaith
      hDF hIF hDcard hIcard hfixed hfixedEq
    rw [heq]
    exact Subgroup.mem_map_of_mem _ hmember
  refine ⟨D, hDF, hDcard, hnormal, hfixed, ?_⟩
  by_contra htrivial
  push Not at htrivial
  have hPfixed (actor : J) (point : V) (hpoint : point ∈ P) : actor • point = point := by
    apply htrivial actor point
    rwa [← hDP]
  let _ : IsInvariant J V Q := ⟨fun actor point => ⟨(hstable actor).2 point, fun hp => by
    have hh := (hstable actor⁻¹).2 (actor • point) hp
    simpa only [inv_smul_smul] using hh⟩⟩
  let _ : IsElementaryAbelian 2 Q := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro point
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) (point : V) }
  have hfaithQ : fixingSubgroup J (Set.univ : Set Q) = ⊥ := by
    apply bot_unique
    intro actor hactor
    apply hfaithJ.le
    rw [mem_fixingSubgroup_iff] at hactor ⊢
    intro point _
    have hinjoin : point ∈ P ⊔ Q := hcompl.sup_eq_top.ge (Subgroup.mem_top point)
    obtain ⟨p, hp, q, hq, rfl⟩ := Subgroup.mem_sup.mp hinjoin
    have hqfix : actor • q = q := congrArg Subtype.val
      (hactor (⟨q, hq⟩ : Q) (Set.mem_univ _))
    rw [smul_mul', hPfixed actor p hp, hqfix]
  obtain ⟨embedding, hinjective, _⟩ :=
    FourGroupMatrixCoordinates.faithful_card_four_embedding hfaithQ hQ.1
  have hdvd := Subgroup.card_dvd_of_injective embedding hinjective
  obtain ⟨equivalence⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  rw [hJ, Nat.card_congr equivalence.toEquiv, Nat.card_perm, Nat.card_fin] at hdvd
  norm_num [Nat.factorial] at hdvd

end Stellmacher.SectionOne
