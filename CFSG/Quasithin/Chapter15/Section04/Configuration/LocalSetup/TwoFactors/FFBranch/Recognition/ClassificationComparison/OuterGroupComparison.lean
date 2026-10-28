module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ProductComparison
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Adequate
/-!
# Excluding the outer A₆–C₃ configuration in the mixed comparison

Only the actual group data of B.5.6(4) is needed. The A₆ factor excludes the
small solvable row, the cyclic quotient over A₆ × C₃ has two-power order by
offender generation, and the component rows contradict the disjoint C₃
centralizer. Thus no fixed-space splitting, splitting of the outer extension,
or equality of the offender subgroup with the ambient group is used.

The component argument is the group-only version of
`ProductComparison.outerSixThree_not_quasisimple`.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6(4), p.105; F.6.18, pp.309–310; 15.4.18, p.1163.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace OuterGroupComparison
open FFAlternatives
variable {D : Type*} [Group D]

private theorem commutative_of_injective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) [IsMulCommutative B] : IsMulCommutative A :=
  ⟨⟨fun a b => hf (by simp only [map_mul, mul_comm'])⟩⟩


private theorem nonabelian_subnormal_contains_fitting [Finite D]
    (hL : IsQuasisimple (generalizedFitting D)) (A : Subgroup D)
    (hA : A.IsSubnormal) (hna : ¬ IsMulCommutative A) : generalizedFitting D ≤ A := by
  let L := generalizedFitting D
  have hcomp : IsComponent D L := ⟨(inferInstance : L.Normal).isSubnormal, hL⟩
  rcases hcomp.subnormal_dichotomy A hA with h | h
  · exact h
  · have ha : A ≤ centralizer (L : Set D) :=
      commutator_eq_bot_iff_le_centralizer.mp (by simpa [commutator_comm] using h)
    have hal : A ≤ L := ha.trans ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
    apply (hna ?_).elim
    exact ⟨⟨fun a b => Subtype.ext (mem_centralizer_iff.mp (ha a.property) b (hal b.property)).symm⟩⟩


private theorem pair_commute {A B : Subgroup D} (f : (A × B) →* D)
    (hf : ∀ a b, f (a,b) = (a : D) * (b : D)) : ⁅A,B⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro a ha
  apply mem_centralizer_iff.mpr
  intro b hb
  have he : f (⟨a,ha⟩,1) * f (1,⟨b,hb⟩) = f (1,⟨b,hb⟩) * f (⟨a,ha⟩,1) := by
    rw [← map_mul, ← map_mul]
    simp
  simpa [hf] using he.symm

private theorem pair_disjoint {A B : Subgroup D} (f : (A × B) →* D)
    (hi : Function.Injective f) (hf : ∀ a b, f (a,b) = (a : D) * (b : D)) :
    Disjoint A B := by
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  intro x hx
  have he : f (⟨x,hx.1⟩,1) = f (1,⟨x,hx.2⟩) := by simp [hf]
  have hh := congrArg (fun y : A × B => (y.1 : D)) (hi he)
  exact hh

private theorem not_quasisimple_of_disjoint [Finite D] (A B : Subgroup D)
    (hA : A.IsSubnormal) (hna : ¬ IsMulCommutative A) (hne : B ≠ ⊥)
    (hc : ⁅A,B⁆ = ⊥) (hd : Disjoint A B) :
    ¬ IsQuasisimple (generalizedFitting D) := by
  intro hL
  have ha := nonabelian_subnormal_contains_fitting hL A hA hna
  have hb : B ≤ centralizer (A : Set D) :=
    commutator_eq_bot_iff_le_centralizer.mp (by simpa [commutator_comm] using hc)
  have hbL : B ≤ generalizedFitting D :=
    (hb.trans (centralizer_le ha)).trans ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  apply hne
  exact le_bot_iff.mp ((le_inf (hbL.trans ha) le_rfl).trans (disjoint_iff.mp hd).le)

variable [Finite D] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
attribute [local instance] offenderSubgroup_normal

/-- The actual outer factors rule out a quasisimple ambient F*. -/
theorem outerShape_not_quasisimple
    (c : ChapterB.OuterSixThreeShape (offenderSubgroup ρ)) :
    ¬ IsQuasisimple (generalizedFitting D) := by
  let N := offenderSubgroup ρ
  let f : (c.first × c.second) →* N :=
    (c.first ⊔ c.second).subtype.comp c.product.toMonoidHom
  have hf : ∀ a b, f (a,b) = (a : N) * (b : N) := c.product_apply
  have hc : ⁅c.first,c.second⁆ = ⊥ := pair_commute f hf
  have hd : Disjoint c.first c.second := pair_disjoint f
    (Subtype.val_injective.comp c.product.injective) hf
  let : c.first.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← c.generates]
    have ho : InducesOuter c.first c.element := c.firstOuter
    refine sup_le (sup_le c.first.le_normalizer ?_) (zpowers_le.mpr ho.mem_normalizer)
    exact (commutator_eq_bot_iff_le_centralizer.mp
      (by simpa [commutator_comm] using hc)).trans (Subgroup.centralizer_le_normalizer _)
  have hna : ¬ IsMulCommutative c.first := by
    intro h
    let := h
    have hcomm := commutative_of_injective c.firstEquiv.symm.toMonoidHom c.firstEquiv.symm.injective
    have hh := alternatingGroup.isMulCommutative_iff_card_le_three.mp hcomm
    norm_num at hh
  have hne : c.second.map N.subtype ≠ ⊥ := by
    let : Nontrivial c.second := c.secondEquiv.symm.injective.nontrivial
    let : Nontrivial (c.second.map N.subtype) :=
      (equivMapOfInjective c.second N.subtype N.subtype_injective).injective.nontrivial
    exact (nontrivial_iff_ne_bot _).mp inferInstance
  refine not_quasisimple_of_disjoint (c.first.map N.subtype) (c.second.map N.subtype)
    ((inferInstance : c.first.Normal).isSubnormal.trans' (inferInstance : N.Normal).isSubnormal)
    ?_ hne ?_ ?_
  · intro h
    let := h
    exact hna (commutative_of_injective
      (equivMapOfInjective c.first N.subtype N.subtype_injective).toMonoidHom
      (equivMapOfInjective c.first N.subtype N.subtype_injective).injective)
  · rw [← map_commutator, hc, Subgroup.map_bot]
  · exact disjoint_map N.subtype_injective hd

private theorem odd_prime_dvd_normal (N : Subgroup D) [N.Normal]
    (hq : IsPGroup 2 (D ⧸ N)) {p : ℕ} (hp : p.Prime) (hne : p ≠ 2)
    (hd : p ∣ Nat.card D) : p ∣ Nat.card N := by
  obtain ⟨k, hk⟩ := hq.exists_card_eq
  have he : Nat.card D = Nat.card N * 2 ^ k := by
    rw [← hk, ← Subgroup.index_eq_card, Subgroup.card_mul_index]
  rw [he] at hd
  rcases hp.dvd_mul.mp hd with hd | hd
  · exact hd
  · have hh := hp.dvd_of_dvd_pow hd
    exact (hne ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hh |>.resolve_left hp.ne_one)).elim

private theorem outer_not_large_prime
    (c : ChapterB.OuterSixThreeShape (offenderSubgroup ρ))
    (hg : offenderSubgroup (ρ.comp (offenderSubgroup ρ).subtype) = ⊤)
    (hq : IsPGroup 2 (D ⧸ offenderSubgroup ρ))
    {p : ℕ} (hp : p.Prime) (hlarge : 5 < p) : ¬ p ∣ Nat.card D := by
  intro hd
  have hN := odd_prime_dvd_normal (offenderSubgroup ρ) hq hp (by omega) hd
  let := outerSixThreeShape_product_normal c
  let := outerSixThreeShape_quotient_isCyclic c
  let := IsCyclic.commGroup (α := offenderSubgroup ρ ⧸ (c.first ⊔ c.second))
  have hq' := abelian_image_isTwoGroup _ (QuotientGroup.mk' (c.first ⊔ c.second))
    (QuotientGroup.mk'_surjective _) hg
  have hprod := odd_prime_dvd_normal (c.first ⊔ c.second) hq' hp (by omega) hN
  have hcard : Nat.card (c.first ⊔ c.second : Subgroup (offenderSubgroup ρ)) = 1080 := by
    rw [← Nat.card_congr c.product.toEquiv, Nat.card_prod,
      Nat.card_congr c.firstEquiv.toEquiv, Nat.card_congr c.secondEquiv.toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [hcard, show (1080 : ℕ) = 2 ^ 3 * 3 ^ 3 * 5 by decide] at hprod
  rcases hp.dvd_mul.mp hprod with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · have := Nat.le_of_dvd (by decide : 0 < 2) (hp.dvd_of_dvd_pow h)
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 3) (hp.dvd_of_dvd_pow h)
      omega
  · have := Nat.le_of_dvd (by decide : 0 < 5) h
    omega

private theorem psl_prime_dvd {A : Type*} [Group A] {p : ℕ} (hp : p.Prime)
    (ho : Odd p) (hm : ClassicalGroup.IsPSL A 2 p) : p ∣ Nat.card A := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  rw [Nat.card_congr e.toEquiv]
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hF ▸ ho)
  have hd : p ∣ Nat.card PSL(2,F) * 2 := by
    rw [hc, hF]
    exact dvd_mul_right _ _
  rcases hp.dvd_mul.mp hd with hd | hd
  · exact hd
  · have he := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd |>.resolve_left hp.ne_one
    have hh := Nat.odd_iff.mp ho
    omega

private theorem not_case2
    (c : ChapterB.OuterSixThreeShape (offenderSubgroup ρ)) :
    ¬ GoldschmidtAlternatives.Case2 D := by
  have hh := (Nat.card_le_card_of_injective c.first.subtype c.first.subtype_injective).trans
    (Nat.card_le_card_of_injective (offenderSubgroup ρ).subtype
      (offenderSubgroup ρ).subtype_injective)
  rw [Nat.card_congr c.firstEquiv.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hh
  norm_num [Nat.factorial] at hh
  intro h
  rcases h with he | he
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv] at hh
    norm_num [Nat.card_prod, GoldschmidtAlternatives.S3, Nat.card_eq_fintype_card,
      Fintype.card_perm, Nat.factorial] at hh
  · rw [he.card, HeisenbergPrime.card] at hh
    norm_num [GoldschmidtAlternatives.E4, GoldschmidtAlternatives.C, Nat.card_prod] at hh

/-- Exclude the adequate outer branch against all retained F.6.18 rows in
both generator orientations. The two-group extension remains the actual D/N. -/
theorem not_outerShape {G₁ G₂ : Subgroup D}
    (hcore : pCore 2 D = ⊥)
    (hr : GoldschmidtAlternatives.Remaining G₁ G₂)
    (hg : offenderSubgroup (ρ.comp (offenderSubgroup ρ).subtype) = ⊤)
    (hq : IsPGroup 2 (D ⧸ offenderSubgroup ρ)) :
    ¬ Nonempty (ChapterB.OuterSixThreeShape (offenderSubgroup ρ)) := by
  rintro ⟨c⟩
  have ordered (A B : Subgroup D) (h : GoldschmidtAlternatives.RemainingOrdered A B) :
      False := by
    rcases h with h2 | h3 | hc
    · exact not_case2 ρ c h2
    · obtain ⟨p, L, _, hp, hm, hL, _⟩ := h3
      have hd : p ∣ Nat.card D :=
        (psl_prime_dvd hp (Nat.odd_iff.mpr (by omega)) hL).trans L.card_subgroup_dvd_card
      exact outer_not_large_prime ρ c hg hq hp (by omega) hd
    · exact outerShape_not_quasisimple ρ c
        (ProductComparison.componentRows_quasisimple hcore hc)
  exact hr.elim (ordered G₁ G₂) (ordered G₂ G₁)

end OuterGroupComparison
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
