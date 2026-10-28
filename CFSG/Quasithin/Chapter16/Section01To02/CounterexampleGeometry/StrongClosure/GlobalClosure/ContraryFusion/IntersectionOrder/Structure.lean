module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.IntersectionBounds
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.GroupTheory.InvolutionCentralizerFourRecognition

/-!
# The intersection extension under contrary fusion

Let an outside transporter send a factor involution to t in the prescribed
Sylow two-subgroup. If the factors intersect nontrivially, their intersection
C has a fixed subgroup of order exactly two under t. Indeed, C is normal in
the two-group D = C⟨t⟩, so a nontrivial element of C is central in D; the
source's unique-conjugate condition gives the matching upper bound.

The actual centralizer of t in D has order four. For noncentral t, the
involution-centralizer recognition theorem gives a dihedral equivalence or
a semidihedral presentation, which is converted to the standard model.
For central t, C has order two and D is constructed as the four-group.
Thus the recognition theorem is never used without its noncentrality input.
All results allow the original involution to lie in either factor.

This supplies the structural input to the subsequent v, vvᵗ and tz argument;
it does not yet assert that the whole intersection has order two.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, from “So A₁ ∩ A₂ ≠ 1” through the recognition of D.
DOI: 10.1215/ijm/1256050927.
-/

@[expose] public section
open scoped Pointwise
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

omit [Finite G] in
private theorem extension_normalizes_intersection {t : G}
    (hs : conjugate A₁ t = A₂ ∧ conjugate A₂ t = A₁) :
    (A₁ ⊓ A₂) ⊔ zpowers t ≤ normalizer ((A₁ ⊓ A₂ : Subgroup G) : Set G) := by
  apply sup_le (A₁ ⊓ A₂).le_normalizer
  apply zpowers_le.mpr
  apply (mem_normalizer_iff_conjugate_eq _ _).mpr
  change (A₁ ⊓ A₂).map (MulAut.conj t⁻¹).toMonoidHom = A₁ ⊓ A₂
  rw [map_inf _ _ _ (MulAut.conj t⁻¹).injective]
  change conjugate A₁ t ⊓ conjugate A₂ t = _
  rw [hs.1, hs.2, inf_comm]

omit [Finite G] in
private theorem centralizer_normalizing_join (C : Subgroup G) (t : G)
    (hn : t ∈ normalizer (C : Set G)) :
    (C ⊔ zpowers t) ⊓ centralizer ({t} : Set G) =
      (C ⊓ centralizer ({t} : Set G)) ⊔ zpowers t := by
  have htC : zpowers t ≤ centralizer ({t} : Set G) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  apply le_antisymm
  · rintro x ⟨hxD, hxC⟩
    have hxprod : x ∈ (C : Set G) * (zpowers t : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left C (zpowers t) (zpowers_le.mpr hn)]
      exact hxD
    obtain ⟨c, hc, y, hy, rfl⟩ := hxprod
    have hcC : c ∈ centralizer ({t} : Set G) := by
      simpa using (centralizer ({t} : Set G)).mul_mem hxC
        ((centralizer ({t} : Set G)).inv_mem (htC hy))
    exact mul_mem_sup ⟨hc, hcC⟩ hy
  · exact sup_le (inf_le_inf_right _ le_sup_left)
      (le_inf le_sup_right htC)

omit [Finite G] in
private theorem centralizer_subtype_card (D : Subgroup G) (t : D) :
    Nat.card (centralizer ({t} : Set D)) =
      Nat.card (D ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) := by
  let e : centralizer ({t} : Set D) ≃*
      (D ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) := {
    toFun x := ⟨(x : D), (x : D).property,
      mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (mem_centralizer_singleton_iff.mp x.property))⟩
    invFun x := ⟨⟨x, x.property.1⟩,
      mem_centralizer_singleton_iff.mpr (Subtype.ext
        (mem_centralizer_singleton_iff.mp x.property.2))⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  exact Nat.card_congr e.toEquiv

private theorem small_dihedral_of_central_external_involution
    (C : Subgroup G) (t : G) (hC : Nat.card C = 2)
    (htsq : t ^ 2 = 1) (htout : t ∉ C)
    (hCt : C ≤ centralizer ({t} : Set G)) :
    Nonempty ((C ⊔ zpowers t : Subgroup G) ≃* DihedralGroup 2) := by
  let D := C ⊔ zpowers t
  have htn : t ∈ normalizer (C : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    intro c hc
    exact mem_centralizer_singleton_iff.mp (hCt hc)
  have hD : Nat.card D = 4 := by
    rw [card_sup_zpowers_of_normalizing_involution C t htsq htout htn, hC]
  have hexp : ∀ d : D, d ^ 2 = 1 := by
    intro d
    have hd : (d : G) ∈ (C : Set G) * (zpowers t : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left C (zpowers t) (zpowers_le.mpr htn)]
      exact d.property
    obtain ⟨c, hc, y, hy, hcy⟩ := hd
    obtain ⟨n, rfl⟩ := hy
    have hcsq : c ^ 2 = 1 := by
      have hh := pow_card_eq_one' (x := (⟨c, hc⟩ : C))
      rw [hC] at hh
      exact congrArg Subtype.val hh
    have hysq : (t ^ n) ^ 2 = 1 := by
      have hh := zpow_comm t n (2 : ℤ)
      simpa only [zpow_ofNat, htsq, one_zpow] using hh
    have hcomm : Commute c t := mem_centralizer_singleton_iff.mp (hCt hc)
    apply Subtype.ext
    change (d : G) ^ 2 = 1
    rw [← hcy, (hcomm.zpow_right n).mul_pow, hcsq, hysq, one_mul]
  let : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp (by rw [hD]; decide)
  let : IsKleinFour D := ⟨hD, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr
    (fun d hd => orderOf_eq_prime (hexp d) hd)⟩
  exact IsKleinFour.nonempty_mulEquiv

theorem LocalControl.intersection_centralizer_card_two
    (l : LocalControl S A₁ A₂) (h : Hypotheses S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha2 : orderOf a = 2)
    (hg : g ∉ intersectionGenerated A₁ A₂) (ht : g⁻¹ * a * g ∈ S)
    (hcap : A₁ ⊓ A₂ ≠ ⊥) :
    Nat.card ((A₁ ⊓ A₂) ⊓ centralizer ({g⁻¹ * a * g} : Set G) : Subgroup G) = 2 := by
  let t := g⁻¹ * a * g
  let C := A₁ ⊓ A₂
  let D := C ⊔ zpowers t
  have ha1 : a ≠ 1 := by intro he; simp [he] at ha2
  have hs := l.swap_of_outside_transporter h ha ha1 hg ht
  have hCD : C ≤ D := le_sup_left
  have htD : t ∈ D := (le_sup_right : zpowers t ≤ D) (mem_zpowers t)
  have hDS : D ≤ (S : Subgroup G) := sup_le (inf_le_left.trans h.left_le) (zpowers_le.mpr ht)
  have hD : IsPGroup 2 D := S.isPGroup'.to_le hDS
  have hnorm : D ≤ normalizer (C : Set G) := extension_normalizes_intersection hs
  let : (C.subgroupOf D).Normal := (normal_subgroupOf_iff_le_normalizer hCD).mpr hnorm
  let : Nontrivial C := (nontrivial_iff_ne_bot _).mpr hcap
  let : Nontrivial (C.subgroupOf D) := (subgroupOfEquivOfLe hCD).toEquiv.nontrivial
  let : Fact (IsPGroup 2 D) := ⟨hD⟩
  obtain ⟨z, hz1, hzcent⟩ := exists_nontrivial_center_mem_normal (p := 2) (C.subgroupOf D)
  have hzC : ((z : D) : G) ∈ C := z.property
  have hzct : ((z : D) : G) ∈ centralizer ({t} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    exact (congrArg Subtype.val ((mem_center_iff.mp hzcent) ⟨t, htD⟩)).symm
  have hz1' : ((z : D) : G) ≠ 1 := fun he => hz1 (Subtype.ext (Subtype.ext he))
  have hne : C ⊓ centralizer ({t} : Set G) ≠ ⊥ := by
    intro he
    have hh : ((z : D) : G) ∈ C ⊓ centralizer ({t} : Set G) := ⟨hzC, hzct⟩
    rw [he, mem_bot] at hh
    exact hz1' hh
  have hlo : 1 < Nat.card (C ⊓ centralizer ({t} : Set G) : Subgroup G) :=
    Finite.one_lt_card_iff_nontrivial.mpr ((nontrivial_iff_ne_bot _).mpr hne)
  have hhi := l.intersection_centralizer_card_le_two h ha ha1 hg
  change Nat.card (C ⊓ centralizer ({t} : Set G) : Subgroup G) ≤ 2 at hhi
  change Nat.card (C ⊓ centralizer ({t} : Set G) : Subgroup G) = 2
  omega

theorem LocalControl.intersection_extension_centralizer_card_four
    (l : LocalControl S A₁ A₂) (h : Hypotheses S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha2 : orderOf a = 2)
    (hg : g ∉ intersectionGenerated A₁ A₂) (ht : g⁻¹ * a * g ∈ S)
    (hcap : A₁ ⊓ A₂ ≠ ⊥) :
    Nat.card (((A₁ ⊓ A₂) ⊔ zpowers (g⁻¹ * a * g)) ⊓
      centralizer ({g⁻¹ * a * g} : Set G) : Subgroup G) = 4 := by
  let t := g⁻¹ * a * g
  let C := A₁ ⊓ A₂
  let F := C ⊓ centralizer ({t} : Set G)
  have ha1 : a ≠ 1 := by intro he; simp [he] at ha2
  have ht2 : orderOf t = 2 := by
    simpa only [t, MulAut.conj_apply, inv_inv] using (MulAut.conj g⁻¹).orderOf_eq a |>.trans ha2
  have htsq : t ^ 2 = 1 := ht2 ▸ pow_orderOf_eq_one t
  have htout : t ∉ C := fun hh => hg (transporter_mem_intersectionGenerated ha ha1 (Or.inl hh.1))
  have hnorm : t ∈ normalizer (C : Set G) :=
    extension_normalizes_intersection (l.swap_of_outside_transporter h ha ha1 hg ht)
      ((le_sup_right : zpowers t ≤ C ⊔ zpowers t) (mem_zpowers t))
  have hnormF : t ∈ normalizer (F : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx.2
  change Nat.card ((C ⊔ zpowers t) ⊓ centralizer ({t} : Set G) : Subgroup G) = 4
  rw [centralizer_normalizing_join C t hnorm,
    card_sup_zpowers_of_normalizing_involution F t htsq (fun hh => htout hh.1) hnormF,
    l.intersection_centralizer_card_two h ha ha2 hg ht hcap]

/-- The unique fixed involution in the nontrivial factor intersection. -/
theorem LocalControl.exists_intersection_fixed_involution
    (l : LocalControl S A₁ A₂) (h : Hypotheses S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha2 : orderOf a = 2)
    (hg : g ∉ intersectionGenerated A₁ A₂) (ht : g⁻¹ * a * g ∈ S)
    (hcap : A₁ ⊓ A₂ ≠ ⊥) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ A₁ ⊓ A₂ ∧ Commute z (g⁻¹ * a * g) ∧
      (A₁ ⊓ A₂) ⊓ centralizer ({g⁻¹ * a * g} : Set G) = zpowers z := by
  let F := (A₁ ⊓ A₂) ⊓ centralizer ({g⁻¹ * a * g} : Set G)
  have hF : Nat.card F = 2 := l.intersection_centralizer_card_two h ha ha2 hg ht hcap
  let : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by rw [hF]; decide)
  obtain ⟨z, hz⟩ := exists_ne (1 : F)
  have hz1 : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
  have hz2 : orderOf (z : G) = 2 := by
    apply orderOf_eq_prime _ hz1
    have hh := pow_card_eq_one' (x := z)
    rw [hF] at hh
    exact congrArg Subtype.val hh
  refine ⟨z, hz2, z.property.1, mem_centralizer_singleton_iff.mp z.property.2, ?_⟩
  exact (eq_of_le_of_card_ge (zpowers_le.mpr z.property)
    (by rw [Nat.card_zpowers, hz2, hF])).symm

/-- The source extension is an actual dihedral or semidihedral two-group.
The central involution case is the four-group and is handled separately. -/
theorem LocalControl.intersection_extension_model
    (l : LocalControl S A₁ A₂) (h : Hypotheses S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha2 : orderOf a = 2)
    (hg : g ∉ intersectionGenerated A₁ A₂) (ht : g⁻¹ * a * g ∈ S)
    (hcap : A₁ ⊓ A₂ ≠ ⊥) :
    DihedralOrSemidihedral ((A₁ ⊓ A₂) ⊔ zpowers (g⁻¹ * a * g) : Subgroup G) := by
  let t := g⁻¹ * a * g
  let C := A₁ ⊓ A₂
  let D := C ⊔ zpowers t
  have ha1 : a ≠ 1 := by intro he; simp [he] at ha2
  have ht2 : orderOf t = 2 := by
    simpa only [t, MulAut.conj_apply, inv_inv] using (MulAut.conj g⁻¹).orderOf_eq a |>.trans ha2
  have htD : t ∈ D := (le_sup_right : zpowers t ≤ D) (mem_zpowers t)
  let td : D := ⟨t, htD⟩
  have htd2 : orderOf td = 2 := by simpa only [td, Subgroup.orderOf_mk] using ht2
  have htout : t ∉ C := fun hh => hg (transporter_mem_intersectionGenerated ha ha1 (Or.inl hh.1))
  have hDS : D ≤ (S : Subgroup G) := sup_le (inf_le_left.trans h.left_le) (zpowers_le.mpr ht)
  have hD : IsPGroup 2 D := S.isPGroup'.to_le hDS
  have hcard : Nat.card (centralizer ({td} : Set D)) = 4 := by
    rw [centralizer_subtype_card]
    exact l.intersection_extension_centralizer_card_four h ha ha2 hg ht hcap
  by_cases htz : td ∈ center D
  · have hCt : C ≤ centralizer ({t} : Set G) := by
      intro c hc
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val ((mem_center_iff.mp htz) ⟨c, (le_sup_left : C ≤ D) hc⟩)
    have hC2 : Nat.card C = 2 := by
      have hh := l.intersection_centralizer_card_two h ha ha2 hg ht hcap
      change Nat.card (C ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 at hh
      rwa [inf_eq_left.mpr hCt] at hh
    exact Or.inl ⟨1, le_rfl, small_dihedral_of_central_external_involution C t hC2
      (ht2 ▸ pow_orderOf_eq_one t) htout hCt⟩
  · rcases exists_dihedral_or_semidihedral_of_involution_centralizer_card_four hD td htd2 htz hcard with
      ⟨n, ⟨e⟩⟩ | ⟨n, hn, hDn, r, b, hr, hb, hconj, hgen⟩
    · obtain ⟨k, hk⟩ := (hD.of_equiv e).exists_orderOf_eq_pow (DihedralGroup.r 1)
      rw [DihedralGroup.orderOf_r_one] at hk
      have hlow := card_le_card_group (centralizer ({td} : Set D))
      rw [hcard, Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hk] at hlow
      have hkpos : 1 ≤ k := by
        by_contra he
        have hk0 : k = 0 := by omega
        simp [hk0] at hlow
      refine Or.inl ⟨k, hkpos, ?_⟩
      change Nonempty (D ≃* DihedralGroup (2 ^ k))
      rw [← hk]
      exact ⟨e⟩
    · exact Or.inr ⟨n, hn,
        Semidihedral.standardModel_equiv_of_presentation hn r b hr hb hconj hgen hDn⟩

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
