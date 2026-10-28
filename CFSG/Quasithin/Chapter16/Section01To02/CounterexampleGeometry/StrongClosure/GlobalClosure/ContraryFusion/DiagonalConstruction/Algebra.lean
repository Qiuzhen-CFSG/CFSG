module
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.IntersectionBounds
public import Theory.GroupTheory.SemidihedralCenter

/-!
# Algebra and centralizer geometry of the source diagonal

For commuting factors exchanged by an involution, the map a ↦ a aᵗ is a
homomorphism into C_G(t). When the intersection has order two, its kernel
is precisely A₁ ∩ A₂, giving the actual quotient comparison on printed p.95.
An order-four preimage lies in the center of its restricted factor, excluding
the dihedral and semidihedral models there. Its order also proves both
nonnesting conditions. Clause (c) bounds fixed points in an outside conjugate
when a diagonal centralizer lies in H.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, the paragraph ending “Thus y ∈ Z(G)”.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
variable {G : Type*} [Group G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

namespace DiagonalConstruction

theorem factors_commute (h : Hypotheses S A₁ A₂)
    {a b : G} (ha : a ∈ A₁) (hb : b ∈ A₂) : Commute a b :=
  (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h.commute ha) b hb).symm

theorem conjugate_mem {t x : G} (hs : conjugate A₁ t = A₂) (hx : x ∈ A₁) :
    t⁻¹ * x * t ∈ A₂ := by
  rw [← hs]
  exact mem_map.mpr ⟨x, hx, by simp⟩

/-- The source diagonal map, with its actual right-conjugation formula. -/
def diagonalHom (h : Hypotheses S A₁ A₂) {t : G}
    (hs : conjugate A₁ t = A₂) : A₁ →* G where
  toFun x := (x : G) * (t⁻¹ * (x : G) * t)
  map_one' := by simp
  map_mul' x y := by
    have hc := factors_commute h y.property (conjugate_mem hs x.property)
    change ((x : G) * y) * (t⁻¹ * ((x : G) * y) * t) = _
    calc
      _ = (x : G) * ((y : G) * (t⁻¹ * (x : G) * t)) * (t⁻¹ * (y : G) * t) := by group
      _ = (x : G) * ((t⁻¹ * (x : G) * t) * (y : G)) * (t⁻¹ * (y : G) * t) := by rw [hc.eq]
      _ = _ := by group

@[simp] theorem diagonalHom_apply (h : Hypotheses S A₁ A₂) {t : G}
    (hs : conjugate A₁ t = A₂) (x : A₁) :
    diagonalHom h hs x = (x : G) * (t⁻¹ * (x : G) * t) := rfl

theorem intersection_fixed {t : G}
    (hs : conjugate A₁ t = A₂ ∧ conjugate A₂ t = A₁)
    (hcap : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2)
    {x : G} (hx : x ∈ A₁ ⊓ A₂) : t⁻¹ * x * t = x := by
  by_cases hx1 : x = 1
  · simp [hx1]
  have htx : t⁻¹ * x * t ∈ A₁ ⊓ A₂ :=
    ⟨conjugate_mem hs.2 hx.2, conjugate_mem hs.1 hx.1⟩
  have he : (⟨t⁻¹ * x * t, htx⟩ : (A₁ ⊓ A₂ : Subgroup G)) = ⟨x, hx⟩ := by
    apply ((Nat.card_eq_two_iff' (1 : (A₁ ⊓ A₂ : Subgroup G))).mp hcap).unique
    · intro he
      have hh : t⁻¹ * x * t = 1 := congrArg Subtype.val he
      apply hx1
      have hh' := congrArg (MulAut.conj t) hh
      simpa [MulAut.conj_apply, mul_assoc] using hh'
    · exact fun he => hx1 (congrArg Subtype.val he)
  exact congrArg Subtype.val he

theorem diagonalHom_ker (h : Hypotheses S A₁ A₂) {t : G}
    (hs : conjugate A₁ t = A₂ ∧ conjugate A₂ t = A₁)
    (hcap : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2) :
    (diagonalHom h hs.1).ker = A₂.subgroupOf A₁ := by
  ext x
  change (x : G) * (t⁻¹ * (x : G) * t) = 1 ↔ (x : G) ∈ A₂
  constructor
  · intro he
    rw [eq_inv_of_mul_eq_one_left he]
    exact A₂.inv_mem (conjugate_mem hs.1 x.property)
  · intro hx
    rw [intersection_fixed hs hcap ⟨x.property, hx⟩, ← pow_two]
    exact congrArg (fun z : (A₁ ⊓ A₂ : Subgroup G) => (z : G))
      (show (⟨x, x.property, hx⟩ : (A₁ ⊓ A₂ : Subgroup G)) ^ 2 = 1 from
        hcap ▸ pow_card_eq_one')

/-- The kernel identification makes this the literal quotient by A₁ ∩ A₂. -/
noncomputable def quotientDiagonalEquiv (h : Hypotheses S A₁ A₂) {t : G}
    (hs : conjugate A₁ t = A₂ ∧ conjugate A₂ t = A₁)
    (hcap : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2) :
    letI : (A₂.subgroupOf A₁).Normal := diagonalHom_ker h hs hcap ▸ inferInstance
    A₁ ⧸ A₂.subgroupOf A₁ ≃* (diagonalHom h hs.1).range := by
  letI : (A₂.subgroupOf A₁).Normal := diagonalHom_ker h hs hcap ▸ inferInstance
  exact (QuotientGroup.quotientMulEquivOfEq (diagonalHom_ker h hs hcap).symm).trans
    (QuotientGroup.quotientKerEquivRange _)

theorem diagonal_range_centralizes (h : Hypotheses S A₁ A₂) {t : G}
    (hs : conjugate A₁ t = A₂) (ht : orderOf t = 2) :
    (diagonalHom h hs).range ≤ centralizer ({t} : Set G) := by
  rintro _ ⟨x, rfl⟩
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left
    (by simpa only [pow_two] using (orderOf_eq_prime_iff.mp ht).1)
  apply mem_centralizer_singleton_iff.mpr
  have hc := factors_commute h x.property (conjugate_mem hs x.property)
  have he : t⁻¹ * diagonalHom h hs x * t = diagonalHom h hs x := by
    change t⁻¹ * ((x : G) * (t⁻¹ * (x : G) * t)) * t = _
    calc
      _ = (t⁻¹ * (x : G) * t) * (x : G) := by
        rw [hti]
        have htt : t * t = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp ht).1
        simp [mul_assoc, htt]
      _ = _ := hc.eq.symm
  have he' := congrArg (fun z => t * z) he
  simpa [mul_assoc] using he'


/-- The centers of the two exceptional models have exponent at most two. -/
theorem model_center_sq {P : Type*} [Group P] (hm : DihedralOrSemidihedral P)
    (x : P) (hx : x ∈ center P) : x ^ 2 = 1 := by
  have transport {Q : Type} [Group Q] (e : P ≃* Q) : e x ∈ center Q := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx y)
  rcases hm with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · apply e.injective
    rw [map_pow, map_one]
    have hh := mem_center_iff.mp (transport e) (DihedralGroup.sr 0)
    cases he : e x with
    | sr i => simp [pow_two]
    | r i =>
      rw [he] at hh
      have hi : i = -i := by simpa using hh
      have hii : i + i = 0 := eq_neg_iff_add_eq_zero.mp hi
      simp [pow_two, hii]
  · apply e.injective
    rw [map_pow, map_one]
    have hh := transport e
    rw [Semidihedral.center_eq hn (Semidihedral.standardRotation n hn)
      (Semidihedral.standardReflection n hn) (Semidihedral.standardRotation_order n hn)
      (Semidihedral.standardReflection_order n hn) (Semidihedral.standard_conjugation n hn)
      (Semidihedral.standard_generators n hn)] at hh
    obtain ⟨k, hk⟩ := hh
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul]
    have hs : ((Semidihedral.standardRotation n hn) ^ (2 ^ (n - 2))) ^ (2 : ℤ) = 1 := by
      rw [zpow_ofNat, ← pow_mul]
      have he : 2 ^ (n - 2) * 2 = 2 ^ (n - 1) := by
        rw [← pow_succ]; congr 1; omega
      rw [he]
      simpa only [Semidihedral.standardRotation_order] using
        pow_orderOf_eq_one (Semidihedral.standardRotation n hn)
    change (((Semidihedral.standardRotation n hn) ^ (2 ^ (n - 2))) ^ (2 : ℤ)) ^ k = 1
    rw [hs, one_zpow]

/-- The order-four preimage lies in the center of its restricted factor. -/
theorem diagonal_preimage_central (h : Hypotheses S A₁ A₂) {t u : G}
    (hs : conjugate A₁ t = A₂) (hu : u ∈ A₁) :
    ∃ huK : u ∈ centralizer ({u * (t⁻¹ * u * t)} : Set G),
      (⟨⟨u, huK⟩, hu⟩ : A₁.subgroupOf (centralizer ({u * (t⁻¹ * u * t)} : Set G)))
        ∈ center (A₁.subgroupOf (centralizer ({u * (t⁻¹ * u * t)} : Set G))) := by
  have hv := conjugate_mem hs hu
  have hc := factors_commute h hu hv
  refine ⟨mem_centralizer_singleton_iff.mpr ((Commute.refl u).mul_right hc).eq, ?_⟩
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  apply Subtype.ext
  have hh : Commute ((x : centralizer ({u * (t⁻¹ * u * t)} : Set G)) : G)
      (u * (t⁻¹ * u * t)) := mem_centralizer_singleton_iff.mp x.val.property
  have hxv := factors_commute h x.property hv
  have hh' := hh.mul_right hxv.inv_right
  change (x.val.val : G) * u = u * (x.val.val : G)
  simpa only [mul_inv_cancel_right] using hh'.eq

theorem diagonal_local_not_model (h : Hypotheses S A₁ A₂) {t u : G}
    (hs : conjugate A₁ t = A₂) (hu : u ∈ A₁) (hu4 : orderOf u = 4) :
    ¬ DihedralOrSemidihedral
      (A₁.subgroupOf (centralizer ({u * (t⁻¹ * u * t)} : Set G))) := by
  obtain ⟨huK, huc⟩ := diagonal_preimage_central h hs hu
  intro hm
  have hh := model_center_sq hm _ huc
  have hu2 : u ^ 2 = 1 := congrArg
    (fun x : A₁.subgroupOf (centralizer ({u * (t⁻¹ * u * t)} : Set G)) => ((x : _) : G)) hh
  have hd := orderOf_dvd_of_pow_eq_one hu2
  rw [hu4] at hd
  norm_num at hd

theorem diagonal_nonnesting [Finite G] (h : Hypotheses S A₁ A₂) {t u : G}
    (hs : conjugate A₁ t = A₂) (hu : u ∈ A₁) (hu4 : orderOf u = 4)
    (hcap : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2) :
    (¬ A₁ ⊓ centralizer ({u * (t⁻¹ * u * t)} : Set G) ≤ A₂) ∧
    (¬ A₂ ⊓ centralizer ({u * (t⁻¹ * u * t)} : Set G) ≤ A₁) := by
  have hv := conjugate_mem hs hu
  have hv4 : orderOf (t⁻¹ * u * t) = 4 := by
    simpa only [MulAut.conj_apply, inv_inv] using (MulAut.conj t⁻¹).orderOf_eq u |>.trans hu4
  have hc := factors_commute h hu hv
  have huc := mem_centralizer_singleton_iff.mpr ((Commute.refl u).mul_right hc).eq
  have hvc := mem_centralizer_singleton_iff.mpr (hc.symm.mul_right (Commute.refl _)).eq
  have nofour (x : G) (hx : x ∈ A₁ ⊓ A₂) (hx4 : orderOf x = 4) : False := by
    have hd := orderOf_dvd_natCard (⟨x, hx⟩ : (A₁ ⊓ A₂ : Subgroup G))
    rw [← Subgroup.orderOf_coe, hx4, hcap] at hd
    norm_num at hd
  exact ⟨fun hn => nofour u ⟨hu, hn ⟨hu, huc⟩⟩ hu4,
    fun hn => nofour _ ⟨hn ⟨hv, hvc⟩, hv⟩ hv4⟩


theorem rank_of_equiv {P Q : Type*} [Group P] [Group Q]
    (e : P ≃* Q) (h : TwoRankAtLeastTwo P) : TwoRankAtLeastTwo Q := by
  obtain ⟨E, hE, hs⟩ := h
  refine ⟨E.map e.toMonoidHom, (card_map_of_injective e.injective).trans hE, ?_⟩
  intro x
  obtain ⟨v, hv, he⟩ := x.property
  apply Subtype.ext
  change (x : Q) ^ 2 = 1
  rw [← he, ← map_pow]
  have hv2 : v ^ 2 = 1 := congrArg Subtype.val (hs ⟨v, hv⟩)
  rw [hv2, map_one]

theorem model_of_equiv {P Q : Type*} [Group P] [Group Q]
    (e : P ≃* Q) (h : DihedralOrSemidihedral Q) : DihedralOrSemidihedral P := by
  rcases h with ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩
  · exact Or.inl ⟨n, hn, ⟨e.trans f⟩⟩
  · exact Or.inr ⟨n, hn, ⟨e.trans f⟩⟩

/-- Clause (c) bounds fixed points in an outside conjugate when C(y) lies in H. -/
theorem outside_fixed_card [Finite G] (l : LocalControl S A₁ A₂)
    {A : Subgroup G} (hA : A ≤ A₁ ∨ A ≤ A₂) {k y : G}
    (hk : k ∉ intersectionGenerated A₁ A₂)
    (hC : centralizer ({y} : Set G) ≤ intersectionGenerated A₁ A₂) :
    Nat.card (conjugate A k ⊓ centralizer ({y} : Set G) : Subgroup G) ≤ 2 := by
  by_contra hn
  let X := conjugate (conjugate A k ⊓ centralizer ({y} : Set G)) k⁻¹
  have hXA : X ≤ A := by
    have hh := map_mono (f := (MulAut.conj (k⁻¹)⁻¹).toMonoidHom)
      (show conjugate A k ⊓ centralizer ({y} : Set G) ≤ conjugate A k from inf_le_left)
    change X ≤ conjugate (conjugate A k) k⁻¹ at hh
    simpa only [conjugate_conjugate, mul_inv_cancel, conjugate_one] using hh
  have hcard : 2 < Nat.card X := by
    change 2 < Nat.card ((conjugate A k ⊓ centralizer ({y} : Set G)).map _)
    rw [card_map_of_injective (MulAut.conj (k⁻¹)⁻¹).injective]
    omega
  have hh : conjugate X k ≤ intersectionGenerated A₁ A₂ := by
    dsimp [X]
    rw [conjugate_conjugate, inv_mul_cancel, conjugate_one]
    exact inf_le_right.trans hC
  exact hk (((l.unique_large X (hA.imp (hXA.trans ·) (hXA.trans ·)) hcard).2 k).mp hh)

end DiagonalConstruction
end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
