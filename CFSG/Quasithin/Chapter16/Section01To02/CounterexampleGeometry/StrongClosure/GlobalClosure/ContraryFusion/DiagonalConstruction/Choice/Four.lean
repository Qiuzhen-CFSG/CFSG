module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.DiagonalConstruction.Algebra
public import Theory.GroupTheory.PGroup.RootlessInvolutionFour

/-!
# The four-group in the literal diagonal image

The diagonal kernel is the intrinsic intersection A₂.subgroupOf A₁.
Its order two and the exclusion of the four-group factor model make the
image larger than two. A rootless involution in this image therefore belongs
to an actual Klein four. The image centralizes t, so rootlessness in C(t)
passes both to the image and to its marked preimage.

The two possible choices of a second generator preserve the same four.
A preimage with nontrivial square has order four because its square lies
in the order-two kernel. Clause (c) independently constructs the required
factor involution outside Hᵍ, and the fixed intersection excludes A₂.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, the diagonal comparison and the sentence “Then u² = z”.
These results feed the conditional choice assembly; they do not assert the
still-needed pair-action and Sylow-placement geometry.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
namespace DiagonalConstruction
variable {G : Type*} [Group G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- The intrinsic kernel has the same cardinality as the ambient intersection. -/
theorem intersection_subgroupOf_card
    (hcap : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2) :
    Nat.card (A₂.subgroupOf A₁) = 2 := by
  have hh := card_map_of_injective (K := A₂.subgroupOf A₁) A₁.subtype_injective
  rw [subgroupOf_map_subtype, inf_comm] at hh
  exact hh.symm.trans hcap

private theorem four_lt_card_of_rank_of_not_model
    {P : Type*} [Group P] [Finite P] (hrank : TwoRankAtLeastTwo P)
    (hmodel : ¬ DihedralOrSemidihedral P) : 4 < Nat.card P := by
  obtain ⟨E, hE, hsq⟩ := hrank
  have hle := card_le_card_group E
  rw [hE] at hle
  by_contra hn
  have hcard : Nat.card P = 4 := by omega
  have htop : E = ⊤ := E.eq_top_of_card_eq (hE.trans hcard.symm)
  have hsqP (x : P) : x ^ 2 = 1 :=
    congrArg Subtype.val (hsq ⟨x, htop ▸ mem_top x⟩)
  let : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour P := ⟨hcard,
    (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr
      (fun x hx => orderOf_eq_prime_iff.mpr ⟨hsqP x, hx⟩)⟩
  apply hmodel
  refine Or.inl ⟨1, le_rfl, ?_⟩
  change Nonempty (P ≃* DihedralGroup 2)
  exact IsKleinFour.nonempty_mulEquiv

/-- A diagonal image of order at most two would make the rank-two factor a Klein four. -/
theorem diagonal_range_card_gt_two [Finite G] (h : Hypotheses S A₁ A₂) {t : G}
    (hs : conjugate A₁ t = A₂ ∧ conjugate A₂ t = A₁)
    (hcap : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2)
    (hmodel : ¬ DihedralOrSemidihedral A₁) :
    2 < Nat.card (diagonalHom h hs.1).range := by
  let : (A₂.subgroupOf A₁).Normal := diagonalHom_ker h hs hcap ▸ inferInstance
  have hh := card_eq_card_quotient_mul_card_subgroup (A₂.subgroupOf A₁)
  rw [intersection_subgroupOf_card hcap,
    Nat.card_congr (quotientDiagonalEquiv h hs hcap).toEquiv] at hh
  have hgt := four_lt_card_of_rank_of_not_model h.left_rank hmodel
  omega

/-- An involution outside the kernel has an involutory diagonal image. -/
theorem diagonal_involution (h : Hypotheses S A₁ A₂) {t v : G}
    (hs : conjugate A₁ t = A₂ ∧ conjugate A₂ t = A₁)
    (hcap : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2)
    (hv : v ∈ A₁) (hv2 : orderOf v = 2) (hvout : v ∉ A₂) :
    orderOf (v * (t⁻¹ * v * t)) = 2 := by
  let f := diagonalHom h hs.1
  have hne : f ⟨v, hv⟩ ≠ 1 := by
    intro he
    have hm : (⟨v, hv⟩ : A₁) ∈ f.ker := he
    rw [diagonalHom_ker h hs hcap] at hm
    exact hvout hm
  apply orderOf_eq_prime _ hne
  change f ⟨v, hv⟩ ^ 2 = 1
  rw [← map_pow]
  have hvpow : (⟨v, hv⟩ : A₁) ^ 2 = 1 := by
    apply Subtype.ext
    exact (orderOf_eq_prime_iff.mp hv2).1
  rw [hvpow, map_one]

/-- A square root in the factor would map to a square root in C(t). -/
theorem diagonal_preimage_rootless (h : Hypotheses S A₁ A₂) {t v : G}
    (hs : conjugate A₁ t = A₂) (ht : orderOf t = 2) (hv : v ∈ A₁)
    (hroot : ∀ w ∈ centralizer ({t} : Set G), w ^ 2 ≠ v * (t⁻¹ * v * t)) :
    ∀ w ∈ A₁, w ^ 2 ≠ v := by
  intro w hw he
  let f := diagonalHom h hs
  apply hroot (f ⟨w, hw⟩) (diagonal_range_centralizes h hs ht ⟨⟨w, hw⟩, rfl⟩)
  change f ⟨w, hw⟩ ^ 2 = f ⟨v, hv⟩
  rw [← map_pow]
  apply congrArg f
  exact Subtype.ext he

/-- The literal diagonal image supplies a second generator for a Klein four through vvᵗ. -/
theorem diagonal_image_four_of_rootless [Finite G] (h : Hypotheses S A₁ A₂) {t v : G}
    (hs : conjugate A₁ t = A₂ ∧ conjugate A₂ t = A₁) (ht : orderOf t = 2)
    (hcap : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2)
    (hmodel : ¬ DihedralOrSemidihedral A₁)
    (hv : v ∈ A₁) (hv2 : orderOf v = 2) (hvout : v ∉ A₂)
    (hroot : ∀ w ∈ centralizer ({t} : Set G), w ^ 2 ≠ v * (t⁻¹ * v * t)) :
    ∃ u ∈ A₁, orderOf (u * (t⁻¹ * u * t)) = 2 ∧
      IsKleinFour (closure ({v * (t⁻¹ * v * t), u * (t⁻¹ * u * t)} : Set G)) := by
  let f := diagonalHom h hs.1
  let x : f.range := ⟨f ⟨v, hv⟩, ⟨⟨v, hv⟩, rfl⟩⟩
  have hp : IsPGroup 2 f.range :=
    (S.isPGroup'.to_le h.left_le).of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hx2 : orderOf x = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact diagonal_involution h hs hcap hv hv2 hvout
  have hxroot (w : f.range) : w ^ 2 ≠ x := by
    intro he
    exact hroot w (diagonal_range_centralizes h hs.1 ht w.property)
      (congrArg Subtype.val he)
  obtain ⟨y, hy2, hxy, hcomm⟩ := hp.exists_commuting_involution_of_rootless
    (diagonal_range_card_gt_two h hs hcap hmodel) x hx2 hxroot
  obtain ⟨u, hu⟩ := y.property
  have hy2' : orderOf (y : G) = 2 := (Subgroup.orderOf_coe y).trans hy2
  have hxy' : (x : G) ≠ y := fun he => hxy (Subtype.ext he)
  have hcomm' : Commute (x : G) (y : G) := congrArg Subtype.val hcomm.eq
  refine ⟨u, u.property, ?_, ?_⟩
  · change orderOf (f u) = 2
    rw [hu]
    exact hy2'
  · have hfour := isKleinFour_closure_pair_of_orderOf (x : G) (y : G)
      ((Subgroup.orderOf_coe x).trans hx2) hy2' hxy' hcomm'
    change IsKleinFour (closure ({(x : G), f u} : Set G))
    rwa [hu]

/-- A noninvolutory lift of a diagonal involution has order four. -/
theorem diagonal_preimage_order_four (h : Hypotheses S A₁ A₂) {t u : G}
    (hs : conjugate A₁ t = A₂ ∧ conjugate A₂ t = A₁)
    (hcap : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2)
    (hu : u ∈ A₁) (hy : orderOf (u * (t⁻¹ * u * t)) = 2) (hu2 : u ^ 2 ≠ 1) :
    orderOf u = 4 := by
  let f := diagonalHom h hs.1
  have hker : (⟨u, hu⟩ : A₁) ^ 2 ∈ f.ker := by
    change f ((⟨u, hu⟩ : A₁) ^ 2) = 1
    rw [map_pow]
    exact (orderOf_eq_prime_iff.mp hy).1
  rw [diagonalHom_ker h hs hcap] at hker
  have hcapU : u ^ 2 ∈ A₁ ⊓ A₂ := ⟨A₁.pow_mem hu 2, hker⟩
  have hu4 : u ^ 4 = 1 := by
    have hh : (⟨u ^ 2, hcapU⟩ : (A₁ ⊓ A₂ : Subgroup G)) ^ 2 = 1 := by
      simpa only [hcap] using
        (pow_card_eq_one' (x := (⟨u ^ 2, hcapU⟩ : (A₁ ⊓ A₂ : Subgroup G))))
    have hh' : (u ^ 2) ^ 2 = 1 := congrArg Subtype.val hh
    simpa only [← pow_mul] using hh'
  have hd : orderOf u ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one hu4
  obtain ⟨n, hn, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases n
  · have hh := pow_orderOf_eq_one u
    rw [he] at hh
    simp only [pow_zero, pow_one] at hh
    exact (hu2 (by rw [hh]; simp)).elim
  · exact (hu2 (by simpa only [he, pow_one] using pow_orderOf_eq_one u)).elim
  · exact he

/-- Replacing u by vu chooses the third nonidentity element of the same diagonal four. -/
theorem diagonal_four_replace (h : Hypotheses S A₁ A₂) {t v u u' : G}
    (hs : conjugate A₁ t = A₂) (hv : v ∈ A₁) (hu : u ∈ A₁)
    (hx : orderOf (v * (t⁻¹ * v * t)) = 2)
    (hy : orderOf (u * (t⁻¹ * u * t)) = 2)
    (hfour : IsKleinFour (closure
      ({v * (t⁻¹ * v * t), u * (t⁻¹ * u * t)} : Set G)))
    (hu' : u' ∈ ({u, v * u} : Set G)) :
    u' ∈ A₁ ∧ orderOf (u' * (t⁻¹ * u' * t)) = 2 ∧
      IsKleinFour (closure ({v * (t⁻¹ * v * t), u' * (t⁻¹ * u' * t)} : Set G)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu'
  rcases hu' with rfl | rfl
  · exact ⟨hu, hy, hfour⟩
  let f := diagonalHom h hs
  let x := v * (t⁻¹ * v * t)
  let y := u * (t⁻¹ * u * t)
  have hprod : (v * u) * (t⁻¹ * (v * u) * t) = x * y :=
    f.map_mul ⟨v, hv⟩ ⟨u, hu⟩
  have hclosure : closure ({x, x * y} : Set G) = closure ({x, y} : Set G) := by
    apply le_antisymm
    · apply (closure_le _).mpr
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact subset_closure (by simp)
      · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    · apply (closure_le _).mpr
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact subset_closure (by simp)
      · have hh := (closure ({x, x * y} : Set G)).mul_mem
          ((closure ({x, x * y} : Set G)).inv_mem (subset_closure (by simp : x ∈ ({x, x * y} : Set G))))
          (subset_closure (by simp : x * y ∈ ({x, x * y} : Set G)))
        change y ∈ closure ({x, x * y} : Set G)
        simpa only [inv_mul_cancel_left] using hh
  have hxyne : x * y ≠ 1 := by
    intro he
    have hc : closure ({x, x * y} : Set G) = zpowers x := by
      rw [he, Set.pair_comm, closure_insert_one, ← zpowers_eq_closure]
    let := hfour
    have hh : Nat.card (closure ({x, y} : Set G)) = 4 := IsKleinFour.card_four
    rw [← hclosure, hc, Nat.card_zpowers, hx] at hh
    omega
  let := hfour
  have hm : x * y ∈ closure ({x, y} : Set G) :=
    mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  have hsquare : (x * y) ^ 2 = 1 := by
    simpa [pow_two] using congrArg Subtype.val
      (IsKleinFour.mul_self (⟨x * y, hm⟩ : closure ({x, y} : Set G)))
  refine ⟨A₁.mul_mem hv hu, ?_, ?_⟩
  · rw [hprod]
    exact orderOf_eq_prime hsquare hxyne
  · rw [hprod, hclosure]
    exact hfour


/-- The centralizer of a contrary conjugate lies in the corresponding
conjugate of H, with the original right-conjugation convention. -/
theorem contrary_centralizer_le_conjugate (h : Hypotheses S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha1 : a ≠ 1) :
    centralizer ({g⁻¹ * a * g} : Set G) ≤
      conjugate (intersectionGenerated A₁ A₂) g := by
  intro w hw
  apply mem_map.mpr
  refine ⟨g * w * g⁻¹, h.centralizer_le_generated ha ha1 ?_, ?_⟩
  · apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp hw)
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · simp [mul_assoc]

/-- Clause (c) selects an involution outside the actual conjugate of H.
Its exclusion from the opposite factor follows separately from the
order-two intersection. -/
theorem exists_left_involution_outside_conjugate [Finite G]
    (h : Hypotheses S A₁ A₂) (l : LocalControl S A₁ A₂)
    {g : G} (hg : g ∉ intersectionGenerated A₁ A₂) :
    ∃ v ∈ A₁, orderOf v = 2 ∧ v ∉ conjugate (intersectionGenerated A₁ A₂) g := by
  obtain ⟨E, hE, hsq⟩ := h.left_rank
  let X := E.map A₁.subtype
  have hX : X ≤ A₁ := by
    rintro _ ⟨v, _, rfl⟩
    exact v.property
  have hXcard : Nat.card X = 4 :=
    (card_map_of_injective A₁.subtype_injective).trans hE
  have hnle : ¬ X ≤ conjugate (intersectionGenerated A₁ A₂) g := by
    intro hh
    have hconj := map_mono (f := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom) hh
    change conjugate X g⁻¹ ≤
      conjugate (conjugate (intersectionGenerated A₁ A₂) g) g⁻¹ at hconj
    rw [conjugate_conjugate, mul_inv_cancel, conjugate_one] at hconj
    have hginv := ((l.unique_large X (Or.inl hX) (by omega)).2 g⁻¹).mp hconj
    exact hg ((intersectionGenerated A₁ A₂).inv_mem_iff.mp hginv)
  obtain ⟨v, hvX, hvout⟩ := SetLike.not_le_iff_exists.mp hnle
  have hvne : v ≠ 1 := fun he => hvout (he ▸ (conjugate _ g).one_mem)
  obtain ⟨w, hw, rfl⟩ := hvX
  have hw2 : (w : G) ^ 2 = 1 :=
    congrArg (fun z : E => ((z : A₁) : G)) (hsq ⟨w, hw⟩)
  exact ⟨w, w.property, orderOf_eq_prime hw2 hvne, hvout⟩

/-- The order-two intersection is fixed by t and hence lies in Hᵍ. -/
theorem outside_conjugate_not_mem_right (h : Hypotheses S A₁ A₂)
    {a g v : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha1 : a ≠ 1)
    (hs : conjugate A₁ (g⁻¹ * a * g) = A₂ ∧ conjugate A₂ (g⁻¹ * a * g) = A₁)
    (hcap : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2)
    (hv : v ∈ A₁) (hvout : v ∉ conjugate (intersectionGenerated A₁ A₂) g) :
    v ∉ A₂ := by
  intro hv2
  apply hvout
  apply contrary_centralizer_le_conjugate h ha ha1
  apply mem_centralizer_singleton_iff.mpr
  have hh := intersection_fixed hs hcap ⟨hv, hv2⟩
  have hh' := congrArg (fun w => (g⁻¹ * a * g) * w) hh
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh'


end DiagonalConstruction
end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
