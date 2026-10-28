module
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.NormalFour.Preparation
public import Theory.GroupTheory.PGroup.OmegaImage
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Excluding an elementary projection inverse image

If the inverse image of omega were elementary, its order comparison with
omega of `S` would kill the central kernel and identify these subgroups.
Normality of `S` inside the finite two-group `C` makes omega meet `Z(C)`
nontrivially, contradicting the corrected central-intersection formula.
Thus the kernel is nontrivial. An explicit multiplication-coordinate
calculation also produces a lift in `L` whose nonidentity square is central.
The outer-index estimate then saturates the projection order inequalities.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Lemma 16.4.10, printed p.1193. These deductions do not assert the remaining
normal-four construction or the terminal TI/centrality argument.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {C L A S R : Subgroup G}

omit [Finite G] in
/-- Intersecting with an overgroup of all involutions preserves omega. -/
theorem omegaOneAmbient_eq_of_omega_le (hAR : A ≤ R) (hO : omegaOneAmbient R ≤ A) :
    omegaOneAmbient A = omegaOneAmbient R := by
  apply le_antisymm (omegaOneAmbient_mono hAR)
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro r hr hr2
  have hrO := (omegaOneAmbient_le_iff _ _).mp (le_refl (omegaOneAmbient R)) r hr hr2
  exact (omegaOneAmbient_le_iff _ _).mp le_rfl r (hO hrO) hr2

omit [Finite G] in
/-- The cardinal equality needed by the elementary-image comparison. -/
theorem omega_card_eq_of_inner (hAR : A ≤ R) (hO : omegaOneAmbient R ≤ A)
    (e : R ≃* S) : Nat.card (omega₁ A (p := 2)) = Nat.card (omega₁ S (p := 2)) := by
  have he := congrArg (fun Q : Subgroup G => Nat.card Q) (omegaOneAmbient_eq_of_omega_le hAR hO)
  change Nat.card ((omega₁ A (p := 2)).map A.subtype) =
    Nat.card ((omega₁ R (p := 2)).map R.subtype) at he
  rw [card_map_of_injective A.subtype_injective, card_map_of_injective R.subtype_injective] at he
  exact he.trans (Nat.card_congr (e.omega 2 1).toEquiv)

/-- The elementary-image case contradicts the nontrivial central intersection
of a normal subgroup of a finite two-group. -/
theorem Projection.not_elementary_inverseImage
    (h : ProjectionConfiguration C L A S) [(L.subgroupOf S).Normal]
    (π : Projection S L A) (hC : IsPGroup 2 C) (hSn : (S.subgroupOf C).Normal)
    (B : Subgroup A) (hcard : Nat.card B = Nat.card (omega₁ S (p := 2))) :
    ¬ IsElementaryAbelian 2 (π.inverseImage B) := by
  intro helem
  let : IsElementaryAbelian 2 (π.inverseImage B) := helem
  obtain ⟨hZ, he⟩ := π.elementary_inverseImage B hcard
  have hSne : S ≠ ⊥ := by
    intro hs
    have hc := π.card_mul_kernel_le
    have hcS : Nat.card S = 1 := hs ▸ card_bot
    rw [hcS] at hc
    have hpos : 0 < Nat.card (L.subgroupOf S) := Nat.card_pos
    have ha := A.one_lt_card_iff_ne_bot.mpr h.nontrivial
    nlinarith
  have hSp : IsPGroup 2 S := hC.to_le h.proper.le
  have hd : 2 ∣ Nat.card S := by
    rcases hSp.card_eq_or_dvd with hc | hc
    · exact (hSne (S.eq_bot_iff_card.mpr hc)).elim
    · exact hc
  let O := omegaOneAmbient S
  have hOC : O ≤ C := (omegaOneAmbient_le S).trans h.proper.le
  have hOne : O ≠ ⊥ := omega₁_map_subtype_ne_bot S 2 hd
  let : (omega₁ S (p := 2)).Characteristic := omega₁_characteristic S
  let : (O.subgroupOf C).Normal :=
    (normal_subgroupOf_iff_le_normalizer hOC).mpr
      (((normal_subgroupOf_iff_le_normalizer h.proper.le).mp hSn).trans
        (normalizer_le_normalizer_characteristic_image S (omega₁ S (p := 2))))
  have hO₀ne : O.subgroupOf C ≠ ⊥ := by
    intro hb
    apply hOne
    rw [← map_subgroupOf_eq_of_le hOC, hb, Subgroup.map_bot]
  have hcne := center_inf_ne_bot_of_normal hC (O.subgroupOf C) hO₀ne
  apply hcne
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨s, hs, hsex⟩ := hx.2
  change (s : G) = (x : G) at hsex
  have hsC : s ∈ (centralizer (C : Set G)).subgroupOf S := by
    apply mem_centralizer_iff.mpr
    intro c hc
    have hh := mem_center_iff.mp hx.1 (⟨c, hc⟩ : C)
    have hh' := congrArg C.subtype hh
    change c * (x : G) = (x : G) * c at hh'
    change c * (s : G) = (s : G) * c
    rw [hsex]
    exact hh'
  have hz : s ∈ L.subgroupOf S := by
    rw [← π.inverseImage_inf_centralizer h B]
    exact ⟨he.symm ▸ hs, hsC⟩
  rw [hZ] at hz
  have hs1 : s = 1 := mem_bot.mp hz
  exact Subtype.ext (hsex.symm.trans (by rw [hs1]; rfl))

/-- If the kernel were trivial, the inverse image of an elementary subgroup
in an abelian `S` would itself be elementary. Hence the source kernel is nontrivial. -/
theorem Projection.kernel_ne_bot
    (h : ProjectionConfiguration C L A S) [(L.subgroupOf S).Normal]
    (π : Projection S L A) (hC : IsPGroup 2 C) (hSn : (S.subgroupOf C).Normal)
    [IsMulCommutative S] (B : Subgroup A) [IsElementaryAbelian 2 B]
    (hcard : Nat.card B = Nat.card (omega₁ S (p := 2))) :
    L.subgroupOf S ≠ ⊥ := by
  intro hZ
  apply π.not_elementary_inverseImage h hC hSn B hcard
  refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
  intro s
  apply Subtype.ext
  have hs := s.property
  obtain ⟨a, ha, he⟩ := hs
  have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  have hs2 : (s : S) ^ 2 ∈ L.subgroupOf S := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (L.subgroupOf S)) ((s : S) ^ 2) = 1
    rw [map_pow, ← he, ← map_pow, ha2, map_one]
  rwa [hZ, mem_bot] at hs2

/-- Nontriviality of the central kernel turns the outer-index estimate into
all three source order equalities. -/
theorem Projection.saturation_of_inner
    (h : ProjectionConfiguration C L A S) [(L.subgroupOf S).Normal]
    (π : Projection S L A) (hC : IsPGroup 2 C) (hSn : (S.subgroupOf C).Normal)
    [IsMulCommutative R] (hAR : A ≤ R) (hO : omegaOneAmbient R ≤ A)
    (e : R ≃* S) (hindex : A.relIndex R ≤ 2) :
    Nat.card (L.subgroupOf S) = 2 ∧ Nat.card S = 2 * Nat.card A ∧
      π.inverseImage ⊤ = ⊤ := by
  let : IsMulCommutative A := IsMulCommutative.of_comm (fun a b =>
    Subtype.ext (setLike_mul_comm (s := R) (hAR a.property) (hAR b.property)))
  let : IsMulCommutative S := IsMulCommutative.of_comm (fun a b =>
    e.symm.injective (by simp only [map_mul, mul_comm]))
  let : IsElementaryAbelian 2 (omega₁ A (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative A
  have hne := π.kernel_ne_bot h hC hSn (omega₁ A (p := 2))
    (omega_card_eq_of_inner hAR hO e)
  exact π.order_saturation hAR hindex (Nat.card_congr e.symm.toEquiv)
    ((L.subgroupOf S).one_lt_card_iff_ne_bot.mpr hne)

omit [Finite G] in
/-- Membership in the full inverse image is equivalent to actual
multiplication coordinates, including the entire central kernel. -/
theorem Projection.mem_inverseImage_iff_factors
    (h : ProjectionConfiguration C L A S) [(L.subgroupOf S).Normal]
    (π : Projection S L A) (B : Subgroup A) (s : S) :
    s ∈ π.inverseImage B ↔ ∃ a : A, a ∈ B ∧ ∃ l : L, (s : G) * l = a := by
  constructor
  · rintro ⟨a, ha, he⟩
    have hf := h.factors_in_centralizer a.property
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right S L
      (h.proper.le.trans (h.centralizes.trans (centralizer_le_normalizer _)))] at hf
    obtain ⟨c, hc, l, hl, hcl⟩ := hf
    have hq : (QuotientGroup.mk s : S ⧸ L.subgroupOf S) = QuotientGroup.mk (⟨c, hc⟩ : S) :=
      he.symm.trans (π.on_factors a ⟨c, hc⟩ ⟨l, hl⟩ hcl)
    have hsc : (s : G)⁻¹ * c ∈ L :=
      (show s⁻¹ * (⟨c, hc⟩ : S) ∈ L.subgroupOf S from QuotientGroup.eq.mp hq)
    refine ⟨a, ha, ⟨(s : G)⁻¹ * c * l, L.mul_mem hsc hl⟩, ?_⟩
    change (s : G) * ((s : G)⁻¹ * c * l) = a
    simpa only [mul_assoc, mul_inv_cancel_left] using hcl
  · rintro ⟨a, ha, l, he⟩
    exact ⟨a, ha, π.on_factors a s l he⟩

/-- The nonelementary inverse image produces the actual nonsplit involution
lift used to exclude the `L₃(4)` cover. -/
theorem Projection.exists_nonsplit_lift
    (h : ProjectionConfiguration C L A S) [(L.subgroupOf S).Normal]
    (π : Projection S L A) (hC : IsPGroup 2 C) (hSn : (S.subgroupOf C).Normal)
    [IsMulCommutative S] (B : Subgroup A) [IsElementaryAbelian 2 B]
    (hcard : Nat.card B = Nat.card (omega₁ S (p := 2))) :
    ∃ l : L, l ^ 2 ∈ center L ∧ l ^ 2 ≠ 1 := by
  have hn := π.not_elementary_inverseImage h hC hSn B hcard
  have hex : ∃ s : π.inverseImage B, s ^ 2 ≠ 1 := by
    by_contra! hall
    exact hn ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hall⟩
  obtain ⟨s, hs⟩ := hex
  obtain ⟨a, ha, l, he⟩ := (π.mem_inverseImage_iff_factors h B s).mp s.property
  have ha2 : (a : G) ^ 2 = 1 :=
    congrArg A.subtype (elemPow_eq_one_of_isElementaryAbelian a ha)
  have hcomm : Commute ((s : S) : G) (l : G) :=
    (mem_centralizer_iff.mp (h.centralizes (h.proper.le (s : S).property)) l l.property).symm
  have hprod : ((s : S) : G) ^ 2 * (l : G) ^ 2 = 1 := by
    rw [← hcomm.mul_pow, he, ha2]
  have hsq : (l : G) ^ 2 = (((s : S) : G) ^ 2)⁻¹ :=
    eq_inv_of_mul_eq_one_right hprod
  refine ⟨l, ?_, ?_⟩
  · apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    change (x : G) * (l : G) ^ 2 = (l : G) ^ 2 * x
    rw [hsq]
    exact mem_centralizer_iff.mp
      ((centralizer (L : Set G)).inv_mem ((centralizer (L : Set G)).pow_mem
        (h.centralizes (h.proper.le (s : S).property)) 2)) x x.property
  · intro hl2
    have hl2G : (l : G) ^ 2 = 1 := congrArg L.subtype hl2
    rw [hl2G, mul_one] at hprod
    apply hs
    apply Subtype.ext
    apply Subtype.ext
    exact hprod

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry
