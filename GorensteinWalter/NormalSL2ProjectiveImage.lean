module
public import GorensteinWalter.SL2ProjectiveCover
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Normal SL2 images in central Sylow quotients

If a normal subgroup M of a finite group is SL2 over an odd field, and a
central normal subgroup N contains the center image of a Sylow two-subgroup,
then the actual image of M in G/N is the corresponding PSL2 group. The center
of M has order two; the generic normal center-image theorem identifies the
image with M/Z(M), and the given equivalence transports this central quotient.
The canonical variant retains the element equation through the supplied SL2
identification, while the original Nonempty theorem remains a wrapper. This
equation aligns the prescribed projective-core action in II.3 Proposition 3.

This is the shared quotient calculation in ABG II.3 Proposition2 and Lemma2,
article pp22--24. Extracted from the previously proved NormalSL2 assembly,
it includes field order three and requires no perfectness. The Sylow-center
image is written directly, with no campaign predicate in the public API.
-/

namespace GorensteinWalter

private theorem odd_card_of_odd_prime_power {q : ℕ} (hq : IsOddPrimePower q) : Odd q := by
  obtain ⟨p, n, _, hp, _, rfl⟩ := hq
  exact hp.pow

public theorem exists_normal_sl2_projective_image
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (N M : Subgroup G) [N.Normal] [M.Normal]
    (hNcentral : N ≤ Subgroup.center G)
    (hSN : (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype ≤ N)
    (F : Type*) [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (e : M ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ eImage : M.map (QuotientGroup.mk' N) ≃* PSL2 F,
      ∀ m : M, eImage ⟨QuotientGroup.mk' N m.val, ⟨m.val, m.property, rfl⟩⟩ =
        sl2ProjectiveProjection F (e m) := by
  have hcenter : Nat.card (Subgroup.center M) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    rw [← sl2ProjectiveProjection_ker F]
    exact sl2ProjectiveProjection_ker_card F (odd_card_of_odd_prime_power hF)
  obtain ⟨eimage, heimage⟩ := Subgroup.exists_normal_center_quotient_image_equiv S N M
    hNcentral hSN hcenter
  have hecenter : (Subgroup.center M).map e.toMonoidHom =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Subgroup.centerCongr e ⟨x, hx⟩).property
    · intro hy
      exact ⟨e.symm y, (Subgroup.centerCongr e.symm ⟨y, hy⟩).property,
        e.apply_symm_apply y⟩
  refine ⟨eimage.trans (QuotientGroup.congr _ _ e hecenter), ?_⟩
  intro m
  change (QuotientGroup.congr _ _ e hecenter)
    (eimage ⟨QuotientGroup.mk' N m.val, ⟨m.val, m.property, rfl⟩⟩) = _
  rw [heimage]
  rfl

public theorem normal_sl2_projective_image
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (N M : Subgroup G) [N.Normal] [M.Normal]
    (hNcentral : N ≤ Subgroup.center G)
    (hSN : (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype ≤ N)
    (F : Type*) [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (e : M ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Nonempty (M.map (QuotientGroup.mk' N) ≃* PSL2 F) := by
  obtain ⟨eImage, _⟩ := exists_normal_sl2_projective_image S N M hNcentral hSN F hF e
  exact ⟨eImage⟩

end GorensteinWalter
