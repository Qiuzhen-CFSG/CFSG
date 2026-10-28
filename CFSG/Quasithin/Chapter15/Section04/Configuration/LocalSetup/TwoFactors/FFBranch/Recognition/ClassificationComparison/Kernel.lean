module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ActionGroup
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.SeedCriterion
public import Theory.GroupTheory.PPrimeCoreSurjection

/-!
# Comparing the Goldschmidt and representation kernels

F.6.18 classifies the quotient by the three-prime core, whereas the actual
module has kernel the two-core. These are kept distinct. F.6.11 makes the
three-prime-core image odd; the two-group quotient by the offender group
then puts that image inside the offender group. If classification gives a
trivial three-prime core there, the two kernels coincide. The last premise
is an outstanding classification obligation, not a conclusion of this module.

The equivalence of the two quotient groups is the canonical map on original
elements, so it also preserves the local subgroup images.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, F.6.11, printed pp.306–307, and 15.4.18, p.1163.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
variable {H D : Type*} [Group H] [Finite H] [Group D]

private theorem coprime_card_range_of_sylow_killed (f : H →* D) (S : Sylow 2 H)
    (hS : (S : Subgroup H) ≤ f.ker) : Nat.Coprime 2 (Nat.card f.range) := by
  rw [← Subgroup.index_ker]
  exact (Nat.prime_two.coprime_iff_not_dvd.mpr S.not_dvd_index).of_dvd_right
    (Subgroup.index_dvd_of_le hS)

omit [Finite H] in
private theorem le_of_quotient_twoGroup (N R : Subgroup H) [N.Normal]
    (hq : IsPGroup 2 (H ⧸ N)) (hR : Nat.Coprime 2 (Nat.card R)) : R ≤ N := by
  intro r hr
  apply (QuotientGroup.eq_one_iff r).mp
  apply orderOf_eq_one_iff.mp
  obtain ⟨k, hk⟩ := hq.exists_orderOf_eq_pow (QuotientGroup.mk' N r)
  exact Nat.eq_one_of_dvd_coprimes (hR.pow_left k)
    (hk ▸ dvd_refl _) ((orderOf_map_dvd (QuotientGroup.mk' N) r).trans
      (R.orderOf_dvd_natCard hr))

/-- The two-core is a normal subgroup of order prime to three. -/
theorem twoCore_le_threePrimeCore : pCore 2 H ≤ pPrimeCore 3 H := by
  apply le_sSup
  refine ⟨inferInstance, ?_⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := 2) (G := H))
  rw [hk]
  exact (by decide : Nat.Coprime 3 2).pow_right k

/-- Equality of the source and action kernels is equivalent to triviality
of the three-prime core of the full action quotient. -/
theorem threePrimeCore_eq_twoCore_iff :
    pPrimeCore 3 H = pCore 2 H ↔ pPrimeCore 3 (coreQuotient H) = ⊥ := by
  have hc : Nat.Coprime 3 (Nat.card (coreProjection (H := H)).ker) := by
    rw [coreProjection, QuotientGroup.ker_mk']
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := 2) (G := H))
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have he := pPrimeCore_comap_eq_of_surjective_coprime 3
    (coreProjection (H := H)) (QuotientGroup.mk'_surjective _) hc
  constructor
  · intro h
    apply comap_injective (QuotientGroup.mk'_surjective (pCore 2 H))
    change (pPrimeCore 3 (coreQuotient H)).comap coreProjection =
      (coreProjection (H := H)).ker
    rw [he, h, coreProjection, QuotientGroup.ker_mk']
  · intro h
    rw [h] at he
    simpa only [MonoidHom.comap_bot, coreProjection, QuotientGroup.ker_mk'] using he.symm

/-- The actual isomorphism between the two quotients after identifying their kernels. -/
def threePrimeQuotientEquivCore (h : pPrimeCore 3 H = pCore 2 H) :
    (H ⧸ pPrimeCore 3 H) ≃* coreQuotient H :=
  QuotientGroup.quotientMulEquivOfEq h

omit [Finite H] in
/-- The kernel bridge preserves the images of elements of the original group. -/
theorem threePrimeQuotientEquivCore_apply (h : pPrimeCore 3 H = pCore 2 H) (x : H) :
    threePrimeQuotientEquivCore h (QuotientGroup.mk' (pPrimeCore 3 H) x) =
      coreProjection x :=
  QuotientGroup.quotientMulEquivOfEq_mk h x

/-- The genuine F.6.11 Sylow conclusion makes the image of the three-prime
core odd after factoring out the two-core. -/
theorem threePrimeCore_image_coprime_two
    (S : Sylow 2 (pPrimeCore 3 H))
    (hS : (S : Subgroup (pPrimeCore 3 H)).map (pPrimeCore 3 H).subtype = pCore 2 H) :
    Nat.Coprime 2 (Nat.card ((pPrimeCore 3 H).map (coreProjection (H := H)))) := by
  let f := (coreProjection (H := H)).comp (pPrimeCore 3 H).subtype
  have hk : (S : Subgroup (pPrimeCore 3 H)) ≤ f.ker := by
    intro s hs
    change coreProjection (s : H) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [← hS]
    exact mem_map.mpr ⟨s, hs, rfl⟩
  have hr : f.range = (pPrimeCore 3 H).map coreProjection := by
    rw [← MonoidHom.map_range, Subgroup.range_subtype]
  rw [← hr]
  exact coprime_card_range_of_sylow_killed f S hk

/-- F.6.11 and the two-group quotient put the three-prime-core image
inside the actual offender group, without equating that group to the quotient. -/
theorem threePrimeCore_image_le_offenderGroup
    (P : Sylow 2 H) (Z : Subgroup H) [IsElementaryAbelian 2 (moduleClosure Z)]
    (hC : centralizer (Z : Set H) = (P : Subgroup H))
    (S : Sylow 2 (pPrimeCore 3 H))
    (hS : (S : Subgroup (pPrimeCore 3 H)).map (pPrimeCore 3 H).subtype = pCore 2 H)
    (hq : IsPGroup 2 (coreQuotient H ⧸ offenderGroup P Z hC)) :
    (pPrimeCore 3 H).map coreProjection ≤ offenderGroup P Z hC :=
  le_of_quotient_twoGroup _ _ hq (threePrimeCore_image_coprime_two S hS)

/-- A precise bridge between the kernels in F.6.18 and the module action.
The remaining offender-core hypothesis must be discharged from classification. -/
theorem threePrimeCore_eq_twoCore_of_offender_core
    (P : Sylow 2 H) (Z : Subgroup H) [IsElementaryAbelian 2 (moduleClosure Z)]
    (hC : centralizer (Z : Set H) = (P : Subgroup H))
    (S : Sylow 2 (pPrimeCore 3 H))
    (hS : (S : Subgroup (pPrimeCore 3 H)).map (pPrimeCore 3 H).subtype = pCore 2 H)
    (hq : IsPGroup 2 (coreQuotient H ⧸ offenderGroup P Z hC))
    (hN : pPrimeCore 3 (offenderGroup P Z hC) = ⊥) :
    pPrimeCore 3 H = pCore 2 H := by
  let R := (pPrimeCore 3 H).map (coreProjection (H := H))
  let N := offenderGroup P Z hC
  have hRN : R ≤ N := threePrimeCore_image_le_offenderGroup P Z hC S hS hq
  have hnormal : R.Normal := Subgroup.Normal.map inferInstance _
    (QuotientGroup.mk'_surjective _)
  have hc : Nat.Coprime 3 (Nat.card (R.subgroupOf N)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRN).toEquiv]
    exact pPrimeCore_coprime_card.of_dvd_right (card_map_dvd _ _)
  have hle : R.subgroupOf N ≤ pPrimeCore 3 N := le_sSup ⟨inferInstance, hc⟩
  rw [hN] at hle
  have hb : R = ⊥ := by
    rw [← map_subgroupOf_eq_of_le hRN, le_bot_iff.mp hle, Subgroup.map_bot]
  apply le_antisymm _ twoCore_le_threePrimeCore
  have hk : pPrimeCore 3 H ≤ (coreProjection (H := H)).ker :=
    map_le_iff_le_comap.mp (show R ≤ ⊥ from hb.le)
  simpa only [coreProjection, QuotientGroup.ker_mk'] using hk

/-- The bridge needs the offender group's three-prime core, not an unproved
identification of the offender group with the whole action group. -/
theorem mixed_threePrimeCore_eq_twoCore
    (P : Sylow 2 H) (Z Y₁ Y₂ : Subgroup H)
    [IsElementaryAbelian 2 (moduleClosure Z)]
    (hC : centralizer (Z : Set H) = (P : Subgroup H))
    (S : Sylow 2 (pPrimeCore 3 H))
    (hS : (S : Subgroup (pPrimeCore 3 H)).map (pPrimeCore 3 H).subtype = pCore 2 H)
    (hgen : Y₁ ⊔ Y₂ ⊔ (P : Subgroup H) = ⊤)
    (h₁ : Y₁ = ⁅Y₁, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (h₂ : Y₂ = ⁅Y₂, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (hJ : (Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)).map coreProjection ≤
      offenderGroup P Z hC)
    (hN : pPrimeCore 3 (offenderGroup P Z hC) = ⊥) :
    pPrimeCore 3 H = pCore 2 H :=
  threePrimeCore_eq_twoCore_of_offender_core P Z hC S hS
    (quotient_offenderGroup_isTwoGroup P Z hC Y₁ Y₂ hgen h₁ h₂ hJ) hN

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
