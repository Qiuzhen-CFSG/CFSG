module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.Source.Defs
public import Theory.GroupTheory.QuaternionSylowCentrality
public import Theory.GroupTheory.InvolutionCentralizerLifting
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The odd complement in the literal five-centralizer

The five-subgroup has order five and is central in its centralizer, hence
belongs to its odd core. Brauer–Suzuki and coprime centralizer lifting give
C_G(B₅) = O(C_G(B₅)) C_H(B₅); the local quaternion product absorbs B₅.
This proves the odd-complement step without presupposing a five-group.
Its z-fixed subgroup is B₅: it has odd order dividing 40 and contains B₅.

The quaternion Sylow and local order-40 calculation are explicit inputs,
to be constructed from the genuine earlier source data. No legacy
FiveLocalData or M10Witness field is used.

Source: Aschbacher–Smith, J.2.7(5), printed pp.435–436 (PDF pp.446–447).
-/

public section
noncomputable section
open Subgroup BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

private instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem B5Image_card (hZ : Nat.card d.toTypeRuSetup.Z = 2)
    (B5 : Sylow 5 d.toTypeRuSetup.H) : Nat.card (B5Image B5) = 5 := by
  rw [card_map_of_injective d.toTypeRuSetup.H.subtype_injective,
    B5.card_eq_multiplicity, d.ru2.card_H hZ]
  decide +kernel

theorem B5Image_le_G5 (hZ : Nat.card d.toTypeRuSetup.Z = 2)
    (B5 : Sylow 5 d.toTypeRuSetup.H) : B5Image B5 ≤ G5 B5 := by
  let : IsCyclic (B5Image B5) := isCyclic_of_prime_card (B5Image_card hZ B5)
  intro x hx y hy
  exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : B5Image B5) ⟨x, hx⟩)

theorem fiveOddPart_le_G5 (B5 : Sylow 5 d.toTypeRuSetup.H) :
    fiveOddPart B5 ≤ G5 B5 := map_subtype_le _

theorem fiveOddPart_odd (B5 : Sylow 5 d.toTypeRuSetup.H) :
    Odd (Nat.card (fiveOddPart B5)) := by
  rw [card_map_of_injective (G5 B5).subtype_injective]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem G5_normalizes_fiveOddPart (B5 : Sylow 5 d.toTypeRuSetup.H) :
    G5 B5 ≤ normalizer (fiveOddPart B5 : Set G) :=
  (G5 B5).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ _)

theorem normalizer_B5Image_le_normalizer_fiveOddPart
    (B5 : Sylow 5 d.toTypeRuSetup.H) :
    normalizer (B5Image B5 : Set G) ≤ normalizer (fiveOddPart B5 : Set G) :=
  (normalizer_le_normalizer_centralizer _).trans
    (normalizer_le_normalizer_characteristic_image _ _)

theorem B5Image_le_fiveOddPart (hZ : Nat.card d.toTypeRuSetup.Z = 2)
    (B5 : Sylow 5 d.toTypeRuSetup.H) : B5Image B5 ≤ fiveOddPart B5 := by
  let K := (B5Image B5).subgroupOf (G5 B5)
  have hK : K ≤ center (G5 B5) := by
    intro x hx
    exact mem_center_iff.mpr fun y => Subtype.ext ((y.property x hx).symm)
  let : K.Normal := ⟨fun x hx y => by
    have he := mem_center_iff.mp (hK hx) y
    simpa only [he, mul_inv_cancel_right] using hx⟩
  have hcard : Nat.card K = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe (B5Image_le_G5 hZ B5)).toEquiv).trans
      (B5Image_card hZ B5)
  have hle : K ≤ pPrimeCore 2 (G5 B5) :=
    le_sSup ⟨inferInstance, by rw [hcard]; decide⟩
  have hm := map_mono (f := (G5 B5).subtype) hle
  change ((B5Image B5).subgroupOf (G5 B5)).map (G5 B5).subtype ≤ _ at hm
  rwa [map_subgroupOf_eq_of_le (B5Image_le_G5 hZ B5)] at hm

theorem z_mem_G5 (B5 : Sylow 5 d.toTypeRuSetup.H) : c.z ∈ G5 B5 := by
  intro b hb
  exact ((map_subtype_le _ hb) c.z c.z_mem_Z).symm

theorem z_involution_of_card (hZ : Nat.card d.toTypeRuSetup.Z = 2) :
    IsInvolution c.z := by
  have ho : orderOf c.z = 2 := by
    rw [← Nat.card_zpowers, ← c.z_generator, hZ]
  exact ⟨fun he => by simp [he] at ho, by rw [← ho]; exact pow_orderOf_eq_one _⟩

include c in
/-- Brauer–Suzuki supplies the odd-complement product in the actual ambient image. -/
theorem G5_eq_fiveOddPart_sup_CQ (hZ : Nat.card d.toTypeRuSetup.Z = 2)
    (B5 : Sylow 5 d.toTypeRuSetup.H) (q : FiveQuaternionData B5) :
    G5 B5 = fiveOddPart B5 ⊔ CQ B5 := by
  let z : G5 B5 := ⟨c.z, c.z_mem_G5 B5⟩
  have hz : IsInvolution z :=
    ⟨fun he => (c.z_involution_of_card hZ).1 (congrArg Subtype.val he),
      Subtype.ext (c.z_involution_of_card hZ).2⟩
  have hq : Nonempty (q.twoSylow ≃* QuaternionGroup (2 ^ (3 - 2))) := by
    obtain ⟨e⟩ := q.quaternion
    exact ⟨((equivMapOfInjective (q.twoSylow : Subgroup (G5 B5))
      (G5 B5).subtype (G5 B5).subtype_injective).trans
      (MulEquiv.subgroupCongr q.twoSylow_image)).trans e⟩
  have hcentral := BenderSuzuki.PFAppendixII.appendixII_quotient_involution_central_public
    q.twoSylow (by decide : 3 ≤ 3) hq z hz
  have hprod := Theory.GroupTheory.oddCore_sup_involution_centralizer hz hcentral
  have hmap := congrArg (map (G5 B5).subtype) hprod
  have hfix : (centralizer ({z} : Set (G5 B5))).map (G5 B5).subtype =
      d.toTypeRuSetup.H ⊓ G5 B5 := by
    ext x
    rw [c.H_eq_centralizer_z]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy)), y.property⟩
    · intro hx
      exact ⟨⟨x, hx.2⟩, mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hx.1)), rfl⟩
  rw [Subgroup.map_sup, hfix, ← MonoidHom.range_eq_map, Subgroup.range_subtype, q.local_product,
    ← sup_assoc, sup_eq_left.mpr (B5Image_le_fiveOddPart hZ B5)] at hmap
  exact hmap.symm

/-- The z-fixed subgroup of the odd complement is the original five-subgroup. -/
theorem fiveOddPart_inf_centralizer_z (hZ : Nat.card d.toTypeRuSetup.Z = 2)
    (B5 : Sylow 5 d.toTypeRuSetup.H) (q : FiveQuaternionData B5) :
    fiveOddPart B5 ⊓ centralizer ({c.z} : Set G) = B5Image B5 := by
  have hle : B5Image B5 ≤ fiveOddPart B5 ⊓ centralizer ({c.z} : Set G) := by
    rw [← c.H_eq_centralizer_z]
    exact le_inf (B5Image_le_fiveOddPart hZ B5) (map_subtype_le _)
  have hdiv := card_dvd_of_le (show
      fiveOddPart B5 ⊓ centralizer ({c.z} : Set G) ≤
        d.toTypeRuSetup.H ⊓ G5 B5 from
      le_inf (by rw [c.H_eq_centralizer_z]; exact inf_le_right)
        (inf_le_left.trans (fiveOddPart_le_G5 B5)))
  rw [q.local_card] at hdiv
  have hodd := (fiveOddPart_odd B5).of_dvd_nat
    (card_dvd_of_le (show fiveOddPart B5 ⊓ centralizer ({c.z} : Set G) ≤
      fiveOddPart B5 from inf_le_left))
  have hsmall : Nat.card (fiveOddPart B5 ⊓ centralizer ({c.z} : Set G) : Subgroup G) ≤ 5 := by
    have hc := (Nat.coprime_two_left.mpr hodd).symm.pow_right 3
    exact Nat.le_of_dvd (by decide)
      (hc.dvd_of_dvd_mul_left (show Nat.card
        (fiveOddPart B5 ⊓ centralizer ({c.z} : Set G) : Subgroup G) ∣ 2 ^ 3 * 5 from hdiv))
  exact (eq_of_le_of_card_ge hle (by rw [B5Image_card hZ B5]; exact hsmall)).symm

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
