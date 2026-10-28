module

public import Theory.Representation.HexacodeAction.ThompsonOffenders
public import Theory.ElementaryAbelian.Injective
-- This model-calculation extension uses the private eight-word implementation;
-- the public statements below are independent of that implementation.
import all Theory.Representation.HexacodeAction.ThompsonOffenders

open Subgroup Representation Representation.BinaryOffender Atlas.Codes
open Representation.Hexacode
open Representation.Hexacode.ThompsonOffenders

/-!
# The exceptional critical-action calculation

A four-group in the even hexacode cover is self-centralizing inside each
containing two-subgroup. This follows from the eight-element dihedral Sylow
model, and does not assume that the source radical is Sylow. An odd
hexacode automorphism cannot fix a nonzero displacement and its cubic scalar
multiple. Hence a two-element centralizing a best offender and its moved
space belongs to that offender.

Transport through an actual equivariant hexacode section gives a bound on
the entire acting subgroup image. If the projection kernel centralizes X,
this bounds [Y,X] by [E,X]. The graph application in CriticalAction derives
the centralization premises from the original critical pair.

Source: Meierfrankenfeld--Stellmacher (1993), the exceptional case of (3.3),
pp.866--868, used in (3.6), p.870. The imported concrete hexacode and Sylow
model retain the ATLAS attribution and license in LICENSES/ATLAS.txt.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.HexacodeLocal

private theorem sylow_four_centralizer (A : Subgroup HexEvenAutomorphisms)
    (ha : IsElementaryAbelian 2 A) (hAS : A ≤ SylowModel.sylowGroup)
    (hcard : Nat.card A = 4) :
    SylowModel.sylowGroup ⊓ centralizer (A : Set HexEvenAutomorphisms) ≤ A := by
  rcases SylowModel.fourGroup_exhaustion A ha hAS hcard with rfl | rfl
  · rintro x ⟨⟨p,rfl⟩,hc⟩
    apply (SylowModel.word_mem_line p).mpr
    have hh := hc (SylowModel.word (0,1,0)) ((SylowModel.word_mem_line (0,1,0)).mpr rfl)
    change SylowModel.word (0,1,0) * SylowModel.word p =
      SylowModel.word p * SylowModel.word (0,1,0) at hh
    rw [←SylowModel.word_mul,←SylowModel.word_mul] at hh
    have hp := SylowModel.word_injective hh
    exact (by decide : ∀ p : SylowModel.Bits,
      SylowModel.mulBits (0,1,0) p = SylowModel.mulBits p (0,1,0) → p.2.2 = 0) p hp
  · rintro x ⟨⟨p,rfl⟩,hc⟩
    apply (SylowModel.word_mem_plane p).mpr
    have hh := hc (SylowModel.word (0,0,1)) ((SylowModel.word_mem_plane (0,0,1)).mpr rfl)
    change SylowModel.word (0,0,1) * SylowModel.word p =
      SylowModel.word p * SylowModel.word (0,0,1) at hh
    rw [←SylowModel.word_mul,←SylowModel.word_mul] at hh
    have hp := SylowModel.word_injective hh
    exact (by decide : ∀ p : SylowModel.Bits,
      SylowModel.mulBits (0,0,1) p = SylowModel.mulBits p (0,0,1) → p.2.1 = 0) p hp

/-- The even four-group is self-centralizing in any containing two-subgroup. -/
theorem even_four_centralizer (P A : Subgroup HexEvenAutomorphisms)
    (hP : IsPGroup 2 P) (hAP : A ≤ P)
    (ha : IsElementaryAbelian 2 A) (hcard : Nat.card A = 4) :
    P ⊓ centralizer (A : Set HexEvenAutomorphisms) ≤ A := by
  obtain ⟨S,hPS⟩ := hP.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq HexEvenAutomorphisms S standardSylow
  have hS : (S : Subgroup HexEvenAutomorphisms).map
      (MulAut.conj g).toMonoidHom = SylowModel.sylowGroup :=
    congrArg Sylow.toSubgroup hg
  let f := (MulAut.conj g).toMonoidHom
  have hAS : A.map f ≤ SylowModel.sylowGroup := by
    rw [←hS]
    exact map_mono (hAP.trans hPS)
  let := ha
  have he := sylow_four_centralizer (A.map f) (IsElementaryAbelian.map f) hAS
    ((card_map_of_injective (MulAut.conj g).injective).trans hcard)
  intro x hx
  have hxA : f x ∈ A.map f := by
    apply he
    refine ⟨?_, ?_⟩
    · rw [←hS]
      exact mem_map_of_mem f (hPS hx.1)
    · rintro _ ⟨a,ha,rfl⟩
      simpa only [map_mul] using congrArg f (hx.2 a ha)
  exact (mem_map_iff_mem (f := f) (MulAut.conj g).injective).mp hxA

/-- Centralizing an offender and its displacement forces membership in it. -/
theorem full_best_centralizer (P A : Subgroup HexAutomorphisms)
    (hP : IsPGroup 2 P) (hAP : A ≤ P)
    (ha : IsBestOffender action A)
    {y : HexAutomorphisms} (hy : y ∈ P) (hya : y ∈ centralizer (A : Set HexAutomorphisms))
    (hfix : ∀ a ∈ A, ∀ v : hexacode,
      action y (action a v - v) = action a v - v) : y ∈ A := by
  have hAe := Hexacode.bestOffender_le_even A ha
  have hye : hexSign y = 1 := by
    rcases Int.units_eq_one_or (hexSign y) with hh | hh
    · exact hh
    · have heq : ∀ a ∈ A, a = 1 := by
        intro a ha'
        apply action_injective
        apply LinearMap.ext
        intro v
        have hv : action a v - v = 0 := by
          apply ThompsonOffenders.eq_zero_of_odd_fixes_scalar y hh _ (hfix a ha' v)
          have hs := hfix a ha' (Hexacode.omega • v)
          rw [action_even_smul a (hAe ha'),←smul_sub] at hs
          exact hs
        simpa using sub_eq_zero.mp hv
      exact (ha.1.1 (le_bot_iff.mp (fun a ha' => heq a ha'))).elim
  let Pe := P.subgroupOf hexSign.ker
  let Ae := A.subgroupOf hexSign.ker
  have hPe' : IsPGroup 2 Pe := by
    exact hP.of_injective
      ((hexSign.ker.subtype.comp Pe.subtype).codRestrict P (fun x => x.property))
      (fun x z hz => Subtype.ext (Subtype.ext (congrArg (fun a : P => (a : HexAutomorphisms)) hz)))
  have hAeCard : Nat.card Ae = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAe).toEquiv).trans (Hexacode.bestOffender_card A ha)
  have hAeElem : IsElementaryAbelian 2 Ae := by
    let := ha.1.2
    exact IsElementaryAbelian.comap_of_injective hexSign.ker.subtype hexSign.ker.subtype_injective A
  have he := even_four_centralizer Pe Ae hPe' (fun _ hx => hAP hx) hAeElem hAeCard
  exact he (show (⟨y,hye⟩ : HexEvenAutomorphisms) ∈ Pe ⊓ centralizer (Ae : Set HexEvenAutomorphisms) from
    ⟨hy, fun a ha' => Subtype.ext (hya a ha')⟩)


open scoped commutatorElement
open scoped IsMulCommutative

/-- The original action image is controlled by its offending subgroup. -/
theorem image_le_of_hexacode_offender
    {H : Type*} [Group H] (f : H →* HexAutomorphisms)
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (φ : Additive W ≃ₗ[ZMod 2] hexacode)
    (hφ : ∀ (g : H) (v : W),
      φ (Additive.ofMul (MulAut.conjNormal g v)) = action (f g) (φ (Additive.ofMul v)))
    (E Y P : Subgroup H) (hP : IsPGroup 2 P) (hEP : E ≤ P) (hYP : Y ≤ P)
    (hEY : Y ≤ centralizer (E : Set H))
    (hcomm : Y ≤ centralizer ((⁅E,W⁆ : Subgroup H) : Set H))
    (ho : IsOffender action (E.map f)) : Y.map f ≤ E.map f := by
  obtain ⟨B,hBE,hB⟩ := ho.exists_bestOffender action
  rintro _ ⟨y,hy,rfl⟩
  apply hBE
  apply full_best_centralizer (P.map f) B (hP.map f)
    (hBE.trans (map_mono hEP)) hB (mem_map_of_mem f (hYP hy))
  · rintro _ hb
    obtain ⟨a,ha,rfl⟩ := hBE hb
    simpa only [map_mul] using congrArg f (hEY hy a ha)
  · intro b hb v
    obtain ⟨a,ha,rfl⟩ := hBE hb
    obtain ⟨w,rfl⟩ := φ.surjective v
    let c : W := MulAut.conjNormal a w.toMul * w.toMul⁻¹
    have hc : (c : H) ∈ ⁅E,W⁆ :=
      commutator_mem_commutator ha w.toMul.property
    have hyc : MulAut.conjNormal y c = c := by
      apply Subtype.ext
      change y * (c : H) * y⁻¹ = c
      rw [← hcomm hy c hc, mul_assoc, mul_inv_cancel, mul_one]
    have he : φ (Additive.ofMul c) = action (f a) (φ w) - φ w := by
      simp only [c, ofMul_mul, ofMul_inv, map_add, map_neg, hφ,
        ofMul_toMul, sub_eq_add_neg]
    rw [←he,←hφ,hyc]

private theorem commutator_le_of_image_le
    {H I : Type*} [Group H] [Group I] (f : H →* I)
    (A B X : Subgroup H) (hk : f.ker ≤ centralizer (X : Set H))
    (hab : A.map f ≤ B.map f) : ⁅A,X⁆ ≤ ⁅B,X⁆ := by
  apply commutator_le.mpr
  intro a ha x hx
  obtain ⟨b,hb,hba⟩ := hab (mem_map_of_mem f ha)
  have he : b⁻¹*a ∈ f.ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv,hba,inv_mul_cancel]
  have hc := hk he x hx
  have heq : ⁅a,x⁆ = ⁅b,x⁆ := by
    simp only [commutatorElement_def]
    calc a*x*a⁻¹*x⁻¹ = b*((b⁻¹*a)*x*(b⁻¹*a)⁻¹)*b⁻¹*x⁻¹ := by group
         _ = b*x*b⁻¹*x⁻¹ := by rw [←hc,mul_inv_cancel_right]
  rw [heq]
  exact commutator_mem_commutator hb hx

/-- A faithful section calculation bounds the commutator on all of X. -/
theorem commutator_le_of_hexacode_offender
    {H : Type*} [Group H] (f : H →* HexAutomorphisms)
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (φ : Additive W ≃ₗ[ZMod 2] hexacode)
    (hφ : ∀ (g : H) (v : W),
      φ (Additive.ofMul (MulAut.conjNormal g v)) = action (f g) (φ (Additive.ofMul v)))
    (E Y P X : Subgroup H) (hP : IsPGroup 2 P) (hEP : E ≤ P) (hYP : Y ≤ P)
    (hEY : Y ≤ centralizer (E : Set H))
    (hcomm : Y ≤ centralizer ((⁅E,W⁆ : Subgroup H) : Set H))
    (ho : IsOffender action (E.map f))
    (hk : f.ker ≤ centralizer (X : Set H)) : ⁅Y,X⁆ ≤ ⁅E,X⁆ :=
  commutator_le_of_image_le f Y E X hk
    (image_le_of_hexacode_offender f W φ hφ E Y P hP hEP hYP hEY hcomm ho)

end AlternatingSixReconstruction.Exceptional.Exhaustion.HexacodeLocal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
