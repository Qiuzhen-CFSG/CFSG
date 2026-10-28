module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.FieldFourModule

/-!
# The literal covering residual and seed in an ordinary component

The same inclusion of B in the actual component K defines every map here.
The component center is a two-group, so projection preserves the full
B/O₂(B) quotient. At field four, the original natural seed has no fixed
vectors. A central projection kernel therefore meets it trivially, and
its image has order 64 with the original conjugation action. The full
C.2.8 module W is unchanged and no shortness hypothesis is used.

The Rudvalis extension applies the quotient comparison to the ordinary
C.2.8 exclusion. The J₄ inspection and final assembly remain with
qt-d-1222-natural-point-fixed-summand; the odd-normalizer owner uses the
same covering-residual contract.
Source: Aschbacher--Smith C.3.2--5, pp.149--150, and the local inspections
in 4.2.13 and 4.4.12, pp.611--612 and 622.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
open WeakClosure.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {H M B R W : Subgroup G}

/-- The literal map from the covering residual into the ordinary component. -/
def ordinaryCoverInclusion
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (K : Subgroup H) (hK : IsComponent H K) : B →* K where
  toFun b := ⟨⟨b,h.component_le.trans h.local_le b.property⟩,
    h.ordinary_component_contains_original K hK b.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem ordinaryCoverInclusion_injective
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (K : Subgroup H) (hK : IsComponent H K) :
    Function.Injective (ordinaryCoverInclusion h K hK) := by
  intro b c he
  exact Subtype.ext (congrArg (fun k : K => ((k : H) : G)) he)

/-- Central projection uses the inclusion of the same B in K. -/
def ordinaryCoverProjection
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (K : Subgroup H) (hK : IsComponent H K) : B →* K ⧸ center K :=
  (QuotientGroup.mk' (center K)).comp (ordinaryCoverInclusion h K hK)

theorem ordinaryCoverProjection_kernel
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (K : Subgroup H) (hK : IsComponent H K) :
    IsPGroup 2 (ordinaryCoverProjection h K hK).ker ∧
      (ordinaryCoverProjection h K hK).ker ≤ center B := by
  let j := ordinaryCoverInclusion h K hK
  let := hK.2
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)
  constructor
  · change IsPGroup 2 ((QuotientGroup.mk' (center K)).comp j).ker
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk',hz]
    exact pCore_isPGroup.comap_of_injective j (ordinaryCoverInclusion_injective h K hK)
  · intro b hb
    apply mem_center_iff.mpr
    intro c
    apply ordinaryCoverInclusion_injective h K hK
    simpa only [map_mul] using
      (mem_center_iff.mp ((QuotientGroup.eq_one_iff (j b)).mp hb)) (j c)

include D S in
/-- A central kernel on a covering subgroup kills no vector of the original
field-four seed. No statement about the size of W is used. -/
theorem field_four_seed_injective {Q : Type*} [Group Q]
    (_hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B) (hf : S.field.degree = 2)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (f : B →* Q) (hz : f.ker ≤ center B) :
    Function.Injective (f.comp (inclusion hVB)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro v hv
  have hBC : (v : G) ∈ centralizer (B : Set G) := by
    intro b hb
    exact congrArg Subtype.val
      (mem_center_iff.mp (hz (show inclusion hVB v ∈ f.ker from hv)) ⟨b,hb⟩)
  have hQC : (v : G) ∈ centralizer (L.pCoreIn 2 : Set G) :=
    le_centralizer_iff.mp ((OddNormalizer.centralizer_eq_core D S).ge.trans inf_le_right)
      v.property
  have hLC : (v : G) ∈ centralizer (L : Set G) := by
    intro l hl
    obtain ⟨b,hb,q,hq,rfl⟩ := hc ▸ hl
    calc
      b * q * (v : G) = b * ((v : G) * q) := by rw [mul_assoc,hQC q hq]
      _ = (v : G) * (b * q) := by rw [←mul_assoc,hBC b hb,mul_assoc]
  apply Subtype.ext
  exact mem_bot.mp ((OddNormalizer.original_module_card_of_field_four D S hf e).1 ▸
    (show (v : G) ∈ V ⊓ centralizer (L : Set G) from ⟨v.property,hLC⟩))

/-- The seed is carried to the component by its unchanged ambient inclusion. -/
def ordinarySeedProjection
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hVB : V ≤ B) (K : Subgroup H) (hK : IsComponent H K) :
    V →* K ⧸ center K := (ordinaryCoverProjection h K hK).comp (inclusion hVB)

include D S in
theorem ordinarySeedProjection_injective
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B) (hf : S.field.degree = 2)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (K : Subgroup H) (hK : IsComponent H K) :
    Function.Injective (ordinarySeedProjection h hVB K hK) :=
  field_four_seed_injective D S hBL hc hVB hf e _
    (ordinaryCoverProjection_kernel h K hK).2

include D S in
theorem ordinarySeedProjection_card
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B) (hf : S.field.degree = 2)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (K : Subgroup H) (hK : IsComponent H K) :
    Nat.card (ordinarySeedProjection h hVB K hK).range = 64 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective
    (ordinarySeedProjection_injective D S h hBL hc hVB hf e K hK)).toEquiv]
  exact (OddNormalizer.original_module_card_of_field_four D S hf e).2


include D in
/-- The projected seed action is the original conjugation by each b in B. -/
theorem ordinarySeedProjection_conj
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hBL : B ≤ L) (hVB : V ≤ B) (K : Subgroup H) (hK : IsComponent H K)
    (b : B) (v : V) :
    ordinarySeedProjection h hVB K hK
      ⟨(b : G) * v * (b : G)⁻¹, (D.normalizes (hBL b.property) _).mp v.property⟩ =
      ordinaryCoverProjection h K hK b * ordinarySeedProjection h hVB K hK v *
        (ordinaryCoverProjection h K hK b)⁻¹ := by
  change ordinaryCoverProjection h K hK (b * inclusion hVB v * b⁻¹) = _
  simp only [map_mul,map_inv,ordinarySeedProjection,MonoidHom.comp_apply]

/-- Central projection retains the full residual quotient, with its actual
representative map. This includes the cubic center of SL3(4). -/
def ordinaryCoverQuotient
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (K : Subgroup H) (hK : IsComponent H K) :
    (B ⧸ pCore 2 B) ≃*
      ((ordinaryCoverProjection h K hK).range ⧸ pCore 2 (ordinaryCoverProjection h K hK).range) :=
  (ordinaryCoverProjection h K hK).rangeRestrict.quotientPCoreEquivOfSurjective
    (ordinaryCoverProjection h K hK).rangeRestrict_surjective (by
      rw [MonoidHom.ker_rangeRestrict]
      exact (ordinaryCoverProjection_kernel h K hK).1)

theorem ordinaryCoverQuotient_mk
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (K : Subgroup H) (hK : IsComponent H K) (b : B) :
    ordinaryCoverQuotient h K hK (QuotientGroup.mk' (pCore 2 B) b) =
      QuotientGroup.mk' (pCore 2 (ordinaryCoverProjection h K hK).range)
        ((ordinaryCoverProjection h K hK).rangeRestrict b) := by
  exact MonoidHom.quotientPCoreEquivOfSurjective_mk _ _ _ b

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
