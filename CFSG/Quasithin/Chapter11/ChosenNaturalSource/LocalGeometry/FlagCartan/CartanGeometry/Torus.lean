module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Existence
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
public import Theory.AtlasPort.LinearGroups.G2.EvenBorelTorus
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.Quasithin.PositiveLocalRank

/-!
# The full split torus of the original source Cartan

The source subgroup T_L is the product of T intersect L and O₂(LT).
Since L normalizes this two-core, its normalizer of T_L is exactly its
normalizer of T intersect L. The latter intersection is Sylow in L.
The original quotient map L → L/O₂(L), followed by the supplied marking,
therefore maps this normalizer onto the marked Sylow normalizer with
two-group kernel. Their quotients by their two-cores are isomorphic.

The existing full SL₃, rank-two Sp₄, and concrete octonion G₂ Borel
calculations identify that quotient with Fˣ × Fˣ. In the SL₃ row the
full determinant-one marking retains the cubic scalar center. Every
actual odd Hall subgroup complements the two-core, giving an isomorphism
from the source Cartan itself to this full torus, induced by the original
quotient maps. Cyclicity of Fˣ gives prime rank two at every prime
dividing q - 1 and the exact Cartan order (q - 1)².

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
Chapter 11 opening and the Cartan rank observation associated with
11.0.4, printed pp.759--760. The concrete G₂ results are from the
licensed ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped Pointwise
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField}

omit [Finite G] in
private theorem component_normalizes_join_core :
    L ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
  (le_sup_left : L ≤ L ⊔ (T : Subgroup G)).trans
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

omit [Finite G] in
/-- The literal source T_L is its inner Sylow joined with O₂(LT). -/
theorem sourceTL_eq_sup_core :
    sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ T := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  apply le_antisymm
  · rintro x ⟨hxT,hx⟩
    change x ∈ ((L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 : Subgroup G) : Set G) at hx
    rw [coe_mul_of_left_le_normalizer_right _ _ component_normalizes_join_core] at hx
    obtain ⟨l,hl,q,hq,rfl⟩ := hx
    have hlT : l ∈ (T : Subgroup G) := by
      simpa only [mul_inv_cancel_right] using T.mul_mem hxT (T.inv_mem (hQT hq))
    exact mul_mem (mem_sup_left ⟨hlT,hl⟩) (mem_sup_right hq)
  · exact sup_le sylow_intersection_le_sourceTL (le_inf hQT le_sup_right)

omit [Finite G] in
/-- The source Cartan normalizer is exactly N_L(T intersect L). -/
theorem cartanNormalizer_eq_intersection_normalizer :
    cartanNormalizer T L = L ⊓ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
  apply le_antisymm (le_inf inf_le_left cartanNormalizer_normalizes_intersection)
  intro x hx
  refine ⟨hx.1, ?_⟩
  rw [sourceTL_eq_sup_core]
  exact normalizer_inf_normalizer_le_normalizer_sup _ _
    ⟨hx.2, component_normalizes_join_core hx.1⟩

omit [Finite G] in
/-- The intrinsic Sylow normalizer in L maps to the original source normalizer. -/
theorem componentNormalizer_map (P : Sylow 2 L)
    (hP : (P : Subgroup L) = (T : Subgroup G).subgroupOf L) :
    (normalizer (P : Set L)).map L.subtype = cartanNormalizer T L := by
  change (normalizer ((P : Subgroup L) : Set L)).map L.subtype = _
  rw [hP, ← inf_subgroupOf_right (T : Subgroup G) L,
    ← subgroupOf_normalizer_eq (show (T : Subgroup G) ⊓ L ≤ L from inf_le_right),
    subgroupOf_map_subtype, cartanNormalizer_eq_intersection_normalizer, inf_comm]

namespace Coordinates
variable (c : Coordinates D F)

/-- The Sylow subgroup of L whose ambient image is T intersect L. -/
def innerSylow (_c : Coordinates D F) : Sylow 2 L :=
  (NormalSylowQuotientAction.intersection_sylow T L D.sylow_normalizes_component).choose

/-- The selected inner Sylow retains the original intersection. -/
theorem innerSylow_coe : (c.innerSylow : Subgroup L) = (T : Subgroup G).subgroupOf L :=
  (NormalSylowQuotientAction.intersection_sylow T L D.sylow_normalizes_component).choose_spec

/-- The image of that same inner Sylow under the supplied model marking. -/
def modelSylow : Sylow 2 c.ModelGroup := c.innerSylow.mapSurjective c.quotientMap_surjective

/-- Restriction to L identifies the original source normalizer with its intrinsic version. -/
def componentNormalizerEquiv : cartanNormalizer T L ≃* normalizer (c.innerSylow : Set L) :=
  ((normalizer (c.innerSylow : Set L)).equivMapOfInjective L.subtype L.subtype_injective |>.trans
    (MulEquiv.subgroupCongr (componentNormalizer_map c.innerSylow c.innerSylow_coe))).symm

/-- The original quotient map restricted to the source Cartan normalizer. -/
def cartanProjection : cartanNormalizer T L →* normalizer (c.modelSylow : Set c.ModelGroup) :=
  ((c.quotientMap.comp (normalizer (c.innerSylow : Set L)).subtype).codRestrict _ (by
    intro x
    change c.quotientMap x ∈ normalizer (((c.innerSylow : Subgroup L).map c.quotientMap) : Set c.ModelGroup)
    rw [← c.innerSylow.normalizer_map_surjective c.quotientMap c.quotientMap_surjective]
    exact mem_map_of_mem _ x.property)).comp c.componentNormalizerEquiv.toMonoidHom

/-- On ambient representatives the projection is the supplied original quotient map. -/
theorem cartanProjection_coe (x : cartanNormalizer T L) :
    (c.cartanProjection x : c.ModelGroup) = c.quotientMap ⟨x, x.property.1⟩ := by
  change c.quotientMap (c.componentNormalizerEquiv x).val = _
  congr 1
  apply Subtype.ext
  exact congrArg (fun z : cartanNormalizer T L => (z : G))
    (c.componentNormalizerEquiv.symm_apply_apply x)

/-- Sylow normalizer lifting makes the literal normalizer projection surjective. -/
theorem cartanProjection_surjective : Function.Surjective c.cartanProjection := by
  intro y
  have hy : y.val ∈ (normalizer (c.innerSylow : Set L)).map c.quotientMap := by
    rw [c.innerSylow.normalizer_map_surjective c.quotientMap c.quotientMap_surjective]
    exact y.property
  obtain ⟨x,hx,he⟩ := hy
  refine ⟨c.componentNormalizerEquiv.symm ⟨x,hx⟩, ?_⟩
  apply Subtype.ext
  change c.quotientMap (c.componentNormalizerEquiv (c.componentNormalizerEquiv.symm ⟨x,hx⟩)).val = y.val
  rw [c.componentNormalizerEquiv.apply_symm_apply]
  exact he

/-- The normalizer projection kernel embeds in the original O₂(L). -/
theorem cartanProjection_ker_isTwoGroup : IsPGroup 2 c.cartanProjection.ker := by
  let j : c.cartanProjection.ker →* pCore 2 L :=
    ((inclusion (show cartanNormalizer T L ≤ L from inf_le_left)).comp
      c.cartanProjection.ker.subtype).codRestrict _ (by
        intro x
        apply (QuotientGroup.eq_one_iff _).mp
        apply c.groupEquiv.injective
        rw [map_one]
        exact (c.cartanProjection_coe x.val).symm.trans (congrArg Subtype.val x.property))
  exact pCore_isPGroup.of_injective j (by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : pCore 2 L => (z.val : G)) h)))

/-- All three marked models have the full rank-two split torus quotient. -/
def modelNormalizerQuotientEquiv :
    (normalizer (c.modelSylow : Set c.ModelGroup) ⧸
      pCore 2 (normalizer (c.modelSylow : Set c.ModelGroup))) ≃* (F.Carrierˣ × F.Carrierˣ) := by
  cases c with
  | sl3 m =>
    exact Matrix.PSL3.CartanActions.BorelQuotient.sylowSLNormalizerQuotientEquiv
      F.Carrier F.degree_pos F.card_eq _
  | sp4 m =>
    let e := Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.sylowNormalizerEquiv
      F.card_eq F.degree_pos (Coordinates.sp4 m |>.modelSylow)
    exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
      (Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.quotientTorusEquiv F.card_eq)
  | g2 m =>
    exact Atlas.G2.EvenBorelTorus.sylowNormalizerQuotientEquiv _

/-- The original source normalizer has the same full split torus quotient. -/
def cartanNormalizerQuotientEquiv :
    (cartanNormalizer T L ⧸ pCore 2 (cartanNormalizer T L)) ≃* (F.Carrierˣ × F.Carrierˣ) :=
  (c.cartanProjection.pCoreQuotientEquiv c.cartanProjection_surjective
    c.cartanProjection_ker_isTwoGroup).trans c.modelNormalizerQuotientEquiv

include c in
/-- The two-core of the original source normalizer is Sylow. -/
theorem cartanNormalizer_core_odd_index : Odd (pCore 2 (cartanNormalizer T L)).index := by
  change Odd (Nat.card (cartanNormalizer T L ⧸ pCore 2 (cartanNormalizer T L)))
  rw [Nat.card_congr c.cartanNormalizerQuotientEquiv.toEquiv]
  exact Nat.coprime_two_left.mp
    (Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.torus_odd F.card_eq)

/-- Every actual source Cartan maps isomorphically onto the full split torus. -/
def cartanTorusEquiv {X : Subgroup G} (hX : IsCartan T L X) :
    X ≃* (F.Carrierˣ × F.Carrierˣ) := by
  let P : Sylow 2 (cartanNormalizer T L) :=
    pCore_isPGroup.toSylow c.cartanNormalizer_core_odd_index.not_two_dvd_nat
  have hc : (pCore 2 (cartanNormalizer T L)).IsComplement'
      (X.subgroupOf (cartanNormalizer T L)) := OddHall.sylow_complement_of_hall P hX.2
  exact (subgroupOfEquivOfLe hX.1).symm.trans
    (hc.symm.QuotientMulEquiv.symm.trans c.cartanNormalizerQuotientEquiv)

/-- The Cartan equivalence is induced by the literal normalizer quotient map. -/
theorem cartanTorusEquiv_apply {X : Subgroup G} (hX : IsCartan T L X) (x : X) :
    c.cartanTorusEquiv hX x = c.cartanNormalizerQuotientEquiv
      (QuotientGroup.mk' _ (⟨x, hX.1 x.property⟩ : cartanNormalizer T L)) := rfl

include c in
/-- The source Cartan has exactly the two independent multiplicative coordinates. -/
theorem cartan_card {X : Subgroup G} (hX : IsCartan T L X) :
    Nat.card X = (2 ^ F.degree - 1) ^ 2 := by
  rw [Nat.card_congr (c.cartanTorusEquiv hX).toEquiv, Nat.card_prod,
    Nat.card_units, F.card_eq, pow_two]

include c in
/-- Each prime dividing q - 1 has rank two in every source Cartan. -/
theorem cartan_primeRank {X : Subgroup G} (hX : IsCartan T L X)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ 2 ^ F.degree - 1) : primeRank p X = 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hu : primeRank p F.Carrierˣ = 1 := by
    apply le_antisymm
    · exact (Sylow.nonempty.some : Sylow p F.Carrierˣ).primeRank_le_one_of_isCyclic inferInstance
    · apply Theory.Quasithin.one_le_primeRank_of_dvd_card
      simpa only [Nat.card_units, F.card_eq] using hd
  rw [primeRank_equiv p (c.cartanTorusEquiv hX), primeRank_prod_eq_add, hu]

end Coordinates
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
