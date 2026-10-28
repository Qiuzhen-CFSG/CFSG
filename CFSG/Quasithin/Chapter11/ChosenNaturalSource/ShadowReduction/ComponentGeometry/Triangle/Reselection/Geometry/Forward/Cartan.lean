module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.FixedCubic
public import Theory.SpecificGroups.SymplecticFour.SylowFixedCubic
public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement

/-!
# Transfer of the actual Cartan to the swapped field-four vertex

The original Cartan joins T inside a solvable group: the Cartan normalizer
has a two-group kernel and an abelian torus quotient, and T normalizes that
normalizer. Inside the new vertex, a solvable subgroup containing the inner
Sylow lies in its Borel. This is checked on the actual SL₃, Sp₄ and G₂
models and lifted through the original two-core quotient. Equality of the
Cartan orders then gives the required odd Hall condition.

Thus a source Cartan contained in the new field-four vertex is again a
Cartan there. The argument does not replace the source permutability XT=TX
by the stronger assertion that X normalizes T. Forward/Source.lean applies
the transfer to the original triangle's point-centralization argument.
The remaining inclusion X ≤ I belongs to this task's triangle geometry.
Source: Aschbacher–Smith, 11.1.2(3), printed p.764.
The G₂ model uses the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V I U : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)

include D S in
/-- The original Cartan and full Sylow generate a solvable subgroup. -/
theorem cartan_join_sylow_solvable {X : Subgroup G} (hX : IsCartan T L X) :
    Group.IsSolvable (X ⊔ (T : Subgroup G) : Subgroup G) := by
  let c := coordinates D S
  let N := cartanNormalizer T L
  have hquot : Group.IsSolvable (N ⧸ pCore 2 N) :=
    Group.isSolvable_of_isSolvable_injective
      (f := c.cartanNormalizerQuotientEquiv.toMonoidHom)
      c.cartanNormalizerQuotientEquiv.injective
  let : Group.IsNilpotent (pCore 2 N) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable N :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 N)).mpr ⟨inferInstance, hquot⟩
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  have hTP : (T : Subgroup G) ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer D.sylow_normalizes_component).trans
      inf_normalizer_le_normalizer_inf
  have hTN : (T : Subgroup G) ≤ normalizer (N : Set G) := by
    dsimp only [N]
    rw [cartanNormalizer_eq_intersection_normalizer]
    exact (le_inf D.sylow_normalizes_component
      (hTP.trans (normalizer _).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  let : Group.IsSolvable (N ⊔ (T : Subgroup G) : Subgroup G) :=
    Group.isSolvable_sup_of_normalizes N T hTN
  exact Group.isSolvable_of_isSolvable_injective
    (f := inclusion (sup_le_sup_right hX.1 (T : Subgroup G)))
    (inclusion_injective _)

private theorem g2_solvable_overgroup_normalizes
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (P : Sylow 2 (Atlas.G2.Model F))
    (H : Subgroup (Atlas.G2.Model F)) (hH : Group.IsSolvable H)
    (hPH : (P : Subgroup _) ≤ H) : H ≤ normalizer (P : Set _) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Atlas.G2.Model F) P
    (Atlas.G2.LieParabolicSetup.sylow (F := F))
  let e := MulAut.conj g
  have hP : (P : Subgroup (Atlas.G2.Model F)).map e.toMonoidHom = Atlas.G2.unipotent := by
    change ((g • P : Sylow 2 (Atlas.G2.Model F)) : Subgroup (Atlas.G2.Model F)) = _
    rw [hg]
    rfl
  let := hH
  have hs : Group.IsSolvable (H.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective H)
  have hn := Atlas.G2.SolvableSylowPlacement.le_borel hq (H.map e.toMonoidHom)
    (hP ▸ map_mono hPH) hs
  rw [← Atlas.G2.SylowNormalizer.normalizer_unipotent,
    ← hP, ← map_equiv_normalizer_eq] at hn
  exact (map_le_map_iff_of_injective e.injective).mp hn

private theorem model_solvable_overgroup_normalizes
    (c : Coordinates D S.field) (hd : S.field.degree = 2)
    (P : Sylow 2 c.ModelGroup) (H : Subgroup c.ModelGroup)
    (hH : Group.IsSolvable H) (hPH : (P : Subgroup _) ≤ H) :
    H ≤ normalizer (P : Set _) := by
  have hq : Nat.card S.field.Carrier = 4 := by simpa [hd] using S.field.card_eq
  cases c with
  | sl3 m => exact Matrix.PSL3.LinearThree.four_solvable_sylow_overgroup_normalizes hq P H hH hPH
  | sp4 m =>
    exact Theory.SpecificGroups.SymplecticFour.solvable_sylow_overgroup_normalizes
      (F := S.field.Carrier) (by omega) P H hH hPH
  | g2 m => exact g2_solvable_overgroup_normalizes (F := S.field.Carrier) (by omega) P H hH hPH

private theorem cartan_normalizer_of_solvable_join
    (hd : S.field.degree = 2) (X : Subgroup G) (hXL : X ≤ L)
    (hsol : Group.IsSolvable (X ⊔ (T : Subgroup G) : Subgroup G)) :
    X ≤ cartanNormalizer T L := by
  let c := coordinates D S
  let H := (X ⊔ (T : Subgroup G)).subgroupOf L
  let := hsol
  let : Group.IsSolvable H := Group.isSolvable_of_isSolvable_injective
    (f := L.subtype.subgroupComap (X ⊔ (T : Subgroup G)))
    (by intro a b h; exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val) h)))
  have hH : Group.IsSolvable (H.map c.quotientMap) :=
    Group.isSolvable_of_surjective (c.quotientMap.subgroupMap_surjective H)
  have hPH : (c.innerSylow : Subgroup L) ≤ H := by
    rw [c.innerSylow_coe]
    exact comap_mono le_sup_right
  have hn := model_solvable_overgroup_normalizes D S c hd c.modelSylow
    (H.map c.quotientMap) hH (map_mono hPH)
  have hk : c.quotientMap.ker ≤ c.innerSylow := by
    rw [Coordinates.quotientMap, MonoidHom.ker_comp_of_injective _ _ c.groupEquiv.injective,
      QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal c.innerSylow
  have hHN : H ≤ normalizer (c.innerSylow : Set L) := by
    have hh := (map_le_iff_le_comap.mp hn).trans
      (((c.innerSylow : Subgroup L).map c.quotientMap).le_normalizer_comap c.quotientMap)
    simpa only [Coordinates.modelSylow, Sylow.coe_mapSurjective, comap_map_eq_self hk,
      Sylow.coe_coe] using hh
  rw [← componentNormalizer_map c.innerSylow c.innerSylow_coe]
  intro x hx
  exact mem_map_of_mem L.subtype (hHN (show (⟨x,hXL hx⟩ : L) ∈ H from mem_sup_left hx))

private theorem cartan_of_card_and_solvable_join
    (hd : S.field.degree = 2) (X : Subgroup G) (hXL : X ≤ L)
    (hsol : Group.IsSolvable (X ⊔ (T : Subgroup G) : Subgroup G))
    (hcard : Nat.card X = (2 ^ S.field.degree - 1) ^ 2) : IsCartan T L X := by
  have hXN := cartan_normalizer_of_solvable_join D S hd X hXL hsol
  obtain ⟨Y,hY⟩ := exists_cartan D
  have hXY : Nat.card (X.subgroupOf (cartanNormalizer T L)) =
      Nat.card (Y.subgroupOf (cartanNormalizer T L)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hXN).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hY.1).toEquiv,
      (coordinates D S).cartan_card hY, hcard]
  have hindex : (X.subgroupOf (cartanNormalizer T L)).index =
      (Y.subgroupOf (cartanNormalizer T L)).index := by
    apply Nat.eq_of_mul_eq_mul_right
      (Nat.card_pos (α := X.subgroupOf (cartanNormalizer T L)))
    rw [index_mul_card, hXY, index_mul_card]
  refine ⟨hXN, ?_⟩
  constructor
  · intro p hp
    exact hY.2.p_in_pi_of_p_dvd_card p (hXY ▸ hp)
  · intro p hp
    exact hY.2.p_in_pi_of_p_dvd_index p (hindex ▸ hp)

/-- A source Cartan contained in a second field-four natural component is
also its source Cartan, for the same literal Sylow subgroup. -/
theorem cartan_transfer
    (hd : S.field.degree = 2) {X : Subgroup G} (hX : IsCartan T L X)
    (D_I : Chapter12.Section02.ChosenModule T I U) (S_I : D_I.NonbinaryNaturalInput)
    (hd_I : S_I.field.degree = 2) (hXI : X ≤ I) : IsCartan T I X := by
  apply cartan_of_card_and_solvable_join D_I S_I hd_I X hXI
    (cartan_join_sylow_solvable D S hX)
  rw [(coordinates D S).cartan_card hX, hd, hd_I]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
