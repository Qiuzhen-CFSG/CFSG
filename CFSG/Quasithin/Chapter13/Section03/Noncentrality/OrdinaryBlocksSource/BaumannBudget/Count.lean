module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.Contracts
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.BlockChiefCount
public import Theory.GroupTheory.PCoreActionSplitting

/-!
# The chief budget of the original ordinary point residual

The natural action identifies the literal point residual's image with A₄
and its kernel with the restriction of O₂(LT). An A₆ block bounds the cubic
fixed length on O₂(LT) by one; A₄ contributes one more binary chief factor.
Thus every complete chief series of the original actor has count at most two.
No nonabelian full-span or plane-noncentrality premise is used.

This proves the final counting implication. The original block conclusion
must still be supplied by the preceding Baumann argument.
Source: Aschbacher--Smith, 13.3.14, final paragraph on printed p.893.
-/

public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion Section08.TransvectionRecognition.Component.ModelExtension
open Section07.NaturalAction Section07.ModelExclusions
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

/-- The ordinary natural action has the literal LT two-core as kernel. -/
theorem ordinary_natural_permutation_kernel
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    (permutation d).ker = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
  rcases NaturalModels.quotient_alternatives d with ⟨e,he⟩ | ⟨e,he⟩
  · let a : OrdinarySource.NaturalSetup L (T : Subgroup G) V P := {
      model := e
      normalizes_L := d.normalizes_L
      normalizes_V := d.normalizes_V
      sylow := T.subtype le_sup_right
      sylow_eq := rfl
      permutation := permutation d
      model_compatible := fun l => (permutation_L d l).trans (congrArg Subtype.val (he l)).symm
      naturalMap := d.coordinate.toMonoidHom
      naturalMap_surjective := d.coordinate.surjective
      naturalMap_kernel := by
        rw [NaturalModels.centralizer_bot d]
        exact (MonoidHom.ker_eq_bot_iff _).mpr d.coordinate.injective
      conjugation := conjugation d
      point := image d P
      point_dim := image_dim d P
        (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) 1 (by simpa using d.line_card)
      line_eq := NaturalModels.flag_preimage d P
        (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le))
      line_stable := d.line_stable }
    exact (permutation d).ker_eq_pCore_of_range_core_eq_bot 2
      a.permutation_kernel_isPGroup (Section05.PlaneGeometry.permutation_range_twoCore d)
  · have hc := Nat.card_congr (centerCongr (e.symm.trans eL)).toEquiv
    rw [Representation.Hexacode.even_center_card,
      alternatingGroup.center_eq_bot (by simp), card_bot] at hc
    omega

/-- The actual point residual maps onto A₄ with the restriction of O₂(LT)
as kernel, before any conclusion about a conjugate span. -/
theorem ordinary_point_residual_surjection
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    ∃ f : sourceOne L T P →* alternatingGroup (Fin 4), Function.Surjective f ∧
      f.ker = ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (sourceOne L T P) := by
  let X := L ⊔ (T : Subgroup G)
  let Y := X ⊓ normalizer (P : Set G)
  let A := sourceOne L T P
  let C := (permutation d).range ⊓ Representation.BinaryOffender.subspaceStabilizer
    (BinaryPermutation.naturalRepresentation (Fin 6)) (image d P)
  have hPX : P ≤ V := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)
  have hYi : (Y.subgroupOf X).map (permutation d) = C := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨⟨x,rfl⟩,(Section07.permutation_stabilizes_iff d P hPX x).mpr hx.2⟩
    · rintro y ⟨⟨x,rfl⟩,hy⟩
      exact ⟨x,⟨x.property,(Section07.permutation_stabilizes_iff d P hPX x).mp hy⟩,rfl⟩
  have hAX : A ≤ X := (one_le L T P).trans inf_le_left
  have hsub : A.subgroupOf X =
      (pResidual 2 (Y.subgroupOf X)).map (Y.subgroupOf X).subtype := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hAX,map_embedded_pResidual,
      map_subgroupOf_eq_of_le (show Y ≤ X from inf_le_left)]
    rfl
  have him : (A.subgroupOf X).map (permutation d) = (pResidual 2 C).map C.subtype := by
    rw [hsub,map_embedded_pResidual,hYi]
  let k : A →* Equiv.Perm (Fin 6) := (permutation d).comp (inclusion hAX)
  have hr : k.range = (pResidual 2 C).map C.subtype := by
    rw [MonoidHom.range_comp,inclusion_range]
    exact him
  obtain ⟨g,hg⟩ := Theory.SpecificGroups.SymmetricSix.BinaryFlags.OrdinaryNormalizer.point_residual_conjugate
    (permutation d).range (alternating_le_range d) (image d P)
    (image_dim d P hPX 1 (by simpa using d.line_card))
  let e : k.range ≃* alternatingGroup (Fin 4) :=
    ((MulAut.conj g).subgroupMap k.range).trans
      ((MulEquiv.subgroupCongr (hr ▸ hg)).trans
        Theory.SpecificGroups.SymmetricSix.BinaryFlags.fourLetterEquiv)
  let f : A →* alternatingGroup (Fin 4) := e.toMonoidHom.comp k.rangeRestrict
  refine ⟨f,e.surjective.comp k.rangeRestrict_surjective,?_⟩
  have hk : f.ker = k.ker := (MonoidHom.ker_comp_of_injective k.rangeRestrict
    e.toMonoidHom e.injective).trans (MonoidHom.ker_rangeRestrict k)
  rw [hk]
  ext x
  constructor
  · intro hx
    have hx' : inclusion hAX x ∈ (permutation d).ker := hx
    rw [ordinary_natural_permutation_kernel d eL] at hx'
    exact mem_map_of_mem X.subtype hx'
  · intro hx
    obtain ⟨y,hy,he⟩ := hx
    have he' : y = inclusion hAX x := Subtype.ext he
    have hx' : inclusion hAX x ∈ pCore 2 X := he' ▸ hy
    rw [←ordinary_natural_permutation_kernel d eL] at hx'
    exact hx'

/-- An original A₆ block supplies the two-chief-factor budget for the literal
point residual. No nonabelian full-span premise is used. -/
theorem ordinary_chief_count_le_two_of_block
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hb : ChapterC.IsAlternatingBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) 6)
    (s : ChiefSeries (sourceOne L T P)) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ 2 := by
  let J := sourceOne L T P
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  obtain ⟨f,hf,hker⟩ := ordinary_point_residual_surjection d eL
  have hd : 3 ∣ Nat.card J := by
    apply dvd_trans (b := Nat.card (alternatingGroup (Fin 4)))
    · rw [nat_card_alternatingGroup]
      norm_num
    · exact card_dvd_of_surjective f hf
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := J) 3 hd
  let A := zpowers (x : G)
  have hA : Nat.card A = 3 := by rw [Nat.card_zpowers,J.orderOf_coe x,hx]
  have hAJ : A ≤ J := zpowers_le.mpr x.property
  have hAL : A ≤ L := by
    have hh := Section08.TransvectionQuotients.FiveSeed.BarMarking.normalizer_residual_eq
      L P (T : Subgroup G) T.isPGroup' d.normalizes_L
    have hJL : J ≤ L := by
      change (pResidual 2 ((L ⊔ (T : Subgroup G)) ⊓ normalizer (P : Set G) : Subgroup G)).map
        ((L ⊔ (T : Subgroup G)) ⊓ normalizer (P : Set G)).subtype ≤ L
      rw [hh]
      exact (map_subtype_le _).trans inf_le_left
    exact hAJ.trans hJL
  have hAP : A ≤ centralizer (P : Set G) :=
    hAJ.trans (((one_le L T P).trans inf_le_right).trans
      (normalizer_le_centralizer_of_card_two P d.line_card))
  have hp : IsPGroup 2 f.ker := by
    rw [hker]
    exact (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).comap_subtype
  have hAi : Nat.card (A.subgroupOf J) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv).trans hA
  have hc := CubicComparison.alternatingFour_count f hf hp (A.subgroupOf J) hAi s h0 h1
  have hl : conjugationCubicLength (A.subgroupOf J) f.ker ≤ 1 := by
    rw [hker]
    have he := CubicComparison.length_subgroupOf A (Q ⊓ J) J hAJ inf_le_right
    rw [inf_subgroupOf_right] at he
    rw [he]
    exact (conjugationCubicLength_mono A inf_le_left).trans
      (Section07.source_block_cubic_length_le_one d hb A hA hAL hAP)
  omega

/-- This is precisely the budget consumed by the ordinary block assembly,
conditional on the earlier original A₆ block alternative. -/
theorem ordinaryChiefBudgetSource_of_block
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hb : ChapterC.IsAlternatingBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) 6) :
    OrdinaryChiefBudgetSource d := by
  intro K hK hKs hm hn hgen hq hU hf hout hmodel s h0 h1
  exact ordinary_chief_count_le_two_of_block d eL hb s h0 h1

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
