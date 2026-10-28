module

public import CFSG.Quasithin.Chapter13.Section07.SourceCover
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Fitting.Orders

/-!
# Marked local models before the abelian-span theorem

The original natural setup already determines the ordinary or covered
local quotient over the prescribed six-letter projection. It therefore
supplies the exact point and Sylow models used in the earlier local
residual calculations. These constructions use no abelian V-span premise.

Source: Aschbacher–Smith, Notation 13.2.1, pp.876–878,
and 13.7.3(9), printed pp.936–937.
-/

public section
open Subgroup BinaryPermutation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions.NaturalModels
open Section08.SourceCompletion NaturalAction
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionQuotients.FiveSeed.BarMarking
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem quotient_alternatives :
    (∃ e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6),
      ∀ l : L, e (QuotientGroup.mk' (pCore 2 L) l) =
        d.local_quotient (QuotientGroup.mk' (centralCore L) l)) ∨
    (∃ e : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms,
      ∀ l : L, Atlas.Codes.hexEvenCoordinate (e (QuotientGroup.mk' (pCore 2 L) l)) =
        d.local_quotient (QuotientGroup.mk' (centralCore L) l)) := by
  let := source_core_quotient_quasisimple d
  rcases source_odd_center_alternatives d with hc | hc
  · let e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6) :=
      QuotientGroup.quotientBot.symm.trans
        ((QuotientGroup.quotientMulEquivOfEq ((eq_bot_iff_card _).mpr hc).symm).trans
          (source_central_quotient d))
    refine Or.inl ⟨e, ?_⟩
    intro l
    change (source_central_quotient d) (QuotientGroup.mk' (center (L ⧸ pCore 2 L))
      (QuotientGroup.mk' (pCore 2 L) l)) = _
    exact source_central_quotient_apply d l
  · let f : Covering (L ⧸ pCore 2 L) (alternatingGroup (Fin 6)) := {
      toMonoidHom := GLS3.Chapter5.alternatingQuotientHom (source_central_quotient d)
      surjective := (source_central_quotient d).surjective.comp
        (QuotientGroup.mk'_surjective (center (L ⧸ pCore 2 L))) }
    have hk : Nat.card f.toMonoidHom.ker = 3 := by
      have he : f.toMonoidHom.ker = center (L ⧸ pCore 2 L) := by
        ext x
        simp [f, GLS3.Chapter5.alternatingQuotientHom]
      rw [he]
      exact hc
    obtain ⟨e, he⟩ := Representation.Hexacode.CoverComparison.exists_even_equiv_over_coordinate f hk
    refine Or.inr ⟨e, ?_⟩
    intro l
    have h := congrArg (fun F : (L ⧸ pCore 2 L) →* alternatingGroup (Fin 6) =>
      F (QuotientGroup.mk' (pCore 2 L) l)) he
    change Atlas.Codes.hexEvenCoordinate (e (QuotientGroup.mk' (pCore 2 L) l)) =
      source_central_quotient d
        (QuotientGroup.mk' (center (L ⧸ pCore 2 L)) (QuotientGroup.mk' (pCore 2 L) l)) at h
    exact h.trans (source_central_quotient_apply d l)

theorem image_mono (A B : Subgroup G) (h : A ≤ B) :
    image d A ≤ image d B := by
  intro x hx
  obtain ⟨v,hv,rfl⟩ := (mem_image d A x).mp hx
  exact (mem_image d B _).mpr ⟨v,h hv,rfl⟩

theorem flag_preimage (A : Subgroup G) (hA : A ≤ V) :
    A = ((image d A).toAddSubgroup.toSubgroup.comap
      d.coordinate.toMonoidHom).map V.subtype := by
  apply le_antisymm
  · intro x hx
    let v : V := ⟨x,hA hx⟩
    refine ⟨v, ?_,rfl⟩
    exact (mem_image d A _).mpr ⟨v,hx,rfl⟩
  · rintro x ⟨v,hv,rfl⟩
    obtain ⟨w,hw,he⟩ := (mem_image d A _).mp hv
    have heq : w = v := d.coordinate.injective he
    exact heq ▸ hw

theorem centralizer_bot :
    (centralizer (L : Set G)).comap V.subtype = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  have hfix : (d.coordinate v).toAdd ∈
      Representation.invariants (alternatingNaturalRepresentation (Fin 6)) := by
    intro a
    obtain ⟨q, rfl⟩ := d.local_quotient.surjective a
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) q
    have hc : V.normalizerMonoidHom
        ⟨l.val, d.normalizes_V (mem_sup_left l.property)⟩ v = v := by
      apply Subtype.ext
      change l.val * v.val * l.val⁻¹ = v.val
      have hcomm := (mem_centralizer_iff.mp hv) l.val l.property
      change l.val * (V.subtype v) * l.val⁻¹ = V.subtype v
      rw [hcomm, mul_inv_cancel_right]
    have he := d.conjugation l v
    rw [hc] at he
    exact he.symm
  have hz : (d.coordinate v).toAdd = 0 := by
    simpa only [Section08.TransvectionParabolic.Marking.NaturalSection.natural_fixed_eq_bot,
      Submodule.mem_bot] using hfix
  have he : d.coordinate v = 1 := by
    apply Multiplicative.toAdd.injective
    simpa using hz
  exact (Subgroup.mem_bot).mpr (d.coordinate.injective (he.trans (map_one _).symm))

theorem centralPreimage_centralizes : centralPreimage L ≤ centralizer (V : Set G) := by
  rintro _ ⟨l, hl, rfl⟩
  have he : permutation d (inclusion le_sup_left l) = 1 := by
    rw [permutation_L, show QuotientGroup.mk' (centralCore L) l = 1 from
      (QuotientGroup.eq_one_iff l).mpr hl, map_one]
    rfl
  exact (permutation_eq_one_iff d (inclusion le_sup_left l)).mp he

theorem ordinary_natural
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (he : ∀ l : L, e (QuotientGroup.mk' (pCore 2 L) l) =
      d.local_quotient (QuotientGroup.mk' (centralCore L) l)) :
    Nonempty (OrdinarySource.NaturalSetup L (T : Subgroup G) V V₁) := by
  obtain ⟨f,hf,hv⟩ := permutation_extension d
  refine ⟨{
    model := e
    normalizes_L := d.normalizes_L
    normalizes_V := d.normalizes_V
    sylow := T.subtype le_sup_right
    sylow_eq := rfl
    permutation := f
    model_compatible := fun l => (hf l).trans (congrArg Subtype.val (he l)).symm
    naturalMap := d.coordinate.toMonoidHom
    naturalMap_surjective := d.coordinate.surjective
    naturalMap_kernel := ?_
    conjugation := hv
    point := image d V₁
    point_dim := image_dim d V₁
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) 1 (by simpa using d.line_card)
    line_eq := flag_preimage d V₁
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le))
    line_stable := d.line_stable }⟩
  rw [centralizer_bot d]
  exact (MonoidHom.ker_eq_bot_iff _).mpr d.coordinate.injective

theorem covered_natural
    (e : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (he : ∀ l : L,
      Atlas.Codes.hexEvenCoordinate (e (QuotientGroup.mk' (pCore 2 L) l)) =
        d.local_quotient (QuotientGroup.mk' (centralCore L) l)) :
    Nonempty (LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃) := by
  let := elementary d
  let f := (permutation_extension d).choose
  have hf := (permutation_extension d).choose_spec
  refine ⟨{
    cover := e
    normalizes_L := d.normalizes_L
    normalizes_V := d.normalizes_V
    sylow := T.subtype le_sup_right
    sylow_eq := rfl
    elementary := inferInstance
    exponent_two := ?_
    permutation := f
    cover_compatible := ?_
    naturalMap := d.coordinate.toMonoidHom
    naturalMap_surjective := d.coordinate.surjective
    naturalMap_kernel := ?_
    conjugation := hf.2
    point := image d V₁
    hyperplane := image d V₃
    point_dim := ?_
    hyperplane_dim := ?_
    compatible := image_mono d V₁ V₃ (d.line_le_plane.trans d.plane_le_seed)
    line_eq := ?_
    seed_eq := ?_
    line_stable := d.line_stable
    seed_stable := d.seed_stable
    centralPreimage_centralizes := centralPreimage_centralizes d }⟩
  · intro v
    apply d.coordinate.injective
    rw [map_pow, map_one, pow_two]
    change (d.coordinate v).toAdd + (d.coordinate v).toAdd = 0
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  · intro l
    rw [hf.1 l, he l]
  · have hk : d.coordinate.toMonoidHom.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff d.coordinate.toMonoidHom).mpr d.coordinate.injective
    rw [hk, centralizer_bot d]
  · exact image_dim d V₁
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) 1 (by simpa using d.line_card)
  · exact image_dim d V₃ d.seed_le 3 (by simpa using d.seed_card)
  · exact flag_preimage d V₁
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le))
  · exact flag_preimage d V₃ d.seed_le

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions.NaturalModels
