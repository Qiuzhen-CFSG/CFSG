module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.FlagGeometry
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.NaturalSection.Models

/-!
# The covered A₆ source flag

The original natural action extends from L to LT by the concrete linear
normalizer of A₆. The natural module has no L-fixed vector, so the literal
map on V has precisely the required centralizer kernel. The marked triple
cover, actual Sylow restriction and original V₁,V₃ subspaces then form the
covered local setup used in 13.8.5. The separate factorization of L₁ into
L₁,+ and L₀ is not asserted here.

Source: Aschbacher–Smith, Notation 13.2.1 and 13.2.2, pp.877–878.
-/

@[expose] public section

open Subgroup BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition.Component.ModelExtension
open TransvectionQuotients.FiveSeed.BarMarking
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem local_elementary : IsElementaryAbelian 2 V := by
  let : IsElementaryAbelian 2 (Multiplicative (natural (Fin 6))) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun v => by
      rw [pow_two]
      change v.toAdd + v.toAdd = 0
      rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]) }
  exact IsElementaryAbelian.of_injective d.coordinate.toMonoidHom d.coordinate.injective

private noncomputable def local_linearCoordinate :
    letI := local_elementary d
    Additive V ≃ₗ[ZMod 2] natural (Fin 6) := by
  letI := local_elementary d
  exact d.coordinate.toAdditiveLeft.toLinearEquiv (ZMod.map_smul _)

theorem local_permutation_extension :
    ∃ f : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6),
      (∀ l : L, f (inclusion le_sup_left l) =
        (d.local_quotient (QuotientGroup.mk' (centralCore L) l)).val) ∧
      (∀ (g : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
        (d.coordinate (V.normalizerMonoidHom ⟨g.val, d.normalizes_V g.property⟩ v)).toAdd =
          naturalRepresentation (Fin 6) (f g) (d.coordinate v).toAdd) := by
  let := local_elementary d
  let α := d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' _)
  have hα : Function.Surjective α :=
    d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨f, hfL, hfV, _⟩ := natural_extension (L ⊔ T) L V le_sup_left
    (sup_le L.le_normalizer d.normalizes_L) d.normalizes_V α hα
    (local_linearCoordinate d) (fun l v => d.conjugation l v.toMul)
  exact ⟨f, hfL, fun g v => hfV g (Additive.ofMul v)⟩

/-- The original four-dimensional natural module has no L-fixed vector. -/
theorem local_centralizer_bot :
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
    simpa only [TransvectionParabolic.Marking.NaturalSection.natural_fixed_eq_bot,
      Submodule.mem_bot] using hfix
  have he : d.coordinate v = 1 := by
    apply Multiplicative.toAdd.injective
    simpa using hz
  exact (Subgroup.mem_bot).mpr (d.coordinate.injective (he.trans (map_one _).symm))

theorem local_centralPreimage_centralizes :
    centralPreimage L ≤ centralizer (V : Set G) := by
  change (centralCore L).map L.subtype ≤ centralizer (V : Set G)
  rintro _ ⟨l, hl, rfl⟩
  have hm : l ∈ (centralizer (V : Set G)).subgroupOf L := by
    rwa [← d.centralCore_eq_centralizer]
  exact hm

/-- The compatible covered local setup on the literal source flag. -/
theorem local_covered_flag_model
    (e : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (he : ∀ l : L,
      Atlas.Codes.hexEvenCoordinate (e (QuotientGroup.mk' (pCore 2 L) l)) =
        d.local_quotient (QuotientGroup.mk' (centralCore L) l)) :
    Nonempty (LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃) := by
  let := local_elementary d
  let f := (local_permutation_extension d).choose
  have hf := (local_permutation_extension d).choose_spec
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
    point := local_flag_image d V₁
    hyperplane := local_flag_image d V₃
    point_dim := ?_
    hyperplane_dim := ?_
    compatible := local_flag_image_mono d V₁ V₃ (d.line_le_plane.trans d.plane_le_seed)
    line_eq := ?_
    seed_eq := ?_
    line_stable := d.line_stable
    seed_stable := d.seed_stable
    centralPreimage_centralizes := local_centralPreimage_centralizes d }⟩
  · intro v
    apply d.coordinate.injective
    rw [map_pow, map_one, pow_two]
    change (d.coordinate v).toAdd + (d.coordinate v).toAdd = 0
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  · intro l
    rw [hf.1 l, he l]
  · have hk : d.coordinate.toMonoidHom.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff d.coordinate.toMonoidHom).mpr d.coordinate.injective
    rw [hk, local_centralizer_bot d]
  · exact local_flag_image_dim d V₁
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) 1 (by simpa using d.line_card)
  · exact local_flag_image_dim d V₃ d.seed_le 3 (by simpa using d.seed_card)
  · exact local_flag_preimage_cover d V₁
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le))
  · exact local_flag_preimage_cover d V₃ d.seed_le

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion

end
