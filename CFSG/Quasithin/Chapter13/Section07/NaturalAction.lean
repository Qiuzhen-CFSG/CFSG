module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.NaturalSetup
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Action
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalHyperplanes
public import Theory.ElementaryAbelian.Injective

/-!
# The original natural action and seed centralizer in Section 13.7

The original central quotient L/O₂,Z(L), its equivariant coordinates on V,
and the Sylow-stable flag determine the full LT action by the proved
normalizer of natural A₆. This retains both ordinary and covered source
cases. The invariant form identifies the hyperplane V₃ with V₁-perpendicular.
Fixing V₃ therefore puts every displacement of V in the original line V₁.

No conjugate-span abelianness, local-core identity or action on U_H is an
input. Source: Aschbacher–Smith, 13.7.1 and proof of 13.7.3, pp.935–936.
-/

@[expose] public section
open Subgroup BinaryPermutation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07.NaturalAction
open Section08.SourceCompletion
open Section08.TransvectionQuotients.FiveSeed.BarMarking
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)

include d

theorem elementary : IsElementaryAbelian 2 V := by
  let : IsElementaryAbelian 2 (Multiplicative (natural (Fin 6))) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun v => by
      rw [pow_two]
      change v.toAdd + v.toAdd = 0
      rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]) }
  exact IsElementaryAbelian.of_injective d.coordinate.toMonoidHom d.coordinate.injective

noncomputable def linearCoordinate :
    letI := elementary d
    Additive V ≃ₗ[ZMod 2] natural (Fin 6) := by
  letI := elementary d
  exact d.coordinate.toAdditiveLeft.toLinearEquiv (ZMod.map_smul _)

theorem permutation_extension :
    ∃ f : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6),
      (∀ l : L, f (inclusion le_sup_left l) =
        (d.local_quotient (QuotientGroup.mk' _ l)).val) ∧
      (∀ (g : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
        (d.coordinate (V.normalizerMonoidHom ⟨g.val, d.normalizes_V g.property⟩ v)).toAdd =
          naturalRepresentation (Fin 6) (f g) (d.coordinate v).toAdd) := by
  let := elementary d
  let α := d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' _)
  have hα : Function.Surjective α :=
    d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨f, hfL, hfV, _⟩ := natural_extension (L ⊔ T) L V le_sup_left
    (sup_le L.le_normalizer d.normalizes_L) d.normalizes_V α hα
    (linearCoordinate d) (fun l v => d.conjugation l v.toMul)
  exact ⟨f, hfL, fun g v => hfV g (Additive.ofMul v)⟩

noncomputable def permutation : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6) :=
  (permutation_extension d).choose

theorem permutation_L (l : L) : permutation d (inclusion le_sup_left l) =
    (d.local_quotient (QuotientGroup.mk' _ l)).val :=
  (permutation_extension d).choose_spec.1 l

theorem conjugation (g : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V) :
    (d.coordinate (V.normalizerMonoidHom ⟨g.val, d.normalizes_V g.property⟩ v)).toAdd =
      naturalRepresentation (Fin 6) (permutation d g) (d.coordinate v).toAdd :=
  (permutation_extension d).choose_spec.2 g v

noncomputable def image (A : Subgroup G) : Submodule (ZMod 2) (natural (Fin 6)) :=
  AddSubgroup.toZModSubmodule 2
    (AddSubgroup.toSubgroup.symm ((A.subgroupOf V).map d.coordinate.toMonoidHom))

theorem mem_image (A : Subgroup G) (w : natural (Fin 6)) :
    w ∈ image d A ↔ ∃ v : V, v.val ∈ A ∧ (d.coordinate v).toAdd = w := Iff.rfl

theorem image_dim (A : Subgroup G) (hA : A ≤ V) (n : ℕ) (hc : Nat.card A = 2 ^ n) :
    Module.finrank (ZMod 2) (image d A) = n := by
  have hcard : Nat.card (image d A) = Nat.card A := by
    change Nat.card ((A.subgroupOf V).map d.coordinate.toMonoidHom) = Nat.card A
    rw [Subgroup.card_map_of_injective d.coordinate.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_eq_fintype_card, ZMod.card, hc] at hcard
  exact Nat.pow_right_injective (by decide : 1 < 2) hcard

theorem alternating_le_range : alternatingGroup (Fin 6) ≤ (permutation d).range := by
  intro a ha
  obtain ⟨q, hq⟩ := d.local_quotient.surjective ⟨a, ha⟩
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective _ q
  refine ⟨inclusion le_sup_left l, ?_⟩
  rw [permutation_L, hl, hq]

theorem image_stable (A : Subgroup G) (hA : (T : Subgroup G) ≤ normalizer (A : Set G)) :
    ((T : Subgroup G).subgroupOf (L ⊔ T)).map (permutation d) ≤
      subspaceStabilizer (naturalRepresentation (Fin 6)) (image d A) := by
  rintro _ ⟨g, hg, rfl⟩ w
  constructor
  · intro hw
    obtain ⟨v, hv, he⟩ := (mem_image d A _).mp hw
    let v' := V.normalizerMonoidHom ⟨g.val⁻¹, d.normalizes_V
      ((L ⊔ (T : Subgroup G)).inv_mem g.property)⟩ v
    apply (mem_image d A w).mpr
    refine ⟨v', (mem_normalizer_iff.mp ((normalizer (A : Set G)).inv_mem (hA hg)) v.val).mp hv, ?_⟩
    rw [show (d.coordinate v').toAdd = naturalRepresentation (Fin 6)
      (permutation d g⁻¹) (d.coordinate v).toAdd from conjugation d g⁻¹ v, he]
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  · intro hw
    obtain ⟨v, hv, rfl⟩ := (mem_image d A _).mp hw
    apply (mem_image d A _).mpr
    refine ⟨V.normalizerMonoidHom ⟨g.val, d.normalizes_V g.property⟩ v,
      (mem_normalizer_iff.mp (hA hg) v.val).mp hv, conjugation d g v⟩

theorem seed_perpendicular : image d V₃ = form.orthogonal (image d V₁) := by
  let f := permutation d
  let Q := (T.subtype (show (T : Subgroup G) ≤ L ⊔ T from le_sup_right)).mapSurjective
    f.rangeRestrict_surjective
  have hQ : (Q : Subgroup f.range).map f.range.subtype =
      ((T : Subgroup G).subgroupOf (L ⊔ T)).map f := by
    rw [Sylow.coe_mapSurjective, map_map, Sylow.coe_subtype]
    rfl
  apply Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalHyperplanes.sylow_invariant_hyperplane_eq_orthogonal
    f.range (alternating_le_range d) Q (image d V₁) (image d V₃)
    (image_dim d V₁ (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) 1 d.line_card)
    (image_dim d V₃ d.seed_le 3 d.seed_card)
  · rw [hQ]
    exact image_stable d V₁ d.line_stable
  · rw [hQ]
    exact image_stable d V₃ d.seed_stable

/-- Fixing the source hyperplane puts every displacement in the original point. -/
theorem seed_centralizer_bound :
    ⁅V, (L ⊔ (T : Subgroup G)) ⊓ centralizer (V₃ : Set G)⁆ ≤ V₁ := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro g hg v hv
  let x : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨g, hg.1⟩
  let w : V := ⟨v, hv⟩
  let c := V.normalizerMonoidHom ⟨g, d.normalizes_V hg.1⟩ w * w⁻¹
  have hfix : ∀ y ∈ image d V₃,
      naturalRepresentation (Fin 6) (permutation d x) y = y := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (mem_image d V₃ y).mp hy
    rw [← conjugation d x a]
    apply congrArg (fun b : V => (d.coordinate b).toAdd)
    apply Subtype.ext
    change g * a.val * g⁻¹ = a.val
    rw [← mem_centralizer_iff.mp hg.2 a.val ha, mul_inv_cancel_right]
  have hc : (d.coordinate c).toAdd ∈ image d V₁ := by
    have horth : (d.coordinate c).toAdd ∈ form.orthogonal (image d V₃) := by
      intro y hy
      have hp := form_invariant (permutation d x) y (d.coordinate w).toAdd
      rw [hfix y hy] at hp
      change form y (d.coordinate c).toAdd = 0
      change form y (d.coordinate (V.normalizerMonoidHom _ w * w⁻¹)).toAdd = 0
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg,
        conjugation d x w, map_sub, hp, sub_self]
    rwa [seed_perpendicular d, LinearMap.BilinForm.orthogonal_orthogonal
      form_nondegenerate form_alt.isRefl] at horth
  obtain ⟨a, ha, he⟩ := (mem_image d V₁ _).mp hc
  have he' : a = c := d.coordinate.injective he
  have hcv : c.val ∈ V₁ := he' ▸ ha
  exact hcv

end CFSG.Quasithin.Chapter13.Section07.NaturalAction
