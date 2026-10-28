module
public import Theory.Representation.BinaryAlternatingFiveExtension.IndexTwo
public import Theory.Representation.BinaryAlternatingFiveExtension.SylowModel
public import Theory.Representation.BinaryAlternatingFiveExtension.OuterRecognition
public import Theory.GroupTheory.PCoreSurjective
public import Theory.SpecificGroups.SymmetricFive.AutomorphismRank
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.FivePair.Coordinates
import all Theory.Representation.BinaryAlternatingFiveExtension.OuterRecognition
import all Theory.Representation.BinaryAlternatingFiveExtension.FaithfulExtension

/-!
# Inner automorphisms of the binary affine plane

Every automorphism of the natural binary extension `2⁴ : S₅` is inner.
The translations form its characteristic two-core. The existing index-two
uniqueness theorem consequently makes the affine `A₅` subgroup characteristic.
Its automorphism coordinates and vanishing first cohomology give conjugation
by an element of the full affine group. The affine `A₅` subgroup has trivial
centralizer, so restriction determines an automorphism of the full group.

This is the endpoint alignment used in Aschbacher--Smith F.5.7(1), printed
p.303: a comparison preserving the plane subgroup can be adjusted inside
that plane to preserve its elements individually. The internal imports reuse
the established affine `A₅` coordinate proof without changing its public API.
-/

public noncomputable section
namespace BinaryPermutation.AlternatingFiveExtension.PlaneAutomorphism
open Subgroup OverlapFactorizationExtension
local notation "A" => AlternatingModel
local notation "S5" => Equiv.Perm (Fin 5)
local notation "A5" => alternatingGroup (Fin 5)
private abbrev j := symmetricEmbedding
private instance : Finite A := Finite.of_equiv _ SemidirectProduct.equivProd.symm

private theorem translations_pgroup : IsPGroup 2 V := by
  apply IsPGroup.of_card (n := 4)
  change Nat.card (core (Fin 5)) = 2 ^ 4
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, finrank_core]
  rfl

private theorem alternating_core :
    (SemidirectProduct.rightHom : A →* A5).ker = pCore 2 A := by
  have hp : IsPGroup 2 (SemidirectProduct.rightHom : A →* A5).ker := by
    rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
    exact translations_pgroup.of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have hh := (SemidirectProduct.rightHom : A →* A5).comap_pCore_of_ker_isPGroup
    SemidirectProduct.rightHom_surjective hp
  rwa [Theory.SpecificGroups.SymmetricSix.BinaryFlags.FivePair.alternating_five_twoCore,
    MonoidHom.comap_bot] at hh

private theorem symmetric_core :
    (SemidirectProduct.inl : V →* Model).range = pCore 2 Model := by
  have hp : IsPGroup 2 (SemidirectProduct.rightHom : Model →* S5).ker := by
    rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
    exact translations_pgroup.of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have hh := (SemidirectProduct.rightHom : Model →* S5).comap_pCore_of_ker_isPGroup
    SemidirectProduct.rightHom_surjective hp
  rw [Theory.SpecificGroups.SymmetricFive.pCore_two_eq_bot, MonoidHom.comap_bot] at hh
  exact SemidirectProduct.range_inl_eq_ker_rightHom.trans hh

private theorem ordinary_map (α : MulAut Model) :
    j.range.map α.toMonoidHom = j.range := by
  apply eq_symmetricEmbedding_range_of_index_two
  · have hv : (SemidirectProduct.inl : V →* Model).range ≤ j.range := by
      rintro _ ⟨v, rfl⟩
      exact ⟨SemidirectProduct.inl v, symmetricEmbedding_inl v⟩
    rw [symmetric_core] at hv ⊢
    rw [← pCore_map_iso 2 α]
    exact map_mono hv
  · exact (index_map_of_bijective α.bijective j.range).trans symmetricEmbedding_range_index

private theorem alternating_induced (α : MulAut A) :
    ∃ g : Model, ∀ a : A, j (α a) = g * j a * g⁻¹ := by
  have hQ : ((SemidirectProduct.rightHom : A →* A5).ker).map α.toMonoidHom =
      (SemidirectProduct.rightHom : A →* A5).ker := by
    rw [alternating_core, pCore_map_iso]
  obtain ⟨σ, hσq, hσv⟩ := OuterRecognition.automorphism_coordinates α hQ
  obtain ⟨n, hn⟩ := automorphism_correction SemidirectProduct.rightHom
    SemidirectProduct.rightHom_surjective OuterRecognition.kernelEquiv
    OuterRecognition.kernel_coordinate_action (MulEquiv.refl A) (fun _ => rfl)
    OuterRecognition.kernel_coordinate_mark σ α hσq hσv
  refine ⟨(j n.val)⁻¹ * SemidirectProduct.inr σ, ?_⟩
  intro a
  rw [hn]
  change j (n.val⁻¹ * standardAction σ a * n.val) = _
  rw [map_mul, map_mul, map_inv, symmetricEmbedding_standardAction]
  simp only [MulAut.conj_apply]
  group

private theorem centralizes_ordinary (g : Model)
    (h : ∀ a : A, g * j a = j a * g) : g = 1 := by
  have hr : g.right = 1 := by
    apply OuterRecognition.action_injective
    apply MulEquiv.ext
    intro v
    have hh := congrArg SemidirectProduct.left (h (SemidirectProduct.inl v))
    rw [show j (SemidirectProduct.inl v) = SemidirectProduct.inl v from symmetricEmbedding_inl v] at hh
    change g.left * coreAction g.right v = v * coreAction 1 g.left at hh
    simp only [map_one, MulAut.one_apply] at hh ⊢
    exact mul_left_cancel (hh.trans (mul_comm v g.left))
  have hl : g.left = 1 := by
    apply core_fixed_alternating
    intro a
    have hh := congrArg SemidirectProduct.left (h (SemidirectProduct.inr a))
    simp only [SemidirectProduct.mul_left, j, symmetricEmbedding_left,
      symmetricEmbedding_right, SemidirectProduct.left_inr, SemidirectProduct.right_inr] at hh
    simpa only [map_one, mul_one, one_mul] using hh.symm
  apply SemidirectProduct.ext
  · exact hl
  · exact hr

private instance ordinary_normal : j.range.Normal := by
  change symmetricEmbedding.range.Normal
  rw [symmetricEmbedding_range]
  infer_instance

/-- Every automorphism of the binary affine symmetric-five group is inner. -/
theorem exists_conj (α : MulAut Model) : ∃ g : Model, α = MulAut.conj g := by
  let e : A ≃* j.range := MonoidHom.ofInjective symmetricEmbedding_injective
  let β : MulAut A := e.trans ((α.subgroupMap j.range).trans
    ((MulEquiv.subgroupCongr (ordinary_map α)).trans e.symm))
  have hβ (a : A) : j (β a) = α (j a) := by
    exact congrArg Subtype.val (e.apply_symm_apply _)
  obtain ⟨g, hg⟩ := alternating_induced β
  have hα (a : A) : α (j a) = g * j a * g⁻¹ := (hβ a).symm.trans (hg a)
  let γ : MulAut Model := (MulAut.conj g)⁻¹ * α
  have hγ (a : A) : γ (j a) = j a := by
    change g⁻¹ * α (j a) * g = j a
    rw [hα]
    group
  have hfix (x : Model) : γ x = x := by
    have hc : x⁻¹ * γ x = 1 := by
      apply centralizes_ordinary
      intro a
      have hm : x * j a * x⁻¹ ∈ j.range :=
        (inferInstance : j.range.Normal).conj_mem _ ⟨a, rfl⟩ x
      obtain ⟨b, hb⟩ := hm
      have hh := hγ b
      rw [hb, map_mul, map_mul, map_inv, hγ] at hh
      have hh' := congrArg (fun z => x⁻¹ * z * γ x) hh
      group at hh'
      simpa only [zpow_neg_one, mul_assoc] using hh'
    exact (inv_mul_eq_one.mp hc).symm
  refine ⟨g, ?_⟩
  apply MulEquiv.ext
  intro x
  have hh := hfix x
  change g⁻¹ * α x * g = x at hh
  change α x = g * x * g⁻¹
  have hh' := congrArg (fun z => g * z * g⁻¹) hh
  group at hh'
  simpa only [zpow_neg_one] using hh'

end BinaryPermutation.AlternatingFiveExtension.PlaneAutomorphism
