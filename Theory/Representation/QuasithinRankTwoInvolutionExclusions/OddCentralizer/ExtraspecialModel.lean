module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.ExtraspecialModel.Group
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.ExtraspecialModel.Core
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.ExtraspecialModel.BinaryAction
/-!
# Cubic witnesses for the marked extraspecial-three extension

For an actual subgroup of `Model` containing `fourExtension`, the kernel of
its projection to SD16 is explicitly identified with the Heisenberg group.
The quotient is a two-group, so this kernel is O(H), in the genuine odd-core
convention. The marked third-coordinate generator supplies Z(O(H)).
Faithful binary degree six implies irreducibility on the Heisenberg subgroup,
and therefore supplies the required zero fixed space. This proves the witness
and the rank-two application for every such faithful representation.

The explicit action on three coordinates over F₄ supplies a faithful binary
representation of degree six. We apply the witnesses both to its restrictions
and to actual subgroups between the marked four-group image and the generated
linear image. Their literal inclusions intertwine the representations, and the
image of their odd core is exactly the represented Heisenberg subgroup.

Source: Aschbacher–Smith G.9.4(5), printed pp.354–355; G.11.2(3), printed
p.364; and the proof of 6.2.19, printed p.691. These results supply the concrete
model input to the latter cubic-center exclusion. Recognition of an arbitrary
source group inside this linear model remains a separate G.9.4 theorem.
-/

@[expose] public section

open Representation Subgroup
namespace Representation.RankTwo.ExtraspecialModel

def restrictedProjection (H : Subgroup Model) : H →* S := projection.comp H.subtype

/-- The Heisenberg identification uses the actual projection and inclusion. -/
def kernelEquiv (H : Subgroup Model) (hH : core ≤ H) :
    (restrictedProjection H).ker ≃* P where
  toFun x := x.val.val.left
  invFun p := ⟨⟨SemidirectProduct.inl p, hH (show projection (SemidirectProduct.inl p) = 1 from
    SemidirectProduct.rightHom_inl (φ := action) p)⟩, SemidirectProduct.rightHom_inl (φ := action) p⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact x.property.symm
  right_inv _ := rfl
  map_mul' x y := by
    have hx : x.val.val.right = 1 := x.property
    change (x.val.val * y.val.val).left = x.val.val.left * y.val.val.left
    rw [SemidirectProduct.mul_left, hx, map_one, MulAut.one_apply]

theorem restricted_quotient_two (H : Subgroup Model) :
    IsPGroup 2 (H ⧸ (restrictedProjection H).ker) := by
  have hs : IsPGroup 2 S := IsPGroup.of_card (Semidihedral.standardModel_card 4 (by decide))
  exact (hs.to_subgroup (restrictedProjection H).range).of_equiv
    (QuotientGroup.quotientKerEquivRange (restrictedProjection H)).symm

/-- On each allowed subgroup, the odd core is the actual projection kernel. -/
theorem model_oddCore (H : Subgroup Model) (hH : fourExtension ≤ H) :
    pPrimeCore 2 H = (restrictedProjection H).ker :=
  oddCore_eq_of_heisenberg (restrictedProjection H).ker
    (kernelEquiv H (core_le_fourExtension.trans hH)) (restricted_quotient_two H)

/-- The actual extension supplies the central C3 for every faithful binary
six-dimensional action of each allowed subgroup. -/
theorem model_cubic_witness (H : Subgroup Model) (hH : fourExtension ≤ H)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 6) :
    ∃ c : H, orderOf c = 3 ∧ (zpowers c).Normal ∧
      zpowers c = (center (pPrimeCore 2 H)).map (pPrimeCore 2 H).subtype ∧
      (∀ x, ρ c x = x → x = 0) :=
  exists_cubic_witness (restrictedProjection H).ker
    (kernelEquiv H (core_le_fourExtension.trans hH)) (restricted_quotient_two H) ρ hρ hdim

/-- Application to the rank-two centralization and transitivity consumers. -/
theorem model_rank_two (H : Subgroup Model) (hH : fourExtension ≤ H)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 6) (v : H) (hv : v * v = 1)
    (hrank : Module.finrank (ZMod 2) (movedSpace ρ v) = 2) :
    ∃ c : H, orderOf c = 3 ∧
      zpowers c = (center (pPrimeCore 2 H)).map (pPrimeCore 2 H).subtype ∧
      Commute c v ∧ StabilizerTransitive ρ (movedSpace ρ v) := by
  obtain ⟨c,hc,hn,hz,hfix⟩ := model_cubic_witness H hH ρ hρ hdim
  exact ⟨c,hc,hz,commute_of_rank_two_normal_three ρ v c hdim hv hc hn hfix hrank,
    stabilizerTransitive_of_rank_two_normal_three ρ v c hdim hv hc hn hfix hrank⟩

/-- The constructed binary action discharges both the faithfulness and degree-six
premises of the cubic witness. -/
theorem binary_cubic_witness (H : Subgroup Model) (hH : fourExtension ≤ H) :
    ∃ c : H, orderOf c = 3 ∧ (zpowers c).Normal ∧
      zpowers c = (center (pPrimeCore 2 H)).map (pPrimeCore 2 H).subtype ∧
      (∀ x, BinaryAction.representation c x = x → x = 0) :=
  model_cubic_witness H hH (BinaryAction.representation.comp H.subtype)
    (BinaryAction.representation_restrict_injective H) BinaryAction.finrank_vector

/-- The rank-two centralization and orbit conclusion for the actual binary action. -/
theorem binary_rank_two (H : Subgroup Model) (hH : fourExtension ≤ H)
    (v : H) (hv : v * v = 1)
    (hrank : Module.finrank (ZMod 2)
      (movedSpace (BinaryAction.representation.comp H.subtype) v) = 2) :
    ∃ c : H, orderOf c = 3 ∧
      zpowers c = (center (pPrimeCore 2 H)).map (pPrimeCore 2 H).subtype ∧
      Commute c v ∧ StabilizerTransitive (BinaryAction.representation.comp H.subtype)
        (movedSpace (BinaryAction.representation.comp H.subtype) v) :=
  model_rank_two H hH (BinaryAction.representation.comp H.subtype)
    (BinaryAction.representation_restrict_injective H) BinaryAction.finrank_vector v hv hrank

namespace BinaryAction

/-- The literal linear subgroup is identified with its preimage in the marked model. -/
noncomputable def subgroupEquiv (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hH : H ≤ binaryImage) : H.comap linearAction ≃* H :=
  ((H.comap linearAction).equivMapOfInjective linearAction linearAction_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self (by
      simpa only [binaryImage_eq_range] using hH)))

theorem subgroupEquiv_apply (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hH : H ≤ binaryImage) (g : H.comap linearAction) :
    (subgroupEquiv H hH g : V ≃ₗ[ZMod 2] V) = linearAction g := rfl

/-- Containment of the marked linear four-group extension gives the required
containment in the semidirect-product model. -/
theorem fourExtension_le_comap (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hH : fourImage ≤ H) : fourExtension ≤ H.comap linearAction := by
  apply (Subgroup.map_le_iff_le_comap).mp
  simpa only [map_fourExtension] using hH

/-- The projection to SD₁₆ transported through the actual subgroup equivalence. -/
noncomputable def imageProjection (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hH : H ≤ binaryImage) : H →* S :=
  (restrictedProjection (H.comap linearAction)).comp (subgroupEquiv H hH).symm.toMonoidHom

/-- The transported projection agrees with the original semidirect-product projection. -/
theorem imageProjection_subgroupEquiv (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hH : H ≤ binaryImage) (g : H.comap linearAction) :
    imageProjection H hH (subgroupEquiv H hH g) = projection g := by
  simp only [imageProjection, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, restrictedProjection]
  rfl

/-- The transported projection kernel is the genuine Heisenberg group. -/
noncomputable def imageKernelEquiv (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hlo : fourImage ≤ H) (hhi : H ≤ binaryImage) :
    (imageProjection H hhi).ker ≃* P :=
  ((MulEquiv.subgroupCongr
    (MonoidHom.ker_comp_mulEquiv (restrictedProjection (H.comap linearAction))
      (subgroupEquiv H hhi).symm)).trans
    ((subgroupEquiv H hhi).subgroupMap
      (restrictedProjection (H.comap linearAction)).ker).symm).trans
    (kernelEquiv (H.comap linearAction)
      (core_le_fourExtension.trans (fourExtension_le_comap H hlo)))

/-- The quotient of the represented subgroup by its projection kernel is a two-group. -/
theorem image_quotient_two (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hH : H ≤ binaryImage) : IsPGroup 2 (H ⧸ (imageProjection H hH).ker) := by
  have hs : IsPGroup 2 S := IsPGroup.of_card (Semidihedral.standardModel_card 4 (by decide))
  exact (hs.to_subgroup (imageProjection H hH).range).of_equiv
    (QuotientGroup.quotientKerEquivRange (imageProjection H hH)).symm

/-- The odd core uses the genuine prime-complement core convention. -/
theorem image_oddCore (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hlo : fourImage ≤ H) (hhi : H ≤ binaryImage) :
    pPrimeCore 2 H = (imageProjection H hhi).ker := by
  let : Finite H := Finite.of_equiv (H.comap linearAction) (subgroupEquiv H hhi).toEquiv
  exact oddCore_eq_of_heisenberg (imageProjection H hhi).ker
    (imageKernelEquiv H hlo hhi) (image_quotient_two H hhi)

/-- Under the literal inclusion, the odd core is exactly the represented Heisenberg subgroup. -/
theorem image_oddCore_map (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hlo : fourImage ≤ H) (hhi : H ≤ binaryImage) :
    (pPrimeCore 2 H).map H.subtype = heisenbergImage := by
  have hker : (imageProjection H hhi).ker =
      (restrictedProjection (H.comap linearAction)).ker.map (subgroupEquiv H hhi).toMonoidHom :=
    MonoidHom.ker_comp_mulEquiv (restrictedProjection (H.comap linearAction))
      (subgroupEquiv H hhi).symm
  rw [image_oddCore H hlo hhi, hker, Subgroup.map_map]
  change (restrictedProjection (H.comap linearAction)).ker.map
    (linearAction.comp (H.comap linearAction).subtype) = heisenbergImage
  rw [← Subgroup.map_map]
  change ((core.comap (H.comap linearAction).subtype).map
    (H.comap linearAction).subtype).map linearAction = heisenbergImage
  rw [Subgroup.map_comap_eq_self, map_core]
  rw [Subgroup.range_subtype]
  exact core_le_fourExtension.trans (fourExtension_le_comap H hlo)

/-- The natural action of an actual subgroup of the binary linear group. -/
def imageRepresentation (H : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Representation (ZMod 2) H V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp H.subtype

theorem imageRepresentation_apply (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (g : H) (x : V) : imageRepresentation H g x = (g : V ≃ₗ[ZMod 2] V) x := rfl

theorem imageRepresentation_injective (H : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Function.Injective (imageRepresentation H) := by
  intro g h he
  exact Subtype.ext (LinearEquiv.toLinearMap_injective he)

/-- The group equivalence intertwines the constructed action and the literal linear action. -/
theorem subgroupEquiv_representation (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hH : H ≤ binaryImage) (g : H.comap linearAction) :
    imageRepresentation H (subgroupEquiv H hH g) = representation g := rfl

/-- For every subgroup in the specified linear interval, the central cubic subgroup
of its odd core is normal and has zero fixed space on the actual module. -/
theorem image_cubic_witness (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hlo : fourImage ≤ H) (hhi : H ≤ binaryImage) :
    ∃ c : H, orderOf c = 3 ∧ (zpowers c).Normal ∧
      zpowers c = (center (pPrimeCore 2 H)).map (pPrimeCore 2 H).subtype ∧
      (∀ x, (c : V ≃ₗ[ZMod 2] V) x = x → x = 0) := by
  let : Finite H := Finite.of_equiv (H.comap linearAction) (subgroupEquiv H hhi).toEquiv
  exact exists_cubic_witness (imageProjection H hhi).ker (imageKernelEquiv H hlo hhi)
    (image_quotient_two H hhi) (imageRepresentation H)
    (imageRepresentation_injective H) finrank_vector

/-- The concrete model input to the G.11.2(3) exclusion in 6.2.19: a rank-two
involution centralizes the cubic center, which supplies stabilizer transitivity. -/
theorem image_rank_two (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hlo : fourImage ≤ H) (hhi : H ≤ binaryImage)
    (v : H) (hv : v * v = 1)
    (hrank : Module.finrank (ZMod 2) (movedSpace (imageRepresentation H) v) = 2) :
    ∃ c : H, orderOf c = 3 ∧
      zpowers c = (center (pPrimeCore 2 H)).map (pPrimeCore 2 H).subtype ∧
      Commute c v ∧ StabilizerTransitive (imageRepresentation H)
        (movedSpace (imageRepresentation H) v) := by
  obtain ⟨c, hc, hn, hz, hfix⟩ := image_cubic_witness H hlo hhi
  exact ⟨c, hc, hz,
    commute_of_rank_two_normal_three (imageRepresentation H) v c finrank_vector
      hv hc hn hfix hrank,
    stabilizerTransitive_of_rank_two_normal_three (imageRepresentation H) v c finrank_vector
      hv hc hn hfix hrank⟩

end BinaryAction

end Representation.RankTwo.ExtraspecialModel
