module

public import Theory.GroupTheory.Recognition.ReeTwo.CentricNormalizerSetup
public import Theory.SpecificGroups.ReeTwo.FirstParabolicAutomorphisms

/-!
# The actual action on the first parabolic core

For any finite group with a Sylow subgroup isomorphic to the Ree two model,
transport the actual action of `N_G(C_S(Z₂(S)))` into the automorphism group of
the model core. Its Sylow two-subgroup is exactly the conjugation image of the
model Sylow group: restrict the ambient Sylow subgroup to the normalizer and
apply the surjective-image theorem to the action homomorphism.

Character invariance under this image is equivalent to the ambient normalizer
condition. The verified four-character action of the concrete core then selects
one of the two alternative characters invariant under the actual normalizer.
Only finiteness and an actual Sylow equivalence are needed; specialization to
the involution-centralizer equivalence gives the recognition interface.

Source: van Beek, *Fusion Systems and Rank 2 Simple Groups of Lie Type*
(2024), Proposition 3.1, p. 10, motivates the model-specific calculation. The
transport and Sylow arguments here are ordinary finite-group arguments.
-/

namespace ReeTwo

variable {G : Type*} [Group G] (S : Sylow 2 G) (e : S ≃* SylowModel)

/-- The ambient exceptional subgroup identified with the concrete model subgroup. -/
private def firstParabolicEquiv :
    firstParabolicCoreIn S e ≃* SylowModel.firstParabolicCore where
  toFun x := ⟨e ⟨x, firstParabolicCoreIn_le S e x.property⟩,
    (mem_firstParabolicCoreIn S e _).mp x.property⟩
  invFun x := ⟨(e.symm x : S), (mem_firstParabolicCoreIn S e _).mpr
    (by simpa only [e.apply_symm_apply] using x.property)⟩
  left_inv x := by
    apply Subtype.ext
    change ((e.symm (e ⟨x.val, firstParabolicCoreIn_le S e x.property⟩) : S) : G) = x.val
    rw [e.symm_apply_apply]
  right_inv x := by apply Subtype.ext; exact e.apply_symm_apply _
  map_mul' x y := by
    apply Subtype.ext
    exact e.map_mul ⟨x.val, firstParabolicCoreIn_le S e x.property⟩
      ⟨y.val, firstParabolicCoreIn_le S e y.property⟩

/-- The actual ambient normalizer action, transported to the model subgroup. -/
public def firstParabolicNormalizerAction :
    Subgroup.normalizer (firstParabolicCoreIn S e : Set G) →*
      MulAut SylowModel.firstParabolicCore :=
  (MulAut.congr (firstParabolicEquiv S e)).toMonoidHom.comp
    (firstParabolicCoreIn S e).normalizerMonoidHom

/-- The whole Sylow subgroup normalizes its characteristic first parabolic core. -/
public theorem sylow_le_firstParabolicNormalizer :
    (S : Subgroup G) ≤ Subgroup.normalizer (firstParabolicCoreIn S e : Set G) :=
  (S : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_firstParabolicCoreIn S e)

/-- On Sylow elements the transported action is exactly model conjugation. -/
public theorem firstParabolicNormalizerAction_sylow (s : S) :
    firstParabolicNormalizerAction S e ⟨s, sylow_le_firstParabolicNormalizer S e s.property⟩ =
      SylowModel.firstParabolicAction (e s) := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change e (s * e.symm x * s⁻¹) = e s * (x : SylowModel) * (e s)⁻¹
  simp

/-- The prescribed model action is a Sylow two-subgroup of the actual automizer.
This uses the Sylow image theorem, with no assumption on the action kernel. -/
public theorem firstParabolicNormalizerAction_sylow_image [Finite G] :
    ∃ P : Sylow 2 (firstParabolicNormalizerAction S e).range,
      (P : Subgroup (firstParabolicNormalizerAction S e).range).map
        (firstParabolicNormalizerAction S e).range.subtype =
          SylowModel.firstParabolicAction.range := by
  let f := firstParabolicNormalizerAction S e
  let T := S.subtype (sylow_le_firstParabolicNormalizer S e)
  refine ⟨T.mapSurjective f.rangeRestrict_surjective, ?_⟩
  change ((T : Subgroup _).map f.rangeRestrict).map f.range.subtype = _
  rw [Subgroup.map_map]
  ext a
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨e ⟨s.val, hs⟩, ?_⟩
    exact (firstParabolicNormalizerAction_sylow S e ⟨s.val, hs⟩).symm
  · rintro ⟨s, rfl⟩
    refine ⟨⟨(e.symm s).val,
      sylow_le_firstParabolicNormalizer S e (e.symm s).property⟩,
      (e.symm s).property, ?_⟩
    change firstParabolicNormalizerAction S e _ = SylowModel.firstParabolicAction s
    rw [firstParabolicNormalizerAction_sylow, e.apply_symm_apply]

private theorem normalizerRespects_of_firstParabolicAction (χ : SylowModel →* FiveFour.Cyclic 2)
    (h : ∀ a ∈ (firstParabolicNormalizerAction S e).range,
      ∀ x : SylowModel.firstParabolicCore, χ (a x : SylowModel) = χ x) :
    NormalizerRespects S e χ (firstParabolicCoreIn S e) := by
  intro g hg x y hx hxy
  let gi : Subgroup.normalizer (firstParabolicCoreIn S e : Set G) :=
    ⟨g⁻¹, (Subgroup.normalizer _).inv_mem hg⟩
  let qx : firstParabolicCoreIn S e := ⟨x.val, hx⟩
  have he := h (firstParabolicNormalizerAction S e gi) ⟨gi, rfl⟩
    (firstParabolicEquiv S e qx)
  have hout :
      (firstParabolicNormalizerAction S e gi (firstParabolicEquiv S e qx) :
        SylowModel) = e y := by
    change e ⟨g⁻¹ * ((firstParabolicEquiv S e).symm
      (firstParabolicEquiv S e qx)).val * (g⁻¹)⁻¹, _⟩ = e y
    apply congrArg e
    apply Subtype.ext
    simpa only [MulEquiv.symm_apply_apply, inv_inv] using hxy
  rw [hout] at he
  exact he.symm

/-- The ambient right-conjugation condition is precisely invariance under the
actual transported automizer. Inversion accounts for the left-conjugation
convention of `Subgroup.normalizerMonoidHom`. -/
public theorem normalizerRespects_firstParabolic_iff (χ : SylowModel →* FiveFour.Cyclic 2) :
    NormalizerRespects S e χ (firstParabolicCoreIn S e) ↔
      ∀ a ∈ (firstParabolicNormalizerAction S e).range,
        ∀ x : SylowModel.firstParabolicCore, χ (a x : SylowModel) = χ x := by
  refine ⟨?_, normalizerRespects_of_firstParabolicAction S e χ⟩
  intro h a ha x
  obtain ⟨g, rfl⟩ := ha
  let q := (firstParabolicEquiv S e).symm x
  let r := (firstParabolicCoreIn S e).normalizerMonoidHom g q
  let sx : S := ⟨q.val, firstParabolicCoreIn_le S e q.property⟩
  let sy : S := ⟨r.val, firstParabolicCoreIn_le S e r.property⟩
  have hx : e sx = (x : SylowModel) :=
    congrArg Subtype.val ((firstParabolicEquiv S e).apply_symm_apply x)
  have hy : e sy = (firstParabolicNormalizerAction S e g x : SylowModel) := rfl
  rw [← hx, ← hy]
  apply Eq.symm
  apply h g.val⁻¹ ((Subgroup.normalizer _).inv_mem g.property) sx sy q.property
  simp only [inv_inv]
  rfl

/-- One of the two alternative characters is invariant under the actual
normalizer of the first parabolic core. The Sylow image of that normalizer
discharges the hypothesis of the concrete automorphism selection theorem. -/
public theorem alternativeCharacters_respect_firstParabolicNormalizer [Finite G] :
    NormalizerRespects S e SylowModel.coreCharacter (firstParabolicCoreIn S e) ∨
      NormalizerRespects S e SylowModel.mixedCharacter (firstParabolicCoreIn S e) := by
  rcases SylowModel.firstParabolic_character_selection
    (firstParabolicNormalizerAction S e).range
    (firstParabolicNormalizerAction_sylow_image S e) with h | h
  · exact Or.inl ((normalizerRespects_firstParabolic_iff S e _).mpr h)
  · exact Or.inr ((normalizerRespects_firstParabolic_iff S e _).mpr h)

/-- Character selection for the Sylow equivalence supplied by the actual
involution centralizer. No simplicity or local solvability assumption is needed. -/
public theorem alternativeCharacters_respect_firstParabolicNormalizer_of_centralizer
    [Finite G] (z : G)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (ec : Subgroup.centralizer {z} ≃* Centralizer) :
    let e := sylowEquivOfCentralizer S z hcentral ec
    NormalizerRespects S e SylowModel.coreCharacter (firstParabolicCoreIn S e) ∨
      NormalizerRespects S e SylowModel.mixedCharacter (firstParabolicCoreIn S e) :=
  alternativeCharacters_respect_firstParabolicNormalizer S
    (sylowEquivOfCentralizer S z hcentral ec)

end ReeTwo
