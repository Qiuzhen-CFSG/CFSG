module

public import Theory.GroupTheory.Recognition.ReeTwo.TransferReduction
public import Theory.SpecificGroups.ReeTwo.FirstParabolic

/-!
# Character conditions on Ree two centric normalizers

The desired common character must respect every actual centric extremal
normalizer. We state that condition with ambient subgroups and right
conjugation, and transport the two alternative characters through the
specified centralizer isomorphism. Both characters respect every normalizer
contained in the given involution centralizer.

The distinguished subgroup for the remaining local analysis is
`C_S(Z₂(S))`. Its normalizer need not lie in the involution centralizer.
Neither invariance under this normalizer nor a common character for all
centric extremal normalizers is asserted here.

Source: van Beek, *Fusion Systems and Rank 2 Simple Groups of Lie Type*
(2024), Proposition 3.1, p. 10; Shinoda (1975), pp. 81–83 for the model
and its specified centralizer action.
-/

namespace ReeTwo

/-- The ambient copy of `C_S(Z₂(S))`, transported from the verified model. -/
@[expose] public def firstParabolicCoreIn
    {G : Type*} [Group G] (S : Sylow 2 G) (e : S ≃* SylowModel) : Subgroup G :=
  (SylowModel.firstParabolicCore.comap e.toMonoidHom).map (S : Subgroup G).subtype

@[simp] public theorem mem_firstParabolicCoreIn
    {G : Type*} [Group G] (S : Sylow 2 G) (e : S ≃* SylowModel) (x : S) :
    (x : G) ∈ firstParabolicCoreIn S e ↔ e x ∈ SylowModel.firstParabolicCore := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have heq : y = x := Subtype.ext hxy
    simpa [heq] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

public theorem firstParabolicCoreIn_le
    {G : Type*} [Group G] (S : Sylow 2 G) (e : S ≃* SylowModel) :
    firstParabolicCoreIn S e ≤ (S : Subgroup G) :=
  Subgroup.map_subtype_le _

/-- The exceptional ambient subgroup is independent of the chosen model
equivalence, since its definition in the model is characteristic. -/
public theorem firstParabolicCoreIn_eq
    {G : Type*} [Group G] (S : Sylow 2 G) (e f : S ≃* SylowModel) :
    firstParabolicCoreIn S e = firstParabolicCoreIn S f := by
  apply congrArg (Subgroup.map (S : Subgroup G).subtype)
  ext x
  change e x ∈ SylowModel.firstParabolicCore ↔ f x ∈ SylowModel.firstParabolicCore
  constructor
  · intro hx
    have h := Subgroup.characteristic_iff_le_comap.mp
      SylowModel.firstParabolicCore_characteristic (e.symm.trans f) hx
    simpa using h
  · intro hx
    have h := Subgroup.characteristic_iff_le_comap.mp
      SylowModel.firstParabolicCore_characteristic (f.symm.trans e) hx
    simpa using h

/-- The Sylow normalizer preserves the exceptional subgroup. -/
public theorem normalizer_le_normalizer_firstParabolicCoreIn
    {G : Type*} [Group G] (S : Sylow 2 G) (e : S ≃* SylowModel) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (firstParabolicCoreIn S e : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := hx
  let f := (S : Subgroup G).normalizerMonoidHom ⟨g, hg⟩
  have h := Subgroup.characteristic_iff_le_comap.mp
    SylowModel.firstParabolicCore_characteristic ((e.symm.trans f).trans e) hy
  have hfy : e (f y) ∈ SylowModel.firstParabolicCore := by simpa using h
  exact ⟨f y, hfy, rfl⟩

/-- A model character respects actual right conjugation by a subgroup's
ambient normalizer. The endpoints lie in the fixed Sylow subgroup. -/
@[expose] public def NormalizerRespects
    {G : Type*} [Group G] (S : Sylow 2 G) (e : S ≃* SylowModel)
    (χ : SylowModel →* FiveFour.Cyclic 2) (U : Subgroup G) : Prop :=
  ∀ g : G, g ∈ Subgroup.normalizer (U : Set G) →
    ∀ x y : S, (x : G) ∈ U → g⁻¹ * (x : G) * g = (y : G) → χ (e x) = χ (e y)

/-- The local character condition needed by centric fusion transport.
Extremality is expressed by equality of the two-parts of normalizer orders. -/
@[expose] public def CentricNormalizerInvariant
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (e : S ≃* SylowModel)
    (χ : SylowModel →* FiveFour.Cyclic 2) : Prop :=
  ∀ U : Subgroup G, U ≤ (S : Subgroup G) →
    (Nat.card ↥((S : Subgroup G) ⊓ Subgroup.normalizer (U : Set G))).factorization 2 =
      (Nat.card (Subgroup.normalizer (U : Set G))).factorization 2 →
    (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) ≤ U →
    NormalizerRespects S e χ U

/-- Exact transport of the core-coordinate character to the ambient Sylow. -/
public theorem coreCharacter_sylowEquivOfCentralizer
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (z : G)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (ec : Subgroup.centralizer {z} ≃* Centralizer) (x : S) :
    SylowModel.coreCharacter (sylowEquivOfCentralizer S z hcentral ec x) =
      Centralizer.coreCharacter (ec ⟨x, hcentral x.property⟩) := by
  simpa only [Centralizer.coreCharacter_embedding] using
    abelianCharacter_sylowEquivOfCentralizer Centralizer.coreCharacter S z hcentral ec x

/-- Exact transport of the product of core-coordinate and parity characters. -/
public theorem mixedCharacter_sylowEquivOfCentralizer
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (z : G)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (ec : Subgroup.centralizer {z} ≃* Centralizer) (x : S) :
    SylowModel.mixedCharacter (sylowEquivOfCentralizer S z hcentral ec x) =
      Centralizer.mixedCharacter (ec ⟨x, hcentral x.property⟩) := by
  simpa only [Centralizer.mixedCharacter_embedding] using
    abelianCharacter_sylowEquivOfCentralizer Centralizer.mixedCharacter S z hcentral ec x

/-- A character extending to the concrete centralizer respects every normalizer
contained in the actual involution centralizer. No extremality is needed. -/
public theorem normalizerRespects_of_centralizerCharacter
    (χ : Centralizer →* FiveFour.Cyclic 2)
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (z : G)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (ec : Subgroup.centralizer {z} ≃* Centralizer) (U : Subgroup G)
    (hU : Subgroup.normalizer (U : Set G) ≤ Subgroup.centralizer {z}) :
    NormalizerRespects S (sylowEquivOfCentralizer S z hcentral ec)
      (χ.comp SylowModel.embedding) U := by
  intro g hg x y _ hxy
  apply abelianCharacter_eq_of_conjugator_mem_centralizer χ S z hcentral ec
    ((Subgroup.centralizer {z}).inv_mem (hU hg))
  simpa only [inv_inv] using hxy

/-- Both alternative characters respect any normalizer contained in `C_G(z)`.
Consequently choosing between them requires no additional compatibility check
at such a normalizer. -/
public theorem alternativeCharacters_respect_centralizer_normalizer
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (z : G)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (ec : Subgroup.centralizer {z} ≃* Centralizer) (U : Subgroup G)
    (hU : Subgroup.normalizer (U : Set G) ≤ Subgroup.centralizer {z}) :
    NormalizerRespects S (sylowEquivOfCentralizer S z hcentral ec)
        SylowModel.coreCharacter U ∧
      NormalizerRespects S (sylowEquivOfCentralizer S z hcentral ec)
        SylowModel.mixedCharacter U := by
  constructor
  · exact normalizerRespects_of_centralizerCharacter Centralizer.coreCharacter
      S z hcentral ec U hU
  · have heq : Centralizer.mixedCharacter.comp SylowModel.embedding =
        SylowModel.mixedCharacter := by
      ext x
      exact Centralizer.mixedCharacter_embedding x
    rw [← heq]
    exact normalizerRespects_of_centralizerCharacter Centralizer.mixedCharacter
      S z hcentral ec U hU

end ReeTwo
