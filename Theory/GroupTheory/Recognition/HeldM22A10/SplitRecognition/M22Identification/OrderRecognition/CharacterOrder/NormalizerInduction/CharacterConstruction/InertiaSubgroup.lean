module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.Quotient
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.NormalizerAction
public import Theory.Character.AbelianLinearCharacters
public import Theory.GroupAction.SimpleCosets
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The actual character inertia group in Janko's normalizer

The coordinate-sum character of the binary four-space is nonprincipal and
invariant under the marked parity-twisted S4 action. Transport it to the actual
E. Its inertia group in N(E) contains the given involution centralizer E:S4,
so its index divides fifteen. Transitivity on the nonidentity vectors makes
this inertia group proper. In the actual A6 quotient, simplicity and the
coset-action factorial bound exclude indices one, three and five. Thus its
index is fifteen, and its inertia group is exactly the marked centralizer.
There are sixteen linear characters of E, so the orbit consists of all fifteen
nonprincipal characters.

The resulting isomorphism identifies the inertia group with the semidirect
product of the actual E and the original S4 actors, with their actual conjugation
action. The character extends by taking its value on the E coordinate. The
extension is trivial on the marked actors, and restricts to the original
character along the literal subgroup inclusion. The projection to S4 has
exactly the actual E as kernel. These maps support the construction of the five
noninflated normalizer characters.

The arbitrary A6 complement in `LocalAnalysisData.normalizer_E` is used only
for the quotient and order arguments. No containment of the marked actors in
that complement is asserted or needed. The local-analysis input remains with
its existing source assembly owner.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Lemma 6 and Section 6, pp.10–11,
DOI 10.1016/0021-8693(68)90002-1. This supplies a structural construction for
the five rows whose degrees the source obtains by character orthogonality.
-/

open Subgroup
open scoped BigOperators
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy

/-- The coordinate-sum sign, with its small multiplication certificate checked in the kernel. -/
@[expose] public def binaryParitySign : BinaryFour →* ℤ where
  toFun v := if (∑ i, v.toAdd i) = 0 then 1 else -1
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

/-- The complex linear character attached to the sum of the four binary coordinates. -/
@[expose] public def binaryParityCharacter : BinaryFour →* ℂ :=
  (Int.castRingHom ℂ).toMonoidHom.comp binaryParitySign

/-- The original parity-twisted actors fix the coordinate-sum character. -/
public theorem binaryParityCharacter_actor (s : SymmetricFour) (v : BinaryFour) :
    binaryParityCharacter (twistedAction s v) = binaryParityCharacter v := by
  have h : ∀ (s : SymmetricFour) (v : BinaryFour),
      binaryParitySign (twistedAction s v) = binaryParitySign v := by decide +kernel
  exact congrArg (fun x : ℤ => (x : ℂ)) (h s v)

/-- The coordinate character extends trivially across the marked S4. -/
@[expose] public def binaryParityExtension : TwistedModel →* ℂ where
  toFun x := binaryParityCharacter x.left
  map_one' := map_one _
  map_mul' x y := by
    simp only [SemidirectProduct.mul_left, map_mul, binaryParityCharacter_actor]

universe u
variable {G : Type u} [Group G] (D : LocalData G) (k : TwistedModel ≃* D.centralizer)

/-- The marked nonprincipal character on the actual E. -/
@[expose] public def normalizerLinearCharacter : CaseII.E D k →* ℂ :=
  binaryParityCharacter.comp (normalizerVectorEquiv D k).symm.toMonoidHom

/-- Character transport retains the original binary coordinates. -/
public theorem normalizerLinearCharacter_vector (v : BinaryFour) :
    normalizerLinearCharacter D k (normalizerVector D k v) = binaryParityCharacter v := by
  exact congrArg binaryParityCharacter ((normalizerVectorEquiv D k).symm_apply_apply v)

/-- The contragredient action: pull back a character by inverse conjugation. -/
public instance normalizerDualAction : MulAction (normalizer (CaseII.E D k : Set G))
    (CaseII.E D k →* ℂ) where
  smul g χ := χ.comp (normalizerConjugation D k g⁻¹).toMonoidHom
  one_smul χ := by
    ext v
    change χ (normalizerConjugation D k (1⁻¹) v) = χ v
    simp
  mul_smul g h χ := by
    ext v
    change χ (normalizerConjugation D k ((g * h)⁻¹) v) =
      χ (normalizerConjugation D k h⁻¹ (normalizerConjugation D k g⁻¹ v))
    simp

/-- Evaluation of the dual action uses inverse conjugation. -/
public theorem normalizerDualAction_apply
    (g : normalizer (CaseII.E D k : Set G)) (χ : CaseII.E D k →* ℂ) (v : CaseII.E D k) :
    (g • χ) v = χ (normalizerConjugation D k g⁻¹ v) := rfl

/-- The marked character affords a genuine degree-one complex representation. -/
public theorem normalizerLinearCharacter_linear :
    IsLinearCharacter (normalizerLinearCharacter D k : CaseII.E D k → ℂ) :=
  (normalizerLinearCharacter D k).isLinearCharacter

/-- The actual stabilizer of the marked E-character in N(E). -/
@[expose] public def normalizerInertia : Subgroup (normalizer (CaseII.E D k : Set G)) :=
  MulAction.stabilizer _ (normalizerLinearCharacter D k)

/-- Inertia membership is invariance under actual direct conjugation on E. -/
public theorem mem_normalizerInertia (g : normalizer (CaseII.E D k : Set G)) :
    g ∈ normalizerInertia D k ↔ ∀ v,
      normalizerLinearCharacter D k (normalizerConjugation D k g v) =
        normalizerLinearCharacter D k v := by
  change (normalizerLinearCharacter D k).comp
    (normalizerConjugation D k g⁻¹).toMonoidHom = normalizerLinearCharacter D k ↔ _
  constructor
  · intro h v
    have he := DFunLike.congr_fun h (normalizerConjugation D k g v)
    simpa using he.symm
  · intro h
    ext v
    have he := h (normalizerConjugation D k g⁻¹ v)
    simpa using he.symm

/-- The whole marked centralizer fixes the chosen E-character. -/
public theorem normalizerCentralizer_le_inertia :
    (normalizerCentralizer D k).range ≤ normalizerInertia D k := by
  rintro _ ⟨x, rfl⟩
  rw [mem_normalizerInertia]
  intro v
  obtain ⟨w, rfl⟩ := normalizerVector_bijective D k |>.2 v
  have ha : normalizerConjugation D k (normalizerCentralizer D k x)
      (normalizerVector D k w) = normalizerVector D k (twistedAction x.right w) := by
    apply Subtype.ext
    change CaseII.into D k x * CaseII.into D k (SemidirectProduct.inl w) *
      (CaseII.into D k x)⁻¹ = CaseII.into D k (SemidirectProduct.inl (twistedAction x.right w))
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    ext <;> simp [mul_comm]
  rw [ha, normalizerLinearCharacter_vector, normalizerLinearCharacter_vector,
    binaryParityCharacter_actor]


/-- The literal E subgroup of its normalizer lies in the inertia subgroup. -/
public theorem normalizerE_le_inertia :
    (CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G)) ≤
      normalizerInertia D k := by
  intro v hv
  apply normalizerCentralizer_le_inertia D k
  obtain ⟨w, hw⟩ := hv
  exact ⟨SemidirectProduct.inl w, Subtype.ext hw⟩

/-- The chosen character is nonprincipal. -/
public theorem normalizerLinearCharacter_ne_one : normalizerLinearCharacter D k ≠ 1 := by
  intro h
  have he := DFunLike.congr_fun h
    (normalizerVector D k (Multiplicative.ofAdd ![1, 0, 0, 0]))
  rw [normalizerLinearCharacter_vector] at he
  change (binaryParitySign (Multiplicative.ofAdd ![1, 0, 0, 0]) : ℂ) = 1 at he
  rw [show binaryParitySign (Multiplicative.ofAdd ![1, 0, 0, 0]) = -1 from by decide +kernel] at he
  norm_num at he

variable [Finite G]

omit [Finite G] in
/-- The marked semidirect product has order 384. -/
public theorem normalizerCentralizer_range_card : Nat.card (normalizerCentralizer D k).range = 384 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (normalizerCentralizer_injective D k)).toEquiv,
    Nat.card_congr k.toEquiv, D.centralizer_card]

omit [Finite G] in
/-- Its index in the actual normalizer is fifteen. -/
public theorem normalizerCentralizer_range_index (L : LocalAnalysisData D k) :
    (normalizerCentralizer D k).range.index = 15 := by
  have h := (normalizerCentralizer D k).range.card_mul_index
  rw [normalizerCentralizer_range_card, normalizer_E_card D k L] at h
  omega

/-- Vector transitivity prevents the nonprincipal character from being invariant. -/
public theorem normalizerInertia_ne_top (L : LocalAnalysisData D k) : normalizerInertia D k ≠ ⊤ := by
  intro htop
  obtain ⟨K, hK, ⟨eK⟩⟩ := L.normalizer_E
  have hc : Nat.card (CaseII.eNormalizerQuotient D k) = 360 := by
    rw [Nat.card_congr (hK.symm.QuotientMulEquiv.trans eK).toEquiv,
      nat_card_alternatingGroup, Nat.card_fin]
    decide
  let v := Multiplicative.ofAdd ![1, 0, 0, 0] (α := Fin 4 → ZMod 2)
  have hv : normalizerVector D k v ≠ 1 := by
    intro he
    have he' := (normalizerVector_bijective D k).1 (he.trans (map_one _).symm)
    have h0 := congrArg (fun w : BinaryFour => w.toAdd 0) he'
    norm_num [v] at h0
  obtain ⟨g, hg⟩ := CaseII.E_fusion_of_quotient_card D k hc
    (normalizerVector D k v) (CaseII.eNormalizerPoint D k) hv
    (CaseII.eNormalizerPoint_ne_one D k)
  have hfix := (mem_normalizerInertia D k g).mp (htop ▸ mem_top g)
    (normalizerVector D k v)
  have he : normalizerConjugation D k g (normalizerVector D k v) =
      normalizerVector D k (Multiplicative.ofAdd ![1, 1, 1, 1]) := by
    apply Subtype.ext
    exact hg.trans (CaseII.into_z_zero D k).symm
  rw [he, normalizerLinearCharacter_vector, normalizerLinearCharacter_vector] at hfix
  change (binaryParitySign (Multiplicative.ofAdd ![1, 1, 1, 1]) : ℂ) =
    (binaryParitySign v : ℂ) at hfix
  rw [show binaryParitySign (Multiplicative.ofAdd ![1, 1, 1, 1]) = 1 from by decide +kernel,
    show binaryParitySign v = -1 from by decide +kernel] at hfix
  norm_num at hfix

/-- The A6 quotient excludes every proper divisor of the index fifteen. -/
public theorem normalizerInertia_index (L : LocalAnalysisData D k) :
    (normalizerInertia D k).index = 15 := by
  have hd : (normalizerInertia D k).index ∣ 15 := by
    rw [← normalizerCentralizer_range_index D k L]
    exact index_dvd_of_le (normalizerCentralizer_le_inertia D k)
  obtain ⟨π, hπ, hker⟩ := exists_normalizerQuotient D k L
  let J := (normalizerInertia D k).map π
  have hidx : J.index = (normalizerInertia D k).index :=
    (normalizerInertia D k).index_map_eq hπ (hker ▸ normalizerE_le_inertia D k)
  have hj : J ≠ ⊤ := by
    intro ht
    apply normalizerInertia_ne_top D k L
    apply index_eq_one.mp
    rw [← hidx, ht, index_top]
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hf := J.card_dvd_factorial_index_of_simple hj
  rw [nat_card_alternatingGroup, Nat.card_fin, hidx] at hf
  have hle : (normalizerInertia D k).index ≤ 15 := Nat.le_of_dvd (by decide) hd
  interval_cases h : (normalizerInertia D k).index <;> norm_num [h, Nat.factorial] at *

/-- The actual inertia subgroup has order 384. -/
public theorem normalizerInertia_card (L : LocalAnalysisData D k) :
    Nat.card (normalizerInertia D k) = 384 := by
  have h := (normalizerInertia D k).card_mul_index
  rw [normalizerInertia_index D k L, normalizer_E_card D k L] at h
  omega

/-- The inertia subgroup is precisely the image of the marked semidirect product. -/
public theorem normalizerInertia_eq_range (L : LocalAnalysisData D k) :
    normalizerInertia D k = (normalizerCentralizer D k).range := by
  exact (Subgroup.eq_of_le_of_card_ge (normalizerCentralizer_le_inertia D k)
    (by rw [normalizerInertia_card D k L, normalizerCentralizer_range_card])).symm


/-- All fifteen nonprincipal E-characters form one actual normalizer orbit. -/
public theorem normalizerDualOrbit_eq_nonprincipal (L : LocalAnalysisData D k) :
    MulAction.orbit (normalizer (CaseII.E D k : Set G)) (normalizerLinearCharacter D k) =
      {1}ᶜ := by
  let : IsElementaryAbelian 2 (CaseII.E D k) := L.E_elementary
  apply Set.eq_of_subset_of_ncard_le
  · intro χ hχ hχ1
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hχ
    apply normalizerLinearCharacter_ne_one D k
    ext v
    have he := DFunLike.congr_fun hχ1 (normalizerConjugation D k g v)
    change normalizerLinearCharacter D k
      (normalizerConjugation D k g⁻¹ (normalizerConjugation D k g v)) = 1 at he
    simpa using he
  · rw [Set.ncard_compl, Set.ncard_singleton, AbelianLinearCharacters.card, L.E_card,
      ← MulAction.index_stabilizer]
    exact le_of_eq (normalizerInertia_index D k L).symm
  · exact Set.toFinite _

/-- The dual orbit has size fifteen. -/
public theorem normalizerDualOrbit_card (L : LocalAnalysisData D k) :
    (MulAction.orbit (normalizer (CaseII.E D k : Set G))
      (normalizerLinearCharacter D k)).ncard = 15 := by
  rw [← MulAction.index_stabilizer]
  exact normalizerInertia_index D k L

/-- Every nonprincipal E-character is an actual conjugate of the chosen character. -/
public theorem normalizerDualOrbit_covers (L : LocalAnalysisData D k)
    (χ : CaseII.E D k →* ℂ) (hχ : χ ≠ 1) :
    ∃ g : normalizer (CaseII.E D k : Set G),
      χ = (normalizerLinearCharacter D k).comp
        (normalizerConjugation D k g).toMonoidHom := by
  have hm : χ ∈ MulAction.orbit (normalizer (CaseII.E D k : Set G))
      (normalizerLinearCharacter D k) := by
    rw [normalizerDualOrbit_eq_nonprincipal D k L]
    exact hχ
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hm
  exact ⟨g⁻¹, hg.symm⟩

/-- The isomorphism retains both the binary and the actor marking. -/
@[expose] public def normalizerInertiaEquiv (L : LocalAnalysisData D k) :
    TwistedModel ≃* normalizerInertia D k :=
  (MonoidHom.ofInjective (normalizerCentralizer_injective D k)).trans
    (MulEquiv.subgroupCongr (normalizerInertia_eq_range D k L).symm)

/-- The inertia isomorphism is the original marked centralizer embedding. -/
public theorem normalizerInertiaEquiv_coe (L : LocalAnalysisData D k) (x : TwistedModel) :
    (normalizerInertiaEquiv D k L x : normalizer (CaseII.E D k : Set G)) =
      normalizerCentralizer D k x := rfl

/-- On the binary factor, the isomorphism is exactly normalizerVector. -/
public theorem normalizerInertiaEquiv_vector (L : LocalAnalysisData D k) (v : BinaryFour) :
    ((normalizerInertiaEquiv D k L (SemidirectProduct.inl v) :
      normalizer (CaseII.E D k : Set G)) : G) = normalizerVector D k v := rfl

/-- On the S4 factor, the isomorphism is exactly normalizerActor. -/
public theorem normalizerInertiaEquiv_actor (L : LocalAnalysisData D k) (s : SymmetricFour) :
    (normalizerInertiaEquiv D k L (SemidirectProduct.inr s) :
      normalizer (CaseII.E D k : Set G)) = normalizerActor D k s := rfl

/-- The character extension is trivial on the original marked S4 actors. -/
@[expose] public def normalizerInertiaExtension (L : LocalAnalysisData D k) : normalizerInertia D k →* ℂ :=
  binaryParityExtension.comp (normalizerInertiaEquiv D k L).symm.toMonoidHom

/-- The extension reads the binary coordinate in the original model. -/
public theorem normalizerInertiaExtension_apply (L : LocalAnalysisData D k) (x : TwistedModel) :
    normalizerInertiaExtension D k L (normalizerInertiaEquiv D k L x) =
      binaryParityCharacter x.left := by
  change binaryParityExtension ((normalizerInertiaEquiv D k L).symm
    (normalizerInertiaEquiv D k L x)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- On each marked vector, the extension agrees with the E-character. -/
public theorem normalizerInertiaExtension_vector (L : LocalAnalysisData D k) (v : BinaryFour) :
    normalizerInertiaExtension D k L
      (normalizerInertiaEquiv D k L (SemidirectProduct.inl v)) =
        normalizerLinearCharacter D k (normalizerVector D k v) := by
  rw [normalizerInertiaExtension_apply, normalizerLinearCharacter_vector]
  rfl

/-- The extension is one on each original marked S4 actor. -/
public theorem normalizerInertiaExtension_actor (L : LocalAnalysisData D k) (s : SymmetricFour) :
    normalizerInertiaExtension D k L
      (normalizerInertiaEquiv D k L (SemidirectProduct.inr s)) = 1 := by
  rw [normalizerInertiaExtension_apply, SemidirectProduct.left_inr, map_one]

/-- The extension affords a genuine one-dimensional complex representation. -/
public theorem normalizerInertiaExtension_linear (L : LocalAnalysisData D k) :
    IsLinearCharacter (normalizerInertiaExtension D k L : normalizerInertia D k → ℂ) :=
  (normalizerInertiaExtension D k L).isLinearCharacter


/-- The actual inertia quotient map to the original S4 actor labels. -/
@[expose] public def normalizerInertiaProjection (L : LocalAnalysisData D k) :
    normalizerInertia D k →* SymmetricFour :=
  SemidirectProduct.rightHom.comp (normalizerInertiaEquiv D k L).symm.toMonoidHom

/-- The quotient map reads the original actor coordinate. -/
public theorem normalizerInertiaProjection_apply (L : LocalAnalysisData D k) (x : TwistedModel) :
    normalizerInertiaProjection D k L (normalizerInertiaEquiv D k L x) = x.right := by
  change ((normalizerInertiaEquiv D k L).symm (normalizerInertiaEquiv D k L x)).right = _
  rw [MulEquiv.symm_apply_apply]

/-- All original S4 actors occur in the inertia quotient. -/
public theorem normalizerInertiaProjection_surjective (L : LocalAnalysisData D k) :
    Function.Surjective (normalizerInertiaProjection D k L) := by
  intro s
  exact ⟨normalizerInertiaEquiv D k L (SemidirectProduct.inr s),
    normalizerInertiaProjection_apply D k L _⟩

/-- The quotient kernel is exactly the actual E restricted to the inertia subgroup. -/
public theorem normalizerInertiaProjection_ker (L : LocalAnalysisData D k) :
    (normalizerInertiaProjection D k L).ker =
      ((CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G))).subgroupOf
        (normalizerInertia D k) := by
  ext x
  obtain ⟨t, rfl⟩ := (normalizerInertiaEquiv D k L).surjective x
  change normalizerInertiaProjection D k L (normalizerInertiaEquiv D k L t) = 1 ↔
    normalizerCentralizer D k t ∈
      (CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G))
  rw [normalizerInertiaProjection_apply, normalizerCentralizer_mem_E]

omit [Finite G] in
/-- The same character on the literal normal subgroup E of N(E). -/
@[expose] public def normalizerECharacter :
    (CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G)) →* ℂ :=
  (normalizerLinearCharacter D k).comp
    (subgroupOfEquivOfLe (CaseII.E D k).le_normalizer).toMonoidHom

/-- The extension restricts along the literal subgroup inclusion to the chosen E-character. -/
public theorem normalizerInertiaExtension_restrict (L : LocalAnalysisData D k) :
    (normalizerInertiaExtension D k L).comp
      (Subgroup.inclusion (normalizerE_le_inertia D k)) = normalizerECharacter D k := by
  ext x
  obtain ⟨v, hv⟩ := (normalizerVector_bijective D k).2
    ((subgroupOfEquivOfLe (CaseII.E D k).le_normalizer) x)
  have hx : Subgroup.inclusion (normalizerE_le_inertia D k) x =
      normalizerInertiaEquiv D k L (SemidirectProduct.inl v) := by
    apply Subtype.ext
    apply Subtype.ext
    exact (congrArg (fun t : CaseII.E D k => (t : G)) hv).symm
  change normalizerInertiaExtension D k L
    (Subgroup.inclusion (normalizerE_le_inertia D k) x) = _
  rw [hx, normalizerInertiaExtension_vector, hv]
  rfl


omit [Finite G] in
/-- The model image is the actual centralizer restricted to N(E). -/
public theorem normalizerCentralizer_range :
    (normalizerCentralizer D k).range =
      D.centralizer.subgroupOf (normalizer (CaseII.E D k : Set G)) := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact (k x).property
  · intro hg
    refine ⟨k.symm ⟨g, hg⟩, ?_⟩
    apply Subtype.ext
    exact congrArg (fun t : D.centralizer => (t : G)) (k.apply_symm_apply ⟨g, hg⟩)

/-- The actual character inertia subgroup is the marked involution centralizer. -/
public theorem normalizerInertia_eq_centralizer (L : LocalAnalysisData D k) :
    normalizerInertia D k =
      D.centralizer.subgroupOf (normalizer (CaseII.E D k : Set G)) := by
  rw [normalizerInertia_eq_range D k L, normalizerCentralizer_range]

omit [Finite G] in
/-- Conjugation on the actual E by the original marked S4 actors. -/
@[expose] public def normalizerActorAction : SymmetricFour →* MulAut (CaseII.E D k) :=
  (normalizerConjugation D k).comp (normalizerActor D k)

omit [Finite G] in
/-- The binary model agrees with the semidirect product using the actual E and its actual action. -/
@[expose] public def normalizerSemidirectCoordinates : TwistedModel ≃*
    (CaseII.E D k) ⋊[normalizerActorAction D k] SymmetricFour :=
  SemidirectProduct.congr (normalizerVectorEquiv D k) (MulEquiv.refl _)
    (fun s => by
      apply MulEquiv.ext
      intro v
      exact (normalizerConjugation_actor D k s v).symm)

/-- The actual inertia subgroup is E semidirect S4, with the given marking. -/
@[expose] public def normalizerInertiaSemidirectEquiv (L : LocalAnalysisData D k) :
    (CaseII.E D k) ⋊[normalizerActorAction D k] SymmetricFour ≃* normalizerInertia D k :=
  (normalizerSemidirectCoordinates D k).symm.trans (normalizerInertiaEquiv D k L)

/-- The semidirect isomorphism multiplies the actual vector and marked actor. -/
public theorem normalizerInertiaSemidirectEquiv_coe (L : LocalAnalysisData D k)
    (x : (CaseII.E D k) ⋊[normalizerActorAction D k] SymmetricFour) :
    ((normalizerInertiaSemidirectEquiv D k L x : normalizer (CaseII.E D k : Set G)) : G) =
      (x.left : G) * (normalizerActor D k x.right : G) := by
  change CaseII.into D k ⟨(normalizerVectorEquiv D k).symm x.left, x.right⟩ = _
  rw [SemidirectProduct.mk_eq_inl_mul_inr, map_mul]
  congr 1
  exact congrArg (fun t : CaseII.E D k => (t : G))
    ((normalizerVectorEquiv D k).apply_symm_apply x.left)

/-- In actual semidirect coordinates, the extension takes its value on E. -/
public theorem normalizerInertiaSemidirectExtension (L : LocalAnalysisData D k)
    (x : (CaseII.E D k) ⋊[normalizerActorAction D k] SymmetricFour) :
    normalizerInertiaExtension D k L (normalizerInertiaSemidirectEquiv D k L x) =
      normalizerLinearCharacter D k x.left := by
  rw [normalizerInertiaSemidirectEquiv, MulEquiv.trans_apply, normalizerInertiaExtension_apply]
  rfl

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
