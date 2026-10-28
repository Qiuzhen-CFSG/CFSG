module

public import Theory.Representation.G2NaturalOuterOffenders
public import Theory.Representation.G2NaturalTransitivity
public import Theory.Representation.G2NaturalFaithfulness
public import Theory.Representation.FirstCohomologyG2Natural.Commutant
public import Theory.Representation.BinaryOffender.NormalizerImage
public import Theory.Representation.BinaryOffender.InnerNormalizerActors

/-!
# Offenders in the full natural G₂ normalizer and original ambient actors

Faithfulness identifies normalizer conjugation with an actual G₂ automorphism.
The proved inner-field description and scalar commutant express its operator
as a scalar times the specified inner and coefficient operators. Field
involutions move half the binary space; their elementary subgroups have
strictly smaller rank. Inner involutions have scalar one in characteristic
two. Consequently every offender of the full linear normalizer is inner.

The last theorem transports this conclusion through a literal natural-action
marking of a normal subgroup in the original faithful ambient representation.
No ambient semilinearity, scalar factor or offender containment is assumed.
Source: Aschbacher–Smith B.4.6(9), (13), printed pp.89–90.
-/

public noncomputable section
namespace Atlas.G2.Natural.Normalizer
open Representation Representation.BinaryOffender Subgroup
attribute [local instance] ZMod.algebra
variable (F : Type*) [Field F] [CharP F 2]

def binary := Representation.restrictScalars (k := ZMod 2) (Natural.action F)

/-- The binary action is the scalar restriction of the actual natural operator. -/
theorem binary_apply (g : Model F) :
    binary F g = (Natural.action F g).restrictScalars (ZMod 2) := by rfl

theorem binary_faithful : Function.Injective (binary F) := by
  intro g h he
  apply Natural.action_injective F
  exact LinearMap.ext (fun v => LinearMap.congr_fun he v)

theorem centralizer_scalar (f : Space F →+ Space F)
    (hf : ∀ g v, f (Natural.action F g v) = Natural.action F g (f v)) :
    ∃ c : F, ∀ v, f v = c • v :=
  exists_scalar_of_additive_commutes_derived f (fun g v => hf g v)

theorem field_smul (σ : F ≃+* F) (c : F) (v : Space F) :
    BinarySemilinear.fieldEquivalence F σ (c • v) =
      σ c • BinarySemilinear.fieldEquivalence F σ v := by
  apply (BinarySemilinear.coordinatesEquiv F).injective
  simp only [BinarySemilinear.fieldEquivalence, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  change (fun i => σ (Restricted.NaturalCoordinates.equiv F (c • v) i)) =
    Restricted.NaturalCoordinates.equiv F
      (σ c • (Restricted.NaturalCoordinates.equiv F).symm
        (fun i => σ (Restricted.NaturalCoordinates.equiv F v i)))
  rw [map_smul, map_smul, LinearEquiv.apply_symm_apply]
  ext i
  exact map_mul σ c _

/-- Actual normalizer conjugation, transported back along the faithful action image. -/
def normalizerAutomorphism :
    linearNormalizer (binary F) →* MulAut (Model F) :=
  let hf : Function.Injective (binary F).asGroupHom :=
    fun _ _ h => binary_faithful F (congrArg Units.val h)
  let e : Model F ≃* actionImage (binary F) := MonoidHom.ofInjective hf
  (MulAut.congr e.symm).toMonoidHom.comp (actionImage (binary F)).normalizerMonoidHom

/-- The transported automorphism retains the original normalizer operator. -/
theorem normalizerAutomorphism_intertwines
    (t : linearNormalizer (binary F)) (g : Model F) (v : Space F) :
    t.val.val (Natural.action F g v) =
      Natural.action F (normalizerAutomorphism F t g) (t.val.val v) := by
  let hf : Function.Injective (binary F).asGroupHom :=
    fun _ _ h => binary_faithful F (congrArg Units.val h)
  let e : Model F ≃* actionImage (binary F) := MonoidHom.ofInjective hf
  let t' : normalizer (actionImage (binary F) : Set (Module.End (ZMod 2) (Space F))ˣ) := ⟨t.val, t.property⟩
  have he : (binary F).asGroupHom (normalizerAutomorphism F t g) =
      t.val * (binary F).asGroupHom g * t.val⁻¹ := by
    change (e (e.symm ((actionImage (binary F)).normalizerMonoidHom t' (e g)))).val = _
    rw [e.apply_symm_apply]
    rfl
  have hh := congrArg (fun u : (Module.End (ZMod 2) (Space F))ˣ =>
    u.val (t.val.val v)) he
  have hinv : (t.val⁻¹).val (t.val.val v) = v := by
    change (t.val⁻¹ * t.val).val v = v
    rw [inv_mul_cancel]
    rfl
  change Natural.action F (normalizerAutomorphism F t g) (t.val.val v) =
    t.val.val (Natural.action F g ((t.val⁻¹).val (t.val.val v))) at hh
  rw [hinv] at hh
  exact hh.symm

local notation "V" => Space F

private theorem coefficient_one (v : V) :
    BinarySemilinear.fieldEquivalence F (1 : F ≃+* F) v = v := by
  apply (BinarySemilinear.coordinatesEquiv F).injective
  exact (BinarySemilinear.coordinatesEquiv F).apply_symm_apply _

/-- A literal normalizer operator over an inner-field automorphism differs only
by a field scalar from the specified inner and coefficient operators. -/
theorem normalizer_scalar_factor
    (t : linearNormalizer (binary F)) (g : Model F) (σ : F ≃+* F)
    (ha : normalizerAutomorphism F t =
      MulAut.conj g * LieAutomorphismExtensions.fieldAction σ) :
    ∃ c : F, ∀ v : V, t.val.val v =
      c • Natural.action F g (BinarySemilinear.fieldEquivalence F σ v) := by
  let τ := BinarySemilinear.fieldEquivalence F σ
  have hc (h : Model F) (v : V) :
      τ.symm (Natural.action F (fieldEquiv σ h) v) =
        Natural.action F h (τ.symm v) := by
    apply τ.injective
    rw [τ.apply_symm_apply, BinarySemilinear.fieldEquivalence_action,
      τ.apply_symm_apply]
  have hg (h : Model F) (v : V) :
      Natural.action F g⁻¹ (Natural.action F (normalizerAutomorphism F t h) v) =
      Natural.action F (fieldEquiv σ h) (Natural.action F g⁻¹ v) := by
    have he : g⁻¹ * normalizerAutomorphism F t h = fieldEquiv σ h * g⁻¹ := by
      rw [ha]
      change g⁻¹ * (g * fieldEquiv σ h * g⁻¹) = _
      group
    simp only [← Module.End.mul_apply, ← map_mul, he]
  let f : V →+ V := τ.symm.toAddEquiv.toAddMonoidHom.comp
    ((Natural.action F g⁻¹).toAddMonoidHom.comp t.val.val.toAddMonoidHom)
  obtain ⟨c, hc'⟩ := centralizer_scalar F f (by
    intro h v
    change τ.symm (Natural.action F g⁻¹ (t.val.val (Natural.action F h v))) = _
    rw [normalizerAutomorphism_intertwines F t h v, hg, hc]
    rfl)
  refine ⟨σ c, fun v => ?_⟩
  have h := congrArg (fun w : V => Natural.action F g (τ w)) (hc' v)
  change Natural.action F g (τ (τ.symm (Natural.action F g⁻¹ (t.val.val v)))) = _ at h
  rw [τ.apply_symm_apply] at h
  simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] at h
  change t.val.val v = Natural.action F g (BinarySemilinear.fieldEquivalence F σ (c • v)) at h
  rwa [field_smul F, map_smul] at h

variable [Finite F]

/-- Nontrivial coefficient involutions move exactly half the binary natural space. -/
theorem field_involution_codim (hq : 2 < Nat.card F)
    {r : ℕ} (hF : Nat.card F = 2 ^ r)
    (t : linearNormalizer (binary F)) (ht : t ^ 2 = 1)
    (z : Model F ⋊[LieAutomorphismExtensions.fieldAction] (F ≃+* F))
    (hz : LieAutomorphismExtensions.semilinearAction z = normalizerAutomorphism F t)
    (hσ : z.right ≠ 1) :
    fixedCodim (normalizerRepresentation (binary F)) (zpowers t) = 3 * r := by
  have hz2 : z ^ 2 = 1 := by
    apply LieAutomorphismExtensions.semilinearAction_injective hq
    rw [map_pow, hz, ← map_pow, ht, map_one, map_one]
  have hσ2 : z.right ^ 2 = 1 := congrArg SemidirectProduct.right hz2
  have ht1 : t ≠ 1 := by
    intro he
    have hz1 : z = 1 := by
      apply LieAutomorphismExtensions.semilinearAction_injective hq
      rw [hz, he, map_one, map_one]
    exact hσ (congrArg SemidirectProduct.right hz1)
  obtain ⟨c, hc⟩ := normalizer_scalar_factor F t z.left z.right hz.symm
  have hsemi (a : F) (v : V) :
      normalizerRepresentation (binary F) t (a • v) =
        z.right a • normalizerRepresentation (binary F) t v := by
    change t.val.val (a • v) = z.right a • t.val.val v
    rw [hc, hc, field_smul F, map_smul, smul_comm]
  let : FiniteDimensional F V := (Restricted.NaturalCoordinates.equiv F).symm.finiteDimensional
  have hh := Representation.FiniteFieldSemilinearDisplacement.fixedCodim_formula
    (normalizerRepresentation (binary F)) (by decide : 0 < 2)
    t (orderOf_eq_prime ht ht1) z.right (orderOf_eq_prime hσ2 hσ) hsemi
  have hdimF : Module.finrank (ZMod 2) F = r := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    exact (FiniteField.pow_finrank_eq_natCard 2 F).trans hF
  rw [hdimF, Natural.finrank_space] at hh
  omega

/-- If the field component is trivial, an involutory normalizer operator is inner.
The scalar factor is forced to one, rather than assumed absent. -/
theorem inner_involution_mem (hq : 2 < Nat.card F)
    (t : linearNormalizer (binary F)) (ht : t ^ 2 = 1)
    (z : Model F ⋊[LieAutomorphismExtensions.fieldAction] (F ≃+* F))
    (hz : LieAutomorphismExtensions.semilinearAction z = normalizerAutomorphism F t)
    (hσ : z.right = 1) :
    t ∈ (normalizerEmbedding (binary F)).range := by
  have hz2 : z ^ 2 = 1 := by
    apply LieAutomorphismExtensions.semilinearAction_injective hq
    rw [map_pow, hz, ← map_pow, ht, map_one, map_one]
  have hg2 : z.left ^ 2 = 1 := by
    have h := congrArg SemidirectProduct.left hz2
    simpa [pow_two, hσ] using h
  obtain ⟨c, hc⟩ := normalizer_scalar_factor F t z.left z.right hz.symm
  have htv (v : V) : t.val.val v = c • Natural.action F z.left v := by
    have he : BinarySemilinear.fieldEquivalence F z.right v = v :=
      (congrArg (fun σ : F ≃+* F => BinarySemilinear.fieldEquivalence F σ v) hσ).trans
        (coefficient_one F v)
    simpa only [he] using hc v
  have hs (v : V) : (c ^ 2) • v = v := by
    have he := congrArg (fun u : linearNormalizer (binary F) => u.val.val v) ht
    change t.val.val (t.val.val v) = v at he
    rw [htv, htv, map_smul, smul_smul, ← pow_two,
      ← Module.End.mul_apply, ← map_mul, ← pow_two, hg2, map_one,
      Module.End.one_apply] at he
    exact he
  have hc2 : c ^ 2 = 1 := by
    have he := congrArg (fun v : V => Restricted.NaturalCoordinates.equiv F v 0)
      (hs ((Restricted.NaturalCoordinates.equiv F).symm (Pi.single 0 1)))
    simpa only [map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply,
      smul_eq_mul, Pi.single_eq_same, mul_one] using he
  have hc1 : c = 1 := by
    rcases sq_eq_one_iff.mp hc2 with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  refine ⟨z.left, ?_⟩
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro v
  change Natural.action F z.left v = t.val.val v
  simpa only [hc1, one_smul] using (htv v).symm

theorem binary_irreducible : IsIrreducible (binary F) := by
  let : Nontrivial (Space F) := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank F (Space F) by rw [finrank_space]; decide)
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hS' : S.toSubmodule ≠ ⊥ := fun h => hS (Subrepresentation.toSubmodule_injective h)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS'
  apply le_antisymm le_top
  intro w _
  by_cases hw : w = 0
  · subst w; exact S.toSubmodule.zero_mem
  · obtain ⟨g, hg⟩ := derivedAction_transitive F v w hv0 hw
    rw [← hg]
    exact S.apply_mem_toSubmodule g.val hv

theorem offender_le_inner {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    {A : Subgroup (linearNormalizer (binary F))}
    (hA : IsOffender (normalizerRepresentation (binary F)) A) :
    A ≤ (normalizerEmbedding (binary F)).range := by
  classical
  let := hA.1.2
  let : Finite (Space F) := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) (Space F)) := Finite.of_injective
    (fun f : Module.End (ZMod 2) (Space F) => (f : Space F → Space F)) DFunLike.coe_injective
  have hq : 2 < Nat.card F := by
    rw [hF]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (show 1 < n by omega)
  let e := MulEquiv.ofBijective (LieAutomorphismExtensions.semilinearAction (F := F))
    ⟨LieAutomorphismExtensions.semilinearAction_injective hq,
      LieAutomorphismExtensions.semilinearAction_surjective hq⟩
  let π := e.symm.toMonoidHom.comp (normalizerAutomorphism F)
  have hπ (t : linearNormalizer (binary F)) :
      LieAutomorphismExtensions.semilinearAction (π t) = normalizerAutomorphism F t :=
    e.apply_symm_apply _
  let f := π.comp A.subtype
  have hf : Function.Injective f := by
    let hf' : Function.Injective (binary F).asGroupHom :=
      fun _ _ h => binary_faithful F (congrArg Units.val h)
    let j : Model F ≃* actionImage (binary F) := MonoidHom.ofInjective hf'
    exact e.symm.injective.comp ((MulAut.congr j.symm).injective.comp
      (normalizer_elementary_conjugation_injective (binary F) (binary_irreducible F) A))
  intro t ht
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  by_cases hs : (π t).right = 1
  · exact inner_involution_mem F hq t ht2 (π t) (hπ t) hs
  have he : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hc := EvenTwoRank.outer_elementary_card_lt F hn hF f.range he
    ⟨π t, ⟨⟨t,ht⟩,rfl⟩⟩ hs
  rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, hA.1.card_eq_two_pow_rank] at hc
  have hr : rank A < 3*n := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hc
  have hd := field_involution_codim F hq hF t ht2 (π t) (hπ t) hs
  have hle : fixedSpace (normalizerRepresentation (binary F)) A ≤
      fixedSpace (normalizerRepresentation (binary F)) (zpowers t) := by
    intro v hv a
    exact hv ⟨a, (zpowers_le.mpr ht) a.property⟩
  have hdim := Submodule.finrank_mono hle
  have h1 := fixedCodim_add_finrank (normalizerRepresentation (binary F)) A
  have h2 := fixedCodim_add_finrank (normalizerRepresentation (binary F)) (zpowers t)
  have ho := hA.2
  omega
theorem ambient_offender_le {G W : Type*} [Group G] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W)
    (H : Subgroup G) [H.Normal] (e : H ≃* Model F)
    (E : W ≃ₗ[ZMod 2] Space F)
    (hE : ∀ (h : H) v, E (ρ h v) = Natural.action F (e h) (E v))
    (hf : Function.Injective ρ) {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    {A : Subgroup G} (hA : IsOffender ρ A) : A ≤ H := by
  let τ : Representation (ZMod 2) G (Space F) := E.conjRingEquiv.toMonoidHom.comp ρ
  have hτ (g : G) (v : W) : E (ρ g v) = τ g (E v) := by
    change E (ρ g v) = E (ρ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hnat (h : H) : τ.asGroupHom h = (binary F).asGroupHom (e h) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change E (ρ h (E.symm v)) = Natural.action F (e h) v
    rw [hE, E.apply_symm_apply]
  have himage : actionImage (τ.comp H.subtype) = actionImage (binary F) := by
    ext a
    constructor
    · rintro ⟨h,rfl⟩
      exact ⟨e h, Units.ext (congrArg Units.val (hnat h).symm)⟩
    · rintro ⟨g,rfl⟩
      refine ⟨e.symm g, Units.ext ?_⟩
      simpa only [e.apply_symm_apply, Representation.asGroupHom_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] using congrArg Units.val (hnat (e.symm g))
  let k : G →* linearNormalizer (binary F) := τ.asGroupHom.codRestrict _ (fun g => by
    change τ.asGroupHom g ∈ normalizer (actionImage (binary F) : Set _)
    rw [← himage]
    exact actionImage_le_linearNormalizer τ H ⟨g,rfl⟩)
  have hk : Function.Injective k := by
    intro a b hab
    apply hf
    apply E.conjRingEquiv.injective
    exact congrArg (fun x : linearNormalizer (binary F) => x.val.val) hab
  have hke (g : G) (v : W) : E (ρ g v) =
      normalizerRepresentation (binary F) (k g) (E v) := hτ g v
  have hmap := offender_le_inner F hn hF
    (hA.map_equivariant ρ (normalizerRepresentation (binary F)) k hk E hke)
  intro a ha
  obtain ⟨g,hg⟩ := hmap (Subgroup.mem_map_of_mem k ha)
  have heq : τ.asGroupHom (e.symm g) = τ.asGroupHom a := by
    rw [hnat, e.apply_symm_apply]
    exact congrArg Subtype.val hg
  have heq' : τ (e.symm g) = τ a := congrArg Units.val heq
  have haa : (e.symm g : G) = a := hf (E.conjRingEquiv.injective heq')
  exact haa ▸ (e.symm g).property
end Atlas.G2.Natural.Normalizer
