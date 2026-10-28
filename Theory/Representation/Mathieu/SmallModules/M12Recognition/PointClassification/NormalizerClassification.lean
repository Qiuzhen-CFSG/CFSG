module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizerReduction
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The unique faithful degree-ten binary module of the M₁₁ eleven-normalizer

The literal normalizer acts transitively on the eleven points, with a point
stabilizer of order five. On any binary space of dimension ten, that stabilizer
has a nonzero fixed vector: its fixed-point count is congruent to 1024 modulo
five. Averaging the corresponding point-evaluation map over the normalizer
sends the point mass to this vector, since the stabilizer has odd order.

The constant line maps to zero, because the order-eleven subgroup has no fixed
vectors. Thus averaging is nonzero on the augmentation kernel. Irreducibility
and equal dimensions make this map an equivalence. The existing augmentation
comparison identifies it with the marked restriction of the twelve-point heart.
The final application discharges the normalizer input of the M₁₁ assembly;
extension rigidity remains a separate input there.

Source application: the James completeness input in Aschbacher--Smith,
*The Classification of Quasithin Groups*, combined manuscript (1 March 2004),
G.7.3(2), printed p.348 (PDF p.359), citing G. D. James, J. Algebra 27 (1973),
57--111. The proof here uses only the actual normalizer, orbit counting, and
the proved order-eleven degree bound.
-/

public section

open Sporadic.Mathieu BinaryPermutation
namespace Representation.MathieuSmall.M12Recognition.PointClassification

private noncomputable def elevenActor : m11Sylow11Normalizer :=
  ⟨m11Sylow11Generator, Subgroup.le_normalizer m11Sylow11Generator_mem_subgroup⟩

private theorem elevenActor_order : orderOf elevenActor = 11 := by
  rw [← Subgroup.orderOf_coe elevenActor]
  exact m11Sylow11Generator_order

private theorem point_orbit : ∀ i : Fin 11, ∃ g : m11Sylow11Normalizer, g • (0 : Fin 11) = i := by
  have h : ∀ i : Fin 11, ∃ k : Fin 11,
      ((m11Sylow11Generator : Equiv.Perm (Fin 11)) ^ (k : ℕ)) 0 = i := by
    decide +kernel
  intro i
  obtain ⟨k, hk⟩ := h i
  exact ⟨elevenActor ^ (k : ℕ), hk⟩

private instance normalizer_transitive : MulAction.IsPretransitive m11Sylow11Normalizer (Fin 11) where
  exists_smul_eq i j := by
    obtain ⟨g, hg⟩ := point_orbit i
    obtain ⟨h, hh⟩ := point_orbit j
    refine ⟨h * g⁻¹, ?_⟩
    rw [mul_smul, ← hg, inv_smul_smul, hh]

private noncomputable abbrev pointFixer := MulAction.stabilizer m11Sylow11Normalizer (0 : Fin 11)

private theorem pointFixer_card : Nat.card pointFixer = 5 := by
  have h := pointFixer.card_mul_index
  rw [MulAction.index_stabilizer_of_transitive, m11Sylow11_normalizer_card] at h
  norm_num at h ⊢
  omega

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem exists_fixed_vector (τ : Representation (ZMod 2) m11Sylow11Normalizer V)
    (hd : Module.finrank (ZMod 2) V = 10) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : pointFixer, τ g.val v = v := by
  let : MulAction pointFixer V := {
    smul g v := τ g.val v
    one_smul v := by change τ 1 v = v; rw [map_one]; rfl
    mul_smul g h v := by change τ (g.val * h.val) v = τ g.val (τ h.val v); rw [map_mul]; rfl }
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hcard : Nat.card V = 1024 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hd]
    norm_num
  have hp : IsPGroup 5 pointFixer := IsPGroup.of_card (n := 1) (by simpa using pointFixer_card)
  by_contra hn
  have hz : ∀ v : MulAction.fixedPoints pointFixer V, v.val = 0 := by
    intro v
    by_contra h
    exact hn ⟨v.val, h, v.property⟩
  let : Unique (MulAction.fixedPoints pointFixer V) :=
    ⟨⟨0, fun g => map_zero (τ g.val)⟩, fun v => Subtype.ext (hz v)⟩
  have h := hp.card_modEq_card_fixedPoints V
  rw [hcard, Nat.card_unique] at h
  norm_num [Nat.ModEq] at h

private noncomputable def orbitMap (τ : Representation (ZMod 2) m11Sylow11Normalizer V)
    (v : V) : Full (Fin 11) →ₗ[ZMod 2] V := by
  let := Fintype.ofFinite m11Sylow11Normalizer
  exact
    { toFun := fun w => ∑ g : m11Sylow11Normalizer, w (g • (0 : Fin 11)) • τ g v
      map_add' := fun w u => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c w => by simp only [Pi.smul_apply, smul_smul, Finset.smul_sum]; rfl }

omit [FiniteDimensional (ZMod 2) V] in
private theorem orbitMap_equivariant (τ : Representation (ZMod 2) m11Sylow11Normalizer V)
    (v : V) (h : m11Sylow11Normalizer) (w : Full (Fin 11)) :
    orbitMap τ v (representation (Fin 11) h.val.val w) = τ h (orbitMap τ v w) := by
  classical
  let := Fintype.ofFinite m11Sylow11Normalizer
  change (∑ g : m11Sylow11Normalizer, w (h⁻¹ • (g • (0 : Fin 11))) • τ g v) =
    τ h (∑ g : m11Sylow11Normalizer, w (g • (0 : Fin 11)) • τ g v)
  rw [← Equiv.sum_comp (Equiv.mulLeft h)]
  change (∑ g : m11Sylow11Normalizer, w (h⁻¹ • ((h * g) • (0 : Fin 11))) • τ (h * g) v) = _
  simp only [mul_smul, inv_smul_smul, map_mul, Module.End.mul_apply, map_sum, map_smul]

omit [FiniteDimensional (ZMod 2) V] in
private theorem orbitMap_single (τ : Representation (ZMod 2) m11Sylow11Normalizer V)
    (v : V) (hv : ∀ g : pointFixer, τ g.val v = v) :
    orbitMap τ v (Pi.single 0 1) = v := by
  classical
  let := Fintype.ofFinite m11Sylow11Normalizer
  let := Fintype.ofFinite pointFixer
  change (∑ g : m11Sylow11Normalizer, (Pi.single (0 : Fin 11) 1 : Full (Fin 11))
    (g • (0 : Fin 11)) • τ g v) = v
  have he (g : m11Sylow11Normalizer) :
      (Pi.single (0 : Fin 11) 1 : Full (Fin 11)) (g • (0 : Fin 11)) • τ g v =
        if g ∈ pointFixer then v else 0 := by
    by_cases hg : g ∈ pointFixer
    · have hg0 : g • (0 : Fin 11) = 0 := hg
      simp only [hg0, Pi.single_eq_same, one_smul, if_pos hg]
      exact hv ⟨g, hg⟩
    · have hg0 : g • (0 : Fin 11) ≠ 0 := hg
      simp [hg0, hg]
  simp_rw [he]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun g => g ∈ pointFixer) _ (by simp) (fun _ => v)]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, pointFixer_card]
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
  change (5 : ZMod 2) • v = v
  rw [show (5 : ZMod 2) = 1 by decide, one_smul]

private theorem orbitMap_allOne (τ : Representation (ZMod 2) m11Sylow11Normalizer V)
    (hf : Function.Injective τ) (hd : Module.finrank (ZMod 2) V = 10) (v : V) :
    orbitMap τ v (allOne (Fin 11)) = 0 := by
  have hm : orbitMap τ v (allOne (Fin 11)) ∈
      BinaryOffender.fixedSpace τ (Subgroup.zpowers elevenActor) := by
    intro g
    have h := orbitMap_equivariant τ v g.val (allOne (Fin 11))
    rw [permute_allOne] at h
    exact h.symm
  rw [eleven_fixedSpace_eq_bot τ hf hd.le elevenActor elevenActor_order] at hm
  exact hm

private noncomputable def coreOrbitMap (τ : Representation (ZMod 2) m11Sylow11Normalizer V)
    (v : V) : IntertwiningMap (augmentationRepresentation.comp m11Sylow11Normalizer.subtype) τ where
  toLinearMap := (orbitMap τ v).comp (core (Fin 11)).subtype
  isIntertwining' g := by
    ext w
    exact orbitMap_equivariant τ v g w.val

private theorem coreOrbitMap_ne_zero (τ : Representation (ZMod 2) m11Sylow11Normalizer V)
    (hf : Function.Injective τ) (hd : Module.finrank (ZMod 2) V = 10)
    (v : V) (hv0 : v ≠ 0) (hv : ∀ g : pointFixer, τ g.val v = v) :
    coreOrbitMap τ v ≠ 0 := by
  classical
  let w : core (Fin 11) := ⟨Pi.single 0 1 - allOne (Fin 11), by
    change augmentation (Fin 11) _ = 0
    rw [map_sub, augmentation_allOne]
    norm_num [augmentation]
    decide⟩
  intro hz
  have he := DFunLike.congr_fun hz w
  change orbitMap τ v (Pi.single 0 1 - allOne (Fin 11)) = 0 at he
  rw [map_sub, orbitMap_single τ v hv, orbitMap_allOne τ hf hd, sub_zero] at he
  exact hv0 he

/-- Every faithful degree-ten binary module for the literal Sylow-eleven normalizer
is the restriction of the marked twelve-point heart. -/
theorem equiv_normalizer_of_faithful_degree_ten
    (τ : Representation (ZMod 2) m11Sylow11Normalizer V)
    (hf : Function.Injective τ) (hd : Module.finrank (ZMod 2) V = 10) :
    Nonempty (τ.Equiv normalizerRepresentation) := by
  obtain ⟨v, hv0, hv⟩ := exists_fixed_vector τ hd
  let : τ.IsIrreducible := irreducible_of_eleven_dvd τ hf hd.le
    (by rw [m11Sylow11_normalizer_card]; norm_num)
  let f := coreOrbitMap τ v
  have hs : Function.Surjective f :=
    (IsIrreducible.surjective_or_eq_zero f).resolve_right (coreOrbitMap_ne_zero τ hf hd v hv0 hv)
  have hi : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_augmentation.trans hd.symm)).mpr hs
  let e : Representation.Equiv (augmentationRepresentation.comp m11Sylow11Normalizer.subtype)
      normalizerRepresentation := .mk augmentationEquivPoint.toLinearEquiv
        (fun g => augmentationEquivPoint.isIntertwining' g.val)
  exact ⟨(f.ofBijective ⟨hi, hs⟩).symm.trans e⟩

/-- Apply normalizer classification to the literal M₁₁ restriction. Only the
independent extension-rigidity input remains in the parent assembly. -/
theorem equiv_point_of_normalizer_extension (σ : Representation (ZMod 2) M11 V)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 10)
    (hextension : ∀ τ : Representation (ZMod 2) M11 M12Heart,
      Function.Injective τ → τ.IsIrreducible →
      (∀ g : m11Sylow11Normalizer, τ g.val = pointRepresentation g.val) →
      ∃ e : normalizerRepresentation.Equiv normalizerRepresentation,
        e.toLinearMap.comp (τ m11GeneratorAInM11) =
          (pointRepresentation m11GeneratorAInM11).comp e.toLinearMap) :
    Nonempty (σ.Equiv pointRepresentation) :=
  equiv_point_of_normalizer_inputs σ hf hd
    (fun τ => equiv_normalizer_of_faithful_degree_ten τ) hextension

end Representation.MathieuSmall.M12Recognition.PointClassification
