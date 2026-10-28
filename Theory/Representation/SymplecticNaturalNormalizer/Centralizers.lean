module

public import Theory.Representation.SymplecticConjugatePair.Ambient.Normalizer
public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.AutomorphismCentralizers
public import Theory.Representation.FirstCohomologySymplecticFour.LargeField

/-!
# Outer involution centralizers in the natural symplectic normalizer

For a finite field of characteristic two with more than two elements, the
literal derived natural image is isomorphic to the full matrix group Sp₄(F).
Transporting normalizer conjugation along this isomorphism gives an actual
homomorphism to Aut(Sp₄(F)). Its kernel consists of coefficient scalars, and
has no nonidentity element of square one. Each elementary abelian two-subgroup
of a literal normalizer centralizer therefore embeds in the corresponding
automorphism centralizer.

The semilinear normal form makes the conjugation diagram-preserving. If an
involution induced an inner automorphism, centerlessness would give a genuine
matrix involution with the same action; their scalar difference has square
one and is trivial. Thus an involution outside the derived natural image
induces a noninner involution. The field-automorphism centralizer calculation
then forces even field degree n and bounds its two-rank by 3(n/2)+1 ≤ 2n.
Only the displayed even-degree field cocycle descent remains conditional.

The universal final bound is the exact input to the Chapter B cover-offender
consumer `symplectic_cover_bestOffender_le_of_centralizer_bound`. That consumer's
assembly owner discharges field descent separately. No graph descent is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.1 printed p.100; H.7 pp.388–389; field-involution conventions in 16.1.4,
pp.1170–1173 of `refs/quasithin.pdf`.
-/

@[expose] public section

open Matrix
open Representation BinaryOffender Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer
namespace SymplecticNaturalNormalizer

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The full symplectic group acting on the literal binary natural module. -/
noncomputable def naturalHom : Sp F →* (Vector F ≃ₗ[ZMod 2] Vector F) :=
  linearAction (restrictScalars (symplecticNatural 2))

omit [Finite F] [CharP F 2] in

/-- The natural operator evaluates by the given matrix representation. -/
lemma naturalHom_apply (g : Sp F) (v : Vector F) :
    naturalHom g v = symplecticNatural 2 g v := rfl

omit [Finite F] [CharP F 2] in

/-- The natural matrix action is faithful, also after restricting scalars. -/
lemma naturalHom_injective : Function.Injective (naturalHom (F := F)) := by
  intro g h he
  apply Subtype.ext
  ext i j
  have hv := congrArg (fun f : Vector F ≃ₗ[ZMod 2] Vector F =>
    f (Pi.single j 1) i) he
  change (g.val *ᵥ Pi.single j 1) i = (h.val *ᵥ Pi.single j 1) i at hv
  simpa [Matrix.mulVec_single] using hv

/-- Perfectness places each full natural operator in the literal derived image. -/
lemma naturalHom_mem (hcard : 2 < Nat.card F) (g : Sp F) :
    naturalHom g ∈ naturalDerivedImage := by
  have hg : g ∈ commutator (Sp F) := by
    rw [Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hcard]
    trivial
  exact ⟨⟨g, hg⟩, rfl⟩

/-- The actual natural representation identifies Sp₄(F) with its derived image. -/
noncomputable def naturalEquiv (hcard : 2 < Nat.card F) : Sp F ≃* naturalDerivedImage (F := F) :=
  MulEquiv.ofBijective ((naturalHom (F := F)).codRestrict naturalDerivedImage (naturalHom_mem hcard))
    ⟨fun _ _ h => naturalHom_injective (congrArg Subtype.val h), by
      rintro ⟨e, x, rfl⟩
      exact ⟨x.val, rfl⟩⟩

/-- The model isomorphism has the original natural operator as its value. -/
lemma naturalEquiv_val (hcard : 2 < Nat.card F) (g : Sp F) :
    (naturalEquiv hcard g).val = naturalHom g := rfl

/-- Conjugation by the single natural normalizer, transported to the matrix group. -/
noncomputable def conjugation (hcard : 2 < Nat.card F) :
    naturalNormalizer (F := F) →* MulAut (Sp F) :=
  (MulAut.congr (naturalEquiv hcard).symm).toMonoidHom.comp
    naturalDerivedImage.normalizerMonoidHom

/-- Transported conjugation agrees with multiplication of actual natural operators. -/
lemma conjugation_apply (hcard : 2 < Nat.card F)
    (s : naturalNormalizer (F := F)) (g : Sp F) :
    naturalHom (conjugation hcard s g) = s.val * naturalHom g * s.val⁻¹ := by
  change (naturalEquiv hcard ((naturalEquiv hcard).symm _)).val = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- The conjugation map intertwines evaluation on the natural module. -/
lemma conjugation_intertwines (hcard : 2 < Nat.card F)
    (s : naturalNormalizer (F := F)) (g : Sp F) (v : Vector F) :
    s.val (naturalHom g v) = naturalHom (conjugation hcard s g) (s.val v) := by
  rw [conjugation_apply]
  change s.val (naturalHom g v) = s.val (naturalHom g (s.val.symm (s.val v)))
  rw [LinearEquiv.symm_apply_apply]

/-- Faithfulness uniquely determines the automorphism induced by an intertwiner. -/
lemma conjugation_eq_of_intertwines (hcard : 2 < Nat.card F)
    (s : naturalNormalizer (F := F)) (a : MulAut (Sp F))
    (ha : ∀ g v, s.val (naturalHom g v) = naturalHom (a g) (s.val v)) :
    conjugation hcard s = a := by
  ext g : 1
  apply naturalHom_injective
  apply LinearEquiv.ext
  intro v
  obtain ⟨v, rfl⟩ := s.val.surjective v
  exact (conjugation_intertwines hcard s g v).symm.trans (ha g v)

/-- Each induced automorphism is inner times an entrywise field automorphism. -/
lemma conjugation_semilinear (hcard : 2 < Nat.card F)
    (s : naturalNormalizer (F := F)) :
    ∃ (g : Sp F) (σ : F ≃+* F), conjugation hcard s = MulAut.conj g * fieldAutomorphism σ := by
  obtain ⟨a, g, σ, he⟩ := naturalNormalizer_semilinear s.val s.property
  refine ⟨g, σ, conjugation_eq_of_intertwines hcard s _ ?_⟩
  intro x v
  rw [he, he]
  change a.val • innerFieldVector g σ (symplecticNatural 2 x v) =
    symplecticNatural 2 ((MulAut.conj g * fieldAutomorphism σ) x)
      (a.val • innerFieldVector g σ v)
  rw [innerFieldVector_intertwines, map_smul]

/-- Natural normalizers preserve both actual parabolic conjugacy classes. -/
lemma conjugation_preservesDiagram (hcard : 2 < Nat.card F)
    (s : naturalNormalizer (F := F)) : PreservesDiagram (conjugation hcard s) := by
  obtain ⟨g, σ, he⟩ := conjugation_semilinear hcard s
  rw [he]
  constructor <;> refine ⟨g, ?_⟩
  · change pointParabolic.map ((MulAut.conj g).toMonoidHom.comp
      (fieldAutomorphism σ).toMonoidHom) = _
    rw [← Subgroup.map_map, field_map_pointParabolic]
  · change planeParabolic.map ((MulAut.conj g).toMonoidHom.comp
      (fieldAutomorphism σ).toMonoidHom) = _
    rw [← Subgroup.map_map, field_map_planeParabolic]

/-- The kernel retains precisely the coefficient scalars. -/
lemma conjugation_eq_one_iff_scalar (hcard : 2 < Nat.card F)
    (s : naturalNormalizer (F := F)) :
    conjugation hcard s = 1 ↔ ∃ c : F, ∀ v, s.val v = c • v := by
  constructor
  · intro hs
    apply natural_commutant_of_pair centralizer_block_scalars s.val.toLinearMap
    intro x v
    have he := conjugation_intertwines hcard s x.val v
    rw [hs] at he
    exact he
  · rintro ⟨c, hc⟩
    apply conjugation_eq_of_intertwines
    intro g v
    change s.val (symplecticNatural 2 g v) = symplecticNatural 2 g (s.val v)
    rw [hc, hc, map_smul]

/-- A coefficient scalar of square one is trivial in characteristic two. -/
lemma eq_one_of_conjugation_eq_one_of_sq (hcard : 2 < Nat.card F)
    (s : naturalNormalizer (F := F)) (hk : conjugation hcard s = 1)
    (hs : s ^ 2 = 1) : s = 1 := by
  obtain ⟨c, hc⟩ := (conjugation_eq_one_iff_scalar hcard s).mp hk
  have hc2 : c ^ 2 = 1 := by
    have hv := congrArg (fun t : naturalNormalizer (F := F) =>
      t.val (Pi.single (.inl 0) 1) (.inl 0)) hs
    change s.val (s.val (Pi.single (.inl 0) 1)) (.inl 0) = 1 at hv
    simpa [hc, smul_smul, pow_two] using hv
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa using hc2)
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  simpa [hc1] using hc v

/-- Embed each full symplectic operator into the literal natural normalizer. -/
noncomputable def naturalElement (hcard : 2 < Nat.card F) :
    Sp F →* naturalNormalizer (F := F) :=
  naturalHom.codRestrict naturalNormalizer
    (fun g => naturalDerivedImage.le_normalizer (naturalHom_mem hcard g))

/-- The normalizer embedding retains the literal natural operator. -/
lemma naturalElement_val (hcard : 2 < Nat.card F) (g : Sp F) :
    (naturalElement hcard g).val = naturalHom g := rfl

/-- A symplectic operator induces its own inner automorphism. -/
lemma conjugation_naturalElement (hcard : 2 < Nat.card F) (g : Sp F) :
    conjugation hcard (naturalElement hcard g) = MulAut.conj g := by
  apply conjugation_eq_of_intertwines
  intro x v
  change (naturalHom g * naturalHom x) v = (naturalHom (g * x * g⁻¹) * naturalHom g) v
  rw [← map_mul, ← map_mul, inv_mul_cancel_right]

/-- An element of square one outside the derived image induces a noninner automorphism. -/
lemma conjugation_not_inner (hcard : 2 < Nat.card F)
    (s : naturalNormalizer (F := F)) (hs : s ^ 2 = 1)
    (hout : s.val ∉ naturalDerivedImage) :
    conjugation hcard s ∉ MulAut.innerSubgroup (Sp F) := by
  rintro ⟨g, hg⟩
  have hg2 : g ^ 2 = 1 := by
    apply inner_injective
    rw [map_pow, hg, ← map_pow, hs, map_one, map_one]
  let t := s * (naturalElement hcard g)⁻¹
  have ht : conjugation hcard t = 1 := by
    dsimp only [t]
    rw [map_mul, map_inv, conjugation_naturalElement, hg, mul_inv_cancel]
  have hcomm : Commute t (naturalElement hcard g) := by
    apply Subtype.ext
    have he := conjugation_apply hcard t g
    rw [ht] at he
    exact mul_inv_eq_iff_eq_mul.mp he.symm
  have ht2 : t ^ 2 = 1 := by
    have he : t * naturalElement hcard g = s := by simp [t]
    have hsq := hcomm.mul_pow 2
    rw [he, hs, ← map_pow, hg2, map_one, mul_one] at hsq
    exact hsq.symm
  have ht1 := eq_one_of_conjugation_eq_one_of_sq hcard t ht ht2
  have he : s = naturalElement hcard g := mul_inv_eq_one.mp ht1
  exact hout (he ▸ naturalHom_mem hcard g)

/-- The scalar kernel does not kill any involution. -/
lemma conjugation_order_two (hcard : 2 < Nat.card F)
    (s : naturalNormalizer (F := F)) (hs : orderOf s = 2) :
    orderOf (conjugation hcard s) = 2 := by
  obtain ⟨hs2, hs1⟩ := orderOf_eq_prime_iff.mp hs
  apply orderOf_eq_prime_iff.mpr
  refine ⟨by rw [← map_pow, hs2, map_one], ?_⟩
  intro he
  exact hs1 (eq_one_of_conjugation_eq_one_of_sq hcard s he hs2)

/-- Restrict conjugation to the centralizers of the specified element and its image. -/
noncomputable def centralizerMap (hcard : 2 < Nat.card F)
    (s : naturalNormalizer (F := F)) :
    centralizer ({s} : Set (naturalNormalizer (F := F))) →*
      centralizer ({conjugation hcard s} : Set (MulAut (Sp F))) :=
  ((conjugation hcard).comp (centralizer ({s} : Set _)).subtype).codRestrict _ (by
    intro x
    apply mem_centralizer_singleton_iff.mpr
    change conjugation hcard x.val * conjugation hcard s =
      conjugation hcard s * conjugation hcard x.val
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp x.property])

/-- Every elementary two-subgroup of the literal centralizer embeds under conjugation. -/
lemma centralizerMap_elementary_injective (hcard : 2 < Nat.card F)
    (s : naturalNormalizer (F := F))
    (E : Subgroup (centralizer ({s} : Set (naturalNormalizer (F := F)))))
    [IsElementaryAbelian 2 E] :
    Function.Injective ((centralizerMap hcard s).comp E.subtype) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  apply Subtype.ext
  apply Subtype.ext
  apply eq_one_of_conjugation_eq_one_of_sq hcard
  · exact congrArg Subtype.val hx
  · have he := elemPow_eq_one_of_isElementaryAbelian (p := 2) x.val x.property
    exact congrArg Subtype.val he

/-- The scalar kernel contributes no elementary two-rank to a centralizer. -/
lemma centralizer_rank_le_automorphism (hcard : 2 < Nat.card F)
    (s : naturalNormalizer (F := F)) :
    primeRank 2 (centralizer ({s} : Set (naturalNormalizer (F := F)))) ≤
      primeRank 2 (centralizer ({conjugation hcard s} : Set (MulAut (Sp F)))) := by
  let : Finite (naturalNormalizer (F := F)) := Finite.of_injective
    (fun s : naturalNormalizer (F := F) => (s.val : Vector F → Vector F))
    (fun _ _ h => Subtype.ext (DFunLike.coe_injective h))
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let := hE
  let f := centralizerMap hcard s
  let fE := f.comp E.subtype
  have hi : Function.Injective fE := centralizerMap_elementary_injective hcard s E
  rw [Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
  have hr : fE.range = E.map f := by simp [fE, MonoidHom.range_comp]
  rw [hr]
  exact (primeRank_le_iff_elementary_card_le _).mp le_rfl (E.map f)
    (IsElementaryAbelian.map f)

/-- An outer involution forces even degree and the sharp bound, conditional only on field descent. -/
theorem outer_centralizer_rank_sharp_of_descent {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hfield : Even n → ∀ g : Sp F,
      g * fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) g = 1 →
      ∃ h : Sp F, g = h * (fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) h)⁻¹)
    (s : naturalNormalizer (F := F)) (hs : orderOf s = 2)
    (hout : s.val ∉ naturalDerivedImage) :
    Even n ∧ primeRank 2 (centralizer ({s} : Set (naturalNormalizer (F := F)))) ≤
      3 * (n / 2) + 1 := by
  have hcard : 2 < Nat.card F := by
    rw [hF]
    exact (show (2 : ℕ) ^ 1 < 2 ^ n from Nat.pow_lt_pow_right (by decide) hn)
  obtain ⟨heven, hb⟩ :=
    SymplecticConjugatePair.Ambient.AutomorphismCentralizers.preserving_outer_centralizer_rank_le_of_descent
      hF (by omega) hfield (conjugation hcard s)
      (conjugation_order_two hcard s hs) (conjugation_preservesDiagram hcard s)
      (conjugation_not_inner hcard s (orderOf_eq_prime_iff.mp hs).1 hout)
  exact ⟨heven, (centralizer_rank_le_automorphism hcard s).trans hb⟩

/-- The universal native bound consumed by the symplectic cover-offender theorem.
Field descent is the sole additional premise; its unconditional proof belongs
to the field-cocycle producer and is discharged by the Chapter B assembly. -/
theorem outer_centralizer_rank_le_of_descent {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hfield : Even n → ∀ g : Sp F,
      g * fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) g = 1 →
      ∃ h : Sp F, g = h * (fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) h)⁻¹) :
    ∀ s : naturalNormalizer (F := F), orderOf s = 2 → s.val ∉ naturalDerivedImage →
      primeRank 2 (centralizer ({s} : Set (naturalNormalizer (F := F)))) ≤ 2 * n := by
  intro s hs hout
  obtain ⟨_, hb⟩ := outer_centralizer_rank_sharp_of_descent hF hn hfield s hs hout
  omega

end SymplecticNaturalNormalizer
