module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.TensorEstimates
public import Theory.Representation.BinaryOffender.SchurNormalizerDisplacement
public import Theory.Representation.SL2NaturalOffenders.FieldAction.Basic

/-!
# Excluding actors which move the actual Schur field

A nontrivial action on the commuting endomorphism field displaces at least
half the binary module. For a noncyclic elementary actor the common fixed
codimension is strictly larger than half: finite-field automorphisms are
cyclic, so the actor contains a nonidentity Schur-linear element. If W is
the common fixed space and f is a moved Schur scalar, W + f(W) is a direct
sum contained in the fixed space of that nonidentity linear element.
Consequently 2 dim W < dim V.

The repeated-word degree gap and the supplied actor-rank bound now exclude
all non-small words, including the degree-8r adjoint boundary. This argument
uses the actual binary normalizer, and does not require a faithful SL₃ cover,
cubicity, absolute irreducibility over F₂, or scalar linearity of outer actors.

Source: Guralnick–Malle, Classification of 2F-modules II, §3.5 and Proposition
4.8, manuscript pp.26–28, cited by Aschbacher–Smith K.3.2, printed p.454.
-/

public section

open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open scoped MonoidAlgebra MatrixGroups

noncomputable section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer

section General
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private def conjugateEnd (t : linearNormalizer ρ) (f : IntertwiningMap ρ ρ) :
    IntertwiningMap ρ ρ where
  toLinearMap := t.val.val * f.toLinearMap * (↑t.val⁻¹ : Module.End (ZMod 2) V)
  isIntertwining' := by
    intro g
    obtain ⟨h, hh⟩ := (Subgroup.mem_normalizer_iff''.mp t.property
      (ρ.asGroupHom g)).mp ⟨g, rfl⟩
    have he : ρ h = (↑t.val⁻¹ : Module.End (ZMod 2) V) * ρ g * t.val.val :=
      congrArg Units.val hh
    have hf : f.toLinearMap * ρ h = ρ h * f.toLinearMap := f.isIntertwining' h
    have hc := congrArg (fun a : Module.End (ZMod 2) V =>
      t.val.val * a * (↑t.val⁻¹ : Module.End (ZMod 2) V)) hf
    change (_ * _ * _) * ρ g = ρ g * (_ * _ * _)
    simpa [he, mul_assoc] using hc

private def conjugateEquiv (t : linearNormalizer ρ) :
    IntertwiningMap ρ ρ ≃+* IntertwiningMap ρ ρ where
  toFun := conjugateEnd ρ t
  invFun := conjugateEnd ρ t⁻¹
  left_inv f := by
    ext v
    change ((↑t.val⁻¹ : Module.End (ZMod 2) V) *
      (t.val.val * f.toLinearMap * (↑t.val⁻¹ : Module.End (ZMod 2) V)) * t.val.val) v = f v
    simp [mul_assoc]
  right_inv f := by
    ext v
    change (t.val.val * ((↑t.val⁻¹ : Module.End (ZMod 2) V) * f.toLinearMap * t.val.val) *
      (↑t.val⁻¹ : Module.End (ZMod 2) V)) v = f v
    simp [mul_assoc]
  map_add' f g := by
    ext v
    change (t.val.val * (f.toLinearMap + g.toLinearMap) *
      (↑t.val⁻¹ : Module.End (ZMod 2) V)) v = _
    simp [mul_add, add_mul, conjugateEnd]
  map_mul' f g := by
    ext v
    change (t.val.val * (f.toLinearMap * g.toLinearMap) *
      (↑t.val⁻¹ : Module.End (ZMod 2) V)) v =
      ((t.val.val * f.toLinearMap * (↑t.val⁻¹ : Module.End (ZMod 2) V)) *
      (t.val.val * g.toLinearMap * (↑t.val⁻¹ : Module.End (ZMod 2) V))) v
    simp [mul_assoc]

private def coefficientAction : linearNormalizer ρ →*
    (Module.End (ZMod 2)[G] ρ.asModule ≃+* Module.End (ZMod 2)[G] ρ.asModule) where
  toFun t := (IntertwiningMap.equivAlgEnd ρ).symm.toRingEquiv.trans
    ((conjugateEquiv ρ t).trans (IntertwiningMap.equivAlgEnd ρ).toRingEquiv)
  map_one' := by
    apply RingEquiv.ext
    intro c
    apply (IntertwiningMap.equivAlgEnd ρ).symm.injective
    change conjugateEnd ρ 1 ((IntertwiningMap.equivAlgEnd ρ).symm c) = _
    ext v
    simp [conjugateEnd]
  map_mul' a b := by
    apply RingEquiv.ext
    intro c
    apply (IntertwiningMap.equivAlgEnd ρ).symm.injective
    change conjugateEnd ρ (a * b) ((IntertwiningMap.equivAlgEnd ρ).symm c) =
      conjugateEnd ρ a (conjugateEnd ρ b ((IntertwiningMap.equivAlgEnd ρ).symm c))
    ext v
    simp [conjugateEnd, mul_assoc]

private theorem coefficientAction_eq_one (t : linearNormalizer ρ) :
    coefficientAction ρ t = 1 ↔ IsSchurLinear ρ t := by
  constructor
  · intro h f v
    have he := DFunLike.congr_fun h (IntertwiningMap.equivAlgEnd ρ f)
    have he' := congrArg ((IntertwiningMap.equivAlgEnd ρ).symm) he
    have hv := congrArg (fun a : IntertwiningMap ρ ρ => a (t.val.val v)) he'
    change (t.val.val * f.toLinearMap * (↑t.val⁻¹ : Module.End (ZMod 2) V) * t.val.val) v = _ at hv
    simpa [mul_assoc] using hv
  · intro h
    apply RingEquiv.ext
    intro c
    apply (IntertwiningMap.equivAlgEnd ρ).symm.injective
    change conjugateEnd ρ t ((IntertwiningMap.equivAlgEnd ρ).symm c) = _
    ext v
    change t.val.val (((IntertwiningMap.equivAlgEnd ρ).symm c)
      ((↑t.val⁻¹ : Module.End (ZMod 2) V) v)) = _
    rw [h]
    simp [← Module.End.mul_apply]

variable [FiniteDimensional (ZMod 2) V] [IsIrreducible ρ]

private theorem exists_nontrivial_schurLinear (A : Subgroup (linearNormalizer ρ))
    (hA : IsElementaryTwo A) (hr : 1 < rank A) :
    ∃ b ∈ A, b ≠ 1 ∧ IsSchurLinear ρ b := by
  let φ := (coefficientAction ρ).comp A.subtype
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (linearNormalizer ρ) := Finite.of_injective
    (fun t : linearNormalizer ρ => (t.val.val : V → V))
    (fun _ _ h => Subtype.ext (Units.ext (LinearMap.ext (congrFun h))))
  let : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hc := SL2NaturalOffenders.fieldAction_range_card_le_two A hA.2 φ
  have hn : φ.ker ≠ ⊥ := by
    intro he
    have hi := (φ.ker_eq_bot_iff).mp he
    have hir : Function.Injective φ.rangeRestrict :=
      fun x y h => hi (congrArg Subtype.val h)
    have hh := (Nat.card_le_card_of_injective _ hir).trans hc
    rw [hA.card_eq_two_pow_rank] at hh
    have hp : 2 ^ 1 < 2 ^ rank A := (Nat.pow_lt_pow_iff_right (by decide)).mpr hr
    norm_num at hp
    omega
  obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hn
  exact ⟨b.val.val, b.val.property,
    fun he => hb (Subtype.ext (Subtype.ext he)),
    (coefficientAction_eq_one ρ b.val.val).mp b.property⟩

private theorem strict_half_codim (A : Subgroup (linearNormalizer ρ))
    (t : linearNormalizer ρ) (ht : t ∈ A) (hs : ¬ IsSchurLinear ρ t)
    (b : linearNormalizer ρ) (hb : b ∈ A) (hb1 : b ≠ 1)
    (hbs : IsSchurLinear ρ b) :
    Module.finrank (ZMod 2) V < 2 * fixedCodim (normalizerRepresentation ρ) A := by
  classical
  obtain ⟨f, hf⟩ : ∃ f, conjugateEnd ρ t f ≠ f := by
    by_contra! hh
    apply hs
    intro f v
    have he := congrArg (fun a : IntertwiningMap ρ ρ => a (t.val.val v)) (hh f)
    change (t.val.val * f.toLinearMap * (↑t.val⁻¹ : Module.End (ZMod 2) V) * t.val.val) v = _ at he
    simpa [mul_assoc] using he
  let W := fixedSpace (normalizerRepresentation ρ) A
  let δ := conjugateEnd ρ t f - f
  have hδ : Function.Injective δ :=
    (IsIrreducible.injective_or_eq_zero δ).resolve_right (sub_ne_zero.mpr hf)
  have hfix (a : linearNormalizer ρ) (ha : a ∈ A) (v : W) : a.val.val v = v :=
    v.property ⟨a, ha⟩
  have hinv (v : W) : (↑t.val⁻¹ : Module.End (ZMod 2) V) v = v := by
    have h := congrArg (↑t.val⁻¹ : Module.End (ZMod 2) V) (hfix t ht v)
    simpa [← Module.End.mul_apply] using h.symm
  have hδv (v : W) : δ v = t.val.val (f v) - f v := by
    change t.val.val (f ((↑t.val⁻¹ : Module.End (ZMod 2) V) v)) - f v = _
    rw [hinv]
  let q : W × W →ₗ[ZMod 2] V :=
    W.subtype.comp (LinearMap.fst _ _ _) +
      f.toLinearMap.comp (W.subtype.comp (LinearMap.snd _ _ _))
  have hq (x : W × W) : q x = x.1.val + f x.2 := rfl
  have hqi : Function.Injective q := by
    intro x y he
    have he₀ : x.1.val + f x.2 = y.1.val + f y.2 := he
    have he₁ := congrArg t.val.val he₀
    simp only [map_add, hfix t ht] at he₁
    have hδeq : δ x.2 = δ y.2 := by
      rw [hδv, hδv]
      calc
        _ = (x.1.val + t.val.val (f x.2)) - (x.1.val + f x.2) := by abel
        _ = (y.1.val + t.val.val (f y.2)) - (y.1.val + f y.2) := by rw [he₀, he₁]
        _ = _ := by abel
    have h2 : x.2 = y.2 := Subtype.ext (hδ hδeq)
    have h1 : x.1 = y.1 := by
      rw [h2] at he₀
      exact Subtype.ext (add_right_cancel he₀)
    exact Prod.ext h1 h2
  have hproper : q.range ≠ ⊤ := by
    intro he
    apply hb1
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨x, rfl⟩ := (LinearMap.range_eq_top.mp he) v
    change b.val.val (q x) = q x
    rw [hq, map_add, hbs, hfix b hb, hfix b hb]
  have hdim := Submodule.finrank_lt hproper
  rw [LinearMap.finrank_range_of_inj hqi, Module.finrank_prod] at hdim
  have hadd := fixedCodim_add_finrank (normalizerRepresentation ρ) A
  change fixedCodim (normalizerRepresentation ρ) A + Module.finrank (ZMod 2) W = _ at hadd
  change Module.finrank (ZMod 2) W + Module.finrank (ZMod 2) W < _ at hdim
  omega

end General

open ChapterB.QuasisimpleSource
open Representation.SL3.BinaryDefiningFactors
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

/-- Every non-small repeated model has binary degree at least eight times
the defining-field exponent. -/
theorem eight_mul_degree_le_finrank (M : RepeatedModel B σ)
    (hp : 0 < naturalCount M.block + adjointCount M.block) (hn : ¬ M.Small) :
    8 * B.degree ≤ Module.finrank (ZMod 2) V := by
  rcases orbit_degree_gap (s := schurDegree σ) M.repetitions_pos hp with h | h | h
  · exact (hn ⟨h.1, h.2.1, Or.inl h.2.2⟩).elim
  · exact (hn ⟨h.1, h.2.1, Or.inr h.2.2⟩).elim
  · simpa only [← M.field_degree, ← M.finrank_eq] using h

/-- A scalar-moving member forces the required strict common-fixed-space
inequality for the whole elementary actor. -/
theorem estimate_of_not_schurLinear (M : RepeatedModel B σ)
    (hp : 0 < naturalCount M.block + adjointCount M.block) (hn : ¬ M.Small)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hr : rank A ≤ 2 * B.degree)
    (t : linearNormalizer σ) (ht : t ∈ A) (hs : ¬ IsSchurLinear σ t) :
    2 * rank A < fixedCodim (normalizerRepresentation σ) A := by
  have hd := eight_mul_degree_le_finrank B σ M hp hn
  by_cases hle : rank A ≤ 1
  · have hh := finrank_le_twice_fixedCodim σ t hs
    have hm := NaturalTensor.fixedCodim_mono (normalizerRepresentation σ)
      (Subgroup.zpowers_le.mpr ht)
    have hpos := B.degree_pos
    omega
  · obtain ⟨b, hb, hb1, hbs⟩ := exists_nontrivial_schurLinear σ A hA (by omega)
    have hh := strict_half_codim σ A t ht hs b hb hb1 hbs
    omega

/-- Any actor violating the desired strict inequality acts linearly over
the actual Schur field. This includes the adjoint degree boundary. -/
theorem schurLinear_of_small_actor (M : RepeatedModel B σ)
    (hp : 0 < naturalCount M.block + adjointCount M.block) (hn : ¬ M.Small)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hr : rank A ≤ 2 * B.degree)
    (hd : fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A) :
    ∀ t ∈ A, IsSchurLinear σ t := by
  intro t ht
  by_contra hs
  exact (not_lt_of_ge hd) (estimate_of_not_schurLinear B σ M hp hn A hA hr t ht hs)

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer
