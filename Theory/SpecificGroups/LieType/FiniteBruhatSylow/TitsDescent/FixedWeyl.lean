module

public import Theory.SpecificGroups.LieType.FiniteBruhatSylow.FixedPoints
public import Theory.AlgebraicGroup.Automorphisms.Lang.CommutativeSurjectivity
public import Theory.AlgebraicGroup.Morphism.CodRestrict

/-!
# Fixed points in the algebraic torus-normalizer quotient

All maps use the literal algebraic normalizer and its torus intersection.
Their restrictions to the full fixed group, the prime-to-p residual, and
intermediate groups have exactly the corresponding torus kernels. Lang's
surjectivity on the invariant torus corrects an arbitrary representative of
a fixed algebraic Weyl coset to a fixed representative. This constructs the
full fixed-normalizer quotient without a surjectivity certificate.

Fixed unipotent root-ray words descend letter by letter to the residual.
Marked lifts of a generating family then identify all intermediate quotient
maps, give N1 = N H1, and control lift squares and normalizer generation.
The finite fixed torus has order prime to p. Consequently full fixed-point
Bruhat coverage and its action on the positive and opposite groups imply
that these groups generate the residual; no separate assertion that the
finite torus lies in their join is needed.

The actual comparison with the root-system Weyl group and its source
isometry, the generation by distinguished relative reflections, their
explicit root words, and the long-element opposition action are separate
geometric obligations. The conditional consumers here do not certify those
source assertions. Root-ray blocks may be nonabelian, and no reduced or
crystallographic condition on the relative roots is imposed.

Sources: GLS3, 2.3.1--2.3.5, 2.3.8(e), and Section 2.4; Lang correction
uses the connected commutative case of Steinberg's Theorem 10.4.
-/

@[expose] public section

namespace Theory.AlgebraicGroup.FiniteBruhatSylow.TitsDescent.FixedWeyl

open FiniteParabolicRealization

variable {k : Type*} [Field k] {K : Variety k} [AlgebraicGroup K]

abbrev algebraicNormalizer (T : ClosedSubgroup K) :=
  Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K))

abbrev algebraicTorus (T : ClosedSubgroup K) :=
  T.toSubgroup.subgroupOf (algebraicNormalizer T)

instance algebraicTorus_normal (T : ClosedSubgroup K) :
    (algebraicTorus T).Normal := T.toSubgroup.normal_in_normalizer

/-- The literal algebraic torus-normalizer quotient, before any root-system comparison. -/
abbrev algebraicWeyl (T : ClosedSubgroup K) :=
  algebraicNormalizer T ⧸ algebraicTorus T

abbrev fixedNormalizer (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K) :=
  (algebraicNormalizer T).comap (fixedPoints σ).subtype

abbrev fixedTorus (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K) :=
  T.toSubgroup.comap (fixedPoints σ).subtype

abbrev intermediateNormalizer (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K)
    (L : Subgroup (fixedPoints σ)) := (fixedNormalizer σ T).subgroupOf L

abbrev intermediateTorus (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K)
    (L : Subgroup (fixedPoints σ)) := (fixedTorus σ T).subgroupOf L

/-- The normalizer map keeps the original algebraic point. -/
def intermediateNormalizerEmbedding (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K)
    (L : Subgroup (fixedPoints σ)) : intermediateNormalizer σ T L →* algebraicNormalizer T where
  toFun n := ⟨n.val.val.val, n.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def intermediateProjection (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K)
    (L : Subgroup (fixedPoints σ)) : intermediateNormalizer σ T L →* algebraicWeyl T :=
  (QuotientGroup.mk' (algebraicTorus T)).comp (intermediateNormalizerEmbedding σ T L)

def fixedNormalizerEmbedding (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K) :
    fixedNormalizer σ T →* algebraicNormalizer T where
  toFun n := ⟨n.val.val, n.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def fixedProjection (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K) :
    fixedNormalizer σ T →* algebraicWeyl T :=
  (QuotientGroup.mk' (algebraicTorus T)).comp (fixedNormalizerEmbedding σ T)

/-- This is the map on `normalizer σ p T`, not on the normalizer of the finite torus. -/
abbrev residualProjection (σ : AlgebraicEndomorphism K) (p : ℕ) (T : ClosedSubgroup K) :
    normalizer σ p T →* algebraicWeyl T := intermediateProjection σ T (definingGroup σ p)

theorem intermediateProjection_ker (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K)
    (L : Subgroup (fixedPoints σ)) :
    (intermediateProjection σ T L).ker =
      (intermediateTorus σ T L).subgroupOf (intermediateNormalizer σ T L) := by
  ext n
  exact QuotientGroup.eq_one_iff (intermediateNormalizerEmbedding σ T L n)

theorem fixedProjection_ker (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K) :
    (fixedProjection σ T).ker = (fixedTorus σ T).subgroupOf (fixedNormalizer σ T) := by
  ext n
  exact QuotientGroup.eq_one_iff (fixedNormalizerEmbedding σ T n)

theorem residualProjection_ker (σ : AlgebraicEndomorphism K) (p : ℕ)
    (T : ClosedSubgroup K) :
    (residualProjection σ p T).ker = (torus σ p T).subgroupOf (normalizer σ p T) :=
  intermediateProjection_ker σ T (definingGroup σ p)

instance intermediateTorus_normal (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K)
    (L : Subgroup (fixedPoints σ)) :
    ((intermediateTorus σ T L).subgroupOf (intermediateNormalizer σ T L)).Normal := by
  rw [← intermediateProjection_ker]
  infer_instance

instance fixedTorus_normal (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K) :
    ((fixedTorus σ T).subgroupOf (fixedNormalizer σ T)).Normal := by
  rw [← fixedProjection_ker]
  infer_instance

instance residualTorus_normal (σ : AlgebraicEndomorphism K) (p : ℕ)
    (T : ClosedSubgroup K) :
    ((torus σ p T).subgroupOf (normalizer σ p T)).Normal :=
  intermediateTorus_normal σ T (definingGroup σ p)

noncomputable def intermediateQuotientEquivImage (σ : AlgebraicEndomorphism K)
    (T : ClosedSubgroup K) (L : Subgroup (fixedPoints σ)) :
    (intermediateNormalizer σ T L ⧸
      (intermediateTorus σ T L).subgroupOf (intermediateNormalizer σ T L)) ≃*
        (intermediateProjection σ T L).range :=
  (QuotientGroup.quotientMulEquivOfEq (intermediateProjection_ker σ T L).symm).trans
    (QuotientGroup.quotientKerEquivRange (intermediateProjection σ T L))

@[simp] theorem intermediateQuotientEquivImage_mk (σ : AlgebraicEndomorphism K)
    (T : ClosedSubgroup K) (L : Subgroup (fixedPoints σ))
    (n : intermediateNormalizer σ T L) :
    ((intermediateQuotientEquivImage σ T L (QuotientGroup.mk n) :
      (intermediateProjection σ T L).range) : algebraicWeyl T) =
        intermediateProjection σ T L n := rfl

noncomputable def fixedQuotientEquivImage (σ : AlgebraicEndomorphism K)
    (T : ClosedSubgroup K) :
    (fixedNormalizer σ T ⧸ (fixedTorus σ T).subgroupOf (fixedNormalizer σ T)) ≃*
      (fixedProjection σ T).range :=
  (QuotientGroup.quotientMulEquivOfEq (fixedProjection_ker σ T).symm).trans
    (QuotientGroup.quotientKerEquivRange (fixedProjection σ T))

@[simp] theorem fixedQuotientEquivImage_mk (σ : AlgebraicEndomorphism K)
    (T : ClosedSubgroup K) (n : fixedNormalizer σ T) :
    ((fixedQuotientEquivImage σ T (QuotientGroup.mk n) :
      (fixedProjection σ T).range) : algebraicWeyl T) = fixedProjection σ T n := rfl

noncomputable abbrev residualQuotientEquivImage (σ : AlgebraicEndomorphism K)
    (p : ℕ) (T : ClosedSubgroup K) :
    (normalizer σ p T ⧸ (torus σ p T).subgroupOf (normalizer σ p T)) ≃*
      (residualProjection σ p T).range :=
  intermediateQuotientEquivImage σ T (definingGroup σ p)

/-- Equal algebraic Weyl images differ by the literal torus intersection. -/
theorem intermediateProjection_eq_iff (σ : AlgebraicEndomorphism K)
    (T : ClosedSubgroup K) (L : Subgroup (fixedPoints σ))
    (n m : intermediateNormalizer σ T L) :
    intermediateProjection σ T L n = intermediateProjection σ T L m ↔
      n.val * m.val⁻¹ ∈ intermediateTorus σ T L := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul]
  change (n * m⁻¹ ∈ (intermediateProjection σ T L).ker) ↔ _
  rw [intermediateProjection_ker]
  rfl

/-- Restriction along the actual inclusion of intermediate groups. -/
def normalizerInclusion (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K)
    {L M : Subgroup (fixedPoints σ)} (hLM : L ≤ M) :
    intermediateNormalizer σ T L →* intermediateNormalizer σ T M where
  toFun n := ⟨⟨n.val.val, hLM n.val.property⟩, n.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem intermediateProjection_inclusion (σ : AlgebraicEndomorphism K)
    (T : ClosedSubgroup K) {L M : Subgroup (fixedPoints σ)} (hLM : L ≤ M)
    (n : intermediateNormalizer σ T L) :
    intermediateProjection σ T M (normalizerInclusion σ T hLM n) =
      intermediateProjection σ T L n := rfl

theorem intermediateProjection_range_le_fixed (σ : AlgebraicEndomorphism K)
    (T : ClosedSubgroup K) (L : Subgroup (fixedPoints σ)) :
    (intermediateProjection σ T L).range ≤ (fixedProjection σ T).range := by
  rintro w ⟨n, rfl⟩
  exact ⟨⟨n.val.val, n.property⟩, rfl⟩

/-- An intermediate group containing the residual has at least its Weyl image. -/
theorem residualProjection_range_le_intermediate (σ : AlgebraicEndomorphism K)
    (p : ℕ) (T : ClosedSubgroup K) (L : Subgroup (fixedPoints σ))
    (hL : definingGroup σ p ≤ L) :
    (residualProjection σ p T).range ≤ (intermediateProjection σ T L).range := by
  rintro w ⟨n, rfl⟩
  exact ⟨normalizerInclusion σ T hL n, rfl⟩

/-- Once residual lifts are constructed, every intermediate normalizer has the
same algebraic Weyl image. This does not assume that equality as an axiom. -/
theorem intermediateProjection_range_eq_of_residual (σ : AlgebraicEndomorphism K)
    (p : ℕ) (T : ClosedSubgroup K) (L : Subgroup (fixedPoints σ))
    (hL : definingGroup σ p ≤ L)
    (hlift : (fixedProjection σ T).range ≤ (residualProjection σ p T).range) :
    (intermediateProjection σ T L).range = (fixedProjection σ T).range :=
  le_antisymm (intermediateProjection_range_le_fixed σ T L)
    (hlift.trans (residualProjection_range_le_intermediate σ p T L hL))

/-- The literal product `N* = N H*`, with its actual embeddings and torus factor. -/
theorem intermediate_normalizer_factors (σ : AlgebraicEndomorphism K)
    (p : ℕ) (T : ClosedSubgroup K) (L : Subgroup (fixedPoints σ))
    (hL : definingGroup σ p ≤ L)
    (hlift : (fixedProjection σ T).range ≤ (residualProjection σ p T).range)
    (n : intermediateNormalizer σ T L) :
    ∃ m : normalizer σ p T, ∃ t : intermediateTorus σ T L,
      n.val = (normalizerInclusion σ T hL m).val * t.val := by
  have hn : intermediateProjection σ T L n ∈ (residualProjection σ p T).range :=
    hlift (intermediateProjection_range_le_fixed σ T L ⟨n, rfl⟩)
  obtain ⟨m, hm⟩ := hn
  let mL := normalizerInclusion σ T hL m
  have ht : (mL⁻¹ * n).val ∈ intermediateTorus σ T L := by
    have he : intermediateProjection σ T L (mL⁻¹ * n) = 1 := by
      rw [map_mul, map_inv]
      change (residualProjection σ p T m)⁻¹ * intermediateProjection σ T L n = 1
      rw [hm, inv_mul_cancel]
    change mL⁻¹ * n ∈ (intermediateTorus σ T L).subgroupOf (intermediateNormalizer σ T L)
    rw [← intermediateProjection_ker]
    exact he
  exact ⟨m, ⟨(mL⁻¹ * n).val, ht⟩, (mul_inv_cancel_left mL.val n.val).symm⟩

/-- Sigma induces an endomorphism of the actual torus normalizer. Exact torus
invariance suffices; no normalizer-surjectivity premise is used. -/
def normalizerEnd (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K)
    (hT : T.toSubgroup.map σ.onPoints = T.toSubgroup) :
    algebraicNormalizer T →* algebraicNormalizer T where
  toFun n := ⟨σ.onPoints n.val, by
    have h := T.toSubgroup.le_normalizer_map σ.onPoints
    rw [hT] at h
    exact h ⟨n.val, n.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one σ.onPoints)
  map_mul' n m := Subtype.ext (map_mul σ.onPoints n.val m.val)

def weylEnd (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K)
    (hT : T.toSubgroup.map σ.onPoints = T.toSubgroup) :
    algebraicWeyl T →* algebraicWeyl T :=
  QuotientGroup.map (algebraicTorus T) (algebraicTorus T) (normalizerEnd σ T hT) (by
    intro t ht
    change σ.onPoints t.val ∈ T.toSubgroup
    rw [← hT]
    exact ⟨t.val, ht, rfl⟩)

/-- Fixed points in the literal algebraic Weyl quotient. Identifying this with
`C_W(tau)` requires the actual root-system comparison and equivariance. -/
abbrev weylFixed (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K)
    (hT : T.toSubgroup.map σ.onPoints = T.toSubgroup) :=
  (weylEnd σ T hT).eqLocus (MonoidHom.id _)

@[simp] theorem weylEnd_mk (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K)
    (hT : T.toSubgroup.map σ.onPoints = T.toSubgroup) (n : algebraicNormalizer T) :
    weylEnd σ T hT (QuotientGroup.mk n) = QuotientGroup.mk (normalizerEnd σ T hT n) := rfl

theorem fixedProjection_range_le_weylFixed (σ : AlgebraicEndomorphism K)
    (T : ClosedSubgroup K) (hT : T.toSubgroup.map σ.onPoints = T.toSubgroup) :
    (fixedProjection σ T).range ≤ weylFixed σ T hT := by
  rintro w ⟨n, rfl⟩
  change QuotientGroup.mk (normalizerEnd σ T hT (fixedNormalizerEmbedding σ T n)) =
    QuotientGroup.mk (fixedNormalizerEmbedding σ T n)
  congr 1
  exact Subtype.ext n.val.property

def torusEnd (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K)
    (hT : T.toSubgroup.map σ.onPoints = T.toSubgroup) :
    AlgebraicGroup.Morphism T.carrierVariety T.carrierVariety :=
  (σ.comp T.inclusion).codRestrictClosedSubgroup T (by
    intro t
    change σ.onPoints (T.inclusion.onPoints t) ∈ T.toSubgroup
    rw [← hT]
    exact ⟨T.inclusion.onPoints t, (T.pointEquiv t).property, rfl⟩)

@[simp] theorem torusEnd_inclusion (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K)
    (hT : T.toSubgroup.map σ.onPoints = T.toSubgroup)
    (t : Variety.Point T.carrierVariety) :
    T.inclusion.onPoints ((torusEnd σ T hT).onPoints t) =
      σ.onPoints (T.inclusion.onPoints t) :=
  AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _

theorem torusEnd_fixed_finite (σ : AlgebraicEndomorphism K)
    [Fact (IsAlgebraicSteinbergEndomorphism σ)]
    (T : ClosedSubgroup K) (hT : T.toSubgroup.map σ.onPoints = T.toSubgroup) :
    Finite {t : Variety.Point T.carrierVariety | (torusEnd σ T hT).onPoints t = t} := by
  let f : {t : Variety.Point T.carrierVariety | (torusEnd σ T hT).onPoints t = t} →
      fixedPoints σ := fun t => ⟨T.inclusion.onPoints t.val, by
        change σ.onPoints (T.inclusion.onPoints t.val) = T.inclusion.onPoints t.val
        rw [← torusEnd_inclusion σ T hT, t.property]⟩
  exact Finite.of_injective f (by
    intro t u h
    apply Subtype.ext
    apply T.inclusion_injective
    exact congrArg (fun x : fixedPoints σ => x.val) h)

section Lang

variable [IsAlgClosed k] (σ : AlgebraicEndomorphism K)
  [Fact (IsAlgebraicSteinbergEndomorphism σ)]
  (T : ClosedSubgroup K) (hT : IsSubtorus T)
  (hσT : T.toSubgroup.map σ.onPoints = T.toSubgroup)

include hT hσT

/-- Lang correction in the supplied invariant algebraic torus. -/
theorem torus_lang_solution (a : Variety.Point K) (ha : a ∈ T.toSubgroup) :
    ∃ c ∈ T.toSubgroup, c * (σ.onPoints c)⁻¹ = a := by
  obtain ⟨c, hc⟩ := langMorphism_surjective_of_connected_commutative
    (torusEnd σ T hσT) hT.isConnected hT.isMulCommutative
    (torusEnd_fixed_finite σ T hσT) (T.pointEquiv.symm ⟨a, ha⟩)
  refine ⟨T.inclusion.onPoints c, (T.pointEquiv c).property, ?_⟩
  have h := congrArg T.inclusion.onPoints hc
  simp only [langMorphism_apply, map_mul, map_inv] at h
  change T.inclusion.onPoints c *
    (T.inclusion.onPoints ((torusEnd σ T hσT).onPoints c))⁻¹ = a at h
  rwa [torusEnd_inclusion] at h

/-- Correct any representative of a fixed algebraic Weyl coset inside its
torus coset to obtain a fixed representative. This is full fixed-normalizer
surjectivity, proved by Lang rather than assumed. -/
theorem exists_fixedNormalizer_lift (w : weylFixed σ T hσT) :
    ∃ n : fixedNormalizer σ T, fixedProjection σ T n = w.val := by
  obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective (algebraicTorus T) w.val
  have hnfix : QuotientGroup.mk (normalizerEnd σ T hσT n) =
      (QuotientGroup.mk n : algebraicWeyl T) := by
    have h := w.property
    change weylEnd σ T hσT w.val = w.val at h
    rw [← hn] at h
    exact h
  have ha : n.val⁻¹ * σ.onPoints n.val ∈ T.toSubgroup := by
    change n⁻¹ * normalizerEnd σ T hσT n ∈ algebraicTorus T
    apply (QuotientGroup.eq_one_iff _).mp
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hnfix, inv_mul_cancel]
  obtain ⟨c, hc, hlang⟩ := torus_lang_solution σ T hT hσT _ ha
  have hfix : σ.onPoints (n.val * c) = n.val * c := by
    rw [map_mul]
    have he : σ.onPoints n.val = n.val * (c * (σ.onPoints c)⁻¹) := by
      rw [hlang, mul_inv_cancel_left]
    rw [he]
    group
  let m : fixedNormalizer σ T :=
    ⟨⟨n.val * c, hfix⟩, (algebraicNormalizer T).mul_mem n.property
      (T.toSubgroup.le_normalizer hc)⟩
  refine ⟨m, ?_⟩
  change QuotientGroup.mk (n * ⟨c, T.toSubgroup.le_normalizer hc⟩) = w.val
  have hcq : (QuotientGroup.mk (⟨c, T.toSubgroup.le_normalizer hc⟩ :
      algebraicNormalizer T) : algebraicWeyl T) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hc
  rw [QuotientGroup.mk_mul, hcq, mul_one]
  exact hn

theorem fixedProjection_range_eq_weylFixed :
    (fixedProjection σ T).range = weylFixed σ T hσT := by
  apply le_antisymm (fixedProjection_range_le_weylFixed σ T hσT)
  intro w hw
  exact exists_fixedNormalizer_lift σ T hT hσT ⟨w, hw⟩

/-- The full fixed-normalizer quotient is canonically the fixed subgroup of
the algebraic normalizer quotient. -/
noncomputable def fixedQuotientEquiv :
    (fixedNormalizer σ T ⧸ (fixedTorus σ T).subgroupOf (fixedNormalizer σ T)) ≃*
      weylFixed σ T hσT :=
  (fixedQuotientEquivImage σ T).trans
    (MulEquiv.subgroupCongr (fixedProjection_range_eq_weylFixed σ T hT hσT))

@[simp] theorem fixedQuotientEquiv_mk (n : fixedNormalizer σ T) :
    ((fixedQuotientEquiv σ T hT hσT (QuotientGroup.mk n) :
      weylFixed σ T hσT) : algebraicWeyl T) = fixedProjection σ T n := rfl

end Lang

section Words

variable [IsAlgClosed k] (σ : AlgebraicEndomorphism K) (p : ℕ)
  [Fact p.Prime] [CharP k p]

/-- A letter is an actual fixed point in a specified closed root-ray block.
The blocks may be nonabelian; no reduced or crystallographic relative-root
assumption enters this construction. -/
abbrev RayLetter {ι : Type*} (R : ι → ClosedSubgroup K) :=
  (i : ι) × {x : fixedPoints σ // x.val ∈ (R i).toSubgroup}

def rayLetterValue {ι : Type*} (R : ι → ClosedSubgroup K)
    (hR : ∀ i, IsUnipotentAlgebraicGroup (R i).carrierVariety)
    (a : RayLetter σ R) : definingGroup σ p :=
  ⟨a.2.val, fixed_unipotent_le_definingGroup σ p (R a.1) (hR a.1) a.2.property⟩

/-- A fixed root word lies in the source prime-to-p residual, letter by letter. -/
def rayWord {ι : Type*} (R : ι → ClosedSubgroup K)
    (hR : ∀ i, IsUnipotentAlgebraicGroup (R i).carrierVariety)
    (l : List (RayLetter σ R)) : definingGroup σ p :=
  (l.map (rayLetterValue σ p R hR)).prod

@[simp] theorem pointEmbedding_rayWord {ι : Type*} (R : ι → ClosedSubgroup K)
    (hR : ∀ i, IsUnipotentAlgebraicGroup (R i).carrierVariety)
    (l : List (RayLetter σ R)) :
    pointEmbedding σ p (rayWord σ p R hR l) =
      (l.map (fun a => a.2.val.val)).prod := by
  induction l with
  | nil => exact map_one _
  | cons a l ih =>
    change pointEmbedding σ p (rayLetterValue σ p R hR a * rayWord σ p R hR l) = _
    rw [map_mul, ih]
    rfl

/-- Raw root-word normalizer identities construct a lift in the residual. -/
def normalizerOfRayWord (T : ClosedSubgroup K) {ι : Type*}
    (R : ι → ClosedSubgroup K)
    (hR : ∀ i, IsUnipotentAlgebraicGroup (R i).carrierVariety)
    (l : List (RayLetter σ R))
    (hn : (l.map (fun a => a.2.val.val)).prod ∈ algebraicNormalizer T) :
    normalizer σ p T :=
  ⟨rayWord σ p R hR l, by
    change pointEmbedding σ p (rayWord σ p R hR l) ∈ algebraicNormalizer T
    rwa [pointEmbedding_rayWord]⟩

@[simp] theorem residualProjection_normalizerOfRayWord (T : ClosedSubgroup K)
    {ι : Type*} (R : ι → ClosedSubgroup K)
    (hR : ∀ i, IsUnipotentAlgebraicGroup (R i).carrierVariety)
    (l : List (RayLetter σ R))
    (hn : (l.map (fun a => a.2.val.val)).prod ∈ algebraicNormalizer T) :
    residualProjection σ p T (normalizerOfRayWord σ p T R hR l hn) =
      QuotientGroup.mk (⟨(l.map (fun a => a.2.val.val)).prod, hn⟩ : algebraicNormalizer T) := by
  change QuotientGroup.mk (intermediateNormalizerEmbedding σ T (definingGroup σ p)
    (normalizerOfRayWord σ p T R hR l hn)) = _
  congr 1
  exact Subtype.ext (pointEmbedding_rayWord σ p R hR l)

theorem rayWord_mem_sup {ι : Type*} (R : ι → ClosedSubgroup K)
    (hR : ∀ i, IsUnipotentAlgebraicGroup (R i).carrierVariety)
    (U V : ClosedSubgroup K)
    (hUV : ∀ i, (R i).toSubgroup ≤ U.toSubgroup ∨ (R i).toSubgroup ≤ V.toSubgroup)
    (l : List (RayLetter σ R)) :
    rayWord σ p R hR l ∈ positive σ p U ⊔ positive σ p V := by
  have hU : positive σ p U ≤ positive σ p U ⊔ positive σ p V := le_sup_left
  have hV : positive σ p V ≤ positive σ p U ⊔ positive σ p V := le_sup_right
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  rcases hUV a.1 with h | h
  · exact hU (h a.2.property)
  · exact hV (h a.2.property)

end Words

/-- Reflection order two in the literal quotient forces the lift square into
the literal residual torus. -/
theorem square_mem_torus_of_projection (σ : AlgebraicEndomorphism K) (p : ℕ)
    (T : ClosedSubgroup K) (n : normalizer σ p T)
    (hs : residualProjection σ p T n * residualProjection σ p T n = 1) :
    n.val * n.val ∈ torus σ p T := by
  have h : n * n ∈ (residualProjection σ p T).ker := by
    change residualProjection σ p T (n * n) = 1
    rwa [map_mul]
  rwa [residualProjection_ker] at h

/-- Generation in the fixed algebraic Weyl group turns marked local lifts into
surjectivity. Neither global Bruhat coverage nor finite BN axioms are used. -/
theorem residualProjection_range_eq_of_generators (σ : AlgebraicEndomorphism K)
    (p : ℕ) (T : ClosedSubgroup K)
    (hσT : T.toSubgroup.map σ.onPoints = T.toSubgroup)
    {J : Type*} (s : J → algebraicWeyl T)
    (hgen : Subgroup.closure (Set.range s) = weylFixed σ T hσT)
    (n : J → normalizer σ p T) (hn : ∀ i, residualProjection σ p T (n i) = s i) :
    (residualProjection σ p T).range = weylFixed σ T hσT := by
  apply le_antisymm ((intermediateProjection_range_le_fixed σ T (definingGroup σ p)).trans
    (fixedProjection_range_le_weylFixed σ T hσT))
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨n i, hn i⟩

/-- Canonical quotient identification on every intermediate group, obtained
from marked residual lifts of a generating family. -/
noncomputable def intermediateQuotientEquivOfGenerators
    (σ : AlgebraicEndomorphism K) (p : ℕ) (T : ClosedSubgroup K)
    (hσT : T.toSubgroup.map σ.onPoints = T.toSubgroup)
    {J : Type*} (s : J → algebraicWeyl T)
    (hgen : Subgroup.closure (Set.range s) = weylFixed σ T hσT)
    (n : J → normalizer σ p T) (hn : ∀ i, residualProjection σ p T (n i) = s i)
    (L : Subgroup (fixedPoints σ)) (hL : definingGroup σ p ≤ L) :
    (intermediateNormalizer σ T L ⧸
      (intermediateTorus σ T L).subgroupOf (intermediateNormalizer σ T L)) ≃*
        weylFixed σ T hσT :=
  (intermediateQuotientEquivImage σ T L).trans (MulEquiv.subgroupCongr (by
    apply le_antisymm ((intermediateProjection_range_le_fixed σ T L).trans
      (fixedProjection_range_le_weylFixed σ T hσT))
    rw [← residualProjection_range_eq_of_generators σ p T hσT s hgen n hn]
    exact residualProjection_range_le_intermediate σ p T L hL))

@[simp] theorem intermediateQuotientEquivOfGenerators_mk
    (σ : AlgebraicEndomorphism K) (p : ℕ) (T : ClosedSubgroup K)
    (hσT : T.toSubgroup.map σ.onPoints = T.toSubgroup)
    {J : Type*} (s : J → algebraicWeyl T)
    (hgen : Subgroup.closure (Set.range s) = weylFixed σ T hσT)
    (n : J → normalizer σ p T) (hn : ∀ i, residualProjection σ p T (n i) = s i)
    (L : Subgroup (fixedPoints σ)) (hL : definingGroup σ p ≤ L)
    (m : intermediateNormalizer σ T L) :
    ((intermediateQuotientEquivOfGenerators σ p T hσT s hgen n hn L hL
      (QuotientGroup.mk m) : weylFixed σ T hσT) : algebraicWeyl T) =
        intermediateProjection σ T L m := rfl

/-- The full fixed normalizer is `N H1`, using exactly the residual inclusion. -/
theorem fixed_normalizer_factors_of_generators
    (σ : AlgebraicEndomorphism K) (p : ℕ) (T : ClosedSubgroup K)
    (hσT : T.toSubgroup.map σ.onPoints = T.toSubgroup)
    {J : Type*} (s : J → algebraicWeyl T)
    (hgen : Subgroup.closure (Set.range s) = weylFixed σ T hσT)
    (n : J → normalizer σ p T) (hn : ∀ i, residualProjection σ p T (n i) = s i)
    (m : fixedNormalizer σ T) :
    ∃ r : normalizer σ p T, ∃ t : fixedTorus σ T, m.val = r.val.val * t.val := by
  have hm := fixedProjection_range_le_weylFixed σ T hσT ⟨m, rfl⟩
  rw [← residualProjection_range_eq_of_generators σ p T hσT s hgen n hn] at hm
  obtain ⟨r, hr⟩ := hm
  let r₁ : fixedNormalizer σ T := ⟨r.val.val, r.property⟩
  have he : fixedProjection σ T (r₁⁻¹ * m) = 1 := by
    rw [map_mul, map_inv]
    change (residualProjection σ p T r)⁻¹ * fixedProjection σ T m = 1
    rw [hr, inv_mul_cancel]
  have ht : (r₁⁻¹ * m).val ∈ fixedTorus σ T := by
    change r₁⁻¹ * m ∈ (fixedTorus σ T).subgroupOf (fixedNormalizer σ T)
    rw [← fixedProjection_ker]
    exact he
  exact ⟨r, ⟨(r₁⁻¹ * m).val, ht⟩, (mul_inv_cancel_left r.val.val m.val).symm⟩

/-- Lifting a generating family controls the full normalizer, including its
torus parameters. This is the generation input needed by the Bruhat parent. -/
theorem normalizer_le_of_generators (σ : AlgebraicEndomorphism K) (p : ℕ)
    (T : ClosedSubgroup K)
    (hσT : T.toSubgroup.map σ.onPoints = T.toSubgroup)
    {J : Type*} (s : J → algebraicWeyl T)
    (hgen : Subgroup.closure (Set.range s) = weylFixed σ T hσT)
    (n : J → normalizer σ p T) (hn : ∀ i, residualProjection σ p T (n i) = s i)
    (A : Subgroup (definingGroup σ p)) (hH : torus σ p T ≤ A)
    (hA : ∀ i, (n i).val ∈ A) : normalizer σ p T ≤ A := by
  have hmap : weylFixed σ T hσT ≤
      (A.subgroupOf (normalizer σ p T)).map (residualProjection σ p T) := by
    rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨n i, hA i, hn i⟩
  intro x hx
  have hw : residualProjection σ p T ⟨x, hx⟩ ∈ weylFixed σ T hσT :=
    fixedProjection_range_le_weylFixed σ T hσT
      (intermediateProjection_range_le_fixed σ T (definingGroup σ p) ⟨⟨x, hx⟩, rfl⟩)
  obtain ⟨m, hm, he⟩ := hmap hw
  have ht : x * m.val⁻¹ ∈ torus σ p T :=
    (intermediateProjection_eq_iff σ T (definingGroup σ p) ⟨x, hx⟩ m).mp he.symm
  have h := A.mul_mem (hH ht) hm
  simpa only [Subgroup.coe_subtype, inv_mul_cancel_right] using h

/-- Literal consumer of marked root words and the parent's `U N U` coverage:
it proves GLS3 2.3.8(e) once torus word generation and opposition are supplied. -/
theorem positive_sup_negative_eq_top (σ : AlgebraicEndomorphism K) (p : ℕ)
    (T U V : ClosedSubgroup K)
    (hσT : T.toSubgroup.map σ.onPoints = T.toSubgroup)
    {J : Type*} (s : J → algebraicWeyl T)
    (hgen : Subgroup.closure (Set.range s) = weylFixed σ T hσT)
    (n : J → normalizer σ p T) (hn : ∀ i, residualProjection σ p T (n i) = s i)
    (hH : torus σ p T ≤ positive σ p U ⊔ positive σ p V)
    (hword : ∀ i, (n i).val ∈ positive σ p U ⊔ positive σ p V)
    (hcover : ∀ g : definingGroup σ p, ∃ u ∈ positive σ p U,
      ∃ m ∈ normalizer σ p T, ∃ v ∈ positive σ p U, g = u * m * v) :
    positive σ p U ⊔ positive σ p V = ⊤ := by
  have hU : positive σ p U ≤ positive σ p U ⊔ positive σ p V := le_sup_left
  apply top_unique
  intro g _
  obtain ⟨u, hu, m, hm, v, hv, rfl⟩ := hcover g
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hU hu)
    (normalizer_le_of_generators σ p T hσT s hgen n hn _ hH hword hm)) (hU hv)

section ResidualGeneration

variable [IsAlgClosed k] (σ : AlgebraicEndomorphism K) (p : ℕ)
  [Fact p.Prime] [CharP k p] [Fact (IsAlgebraicSteinbergEndomorphism σ)]

omit [IsAlgClosed k] in
/-- The full fixed torus, not just its residual intersection, has order prime to p. -/
theorem fixedTorus_card_coprime (T : ClosedSubgroup K) (hT : IsSubtorus T) :
    Nat.Coprime p (Nat.card (fixedTorus σ T)) := by
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro hdvd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := fixedTorus σ T) p hdvd
  have hpow : t.val.val ^ (p ^ 1) = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    simpa only [pow_one, Subgroup.coe_pow, Subgroup.coe_one] using
      congrArg (fun x : fixedTorus σ T => x.val.val) h
  have he : t = 1 := Subtype.ext (Subtype.ext
    (hT.eq_one_of_mem_of_pow_prime_pow_eq_one t.property 1 hpow))
  rw [he, orderOf_one] at ht
  exact (Fact.out : p.Prime).ne_one ht.symm

omit [IsAlgClosed k] in
/-- If the full fixed group is generated by A and the fixed torus, and that
torus normalizes A, then the source residual lies in A. This supplies the finite
torus factors by the prime-to-p residual convention, without assuming them. -/
theorem definingGroup_le_of_torus_sup (T : ClosedSubgroup K) (hT : IsSubtorus T)
    (A : Subgroup (fixedPoints σ))
    (hgen : A ⊔ fixedTorus σ T = ⊤)
    (hnorm : fixedTorus σ T ≤ Subgroup.normalizer (A : Set (fixedPoints σ))) :
    definingGroup σ p ≤ A := by
  have hAn : A.Normal := Subgroup.normalizer_eq_top_iff.mp (by
    apply top_unique
    rw [← hgen]
    exact sup_le A.le_normalizer hnorm)
  let := hAn
  let f : fixedTorus σ T →* fixedPoints σ ⧸ A :=
    (QuotientGroup.mk' A).comp (fixedTorus σ T).subtype
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    change ((QuotientGroup.mk' A).comp (fixedTorus σ T).subtype).range = ⊤
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have h := congrArg (Subgroup.map (QuotientGroup.mk' A)) hgen
    simpa only [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective A)] using h
  exact Subgroup.primeToResidual_le A
    ((fixedTorus_card_coprime σ p T hT).coprime_dvd_right
      (Subgroup.card_dvd_of_surjective f hf))

omit [IsAlgClosed k] in
/-- Apply the residual argument to the actual full fixed-point Bruhat coverage.
The only torus input is its action on A, not torus membership in A. Marked
reflection lifts and their Weyl generation supply every normalizer factor. -/
theorem definingGroup_le_of_fixed_coverage
    (T U : ClosedSubgroup K) (hT : IsSubtorus T)
    (hσT : T.toSubgroup.map σ.onPoints = T.toSubgroup)
    {J : Type*} (s : J → algebraicWeyl T)
    (hgen : Subgroup.closure (Set.range s) = weylFixed σ T hσT)
    (n : J → normalizer σ p T) (hn : ∀ i, residualProjection σ p T (n i) = s i)
    (A : Subgroup (fixedPoints σ))
    (hU : U.toSubgroup.comap (fixedPoints σ).subtype ≤ A)
    (hword : ∀ i, (n i).val.val ∈ A)
    (hH : fixedTorus σ T ≤ Subgroup.normalizer (A : Set (fixedPoints σ)))
    (hcover : ∀ g : fixedPoints σ,
      ∃ u ∈ U.toSubgroup.comap (fixedPoints σ).subtype,
      ∃ m ∈ fixedNormalizer σ T,
      ∃ v ∈ U.toSubgroup.comap (fixedPoints σ).subtype, g = u * m * v) :
    definingGroup σ p ≤ A := by
  apply definingGroup_le_of_torus_sup σ p T hT A _ hH
  let C := A ⊔ fixedTorus σ T
  have hAC : A ≤ C := le_sup_left
  have hTC : fixedTorus σ T ≤ C := le_sup_right
  have hN : normalizer σ p T ≤ C.comap (definingGroup σ p).subtype := by
    apply normalizer_le_of_generators σ p T hσT s hgen n hn
    · intro t ht
      exact hTC ht
    · intro i
      exact hAC (hword i)
  have hN₁ : fixedNormalizer σ T ≤ C := by
    intro m hm
    obtain ⟨r, t, he⟩ := fixed_normalizer_factors_of_generators σ p T hσT s hgen n hn ⟨m, hm⟩
    change m = r.val.val * t.val at he
    rw [he]
    exact C.mul_mem (hN r.property) (hTC t.property)
  apply top_unique
  intro g _
  obtain ⟨u, hu, m, hm, v, hv, rfl⟩ := hcover g
  exact C.mul_mem (C.mul_mem (hAC (hU hu)) (hN₁ hm)) (hAC (hU hv))

/-- The actual residual is generated by positive and opposite fixed unipotent
groups. In particular this proves that its finite torus factors are such words.
The parent's full fixed-point coverage, local torus normalization, and marked
reflection words are the explicit inputs still to be constructed geometrically. -/
theorem definingGroup_eq_fixed_positive_sup_negative
    (T U V : ClosedSubgroup K) (hT : IsSubtorus T)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hV : IsUnipotentAlgebraicGroup V.carrierVariety)
    (hσT : T.toSubgroup.map σ.onPoints = T.toSubgroup)
    {J : Type*} (s : J → algebraicWeyl T)
    (hgen : Subgroup.closure (Set.range s) = weylFixed σ T hσT)
    (n : J → normalizer σ p T) (hn : ∀ i, residualProjection σ p T (n i) = s i)
    (hword : ∀ i, (n i).val.val ∈
      U.toSubgroup.comap (fixedPoints σ).subtype ⊔ V.toSubgroup.comap (fixedPoints σ).subtype)
    (hH : fixedTorus σ T ≤
      Subgroup.normalizer (U.toSubgroup.comap (fixedPoints σ).subtype : Set (fixedPoints σ)) ⊓
      Subgroup.normalizer (V.toSubgroup.comap (fixedPoints σ).subtype : Set (fixedPoints σ)))
    (hcover : ∀ g : fixedPoints σ,
      ∃ u ∈ U.toSubgroup.comap (fixedPoints σ).subtype,
      ∃ m ∈ fixedNormalizer σ T,
      ∃ v ∈ U.toSubgroup.comap (fixedPoints σ).subtype, g = u * m * v) :
    definingGroup σ p = U.toSubgroup.comap (fixedPoints σ).subtype ⊔
      V.toSubgroup.comap (fixedPoints σ).subtype := by
  apply le_antisymm
  · exact definingGroup_le_of_fixed_coverage σ p T U hT hσT s hgen n hn _
      le_sup_left hword (hH.trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)) hcover
  · exact sup_le (fixed_unipotent_le_definingGroup σ p U hU)
      (fixed_unipotent_le_definingGroup σ p V hV)

/-- The source generation statement on the literal residual carrier. Unlike
`positive_sup_negative_eq_top`, this needs no separate finite-torus generation
premise: full fixed coverage and torus normalization discharge it. The equality
`V = U^(w0)` is an independent root/opposition comparison. -/
theorem positive_sup_negative_eq_top_of_fixed_coverage
    (T U V : ClosedSubgroup K) (hT : IsSubtorus T)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hV : IsUnipotentAlgebraicGroup V.carrierVariety)
    (hσT : T.toSubgroup.map σ.onPoints = T.toSubgroup)
    {J : Type*} (s : J → algebraicWeyl T)
    (hgen : Subgroup.closure (Set.range s) = weylFixed σ T hσT)
    (n : J → normalizer σ p T) (hn : ∀ i, residualProjection σ p T (n i) = s i)
    (hword : ∀ i, (n i).val.val ∈
      U.toSubgroup.comap (fixedPoints σ).subtype ⊔ V.toSubgroup.comap (fixedPoints σ).subtype)
    (hH : fixedTorus σ T ≤
      Subgroup.normalizer (U.toSubgroup.comap (fixedPoints σ).subtype : Set (fixedPoints σ)) ⊓
      Subgroup.normalizer (V.toSubgroup.comap (fixedPoints σ).subtype : Set (fixedPoints σ)))
    (hcover : ∀ g : fixedPoints σ,
      ∃ u ∈ U.toSubgroup.comap (fixedPoints σ).subtype,
      ∃ m ∈ fixedNormalizer σ T,
      ∃ v ∈ U.toSubgroup.comap (fixedPoints σ).subtype, g = u * m * v) :
    positive σ p U ⊔ positive σ p V = ⊤ := by
  have hmap (R : ClosedSubgroup K) (hR : IsUnipotentAlgebraicGroup R.carrierVariety) :
      (positive σ p R).map (definingGroup σ p).subtype =
        R.toSubgroup.comap (fixedPoints σ).subtype := by
    change ((R.toSubgroup.comap (fixedPoints σ).subtype).comap
      (definingGroup σ p).subtype).map (definingGroup σ p).subtype = _
    apply Subgroup.map_comap_eq_self
    rw [Subgroup.range_subtype]
    exact fixed_unipotent_le_definingGroup σ p R hR
  apply Subgroup.map_injective (definingGroup σ p).subtype_injective
  rw [Subgroup.map_sup, hmap U hU, hmap V hV, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact (definingGroup_eq_fixed_positive_sup_negative σ p T U V hT hU hV hσT
    s hgen n hn hword hH hcover).symm

end ResidualGeneration

end Theory.AlgebraicGroup.FiniteBruhatSylow.TitsDescent.FixedWeyl
