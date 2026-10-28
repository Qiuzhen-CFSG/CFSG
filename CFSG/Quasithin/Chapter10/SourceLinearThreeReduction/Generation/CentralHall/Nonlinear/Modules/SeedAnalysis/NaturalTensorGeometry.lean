module
public import Theory.Representation.OrthogonalFourPlusMatrix.NaturalTensor
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.EvenHermitianExclusion
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module

/-!
# Determinant geometry on the original remaining natural tensor

The recognized tensor is put in literal left-right matrix coordinates,
retaining its factor automorphism, the exact O₂ quotient kernel and both
original component restrictions. Conjugation by M intersect N_G(seed) gives
an actual homomorphism to automorphisms of its coefficient field. This
constructs semilinearity for that whole stabilizer, including factor exchanges.

Every nonidentity element of the seed's full linear normalizer moves at least
n binary dimensions. Hence its minimum-involution parameter is at least n;
an element of the original ambient stabilizer moving at most two dimensions
centralizes the seed, since n ≥ 3. The literal Hall alternative retains all
these conclusions alongside its original natural-tensor witness.

This is the original-seed geometry needed for the source's orthogonal-plus
exclusion. Equality of the seed with the full module, and the ambient
reduction to n = 2, still require proof; no stability of the seed under all
of M is assumed or concluded here.
Source: Aschbacher--Smith 9.1.2(1), 9.2.3--7, printed pp.729--732,
and 10.1.1, 10.2.3, pp.741,745, refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
open ClassicalOrthogonal.FourPlusMatrix
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary
local instance (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2

/-- Literal determinant coordinates with the original quotient and both component markings. -/
theorem original_even_seed_determinant
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    ∃ q : localOrbit T L →* SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n),
      Function.Surjective q ∧ q.ker = pCore 2 (localOrbit T L) ∧
      (∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (e (QuotientGroup.mk' _ l),1)) ∧
      (∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,e (QuotientGroup.mk' _ l))) ∧
      ∃ α : MulAut SL(2,GaloisField 2 n),
        ∃ f : Additive D.seed ≃ₗ[ZMod 2] Mat (F := GaloisField 2 n),
          ∀ g v, f (originalSeedAction D g v) =
            representation (NaturalTensor.marking α (q g)) (f v) := by
  obtain ⟨q,hq,hker,hl,hr,σ,_,_,hσ,α,⟨b⟩⟩ :=
    original_even_seed_natural_tensor D c n hn e ht htn hsep
  let a := b.trans (NaturalTensor.binaryTensorEquiv α)
  refine ⟨q,hq,hker,hl,hr,α,a.toLinearEquiv,fun g v => ?_⟩
  rw [←hσ]
  exact LinearMap.congr_fun (a.isIntertwining' (q g)) v

/-- Every nonidentity element of the full seed normalizer moves at least the field degree. -/
theorem original_even_seed_normalizer_displacement_ge
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    ∀ a : linearNormalizer (originalSeedAction D), a ≠ 1 →
      n ≤ Representation.BinaryOffender.NaturalTensor.operatorFixedCodim
        (normalizerRepresentation (originalSeedAction D) a) := by
  obtain ⟨q,hq,_,_,_,σ,_,hf,hσ,α,⟨b⟩⟩ :=
    original_even_seed_natural_tensor D c n hn e ht htn hsep
  let a := b.trans (NaturalTensor.binaryTensorEquiv α)
  have himage : actionImage (originalSeedAction D) = actionImage σ := by
    rw [←hσ]
    ext z
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨q g,Units.ext rfl⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨l,rfl⟩ := hq g
      exact ⟨l,Units.ext rfl⟩
  have hb : ∀ x : linearNormalizer σ, x ≠ 1 →
      n ≤ Representation.BinaryOffender.NaturalTensor.operatorFixedCodim
        (normalizerRepresentation σ x) := by
    intro x hx
    have hh := NaturalTensor.normalizer_displacement_ge σ hf (NaturalTensor.marking α)
      a.toLinearEquiv (fun g v => LinearMap.congr_fun (a.isIntertwining' g) v) x hx
    rwa [Representation.BinaryOffender.NaturalTensor.finrank_field _
      (GaloisField.card 2 n (by omega))] at hh
  unfold normalizerRepresentation linearNormalizer at hb ⊢
  rwa [himage]

/-- The actual seed-preserving elements of M normalize its unchanged orbit action. -/
theorem original_seed_ambient_action_mem_normalizer
    (m : G) (hm : m ∈ D.maximalLocal) (hs : m ∈ normalizer (D.seed : Set G)) :
    (originalSeedNormalizerAction D).asGroupHom ⟨m,hs⟩ ∈
      linearNormalizer (originalSeedAction D) := by
  let U := (localOrbit T L).subgroupOf (normalizer (D.seed : Set G))
  let ρ := originalSeedNormalizerAction D
  have he : actionImage (originalSeedAction D) = U.map ρ.asGroupHom := by
    ext z
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨⟨l,D.orbit_normalizes_seed l.property⟩,l.property,rfl⟩
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,hl⟩,rfl⟩
  have hmn : (⟨m,hs⟩ : normalizer (D.seed : Set G)) ∈ normalizer (U : Set _) := by
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp hm (x : G)
  change ρ.asGroupHom ⟨m,hs⟩ ∈ normalizer (actionImage (originalSeedAction D) : Set _)
  rw [he]
  exact U.le_normalizer_map ρ.asGroupHom ⟨⟨m,hs⟩,hmn,rfl⟩

/-- The actual action homomorphism, without discarding its pointwise seed kernel. -/
def originalSeedAmbientNormalizerHom :
    (D.maximalLocal ⊓ normalizer (D.seed : Set G) : Subgroup G) →*
      linearNormalizer (originalSeedAction D) where
  toFun m := ⟨(originalSeedNormalizerAction D).asGroupHom ⟨m,m.property.2⟩,
    original_seed_ambient_action_mem_normalizer D m m.property.1 m.property.2⟩
  map_one' := Subtype.ext (originalSeedNormalizerAction D).asGroupHom.map_one
  map_mul' m k := Subtype.ext ((originalSeedNormalizerAction D).asGroupHom.map_mul
    ⟨m,m.property.2⟩ ⟨k,k.property.2⟩)

/-- Exact determinant coordinates and semilinearity of M intersect N_G(seed). -/
def OriginalEvenSeedDeterminantCoordinates {t : G} (ht : t ∈ (T : Subgroup G))
    (n : ℕ) (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)) : Prop :=
    ∃ q : localOrbit T L →* SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n),
      Function.Surjective q ∧ q.ker = pCore 2 (localOrbit T L) ∧
      (∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (e (QuotientGroup.mk' _ l),1)) ∧
      (∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,e (QuotientGroup.mk' _ l))) ∧
      ∃ α : MulAut SL(2,GaloisField 2 n),
        ∃ f : Additive D.seed ≃ₗ[ZMod 2] Mat (F := GaloisField 2 n),
          (∀ g v, f (originalSeedAction D g v) =
            representation (NaturalTensor.marking α (q g)) (f v)) ∧
          ∃ φ : (D.maximalLocal ⊓ normalizer (D.seed : Set G) : Subgroup G) →*
              (GaloisField 2 n ≃+* GaloisField 2 n),
            ∀ (m : (D.maximalLocal ⊓ normalizer (D.seed : Set G) : Subgroup G)) c v,
            f (originalSeedNormalizerAction D ⟨m,m.property.2⟩ (f.symm (c • f v))) =
              φ m c • f (originalSeedNormalizerAction D ⟨m,m.property.2⟩ v)

/-- Construct the field action of the actual ambient seed stabilizer in the same determinant coordinates. -/
theorem original_even_seed_ambient_semilinear
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    OriginalEvenSeedDeterminantCoordinates D ht n e := by
  obtain ⟨q,hq,hker,hl,hr,σ,_,hf,hσ,α,⟨b⟩⟩ :=
    original_even_seed_natural_tensor D c n hn e ht htn hsep
  let a := b.trans (NaturalTensor.binaryTensorEquiv α)
  have himage : actionImage (originalSeedAction D) = actionImage σ := by
    rw [←hσ]
    ext z
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨q g,Units.ext rfl⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨l,rfl⟩ := hq g
      exact ⟨l,Units.ext rfl⟩
  have hfield : ∃ φ : linearNormalizer (originalSeedAction D) →*
      (GaloisField 2 n ≃+* GaloisField 2 n), ∀ x c v,
        a (normalizerRepresentation (originalSeedAction D) x (a.symm (c • a v))) =
          φ x c • a (normalizerRepresentation (originalSeedAction D) x v) := by
    have hh := NaturalTensor.normalizer_semilinear σ hf (NaturalTensor.marking α)
      a.toLinearEquiv (fun g v => LinearMap.congr_fun (a.isIntertwining' g) v)
    unfold normalizerRepresentation linearNormalizer at hh ⊢
    rwa [himage]
  obtain ⟨φ,hφ⟩ := hfield
  refine ⟨q,hq,hker,hl,hr,α,a.toLinearEquiv,?_,
    φ.comp (originalSeedAmbientNormalizerHom D),fun m c v => ?_⟩
  · intro g v
    rw [←hσ]
    exact LinearMap.congr_fun (a.isIntertwining' (q g)) v
  · exact hφ (originalSeedAmbientNormalizerHom D m) c v

/-- Apply the full-normalizer bound to the original ambient conjugation action. -/
theorem original_even_seed_ambient_displacement_ge
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (m : G) (hm : m ∈ D.maximalLocal) (hs : m ∈ normalizer (D.seed : Set G))
    (hmove : originalSeedNormalizerAction D ⟨m,hs⟩ ≠ 1) :
    n ≤ Representation.BinaryOffender.NaturalTensor.operatorFixedCodim
      (originalSeedNormalizerAction D ⟨m,hs⟩) := by
  let a : linearNormalizer (originalSeedAction D) :=
    ⟨(originalSeedNormalizerAction D).asGroupHom ⟨m,hs⟩,
      original_seed_ambient_action_mem_normalizer D m hm hs⟩
  have ha : a ≠ 1 := fun he => hmove (congrArg (fun z : linearNormalizer
    (originalSeedAction D) => z.val.val) he)
  exact original_even_seed_normalizer_displacement_ge D c n hn e ht htn hsep a ha

/-- An ambient seed-preserving action moving at most two dimensions is trivial. -/
theorem original_even_seed_small_ambient_action_trivial
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (m : G) (hm : m ∈ D.maximalLocal) (hs : m ∈ normalizer (D.seed : Set G))
    (hsmall : Representation.BinaryOffender.NaturalTensor.operatorFixedCodim
      (originalSeedNormalizerAction D ⟨m,hs⟩) ≤ 2) :
    originalSeedNormalizerAction D ⟨m,hs⟩ = 1 := by
  by_contra hmove
  have hh := original_even_seed_ambient_displacement_ge D c n hn e ht htn hsep m hm hs hmove
  omega

/-- The same small-displacement conclusion as literal ambient centralization. -/
theorem original_even_seed_small_ambient_centralizes
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (m : G) (hm : m ∈ D.maximalLocal) (hs : m ∈ normalizer (D.seed : Set G))
    (hsmall : Representation.BinaryOffender.NaturalTensor.operatorFixedCodim
      (originalSeedNormalizerAction D ⟨m,hs⟩) ≤ 2) :
    m ∈ centralizer (D.seed : Set G) := by
  have he := original_even_seed_small_ambient_action_trivial D c n hn e ht htn hsep m hm hs hsmall
  intro v hv
  have hh := congrArg (fun w : Additive D.seed => (w.toMul : G))
    (LinearMap.congr_fun he (Additive.ofMul ⟨v,hv⟩))
  change m*v*m⁻¹ = v at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The source minimum-involution parameter of the full seed normalizer is at least n. -/
theorem original_even_seed_moduleM_ge
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    n ≤ ChapterE.moduleM (normalizerRepresentation (originalSeedAction D)) := by
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  apply le_csInf ⟨_,Set.mem_insert _ _⟩
  rintro k (rfl | ⟨a,ha,rfl⟩)
  · have hd := original_nonseparated_even_seed_finrank_eq D c n hn e ht htn hsep
    omega
  · have hh := original_even_seed_normalizer_displacement_ge D c n hn e ht htn hsep a
      (by intro he; simp [he] at ha)
    exact hh.trans (Representation.BinaryOffender.NaturalTensor.operatorFixedCodim_le_fixedCodim
      (normalizerRepresentation (originalSeedAction D)) (zpowers a) (mem_zpowers a))

/-- The literal Hall consumer retains determinant geometry, its actual field action and the displacement bound. -/
theorem original_hall_conclusion_or_natural_tensor_displacement
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨
      ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
        ∃ n : ℕ, 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
          ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
            D.seed ≤ centralizer (L : Set G)) ∧
          OriginalEvenNaturalTensorAnalysis D ht n e ∧
          OriginalEvenSeedDeterminantCoordinates D ht n e ∧
          n ≤ ChapterE.moduleM (normalizerRepresentation (originalSeedAction D)) ∧
          (∀ a : linearNormalizer (originalSeedAction D), a ≠ 1 →
            n ≤ Representation.BinaryOffender.NaturalTensor.operatorFixedCodim
              (normalizerRepresentation (originalSeedAction D) a)) := by
  rcases original_hall_conclusion_or_natural_tensor D c with hh | ⟨t,ht,htn,n,hn,e,hs,ha⟩
  · exact Or.inl hh
  · exact Or.inr ⟨t,ht,htn,n,hn,e,hs,ha,
      original_even_seed_ambient_semilinear D c n hn e ht htn hs,
      original_even_seed_moduleM_ge D c n hn e ht htn hs,
      original_even_seed_normalizer_displacement_ge D c n hn e ht htn hs⟩
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
