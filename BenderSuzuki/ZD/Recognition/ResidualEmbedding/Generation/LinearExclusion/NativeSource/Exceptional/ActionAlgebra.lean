module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Exceptional.Centralizer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.Exceptional.MarkedQuotient.LocalData
public import Theory.GroupTheory.PGroup.HomocyclicFourProduct

/-!
# Square coordinates on the exceptional involution coset

Write B=R₀, A=M°, and V=O₂(M). The homocyclic square map B→A is onto
with kernel A. Since V/B has order two, every displacement m u m⁻¹u⁻¹
lies in B. Its square is the translation term of the actual M-action on
the coset Bu/A, written in A-coordinates. The resulting cocycle identity
constructs this permutation action without assuming any field coordinates.

Source: GLS IV, Chapter 2, Lemma 15.7, exceptional equality branch.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion.Exceptional
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ}
  (s : ExceptionalLocalStructure Z M z t n)
local notation "A" => Subgroup.subgroupOf (closure (Z ∩ (M : Set G))) M
local notation "V" => pCore 2 M

omit [Finite G] in
public theorem kernel_commute (x y : s.kernel) : Commute x y := by
  change x * y = y * x
  apply s.homocyclic.injective
  simp only [map_mul, mul_comm]

omit [Finite G] in
public theorem square_mem (x : s.kernel) : (x : M) ^ 2 ∈ A := by
  have hh := (s.omega (x ^ 2)).mp
    ((square_iff_square_one_of_homocyclic_four s.homocyclic _).mp ⟨x, rfl⟩)
  simpa only [Subgroup.coe_pow] using hh

omit [Finite G] in
public theorem exists_square (a : A) : ∃ x : s.kernel, (x : M) ^ 2 = a := by
  let x : s.kernel := ⟨a, s.distinguished_le a.property⟩
  obtain ⟨y, hy⟩ := (square_iff_square_one_of_homocyclic_four s.homocyclic x).mpr
    ((s.omega x).mpr a.property)
  exact ⟨y, by simpa only [Subgroup.coe_pow] using congrArg Subtype.val hy⟩

omit [Finite G] in
public theorem u_square
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2) :
    s.u ^ 2 = 1 := by
  apply Subtype.ext
  have hh := pow_card_eq_one'
    (x := (⟨s.u, s.u_mem⟩ : centralizer (residualGenerated M z t : Set G)))
  rw [hJ] at hh
  simpa only [Subgroup.coe_pow, OneMemClass.coe_one] using congrArg Subtype.val hh

/-- The translation displacement lies in the literal normal homocyclic
subgroup, because the image V/B is normal of order two. -/
public theorem displacement_mem
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hRV : linearCentralizerClosure M z t = V) (m : M) :
    m * s.u * m⁻¹ * s.u⁻¹ ∈ s.kernel := by
  let q := QuotientGroup.mk' s.kernel
  let W := (V).map q
  have hW : Nat.card W = 2 := s.core_image_card_two hR hRV
  have hn : q m ∈ normalizer (W : Set (M ⧸ s.kernel)) :=
    le_normalizer_of_normal (mem_top _)
  have huW : q s.u ∈ W := mem_map_of_mem q (hRV ▸ s.u_mem_closure)
  have hc := mem_centralizer_iff.mp (normalizer_le_centralizer_of_card_two W hW hn)
    (q s.u) huW
  apply (QuotientGroup.eq_one_iff _).mp
  change q (m * s.u * m⁻¹ * s.u⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
  group

/-- The element of A labeling the conjugate of the base coset uA. -/
@[expose] public def translation
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hRV : linearCentralizerClosure M z t = V) (m : M) : A :=
  ⟨(m * s.u * m⁻¹ * s.u⁻¹) ^ 2,
    square_mem s ⟨_, displacement_mem s hR hRV m⟩⟩

public theorem translation_mul
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hRV : linearCentralizerClosure M z t = V) (m k : M) :
    (translation s hR hRV (m*k) : M) =
      m * (translation s hR hRV k : M) * m⁻¹ * (translation s hR hRV m : M) := by
  let x : s.kernel := ⟨m * (k * s.u * k⁻¹ * s.u⁻¹) * m⁻¹,
    s.kernel_normal.conj_mem _ (displacement_mem s hR hRV k) m⟩
  let y : s.kernel := ⟨m * s.u * m⁻¹ * s.u⁻¹, displacement_mem s hR hRV m⟩
  have hc : Commute (x : M) (y : M) := (kernel_commute s x y).map s.kernel.subtype
  have he : (m*k) * s.u * (m*k)⁻¹ * s.u⁻¹ = (x : M) * y := by dsimp [x,y]; group
  change ((m*k) * s.u * (m*k)⁻¹ * s.u⁻¹) ^ 2 = _
  rw [he, hc.mul_pow]
  dsimp [x, y, translation]
  simp only [pow_two]
  group

/-- Conjugation on Bu/A, in the square coordinates B/A≃A. -/
@[expose, instance_reducible] public def pointAction
    (d : Context Z M z t n)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hRV : linearCentralizerClosure M z t = V) : MulAction M A where
  smul m a := ⟨m * (a : M) * m⁻¹ * translation s hR hRV m,
    (A).mul_mem ((distinguishedClosure_normal d.minimal.disconnected).conj_mem
      _ a.property m) (translation s hR hRV m).property⟩
  one_smul a := by
    apply Subtype.ext
    change (1:M) * (a:M) * (1:M)⁻¹ * (translation s hR hRV 1:M) = a
    simp [translation]
  mul_smul m k a := by
    apply Subtype.ext
    change (m*k) * (a:M) * (m*k)⁻¹ * (translation s hR hRV (m*k):M) =
      m * (k * (a:M) * k⁻¹ * (translation s hR hRV k:M)) * m⁻¹ *
        (translation s hR hRV m:M)
    rw [translation_mul]
    group

end BenderSuzuki.ZD.LinearExclusion.Exceptional
