module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NormalizerSixteen
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SixteenIntersectionNonseed
public import Theory.GroupAction.ElementConjugacyOrbit

/-!
# The full original point stabilizer of the pure sixteen

The marked symplectic quotient acts transitively on the fifteen points.
Orbit–stabilizer gives order 768 for its original point stabilizer. Point-core
covariance puts it inside the normalizer of the corresponding nonseed eight;
the latter also has order 768, so these are the same literal subgroup.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The full normalizer acts transitively on the nonidentity points of
any actual pure sixteen with the proved point-core hyperplanes. -/
theorem TypeAt.sixteen_normalizer_transitive (h : TypeAt z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (hCA : centralizer (A : Set G) = A)
    (hpure : ∀ x ∈ A, x ≠ 1 → IsConj x z)
    (hpoints : ∀ x ∈ A, x ≠ 1 →
      Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8)
    (x y : G) (hx : x ∈ A) (hx1 : x ≠ 1) (hy : y ∈ A) (hy1 : y ≠ 1) :
    ∃ g ∈ normalizer (A : Set G), g * x * g⁻¹ = y := by
  obtain ⟨_, _, _, _, e, φ, hmark⟩ :=
    h.sixteen_symplectic_normalizer A hA hCA hpure hpoints
  let x' : A := ⟨x, hx⟩
  let y' : A := ⟨y, hy⟩
  have hx0 : e (Additive.ofMul x') ≠ 0 := by
    intro he
    have hh := e.injective (he.trans e.map_zero.symm)
    exact hx1 (congrArg (fun a : Additive A => (a.toMul : G)) hh)
  have hy0 : e (Additive.ofMul y') ≠ 0 := by
    intro he
    have hh := e.injective (he.trans e.map_zero.symm)
    exact hy1 (congrArg (fun a : Additive A => (a.toMul : G)) hh)
  obtain ⟨s, _, hs⟩ := Matrix.PSp4Three.exists_generated_send hx0 hy0
  obtain ⟨q, rfl⟩ := φ.surjective s
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (A.subgroupOf (normalizer (A : Set G))) q
  have he : e (Additive.ofMul (A.normalizerMonoidHom g x')) =
      e (Additive.ofMul y') := (hmark g x').symm.trans hs
  exact ⟨g, g.property,
    congrArg (fun a : Additive A => (a.toMul : G)) (e.injective he)⟩

/-- The actual point stabilizer in the full sixteen normalizer has
order 768. -/
theorem TypeAt.sixteen_normalizer_point_card (h : TypeAt z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (hCA : centralizer (A : Set G) = A)
    (hpure : ∀ x ∈ A, x ≠ 1 → IsConj x z)
    (hpoints : ∀ x ∈ A, x ≠ 1 →
      Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8)
    (x : G) (hx : x ∈ A) (hx1 : x ≠ 1) :
    Nat.card (normalizer (A : Set G) ⊓ involutionCentralizer x : Subgroup G) = 768 := by
  let N := normalizer (A : Set G)
  have horb : N.elementOrbit x = (A : Set G) \ {1} := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨(mem_normalizer_iff.mp hg x).mp hx, ?_⟩
      exact fun hh => hx1 ((MulAut.conj g).map_eq_one_iff.mp hh)
    · rintro ⟨hy, hy1⟩
      exact h.sixteen_normalizer_transitive A hA hCA hpure hpoints x y hx hx1 hy hy1
  have ho : Nat.card (N.elementOrbit x) = 15 := by
    rw [horb, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem A.one_mem]
    change Nat.card A - 1 = 15
    omega
  have hc := N.elementOrbit_card x (A.le_normalizer hx)
  rw [ho, h.sixteen_normalizer_card A hA hCA hpure hpoints] at hc
  change 15 * Nat.card (normalizer (A : Set G) ⊓ involutionCentralizer x : Subgroup G) = 11520 at hc
  omega

/-- The point stabilizer is the whole original centralizer-normalizer
of the nonseed point-core eight, with both embeddings retained. -/
theorem TypeAt.sixteen_normalizer_point_eq (h : TypeAt z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (hCA : centralizer (A : Set G) = A)
    (hpure : ∀ x ∈ A, x ≠ 1 → IsConj x z)
    (hpoints : ∀ x ∈ A, x ≠ 1 →
      Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8)
    (x : G) (hx : x ∈ A) (hx1 : x ≠ 1) :
    normalizer (A : Set G) ⊓ involutionCentralizer x =
      involutionCentralizer x ⊓
        normalizer ((A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) : Set G) := by
  obtain ⟨W, hxT⟩ := h.exists_typeAt_of_isConj x (hpure x hx hx1)
  have hxQ : x ∈ (involutionCentralizer x).pCoreIn 2 := by
    change x ∈ (pCore 2 (involutionCentralizer x)).map (involutionCentralizer x).subtype
    rw [← hxT.centralizer_fitting]
    exact hxT.seed_le_core hxT.involution_mem_seed
  let D := A ⊓ (involutionCentralizer x).pCoreIn 2
  have hDe : IsElementaryAbelian 2 D :=
    IsElementaryAbelian.of_injective (inclusion (show D ≤ A from inf_le_left))
      (inclusion_injective _)
  let E : pointCoreEights x := ⟨D, inf_le_right, ⟨hx, hxQ⟩, hDe, hpoints x hx hx1⟩
  have hEn : E.val ∉ pointCoreSeedOrbit x W :=
    hxT.eight_in_sixteen_not_seed E A hA inf_le_left
  change normalizer (A : Set G) ⊓ involutionCentralizer x =
    involutionCentralizer x ⊓ normalizer (E.val : Set G)
  apply eq_of_le_of_card_ge
  · intro g hg
    refine ⟨hg.2, mem_normalizer_iff_map_conj_eq.mpr ?_⟩
    have hgx : g * x * g⁻¹ = x := by
      have hh := mem_centralizer_singleton_iff.mp hg.2
      calc
        g * x * g⁻¹ = x * g * g⁻¹ := by rw [hh]
        _ = x := by simp [mul_assoc]
    change (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G).map
      (MulAut.conj g).toMonoidHom = A ⊓ (involutionCentralizer x).pCoreIn 2
    rw [pointCore_intersection_conjugate A x g hg.1, hgx]
  · rw [h.sixteen_normalizer_point_card A hA hCA hpure hpoints x hx hx1,
      hxT.point_core_nonseed_eight_normalizer_card E hEn]

end CFSG.Quasithin.HigmanSims
