module

public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.Construction.Normalizer
public import Theory.GroupTheory.ScalarRootResidual

/-!
# Recovering the genuine root group from its scalar action

A nonidentity scalar makes every additive root element a commutator with
its relative normalizer: solve (a-1)y=x. Thus a model calculation of C_L(X)
and one nontrivial root scalar identify the intrinsic `residualRoot` with
the transported root group. This is the centerless recovery step used in
the root construction; the nontrivial cover retains its commutator lift.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
Lemma 16.5.13, printed p.1201.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot.Construction
open Subgroup
open scoped commutatorElement
variable {G F : Type*} [Group G] [Field F]

/-- A genuine additive root curve acted on by a nontrivial scalar is the
commutator with its relative normalizer. -/
theorem root_eq_normalizer_commutator (L : Subgroup G)
    (r : Multiplicative F →* G) (t : G)
    (ht : t ∈ relativeNormalizer L r.range) (a : F) (ha : a ≠ 1)
    (hact : ∀ x : F, t * r (Multiplicative.ofAdd x) * t⁻¹ =
      r (Multiplicative.ofAdd (a * x))) :
    ⁅relativeNormalizer L r.range, r.range⁆ = r.range := by
  apply le_antisymm (le_normalizer_iff_commutator_le_right.mp inf_le_right)
  rintro _ ⟨x, rfl⟩
  let y : F := x.toAdd / (a - 1)
  have hm : ⁅t, r (Multiplicative.ofAdd y)⁆ ∈
      ⁅relativeNormalizer L r.range, r.range⁆ :=
    commutator_mem_commutator ht ⟨_, rfl⟩
  have he : ⁅t, r (Multiplicative.ofAdd y)⁆ = r x := by
    rw [commutatorElement_def, hact, ← map_inv, ← map_mul]
    congr 1
    change a * y + -y = x.toAdd
    dsimp [y]
    field_simp [sub_ne_zero.mpr ha]
    ring
  rwa [he] at hm

/-- Apply the scalar calculation to the literal residual centralizer, giving
the required equality with the transported concrete root subgroup. -/
theorem residualRoot_eq_of_scalar {L X : Subgroup G}
    (r : Multiplicative F →* G) (hD : L ⊓ centralizer (X : Set G) = r.range)
    (t : G) (ht : t ∈ relativeNormalizer L r.range) (a : F) (ha : a ≠ 1)
    (hact : ∀ x : F, t * r (Multiplicative.ofAdd x) * t⁻¹ =
      r (Multiplicative.ofAdd (a * x))) : residualRoot L X = r.range := by
  rw [residualRoot, hD]
  exact root_eq_normalizer_commutator L r t ht a ha hact

end CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot.Construction
