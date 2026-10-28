module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Seeds
public import Theory.GroupTheory.ElementaryThompsonSpan
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The global Thompson image and the component-normalization input

J(G_v)* is the image of the global elementary Thompson subgroup, not the
whole best-offender subgroup of the representation. Sylow conjugacy identifies
it with the full conjugate span of J(T_v)*. Its normality is also proved.

The C.1.16(1) input retains every C.1.14 hypothesis. A surjection with precisely
the conjugation centralizer as kernel is equivalent to the source quotient.
For the application, U_v is restricted to G_v, and the proof checks both its
normality and the equality of the two literal centralizers. The universal
C.1.16 implication remains an earlier-source input, owned by the C.1 block
argument; this module does not claim that theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
C.1.14–16, printed pp.125–126, and the paragraph after 13.6.13, p.929.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
universe u
variable {G : Type u} [Group G]

/-- The literal global elementary Thompson image J(G_v)*. -/
noncomputable def JGstar (z v : G) : Subgroup (Gstar z v) :=
  starImage z v (Stellmacher.elementaryAbelianMaxJ (Gv v))

/-- The complete universal first clause of source C.1.16. The actual quotient
map is specified by surjectivity and its exact centralizer kernel. This is an
equivalent quotient presentation of the printed statement, not a proved theorem.
Clauses (2) and (3) are not used by this existence argument. -/
def SourceC116One : Prop :=
  ∀ (H D : Type u) [Group H] [Finite H] [Group D] [Finite D]
    (V : Subgroup H), V.Normal → IsElementaryAbelian 2 V →
    generalizedFitting H = pCore 2 H →
    ∀ (q : H →* D), Function.Surjective q → q.ker = centralizer (V : Set H) →
    pCore 2 D = ⊥ → ∀ (S : Sylow 2 H) (E : Subgroup D), IsComponent D E →
    (Stellmacher.elementaryAbelianMaxJ (S : Subgroup H)).map q ≤ normalizer (E : Set D)

/-- Restriction to G_v and the star map preserve the literal Thompson marking. -/
theorem starImage_intrinsic_thompson (z v : G) (S : Subgroup (Gv v)) (R : Subgroup G)
    (hSR : S.map (Gv v).subtype = R) :
    (Stellmacher.elementaryAbelianMaxJ S).map (starMk z v) =
      starImage z v (Stellmacher.elementaryAbelianMaxJ R) := by
  have hi : (Stellmacher.elementaryAbelianMaxJ S).map (Gv v).subtype =
      Stellmacher.elementaryAbelianMaxJ R := by
    rw [← Stellmacher.elementaryAbelianMaxJ_map_injective _ (Gv v).subtype_injective, hSR]
  rw [starImage, ← hi]
  change _ = (((Stellmacher.elementaryAbelianMaxJ S).map
    (Gv v).subtype).comap (Gv v).subtype).map (starMk z v)
  rw [comap_map_eq_self_of_injective (Gv v).subtype_injective]

/-- The global Thompson image is normal in the faithful quotient. -/
theorem JGstar_normal (z v : G) : (JGstar z v).Normal := by
  have he : (Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup (Gv v))).map
      (starMk z v) = JGstar z v :=
    starImage_intrinsic_thompson z v ⊤ (Gv v) (by rw [← MonoidHom.range_eq_map, range_subtype])
  let : (Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup (Gv v))).Characteristic :=
    Stellmacher.elementaryAbelianMaxJ_top_characteristic
  rw [← he]
  exact Subgroup.Normal.map inferInstance _ (starMk_surjective z v)

variable [Finite G]

/-- Global Thompson generation passes through the actual star quotient. -/
theorem JGstar_eq_conjugateSpan (T : Subgroup G) (z v : G)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v)) :
    JGstar z v = conjugateSpanBy
      (starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))) ⊤ := by
  obtain ⟨S, hS⟩ := hSyl
  have he : (Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup (Gv v))).map
      (starMk z v) = JGstar z v :=
    starImage_intrinsic_thompson z v ⊤ (Gv v) (by rw [← MonoidHom.range_eq_map, range_subtype])
  rw [← he, Stellmacher.elementaryAbelianMaxJ_eq_conjugateSpan_sylow S,
    map_conjugateSpanBy, map_top_of_surjective _ (starMk_surjective z v),
    starImage_intrinsic_thompson z v (S : Subgroup (Gv v)) (Tv T v) hS]

/-- Apply universal C.1.16(1) to U_v inside G_v, identifying its exact kernel. -/
theorem thompsonStar_normalizes_components (hC116 : SourceC116One.{u})
    (T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [hU : IsElementaryAbelian 2 (Uv z v)]
    (hF : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hstarCore : pCore 2 (Gstar z v) = ⊥)
    (E : Subgroup (Gstar z v)) (hE : IsComponent (Gstar z v) E) :
    starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v)) ≤ normalizer (E : Set _) := by
  let U := (Uv z v).subgroupOf (Gv v)
  have hUn : U.Normal := normal_subgroupOf_of_le_normalizer (Gv_normalizes_Uv z v)
  have hUe : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf (Uv_le_Gv z v hz)
  have hk : (starMk z v).ker = centralizer (U : Set (Gv v)) := by
    rw [starMk_ker]
    ext x
    change (x : G) ∈ centralizer (Uv z v : Set G) ↔ x ∈ centralizer (U : Set (Gv v))
    constructor
    · intro hx
      apply mem_centralizer_iff.mpr
      intro y hy
      exact Subtype.ext (mem_centralizer_iff.mp hx y hy)
    · intro hx
      apply mem_centralizer_iff.mpr
      intro y hy
      exact congrArg (fun a : Gv v => (a : G))
        (mem_centralizer_iff.mp hx ⟨y, Uv_le_Gv z v hz hy⟩ hy)
  obtain ⟨S, hS⟩ := hSyl
  have h := hC116 (Gv v) (Gstar z v) U hUn hUe hF
    (starMk z v) (starMk_surjective z v) hk hstarCore S E hE
  rwa [starImage_intrinsic_thompson z v (S : Subgroup (Gv v)) (Tv T v) hS] at h

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
