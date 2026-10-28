module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.Sections

/-!
# The canonical starred upper action in G.2.4

The restriction of the original LT/O₂(LT) projection maps I onto L*.
The earlier kernel equality identifies its kernel with S=O₂(I), so
conjugation on the elementary quotient S/S₂ descends to L*. The binary
section retains the original quotient map on every representative.

The original U gives the root commutator and fixed-space bounds. Elements
of L₁ preserve W; identifying L₁* with the root normalizer then gives
full normalizer invariance. That Borel equality is explicitly retained
here and must be supplied by the A₅ model geometry, before recognition.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(6) and G.1.5(3), printed pp.334 and 328.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup
variable {G : Type*} [Group G]

/-- The restriction of LT→LT/O₂(LT) to I, with literal codomain L*. -/
def upperStarProjection (D : Setup G) (g : G)
    (hILT : D.I g ≤ D.LT) (hstar : D.star (D.I g) = D.star D.L) :
    D.I g →* D.star D.L :=
  ((QuotientGroup.mk' (pCore 2 D.LT)).comp (inclusion hILT)).codRestrict _
    (fun i => hstar ▸ (show QuotientGroup.mk' (pCore 2 D.LT)
      (inclusion hILT i) ∈ D.star (D.I g) from ⟨inclusion hILT i, i.property, rfl⟩))

theorem upperStarProjection_surjective (D : Setup G) (g : G)
    (hILT : D.I g ≤ D.LT) (hstar : D.star (D.I g) = D.star D.L) :
    Function.Surjective (upperStarProjection D g hILT hstar) := by
  intro q
  have hq : (q : D.Star) ∈ D.star (D.I g) := hstar.symm ▸ q.property
  obtain ⟨i, hi, he⟩ := hq
  exact ⟨⟨i, hi⟩, Subtype.ext he⟩

theorem upperStarProjection_on_L (D : Setup G) (g : G)
    (hILT : D.I g ≤ D.LT) (hstar : D.star (D.I g) = D.star D.L)
    (hLI : D.L ≤ D.I g) (l : D.L) :
    upperStarProjection D g hILT hstar (inclusion hLI l) = starProjection D l := rfl

theorem upperStarProjection_map (D : Setup G) (g : G)
    (hILT : D.I g ≤ D.LT) (hstar : D.star (D.I g) = D.star D.L)
    (A : Subgroup G) (hAI : A ≤ D.I g) :
    (A.subgroupOf (D.I g)).map (upperStarProjection D g hILT hstar) =
      (D.star A).subgroupOf (D.star D.L) := by
  ext a
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨inclusion hILT i, hi, rfl⟩
  · rintro ⟨x, hx, he⟩
    exact ⟨⟨x, hAI hx⟩, hx, Subtype.ext he⟩

theorem upperStarProjection_ker (D : Setup G) (g : G)
    (hILT : D.I g ≤ D.LT) (hstar : D.star (D.I g) = D.star D.L)
    (hcore : D.S g = D.I g ⊓ D.LT.pCoreIn 2) :
    (upperStarProjection D g hILT hstar).ker = (D.S g).subgroupOf (D.I g) := by
  ext i
  change upperStarProjection D g hILT hstar i = 1 ↔ (i : G) ∈ D.S g
  rw [Subtype.ext_iff]
  change QuotientGroup.mk' (pCore 2 D.LT) (inclusion hILT i) = 1 ↔ _
  change (QuotientGroup.mk (inclusion hILT i) : D.Star) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro hi
    rw [hcore]
    exact ⟨i.property, ⟨inclusion hILT i, hi, rfl⟩⟩
  · intro hi
    obtain ⟨j, hj, he⟩ := (hcore ▸ hi).2
    exact (show j = inclusion hILT i from Subtype.ext he) ▸ hj

namespace Hypothesis
variable [Finite G] {D : Setup G} {g : G} (d : Hypothesis D g)
include d

/-- Earlier generation and containment in T put I in the original LT. -/
theorem upper_actor_le (hI : D.I g = D.L ⊔ D.U) : D.I g ≤ D.LT := by
  rw [hI]
  exact sup_le le_sup_left (d.setup.U_normal_in_T.1.trans le_sup_right)

/-- The Sylow marking supplies U*≤L*, so I*=L* by earlier generation. -/
theorem upper_actor_star (hI : D.I g = D.L ⊔ D.U)
    (hUL : D.star D.U ≤ D.star D.L) : D.star (D.I g) = D.star D.L := by
  rw [hI, Setup.star, subgroupOf_sup
    (show D.L ≤ D.LT from le_sup_left) (d.setup.U_normal_in_T.1.trans le_sup_right),
    Subgroup.map_sup]
  exact sup_eq_left.mpr hUL

/-- The canonical binary action descends through the actual starred map.
The displayed coordinate identity is the original quotient projection. -/
theorem upper_action (hLI : D.L ≤ D.I g)
    (hcore : D.S g = D.I g ⊓ D.LT.pCoreIn 2)
    (hsplit : D.S g = D.W g ⊔ conjugate (D.W g) g)
    (hILT : D.I g ≤ D.LT) (hstar : D.star (D.I g) = D.star D.L)
    [((S₂ D g).subgroupOf (D.S g)).Normal] :
    let := d.upper_elementary hLI hcore hsplit
    ∃ (σ : Representation (ZMod 2) (D.star D.L) (Additive (UpperQuotient D g)))
      (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g)
        (σ.comp (upperStarProjection D g hILT hstar))),
      ∀ s : D.S g, (c.coordinates s).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)) s) := by
  let := d.upper_elementary hLI hcore hsplit
  exact Representation.BinaryConjugationSection.exists_canonical
    (D.I g) (D.S g) (S₂ D g) (pCoreIn_le 2 _) (d.second_le_core hLI)
    (I_normalizes_core D g)
    (le_normalizer_iff_commutator_le_left.mpr ((d.second_commutator hLI).trans le_sup_left))
    (upperStarProjection D g hILT hstar) (upperStarProjection_surjective D g hILT hstar)
    (upperStarProjection_ker D g hILT hstar hcore)

/-- Root bounds on the exact subgroup U* of L*, with no replacement actor. -/
theorem upper_star_root_bounds
    (hcore : D.S g = D.I g ⊓ D.LT.pCoreIn 2)
    (hILT : D.I g ≤ D.LT) (hstar : D.star (D.I g) = D.star D.L)
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) (D.star D.L) M)
    (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g)
      (σ.comp (upperStarProjection D g hILT hstar))) :
    ∀ a ∈ (D.star D.U).subgroupOf (D.star D.L),
      LinearMap.range (σ a - 1) ≤ c.imageSpace (D.W g) ∧
      ∀ v ∈ c.imageSpace (D.W g), σ a v = v := by
  intro a ha
  rw [← upperStarProjection_map D g hILT hstar D.U le_sup_left] at ha
  obtain ⟨u, hu, rfl⟩ := ha
  exact d.upper_root_bounds hcore _ c u hu

/-- L₁ preserves the literal W-image. Full root-normalizer invariance
requires identifying its starred Borel with N_(L*)(U*). -/
theorem upper_local_normalizes (hLI : D.L ≤ D.I g) :
    D.L₁ ≤ normalizer (D.W g : Set G) := by
  have hL₁L : D.L₁ ≤ D.L := by
    rintro x ⟨y, _, rfl⟩; exact y.property.1
  have hL₁H : D.L₁ ≤ D.H := le_sup_left.trans d.setup.local_le
  exact (le_inf (hL₁H.trans (le_normalizer_conjugateSpanBy D.V D.H))
    ((hL₁L.trans hLI).trans (I_normalizes_core D g))).trans
      inf_normalizer_le_normalizer_inf

/-- Once the earlier A₅ Borel is identified, every normalizer element
preserves the marked subspace by lifting through L₁. -/
theorem upper_normalizer_invariant (hLI : D.L ≤ D.I g)
    (hILT : D.I g ≤ D.LT) (hstar : D.star (D.I g) = D.star D.L)
    (hB : (D.star D.L₁).subgroupOf (D.star D.L) =
      normalizer (((D.star D.U).subgroupOf (D.star D.L)) : Set (D.star D.L)))
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) (D.star D.L) M)
    (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g)
      (σ.comp (upperStarProjection D g hILT hstar))) :
    ∀ a ∈ normalizer (((D.star D.U).subgroupOf (D.star D.L)) : Set (D.star D.L)),
      (c.imageSpace (D.W g)).map (σ a) = c.imageSpace (D.W g) := by
  have hL₁L : D.L₁ ≤ D.L := by
    rintro x ⟨y, _, rfl⟩; exact y.property.1
  intro a ha
  rw [← hB, ← upperStarProjection_map D g hILT hstar D.L₁ (hL₁L.trans hLI)] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  have hc := c.imageSpace_conjBy (D.W g) inf_le_right i
  have hn : (D.W g).conjBy (i : G) = D.W g :=
    mem_normalizer_iff_map_conj_eq.mp (d.upper_local_normalizes hLI hi)
  rw [hn] at hc
  exact hc.symm

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
