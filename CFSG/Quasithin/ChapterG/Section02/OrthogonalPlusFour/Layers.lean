module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Defs
public import Theory.GroupTheory.AlmostSpecialIntersection
public import Theory.GroupTheory.IrreducibleNormalizerCore

/-!
# The normal layers in the plus-four almost-special argument

The Frattini bounds put the commutators of U and Uᵍ in V_L. Their
intersection is therefore central modulo V_L in the generated group I.
Adjoining V_L makes this intersection invariant, and the resulting normal
two-subgroup lies in O₂(I). Irreducibility of the actual I-action on V_L
then makes V_L central in that core. The model calculation supplying this
irreducibility, invariance and containment is a separate source step.

Normalization of U by the core gives the marked commutator inclusions
and the quadratic-action bound, without assuming a module decomposition.

Source: Aschbacher–Smith, G.2.6(3–4) and the start of its module argument,
combined manuscript of 1 March 2004, printed p.336.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup
variable {G : Type*} [Group G]

theorem point_le_VL (D : Setup G) : D.V₁ ≤ D.VL := le_conjugateSpanBy _ _

theorem L_normalizes_VL (D : Setup G) : D.L ≤ normalizer (D.VL : Set G) :=
  le_normalizer_conjugateSpanBy _ _

theorem core_normalized (D : Setup G) (g : G) :
    D.I g ≤ normalizer (D.S g : Set G) := by
  have h := (pCore 2 (D.I g)).le_normalizer_map (D.I g).subtype
  rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
  exact h

theorem conjugate_core (D : Setup G) (g : G) (hg : g ∈ D.I g) :
    conjugate (D.S g) g = D.S g :=
  mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (D.S g : Set G)).inv_mem (core_normalized D g hg))

theorem conjugate_W (D : Setup G) (g : G) (hg : g ∈ D.I g) :
    conjugate (D.W g) g = conjugate D.U g ⊓ D.S g := by
  change (D.U ⊓ D.S g).map (MulAut.conj g⁻¹).toMonoidHom = _
  rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective]
  rw [show (D.S g).map (MulAut.conj g⁻¹).toMonoidHom = D.S g from
    conjugate_core D g hg]
  rfl

/-- G.2.2's containment in the actual Sylow makes U a two-group. -/
theorem U_isPGroup [Finite G] {D : Setup G}
    (h : D.BaseHypothesis) (hc : ClosureConclusions D) : IsPGroup 2 D.U := by
  obtain ⟨P, hP⟩ := h.sylow_LT
  have hT : IsPGroup 2 D.T := by
    rw [← hP]
    exact P.isPGroup'.map D.LT.subtype
  exact hT.of_injective (inclusion hc.normal.1) (inclusion_injective _)

/-- The source derived bound, using G.2.2 rather than irreducibility. -/
theorem derived_le_point [Finite G] {D : Setup G}
    (h : D.BaseHypothesis) (hc : ClosureConclusions D) : ⁅D.U, D.U⁆ ≤ D.V₁ :=
  derived_le_of_frattini_image_le (U_isPGroup h hc) hc.frattini

/-- Both generators have derived subgroup in V_L; this controls their
common intersection against the whole group they generate. -/
theorem intersection_commutator [Finite G] {D : Setup G} {g : G}
    (h : D.BaseHypothesis) (hc : ClosureConclusions D)
    (hg : g ∈ D.L) (hN : D.I g ≤ normalizer (D.VL : Set G)) :
    ⁅D.S₂ g, D.I g⁆ ≤ D.VL := by
  have hd := (derived_le_point h hc).trans (point_le_VL D)
  have hdg : ⁅conjugate D.U g, conjugate D.U g⁆ ≤ D.VL := by
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hd
    rw [map_commutator] at hm
    have he : D.VL.map (MulAut.conj g⁻¹).toMonoidHom = D.VL :=
      mem_normalizer_iff_map_conj_eq.mp
        ((normalizer (D.VL : Set G)).inv_mem (L_normalizes_VL D hg))
    exact hm.trans he.le
  exact intersection_commutator_sup_le hd hdg hN

/-- Adjoining V_L yields the printed commutator bound [S₂,I] ≤ V_L. -/
theorem S₂_commutator [Finite G] {D : Setup G} {g : G}
    (h : D.BaseHypothesis) (hc : ClosureConclusions D) (hg : g ∈ D.L)
    (hVI : D.VL ≤ D.I g) (hN : D.I g ≤ normalizer (D.VL : Set G)) :
    ⁅S₂ D g, D.I g⁆ ≤ D.VL := by
  have hE : D.S₂ g ≤ D.I g := inf_le_left.trans le_sup_left
  have hsup : S₂ D g ≤ commutatorPreimage (D.I g) (D.I g) D.VL :=
    sup_le (le_commutatorPreimage hVI (le_normalizer_iff_commutator_le_left.mp hN))
      (le_commutatorPreimage hE (intersection_commutator h hc hg hN))
  exact (commutator_mono hsup le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hN)

/-- The normal middle layer and every inclusion of the source I-series.
Normality is inside I, and is not asserted in the ambient group. -/
theorem normal_layers [Finite G] {D : Setup G} {g : G}
    (h : D.BaseHypothesis) (hc : ClosureConclusions D) (hg : g ∈ D.L)
    (hVp : IsPGroup 2 D.VL) (hVI : D.VL ≤ D.I g)
    (hN : D.I g ≤ normalizer (D.VL : Set G)) :
    D.VL ≤ S₂ D g ∧ S₂ D g ≤ D.S g ∧
      (D.VL.subgroupOf (D.I g)).Normal ∧ ((S₂ D g).subgroupOf (D.I g)).Normal ∧
      ⁅S₂ D g, D.I g⁆ ≤ D.VL := by
  have hE : D.S₂ g ≤ D.I g := inf_le_left.trans le_sup_left
  have hmidI : S₂ D g ≤ D.I g := sup_le hVI hE
  have hcomm := S₂_commutator h hc hg hVI hN
  have hmidN : D.I g ≤ normalizer (S₂ D g : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hcomm.trans le_sup_left)
  have hEp : IsPGroup 2 (D.S₂ g) :=
    (U_isPGroup h hc).of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hmidp : IsPGroup 2 (S₂ D g) :=
    hVp.to_sup_of_normal_left' hEp (hE.trans hN)
  exact ⟨le_sup_left, le_pCoreIn_of_normalizes hmidp hmidI hmidN,
    (normal_subgroupOf_iff_le_normalizer hVI).mpr hN,
    (normal_subgroupOf_iff_le_normalizer hmidI).mpr hmidN, hcomm⟩

/-- The first layer is central in the core once the natural module's
irreducibility under I has been established. -/
theorem central_first_layer [Finite G] {D : Setup G} {g : G}
    (hVp : IsPGroup 2 D.VL) (hVI : D.VL ≤ D.I g)
    (hN : D.I g ≤ normalizer (D.VL : Set G))
    (hirr : ∀ A : Subgroup G, A ≤ D.VL → D.I g ≤ normalizer (A : Set G) →
      A = ⊥ ∨ A = D.VL) :
    D.VL ≤ D.S g ⊓ centralizer (D.S g : Set G) :=
  le_inf (le_pCoreIn_of_normalizes hVp hVI hN)
    (le_centralizer_iff.mp
      (pCoreIn_le_centralizer_of_irreducible D.VL (D.I g) (D.I g) hVp hVI hN le_rfl hirr))

/-- The join defining S₂ is the literal ordered product in the source. -/
theorem S₂_product {D : Setup G} {g : G}
    (hN : D.I g ≤ normalizer (D.VL : Set G)) :
    (S₂ D g : Set G) = (D.VL : Set G) * (D.S₂ g : Set G) :=
  coe_mul_of_right_le_normalizer_left _ _
    ((show D.S₂ g ≤ D.I g from inf_le_left.trans le_sup_left).trans hN)

/-- The core normalizes both W and Wᵍ. -/
theorem core_normalizes_marks {D : Setup G} {g : G} (hg : g ∈ D.I g)
    (hSU : D.S g ≤ normalizer (D.U : Set G)) :
    D.S g ≤ normalizer (D.W g : Set G) ∧
      D.S g ≤ normalizer (conjugate (D.W g) g : Set G) := by
  have hW : D.S g ≤ normalizer (D.W g : Set G) :=
    (le_inf hSU (D.S g).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hh := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hW).trans
    ((D.W g).le_normalizer_map (MulAut.conj g⁻¹).toMonoidHom)
  change conjugate (D.S g) g ≤ normalizer (conjugate (D.W g) g : Set G) at hh
  rw [conjugate_core D g hg] at hh
  exact ⟨hW, hh⟩

/-- The two W-marks intersect in U ∩ Uᵍ even though S₂ is larger. -/
theorem marked_intersection {D : Setup G} {g : G} (hg : g ∈ D.I g)
    (hES : S₂ D g ≤ D.S g) :
    D.W g ⊓ conjugate (D.W g) g = D.S₂ g := by
  rw [conjugate_W D g hg]
  apply le_antisymm
  · exact fun _ hx => ⟨hx.1.1, hx.2.1⟩
  · intro x hx
    have hxS := hES (mem_sup_right hx)
    exact ⟨⟨hx.1, hxS⟩, ⟨hx.2, hxS⟩⟩

/-- The candidate core join is the source product WWᵍ. Its equality
with S is the separate odd-residual/central-kernel step. -/
theorem coreProduct_product {D : Setup G} {g : G} (hg : g ∈ D.I g)
    (hSU : D.S g ≤ normalizer (D.U : Set G)) :
    (coreProduct D g : Set G) = (D.W g : Set G) * (conjugate (D.W g) g : Set G) := by
  apply coe_mul_of_right_le_normalizer_left
  have hXS : conjugate (D.W g) g ≤ D.S g := by
    rw [conjugate_W D g hg]
    exact inf_le_right
  exact hXS.trans (core_normalizes_marks hg hSU).1

/-- The displacement of S under U lies in the literal W. -/
theorem core_commutator_U {D : Setup G} {g : G}
    (hSU : D.S g ≤ normalizer (D.U : Set G)) : ⁅D.S g, D.U⁆ ≤ D.W g := by
  rw [commutator_comm]
  exact le_inf (le_normalizer_iff_commutator_le_left.mp hSU)
    (le_normalizer_iff_commutator_le_right.mp
      ((show D.U ≤ D.I g from le_sup_left).trans (core_normalized D g)))

/-- The source candidate P=WWᵍ is I-normal and makes S/P central in
I/P. Eliminating that central two-kernel remains a separate argument. -/
theorem coreProduct_normal_and_commutator {D : Setup G} {g : G}
    (hg : g ∈ D.I g) (hSU : D.S g ≤ normalizer (D.U : Set G)) :
    coreProduct D g ≤ D.S g ∧ D.I g ≤ normalizer (coreProduct D g : Set G) ∧
      ⁅D.S g, D.I g⁆ ≤ coreProduct D g := by
  have hXS : conjugate (D.W g) g ≤ D.S g := by
    rw [conjugate_W D g hg]
    exact inf_le_right
  have hPS : coreProduct D g ≤ D.S g := sup_le inf_le_right hXS
  have hU : ⁅D.S g, D.U⁆ ≤ coreProduct D g := (core_commutator_U hSU).trans le_sup_left
  have hUg : ⁅D.S g, conjugate D.U g⁆ ≤ coreProduct D g := by
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (core_commutator_U hSU)
    rw [map_commutator] at hm
    change ⁅conjugate (D.S g) g, conjugate D.U g⁆ ≤ conjugate (D.W g) g at hm
    rw [conjugate_core D g hg] at hm
    exact hm.trans le_sup_right
  have hIN : D.I g ≤ normalizer (coreProduct D g : Set G) :=
    sup_le (le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono hPS le_rfl).trans hU))
      (le_normalizer_iff_commutator_le_left.mpr
        ((commutator_mono hPS le_rfl).trans hUg))
  refine ⟨hPS, hIN, ?_⟩
  rw [commutator_comm] at hU hUg ⊢
  have hC : D.I g ≤ commutatorPreimage (D.I g) (D.S g) (coreProduct D g) :=
    sup_le (le_commutatorPreimage le_sup_left hU) (le_commutatorPreimage le_sup_right hUg)
  exact (commutator_mono hC le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hIN)

/-- Quadraticity modulo S₂ follows from the stronger bound into V₁.
This is a commutator calculation, with no representation decomposition input. -/
theorem quadratic_bound [Finite G] {D : Setup G} {g : G}
    (h : D.BaseHypothesis) (hc : ClosureConclusions D)
    (hSU : D.S g ≤ normalizer (D.U : Set G)) :
    ⁅⁅D.S g, D.U⁆, D.U⁆ ≤ D.V₁ :=
  (commutator_mono ((core_commutator_U hSU).trans inf_le_left) le_rfl).trans
    (derived_le_point h hc)

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
