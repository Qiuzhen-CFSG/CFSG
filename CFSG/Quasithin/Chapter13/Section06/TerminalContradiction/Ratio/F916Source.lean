module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.SourceKernel
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.ModuleBound.OriginalF916

/-!
# The actual F.9.16(3) witness in the terminal A₅ argument

The A₅ weak-closure theorem gives commutativity of intersecting conjugates.
The marked hyperplane has the same centralizer as V, so its centralizer
satisfies the normalizer test used in the original F.9.16 construction.
The abelian centralizer closure restricts to every source overgroup H.
These facts supply the critical geometry and both full-denominator cases
of the existing F.9.16 witness construction, on the literal U_H/V₁ action.

The witness lies in O₂((LT)∩H), and its image in H/O₂(H) is nontrivial,
elementary abelian, quadratic and of fixed codimension at most twice its
rank. The terminal consumer therefore needs no separate F.9.16 premise.
The earlier component conclusion and B.4 classifications remain inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.16(3),
printed pp.323–324, applied in the final paragraph of 13.6, printed p.935.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio
open Section08
open Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₃ V₁ H : Subgroup G} [IsElementaryAbelian 2 V]

private noncomputable def sourceConjugationSection
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (h91 : SourceF91 T L V V₃ V₁ H)
    (hn : H ≤ normalizer (V₁ : Set G))
    (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H) :
    ConjugationSection H (Source.UH H V₃) V₁ (starRepresentation H V₃ V₁ hn hk) where
  le := h91.UH_le
  normalizes := le_normalizer_conjugateSpanBy V₃ H
  centralizes := h91.a_centralizes
  line_le := h91.line_le_UH
  quotient := (MulEquiv.multiplicativeAdditive (Source.Utilde H V₃ V₁)).symm.toMonoidHom.comp
    (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)))
  surjective := (MulEquiv.multiplicativeAdditive _).symm.surjective.comp
    (QuotientGroup.mk'_surjective _)
  kernel := by ext u; exact QuotientGroup.eq_one_iff u
  conjugates := by
    intro a u
    exact (congrArg (fun f => f (Additive.ofMul
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)))
      (starRepresentation_mk H V₃ V₁ hn hk a)).trans
      (representation_apply H V₃ V₁ hn a u)

omit [Finite G] in
/-- The original A₅ weak-closure result includes intersecting conjugates. -/
theorem intersecting_conjugates_commute_of_five
    (d : FiveCoordinates V) (v z : V)
    (hv : BinaryPermutation.FiveGeometry.form (d.equiv v).toAdd ≠ 0)
    (hz : z ≠ 1) (hqz : BinaryPermutation.FiveGeometry.form (d.equiv z).toAdd = 0)
    (hAlt : alternatingGroup (Fin 5) ≤ d.actor.range)
    (hfusion : ∀ x : V, x ≠ 1 → ∀ a : G, MulAut.conj a x.val ∈ V →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n x.val = MulAut.conj a x.val)
    [IsMulCommutative (centralizerConjugateClosure V z.val)]
    (hCv : centralizer ({v.val} : Set G) ≤ normalizer (V : Set G))
    (g : G) (hi : V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  by_cases hg : g ∈ normalizer (V : Set G)
  · have he : V.map (MulAut.conj g).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp hg
    rw [he]
    exact commutator_self_eq_bot_iff.mpr inferInstance
  · exact (source_13_6_24_from_earlier V d.equiv v z hv hz hqz
      (d.orbits hAlt) hfusion hCv g hg hi).2.2

/-- The original marked A₅ data supply the literal F.9.16(3) witness. -/
theorem earlierF9163_of_five
    (d : FiveCoordinates V) (v z : V)
    (hv : BinaryPermutation.FiveGeometry.form (d.equiv v).toAdd ≠ 0)
    (hz : z ≠ 1) (hqz : BinaryPermutation.FiveGeometry.form (d.equiv z).toAdd = 0)
    (hAlt : alternatingGroup (Fin 5) ≤ d.actor.range)
    (hfusion : ∀ x : V, x ≠ 1 → ∀ a : G, MulAut.conj a x.val ∈ V →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n x.val = MulAut.conj a x.val)
    [IsMulCommutative (centralizerConjugateClosure V z.val)]
    (hCv : centralizer ({v.val} : Set G) ≤ normalizer (V : Set G))
    (hmark : ∀ x : V, x.val ∈ V₃ ↔ (d.equiv x).toAdd.val 4 = 0)
    (hN : normalizer (V₃ : Set G) ≤ normalizer (V : Set G)) :
    EarlierF9163 T L V V₃ (zpowers z.val) := by
  intro H hU h98 hn hk
  let := hU
  let D : ChapterF.Section09.Setup G := ⟨T, L, V, V₃, zpowers z.val, H⟩
  have hD : D.Hypothesis := h98.toSourceF91.f9Hypothesis
  have hHC : H ≤ centralizer ({z.val} : Set G) := by
    simpa only [zpowers_eq_closure, centralizer_closure] using h98.a_centralizes
  let : IsMulCommutative (conjugateSpanBy V (centralizer ({z.val} : Set G))) := by
    rw [←centralizerConjugateClosure_eq_conjugateSpanBy]
    infer_instance
  let : IsMulCommutative (conjugateSpanBy V H) :=
    conjugateSpanBy_isMulCommutative_of_le le_rfl hHC
  let : IsElementaryAbelian 2 D.VH :=
    conjugateSpanBy_elementary_of_commutative V H
  let : IsElementaryAbelian 2 D.UH := hU
  obtain ⟨A, hA, hq⟩ :=
    Chapter15.Section03.AbelianAmalgam.ModuleBound.OriginalF916.exists_placed_quadratic_member
      D hD (sourceConjugationSection h98.toSourceF91 hn hk)
      (intersecting_conjugates_commute_of_five d v z hv hz hqz hAlt hfusion hCv) (by
        intro x hx
        left
        apply commutator_eq_bot_iff_le_centralizer.mpr
        exact (le_centralizer_iff.mp (d.centralizer_hyperplane_le V₃ hmark hN))
          |>.trans (Subgroup.centralizer_le (zpowers_le.mpr hx)))
  exact ⟨A.subgroupOf H, comap_mono hA, hq⟩

universe u

/-- The actual terminal A₅ contradiction with both F.9 source premises discharged. -/
theorem terminal_contradiction_of_five_source
    {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G)
    {T : Sylow 2 G} {L V V₃ M : Subgroup G} [IsElementaryAbelian 2 V]
    (d : FiveCoordinates V) (v z : V)
    (hv : BinaryPermutation.FiveGeometry.form (d.equiv v).toAdd ≠ 0)
    (hz : z ≠ 1) (hz2 : orderOf z.val = 2)
    (hqz : BinaryPermutation.FiveGeometry.form (d.equiv z).toAdd = 0)
    (hAlt : alternatingGroup (Fin 5) ≤ d.actor.range)
    (hfusion : ∀ x : V, x ≠ 1 → ∀ a : G, MulAut.conj a x.val ∈ V →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n x.val = MulAut.conj a x.val)
    [IsMulCommutative (centralizerConjugateClosure V z.val)]
    (hCv : centralizer ({v.val} : Set G) ≤ normalizer (V : Set G))
    (hmark : ∀ x : V, x.val ∈ V₃ ↔ (d.equiv x).toAdd.val 4 = 0)
    (hN : normalizer (V₃ : Set G) ≤ normalizer (V : Set G))
    (hcontains : residualCentralizer L (zpowers z.val) ⊔ (T : Subgroup G) ≤
      centralizer ({z.val} : Set G))
    (houtside : ¬ centralizer ({z.val} : Set G) ≤ M)
    (hcomponents : Components.Conclusion
      ((T : Subgroup G).subgroupOf (centralizer ({z.val} : Set G))))
    (h1357 : Earlier1357 T L V V₃ (zpowers z.val) (centralizer ({z.val} : Set G)) M)
    (hB42 : SourceClassifications.FullB42.{u,u} 𝒦)
    (hB45 : Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource.FullB45.{u,u} 𝒦) :
    False := by
  exact terminal_contradiction_of_source_kernel hG d v z hv hz hz2 hqz hAlt hfusion hCv
    hmark hN hcontains houtside hcomponents h1357
    (earlierF9163_of_five d v z hv hz hqz hAlt hfusion hCv hmark hN) hB42 hB45

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio
