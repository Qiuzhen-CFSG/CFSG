module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.Source
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.SourceClassifications
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Coordinates
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import CFSG.Quasithin.Defs
public import Theory.Quasithin.Rank

/-!
# The F.9 application in the terminal A₅ argument

For H = C_G(z), its central involution proves membership in the literal
H_z family. We apply the universal 13.5.7 implication, prove F.9.8(f)
from the singular-point weak-closure theorem, and prove (g)(i) from the
five-coordinate hyperplane fixer and 13.2.3(2). The abelian conjugate span
is elementary abelian by closure induction. Its literal quotient action
has kernel O₂(H) by F.9.2(3), hence descends faithfully to H/O₂(H).
F.9.16(3) then gives an actual quadratic actor and the bound q ≤ 2.
SQTK for that actor group is inherited from the involution centralizer
and odd-prime rank lifting through the two-core quotient.

The complete 13.6.27 component alternatives, including the nontrivial
L₃(4) diagram action, yield the strict opposite bound through the faithful
irreducible-section construction. `SourceClassifications` uses the full
B.4.2 contract with its corrected projective-line convention and the full
B.4.5 contract. `terminal_contradiction` combines these bounds to obtain
False for the actual involution centralizer and module.

The component conclusion and the universal earlier 13.5.7, F.9.2(3),
F.9.16(3), B.4.2 and B.4.5 implications remain explicit. Their source
producers and the parent Chapter 13 assembly retain final discharge;
this conditional consumer does not assert the unconditional Theorem 13.6.1.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
the last paragraph of §13.6, printed p.935 / PDF p.952.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio
open Section08
variable {G : Type*} [Group G]

/-- The central involution supplies a nontrivial normal two-subgroup of G₁;
thus G₁ belongs to the literal H_z family once its source overgroup and
outside-M conditions hold. -/
theorem centralizer_mem_Hz (L₁ T M : Subgroup G) (z : G) (hz : orderOf z = 2)
    (hcontains : L₁ ⊔ T ≤ centralizer ({z} : Set G))
    (houtside : ¬ centralizer ({z} : Set G) ≤ M) :
    centralizer ({z} : Set G) ∈ Source.Hz L₁ T (centralizer ({z} : Set G)) M := by
  have hzC : zpowers z ≤ centralizer ({z} : Set G) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hnormal : centralizer ({z} : Set G) ≤ normalizer (zpowers z : Set G) := by
    simpa only [zpowers_eq_closure, centralizer_closure] using
      centralizer_le_normalizer (zpowers z : Set G)
  have hcard : Nat.card (zpowers z) = 2 := (Nat.card_zpowers z).trans hz
  have hcore := le_pCoreIn_of_normalizes
    (IsPGroup.of_card (hcard.trans (by norm_num : 2 = 2 ^ 1))) hzC hnormal
  refine ⟨⟨?_, hcontains⟩, le_rfl, houtside⟩
  change (centralizer ({z} : Set G)).pCoreIn 2 ≠ ⊥
  intro hzero
  have hzbot : zpowers z = ⊥ := le_bot_iff.mp (hcore.trans_eq hzero)
  rw [hzbot] at hcard
  simp at hcard

/-- Restrict the abelian centralizer span of V to the actual seed span U_H.
Exponent two is inherited by closure induction, not inferred from its order. -/
theorem source_UH_elementary (V V₃ : Subgroup G) (z : G)
    [IsElementaryAbelian 2 V] (hV₃ : V₃ ≤ V)
    [hcomm : IsMulCommutative (centralizerConjugateClosure V z)] :
    IsElementaryAbelian 2 (Source.UH (centralizer ({z} : Set G)) V₃) := by
  let H := centralizer ({z} : Set G)
  have hspan : IsMulCommutative (conjugateSpanBy V H) := by
    rw [← centralizerConjugateClosure_eq_conjugateSpanBy]
    exact hcomm
  let := hspan
  have helem : IsElementaryAbelian 2 (conjugateSpanBy V H) := by
    let : IsMulCommutative (closure {x | ∃ h ∈ H, ∃ v ∈ V, h * v * h⁻¹ = x}) := hspan
    apply IsElementaryAbelian.closure_of_isMulCommutative
    rintro x ⟨h, _, v, hv, rfl⟩
    rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian v hv, mul_one, mul_inv_cancel]
  let := helem
  exact IsElementaryAbelian.of_le (conjugateSpanBy_mono hV₃ le_rfl)

/-- Both additional F.9.8 clauses are proved using the actual five-coordinate
geometry and the published weak-closure argument. -/
theorem sourceF98_of_five [Finite G]
    {T : Sylow 2 G} {L V V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
    (d : FiveCoordinates V) (v z : V)
    (hv : BinaryPermutation.FiveGeometry.form (d.equiv v).toAdd ≠ 0)
    (hz : z ≠ 1) (hqz : BinaryPermutation.FiveGeometry.form (d.equiv z).toAdd = 0)
    (hAlt : alternatingGroup (Fin 5) ≤ d.actor.range)
    (hfusion : ∀ x : V, x ≠ 1 → ∀ a : G, MulAut.conj a x.val ∈ V →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n x.val = MulAut.conj a x.val)
    [IsMulCommutative (centralizerConjugateClosure V z.val)]
    (hCv : centralizer ({v.val} : Set G) ≤ normalizer (V : Set G))
    (hmark : ∀ x : V, x.val ∈ V₃ ↔ (d.equiv x).toAdd.val 4 = 0)
    (hN : normalizer (V₃ : Set G) ≤ normalizer (V : Set G))
    (h91 : SourceF91 T L V V₃ (zpowers z.val) H) :
    SourceF98 T L V V₃ (zpowers z.val) H := by
  refine ⟨h91, ?_, Or.inl (d.source_F_9_8_g_i V₃ H (zpowers z.val) hmark hN)⟩
  intro g hg
  exact commuting_of_contains_singular_point V d.equiv v z hv hz hqz
    (d.orbits hAlt) hfusion hCv g hg

/-- The terminal source application of 13.5.7, F.9.2(3) and F.9.16(3).
The quotient, kernel, faithful action and additional F.9.8 hypotheses are
constructed here; the exact universal earlier implications remain explicit. -/
theorem exists_bounded_faithful_source_action [Finite G]
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
    (h1357 : Earlier1357 T L V V₃ (zpowers z.val) (centralizer ({z.val} : Set G)) M)
    (hF923 : EarlierF923 T L V V₃ (zpowers z.val))
    (hF9163 : EarlierF9163 T L V V₃ (zpowers z.val)) :
    ∃ hU : IsElementaryAbelian 2 (Source.UH (centralizer ({z.val} : Set G)) V₃),
      letI := hU
      ∃ (hn : centralizer ({z.val} : Set G) ≤ normalizer (zpowers z.val : Set G))
        (hk : commutatorPreimage (centralizer ({z.val} : Set G))
          (Source.UH (centralizer ({z.val} : Set G)) V₃) (zpowers z.val) =
            Source.QH (centralizer ({z.val} : Set G))),
        Function.Injective
          (starRepresentation (centralizer ({z.val} : Set G)) V₃ (zpowers z.val) hn hk) ∧
        Representation.BinaryOffender.quadraticRatio
          (starRepresentation (centralizer ({z.val} : Set G)) V₃ (zpowers z.val) hn hk) ≤ 2 := by
  have hmem := centralizer_mem_Hz _ _ M z.val hz2 hcontains houtside
  have h91 := h1357 _ hmem
  have h98 := sourceF98_of_five d v z hv hz hqz hAlt hfusion hCv hmark hN h91
  let hU := source_UH_elementary V V₃ z.val h91.v₃_le
  let hn := h91.a_centralizes.trans (centralizer_le_normalizer (zpowers z.val : Set G))
  have hk := hF923 _ h91
  exact ⟨hU, hn, hk, starRepresentation_injective _ _ _ hn hk,
    bound_of_F9163 h98 hF9163 hn hk⟩

/-- The actual star actor is an SQTK-group: proper-K is inherited from the
involution centralizer, and odd-prime rank lifts through the two-core quotient. -/
theorem source_star_sqtk [Finite G] {C : GroupClass}
    (hG : IsSimpleQTKE C G) (z : G) (hz : orderOf z = 2) :
    IsSQTK C (Source.Hstar (centralizer ({z} : Set G))) := by
  have hH := hG.involution_centralizer_sqtk hz
  refine ⟨?_, hH.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 _) pCore_isPGroup).trans
    (hH.stronglyQuasithin p hp ho)


universe u

/-- The final module-ratio contradiction of §13.6, on H = C_G(z) and
its literal module U_H/V₁. The five-coordinate geometry establishes
F.9.8(f),(g)(i); the universal 13.5.7 and F.9 inputs give a faithful star
action with ratio at most two. The complete 13.6.27 output gives the
strict opposite bound via the source-correct B.4 classifications.

This is the conditional terminal consumer. The parent supplies the
component conclusion for the actual restriction of T and discharges
the earlier universal implications; this theorem does not assert those
upstream results or the unconditional Theorem 13.6.1. -/
theorem terminal_contradiction
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
    (hF923 : EarlierF923 T L V V₃ (zpowers z.val))
    (hF9163 : EarlierF9163 T L V V₃ (zpowers z.val))
    (hB42 : SourceClassifications.FullB42.{u,u} 𝒦)
    (hB45 : Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource.FullB45.{u,u} 𝒦) :
    False := by
  obtain ⟨hU, hn, hk, _, hq⟩ := exists_bounded_faithful_source_action
    d v z hv hz hz2 hqz hAlt hfusion hCv hmark hN hcontains houtside h1357 hF923 hF9163
  let := hU
  exact (not_lt_of_ge hq) (SourceClassifications.quadraticRatio_gt_two_of_source
    (centralizer ({z.val} : Set G)) V₃ (zpowers z.val) hn hk
    ((T : Subgroup G).subgroupOf (centralizer ({z.val} : Set G))) hcomponents
    (source_star_sqtk hG z.val hz2) hB42 hB45)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio
end
