module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.BorelSourceConstituents
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ResidualKnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.KnownSimple

/-!
# Suzuki constituents on the literal original singular centralizer

The original A₅ setup identifies C_G(V₁) with the chosen involution's
centralizer. Source13.6.26(1) makes the actual extra component escape N_G(L),
and13.6.25 supplies the solvable-overgroup condition. The full Borel source
theorem then gives trivial and Steinberg constituents on the original U_H/V₁,
without changing its component inclusion or quotient map.

Source: Aschbacher–Smith13.6.25–27, printed pp.934–935. No5.2.3 or
component-uniqueness premise is used.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative TensorProduct MonoidAlgebra
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open Section08 Ratio BenderSuzuki.MatrixGroups Representation SourceParameters
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
universe u
variable {G : Type u} [Group G]

/-- A normal intrinsic component has its original ambient image normalized
by the whole local group. -/
theorem source_component_normalizer (H : Subgroup G) (D : Subgroup H) [D.Normal] :
    H ≤ normalizer (D.map H.subtype : Set G) := by
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    D.le_normalizer_map H.subtype

/-- The source star-image is literally the intrinsic component's image
under the original quotient map. -/
theorem source_component_starImage (H : Subgroup G) (D : Subgroup H) :
    Source.starImage H (D.map H.subtype) = D.map (QuotientGroup.mk' (pCore 2 H)) := by
  simp only [Source.starImage, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]

variable [Finite G]
    {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
attribute [local instance] sourceSpanCommGroup

set_option backward.isDefEq.respectTransparency false in
private theorem constituents_of_centralizer_eq
    (d : Context T L V V₁ V₂ V₃) {z : G} (hz : zpowers z = V₁)
    (H : Subgroup G) (hH : H = centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (hn : H ≤ normalizer (V₁ : Set G))
    (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
    (D : Subgroup H) [D.Normal]
    {m : ℕ} (hm : 1 ≤ m) (e : (D ⧸ pCore 2 D) ≃* SuzukiMatrixGroup m)
    (hout : ¬ D.map H.subtype ≤ normalizer (L : Set G))
    (h25 : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J →
      J ≤ normalizer (L : Set G))
    (K : Type*) [Field K] [Algebra (ZMod 2) K] [Algebra (SuzukiNatural.F m) K] :
    let A := D.map H.subtype
    ∃ f : SuzukiMatrixGroup m ≃* (A ⧸ pCore 2 A),
      typeSpan ((extendScalars K (representation H V₃ V₁ hn)).comp (A.subgroupOf H).subtype)
          (trivial K (A.subgroupOf H) K) ⊔
        typeSpan ((extendScalars K (representation H V₃ V₁ hn)).comp (A.subgroupOf H).subtype)
          (markedComponentSteinberg (map_subtype_le D) K f) = ⊤ ∧
      ∀ J : Subrepresentation
          ((extendScalars K (representation H V₃ V₁ hn)).comp (A.subgroupOf H).subtype),
        IsAtom J →
        Nonempty (J.toRepresentation.Equiv (trivial K (A.subgroupOf H) K)) ∨
          Nonempty (J.toRepresentation.Equiv (markedComponentSteinberg (map_subtype_le D) K f)) := by
  subst H
  exact normal_component_source_constituents hn hk d hz D (map_subtype_le D) hm e hout h25 K

set_option backward.isDefEq.respectTransparency false in
/-- The original normal extra component has precisely the source trivial
and Steinberg type span on the literal singular-centralizer module. Both
earlier source premises are discharged on the original A₅ context. -/
theorem source_context_constituents
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    [IsElementaryAbelian 2 (Source.UH (centralizer (V₁ : Set G)) V₃)]
    (hn : centralizer (V₁ : Set G) ≤ normalizer (V₁ : Set G))
    (hk : commutatorPreimage (centralizer (V₁ : Set G))
      (Source.UH (centralizer (V₁ : Set G)) V₃) V₁ = Source.QH (centralizer (V₁ : Set G)))
    (D : Subgroup (centralizer (V₁ : Set G))) [D.Normal] (hD : D.IsCComponent)
    {m : ℕ} (hm : 1 ≤ m) (e : (D ⧸ pCore 2 D) ≃* SuzukiMatrixGroup m)
    (K : Type*) [Field K] [Algebra (ZMod 2) K] [Algebra (SuzukiNatural.F m) K] :
    let H := centralizer (V₁ : Set G)
    let A := D.map H.subtype
    ∃ f : SuzukiMatrixGroup m ≃* (A ⧸ pCore 2 A),
      typeSpan ((extendScalars K (representation H V₃ V₁ hn)).comp (A.subgroupOf H).subtype)
          (trivial K (A.subgroupOf H) K) ⊔
        typeSpan ((extendScalars K (representation H V₃ V₁ hn)).comp (A.subgroupOf H).subtype)
          (markedComponentSteinberg (map_subtype_le D) K f) = ⊤ ∧
      ∀ J : Subrepresentation
          ((extendScalars K (representation H V₃ V₁ hn)).comp (A.subgroupOf H).subtype),
        IsAtom J →
        Nonempty (J.toRepresentation.Equiv (trivial K (A.subgroupOf H) K)) ∨
          Nonempty (J.toRepresentation.Equiv (markedComponentSteinberg (map_subtype_le D) K f)) := by
  let := d.elementary
  obtain ⟨s, hz, _⟩ := source_parameter_setup_knownSimple d hCv houtside hcounter
  have hC : centralizer (V₁ : Set G) = centralizer ({s.z.val} : Set G) := by
    rw [← hz, zpowers_eq_closure, centralizer_closure]
  have hH := SourceAbelian.point_centralizer_mem_family d houtside
  have hout : ¬ D.map (centralizer (V₁ : Set G)).subtype ≤ normalizer (L : Set G) := by
    apply (source_13_6_26_of_context_knownSimple d hCv houtside hcounter
      (residualCentralizer L V₁) _ hH).1
    refine ⟨map_subtype_le D, ?_⟩
    simpa only [subgroupOf,
      comap_map_eq_self_of_injective (centralizer (V₁ : Set G)).subtype_injective] using hD
  exact constituents_of_centralizer_eq d hz _ hC hn hk D hm e hout
    (source_13_6_25_knownSimple d.hypothesis.qtke s).2.2.1 K

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
