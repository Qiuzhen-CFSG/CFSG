module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.BorelSourceModule
public import Theory.Representation.Suzuki.BorelFixedSemisimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.SemisimpleSpan

/-!
# Semisimplicity on the original Suzuki component section

The full Suzuki Borel fixes each original V₃ seed in U_H/V₁. After scalar
extension, the ovoid permutation decomposition places each seed in a
semisimple Suzuki submodule. Pulling back through the literal component
quotient and taking the H-span proves semisimplicity on the entire section.

The final application constructs the genuine F.11 pair from a normal extra
component in C_G(z), retaining the original quotient and conjugation action.
The earlier-source hypotheses are the actual kernel identity, containment
in H, and the 13.6.25 solvable-overgroup conclusion.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), §13.6,
printed p.918, and Notation 13.5.8, printed pp.934–935.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative TensorProduct MonoidAlgebra
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open ChapterF.Source Section08 Ratio BenderSuzuki.MatrixGroups Representation
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H A : Subgroup G}
  [hU : IsElementaryAbelian 2 (Source.UH H V₃)]
  (hn : H ≤ normalizer (V₁ : Set G))
  (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
  (hAH : A ≤ H) (hHA : H ≤ normalizer (A : Set G))
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
local instance sourceSpanCommGroup : CommGroup (Source.UH H V₃) :=
  inferInstance

set_option backward.isDefEq.respectTransparency false in
def markedExtendedComponentRepresentation
    {m : ℕ} (K : Type*) [Field K] [Algebra (ZMod 2) K]
    (f : SuzukiMatrixGroup m ≃* (A ⧸ pCore 2 A)) :=
  (extendScalars (F := ZMod 2) (G := A ⧸ pCore 2 A) (V := Space H V₃ V₁)
    K (componentQuotientRepresentation hn hk hAH hHA)).comp f.toMonoidHom

include d in
set_option backward.isDefEq.respectTransparency false in
/-- In one compatible matrix marking, every actual source seed belongs to a
semisimple Suzuki submodule after scalar extension. -/
theorem source_pair_semisimple_seeds
    (hF : HypothesisF11 ![L,A] (T : Subgroup G))
    {z : G} (hz : zpowers z = V₁) (hAC : A ≤ centralizer ({z} : Set G))
    {m : ℕ} (hm : 1 ≤ m)
    (e : (A ⧸ pCore 2 A) ≃* SuzukiMatrixGroup m)
    (K : Type*) [Field K] [Algebra (ZMod 2) K] [Algebra (SuzukiNatural.F m) K] :
    ∃ f : SuzukiMatrixGroup m ≃* (A ⧸ pCore 2 A),
      ∀ a : V₃, ∃ S : Subrepresentation
        (markedExtendedComponentRepresentation hn hk hAH hHA K f),
        S.IsSemisimple ∧ (1 : K) ⊗ₜ[ZMod 2] seedVector (H := H) (V₁ := V₁) a ∈ S := by
  obtain ⟨f,hfix⟩ := source_pair_borel_marking hn hk hAH hHA d hF hz hAC hm e
  refine ⟨f,fun a => ?_⟩
  apply SuzukiSmallDegree.borel_fixed_semisimple_subrepresentation hm
  intro g hg
  change (extendScalars K (componentQuotientRepresentation hn hk hAH hHA)) (f g)
    ((1 : K) ⊗ₜ[ZMod 2] seedVector (H := H) (V₁ := V₁) a) = _
  rw [extendScalars_apply, LinearMap.baseChange_tmul, hfix a g hg]


omit [Finite G] in
set_option backward.isDefEq.respectTransparency false in
/-- The marked quotient action pulls back to the literal normal component action. -/
theorem markedExtendedComponentRepresentation_comp
    {m : ℕ} (K : Type*) [Field K] [Algebra (ZMod 2) K]
    (f : SuzukiMatrixGroup m ≃* (A ⧸ pCore 2 A)) :
    (markedExtendedComponentRepresentation hn hk hAH hHA K f).comp
      (f.symm.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 A)).comp
        (subgroupOfEquivOfLe hAH).toMonoidHom)) =
      (extendScalars K (representation H V₃ V₁ hn)).comp (A.subgroupOf H).subtype := by
  apply MonoidHom.ext
  intro a
  change (extendScalars K (componentQuotientRepresentation hn hk hAH hHA))
    (f (f.symm (QuotientGroup.mk' (pCore 2 A) (subgroupOfEquivOfLe hAH a)))) = _
  rw [f.apply_symm_apply, extendScalars_apply, componentQuotientRepresentation_mk]
  rfl

include d hk hAH hHA in
set_option backward.isDefEq.respectTransparency false in
/-- The original central section restricts semisimply to the actual normal
Suzuki component, after any compatible scalar extension. -/
theorem source_pair_component_semisimple
    (hF : HypothesisF11 ![L,A] (T : Subgroup G))
    {z : G} (hz : zpowers z = V₁) (hAC : A ≤ centralizer ({z} : Set G))
    {m : ℕ} (hm : 1 ≤ m)
    (e : (A ⧸ pCore 2 A) ≃* SuzukiMatrixGroup m)
    (K : Type*) [Field K] [Algebra (ZMod 2) K] [Algebra (SuzukiNatural.F m) K] :
    IsSemisimpleModule K[A.subgroupOf H] (Representation.asModule
      ((extendScalars K (representation H V₃ V₁ hn)).comp (A.subgroupOf H).subtype)) := by
  let : (A.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHA
  obtain ⟨f,hs⟩ := source_pair_semisimple_seeds hn hk hAH hHA d hF hz hAC hm e K
  let p : A.subgroupOf H →* SuzukiMatrixGroup m :=
    f.symm.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 A)).comp
      (subgroupOfEquivOfLe hAH).toMonoidHom)
  have hp : Function.Surjective p := f.symm.surjective.comp
    ((QuotientGroup.mk'_surjective (pCore 2 A)).comp (subgroupOfEquivOfLe hAH).surjective)
  have he := markedExtendedComponentRepresentation_comp hn hk hAH hHA K f
  change (markedExtendedComponentRepresentation hn hk hAH hHA K f).comp p = _ at he
  apply Ratio.extendScalars_normal_restriction_semisimple hn K (A.subgroupOf H)
  intro a
  obtain ⟨S,hS,ha⟩ := hs a
  rw [← he]
  exact ⟨S.compActors p,ha,Representation.compActors_semisimple _ p hp S hS⟩


include d hk in
set_option backward.isDefEq.respectTransparency false in
/-- A normal extra Suzuki component in the original involution centralizer acts
semisimply on the scalar extension of U_H/V₁. The source F.11 and full-Borel
fixation hypotheses are discharged from the original A₅ context. -/
theorem normal_component_source_semisimple
    {z : G} (hz : zpowers z = V₁)
    (D : Subgroup (centralizer ({z} : Set G))) [D.Normal]
    (hDH : D.map (centralizer ({z} : Set G)).subtype ≤ H)
    {m : ℕ} (hm : 1 ≤ m) (e : (D ⧸ pCore 2 D) ≃* SuzukiMatrixGroup m)
    (hout : ¬ D.map (centralizer ({z} : Set G)).subtype ≤ normalizer (L : Set G))
    (h25 : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J →
      J ≤ normalizer (L : Set G))
    (K : Type*) [Field K] [Algebra (ZMod 2) K] [Algebra (SuzukiNatural.F m) K] :
    IsSemisimpleModule K[(D.map (centralizer ({z} : Set G)).subtype).subgroupOf H]
      (Representation.asModule ((extendScalars K (representation H V₃ V₁ hn)).comp
        ((D.map (centralizer ({z} : Set G)).subtype).subgroupOf H).subtype)) := by
  let A := D.map (centralizer ({z} : Set G)).subtype
  have hHC : H ≤ centralizer ({z} : Set G) := by
    have he : centralizer (V₁ : Set G) = centralizer ({z} : Set G) := by
      rw [← hz, zpowers_eq_closure, centralizer_closure]
    rw [← he]
    exact hn.trans (normalizer_le_centralizer_of_card_two _ d.flag.one_card)
  have hHA : H ≤ normalizer (A : Set G) := hHC.trans (by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      D.le_normalizer_map (centralizer ({z} : Set G)).subtype)
  let eD := D.equivMapOfInjective (centralizer ({z} : Set G)).subtype
    (centralizer ({z} : Set G)).subtype_injective
  let eQ := QuotientGroup.congr _ _ eD (pCore_map_iso 2 eD)
  exact source_pair_component_semisimple hn hk hDH hHA d
    (source_A5_suzuki_pair_F11 d hz D e hout h25) hz (map_subtype_le D) hm
    (eQ.symm.trans e) K

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
