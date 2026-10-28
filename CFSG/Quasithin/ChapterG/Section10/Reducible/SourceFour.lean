module
public import CFSG.Quasithin.ChapterG.Section10.Reducible.Marking
public import CFSG.Quasithin.ChapterG.Section10.Reducible.RootQuadratic
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Source
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The marked quadratic four-group for B.4.9

A four-subgroup of the genuine quadratic center radical has one common
fixed hyperplane on V/U, because that quotient is the dual of U through
the original pairing. Its order excludes containment in a binary root
group. This discharges the complete source hypothesis of B.4.9(1).
Source: Aschbacher--Smith G.10.4, printed p.358.
-/

public section
open Module Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.ChapterB.NaturalExtensions
open CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem binary_four_not_inRootGroup {n : ℕ} (d : DoubleNatural BinaryField.two n ρ)
    (E : Subgroup G) (hE : Nat.card E = 4) : ¬ InRootGroup d E := by
  rintro ⟨s,i,j,hij,hroot⟩
  let f : BinaryField.two.Carrier → G := fun c =>
    d.natural.groupEquiv.symm (s * Matrix.SpecialLinearGroup.transvection hij c * s⁻¹)
  have hr (a : E) : (a : G) ∈ Set.range f := by
    obtain ⟨c,hc⟩ := hroot a a.property
    exact ⟨c,(congrArg d.natural.groupEquiv.symm hc).symm.trans (d.natural.groupEquiv.symm_apply_apply a)⟩
  let i : E → Set.range f := fun a => ⟨a,hr a⟩
  have hi : Function.Injective i := fun a b he => Subtype.ext (congrArg (fun z : Set.range f => (z : G)) he)
  have hc := (Nat.card_le_card_of_injective i hi).trans
    (Nat.card_le_card_of_surjective (Set.rangeFactorization f) Set.rangeFactorization_surjective)
  change Nat.card E ≤ Nat.card (ZMod 2) at hc
  rw [hE,Nat.card_zmod] at hc
  omega

variable (h : Hypothesis ρ B v W X X₀)
include h

/-- No splitting premise remains: the original G.10 data gives all of B.4.9's
quadratic-four hypotheses on the actual natural submodule. -/
theorem largeDoubleNatural_source (U : Subrepresentation ρ)
    [IsIrreducible U.toRepresentation] (hU0 : U.toSubmodule ≠ ⊥)
    (hUt : U.toSubmodule ≠ ⊤) (hdim : 3 ≤ finrank (ZMod 2) U.toSubmodule) :
    SourceHypotheses (h.largeDoubleNatural U hU0 hUt hdim) := by
  let d := h.largeDoubleNatural U hU0 hUt hdim
  obtain ⟨e,a,he,ha,hquad⟩ := h.exists_quadratic_center_radical U hU0 hUt hdim
  obtain ⟨E',hER,hEa,hEc⟩ := BinaryLinear.LineRadical.exists_four a ha hdim
  let : IsElementaryAbelian 2 E' := hEa
  let E := E'.map e.symm.toMonoidHom
  have hEA : IsElementaryAbelian 2 E := IsElementaryAbelian.map e.symm.toMonoidHom
  have hcard : Nat.card E = 4 := (Subgroup.card_map_of_injective e.symm.injective).trans hEc
  have hle : E ≤ (BinaryLinear.radical (Submodule.span (ZMod 2) {a})).comap e.toMonoidHom := by
    rintro b ⟨c,hc,rfl⟩
    change e (e.symm c) ∈ BinaryLinear.radical (Submodule.span (ZMod 2) {a})
    rw [e.apply_symm_apply]
    exact hER hc
  obtain ⟨eQ,_⟩ := h.quotient_dual_of_large_irreducible_submodule U hU0 hUt hdim
  let l : (V ⧸ U.toSubmodule) →ₗ[ZMod 2] ZMod 2 :=
    (Module.evalEquiv (ZMod 2) U.toSubmodule a).comp eQ.toLinearEquiv.toLinearMap
  have hl : l ≠ 0 := by
    obtain ⟨q,hq⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) ha
    intro hl
    have hh := congrArg (fun k : (V ⧸ U.toSubmodule) →ₗ[ZMod 2] ZMod 2 => k (eQ.symm q)) hl
    change eQ (eQ.symm q) a = 0 at hh
    rw [eQ.apply_symm_apply,hq] at hh
    exact one_ne_zero hh
  have hcodim : finrank (ZMod 2) ((V ⧸ U.toSubmodule) ⧸ l.ker) = 1 := by
    let q := l.quotKerEquivOfSurjective
      (LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hl))
    simpa only [Module.finrank_self] using q.finrank_eq
  have hfixed (b : G) (hb : b ∈ E) (hb1 : b ≠ 1) :
      fixedSpace U.quotientRepresentation (zpowers b) = l.ker := by
    ext z
    rw [mem_fixedSpace_zpowers_iff,LinearMap.mem_ker]
    have hdual : U.toRepresentation.dual b (eQ z) = (e b).symm.dualMap (eQ z) := by
      ext u
      change eQ z (U.toRepresentation b⁻¹ u) = eQ z ((e b).symm u)
      rw [←he,map_inv]
      rfl
    have hequiv : U.quotientRepresentation b z = z ↔ U.toRepresentation.dual b (eQ z) = eQ z := by
      rw [←eQ.injective.eq_iff]
      have ht := LinearMap.congr_fun (eQ.isIntertwining' b) z
      exact ht ▸ Iff.rfl
    rw [hequiv,hdual]
    exact BinaryLinear.LineRadical.dual_fixed_iff a ha (hle hb)
      (fun hh => hb1 (e.injective (hh.trans e.map_one.symm))) (eQ z)
  refine { family := ?_, four := ?_, fourField := ?_ }
  · by_cases hn : finrank (ZMod 2) U.toSubmodule = 3
    · exact Or.inl hn
    · exact Or.inr ⟨rfl,by omega⟩
  · refine ⟨E,⟨hEA,hcard,l.ker,hcodim,hfixed⟩,?_,?_⟩
    · exact fun a ha b hb z => hquad a (hle ha) b (hle hb) z
    · exact fun _ => binary_four_not_inRootGroup d E hcard
  · intro hn
    change 1 = 2 at hn
    omega

end CFSG.Quasithin.ChapterG.Section10.Hypothesis
