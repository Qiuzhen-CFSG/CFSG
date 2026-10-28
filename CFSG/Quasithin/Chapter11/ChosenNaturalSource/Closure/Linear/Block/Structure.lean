module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special.ResidualConsequences

/-!
# The special structure of the original closure

The marked point-radical action gives [V,U]=V₁. Since V≤U and
U′≤Φ(U)≤V₁, both the derived subgroup and Frattini subgroup have
ambient image V₁. Once the natural-sum argument removes C_U(L), the
proved center formula identifies Z(U) with this same elementary point.
Thus U is a nonabelian special two-group, with literal intrinsic
equalities Z(U)=U′=Φ(U).

Source: Aschbacher--Smith, 11.5.7, refs/quasithin.pdf, printed p.782.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
include d

/-- The marked point is precisely both original characteristic images. -/
theorem closure_derived_and_frattini
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁) :
    ⁅E.W, E.W⁆ = E.V₁ ∧ (frattini E.W).map E.W.subtype = E.V₁ := by
  let : Fact (IsPGroup 2 E.W) := ⟨d.U_isPGroup hUT⟩
  have hdf : ⁅E.W, E.W⁆ ≤ (frattini E.W).map E.W.subtype := by
    rw [← E.W.map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  have hpd : E.V₁ ≤ ⁅E.W, E.W⁆ := by
    have hmove : ⁅V, E.W⁆ = E.V₁ := d.commutator_V_U_eq_point hUT hf
    rw [← hmove]
    exact commutator_mono (le_conjugateSpanBy V E.G₁) le_rfl
  exact ⟨le_antisymm (hdf.trans hf) hpd, le_antisymm hf (hpd.trans hdf)⟩

/-- The source special-group structure, after removing the central supplement. -/
theorem closure_special
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y)
    (hfixed : E.W ⊓ centralizer (L : Set G) = ⊥) :
    IsPGroup 2 E.W ∧ closureCenter E = E.V₁ ∧
    center E.W = _root_.commutator E.W ∧
    center E.W = frattini E.W ∧ IsElementaryAbelian 2 (center E.W) ∧
    center E.W ≠ ⊥ := by
  have hz : closureCenter E = E.V₁ := by
    rw [Special.closureCenter_eq E d hUT hf hc, hfixed, sup_bot_eq]
  have hs := closure_derived_and_frattini E d hUT hf
  have hzd : center E.W = _root_.commutator E.W := by
    apply (map_injective E.W.subtype_injective)
    rw [E.W.map_subtype_commutator, hs.1]
    exact hz
  have hzf : center E.W = frattini E.W := by
    apply (map_injective E.W.subtype_injective)
    rw [hs.2]
    exact hz
  have he : IsElementaryAbelian 2 (center E.W) := by
    let : IsElementaryAbelian 2 E.V₁ := D.centralQuotientPreimage_elementary E.point
    let f : center E.W →* E.V₁ :=
      (E.W.subtype.comp (center E.W).subtype).codRestrict E.V₁ (by
        intro z
        exact hz.le (mem_map_of_mem E.W.subtype z.property))
    apply IsElementaryAbelian.of_injective f
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : E.V₁ => (v : G)) h
  have hn : center E.W ≠ ⊥ := by
    intro h
    have hz' := hz
    change (center E.W).map E.W.subtype = E.V₁ at hz'
    rw [h, Subgroup.map_bot] at hz'
    exact d.setup.point_ne_bot hz'.symm
  exact ⟨d.U_isPGroup hUT, hz, hzd, hzf, he, hn⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block
