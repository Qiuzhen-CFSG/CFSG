module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.TorusSplitting
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.InvolutiveAction
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.FourSylow
public import CFSG.Quasithin.Chapter5.Section03ExceptionalSylowModel

/-!
# Constructing the actual exceptional linear Sylow

At original degree two, the Hall-torus split and the index bound [T:S]∣2
construct an involution t with T=S⟨t⟩ whenever S<T. The actual conjugation
action on S is put in common field coordinates, retaining both original
root planes. Transport from the unique four-element field then constructs
one isomorphism UT₃(F₄)⋊C₂ ≃ T, with S, both planes, Z(S), and a central
involution all marked by that same isomorphism.

The final alternative has no extra marking or splitting premise. It also
retains the S=T branch, already covered by the existing centralizer proof.
This supplies the Sylow geometry for §5.3.7 directly from the source action;
compatible maps of the FULL normalizers and the exceptional ambient
centralizer argument remain separate obligations.
Source: Aschbacher--Smith §5.3.7, printed pp.660--661 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Matrix.PSL3Even.UnipotentGeometry Matrix.PSL3.LinearAmbientGeometry
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include d h hH hp hm hF he hmax

/-- The same exceptional Sylow marking is constructed in the actual G,
including both original root planes and the central involution. -/
theorem Preparation.linear_four_marked_sylow
    (hn : n=2) (hne : sourceS L H ≠ (T : Subgroup G)) :
    ∃ c : Chapter5.Section03ExceptionalSylowModel.MarkedCopy G,
      c.carrier=(T : Subgroup G) ∧ c.S=sourceS L H ∧
      ((c.V₁=L.pCoreIn 2 ∧ c.V₂=(residual H).pCoreIn 2) ∨
       (c.V₁=(residual H).pCoreIn 2 ∧ c.V₂=L.pCoreIn 2)) ∧
      c.Z=centerIn (sourceS L H) ∧ orderOf c.z=2 ∧
      (T : Subgroup G) ≤ centralizer ({c.z} : Set G) := by
  obtain ⟨D,_,_,_,_,_,_,hsplit,t,ht2,ht,htS,_,hgen⟩ :=
    d.linear_exists_outer_involution h hH hp F hm hF he hne
  have hsplit' : (T : Set G)=(sourceS L H : Set G)*(zpowers t : Set G) := by
    rw [←hgen hn]
    exact hsplit
  obtain ⟨e,σ,hσ,_,hplanes,hact⟩ :=
    d.linear_mark_outer_involution h hH hp F hm hF he hmax t ht ht2 htS
  have hfour : Nat.card F=4 := by
    rw [hF,(d.linear_core_structure h hH hp F hm hF he).1,hn]
    rfl
  have htt : t^2=1 := by simpa only [ht2] using pow_orderOf_eq_one t
  obtain ⟨f,hfi,hfr,hS,hV₁,hV₂,hZ,hz⟩ := FourSylow.exists_marked_lift
    (sourceS L H) (T : Subgroup G) (sourceS_le_sylow h.sylow_normalizes hH.1.1.2)
    e hfour σ hσ t ht htt htS hsplit' hact
  let c : Chapter5.Section03ExceptionalSylowModel.MarkedCopy G := {
    carrier := (T : Subgroup G)
    equiv := (MonoidHom.ofInjective hfi).trans (MulEquiv.subgroupCongr hfr) }
  have hc : c.embedding=f := by ext u; rfl
  have hcS : c.S=sourceS L H := by
    change Matrix.PSL3Four.SylowModel.S.map c.embedding=sourceS L H
    rw [hc]
    exact hS
  have hcZ : c.Z=centerIn (sourceS L H) := by
    change (Matrix.PSL3Four.SylowModel.Z).map c.embedding=_
    rw [hc,hZ,←marked_center,←centerIn_eq_map_center]
  refine ⟨c,rfl,hcS,?_,hcZ,?_,?_⟩
  · change (Matrix.PSL3Four.SylowModel.V₁.map c.embedding=L.pCoreIn 2 ∧
        Matrix.PSL3Four.SylowModel.V₂.map c.embedding=(residual H).pCoreIn 2) ∨
        (Matrix.PSL3Four.SylowModel.V₁.map c.embedding=(residual H).pCoreIn 2 ∧
        Matrix.PSL3Four.SylowModel.V₂.map c.embedding=L.pCoreIn 2)
    rw [hc,hV₁,hV₂]
    exact hplanes
  · exact orderOf_eq_prime c.z_sq c.z_ne_one
  · intro x hx
    obtain ⟨u,hu⟩ := hfr.symm ▸ hx
    apply mem_centralizer_singleton_iff.mpr
    change x*f Matrix.PSL3Four.SylowModel.z=f Matrix.PSL3Four.SylowModel.z*x
    rw [←hu,←map_mul,←map_mul]
    apply congrArg f
    exact mem_center_iff.mp Matrix.PSL3Four.SylowModel.z_mem_center u

/-- Field four has either no outer Sylow part or the actual exceptional
marked Sylow, derived from the original prepared inputs. -/
theorem Preparation.linear_four_sylow_alternative (hn : n=2) :
    sourceS L H=(T : Subgroup G) ∨
    ∃ c : Chapter5.Section03ExceptionalSylowModel.MarkedCopy G,
      c.carrier=(T : Subgroup G) ∧ c.S=sourceS L H ∧
      ((c.V₁=L.pCoreIn 2 ∧ c.V₂=(residual H).pCoreIn 2) ∨
       (c.V₁=(residual H).pCoreIn 2 ∧ c.V₂=L.pCoreIn 2)) ∧
      c.Z=centerIn (sourceS L H) ∧ orderOf c.z=2 ∧
      (T : Subgroup G) ≤ centralizer ({c.z} : Set G) := by
  by_cases hh : sourceS L H=(T : Subgroup G)
  · exact Or.inl hh
  · exact Or.inr (d.linear_four_marked_sylow h hH hp F hm hF he hmax hn hh)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
