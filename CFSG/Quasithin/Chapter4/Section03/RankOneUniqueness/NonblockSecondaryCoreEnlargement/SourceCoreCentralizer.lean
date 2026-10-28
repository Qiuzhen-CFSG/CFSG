module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCentralizer
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceCoreFixedModule

/-!
# SourceCoreCentralizer without strict core enlargement

These are the original core-action arguments with their literal subtype maps,
using only SecondaryActionData. No strict enlargement clause is supplied.
They feed recognition of the full component-core Frattini module.
Source: Aschbacher--Smith, original 4.3.2 and 4.3.11--16, pp.617--619.
-/

public section
open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
open Representation.SL3ParabolicNatural Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
open Nonblock.RootCoordinates
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} {d : MSData c n}
namespace RootCoordinates
variable (m : RootCoordinates d) (hn : 1 < n)
include m hn

theorem core_centralizer_secondary : Q c ⊓ centralizer (secondary c : Set G) = root c := by
  apply le_antisymm
  · intro q hq
    obtain ⟨p,_,hk,he,_⟩ := d.exists_elementary_dual_lifts
    let qQ : Q c := ⟨q,hq.1⟩
    have hfix (g : SL(3,d.field.Carrier)) (hg : g ∈ pointLocalSL d.field.Carrier) :
        ((Representation.specialLinearNatural 3).dual.prod
          (Representation.specialLinearNatural 3).dual) g (p qQ).toAdd = (p qQ).toAdd := by
      obtain ⟨k,hk⟩ := m.secondaryProjection_surjective hn ⟨g,hg⟩
      have hh := he ⟨k,secondary_le_original k.property⟩ qQ qQ (by
        symm
        change (k : G)*q*(k : G)⁻¹ = q
        rw [mem_centralizer_iff.mp hq.2 k k.property,mul_inv_cancel_right])
      have ha := congrArg Subtype.val hk
      rw [m.secondaryProjection_apply] at ha
      rw [ha] at hh
      exact hh.symm
    have hz : p qQ = 1 := by
      apply Multiplicative.toAdd.injective
      exact Prod.ext
        (point_dual_fixed_zero _ (fun g hg => congrArg Prod.fst (hfix g hg)))
        (point_dual_fixed_zero _ (fun g hg => congrArg Prod.snd (hfix g hg)))
    have hu : q ∈ U c := hk.le hz
    apply (m.root_coordinates ⟨q,hu⟩).mpr
    apply point_fixed_line
    intro g hg
    obtain ⟨k,hk⟩ := m.secondaryProjection_surjective hn ⟨g,hg⟩
    have hh := m.compatible ⟨k,secondary_le_original k.property⟩ ⟨q,hu⟩ ⟨q,hu⟩ (by
      symm
      change (k : G)*q*(k : G)⁻¹ = q
      rw [mem_centralizer_iff.mp hq.2 k k.property,mul_inv_cancel_right])
    have ha := congrArg Subtype.val hk
    rw [m.secondaryProjection_apply] at ha
    rw [ha] at hh
    exact hh.symm
  · exact le_inf (d.root_le_center.trans (map_subtype_le _))
      (le_centralizer_iff.mp secondary_centralizes_root)

omit [Group G] [Finite G] m hn in
private theorem plane_fixed_eq_one {F : Type*} [Field F]
    (v : Multiplicative (Fin 2 → F))
    (hv : ∀ a : SL(2,F), Matrix.SL2.naturalAction F a v = v) : v = 1 := by
  let a : SL(2,F) := ⟨!![1,1;0,1],by simp [Matrix.det_fin_two]⟩
  let b : SL(2,F) := ⟨!![1,0;1,1],by simp [Matrix.det_fin_two]⟩
  have h₀ := congrArg (fun w : Multiplicative (Fin 2 → F) => w.toAdd 0) (hv a)
  have h₁ := congrArg (fun w : Multiplicative (Fin 2 → F) => w.toAdd 1) (hv b)
  change (a.val.mulVec v.toAdd) 0 = v.toAdd 0 at h₀
  change (b.val.mulVec v.toAdd) 1 = v.toAdd 1 at h₁
  have hz₁ : v.toAdd 1 = 0 := by
    simpa [a,Matrix.SL2.naturalAction_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using h₀
  have hz₀ : v.toAdd 0 = 0 := by
    simpa [b,Matrix.SL2.naturalAction_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using h₁
  apply Multiplicative.toAdd.injective
  ext i
  fin_cases i <;> assumption

theorem radical_centralizer_secondary
    (D : Chapter12.Section02.ChosenModule T L V) (s : SecondaryActionData c n) :
    R₂ c ⊓ centralizer (secondary c : Set G) = root c := by
  apply le_antisymm
  · intro r hr
    have hz : (SourceActionEndgame.RootCoordinates.radicalCoordinates m) hn D s ⟨r,hr.1⟩ = 1 := by
      apply plane_fixed_eq_one
      intro a
      obtain ⟨k,rfl⟩ := (SourceActionEndgame.RootCoordinates.secondaryLinear_surjective m) hn a
      symm
      apply (SourceActionEndgame.RootCoordinates.radicalCoordinates_conjugate m) hn D s k ⟨r,hr.1⟩ ⟨r,hr.1⟩
      symm
      change (k : G)*r*(k : G)⁻¹ = r
      rw [mem_centralizer_iff.mp hr.2 k k.property,mul_inv_cancel_right]
    have hq : r ∈ Q c := ((SourceActionEndgame.RootCoordinates.radicalCoordinates_ker m) hn D s).le hz
    exact ((SourceActionEndgame.RootCoordinates.core_centralizer_secondary m) hn).le ⟨hq,hr.2⟩
  · exact le_inf ((d.root_le_center.trans (map_subtype_le _)).trans (core_le_radical c))
      (le_centralizer_iff.mp secondary_centralizes_root)
end RootCoordinates
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
