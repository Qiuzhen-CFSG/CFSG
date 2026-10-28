module

public import Theory.SpecificGroups.PSL3.OddPrimeGraphExtension.GraphLargeStructure.Action
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# The marked projective linear graph involution in the original group

The proved odd-prime automorphism theorem identifies every proper Sylow-two
extension of a simple PSL₃ generalized Fitting subgroup with the actual
inner-and-graph subgroup. Pulling back its canonical graph element yields
an outside involution, generation with the original component, and the
literal inverse-transpose action under a component isomorphism.

Source: Aschbacher--Smith F.6.18(11), pp.309--310; GLS3 2.5.12 and 2.7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open Matrix.PSL3.OddPrimeGraphExtension
open GraphLargeStructure

variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
  [IsSimpleGroup (generalizedFitting G)]

theorem exists_projective_linear_graph_involution (T : Sylow 2 G) (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hproper : generalizedFitting G ≠ ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    (e : generalizedFitting G ≃* PSL(3,F)) :
    ∃ t : G, orderOf t = 2 ∧ t ∉ generalizedFitting G ∧
      generalizedFitting G ⊔ zpowers t = ⊤ ∧
      ∃ j : generalizedFitting G ≃* PSL(3,F),
        ∀ x : generalizedFitting G,
          j (MulAut.conjNormal t x) = Matrix.PSL3.OuterSolvable.graph F (j x) := by
  let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  obtain ⟨a⟩ := exists_mulEquiv_graphExtension T hgen hproper hp ho hF e
  let b : graphExtension F := ⟨Matrix.PSL3.OuterSolvable.graph F,
    (show zpowers (Matrix.PSL3.OuterSolvable.graph F) ≤ graphExtension F from le_sup_right) (mem_zpowers _)⟩
  let t := a.symm b
  have hb2 : b ^ 2 = 1 := Subtype.ext (Matrix.PSL3.OuterSolvable.graph_sq F)
  have hmap : (generalizedFitting G).map a.toMonoidHom = innerPart F :=
    (map_generalizedFitting_equiv a).trans (generalizedFitting_eq_innerPart F)
  let j0 : generalizedFitting G ≃* innerPart F :=
    (a.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
  let j := j0.trans (innerPartEquiv F).symm
  have hbgen : innerPart F ⊔ zpowers b = ⊤ := by
    apply (Subgroup.map_injective (graphExtension F).subtype_injective)
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    change (innerPart F).map (graphExtension F).subtype ⊔
      zpowers (Matrix.PSL3.OuterSolvable.graph F) = (⊤ : Subgroup (graphExtension F)).map _
    rw [innerPart, map_subgroupOf_eq_of_le (show MulAut.innerSubgroup PSL(3,F) ≤ graphExtension F from le_sup_left)]
    rw [← MonoidHom.range_eq_map, range_subtype]
    rfl
  have htgen : generalizedFitting G ⊔ zpowers t = ⊤ := by
    apply (Subgroup.map_injective (f := a.toMonoidHom) a.injective)
    rw [Subgroup.map_sup, hmap, MonoidHom.map_zpowers]
    change innerPart F ⊔ zpowers (a (a.symm b)) = (⊤ : Subgroup G).map a.toMonoidHom
    rw [a.apply_symm_apply, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr a.surjective]
    exact hbgen
  have htout : t ∉ generalizedFitting G := by
    intro ht
    have hz := zpowers_le.mpr ht
    rw [sup_eq_left.mpr hz] at htgen
    exact hproper htgen
  have ht2 : t ^ 2 = 1 := a.injective (by simpa only [map_pow, map_one, t, a.apply_symm_apply] using hb2)
  have htorder : orderOf t = 2 := orderOf_eq_prime_iff.mpr ⟨ht2, fun h => htout (h ▸ one_mem _)⟩
  refine ⟨t, htorder, htout, htgen, j, ?_⟩
  intro x
  have hj0 : j0 (MulAut.conjNormal t x) = MulAut.conjNormal b (j0 x) := by
    apply Subtype.ext
    change a (t * (x : G) * t⁻¹) = b * a x * b⁻¹
    simp [t]
  have ha := congrArg (fun z : MulAut PSL(3,F) => z (j x)) (innerPart_conj_action F b)
  change (innerPartEquiv F).symm (MulAut.conjNormal b ((innerPartEquiv F) (j x))) = _ at ha
  change (innerPartEquiv F).symm (j0 (MulAut.conjNormal t x)) = _
  rw [hj0]
  simpa only [j, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] using ha

end CFSG.Quasithin.ChapterF.SourceAssembly
