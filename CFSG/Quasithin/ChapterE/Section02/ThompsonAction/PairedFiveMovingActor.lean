module
public import Theory.GroupTheory.SylowNormalJoinIntersection
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairResidualControl
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveBaumannDisplacement
/-!
# A surviving transvection on the original invariant submodule

The two actual residual factors generate O²(G) and are normal there.
Their Sylow intersections therefore generate the original residual Sylow
intersection. If that intersection moves W, one factor actor moves W.
The paired Baumann-center displacement calculation puts its entire
nonzero displacement in one line of W, giving an actual transvection.

Only W's placement, Sylow invariance and nontrivial residual action are
required. No identification of the residual factors with an independently
selected component pair is needed for actor selection.
Source: Aschbacher--Smith E.2.3 and 10.2.1, printed pp.216--217,743.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

theorem paired_residual_sylow_factors_generate
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
    let K₁ := factorResidual q Y d.first
    let K₂ := factorResidual q Y (SourceTwoFactorCase.second d)
    (T : Subgroup G) ⊓ pResidual 2 G =
      ((T : Subgroup G) ⊓ K₁) ⊔ ((T : Subgroup G) ⊓ K₂) := by
  let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
  have hgen := paired_residual_factors_generate T hP U hU hJ q hq hker d
  let := d.product.first_normal
  let := d.product.second_normal
  have hY (A : Subgroup Y) : factorResidual q Y A ≤ Y.comap q :=
    (map_subtype_le _).trans (fun _ hx => map_subtype_le A hx)
  have hR : (pResidual 2 G).map q ≤ Y := by
    apply map_le_iff_le_comap.mpr
    rw [←hgen]
    exact sup_le (hY d.first) (hY d.second)
  let := factorResidual_normal_in_residual q Y d.first hR
  let := factorResidual_normal_in_residual q Y d.second hR
  exact T.inf_sup_eq_sup_inf_relative (pResidual 2 G) _ _
    (hgen ▸ le_sup_left) (hgen ▸ le_sup_right) hgen

end CFSG.Quasithin.ChapterE.ThompsonAction

open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction BinaryPermutation
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

theorem paired_baumann_moving_actor
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first)
    (W : Subgroup G) (hW : W ≤ omegaOneCenterAmbient (baumann (T : Subgroup G)))
    (hn : (T : Subgroup G) ≤ normalizer (W : Set G))
    (hm : ¬ (T : Subgroup G) ⊓ pResidual 2 G ≤ centralizer (W : Set G)) :
    ∃ g ∈ (T : Subgroup G) ⊓ pResidual 2 G, ∃ v ∈ W, v ≠ 1 ∧
      (∀ x ∈ W, ⁅g,x⁆ = 1 ∨ ⁅g,x⁆ = v) ∧ ∃ x ∈ W, ⁅g,x⁆ = v := by
  let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
  let A := factorResidual q Y d.first
  let B := factorResidual q Y d.second
  have hg := paired_residual_factors_generate T hP U hU hJ q hq hker d
  have hs := paired_residual_sylow_factors_generate T hP U hU hJ q hq hker d
  obtain ⟨v₁,v₂,_,hv₁,_,hv₂,h₁,h₂⟩ :=
    paired_symmetric_baumann_center_displacement T hP U hU hJ q hq hker d c hexchange
  have hchoose : ∃ K ∈ ({A,B} : Set (Subgroup G)), ∃ v : G, v ≠ 1 ∧
      (∀ g ∈ (T : Subgroup G) ⊓ K, ∀ x ∈ W, ⁅g,x⁆ = 1 ∨ ⁅g,x⁆ = v) ∧
      ¬ (T : Subgroup G) ⊓ K ≤ centralizer (W : Set G) := by
    by_cases ha : (T : Subgroup G) ⊓ A ≤ centralizer (W : Set G)
    · refine ⟨B,Set.mem_insert_of_mem _ (Set.mem_singleton _),v₂,hv₂,?_,?_⟩
      · exact fun g hg x hx => h₂ g hg x (hW hx)
      · intro hb
        exact hm (hs ▸ sup_le ha hb)
    · exact ⟨A,Set.mem_insert _ _,v₁,hv₁,(fun g hg x hx => h₁ g hg x (hW hx)),ha⟩
  obtain ⟨K,hK,v,hv,hline,hnot⟩ := hchoose
  obtain ⟨g,hgK,hgc⟩ := SetLike.not_le_iff_exists.mp hnot
  have hmove : ∃ x ∈ W, ⁅g,x⁆ ≠ 1 := by
    by_contra! hh
    apply hgc
    intro x hx
    exact (commutatorElement_eq_one_iff_mul_comm.mp (hh x hx)).symm
  obtain ⟨x,hx,hgx⟩ := hmove
  have he := (hline g hgK x hx).resolve_left hgx
  have hvW : v ∈ W := by
    rw [←he]
    exact W.mul_mem ((mem_normalizer_iff.mp (hn hgK.1) x).mp hx) (W.inv_mem hx)
  refine ⟨g,⟨hgK.1,?_⟩,v,hvW,hv,hline g hgK,x,hx,he⟩
  rcases hK with rfl | hK
  · exact hg ▸ mem_sup_left hgK.2
  · have he : K = B := hK
    subst K
    exact hg ▸ mem_sup_right hgK.2
end CFSG.Quasithin.ChapterE.ThompsonAction

