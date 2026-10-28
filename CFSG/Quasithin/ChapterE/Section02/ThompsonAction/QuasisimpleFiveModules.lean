module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleFive
public import Theory.Representation.BinaryPermutation.FiveCentralExtension
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# The actual moved module in the quasisimple symmetric-five branch

The original B.5 section supplies an honest natural quotient of [U,O²(G)].
The five-letter class-sum section has image its A5 commutator. Residual
idempotence makes that image the whole original moved subgroup, so the
quotient map is an equivariant linear equivalence. No vanishing fixed
kernel or splitting of U is assumed.

Source: Aschbacher–Smith E.2.3(3), printed pp.216–217.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.QuasisimpleSource
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary

/-- The original moved subgroup itself is the natural A5 module. The
class-sum section and residual idempotence remove its fixed quotient kernel. -/
theorem quasisimple_five_source_natural_module
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (e : MarkedActionEquiv s.action (offenderSubgroup s.action)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)))
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) :
    let W := ⁅U,pResidual 2 G⁆
    ∃ p : G →* Equiv.Perm (Fin 5), ∃ hp : Function.Surjective p,
      ∃ hk : p.ker = centralizer (W : Set G),
      ∃ f : Additive W ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5),
        ∀ g v, f (NormalElementaryQuotient.representation W p hp hk g v) =
          BinaryPermutation.coreRepresentation (Fin 5) g (f v) := by
  let W := ⁅U,pResidual 2 G⁆
  obtain ⟨p,hp,hk,f,hf,he,hfk⟩ := quasisimple_five_source_marker T hP U hU hJ q hq hker hqs s e
  let β := NormalElementaryQuotient.representation W p hp hk
  have hm : (pResidual 2 G).map p = alternatingGroup (Fin 5) := by
    rw [map_pResidual_of_surjective 2 p hp,Equiv.Perm.twoResidual_eq_alternating]
  have hid : (⁅W,pResidual 2 G⁆ : Subgroup G) = W :=
    commutator_isPPerfect_idempotent (pResidual 2 G) U (isPPerfect_pResidual 2)
      (IsElementaryAbelian.isPGroup 2 U) le_normalizer_of_normal
  have hfull : subspaceCommutator β ⊤ (alternatingGroup (Fin 5)) = ⊤ := by
    rw [←hm,←NormalElementaryQuotient.commutatorSpace_eq W p hp hk]
    apply top_unique
    intro v _
    change (v.toMul:G) ∈ ⁅W,pResidual 2 G⁆
    exact hid.symm ▸ v.toMul.property
  have hfix (v : Additive W) (hv : f v = 0)
      (g : Equiv.Perm (Fin 5)) (hg : g ∈ alternatingGroup (Fin 5)) : β g v = v := by
    have hmem : v ∈ fixedSpace β (alternatingGroup (Fin 5)) := by
      rw [←hm,←hfk]
      exact hv
    exact hmem ⟨g,hg⟩
  obtain ⟨s₀,hs₀,_,hr⟩ := BinaryPermutation.FiveCentralExtension.exists_moved_section β f hf he hfix
  have hsurj : Function.Surjective s₀ := LinearMap.range_eq_top.mp (hr.trans hfull)
  have hi : Function.Injective f := by
    intro v w h
    obtain ⟨a,rfl⟩ := hsurj v
    obtain ⟨b,rfl⟩ := hsurj w
    rw [hs₀,hs₀] at h
    exact congrArg s₀ h
  exact ⟨p,hp,hk,LinearEquiv.ofBijective f ⟨hi,hf⟩,he⟩
end CFSG.Quasithin.ChapterE.ThompsonAction
