module
public import Theory.SpecificGroups.BinaryFiveAffine.FivePointModule
public import CFSG.Quasithin.Chapter13.Section09.NormalizerStructure.NaturalPoints
/-!
# The source's literal five-point binary module

Use the original five conjugates of z and their full-product relation to
identify B with the even permutation core. The original marked t is the
first pair product, and the original normalizer conjugation is exactly the
permutation action. No abstract natural-module recognition is assumed.
Source: Aschbacher–Smith 13.9.9–10, printed p.973.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

/-- The actual B and normalizer action identify with the binary five-point model. -/
theorem exists_binary_five_module {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    ∃(eB:BinaryFiveAffine.V≃*m.B)
      (a:normalizer (m.B:Set G)→*BinaryFiveAffine.S),
      Function.Surjective a ∧ a.ker=m.B.subgroupOf (normalizer (m.B:Set G)) ∧
      ((eB BinaryFiveAffine.pair01):G)=m.t ∧
      ∀g x, (eB (BinaryFiveAffine.action (a g) x):G)=
        (g:G)*(eB x:G)*(g:G)⁻¹ := by
  obtain ⟨e,ht,hz,hword⟩ := m.exists_natural_five_points hG
  let v:Fin 5→m.B := fun i=>(e i).val
  let eB := BinaryFiveAffine.fivePointEquiv v (m.card_elementaryGroup false false) hword
  let a := e.symm.permCongrHom.toMonoidHom.comp m.normalizerOrbitAction
  have ha : Function.Surjective a := e.symm.permCongrHom.surjective.comp
    (m.normalizerOrbitAction_surjective hG)
  have hk : a.ker=m.B.subgroupOf (normalizer (m.B:Set G)) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.symm.permCongrHom.injective,
      m.normalizerOrbitAction_kernel hG]
  refine ⟨eB,a,ha,hk,?_,?_⟩
  · change ((BinaryFiveAffine.fivePointEquiv v _ hword BinaryFiveAffine.pair01):G)=m.t
    rw [BinaryFiveAffine.fivePointEquiv_pair01]
    exact ht.symm
  · intro g x
    let α := m.B.normalizerMonoidHom g
    have hv (i:Fin 5) : α (v i)=v (a g i) := by
      apply Subtype.ext
      change (g:G)*((e i).val:G)*(g:G)⁻¹=((e (a g i)).val:G)
      have he : e (a g i)=m.normalizerOrbitAction g (e i) := by
        change e (e.symm (m.normalizerOrbitAction g (e i)))=_
        exact e.apply_symm_apply _
      rw [he,m.normalizerOrbitAction_apply_coe]
    exact congrArg Subtype.val (BinaryFiveAffine.fivePointEquiv_equivariant v (m.card_elementaryGroup false false) hword α (a g) hv x)

end CFSG.Quasithin.Chapter13.Section09.Marking
