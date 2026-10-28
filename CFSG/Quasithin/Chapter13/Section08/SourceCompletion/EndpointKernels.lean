module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.EndpointContainment

/-!
# The actual critical denominators are two-core intersections

F.9.2 identifies the action kernel on UH/V1 with the original two-core.
Restricting that kernel and transporting it by the same endpoint conjugator
identifies both literal commutator-preimage denominators. The endpoint
containments are derived from the critical path, not assumed.

Source: Aschbacher--Smith, F.9.2(3), F.9.12--13 and their use in 13.8.4.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open CriticalGeometry
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
variable {G : Type*} [Group G] [Finite G]

theorem f9_commutatorPreimage_eq (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (A:Subgroup G) (hA:A≤D.H) : commutatorPreimage A D.UH D.V₁=A⊓D.QH := by
  have hn : A≤normalizer (D.V₁:Set G) :=
    hA.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  apply le_antisymm
  · refine le_inf (commutatorPreimage_le _ _ _) ?_
    rw [←h.kernel_UH_eq_QH]
    have hc:=commutator_commutatorPreimage_le A D.UH D.V₁ hn
    rw [commutator_comm] at hc
    intro x hx
    exact (h.mem_kernel_iff h.UH_le_H).mpr
      ⟨hA (commutatorPreimage_le _ _ _ hx),fun u hu=>hc (commutator_mem_commutator hu hx)⟩
  · apply le_commutatorPreimage inf_le_left
    rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_right).trans h.commutator_UH_QH_le_point

theorem f9_endpoint_kernels (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (c:CriticalPair D.L (D.T:Subgroup G) D.H D.V) (hb:3≤c.path.length) :
    Source.DH D.UH (c.Ugamma D.Vplus) (c.Aone D.V₁)=D.UH⊓c.Qgamma ∧
    Source.Dgamma (c.Ugamma D.Vplus) D.UH D.V₁=c.Ugamma D.Vplus⊓D.QH := by
  have huv : D.UH≤Source.VH D.H D.V := conjugateSpanBy_mono h.plus_le le_rfl
  have hends:=f9_endpoint_spans D h c hb
  have hUH : D.UH≤D.H.map (MulAut.conj (c.gb:G)).toMonoidHom := by
    rw [←c.vertexGroup_gamma]
    exact huv.trans hends.1
  have hback : D.UH.map (MulAut.conj (c.gb:G)⁻¹).toMonoidHom≤D.H := by
    have hm:=map_mono (f:=(MulAut.conj (c.gb:G)⁻¹).toMonoidHom) hUH
    rwa [conjugate_inverse_cancel] at hm
  have hUγ : c.Ugamma D.Vplus≤D.H := (map_mono huv).trans hends.2
  constructor
  · have he:=congrArg (fun A:Subgroup G=>A.map (MulAut.conj (c.gb:G)).toMonoidHom)
      (f9_commutatorPreimage_eq D h (D.UH.map (MulAut.conj (c.gb:G)⁻¹).toMonoidHom) hback)
    have hn : D.UH.map (MulAut.conj (c.gb:G)⁻¹).toMonoidHom≤normalizer (D.V₁:Set G) :=
      hback.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    rw [map_commutatorPreimage_equiv _ _ _ _ hn,map_inf _ _ _ (MulAut.conj (c.gb:G)).injective] at he
    have hcancel : (D.UH.map (MulAut.conj (c.gb:G)⁻¹).toMonoidHom).map (MulAut.conj (c.gb:G)).toMonoidHom=D.UH := by
      simpa only [inv_inv] using conjugate_inverse_cancel (c.gb:G)⁻¹ D.UH
    rw [hcancel] at he
    exact he
  · exact f9_commutatorPreimage_eq D h (c.Ugamma D.Vplus) hUγ

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
