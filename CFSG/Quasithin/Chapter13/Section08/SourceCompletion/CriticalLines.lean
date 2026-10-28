module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.EndpointKernels

/-!
# Noncentrality and disjoint lines at the original critical pair

The original two-core fixes the first ball. Thus the F.9 action-kernel
equality makes centralization of U-gamma modulo A1 contradict criticality.
Intersecting-conjugate commutativity then separates the two marked lines,
and the two defining commutator bounds make the denominators centralize.
The sole additional input for the last two conclusions is precisely 13.8.3,
produced from the earlier abelian closure and natural transitivity.

Source: Aschbacher--Smith, F.9.13(5--7), printed p.322, and 13.8.3--4.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open CriticalGeometry
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
open ReversedSourceData
variable {G : Type*} [Group G] [Finite G]

theorem f9_core_le_firstKernel (D:ChapterF.Section09.Setup G) (h:D.Hypothesis) :
    D.QH≤firstKernel D.L (D.T:Subgroup G) D.H (base _ _ _ true) := by
  change D.QH≤vertexGroup _ _ _ (base _ _ _ true)⊓_
  refine le_inf ?_ (le_iInf fun w=>le_iInf fun hw=>?_)
  · rw [vertexGroup_base]
    exact pCoreIn_le 2 D.H
  · obtain ⟨a,ha⟩:=exists_neighbor_transporter hw
    rw [←ha,vertexGroup_smul,vertexGroup_base]
    have hm:=map_mono (f:=(MulAut.conj (a:G)).toMonoidHom)
      (h.QH_le_T.trans (show (D.T:Subgroup G)≤D.L⊔(D.T:Subgroup G) from le_sup_right))
    have he:D.QH.map (MulAut.conj (a:G)).toMonoidHom=D.QH :=
      mem_normalizer_iff_map_conj_eq.mp (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D:=D) a.property)
    rwa [he] at hm

theorem f9_Qgamma_le_firstKernel (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (c:CriticalPair D.L (D.T:Subgroup G) D.H D.V) :
    c.Qgamma≤firstKernel D.L (D.T:Subgroup G) D.H c.gamma := by
  rw [←c.gb_one,firstKernel_smul]
  exact map_mono (f9_core_le_firstKernel D h)

theorem f9_commutator_not_le_Aone (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (c:CriticalPair D.L (D.T:Subgroup G) D.H D.V) (hb:3≤c.path.length) :
    ¬⁅c.Ugamma D.Vplus,D.V⁆≤c.Aone D.V₁ := by
  intro hc
  have hV : D.V≤D.H.map (MulAut.conj (c.gb:G)).toMonoidHom := by
    rw [←c.vertexGroup_gamma]
    exact (le_conjugateSpanBy D.V D.H).trans (f9_endpoint_spans D h c hb).1
  have hback : D.V.map (MulAut.conj (c.gb:G)⁻¹).toMonoidHom≤D.H := by
    have hh:=map_mono (f:=(MulAut.conj (c.gb:G)⁻¹).toMonoidHom) hV
    rwa [conjugate_inverse_cancel] at hh
  have hm:=map_mono (f:=(MulAut.conj (c.gb:G)⁻¹).toMonoidHom) hc
  rw [map_commutator,CriticalPair.Ugamma,CriticalPair.Aone,conjugate_inverse_cancel,conjugate_inverse_cancel] at hm
  have hQ : D.V.map (MulAut.conj (c.gb:G)⁻¹).toMonoidHom≤D.QH := by
    have he:=f9_commutatorPreimage_eq D h _ hback
    exact ((le_commutatorPreimage le_rfl (by rwa [commutator_comm])).trans he.le).trans inf_le_right
  have hv:=map_mono (f:=(MulAut.conj (c.gb:G)).toMonoidHom) hQ
  have hcancel: (D.V.map (MulAut.conj (c.gb:G)⁻¹).toMonoidHom).map (MulAut.conj (c.gb:G)).toMonoidHom=D.V := by
    simpa only [inv_inv] using conjugate_inverse_cancel (c.gb:G)⁻¹ D.V
  rw [hcancel] at hv
  exact c.critical (hv.trans (f9_Qgamma_le_firstKernel D h c))

theorem f9_lines_disjoint (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (c:CriticalPair D.L (D.T:Subgroup G) D.H D.V) (hb:3≤c.path.length)
    (hcomm:∀g:G,D.V⊓D.V.map (MulAut.conj g).toMonoidHom≠⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥) :
    D.V₁⊓c.Aone D.V₁=⊥ := by
  by_contra hn
  have hc : c.Ugamma D.Vplus≤centralizer (D.V:Set G) := by
    rw [CriticalPair.Ugamma,Source.UH,conjugateSpanBy_eq_iSup_conj,Subgroup.map_iSup]
    refine iSup_le fun a=>?_
    have hfix:D.V₁.map (MulAut.conj (a:G)).toMonoidHom=D.V₁ :=
      mem_normalizer_iff_map_conj_eq.mp ((h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) a.property)
    have hpoint:c.Aone D.V₁≤(D.V.map (MulAut.conj (a:G)).toMonoidHom).map (MulAut.conj (c.gb:G)).toMonoidHom := by
      change D.V₁.map (MulAut.conj (c.gb:G)).toMonoidHom≤_
      rw [←hfix]
      exact map_mono (map_mono (h.point_lt.le.trans h.plus_le))
    have he:(D.V.map (MulAut.conj (a:G)).toMonoidHom).map (MulAut.conj (c.gb:G)).toMonoidHom=
        D.V.map (MulAut.conj ((c.gb:G)*(a:G))).toMonoidHom := by
      rw [map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rw [he] at hpoint
    have hinter:D.V⊓D.V.map (MulAut.conj ((c.gb:G)*(a:G))).toMonoidHom≠⊥ := by
      intro hz
      exact hn (eq_bot_iff.mpr ((inf_le_inf (h.point_lt.le.trans h.plus_le) hpoint).trans hz.le))
    have hC:=le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (hcomm _ hinter))
    apply le_trans (map_mono (map_mono h.plus_le))
    rw [he]
    exact hC
  exact f9_commutator_not_le_Aone D h c hb
    ((commutator_eq_bot_iff_le_centralizer.mpr hc).le.trans bot_le)

theorem f9_denominators_centralize (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (c:CriticalPair D.L (D.T:Subgroup G) D.H D.V) (hb:3≤c.path.length)
    (hcomm:∀g:G,D.V⊓D.V.map (MulAut.conj g).toMonoidHom≠⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥) :
    ⁅Source.DH D.UH (c.Ugamma D.Vplus) (c.Aone D.V₁),
      Source.Dgamma (c.Ugamma D.Vplus) D.UH D.V₁⁆=⊥ := by
  have hends:=f9_endpoint_spans D h c hb
  have huv:D.UH≤Source.VH D.H D.V:=conjugateSpanBy_mono h.plus_le le_rfl
  have hZ:D.H≤normalizer (D.V₁:Set G):=
    h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hγZ:c.Ugamma D.Vplus≤normalizer (D.V₁:Set G):=
    ((map_mono huv).trans hends.2).trans hZ
  have hUA:D.UH≤normalizer (c.Aone D.V₁:Set G) := by
    apply le_trans (huv.trans hends.1)
    rw [c.vertexGroup_gamma,CriticalPair.Aone,←map_equiv_normalizer_eq]
    exact map_mono hZ
  have h1 : ⁅Source.DH D.UH (c.Ugamma D.Vplus) (c.Aone D.V₁),
      Source.Dgamma (c.Ugamma D.Vplus) D.UH D.V₁⁆≤c.Aone D.V₁ :=
    (commutator_mono le_rfl (commutatorPreimage_le _ _ _)).trans
      (commutator_commutatorPreimage_le _ _ _ hUA)
  have h2 : ⁅Source.DH D.UH (c.Ugamma D.Vplus) (c.Aone D.V₁),
      Source.Dgamma (c.Ugamma D.Vplus) D.UH D.V₁⁆≤D.V₁ := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl (commutatorPreimage_le _ _ _)).trans
      (commutator_commutatorPreimage_le _ _ _ hγZ)
  exact eq_bot_iff.mpr ((le_inf h2 h1).trans (f9_lines_disjoint D h c hb hcomm).le)

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
