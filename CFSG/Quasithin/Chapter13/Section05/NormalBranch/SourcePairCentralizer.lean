module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairResidualNormal
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.TwoLayerCentralizer

/-!
# The original local Sylow centralizer is trivial

For the constructed normal pair I, its exact two-core and original action
kernel give C_I(U_H)=V₁. Normality then places [I,C_T(L₁)] in V₁, so the
proved two-layer lemma makes O²(I) centralize C_T(L₁). On the other hand,
V≤O₂(M) and the original cubic rotation force O²(I) to escape M. The
unique maximal two-local over LT therefore forces C_T(L)=1.

This discharges the local-centralizer step toward13.5.15(7), used in the
13.5.16 normal-branch recognition. The only additional source input is
Hypothesis1221 for the original L: its maximality is the earlier13.3.2
conclusion, not a consequence asserted of NaturalSetup. Theorems A and C
supply uniqueness; no kernel, pair-normality or core containment is assumed.

Source: Aschbacher–Smith13.5.15, printed p.920.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairCentralizer
open Section08.SourceCompletion
open SourcePairNormal SourcePairResidualNormal SourceOrthogonal SourceOddRotation
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
  (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

theorem pair_centralizer_eq_point (I : Subgroup G) (hIH : I≤D.H)
    (hcore : I.pCoreIn 2=D.UH) : I⊓centralizer (D.UH:Set G)=D.V₁ := by
  have hUI : D.UH≤I := hcore ▸ pCoreIn_le 2 I
  apply le_antisymm
  · intro x hx
    have hxQ : x∈D.QH := by
      rw [←h.kernel_UH_eq_QH]
      apply (h.mem_kernel_iff h.UH_le_H).mpr
      refine ⟨hIH hx.1,?_⟩
      intro u hu
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hx.2 u hu)]
      exact D.V₁.one_mem
    have hxU : x∈D.UH := hcore ▸ inf_pCoreIn_le_of_le 2 hIH ⟨hx.1,hxQ⟩
    have hc : (⟨x,hxU⟩:D.UH)∈center D.UH := by
      rw [mem_center_iff]
      intro u
      exact Subtype.ext (hx.2 u u.property)
    have hm := mem_map_of_mem D.UH.subtype hc
    rwa [center_map d h e hseed hn hU] at hm
  · exact le_inf ((h.point_lt.le.trans (le_conjugateSpanBy _ _)).trans hUI)
      (le_centralizer_iff.mp (h.UH_le_H.trans h.H_centralizes))

theorem residual_centralizes_local_sylow_centralizer (I : Subgroup G) (hIH : I≤D.H)
    (hcore : I.pCoreIn 2=D.UH) (hI : D.H≤normalizer (I:Set G)) :
    (pResidual 2 I).map I.subtype≤centralizer
      (((D.T:Subgroup G)⊓centralizer (D.L₁:Set G):Subgroup G):Set G) := by
  let C := (D.T:Subgroup G)⊓centralizer (D.L₁:Set G)
  have hCU : C≤centralizer (D.UH:Set G) :=
    inf_le_right.trans (centralizer_le ((closure_reduction h hseed hn).2.1.trans (pCoreIn_le 2 D.L₁)))
  have hIC : I≤normalizer (centralizer (D.UH:Set G):Set G) :=
    (hIH.trans (le_normalizer_conjugateSpanBy D.Vplus D.H)).trans
      (normalizer_le_normalizer_centralizer D.UH)
  have hc : ⁅I,C⁆≤D.V₁ := by
    rw [←pair_centralizer_eq_point d h e hseed hn hU I hIH hcore]
    exact le_inf
      (le_normalizer_iff_commutator_le_left.mp ((inf_le_left.trans h.T_le_H).trans hI))
      ((commutator_mono le_rfl hCU).trans (le_normalizer_iff_commutator_le_right.mp hIC))
  exact residual_centralizes_of_two_layer I C D.V₁
    (D.T.isPGroup'.to_le ((h.point_lt.le.trans h.plus_le).trans h.V_le_T))
    (hIH.trans h.H_centralizes) hc

theorem module_le_maximal_core : D.V≤M.pCoreIn 2 := by
  have hv : D.V≤D.L.pCoreIn 2 := by
    rw [←(SourceSixBlock.source13_5_15_four d h e hseed hn hU).2.1]
    exact map_mono (ChapterC.blockU_le_core (L:=D.L))
  apply hv.trans (pCoreIn_mono_of_normalizes ?_ ?_)
  · rw [d.local_normalizer]
    exact D.L.le_normalizer
  · rw [d.local_normalizer]

theorem pair_residual_not_le_maximal (v r:G) (hv:v∈D.V) (hv2:v^2=1)
    (hr:orderOf r=3) (hi:v*r*v⁻¹=r⁻¹) :
    let I:=D.V⊔D.V.map (MulAut.conj r).toMonoidHom
    ¬(pResidual 2 I).map I.subtype≤M := by
  dsimp only
  let I:=D.V⊔D.V.map (MulAut.conj r).toMonoidHom
  let R:=(pResidual 2 I).map I.subtype
  have hrI : r∈I := rotation_mem_pair v r hv hv2 (by decide:Nat.Prime 3) (by decide) hr hi
  have hV := module_le_maximal_core d h e hseed hn hU
  intro hRM
  have hIM : I≤M := by
    change D.V⊔D.V.map (MulAut.conj r).toMonoidHom≤M
    rw [pair_eq_residual_sup_module v r hv hv2 hr hi]
    exact sup_le hRM (hV.trans (pCoreIn_le 2 M))
  have hnorm : M≤normalizer (M.pCoreIn 2:Set G) :=
    M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have he := mem_normalizer_iff_map_conj_eq.mp (hnorm (hIM hrI))
  have hIC : I≤M.pCoreIn 2 := sup_le hV ((map_mono hV).trans_eq he)
  have hc := (isPGroup_pCoreIn 2 M).orderOf_coprime (by decide:Nat.Coprime 2 3) ⟨r,hIC hrI⟩
  rw [←orderOf_coe (⟨r,hIC hrI⟩:M.pCoreIn 2),hr] at hc
  exact (by decide:¬Nat.Coprime 3 3) hc

/-- Original 13.5.15 eliminates C_T(L), retaining only maximality from 13.3.2. -/
theorem sylow_local_centralizer_eq_bot
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L) :
    (D.T:Subgroup G)⊓centralizer (D.L:Set G)=⊥ := by
  let C := (D.T:Subgroup G)⊓centralizer (D.L:Set G)
  by_contra hc
  have hunique : ∀N:Subgroup G,IsMaximalTwoLocal N→D.L⊔(D.T:Subgroup G)≤N→N=M := by
    rw [d.local_normalizer]
    exact (hmax.sylow_normalized_maximal_unique d.normalizes_L
      (fun X _ _=>ChapterA.Section02.theoremA_knownSimple (G:=X))
      (fun X _ _=>ChapterA.Section02.theoremC_knownSimple (G:=X))).2
  have hLN : D.L≤normalizer (C:Set G) :=
    (le_centralizer_iff.mp (show C≤centralizer (D.L:Set G) from inf_le_right)).trans
      (centralizer_le_normalizer C)
  have hTN : (D.T:Subgroup G)≤normalizer (C:Set G) :=
    (le_inf (D.T:Subgroup G).le_normalizer
      (d.normalizes_L.trans (normalizer_le_normalizer_centralizer D.L))).trans
        inf_normalizer_le_normalizer_inf
  have hNM : normalizer (C:Set G)≤M := normalizer_le_of_unique_maximalTwoLocal
    hunique (D.T.isPGroup'.to_le inf_le_left) hc (sup_le hLN hTN)
  obtain ⟨v,hv,hvq,hv2,p,hp,hp2,r,hrH,hr,hi⟩:=exists_odd_rotation h hU
  obtain ⟨hp3,_⟩:=odd_rotation_is_cubic d h e hseed hn hU v r hv hv2 hp hp2 hr hrH hi
  have hr3 : orderOf r=3 := hr.trans hp3
  let I:=D.V⊔D.V.map (MulAut.conj r).toMonoidHom
  have hcore := SourcePairExact.core_eq_closure d h e hseed hn hU v r hv hvq hv2 hr3 hrH hi
  have hI := whole_normalizes_pair d h e hseed hn hU v r hv hv2 hr3 hrH hi
  have hcentral := residual_centralizes_local_sylow_centralizer d h e hseed hn hU I
    (pair_le h hrH) hcore hI
  have hsub : C≤(D.T:Subgroup G)⊓centralizer (D.L₁:Set G) :=
    inf_le_inf_left _ (centralizer_le ((map_subtype_le _).trans inf_le_left))
  exact pair_residual_not_le_maximal d h e hseed hn hU v r hv hv2 hr3 hi
    ((hcentral.trans (centralizer_le hsub)).trans ((centralizer_le_normalizer C).trans hNM))

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairCentralizer
end
