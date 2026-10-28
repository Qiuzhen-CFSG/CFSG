module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.Characteristic
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.BaerSuzukiLocal
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Kernels
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.ActionModel.Quotient

/-!
# The two-conjugate argument for the pure-point core

Once the point core is self-centralizing, the marked natural summand and
its dual polar hyperplane lie in that core. For two conjugates of the whole
module, the conjugate hyperplane and point line form a central two-group.
The action displacements lie in that group, so the two-residual fixes the
moving subgroup. Its centralizer identity makes the residual fix the whole
module. Each conjugate pair is consequently a two-group, and relative
Baer--Suzuki places the original module in the full point-centralizer core.

All conjugates and cores retain their actual embeddings in G. The
characteristic-two premise is the remaining source component exclusion.
Source: Aschbacher--Smith, 12.1.6, printed pp.791--792.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

private theorem pgroup_le_core_of_residual_centralizes
    {G : Type*} [Group G] [Finite G] (A : Subgroup G) (hA : IsPGroup 2 A)
    (hc : pResidual 2 G ≤ centralizer (A : Set G)) : A ≤ pCore 2 G := by
  obtain ⟨P,hAP⟩ := hA.exists_le_sylow
  let X := componentOrbit A (P : Subgroup G)
  have hXP : X ≤ (P : Subgroup G) := (componentOrbit_le_sup A _).trans (sup_le hAP le_rfl)
  have hXC : X ≤ centralizer (pResidual 2 G : Set G) := by
    apply iSup_le
    intro g
    exact (map_mono (le_centralizer_iff.mp hc)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (show (g : G) ∈
        normalizer (centralizer (pResidual 2 G : Set G) : Set G) by
        rw [normalizer_eq_top]; trivial))
  have hn : X.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← pResidual_sup_sylow_eq_top P]
    exact sup_le ((le_centralizer_iff.mp hXC).trans (Subgroup.centralizer_le_normalizer _))
      (le_normalizer_componentOrbit A (P : Subgroup G))
  exact (le_componentOrbit A (P : Subgroup G)).trans (le_sSup ⟨hn,P.isPGroup'.to_le hXP⟩)

private theorem pair_isPGroup_of_residual_centralizes
    {G : Type*} [Group G] [Finite G] (A B : Subgroup G)
    (hA : IsPGroup 2 A) (hB : IsPGroup 2 B)
    (hc : (pResidual 2 (A ⊔ B : Subgroup G)).map (A ⊔ B).subtype ≤
      centralizer (A : Set G)) : IsPGroup 2 (A ⊔ B : Subgroup G) := by
  let I := A ⊔ B
  have hAI : A ≤ I := le_sup_left
  have hBI : B ≤ I := le_sup_right
  have hR : pResidual 2 I ≤ centralizer (A.subgroupOf I : Set I) := by
    intro r hr a ha
    exact Subtype.ext (hc (mem_map_of_mem I.subtype hr) a ha)
  have hcore := pgroup_le_core_of_residual_centralizes (A.subgroupOf I) hA.comap_subtype hR
  have hgen : A.subgroupOf I ⊔ B.subgroupOf I = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hAI, map_subgroupOf_eq_of_le hBI,
      ← MonoidHom.range_eq_map, I.range_subtype]
  have hp := (pCore_isPGroup (p := 2) (G := I)).to_sup_of_normal_left'
    hB.comap_subtype (show B.subgroupOf I ≤ normalizer (pCore 2 I : Set I) by
      rw [normalizer_eq_top]; exact le_top)
  have ht : pCore 2 I ⊔ B.subgroupOf I = ⊤ := top_unique (by
    rw [← hgen]; exact sup_le_sup_right hcore _)
  change IsPGroup 2 (pCore 2 I ⊔ B.subgroupOf I : Subgroup I) at hp
  rw [ht] at hp
  exact hp.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup I) ≃* I)

private theorem orbit_le_core_of_sections
    {G : Type*} [Group G] [Finite G] (H W A E Q Z : Subgroup G)
    (hWH : W ≤ H) (hW : IsPGroup 2 W) (hWW : W ≤ centralizer (W : Set G))
    (hAW : A ≤ W) (hEW : E ≤ W) (hZW : Z ≤ W)
    (hAQ : A ≤ Q) (hEQ : E ≤ Q) (hEC : E ≤ centralizer (Q : Set G))
    (hHQ : H ≤ normalizer (Q : Set G)) (hHZ : H ≤ centralizer (Z : Set G))
    (hWQ : ⁅W,Q⁆ ≤ Z ⊔ E)
    (hcent : centralizer ((A ⊔ E : Subgroup G) : Set G) = centralizer (W : Set G)) :
    W ≤ H.pCoreIn 2 := by
  apply le_pCoreIn_of_conjugate_sup_isPGroup H W hWH hW
  intro g hg
  let f := (MulAut.conj g).toMonoidHom
  let Wg := W.map f
  let Eg := E.map f
  let U := A ⊔ E
  let I := W ⊔ Wg
  let F := Z ⊔ Eg
  have hQ : Q.map f = Q := mem_normalizer_iff_map_conj_eq.mp (hHQ hg)
  have hZ : Z.map f = Z := mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.centralizer_le_normalizer _ (hHZ hg))
  have hUW : U ≤ W := sup_le hAW hEW
  have hUQ : U ≤ Q := sup_le hAQ hEQ
  have hEgQ : Eg ≤ centralizer (Q : Set G) := by
    have hh := (map_mono (f := f) hEC).trans (map_centralizer_le_centralizer_image _ f)
    change E.map f ≤ centralizer (Q.map f : Set G) at hh
    rwa [hQ] at hh
  have hEgW : Eg ≤ centralizer (W : Set G) := by
    rw [← hcent]
    exact hEgQ.trans (centralizer_le hUQ)
  have hEgWg : Eg ≤ centralizer (Wg : Set G) :=
    (map_mono (f := f) (hEW.trans hWW)).trans (map_centralizer_le_centralizer_image _ f)
  have hIH : I ≤ H := sup_le hWH ((map_mono hWH).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer hg)))
  have hIF : I ≤ centralizer (F : Set G) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp (hIH.trans hHZ))
      (le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp hEgW)
        (le_centralizer_iff.mp hEgWg)))
  have hcomm : ⁅I,U⁆ ≤ F := by
    have hb : ⁅Wg,Q⁆ ≤ F := by
      have hm := map_mono (f := f) hWQ
      rwa [map_commutator, Subgroup.map_sup, hQ, hZ] at hm
    have hWU : ⁅W,U⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (hWW.trans (centralizer_le hUW))
    have hle : I ≤ commutatorPreimage I U F := sup_le
      (le_commutatorPreimage le_sup_left (by rw [hWU]; exact bot_le))
      (le_commutatorPreimage le_sup_right ((commutator_mono le_rfl hUQ).trans hb))
    exact (commutator_mono hle le_rfl).trans
      (commutator_commutatorPreimage_le I U F (hIF.trans (Subgroup.centralizer_le_normalizer _)))
  have hFWg : F ≤ Wg := sup_le
    (by rw [← hZ]; exact map_mono hZW) (map_mono hEW)
  have hr := residual_centralizes_of_two_layer I U F ((hW.map f).to_le hFWg) hIF hcomm
  change _ ≤ centralizer ((A ⊔ E : Subgroup G) : Set G) at hr
  rw [hcent] at hr
  exact pair_isPGroup_of_residual_centralizes W Wg hW (hW.map f) hr

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

omit [Finite G] in
private theorem natural_sup_dual :
    B.naturalSummand ⊔ B.dualSummand = componentOrbit V (T : Subgroup G) := by
  apply le_antisymm (sup_le B.naturalSummand_le B.dualSummand_le)
  intro x hx
  let v : componentOrbit V (T : Subgroup G) := ⟨x,hx⟩
  have ht : Additive.ofMul v ∈ B.naturalSpace ⊔ B.dualSpace := by
    rw [B.natural_dual_complement.sup_eq_top]; trivial
  obtain ⟨a,ha,b,hb,he⟩ := Submodule.mem_sup.mp ht
  have he' : (a.toMul : G) * (b.toMul : G) = x := congrArg (fun c => (c.toMul : G)) he
  rw [← he']
  exact (B.naturalSummand ⊔ B.dualSummand).mul_mem
    ((le_sup_left : B.naturalSummand ≤ B.naturalSummand ⊔ B.dualSummand) (show (a.toMul : G) ∈ B.naturalSummand from ⟨a.toMul,ha,rfl⟩))
    ((le_sup_right : B.dualSummand ≤ B.naturalSummand ⊔ B.dualSummand) (show (b.toMul : G) ∈ B.dualSummand from ⟨b.toMul,hb,rfl⟩))

namespace SourceModel
variable (S : B.SourceModel)

include S in
/-- The two-conjugate argument of 12.1.6 places the whole doubled module
in the literal point core once the component exclusion gives characteristic two. -/
theorem pure_orbit_le_core_of_characteristicTwo
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (hs : B.PurePointSylows) (hns : B.NonsingularCentralizers)
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0)
    (hc : centralizer (pCore 2 (centralizer ({(w : G)} : Set G)) : Set
        (centralizer ({(w : G)} : Set G))) ≤ pCore 2 (centralizer ({(w : G)} : Set G))) :
    componentOrbit V (T : Subgroup G) ≤ B.purePointCore w := by
  let W := componentOrbit V (T : Subgroup G)
  let H := centralizer ({(w : G)} : Set G)
  let Q := B.purePointCore w
  let Z := zpowers (w : G)
  let E := S.pureDualHyperplane w hp
  have hWW : W ≤ centralizer (W : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hWH : W ≤ H := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (hWW hx w w.property).symm
  have hEW : E ≤ W := (S.pureDualHyperplane_le_dualSummand w hp).trans B.dualSummand_le
  have hZW : Z ≤ W := zpowers_le.mpr w.property
  have hHQ : H ≤ normalizer (Q : Set G) := by
    have hn := (pCore 2 H).le_normalizer_map H.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, H.range_subtype] at hn
    exact hn
  have hHZ : H ≤ centralizer (Z : Set G) := by
    change centralizer ({(w : G)} : Set G) ≤ centralizer (zpowers (w : G) : Set G)
    rw [zpowers_eq_closure, centralizer_closure]
  have hE := S.pure_dualHyperplane_le_core_of_characteristicTwo hNM hs w hw hp hc
  have hcomm : ⁅W,Q⁆ ≤ Z ⊔ E := by
    have hnormal : W ≤ normalizer ((Z ⊔ E : Subgroup G) : Set G) :=
      (hWW.trans (centralizer_le (show Z ⊔ E ≤ W from sup_le hZW hEW))).trans (Subgroup.centralizer_le_normalizer _)
    have hle : W ≤ commutatorPreimage W Q (Z ⊔ E) := by
      apply (natural_sup_dual (B := B)).ge.trans
      exact sup_le
        (le_commutatorPreimage B.naturalSummand_le
          ((S.purePointCore_natural_commutator hNM hs w hw hp).trans le_sup_left))
        (le_commutatorPreimage B.dualSummand_le
          ((S.purePointCore_dual_commutator hNM hs w hw hp).trans le_sup_right))
    exact (commutator_mono hle le_rfl).trans
      (commutator_commutatorPreimage_le W Q (Z ⊔ E) hnormal)
  exact orbit_le_core_of_sections H W B.naturalSummand E Q Z hWH
    (IsElementaryAbelian.isPGroup 2 W) hWW B.naturalSummand_le hEW hZW
    (S.pure_natural_le_core_of_characteristicTwo hNM hs w hw hp hc)
    (hE.trans inf_le_left) (hE.trans inf_le_right) hHQ hHZ hcomm
    (S.pure_moving_centralizer hNM hns (S.summandCentralizers hNM) w hw hp)

end SourceModel
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
