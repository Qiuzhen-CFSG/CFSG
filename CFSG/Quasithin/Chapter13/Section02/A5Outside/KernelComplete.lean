module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.KernelInnerAction
public import CFSG.Quasithin.Chapter13.Section05.A5Source.QuotientNormalizerAction
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.ExtraspecialActor
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.KernelEscape
public import Theory.GroupTheory.PResidual.PCoreQuotient
public import Theory.ElementaryAbelian.Quotient

/-!
# The original outside omega-action kernel is the two-core

Suppose the kernel has a nontrivial two-residual X. Its original radical
R=O₂(XT) acts inner on L/O₂(L), hence evenly in the five-point module.
The Thompson calculation gives N_G(J(R))≤N_G(L). The original E.2.1
escape and the full wreath action force H to normalize the same J(R),
contradicting the chosen outside H. Thus C_H(U_H)=O₂(H).

The resulting equality also identifies the core of H∩N_G(L) and makes
O²(H)/O₂(O²(H)) elementary cubic, using the actual quotient map. The
Baumann normalizer bound and solvability are the earlier source inputs
5.1.7(1) and 13.2.8(1), retained explicitly.

Source: Aschbacher–Smith, Lemma 13.2.9, printed pp.880–881.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

/-- The original normal two-subgroup acts evenly on the marked five points. -/
theorem source_kernel_radical_even_action
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hne : centralizer ((omegaOrbit T H).subgroupOf H : Set H) ≠ pCore 2 H) :
    let C := centralizer ((omegaOrbit T H).subgroupOf H : Set H)
    let X := ((pResidual 2 C).map C.subtype).map H.subtype
    let R := (X ⊔ (T : Subgroup G)).pCoreIn 2
    (R.subgroupOf (L ⊔ (T : Subgroup G))).map d.localActor ≤ alternatingGroup (Fin 5) := by
  dsimp only
  rintro a ⟨r,hr,rfl⟩
  apply d.localActor_even_of_quotientNormalizerAction_inner
  obtain ⟨x,hx,hxr⟩ := hr
  have hi := source_kernel_radical_action_inner d hH hB hZ hs hne ⟨x,hx⟩
  change d.quotientNormalizerAction _ ∈ MulAut.innerSubgroup _ at hi
  convert hi using 1
  congr 1
  exact Subtype.ext hxr.symm

/-- Original 13.2.9: the whole omega-orbit action kernel is the two-core. -/
theorem source_omega_centralizer_eq_twoCore
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) :
    centralizer ((omegaOrbit T H).subgroupOf H : Set H) = pCore 2 H := by
  by_contra hne
  let h := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
  let S := T.subtype hH.1.1.2
  let C := centralizer ((omegaOrbit T H).subgroupOf H : Set H)
  let X := (pResidual 2 C).map C.subtype
  let R := (X ⊔ (S : Subgroup H)).pCoreIn 2
  let XG := X.map H.subtype
  let RG := (XG ⊔ (T : Subgroup G)).pCoreIn 2
  have heven := source_kernel_radical_even_action d hH hB hZ hs hne
  have hN : normalizer (elementaryAbelianMaxJ RG : Set G) ≤ normalizer (L : Set G) :=
    (source_kernel_thompson_normalizer_of_even_action d hH hB hZ hs hne heven).2
  have hescape := source_kernel_e21_escape_of_even_action d hH hB hZ hs hne heven
  have hx : ¬ centralizerModulo (S : Subgroup H)
      (ChapterB.minimalParabolicCore S h.2.2.1)
      ((ChapterB.minimalParabolicCore S h.2.2.1).pCoreIn 2) ≤ pCore 2 H := by
    intro hc
    apply hescape
    intro t ht
    apply hc
    apply mem_centralizerModulo_iff.mpr
    obtain ⟨htS,htC⟩ := mem_centralizerModulo_iff.mp ht
    refine ⟨htS,?_⟩
    intro j hj
    rw [ChapterE.SolvableMinimalParabolic.core_pCoreIn_eq]
    exact htC j hj
  obtain ⟨_,_,_,hXne,_,_⟩ := source_kernel_residual_moves_component d hH hB hZ hs hne
  have hn := (source_residual_kernel_thompson d hH hB hZ hs hXne (Or.inr hx)).2.2
  have hRmap : R.map H.subtype = RG := by
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective]
    congr 1
    rw [Subgroup.map_sup]
    change XG ⊔ ((T : Subgroup G).subgroupOf H).map H.subtype = XG ⊔ (T : Subgroup G)
    rw [map_subgroupOf_eq_of_le hH.1.1.2]
  change H ≤ normalizer (ChapterB.thompsonJ (R.map H.subtype) 0 : Set G) at hn
  rw [ChapterB.thompsonJ_zero, hRmap] at hn
  exact hH.1.2 (hn.trans hN)

/-- The canonical source overlap core is now the intrinsic two-core. -/
theorem source_overlap_core_eq_twoCore
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) :
    ((normalizer (L : Set G)).subgroupOf H).normalCore = pCore 2 H :=
  (source_overlap_core_eq_omega_centralizer d hH hB hZ hs).trans
    (source_omega_centralizer_eq_twoCore d hH hB hZ hs)

/-- The original residual modulo its own two-core is elementary cubic. -/
theorem source_residual_core_quotient_elementary
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) :
    IsElementaryAbelian 3 (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) := by
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer ((omegaOrbit T H).subgroupOf H : Set H)
  let q := QuotientGroup.mk' C
  let : IsElementaryAbelian 3 (pResidual 2 (H ⧸ C)) :=
    (source_solvable_wreath_omega_action d hH hB hZ hs).residual_elementary
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    change IsPGroup 2 (centralizer ((omegaOrbit T H).subgroupOf H : Set H))
    rw [source_omega_centralizer_eq_twoCore d hH hB hZ hs]
    exact pCore_isPGroup
  let e := q.pResidualCoreQuotientEquiv (QuotientGroup.mk'_surjective C) hk
  exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective

end CFSG.Quasithin.Chapter13.Section02.A5Outside
