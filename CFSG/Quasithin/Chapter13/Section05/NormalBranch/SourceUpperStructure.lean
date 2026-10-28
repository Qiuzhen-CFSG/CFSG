module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceCoreProduct
public import Theory.Representation.BinaryConjugationSection.Canonical
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The original upper quotient and its centrality bounds

The selected original A₅ pair K has V in its two-core S and S centralizes
V. The two marked intersections generating S have commutators and squares
in V, so the literal quotient S/V is elementary abelian. Its commutator
with the original point residual L₁ lies in O₂(L₁), the bound used after
natural-module recognition to collapse this upper quotient.

Source: Aschbacher–Smith,G.2.4(6,8), printed pp.334–335, applied in13.5.15.
-/

@[expose] public section
open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceUpperStructure
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open SourceFiveModule
open ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

theorem module_le_core (h : D.Hypothesis) (hseed : D.Vplus = ⁅D.V,D.L₁⁆)
    (g : D.L) (hK : NormalBranch.K D g.val ≤ D.L) (hL : D.L₁ ≤ NormalBranch.K D g.val)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    D.V ≤ (NormalBranch.K D g.val).pCoreIn 2 := by
  have hc := SourceFiveSpan.module_commutator d hK a hi h hL hseed
  have hVQ : D.V ≤ D.LT.pCoreIn 2 := by
    simpa only [pCoreIn,map_subgroupOf_eq_of_le h.V_le_LT] using
      map_mono (f := D.LT.subtype) h.reduced.le_pCore
  have hv : D.V ≤ NormalBranch.K D g.val := by
    rw [←hc]
    exact le_normalizer_iff_commutator_le_right.mp
      (hVQ.trans (SourcePairResidual.twoCore_normalizes_pair h g))
  exact le_pCoreIn_of_normalizes h.elementary.isPGroup hv
    (hK.trans (le_sup_left.trans d.normalizes_V))

theorem core_centralizes_module (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val ≤ D.L) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    (NormalBranch.K D g.val).pCoreIn 2 ≤ centralizer (D.V : Set G) :=
  (SourceCoreProduct.core_le_local_core d e g hK a hi).trans
    ((SourcePairResidual.local_core_le_LT_core h).trans
      (h.sylow_centralizer.symm.le.trans inf_le_right))

omit [Finite G] in
theorem pair_normalizes_core (g : D.L) :
    NormalBranch.K D g.val ≤ normalizer ((NormalBranch.K D g.val).pCoreIn 2 : Set G) := by
  simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
    (pCore 2 (NormalBranch.K D g.val)).le_normalizer_map (NormalBranch.K D g.val).subtype

theorem core_commutator_le_local_core (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val ≤ D.L) (hL : D.L₁ ≤ NormalBranch.K D g.val)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    ⁅(NormalBranch.K D g.val).pCoreIn 2,D.L₁⁆ ≤ D.L₁.pCoreIn 2 := by
  let S := (NormalBranch.K D g.val).pCoreIn 2
  have hSL : S ≤ D.L := (pCoreIn_le 2 _).trans hK
  have hSG : S ≤ D.Gz :=
    (core_centralizes_module d h e g hK a hi).trans
      (centralizer_le (h.point_lt.le.trans h.plus_le))
  have hSn : S ≤ normalizer (D.L₁ : Set G) :=
    (le_inf hSL hSG).trans (le_normalizer_embedded_pResidual 2 (D.L ⊓ D.Gz))
  have hnS : D.L₁ ≤ normalizer (S : Set G) :=
    hL.trans (pair_normalizes_core g)
  have hcS := le_normalizer_iff_commutator_le_left.mp hnS
  exact le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 (NormalBranch.K D g.val)).to_le hcS)
    (le_normalizer_iff_commutator_le_right.mp hSn)
    (normalizer_commutator_ge_right _ _)

omit [Finite G] in
theorem conjugate_core (g : D.L) (hg : g.val ∈ NormalBranch.K D g.val) :
    conjugate ((NormalBranch.K D g.val).pCoreIn 2) g.val =
      (NormalBranch.K D g.val).pCoreIn 2 :=
  mem_normalizer_iff_map_conj_eq.mp
    ((normalizer ((NormalBranch.K D g.val).pCoreIn 2 : Set G)).inv_mem
      (pair_normalizes_core g hg))

omit [Finite G] in
theorem conjugate_marked (g : D.L) (hg : g.val ∈ NormalBranch.K D g.val) :
    conjugate (D.UH ⊓ (NormalBranch.K D g.val).pCoreIn 2) g.val =
      conjugate D.UH g.val ⊓ (NormalBranch.K D g.val).pCoreIn 2 := by
  change (D.UH ⊓ _).map (MulAut.conj g.val⁻¹).toMonoidHom = _
  rw [map_inf _ _ _ (MulAut.conj g.val⁻¹).injective]
  exact congrArg (conjugate D.UH g.val ⊓ ·) (conjugate_core g hg)

include d in
/-- Normality for the literal upper quotient; no new action is chosen. -/
theorem module_normal_in_core (g : D.L) (hK : NormalBranch.K D g.val ≤ D.L) :
    (D.V.subgroupOf ((NormalBranch.K D g.val).pCoreIn 2)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (((pCoreIn_le 2 _).trans hK).trans (le_sup_left.trans d.normalizes_V))

theorem upper_elementary (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L)
    (hg : g.val ∈ NormalBranch.K D g.val) (hK : NormalBranch.K D g.val ≤ D.L)
    (hL : D.L₁ ≤ NormalBranch.K D g.val) (hp : IsPPerfect 2 (NormalBranch.K D g.val))
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    [(D.V.subgroupOf ((NormalBranch.K D g.val).pCoreIn 2)).Normal] :
    IsElementaryAbelian 2 ((NormalBranch.K D g.val).pCoreIn 2 ⧸
      D.V.subgroupOf ((NormalBranch.K D g.val).pCoreIn 2)) := by
  let S := (NormalBranch.K D g.val).pCoreIn 2
  let W := D.UH ⊓ S
  let X := conjugate W g.val
  let q := QuotientGroup.mk' (D.V.subgroupOf S)
  have hsplit : S=W⊔X := SourceCoreProduct.core_generated d h e hseed hn hU g hg hK hp a hi
  have hXS : X ≤ S := (conjugate_marked g hg).le.trans inf_le_right
  have hSW : S ≤ normalizer (W : Set G) :=
    (le_inf (SourceCoreProduct.core_normalizes_closure d h e g hK a hi) S.le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hSX : S ≤ normalizer (X : Set G) := by
    have hh := (map_mono (f := (MulAut.conj g.val⁻¹).toMonoidHom) hSW).trans
      (W.le_normalizer_map (MulAut.conj g.val⁻¹).toMonoidHom)
    change conjugate S g.val ≤ normalizer (X : Set G) at hh
    rwa [conjugate_core g hg] at hh
  have hWX : ⁅W,X⁆ ≤ D.V := by
    have hc := le_inf (le_normalizer_iff_commutator_le_left.mp (hXS.trans hSW))
      (le_normalizer_iff_commutator_le_right.mp ((show W≤S from inf_le_right).trans hSX))
    exact hc.trans ((inf_le_inf inf_le_left (map_mono inf_le_left)).trans
      ((SourceSecondLayer.intersection_le_seed d h e hseed hn hU g hK hL).trans h.plus_le))
  have hpoint : D.V₁ ≤ D.V := h.point_lt.le.trans h.plus_le
  have hsqU (u : G) (hu : u∈D.UH) : u^2∈D.V₁ := by
    let : Fact (IsPGroup 2 D.UH) := ⟨h.g2_hypothesis.U_isPGroup⟩
    exact h.frattini_UH_le_point
      ⟨(⟨u,hu⟩:D.UH)^2,pth_power_mem_frattini_of_isPGroup _,rfl⟩
  have hsqW : ∀w∈W,w^2∈D.V := fun w hw => hpoint (hsqU w hw.1)
  have hsqX : ∀x∈X,x^2∈D.V := by
    rintro x ⟨w,hw,rfl⟩
    have hh := mem_map_of_mem (MulAut.conj g.val⁻¹).toMonoidHom (hsqW w hw)
    have he : D.V.map (MulAut.conj g.val⁻¹).toMonoidHom = D.V :=
      mem_normalizer_iff_map_conj_eq.mp
        ((normalizer (D.V : Set G)).inv_mem (d.normalizes_V (mem_sup_left g.property)))
    rw [he] at hh
    simpa only [map_pow] using hh
  have hsq : ∀x:S ⧸ D.V.subgroupOf S,x^2=1 := by
    intro x
    obtain ⟨s,rfl⟩ := QuotientGroup.mk'_surjective _ x
    have hprod : s.val ∈ (W:Set G)*(X:Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ (hXS.trans hSW),←hsplit]
      exact s.property
    obtain ⟨w,hw,x,hx,hwx⟩ := hprod
    let wS : S := ⟨w,hw.2⟩
    let xS : S := ⟨x,hXS hx⟩
    have hs : wS*xS=s := Subtype.ext hwx
    have hqw : (q wS)^2=1 := by
      rw [←map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hsqW w hw)
    have hqx : (q xS)^2=1 := by
      rw [←map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hsqX x hx)
    have hcomm : Commute (q wS) (q xS) := by
      change q wS*q xS=q xS*q wS
      rw [←commutatorElement_eq_one_iff_mul_comm,←map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr (hWX (commutator_mem_commutator hw hx))
    change (q s)^2=1
    rw [←hs,map_mul,hcomm.mul_pow,hqw,hqx,mul_one]
  exact {
    is_comm := ⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hsq x)) x y).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }


end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceUpperStructure
end
