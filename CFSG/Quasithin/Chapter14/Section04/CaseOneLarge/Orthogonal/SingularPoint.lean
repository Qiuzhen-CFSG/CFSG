module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.TwoCore
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.OrthogonalInspection

/-!
# The original singular point in the orthogonal branch

The actual Sylow subgroup normalizes the image of V₂, which is a binary
line. The natural Ω₄⁺(4) action therefore makes this line singular. The
original right conjugate s=zᵍ lies in V₂ and survives U/Z(U), so its image
is the unique nonzero vector of this line. Its F₄-span is totally singular.

The final consumer discharges the kernel and center-intersection premises
from the original counterexample and retains the proved O₂(H)=U. It also
records |V|=8 and |Ṽ|=4: the F₄-point belongs to the quotient, and the
ambient seed cannot be assigned order four. Identifying the entire Ṽ with
this F₄-point and constructing the escaping conjugate i remain subsequent
source deductions.

Source: Aschbacher--Smith, 14.4.7--9, printed pp.1009--1010;
refs/quasithin.pdf.
-/

public noncomputable section

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension CoreGeometry ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable [IsMulCommutative V]
local instance (F : InvariantFlag T V 3) : (F.U.subgroupOf F.H).Normal := F.U_normal

private theorem source_singular_line_witness
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hk : F.terminalHatAction.ker = pCore 2 F.H)
    (hc : V ⊓ F.ZU = F.Vi 1)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F hk).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    ∃ s : F.U.subgroupOf F.H, (s : F.H) ∈ (F.Vi 2).subgroupOf F.H ∧
      e ((sourceAction F hk).vector s) ≠ 0 ∧
      formD 2 Binary.F (e ((sourceAction F hk).vector s)) = 0 ∧
      ((sourceAction F hk).image ((F.Vi 2).subgroupOf F.H)).map e.toLinearMap ≤
        (Submodule.span Binary.F {e ((sourceAction F hk).vector s)}).restrictScalars (ZMod 2) := by
  let := F.U_normal
  let V₂ := (F.Vi 2).subgroupOf F.H
  have hn : ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H) ≤
      normalizer (V₂ : Set F.H) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro v
    exact mem_normalizer_iff.mp (F.invariant 2 ht) (v : G)
  have hd : finrank (ZMod 2) ((sourceAction F hk).image V₂) = 1 := by
    rw [sourceAction_image]
    exact finrank_hatSpace_plane F (by decide) hc
  let K := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  let : K.Normal := (inferInstance : (pResidual 2 F.H).Normal).map _
    (QuotientGroup.mk'_surjective _)
  obtain ⟨s, hs, hs0, hsing, hline⟩ :=
    (sourceAction F hk).orthogonal_singular_line K κ e he
      (T.subtype (F.invariant 1)) V₂ hn hd
  exact ⟨s, hs, hs0, hsing, hline⟩

private theorem singular_original_generator
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hk : F.terminalHatAction.ker = pCore 2 F.H)
    (hc : V ⊓ F.ZU = F.Vi 1)
    (g z : G) (hg : g ∈ F.Gi 2) (hgV : g ∈ normalizer (V : Set G))
    (hgH : g ∉ F.H) (hz : z ≠ 1) (hzp : F.Vi 1 = zpowers z)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F hk).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    ∃ hs : MulAut.conj g⁻¹ z ∈ F.U,
      let v := e (hatElement F ⟨MulAut.conj g⁻¹ z,hs⟩)
      MulAut.conj g⁻¹ z ∈ F.Vi 2 ∧ v ≠ 0 ∧
      formD 2 Binary.F v = 0 ∧
      (hatSpace F (F.Vi 2)).map e.toLinearMap = Submodule.span (ZMod 2) {v} ∧
      ∀ w ∈ Submodule.span Binary.F {v}, formD 2 Binary.F w = 0 := by
  let := F.U_normal
  have hzs : MulAut.conj g⁻¹ z ∈ conjugate (F.Vi 1) g :=
    mem_map_of_mem _ (hzp ▸ mem_zpowers z)
  have hgp : conjugate (F.Vi 1) g ≤ F.Vi 2 := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := ha
    exact (mem_normalizer_iff.mp ((F.Gi 2).inv_mem hg) b).mp
      (F.monotone (by decide : 1 ≤ 2) hb)
  have hs₂ := hgp hzs
  have hs : MulAut.conj g⁻¹ z ∈ F.U :=
    (F.le_seed 2).trans (le_conjugateSpanBy V F.H) hs₂
  let s : F.U := ⟨MulAut.conj g⁻¹ z,hs⟩
  have hv : hatElement F s ≠ 0 := by
    intro hzero
    have hmem : s ∈ center F.U := by
      apply (QuotientGroup.eq_one_iff s).mp
      exact congrArg Additive.toMul hzero
    have hZs : (s : G) ∈ F.ZU := ⟨s,hmem,rfl⟩
    have hbot : (s : G) ∈ (⊥ : Subgroup G) :=
      (F.conjugate_point_inf_ZU (by decide) hc g hgV hgH).le ⟨hzs,hZs⟩
    apply hz
    apply (MulAut.conj g⁻¹).injective
    simpa only [map_one] using (Subgroup.mem_bot.mp hbot)
  obtain ⟨t,ht,ht0,htsing,_⟩ := source_singular_line_witness F hk hc κ e he
  have hd : finrank (ZMod 2) (hatSpace F (F.Vi 2)) = 1 :=
    finrank_hatSpace_plane F (by decide) hc
  have himg : hatElement F s ∈ hatSpace F (F.Vi 2) := ⟨s,hs₂,rfl⟩
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hd himg hv
  have htm : (sourceAction F hk).vector t ∈ hatSpace F (F.Vi 2) := by
    rw [← sourceAction_image F hk (F.Vi 2)]
    exact (sourceAction F hk).vector_mem_image _ t ht
  obtain ⟨c,hc'⟩ := Submodule.mem_span_singleton.mp (hspan ▸ htm)
  have htn : (sourceAction F hk).vector t ≠ 0 := by
    intro hh
    exact ht0 (by rw [hh,map_zero])
  have hc0 : c ≠ 0 := by
    intro hh
    rw [hh,zero_smul] at hc'
    exact htn hc'.symm
  have hc1 : c = 1 := by
    have hb : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    exact (hb c).resolve_left hc0
  have heq : (sourceAction F hk).vector t = hatElement F s := by
    simpa only [hc1,one_smul] using hc'.symm
  have hsing : formD 2 Binary.F (e (hatElement F s)) = 0 := by
    simpa only [heq] using htsing
  refine ⟨hs,hs₂,fun h => hv (e.injective (h.trans e.map_zero.symm)),hsing,?_,?_⟩
  · rw [hspan,Submodule.map_span]
    simp only [Set.image_singleton]
    rfl
  · intro w hw
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [QuadraticMap.map_smul,hsing,smul_zero]

/-- The entrance to 14.4.9 on the original flag: the whole two-core is U,
the seed and its central-quotient image have their respective orders eight
and four, and the same right conjugate zᵍ spans the singular binary line.
Its F₄-span is proved totally singular, with no singular-point marking input. -/
theorem source_orthogonal_singular_point (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    F.H.pCoreIn 2 = F.U ∧ Nat.card V = 8 ∧ Nat.card (hatSpace F V) = 4 ∧
      ∃ z : G, orderOf z = 2 ∧ F.Vi 1 = zpowers z ∧
        F.H = centralizer ({z} : Set G) ∧
        ∃ hs : MulAut.conj g⁻¹ z ∈ F.U,
          let v := e (hatElement F ⟨MulAut.conj g⁻¹ z,hs⟩)
          MulAut.conj g⁻¹ z ∈ F.Vi 2 ∧ v ≠ 0 ∧
          formD 2 Binary.F v = 0 ∧
          (hatSpace F (F.Vi 2)).map e.toLinearMap = Submodule.span (ZMod 2) {v} ∧
          ∀ w ∈ Submodule.span Binary.F {v}, formD 2 Binary.F w = 0 := by
  let := chosen.elementary
  have hc := (source_closure d earlier hq chosen structural alternatives F hne).2.2
  have hv : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  have hhat : Nat.card (hatSpace F V) = 4 := by
    have hm := card_hatImage_mul_card_inf F V (le_conjugateSpanBy V F.H)
    rw [hc,F.card 1 (by decide),hv] at hm
    rw [card_hatSpace]
    omega
  refine ⟨(source_orthogonal_twoCore d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he).2,hv,hhat,?_⟩
  obtain ⟨z,hz,hzp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hzo : orderOf z = 2 := by
    rw [← Nat.card_zpowers,← hzp]
    exact F.card 1 (by decide)
  refine ⟨z,hzo,hzp,F.H_eq_centralizer (by decide) z hzp,?_⟩
  exact singular_original_generator F
    (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)
    hc g z (F.P_le_G₂ (by decide) L chosen.normalizes hgP)
    (chosen.normalizes hg) hgH hz hzp κ e he

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
