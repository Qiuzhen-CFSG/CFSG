module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairResidual
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.FivePair.Coordinates

/-!
# The intrinsic A₅ quotient and unchanged point residual of L⁻

The actual pair image is the even five-letter stabilizer. Restriction of
the original natural map has a two-group kernel, so the intrinsic two-core
quotient is the concrete A₅ quotient. The two-perfect original L₁ lies in
the pair, and residual monotonicity proves that its point residual remains
exactly L₁. The final source consumer constructs all this data together
with K=L⁻, rather than assuming a marked substitution.

The A₅ block structure is not asserted: a G.2.4 substitution with the
correct local Sylow is still needed. Retaining the original T in the
fixed-T MarkedBlockInput would require an unavailable normalization of K.

Source: Aschbacher–Smith,13.5.14(3–4), printed p.919.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairQuotient
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
include d

theorem pair_quotient (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val ≤ D.L) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    Nonempty ((NormalBranch.K D g.val ⧸ pCore 2 (NormalBranch.K D g.val)) ≃*
      alternatingGroup (Fin 5)) := by
  let J := (NormalBranch.K D g.val).subgroupOf D.L
  let R := J.map (localMap d)
  let f := (localMap d).subgroupMap J
  have hk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap]
    exact (SourceStar.local_kernel_two d e).comap_subtype
  let eJR := Theory.GroupTheory.ComponentLocalCoreSection.quotientCoreEquiv 2 f
    ((localMap d).subgroupMap_surjective J) hk
  let eRF : R ≃* FivePair.five := (MulEquiv.subgroupCongr hi).trans
    ((MulAut.conj a.val).subgroupMap FivePair.five).symm
  let eRA := eRF.trans FivePair.fiveEquiv
  let eRAQ := Theory.GroupTheory.ComponentLocalCoreSection.quotientCoreEquiv 2 eRA.toMonoidHom
    eRA.surjective (IsPGroup.ker_isPGroup_of_injective eRA.injective)
  let eKJ := (subgroupOfEquivOfLe hK).symm
  let eKJQ := Theory.GroupTheory.ComponentLocalCoreSection.quotientCoreEquiv 2 eKJ.toMonoidHom
    eKJ.surjective (IsPGroup.ker_isPGroup_of_injective eKJ.injective)
  exact ⟨eKJQ.trans (eJR.trans (eRAQ.trans
    ((QuotientGroup.quotientMulEquivOfEq FivePair.alternating_five_twoCore).trans
      QuotientGroup.quotientBot)))⟩


omit d in
/-- Restricting from L to the selected pair keeps the original point residual. -/
theorem point_residual_eq (h : D.Hypothesis) (g : D.L)
    (hK : NormalBranch.K D g.val ≤ D.L) (hL : D.L₁ ≤ NormalBranch.K D g.val) :
    (ChapterG.Section02.AlternatingFive.chapter13Setup D.V₁ D.Vplus
      (NormalBranch.K D g.val) D.T D.H).L₁ = D.L₁ := by
  let C := NormalBranch.K D g.val ⊓ D.Gz
  have he : (ChapterG.Section02.AlternatingFive.chapter13Setup D.V₁ D.Vplus
      (NormalBranch.K D g.val) D.T D.H).L₁ = (pResidual 2 C).map C.subtype := by
    change (pResidual 2 (NormalBranch.K D g.val ⊓ normalizer (D.V₁ : Set G) : Subgroup G)).map
      (NormalBranch.K D g.val ⊓ normalizer (D.V₁ : Set G)).subtype = _
    rw [h.normalizer_point_eq]
  rw [he]
  apply le_antisymm (embedded_pResidual_mono 2 (inf_le_inf_right _ hK))
  have hLC : D.L₁ ≤ C := le_inf hL ((map_subtype_le _).trans inf_le_right)
  have hp : IsPPerfect 2 (D.L₁.subgroupOf C) :=
    (isPPerfect_embedded_pResidual 2 (D.L ⊓ D.Gz)).of_surjective
      (subgroupOfEquivOfLe hLC).symm.toMonoidHom (subgroupOfEquivOfLe hLC).symm.surjective
  have hh := map_mono (f := C.subtype) (le_pResidual_of_isPPerfect (D.L₁.subgroupOf C) hp)
  rwa [map_subgroupOf_eq_of_le hLC] at hh

/-- Original n=6 source consumer, constructing K=L⁻ and its actual A₅
quotient. No G.2.4 marking or block assertion is assumed. -/
theorem exists_original_residual_pair (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) :
    ∃ g : D.L, g.val ∉ D.Gz ∧ NormalBranch.K D g.val ≤ D.L ∧
      D.L₁ ≤ NormalBranch.K D g.val ∧ IsPPerfect 2 (NormalBranch.K D g.val) ∧
      blockResidual D g.val = NormalBranch.K D g.val ∧
      (ChapterG.Section02.AlternatingFive.chapter13Setup D.V₁ D.Vplus
        (NormalBranch.K D g.val) D.T D.H).L₁ = D.L₁ ∧
      Nonempty ((NormalBranch.K D g.val ⧸ pCore 2 (NormalBranch.K D g.val)) ≃*
        alternatingGroup (Fin 5)) := by
  obtain ⟨a,g,hg,_,hK,hL,_,hp,hr,hi⟩ := SourcePairResidual.exists_pair_with_local_residual d h e hseed hn hU
  exact ⟨g,hg,hK,hL,hp,hr,point_residual_eq h g hK hL,pair_quotient d e g hK a hi⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairQuotient
end
