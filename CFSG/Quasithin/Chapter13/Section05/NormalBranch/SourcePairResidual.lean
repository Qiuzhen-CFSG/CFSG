module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceFivePair
public import Theory.GroupTheory.PResidual.NormalizerImage
public import Theory.GroupTheory.PResidual.NormalizedImageContainment
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The original pair absorbs L₁ and is exactly L⁻

The source two-core Q=O₂(LT) normalizes U_H and its chosen conjugate.
The quotient image places L₁ in KQ; two-perfection removes the Q
ambiguity, giving L₁≤K. The selected mover normalizes K for the same
reason. As U_H=[U_H,L₁], the pair K is itself two-perfect. Thus the
source residual O²(QK) equals the actual generated pair K.

This proves the containment and residual assertions in13.5.14(3–4) on
the original n=6 subgroups. It does not assert the later block structure,
whose G.2.4 application must retain the correct local Sylow data.

Source: Aschbacher–Smith,13.5.14, printed p.919.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairResidual
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}

theorem twoCore_normalizes_pair (h : D.Hypothesis) (g : D.L) :
    D.LT.pCoreIn 2 ≤ normalizer (NormalBranch.K D g.val : Set G) := by
  let Q := D.LT.pCoreIn 2
  have hQT : Q ≤ (D.T : Subgroup G) := h.sylow_centralizer.symm.le.trans inf_le_left
  have hn : Q ≤ normalizer (D.UH : Set G) :=
    hQT.trans (h.T_le_H.trans (le_normalizer_conjugateSpanBy D.Vplus D.H))
  have hQ : Q.map (MulAut.conj g.val⁻¹).toMonoidHom = Q :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (Q : Set G)).inv_mem
      ((D.LT.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D.LT
        (pCore 2 D.LT))) (mem_sup_left g.property)))
  have hc : Q ≤ normalizer (ChapterG.Section02.Setup.conjugate D.UH g.val : Set G) := by
    have hh := (map_mono (f := (MulAut.conj g.val⁻¹).toMonoidHom) hn).trans
      (D.UH.le_normalizer_map (MulAut.conj g.val⁻¹).toMonoidHom)
    rwa [hQ] at hh
  exact (le_inf hn hc).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

theorem local_core_le_LT_core (h : D.Hypothesis) : D.L.pCoreIn 2 ≤ D.LT.pCoreIn 2 :=
  pCoreIn_mono_of_normalizes le_sup_left (sup_le D.L.le_normalizer h.normalizes_L)


/-- Once the original local residual lies in the pair and the mover
normalizes it, commutator generation makes that pair two-perfect. -/
theorem pair_twoPerfect (h : D.Hypothesis)
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (g : D.L) (hLK : D.L₁ ≤ NormalBranch.K D g.val)
    (hgK : g.val ∈ normalizer (NormalBranch.K D g.val : Set G)) :
    IsPPerfect 2 (NormalBranch.K D g.val) := by
  let K := NormalBranch.K D g.val
  let R := (pResidual 2 K).map K.subtype
  have hp : IsPPerfect 2 (D.L₁.subgroupOf K) :=
    (isPPerfect_embedded_pResidual 2 (D.L ⊓ D.Gz)).of_surjective
      (subgroupOfEquivOfLe hLK).symm.toMonoidHom (subgroupOfEquivOfLe hLK).symm.surjective
  have hLR : D.L₁ ≤ R := by
    have hh := map_mono (f := K.subtype) (le_pResidual_of_isPPerfect (D.L₁.subgroupOf K) hp)
    rwa [map_subgroupOf_eq_of_le hLK] at hh
  have hKR : K ≤ normalizer (R : Set G) :=
    K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pResidual 2 K))
  have hUR : D.UH ≤ R := by
    rw [(closure_reduction h hseed hn).1]
    exact (commutator_mono (show D.UH≤K from le_sup_left) hLR).trans
      (le_normalizer_iff_commutator_le_right.mp hKR)
  have hgR : g.val⁻¹ ∈ normalizer (R : Set G) :=
    (normalizer_le_normalizer_characteristic_image K (pResidual 2 K))
      ((normalizer (K : Set G)).inv_mem hgK)
  have hconj : ChapterG.Section02.Setup.conjugate D.UH g.val ≤ R := by
    have hh := map_mono (f := (MulAut.conj g.val⁻¹).toMonoidHom) hUR
    have heR : R.map (MulAut.conj g.val⁻¹).toMonoidHom = R :=
      mem_normalizer_iff_map_conj_eq.mp hgR
    exact hh.trans_eq heR
  have he : K=R := le_antisymm (sup_le hUR hconj) (map_subtype_le _)
  change IsPPerfect 2 K
  rw [he]
  exact isPPerfect_embedded_pResidual 2 K

/-- The actual source L⁻ equals the generated pair, with the original Q=O₂(LT). -/
theorem blockResidual_eq_pair (h : D.Hypothesis)
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (g : D.L) (hLK : D.L₁ ≤ NormalBranch.K D g.val)
    (hgK : g.val ∈ normalizer (NormalBranch.K D g.val : Set G)) :
    blockResidual D g.val = NormalBranch.K D g.val := by
  have hh := embedded_pResidual_join_pGroup (NormalBranch.K D g.val) (D.LT.pCoreIn 2)
    (pair_twoPerfect h hseed hn g hLK hgK) (isPGroup_pCoreIn 2 D.LT)
    (twoCore_normalizes_pair h g)
  change (pResidual 2 (D.LT.pCoreIn 2 ⊔ NormalBranch.K D g.val : Subgroup G)).map _ = _
  rw [sup_comm]
  exact hh

open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open PlaneGeometry.TwoBlocks
variable {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

/-- Quotient containment lifts because the original two-core normalizes the
pair; two-perfection of L₁ removes the possible two-group discrepancy. -/
theorem local_le_pair (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (g : D.L) (a : alternatingGroup (Fin 6))
    (ha : Section07.NaturalAction.image d D.V₁ = move a.val canonicalLine)
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    D.L₁ ≤ NormalBranch.K D g.val := by
  let f := localMap d
  let X := D.L₁.subgroupOf D.L
  let Y := (NormalBranch.K D g.val).subgroupOf D.L
  have hLL : D.L₁ ≤ D.L := (map_subtype_le _).trans inf_le_left
  have hp : IsPPerfect 2 X := (isPPerfect_embedded_pResidual 2 (D.L ⊓ D.Gz)).of_surjective
    (subgroupOfEquivOfLe hLL).symm.toMonoidHom (subgroupOfEquivOfLe hLL).symm.surjective
  have hk := SourceStar.local_kernel_two d e
  have hkn : f.ker ≤ normalizer (Y : Set D.L) := by
    have hkcore : f.ker ≤ pCore 2 D.L := le_sSup ⟨inferInstance,hk⟩
    intro l hl
    have hc : l.val ∈ D.LT.pCoreIn 2 := local_core_le_LT_core h
      (mem_map_of_mem D.L.subtype (hkcore hl))
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp (twoCore_normalizes_pair h g hc) y.val
  have himage : X.map f ≤ Y.map f := by
    rw [SourcePointCore.local_residual_marking d h a ha,hi]
    apply map_mono
    exact fun _ hx => ⟨hx.1.2,hx.2⟩
  have hh := isPPerfect_le_of_map_le_of_kernel_normalizes f X Y hp hk hkn himage
  intro l hl
  exact hh (show (⟨l,hLL hl⟩:D.L)∈X from hl)

/-- The original pair is normalized by its selected conjugator: modulo the
two-core that element already lies in the pair image. -/
theorem mover_normalizes_pair (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (g : D.L)
    (hg : localMap d g ∈ ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)) :
    g.val ∈ normalizer (NormalBranch.K D g.val : Set G) := by
  let Y := (NormalBranch.K D g.val).subgroupOf D.L
  have hker : (localMap d).ker ≤ pCore 2 D.L :=
    le_sSup ⟨inferInstance,SourceStar.local_kernel_two d e⟩
  have hm : g ∈ Y ⊔ (localMap d).ker := by
    rw [←comap_map_eq]
    exact hg
  have hnorm : Y ⊔ (localMap d).ker ≤
      (normalizer (NormalBranch.K D g.val : Set G)).comap D.L.subtype := by
    apply sup_le
    · exact fun x hx => (NormalBranch.K D g.val).le_normalizer hx
    · intro x hx
      exact twoCore_normalizes_pair h g (local_core_le_LT_core h
        (mem_map_of_mem D.L.subtype (hker hx)))
  exact hnorm hm

/-- The perfect local residual is contained in the actual pair selected in
13.5.14, without a block or marked G.2.4 input. -/
theorem exists_pair_with_local_residual (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) :
    ∃ a : alternatingGroup (Fin 6), ∃ g : D.L,
      g.val ∉ D.Gz ∧ localMap d g (a.val 5)=a.val 5 ∧
      NormalBranch.K D g.val ≤ D.L ∧ D.L₁ ≤ NormalBranch.K D g.val ∧
      g.val ∈ normalizer (NormalBranch.K D g.val : Set G) ∧
      IsPPerfect 2 (NormalBranch.K D g.val) ∧ blockResidual D g.val = NormalBranch.K D g.val ∧
      ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
        FivePair.five.map (MulAut.conj a.val).toMonoidHom := by
  obtain ⟨a,ha,g,hg,hgn,hfix,hKL,hi⟩ := SourceFivePair.exists_original_five_pair d h e hseed hn hU
  have hLK := local_le_pair d h e g a ha hi
  have hgK : g.val ∈ normalizer (NormalBranch.K D g.val : Set G) := by
    apply mover_normalizes_pair d h e g
    rw [hi,hg]
    exact mem_map_of_mem (MulAut.conj a.val).toMonoidHom FivePair.mover_mem
  exact ⟨a,g,hgn,hfix,hKL,hLK,hgK,pair_twoPerfect h hseed hn g hLK hgK,
    blockResidual_eq_pair h hseed hn g hLK hgK,hi⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairResidual
end
