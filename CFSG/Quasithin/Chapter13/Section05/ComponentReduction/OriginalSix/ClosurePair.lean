module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.Configuration
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceInternalMover

/-!
# The original ordinary A₆ pair from the tilde commutator

The component-module calculation supplies precisely the tilde generation
required by13.5.14. Lift it through the original point line to put U_H in
O₂(L₁). Its nontrivial normalized image fills the even point core. The
marked five-letter mover therefore generates the actual A₅ image; kernel
normalization lifts the local residual into the pair, and replacing the
mover inside that pair preserves the original conjugate closure. The pair
is its own two-residual and spans the original V from V₁.
This substitutes the original module output without assuming L₁ normal in H.
Source: Aschbacher–Smith13.5.14(1–4), printed p.919.
-/
public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.ClosurePair
open Section08.SourceCompletion NormalBranch
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open PlaneGeometry.TwoBlocks SourcePointCore SourceFivePair SourcePairResidual
open ChapterG.Section02.AlternatingFive
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
include d

/-- The original tilde generation lifts through the actual point line. -/
theorem closure_reduction_of_tilde (h : D.Hypothesis)
    (htilde : D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆) :
    D.UH = ⁅D.UH,D.L₁⁆ ∧ D.UH ≤ D.L₁.pCoreIn 2 ∧ D.UH ≤ D.L := by
  have hp : D.g2.V₁ ≤ ⁅D.g2.V,D.g2.L₁⁆ := by
    rw [h.g2_L₁]
    exact h.point_lt.le.trans (NormalBranch.seed_commutator h (seed_identity d h)).ge
  have ht : ⁅D.g2.tilde D.g2.U,D.g2.tilde D.g2.L₁⁆ = D.g2.tilde D.g2.U := by
    rw [h.g2_L₁]
    exact htilde.symm
  have he := U_eq_commutator_of_tilde h.g2_hypothesis hp ht
  have hc := U_le_local_core_of_tilde h.g2_hypothesis hp ht
  rw [h.g2_L₁] at he hc
  exact ⟨he,hc,hc.trans ((pCoreIn_le 2 D.L₁).trans ((map_subtype_le _).trans inf_le_left))⟩

theorem closure_image_eq_point_core_of_tilde (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (htilde : D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆)
    (hU : ¬ IsMulCommutative D.UH)
    (a : alternatingGroup (Fin 6))
    (ha : Section07.NaturalAction.image d D.V₁ = move a.val canonicalLine) :
    (D.UH.subgroupOf D.L).map (localMap d) =
      pointCoreEven.map (MulAut.conj a.val).toMonoidHom := by
  let A := (D.UH.subgroupOf D.L).map (localMap d)
  let R := (D.L₁.subgroupOf D.L).map (localMap d)
  have hLL : D.L₁ ≤ D.L := (map_subtype_le _).trans inf_le_left
  have hr : R = Theory.SpecificGroups.SymmetricSix.BinaryFlags.K.map
      (MulAut.conj a.val).toMonoidHom := local_residual_marking d h a ha
  have hcore : (D.L₁.pCoreIn 2).subgroupOf D.L = (D.L₁.subgroupOf D.L).pCoreIn 2 := by
    apply map_injective D.L.subtype_injective
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 D.L₁).trans hLL),
      map_pCoreIn_of_injective 2 _ D.L.subtype D.L.subtype_injective,
      map_subgroupOf_eq_of_le hLL]
  have hle : A ≤ pointCoreEven.map (MulAut.conj a.val).toMonoidHom := by
    have hh := map_mono (f := localMap d) (subgroupOf_mono D.L (closure_reduction_of_tilde d h htilde).2.1)
    rw [hcore, map_pCoreIn_of_ker_isPGroup (localMap d) (SourceStar.local_kernel_two d e)] at hh
    change A ≤ R.pCoreIn 2 at hh
    rw [hr, ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj a.val).injective,
      K_core_eq_pointCoreEven] at hh
    exact hh
  have hnorm : R ≤ normalizer (A : Set (Equiv.Perm (Fin 6))) := by
    have hN : D.L₁.subgroupOf D.L ≤ normalizer (D.UH.subgroupOf D.L : Set D.L) := by
      intro l hl
      apply mem_normalizer_iff.mpr
      intro u
      exact mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy D.Vplus D.H
        ((le_sup_left.trans h.local_le) hl)) u.val
    exact (map_mono hN).trans ((D.UH.subgroupOf D.L).le_normalizer_map (localMap d))
  let c := (MulAut.conj a.val⁻¹).toMonoidHom
  have hc (X : Subgroup (Equiv.Perm (Fin 6))) :
      (X.map (MulAut.conj a.val).toMonoidHom).map c = X := by
    rw [map_map]
    have he : c.comp (MulAut.conj a.val).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change a.val⁻¹*(a.val*x*a.val⁻¹)*(a.val⁻¹)⁻¹=x
      group
    rw [he,map_id]
  have hback : A.map c = pointCoreEven := by
    apply EvenPointCoreNormal.eq_pointCore_of_normalized
    · exact (map_mono hle).trans_eq (hc pointCoreEven)
    · intro hz
      have hb : A = ⊥ := (map_eq_bot_iff_of_injective A (f := c) (MulAut.conj a.val⁻¹).injective).mp hz
      exact closure_image_nontrivial d h (closure_reduction_of_tilde d h htilde).2.2 hU hb
    · have hh := (map_mono (f := c) hnorm).trans (A.le_normalizer_map c)
      rw [hr,hc] at hh
      exact hh
  apply map_injective (f := c) (MulAut.conj a.val⁻¹).injective
  rw [hback,hc]

theorem exists_five_pair_of_tilde (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (htilde : D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆)
    (hU : ¬ IsMulCommutative D.UH) :
    ∃ a : alternatingGroup (Fin 6),
      Section07.NaturalAction.image d D.V₁ = move a.val canonicalLine ∧
      ∃ g : D.L, localMap d g = a.val*FivePair.mover*a.val⁻¹ ∧
        g.val ∉ D.Gz ∧ localMap d g (a.val 5)=a.val 5 ∧
        NormalBranch.K D g.val ≤ D.L ∧
        ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
          FivePair.five.map (MulAut.conj a.val).toMonoidHom := by
  obtain ⟨a,ha,_⟩ := QuadraticSource.source_even_flag d
  have hr : a.val*FivePair.mover*a.val⁻¹ ∈ alternatingGroup (Fin 6) :=
    (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem _ FivePair.mover_mem.2 a.val
  have hrange : a.val*FivePair.mover*a.val⁻¹ ∈ (localMap d).range :=
    (localMap_range d).symm ▸ hr
  obtain ⟨g,hg⟩ := hrange
  have hUL := (closure_reduction_of_tilde d h htilde).2.2
  refine ⟨a,ha,g,hg,?_,?_,pair_inside hUL g,?_⟩
  · intro hz
    have hh := (ReturningPlane.localNormalizer_mem d D.V₁
      (h.point_lt.le.trans h.plus_le) g).mp (h.normalizer_point_eq.symm ▸ hz)
    rw [hg,ha,flagStabilizer_move,flagStabilizer_line] at hh
    have hc : FivePair.mover∈H1 := by
      have hs : (MulAut.conj a.val) FivePair.mover ∈ H1.map (MulAut.conj a.val).toMonoidHom := hh
      simpa only [MulEquiv.symm_apply_apply] using mem_map_equiv.mp hs
    exact FivePair.mover_moves_line hc
  · rw [hg]
    change a.val (FivePair.mover (a.val.symm (a.val 5)))=a.val 5
    rw [a.val.symm_apply_apply]
    exact congrArg a.val FivePair.mover_mem.1
  · rw [pair_image d hUL g,hg,closure_image_eq_point_core_of_tilde d h e htilde hU a ha]
    exact FivePair.marked_pair_generates a.val

theorem pair_twoPerfect_of_tilde (h : D.Hypothesis)
    (htilde : D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆)
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
    rw [(closure_reduction_of_tilde d h htilde).1]
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
theorem blockResidual_eq_pair_of_tilde (h : D.Hypothesis)
    (htilde : D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆)
    (g : D.L) (hLK : D.L₁ ≤ NormalBranch.K D g.val)
    (hgK : g.val ∈ normalizer (NormalBranch.K D g.val : Set G)) :
    blockResidual D g.val = NormalBranch.K D g.val := by
  have hh := embedded_pResidual_join_pGroup (NormalBranch.K D g.val) (D.LT.pCoreIn 2)
    (pair_twoPerfect_of_tilde d h htilde g hLK hgK) (isPGroup_pCoreIn 2 D.LT)
    (twoCore_normalizes_pair h g)
  change (pResidual 2 (D.LT.pCoreIn 2 ⊔ NormalBranch.K D g.val : Subgroup G)).map _ = _
  rw [sup_comm]
  exact hh

theorem exists_source_pair_of_tilde (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (htilde : D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆)
    (hU : ¬ IsMulCommutative D.UH) :
    ∃ (a : alternatingGroup (Fin 6)) (g : D.L), g.val ∉ D.Gz ∧
      g.val ∈ NormalBranch.K D g.val ∧ NormalBranch.K D g.val ≤ D.L ∧
      D.L₁ ≤ NormalBranch.K D g.val ∧ IsPPerfect 2 (NormalBranch.K D g.val) ∧
      blockResidual D g.val = NormalBranch.K D g.val ∧
      conjugateSpanBy D.V₁ (NormalBranch.K D g.val) = D.V ∧
      ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
        FivePair.five.map (MulAut.conj a.val).toMonoidHom := by
  obtain ⟨a,ha,g,hg,hgn,hfix,hKL,hi⟩ := exists_five_pair_of_tilde d h e htilde hU
  have hgi : localMap d g ∈ ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) := by
    rw [hi,hg]
    exact mem_map_of_mem (MulAut.conj a.val).toMonoidHom FivePair.mover_mem
  obtain ⟨k,hk,hkn,he,hpair⟩ := SourceInternalMover.exists_internal_mover d h e g hgi hgn
  have hLK := SourcePairResidual.local_le_pair d h e g a ha hi
  have hgnK := SourcePairResidual.mover_normalizes_pair d h e g hgi
  have hp := pair_twoPerfect_of_tilde d h htilde g hLK hgnK
  have hr := blockResidual_eq_pair_of_tilde d h htilde g hLK hgnK
  have hs := SourceFiveSpan.point_span d hKL a hi h
  refine ⟨a,k,hkn,hpair.symm ▸ hk,hpair.symm ▸ hKL,hpair.symm ▸ hLK,
    hpair.symm ▸ hp,?_,hpair.symm ▸ hs,?_⟩
  · change (pResidual 2 (D.LT.pCoreIn 2 ⊔ NormalBranch.K D k.val : Subgroup G)).map _ = _
    rw [hpair]
    exact hr
  · rw [hpair]
    exact hi

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.ClosurePair
