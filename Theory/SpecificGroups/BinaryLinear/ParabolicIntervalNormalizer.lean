module
public import Theory.SpecificGroups.BinaryLinear.RadicalFlagClosure
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.AutomorphismModel.Structure
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Normalizers between binary parabolic cores and Sylow subgroups

A parabolic contains the elementary radical of each retained flag cut.
If its core is conjugated into the original Sylow subgroup, each such
radical recovers the cut of the same dimension, forcing the conjugator
into the parabolic. This controls normalizers of all intermediate subgroups.

For a normal binary linear subgroup, apply the calculation to the actual
intersection with the Sylow overgroup. If the ambient group is generated
by that normal subgroup and the Sylow, the same control holds for every
intermediate subgroup normalized by the Sylow. The full automorphism
groups of PSL₄(2) and PSL₅(2) satisfy this generation condition because
the inner subgroup has index two. The final theorem lifts the result
through a given surjection with two-group kernel.

Source application: Aschbacher--Smith, original 14.6.16, printed p.1035.
This proves the interval control used there directly from binary flag
geometry, without assuming the general Lie-type weak-closure theorem I.2.5.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace BinaryLinear
open OuterCyclic InvariantNodeActions

/-- A returning parabolic radical forces its conjugator into the parabolic. -/
theorem mem_of_core_conjugate_le_sylow {m : ℕ}
    (T : Sylow 2 (LinearGroup (m+1))) (B : Subgroup (LinearGroup (m+1)))
    (hTB : (T : Subgroup _) ≤ B) (g : LinearGroup (m+1))
    (hg : (B.pCoreIn 2).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup _)) : g ∈ B := by
  obtain ⟨b,c,hT,rfl⟩ := SylowFlagOvergroups.exists_flag_of_sylow_le T B hTB
  rw [hT] at hg
  have hcut (i : Fin m) (hi : i ∈ c) :
      (cutSpace b i).map g.toLinearMap = cutSpace b i := by
    apply eq_cut_of_radical_le_fullFlag b _ i
    · have hp := inner_map_parabolic (cutSpace b i) g
      rw [←radical_map_of_parabolic_map _ _ _ hp]
      exact (map_mono (cut_radical_le_core b c hi)).trans hg
    · rw [LinearEquiv.finrank_map_eq,cutSpace_finrank]
  rw [mem_cutStabilizer_maps]
  intro i hi v hv
  rw [←hcut i hi]
  exact Submodule.mem_map_of_mem hv

/-- The same radical argument controls every intermediate normalizer. -/
theorem interval_normalizer_le {m : ℕ}
    (T : Sylow 2 (LinearGroup (m+1))) (B U : Subgroup (LinearGroup (m+1)))
    (hTB : (T : Subgroup _) ≤ B) (hcore : B.pCoreIn 2 ≤ U)
    (hUT : U ≤ (T : Subgroup _)) : normalizer (U : Set _) ≤ B := by
  intro g hg
  apply mem_of_core_conjugate_le_sylow T B hTB g
  exact ((map_mono hcore).trans_eq (mem_normalizer_iff_map_conj_eq.mp hg)).trans hUT

end BinaryLinear

namespace BinaryLinear
open OuterCyclic
variable {G : Type*} [Group G] [Finite G]

/-- A normal binary-linear subgroup controls the normalizer inside that subgroup. -/
theorem normal_linear_interval_normalizer_le {m : ℕ}
    (N : Subgroup G) [N.Normal] (e : N ≃* LinearGroup (m+1))
    (T : Sylow 2 G) (B U : Subgroup G) (hTB : (T : Subgroup G) ≤ B)
    (hcore : B.pCoreIn 2 ≤ U) (hUT : U ≤ (T : Subgroup G)) :
    N ⊓ normalizer (U : Set G) ≤ B := by
  obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_normal N
  let D := B ⊓ N
  have hDN : D ≤ N := inf_le_right
  have hDB : D ≤ B := inf_le_left
  have hn : B ≤ normalizer (D : Set G) := by
    apply (le_inf B.le_normalizer ?_).trans inf_normalizer_le_normalizer_inf
    simp only [normalizer_eq_top,le_top]
  have hDC : D.pCoreIn 2 ≤ B.pCoreIn 2 := pCoreIn_mono_of_normalizes hDB hn
  have heC : (B.subgroupOf N).pCoreIn 2 = (D.pCoreIn 2).subgroupOf N := by
    have hBN : B.subgroupOf N = D.subgroupOf N := by
      ext x
      exact ⟨fun hx => ⟨hx,x.property⟩,fun hx => hx.1⟩
    rw [hBN,pCoreIn_subgroupOf 2 D N hDN]
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let B' := (B.subgroupOf N).map e.toMonoidHom
  let U' := (U.subgroupOf N).map e.toMonoidHom
  have hPB : (P' : Subgroup _) ≤ B' := map_mono (by
    rw [hP]
    exact subgroupOf_mono N hTB)
  have hCU : B'.pCoreIn 2 ≤ U' := by
    rw [←map_pCoreIn_of_injective 2 _ e.toMonoidHom e.injective,heC]
    exact map_mono (subgroupOf_mono N (hDC.trans hcore))
  have hUP : U' ≤ (P' : Subgroup _) := map_mono (by
    rw [hP]
    exact subgroupOf_mono N hUT)
  intro g hg
  let x : N := ⟨g,hg.1⟩
  have hx : x ∈ normalizer (U.subgroupOf N : Set N) := by
    exact U.le_normalizer_comap N.subtype hg.2
  have hex : e x ∈ normalizer (U' : Set _) :=
    (U.subgroupOf N).le_normalizer_map e.toMonoidHom (mem_map_of_mem _ hx)
  have hmem := interval_normalizer_le P' B' U' hPB hCU hUP hex
  have hh : x ∈ B.subgroupOf N := by
    simpa only [B',mem_map_equiv,e.symm_apply_apply] using hmem
  exact hh

/-- If the normal binary-linear subgroup and the Sylow generate, an invariant
intermediate subgroup has its full normalizer in the original Sylow overgroup. -/
theorem linear_extension_interval_normalizer_le {m : ℕ}
    (N : Subgroup G) [N.Normal] (e : N ≃* LinearGroup (m+1))
    (T : Sylow 2 G) (hgen : N ⊔ (T : Subgroup G) = ⊤)
    (B U : Subgroup G) (hTB : (T : Subgroup G) ≤ B)
    (hcore : B.pCoreIn 2 ≤ U) (hUT : U ≤ (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (U : Set G)) : normalizer (U : Set G) ≤ B := by
  intro g hg
  have hprod : (g : G) ∈ (N : Set G) * ((T : Subgroup G) : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left N (T : Subgroup G) (by simp [normalizer_eq_top]),hgen]
    exact mem_top g
  obtain ⟨n,hnN,t,ht,rfl⟩ := hprod
  have hnU : n ∈ normalizer (U : Set G) :=
    ((normalizer (U : Set G)).mul_mem_cancel_right (hn ht)).mp hg
  exact B.mul_mem (normal_linear_interval_normalizer_le N e T B U hTB hcore hUT ⟨hnN,hnU⟩) (hTB ht)

end BinaryLinear

namespace BinaryLinear
open OuterCyclic BinaryNaturalDual.ModelOrbits.AutomorphismModel

private instance finite_linear (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

/-- Binary degree-four/five automorphism groups inherit the parabolic interval control. -/
theorem automorphism_interval_normalizer_le {n : ℕ} (hn : n = 4 ∨ n = 5)
    (T : Sylow 2 (MulAut (LinearGroup n))) (B U : Subgroup (MulAut (LinearGroup n)))
    (hTB : (T : Subgroup _) ≤ B) (hcore : B.pCoreIn 2 ≤ U)
    (hUT : U ≤ (T : Subgroup _)) (hTU : (T : Subgroup _) ≤ normalizer (U : Set (MulAut (LinearGroup n)))) :
    normalizer (U : Set (MulAut (LinearGroup n))) ≤ B := by
  let N := MulAut.innerSubgroup (LinearGroup n)
  let q := QuotientGroup.mk' N
  have hp : IsPGroup 2 (MulAut.Outer (LinearGroup n)) := by
    apply IsPGroup.of_card (n := 1)
    rw [←index_eq_card,inner_index hn]
    rfl
  let P := T.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  have htop : (P : Subgroup (MulAut.Outer (LinearGroup n))) = ⊤ :=
    (P.is_maximal' (hp.to_subgroup ⊤) le_top).symm
  have hgen : N ⊔ (T : Subgroup _) = ⊤ := by
    have hh := congrArg (comap q) htop
    change ((T : Subgroup _).map q).comap q = (⊤ : Subgroup _).comap q at hh
    rwa [comap_map_eq,QuotientGroup.ker_mk',comap_top,sup_comm] at hh
  have e := (innerEquiv (show 0 < n by omega)).symm
  rcases hn with rfl | rfl
  · exact linear_extension_interval_normalizer_le N e T hgen B U hTB hcore hUT hTU
  · exact linear_extension_interval_normalizer_le N e T hgen B U hTB hcore hUT hTU

variable {G : Type*} [Group G] [Finite G]
/-- The interval normalizer theorem lifts through a literal surjection with two-group kernel. -/
theorem automorphism_cover_interval_normalizer_le {n : ℕ} (hn : n = 4 ∨ n = 5)
    (f : G →* MulAut (LinearGroup n)) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (T : Sylow 2 G) (B U : Subgroup G)
    (hTB : (T : Subgroup G) ≤ B) (hcore : B.pCoreIn 2 ≤ U)
    (hUT : U ≤ (T : Subgroup G)) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G)) :
    normalizer (U : Set G) ≤ B := by
  let P := T.mapSurjective hf
  have hcore' : (B.map f).pCoreIn 2 ≤ U.map f := by
    rw [←map_pCoreIn_of_ker_isPGroup f hk B]
    exact map_mono hcore
  have hTU' : (P : Subgroup (MulAut (LinearGroup n))) ≤
      normalizer (U.map f : Set (MulAut (LinearGroup n))) :=
    (map_mono hTU).trans (U.le_normalizer_map f)
  have hn' := automorphism_interval_normalizer_le hn P (B.map f) (U.map f)
    (map_mono hTB) hcore' (map_mono hUT) hTU'
  have hkerB : f.ker ≤ B := (hk.le_sylow_of_normal T).trans hTB
  intro x hx
  have hh := hn' (U.le_normalizer_map f (mem_map_of_mem f hx))
  have : x ∈ (B.map f).comap f := hh
  rwa [comap_map_eq_self hkerB] at this
end BinaryLinear
