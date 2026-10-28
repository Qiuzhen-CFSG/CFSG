module
public import CFSG.Quasithin.ChapterC.Section06.Original.ModelSQTK
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.KnownSimpleSource
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Solvable
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ChiTransport
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalSylow.Geometry

/-!
# The quotient-model sieve on the actual C.5 block orbit

The binary linear residual has three-rank at most one, forcing a single
block. In the two solvable model rows every chi-zero block is A₃. Thus
the only paired orbit consists of two actual A₃ blocks. The original
Fitting action also identifies the centralizer of their module join with
O₂(H), discharging the remaining paired-source geometry input.
Source: Aschbacher--Smith C.6.1(2),(5), printed pp.164--165.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section06.Original
variable {A : Type*} [Group A] [Finite A]

omit [Finite A] in
theorem chiZero_cubic_of_solvable [Group.IsSolvable A] (h : IsChiZeroBlock A) :
    IsAlternatingBlock A 3 := by
  rcases h with ⟨n,hn⟩ | h3 | h5
  · exact hn.not_solvable.elim
  · exact h3
  · obtain ⟨e⟩ := h5.2.2.quotient_iso
    let : Group.IsSolvable (alternatingGroup (Fin 5)) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance).elim

open Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G] {H M K R T : Subgroup G}

theorem orbit_alternatives (c : OriginalHypotheses H M K R T)
    (hm : QuotientModels H)
    (b : OrbitDecomposition (c.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H)) :
    b.size = 1 ∨ b.size = 2 ∧ ∀ i, IsAlternatingBlock (b.block i) 3 := by
  by_cases hs : b.size = 1
  · exact Or.inl hs
  right
  have hs2 : b.size = 2 := by have := b.positive; have := b.size_le; omega
  refine ⟨hs2,?_⟩
  change (∃ n, ClassicalGroup.IsPSL (pResidual 2 (H ⧸ pCore 2 H)) 2 (2^n)) ∨
    Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∨
    Nonempty ((H ⧸ pCore 2 H) ≃* CubicWreath) at hm
  rcases hm with ⟨n,hn⟩ | hc
  · have hcard := RankOne.ChiProduct.card_le_threeRank
      (RankOne.ChiProduct.blockCommutationHypothesis_of_fitting c.fitting)
      b.block b.injective (fun i => (b.type i).chi)
    have hr := linear_core_odd_rank (p := 3) (by decide) hn
    simp only [Fintype.card_fin,hs2] at hcard
    omega
  · let : Group.IsSolvable H := cubic_models_solvable hc
    intro i
    exact chiZero_cubic_of_solvable (b.type i).2

omit [Finite G] in
theorem single_block_eq_residual (c : OriginalHypotheses H M K R T)
    (b : OrbitDecomposition (c.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))
    (i : Fin b.size) (hs : b.size = 1) : (b.block i).map H.subtype = K := by
  have hgen : b.block i = pResidual 2 H := by
    apply Eq.trans ?_ b.generate
    apply le_antisymm (le_iSup _ i)
    apply iSup_le
    intro j
    have hj : j = i := Fin.ext (by have := j.isLt; have := i.isLt; omega)
    rw [hj]
  rw [hgen,c.residual]

theorem pair_core_centralizer (c : OriginalHypotheses H M K R R)
    (b : OrbitDecomposition (c.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2) :
    R ⊓ centralizer ((ambientModule (b.block i) ⊔ ambientModule (b.block j) : Subgroup G) : Set G) =
      H.pCoreIn 2 := by
  have hgen : (⨆ k, ambientModule (b.block k)) = ambientModule (b.block i) ⊔ ambientModule (b.block j) := by
    apply le_antisymm
    · apply iSup_le
      intro k
      have hk : k = i ∨ k = j := by
        have hv : i.val ≠ j.val := fun he => hij (Fin.ext he)
        have : k.val = i.val ∨ k.val = j.val := by
          have := i.isLt; have := j.isLt; have := k.isLt; omega
        exact this.imp Fin.ext Fin.ext
      rcases hk with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup (fun k => ambientModule (b.block k)) i) (le_iSup (fun k => ambientModule (b.block k)) j)
  apply le_antisymm
  · intro x hx
    have hxH := c.R_le_H hx.1
    have hxC : (⟨x,hxH⟩ : H) ∈
        centralizer ((⨆ k,moduleLayer (b.block k) : Subgroup H) : Set H) := by
      intro y hy
      apply Subtype.ext
      apply hx.2
      have hy' := mem_map_of_mem H.subtype hy
      rw [Subgroup.map_iSup] at hy'
      exact hgen ▸ hy'
    exact mem_map_of_mem H.subtype
      (centralizer_moduleJoin_le_core b.block (fun k => (b.type k).1) c.fitting b.generate hxC)
  · refine le_inf ?_ ?_
    · simpa only [c.sylow_image] using pCoreIn_le_sylow H c.sylow
    · apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp (c.core_centralizes_module b i))
        (le_centralizer_iff.mp (c.core_centralizes_module b j))
end CFSG.Quasithin.ChapterC.Section06.Original
