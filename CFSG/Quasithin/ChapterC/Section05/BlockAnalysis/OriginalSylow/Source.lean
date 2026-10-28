module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalSylow.Orbit
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.SylowSource
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient.Sylow

/-!
# C.5.6(6) on the original block orbit

The original C.5.5 supplies a noncommuting conjugate, and the distinct block
modules supply the actual permutation action. Restrict the ambient Sylow
subgroup to M and apply the constructed rank-one or A₅ core-pair section.
The result has exactly two blocks, half-Sylow module stabilizer, and an
escaping element normalizing that stabilizer whose square lies in it.

Source: Aschbacher–Smith C.5.6(6) and the opening reduction of C.5.8,
printed pp.157–160. The source C.5.4 markings are the preceding inputs.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
open ConjugateSource ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
variable {H M K R T : Subgroup G}
variable (d : OriginalHypotheses H M K R T)
variable (b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))

private theorem module_half (i : Fin b.size) (hs : b.size = 2) :
    (T ⊓ normalizer (ambientModule (b.block i) : Set G)).relIndex T = 2 := by
  have hi := i.isLt
  let j : Fin b.size := ⟨1-i.val,by omega⟩
  have hij : i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    dsimp only [j] at hv
    omega
  obtain ⟨t,ht,hm⟩ := d.exists_moving_module b i hs
  simpa only [inf_relIndex_left] using normalizer_relIndex_eq_two_of_pair T
    (ambientModule (b.block i)) (ambientModule (b.block j)) (d.module_pair b i j hij hs) t ht hm

/-- The original rank-one or A₃ source setup forces two blocks and constructs
an escaping normalizer of their literal half-Sylow stabilizer. -/
theorem OriginalHypotheses.rankOne_sylow_replacement
    (i : Fin b.size) {F : Type*} [Field F]
    (h : Setup R ((b.block i).map H.subtype) F)
    (P : Sylow 2 G) (hP : (P : Subgroup G) = T) :
    b.size = 2 ∧
      let T₁ := T ⊓ normalizer (ambientModule (b.block i) : Set G)
      T₁.relIndex T = 2 ∧ ∃ x ∈ M,
        x ∈ normalizer (T₁ : Set G) ∧ x ^ 2 ∈ T₁ ∧
        ¬ (ambientModule (b.block i)).map (MulAut.conj x⁻¹).toMonoidHom ≤
          centralizer (ambientModule (b.block i) : Set G) := by
  let P' := P.subtype (hP ▸ d.T_le)
  have hP' : (P' : Subgroup M).map M.subtype = T := by
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (hP ▸ d.T_le),hP]
  have hu : U ((b.block i).map H.subtype) = ambientModule (b.block i) :=
    (ambientModule_eq_literal _).symm
  have hi := i.isLt
  let j : Fin b.size := ⟨b.size-1-i.val,by have := b.positive; omega⟩
  have hji (hs : b.size = 2) : i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    dsimp only [j] at hv
    omega
  obtain ⟨x,hx,hnc⟩ := d.exists_noncommuting_module b i
  have hn : ¬ (ambientModule (b.block i)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (ambientModule (b.block i) : Set G) := by
    intro hc
    exact hnc (by rw [commutator_comm]; exact commutator_eq_bot_iff_le_centralizer.mpr hc)
  obtain ⟨hs,he⟩ := h.source_C56_sylow M d.R_normal P' b.size
    (by have := b.positive; have := b.size_le; omega)
    (fun hs => hP'.symm ▸ d.single_block_normalized b i hs)
    (ambientModule (b.block j))
    (by intro hs; rw [hP',hu]; exact d.module_pair b i j (hji hs) hs)
    (by intro hs; rw [hP',hu]; exact d.exists_moving_module b i hs)
    (by rw [hP',hu]; exact d.module_stabilizer_le_block_normalizer b i)
    hx (hu.symm ▸ hn)
  refine ⟨hs,module_half d b i hs,?_⟩
  rw [hP',hu] at he
  obtain ⟨Q,_,_,y,hy,_,hyn,hys,hym⟩ := he
  exact ⟨y,(map_subtype_le _ hy).1,hyn,hys,hym⟩

/-- The same original Sylow replacement for an A₅ block. The source marking
is the actual C.5.4 setup; every orbit and moving-conjugate input is proved. -/
theorem OriginalHypotheses.alternating_sylow_replacement
    (i : Fin b.size) (L : Subgroup G)
    (h : AlternatingPairSetup R ((b.block i).map H.subtype) L)
    (hsource : R ≤ normalizer ((b.block i).map H.subtype : Set G) ∨
      Nonempty (AlternatingPairSetup R L ((b.block i).map H.subtype)))
    (P : Sylow 2 G) (hP : (P : Subgroup G) = T) :
    b.size = 2 ∧
      let T₁ := T ⊓ normalizer (ambientModule (b.block i) : Set G)
      T₁.relIndex T = 2 ∧ ∃ x ∈ M,
        x ∈ normalizer (T₁ : Set G) ∧ x ^ 2 ∈ T₁ ∧
        ¬ (ambientModule (b.block i)).map (MulAut.conj x⁻¹).toMonoidHom ≤
          centralizer (ambientModule (b.block i) : Set G) := by
  let P' := P.subtype (hP ▸ d.T_le)
  have hP' : (P' : Subgroup M).map M.subtype = T := by
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (hP ▸ d.T_le),hP]
  have hu : U ((b.block i).map H.subtype) = ambientModule (b.block i) :=
    (ambientModule_eq_literal _).symm
  have hi := i.isLt
  let j : Fin b.size := ⟨b.size-1-i.val,by have := b.positive; omega⟩
  have hji (hs : b.size = 2) : i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    dsimp only [j] at hv
    omega
  obtain ⟨x,hx,hnc⟩ := d.exists_noncommuting_module b i
  have hn : ¬ (ambientModule (b.block i)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (ambientModule (b.block i) : Set G) := by
    intro hc
    exact hnc (by rw [commutator_comm]; exact commutator_eq_bot_iff_le_centralizer.mpr hc)
  obtain ⟨hs,he⟩ := AlternatingQuotient.source_C56_sylow h hsource M d.R_normal P' b.size
    (by have := b.positive; have := b.size_le; omega)
    (fun hs => hP'.symm ▸ d.single_block_normalized b i hs)
    (ambientModule (b.block j))
    (by intro hs; rw [hP',hu]; exact d.module_pair b i j (hji hs) hs)
    (by intro hs; rw [hP',hu]; exact d.exists_moving_module b i hs)
    (by rw [hP',hu]; exact d.module_stabilizer_le_block_normalizer b i)
    hx (hu.symm ▸ hn)
  refine ⟨hs,module_half d b i hs,?_⟩
  rw [hP',hu] at he
  obtain ⟨Q,_,_,y,hy,_,hyn,hys,hym⟩ := he
  exact ⟨y,(map_subtype_le _ hy).1,hyn,hys,hym⟩

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
end
