module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalSylow.Orbit
public import CFSG.Quasithin.Chapter1.Section01

/-!
# Literal subgroup geometry for the original C.5.8 reduction

The two source blocks generate the original residual. Their transitive action
constructs an actual exchanging Sylow element outside the module stabilizer.
The original characteristic-two hypothesis and block core action supply the
remaining H and core-centralization inputs of C.5.9 on the same subgroups.

Source: Aschbacher–Smith C.5.3 and C.5.8–9, printed pp.154–155,160–161.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G]
variable {H M K R T : Subgroup G}
variable (d : OriginalHypotheses H M K R T)
variable (b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))

include d in
/-- The literal H is characteristic two, as required in the C.5.9 consumer. -/
theorem OriginalHypotheses.mem_He : H ∈ Chapter1.He G := by
  apply Chapter1.mem_He_iff.mpr
  rw [←d.fitting]
  exact centralizer_generalizedFitting_le H

/-- The actual H-core centralizes every original block module. -/
theorem OriginalHypotheses.core_centralizes_module (i : Fin b.size) :
    H.pCoreIn 2 ≤ centralizer (ambientModule (b.block i) : Set G) := by
  rintro _ ⟨q,hq,rfl⟩ _ ⟨v,hv,rfl⟩
  exact congrArg H.subtype ((b.type i).1.core_centralizes_blockU hq v hv)

omit [Finite G] in
/-- The original residual is the join of the two selected distinct blocks. -/
theorem OriginalHypotheses.pair_join (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2) :
    (b.block i).map H.subtype ⊔ (b.block j).map H.subtype = K := by
  have hgen : (⨆ k,b.block k) = b.block i ⊔ b.block j := by
    apply le_antisymm
    · apply iSup_le
      intro k
      have hi := i.isLt
      have hj := j.isLt
      have hk := k.isLt
      have hn : i.val ≠ j.val := fun he => hij (Fin.ext he)
      have hki : k = i ∨ k = j := by
        have hv : k.val = i.val ∨ k.val = j.val := by omega
        exact hv.imp Fin.ext Fin.ext
      rcases hki with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup _ i) (le_iSup _ j)
  rw [←Subgroup.map_sup,←hgen,b.generate,d.residual]

omit [Finite G] in
/-- Every original T-element permutes the actual selected pair of blocks. -/
theorem OriginalHypotheses.pair_action (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (t : G) (ht : t ∈ T) :
    ((b.block i).map H.subtype).conjBy t = (b.block i).map H.subtype ∨
    ((b.block i).map H.subtype).conjBy t = (b.block j).map H.subtype := by
  obtain ⟨k,hk⟩ := d.ambient_blocks_permuted b t ht i
  have hi := i.isLt
  have hj := j.isLt
  have hh := k.isLt
  have hn : i.val ≠ j.val := fun he => hij (Fin.ext he)
  have hor : k = i ∨ k = j := by
    have hh' : k.val = i.val ∨ k.val = j.val := by omega
    exact hh'.imp Fin.ext Fin.ext
  rcases hor with rfl | rfl
  · exact Or.inl hk.symm
  · exact Or.inr hk.symm

/-- A literal element of T exchanges the blocks and lies outside the
module stabilizer, without assuming an exchange coordinate. -/
theorem OriginalHypotheses.pair_exchange (i j : Fin b.size) (hij : i ≠ j) :
    ∃ t ∈ T, t ∉ T ⊓ normalizer (ambientModule (b.block i) : Set G) ∧
      ((b.block i).map H.subtype).conjBy t = (b.block j).map H.subtype := by
  obtain ⟨a,ha,he⟩ := b.transitive i j
  have ht : (a : G)⁻¹ ∈ T := T.inv_mem (d.sylow_image ▸ mem_map_of_mem H.subtype ha)
  have htK : ((b.block i).map H.subtype).conjBy (a : G)⁻¹ =
      (b.block j).map H.subtype := by
    change ((b.block i).map H.subtype).map (MulAut.conj (a : G)⁻¹).toMonoidHom = _
    rw [he,Subgroup.map_map,Subgroup.map_map]
    rfl
  refine ⟨(a : G)⁻¹,ht,?_,htK⟩
  intro hh
  have hU := mem_normalizer_iff_map_conj_eq.mp hh.2
  have hi := congrArg moduleLayer htK
  change moduleLayer (((b.block i).map H.subtype).map
    (MulAut.conj (a : G)⁻¹).toMonoidHom) = _ at hi
  rw [moduleLayer_map _ (MulAut.conj (a : G)⁻¹).injective,
    ←ambientModule_eq_literal,←ambientModule_eq_literal] at hi
  exact hij (d.ambient_modules_injective b (hU.symm.trans hi))

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
end
