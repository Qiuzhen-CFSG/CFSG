module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalSylow.Source
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.BaumannNormalization

/-!
# The original A₅ branch of C.5.6(6)

C.1.16 normalizes the original blocks by Baum(R). Their actual Sylow
intersections, commutator movement and transitive orbit construct both
alternating setups. The one-block case is excluded by the Sylow section;
the two-block case gives the original half-Sylow stabilizer and its
noncentral replacement conjugator. No marking or action datum is assumed.

Source: Aschbacher–Smith C.5.3–6, printed pp.154–158.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
open ConjugateSource
variable {G : Type*} [Group G] [Finite G]
variable {H M K R T : Subgroup G}
variable (d : OriginalHypotheses H M K R T)
variable (b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))

private theorem alternating_setup (i : Fin b.size)
    (hi : IsAlternatingBlock ((b.block i).map H.subtype) 5)
    (L : Subgroup G) (hc : L ≤ centralizer ((b.block i).map H.subtype : Set G))
    (hp : ∀ r ∈ R, ((b.block i).map H.subtype).map (MulAut.conj r).toMonoidHom =
      (b.block i).map H.subtype ∨
      ((b.block i).map H.subtype).map (MulAut.conj r).toMonoidHom = L) :
    Nonempty (AlternatingPairSetup R ((b.block i).map H.subtype) L) := by
  obtain ⟨P,hP⟩ := d.block_sylow b i
  have hm : (b.block i).map H.subtype =
      ⁅(b.block i).map H.subtype,elementaryAbelianMaxJ R⁆ := by
    have he := congrArg (map H.subtype) (b.moved i)
    rw [map_commutator,←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le d.R_le_H] at he
    exact he
  exact exists_alternatingPairSetup R _ L d.R_twoGroup hi hm
    (d.baumann_normalizes_block b i) P hP hc hp

omit [Finite G] in
private theorem paired_blocks (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (r : G) (hr : r ∈ R) :
    ((b.block i).map H.subtype).map (MulAut.conj r).toMonoidHom =
      (b.block i).map H.subtype ∨
    ((b.block i).map H.subtype).map (MulAut.conj r).toMonoidHom =
      (b.block j).map H.subtype := by
  obtain ⟨k,hk⟩ := d.ambient_blocks_permuted b r (d.R_le hr) i
  have hi := i.isLt
  have hj := j.isLt
  have hh := k.isLt
  have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
  have hor : k = i ∨ k = j := by
    have hh' : k.val = i.val ∨ k.val = j.val := by omega
    exact hh'.imp Fin.ext Fin.ext
  rcases hor with rfl | rfl
  · exact Or.inl hk.symm
  · exact Or.inr hk.symm

omit [Finite G] in
private theorem commuting_blocks (i j : Fin b.size) (hij : i ≠ j) :
    (b.block i).map H.subtype ≤ centralizer ((b.block j).map H.subtype : Set G) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr (b.commute hij),Subgroup.map_bot]

private theorem alternating_type (i j : Fin b.size)
    (hi : IsAlternatingBlock ((b.block i).map H.subtype) 5) :
    IsAlternatingBlock ((b.block j).map H.subtype) 5 := by
  have hi' := ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv
    (equivMapOfInjective (b.block i) H.subtype H.subtype_injective).symm hi
  obtain ⟨t,_,he⟩ := b.transitive i j
  have hj := ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv
    (((MulAut.conj t⁻¹).subgroupMap (b.block i)).trans (MulEquiv.subgroupCongr he.symm)) hi'
  exact ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv
    (equivMapOfInjective (b.block j) H.subtype H.subtype_injective) hj

/-- Both literal A₅ setups for the two original source blocks. -/
theorem OriginalHypotheses.alternating_paired_setups
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map H.subtype) 5) :
    Nonempty (AlternatingPairSetup R ((b.block i).map H.subtype) ((b.block j).map H.subtype)) ∧
      Nonempty (AlternatingPairSetup R ((b.block j).map H.subtype) ((b.block i).map H.subtype)) := by
  exact ⟨alternating_setup d b i hi _
      (commuting_blocks d b j i (Ne.symm hij)) (paired_blocks d b i j hij hs),
    alternating_setup d b j (alternating_type d b i j hi) _
      (commuting_blocks d b i j hij) (paired_blocks d b j i (Ne.symm hij) hs)⟩

/-- C.5.6(6) in the actual alternating-five source branch. The original
block data construct both setups, including C.1.16 Baumann normalization. -/
theorem OriginalHypotheses.alternating_source_sylow
    (i : Fin b.size) (hi : IsAlternatingBlock ((b.block i).map H.subtype) 5)
    (P : Sylow 2 G) (hP : (P : Subgroup G) = T) :
    b.size = 2 ∧
      let T₁ := T ⊓ normalizer (ambientModule (b.block i) : Set G)
      T₁.relIndex T = 2 ∧ ∃ x ∈ M,
        x ∈ normalizer (T₁ : Set G) ∧ x ^ 2 ∈ T₁ ∧
        ¬ (ambientModule (b.block i)).map (MulAut.conj x⁻¹).toMonoidHom ≤
          centralizer (ambientModule (b.block i) : Set G) := by
  have hs : b.size = 1 ∨ b.size = 2 := by
    have := b.positive; have := b.size_le; omega
  rcases hs with hs | hs
  · have hnorm := d.single_block_normalized b i hs
    obtain ⟨h⟩ := alternating_setup d b i hi ⊥ bot_le (by
      intro r hr
      exact Or.inl (mem_normalizer_iff_map_conj_eq.mp (hnorm (d.R_le hr))))
    exact d.alternating_sylow_replacement b i ⊥ h (Or.inl (d.R_le.trans hnorm)) P hP
  · have hi' := i.isLt
    let j : Fin b.size := ⟨1-i.val,by omega⟩
    have hij : i ≠ j := by
      intro he
      have hv := congrArg Fin.val he
      dsimp only [j] at hv
      omega
    obtain ⟨h⟩ := alternating_setup d b i hi ((b.block j).map H.subtype)
      (commuting_blocks d b j i (Ne.symm hij)) (paired_blocks d b i j hij hs)
    obtain ⟨h'⟩ := alternating_setup d b j (alternating_type d b i j hi)
      ((b.block i).map H.subtype) (commuting_blocks d b i j hij)
      (paired_blocks d b j i (Ne.symm hij) hs)
    exact d.alternating_sylow_replacement b i _ h (Or.inr ⟨h'⟩) P hP

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
end
