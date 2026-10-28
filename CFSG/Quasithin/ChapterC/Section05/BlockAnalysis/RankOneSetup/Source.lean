module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.RankOneSetup.Restriction
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.BaumannNormalization
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.LocalSource
/-!
# The original C.5.4 rank-one source consumer

The actual C.5.3 family supplies the block type, movement equation and full
Sylow intersection. C.1.16 supplies Baumann normalization. These facts
construct every rank-one setup field for the original embedded block;
no marked action, quotient or Sylow conclusion is taken as a premise.
The remaining A₅ branch feeds the separately proved alternating setup.

Source: Aschbacher–Smith C.5.3–5, printed pp.154–155.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
open ConjugateSource.RankOne
universe u
variable {G : Type u} [Group G] [Finite G] {H M K R T : Subgroup G}

/-- Original C.5.4(2), on the literal block image in G. -/
theorem OriginalHypotheses.rankOne_setup
    (d : OriginalHypotheses H M K R T)
    (b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))
    (i : Fin b.size)
    (htype : (∃ n, IsL2EvenBlock ((b.block i).map H.subtype) n) ∨
      IsAlternatingBlock ((b.block i).map H.subtype) 3) :
    ∃ (F : Type) (_ : Field F), Nonempty (Setup R ((b.block i).map H.subtype) F) := by
  have hm : (b.block i).map H.subtype =
      ⁅(b.block i).map H.subtype,elementaryAbelianMaxJ R⁆ := by
    have he := congrArg (Subgroup.map H.subtype) (b.moved i)
    rw [map_commutator,←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le d.R_le_H] at he
    exact he
  obtain ⟨P,hP⟩ := d.block_sylow b i
  exact exists_rankOne_setup R _ d.R_twoGroup htype hm (d.baumann_normalizes_block b i) P hP

/-- The exact original alternatives feeding the rank-one and alternating
C.5.6 producers, with the rank-one setup now fully constructed. -/
theorem OriginalHypotheses.rankOne_setup_or_alternating
    (d : OriginalHypotheses H M K R T)
    (b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))
    (i : Fin b.size) :
    (∃ (F : Type) (_ : Field F), Nonempty (Setup R ((b.block i).map H.subtype) F)) ∨
      IsAlternatingBlock ((b.block i).map H.subtype) 5 := by
  have ht := chiZero_equiv (equivMapOfInjective (b.block i) H.subtype H.subtype_injective) (b.type i).2
  rcases ht with hl | ha | ha
  · exact Or.inl (d.rankOne_setup b i (Or.inl hl))
  · exact Or.inl (d.rankOne_setup b i (Or.inr ha))
  · exact Or.inr ha

/-- C.5.1–2 construct the block family, its original marked rank-one
alternatives and the escaping conjugate, using only SQTK of the local H
and the independently owned genuine earlier C.1.28 source. -/
theorem OriginalHypotheses.blocks_setups_and_noncommuting_conjugate
    (d : OriginalHypotheses H M K R T) {𝒦 : GroupClass.{u}}
    (outside : C128Outside 𝒦) (hH : IsSQTK 𝒦 H) :
    ∃ b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H),
      (∀ i, (∃ (F : Type) (_ : Field F), Nonempty (Setup R ((b.block i).map H.subtype) F)) ∨
        IsAlternatingBlock ((b.block i).map H.subtype) 5) ∧
      ∃ i₀ : Fin b.size, ∃ x ∈ M,
        ⁅moduleLayer ((b.block i₀).map H.subtype),
          (moduleLayer ((b.block i₀).map H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom⁆ ≠ ⊥ := by
  obtain ⟨b,i,x,hx,hnc⟩ := d.blocks_and_noncommuting_conjugate_of_local outside hH
  exact ⟨b,d.rankOne_setup_or_alternating b,i,x,hx,hnc⟩

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
