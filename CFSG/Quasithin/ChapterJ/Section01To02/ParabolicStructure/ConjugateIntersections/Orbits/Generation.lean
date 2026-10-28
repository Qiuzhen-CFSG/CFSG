module

public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.ConjugateIntersections.Basic
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility
public import Theory.Representation.BinaryGroupAction
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Generation by the conjugates in J.2.2(5)

The L-conjugate span of U lies in S and contains V. Its image under the
literal Ru1 coordinates is an invariant subspace of the Steinberg module.
Since |U| = 32 > 8 = |V|, that image is nonzero. Irreducibility makes it
the entire module, and the coordinate kernel V already lies in the span.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(5), printed pp.432–433 (PDF pp.443–444).
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.ConjugateIntersections
open Subgroup Representation
variable {G : Type*} [Group G] [Finite G]

/-- The literal L-conjugates of U generate the whole special two-core S. -/
theorem conjugateSpan_eq_S (d : LocalSetup G) :
    conjugateSpan d.L d.toTypeRuSetup.U = d.toTypeRuSetup.S := by
  let C := conjugateSpan d.L d.toTypeRuSetup.U
  have hUC : d.toTypeRuSetup.U ≤ C := le_conjugateSpan _ _
  have hVC : d.V ≤ C := (le_conjugateSpan _ _).trans hUC
  have hCS : C ≤ d.toTypeRuSetup.S := iSup_le fun l => conjugateU_le_S d l l.property
  have hNC : d.L ≤ normalizer C := by
    change d.L ≤ normalizer ((⨆ l : d.L,
      d.toTypeRuSetup.U.map (MulAut.conj (l : G)).toMonoidHom : Subgroup G) : Set G)
    rw [← conjugateSpanBy_eq_iSup_conj]
    exact le_normalizer_conjugateSpanBy _ _
  let I : Subgroup (Multiplicative BinaryLinearThree.Steinberg) := (C.subgroupOf d.toTypeRuSetup.S).map d.ru1.steinberg.coordinates
  let M : Subrepresentation BinaryLinearThree.S := {
    toSubmodule := BinaryGroupAction.submoduleEquivSubgroup.symm I
    apply_mem_toSubmodule := by
      intro g v hv
      change Multiplicative.ofAdd v ∈ I at hv
      change Multiplicative.ofAdd (BinaryLinearThree.S g v) ∈ I
      obtain ⟨l, hl⟩ := d.ru1.quotient_surjective g
      obtain ⟨s, hs, hsv⟩ := hv
      let t : d.toTypeRuSetup.S := ⟨l * s * (l : G)⁻¹,
        (mem_normalizer_iff.mp (d.ru1.steinberg.normalized l.property) s).mp s.property⟩
      refine mem_map.mpr ⟨t, ?_, ?_⟩
      · exact (mem_normalizer_iff.mp (hNC l.property) s).mp hs
      · apply Multiplicative.toAdd.injective
        have he := d.ru1.steinberg.equivariant l s
        simpa only [t, MonoidHom.comp_apply, hl, hsv, toAdd_ofAdd] using he }
  rcases BinaryLinearThree.IrreducibleCatalogue.steinberg_irreducible.eq_bot_or_eq_top M
      with hM | hM
  · have hUV : d.toTypeRuSetup.U ≤ d.V := by
      intro u hu
      have huS := d.U_le_S hu
      have hm : (d.ru1.steinberg.coordinates ⟨u, huS⟩).toAdd ∈ M := by
        change d.ru1.steinberg.coordinates ⟨u, huS⟩ ∈ I
        exact mem_map.mpr ⟨⟨u, huS⟩, hUC hu, rfl⟩
      rw [hM] at hm
      exact (d.ru1.steinberg.coordinates_eq_one_iff _).mp hm
    have hc := card_le_of_le hUV
    rw [d.ru2.card_U d.card_Z, d.ru1.card_V] at hc
    omega
  · apply le_antisymm hCS
    intro s hs
    have hm : (d.ru1.steinberg.coordinates ⟨s, hs⟩).toAdd ∈ M := by
      rw [hM]
      trivial
    change d.ru1.steinberg.coordinates ⟨s, hs⟩ ∈ I at hm
    obtain ⟨c, hc, he⟩ := hm
    have hk : ((c⁻¹ * (⟨s, hs⟩ : d.toTypeRuSetup.S) : d.toTypeRuSetup.S) : G) ∈ d.V := by
      apply (d.ru1.steinberg.coordinates_eq_one_iff _).mp
      rw [map_mul, map_inv, he]
      exact inv_mul_cancel (d.ru1.steinberg.coordinates ⟨s, hs⟩)
    have ht := C.mul_mem hc (hVC hk)
    simpa using ht

end CFSG.Quasithin.ChapterJ.ConjugateIntersections
