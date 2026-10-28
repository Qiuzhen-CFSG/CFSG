module

public import Theory.Representation.BinaryDuadModule.IncidenceRank
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The line-relation quotient of the duad module

The sum of the fifteen line indicators is the constant vector. Their span is
the direct sum of the line-complement span and the constant line. Restricting
the quotient map to the even core therefore gives an explicit equivariant
isomorphism U₀/D ≃ U/⟨L⟩, compatible with the original quotient maps.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.5.3,
printed pp.343–345 (PDF pp.354–356).
-/

@[expose] public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation BinaryDuadModule
namespace BinaryDuadStructure

def line (s : Syntheme) : Full Duad := fun d => if incident d s then 1 else 0

def lineSpan : Submodule (ZMod 2) (Full Duad) :=
  Submodule.span (ZMod 2) (Set.range line)

theorem line_add_complement (s : Syntheme) :
    line s + lineComplement s = allOne Duad := by
  ext d
  change (if incident d s then (1 : ZMod 2) else 0) +
    (if incident d s then 0 else 1) = 1
  split_ifs <;> simp

theorem sum_lines : ∑ s : Syntheme, line s = allOne Duad := by decide

theorem allOne_mem_lineSpan : allOne Duad ∈ lineSpan := by
  rw [← sum_lines]
  exact Submodule.sum_mem _ (fun s _ => Submodule.subset_span (Set.mem_range_self s))

theorem lineComplementSpan_le_lineSpan : lineComplementSpan ≤ lineSpan := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, rfl⟩
  have he : lineComplement s = allOne Duad - line s := by
    rw [← line_add_complement s]; abel
  rw [he]
  exact lineSpan.sub_mem allOne_mem_lineSpan (Submodule.subset_span (Set.mem_range_self s))

theorem lineSpan_eq_sup : lineSpan = lineComplementSpan ⊔ constants Duad := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    have he : line s = allOne Duad - lineComplement s := by
      rw [← line_add_complement s]; abel
    rw [he]
    exact Submodule.sub_mem _
      (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _)))
      (Submodule.mem_sup_left (Submodule.subset_span (Set.mem_range_self s)))
  · refine sup_le lineComplementSpan_le_lineSpan ?_
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr allOne_mem_lineSpan)

theorem lineSpan_inf_core : lineSpan ⊓ core Duad = lineComplementSpan := by
  apply le_antisymm
  · intro u hu
    obtain ⟨d, hd, c, hc, he⟩ := Submodule.mem_sup.mp (lineSpan_eq_sup ▸ hu.1)
    have hc0 : c ∈ core Duad := by
      have h := (core Duad).sub_mem hu.2 (lineComplementSpan_le_core hd)
      rw [← he] at h
      simpa using h
    have hz : c = 0 := Submodule.disjoint_def.mp
      (core_isCompl_constants Duad (by decide)).disjoint c hc0 hc
    have hdu : d = u := by simpa [hz] using he
    exact hdu ▸ hd
  · exact le_inf lineComplementSpan_le_lineSpan lineComplementSpan_le_core

theorem lineSpan_invariant (g : A6) {u : Full Duad} (hu : u ∈ lineSpan) :
    alternatingPointAction g u ∈ lineSpan := by
  rw [lineSpan_eq_sup] at hu ⊢
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hu
  rw [map_add]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (lineComplementSpan_invariant g.val hv))
    (Submodule.mem_sup_right (constants_invariant Duad
      (MulAction.toPermHom S6 Duad g.val) hw))

noncomputable def coreAction : Representation (ZMod 2) A6 (core Duad) :=
  (coreRepresentation Duad).comp (MulAction.toPermHom A6 Duad)

abbrev CoreRelations := lineComplementSpan.comap (core Duad).subtype
abbrev LineQuotient := Full Duad ⧸ lineSpan
abbrev CoreQuotient := core Duad ⧸ CoreRelations

noncomputable def lineQuotientAction : Representation (ZMod 2) A6 LineQuotient :=
  Representation.quotient alternatingPointAction lineSpan (fun g _ hu => lineSpan_invariant g hu)

noncomputable def coreQuotientAction : Representation (ZMod 2) A6 CoreQuotient :=
  coreAction.quotient CoreRelations (fun g _ hu => lineComplementSpan_invariant g.val hu)

def coreToLineQuotient : core Duad →ₗ[ZMod 2] LineQuotient :=
  lineSpan.mkQ.comp (core Duad).subtype

theorem coreToLineQuotient_ker : coreToLineQuotient.ker = CoreRelations := by
  ext u
  change lineSpan.mkQ u.val = 0 ↔ u.val ∈ lineComplementSpan
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro h
    have : u.val ∈ lineSpan ⊓ core Duad := ⟨h, u.property⟩
    rwa [lineSpan_inf_core] at this
  · exact fun h => lineComplementSpan_le_lineSpan h

theorem coreToLineQuotient_surjective : Function.Surjective coreToLineQuotient := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ u =>
    let v := u - augmentation Duad u • allOne Duad
    have hv : v ∈ core Duad := by
      change augmentation Duad v = 0
      have hone : augmentation Duad (allOne Duad) = 1 := by decide
      simp only [v, map_sub, map_smul, hone, smul_eq_mul, mul_one, sub_self]
    refine ⟨⟨v, hv⟩, ?_⟩
    change lineSpan.mkQ v = lineSpan.mkQ u
    simp only [v, map_sub, map_smul]
    rw [show lineSpan.mkQ (allOne Duad) = 0 from
      (Submodule.Quotient.mk_eq_zero lineSpan).mpr allOne_mem_lineSpan]
    simp

noncomputable def coreLineEquiv : CoreQuotient ≃ₗ[ZMod 2] LineQuotient :=
  (Submodule.quotEquivOfEq _ _ coreToLineQuotient_ker.symm).trans
    (coreToLineQuotient.quotKerEquivOfSurjective coreToLineQuotient_surjective)

@[simp] theorem coreLineEquiv_mk (u : core Duad) :
    coreLineEquiv (CoreRelations.mkQ u) = lineSpan.mkQ u.val := rfl

theorem coreLineEquiv_equivariant (g : A6) (u : CoreQuotient) :
    coreLineEquiv (coreQuotientAction g u) = lineQuotientAction g (coreLineEquiv u) := by
  induction u using Submodule.Quotient.induction_on with
  | _ u => rfl

theorem lineQuotient_finrank : Module.finrank (ZMod 2) LineQuotient = 5 := by
  rw [← coreLineEquiv.finrank_eq]
  exact core_quotient_lineComplementSpan_finrank

end BinaryDuadStructure
