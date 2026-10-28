module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.Constituents
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.Extensions.PerfectCover
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.Extensions.WholeCommutator
public import Theory.Representation.BinaryOffender.SingleNoncentralFlag

/-!
# Extension deductions for strong orthogonal sections

The imported results recognize a perfect central cover of the marked natural
module as the natural module or its augmentation cover, retain the literal
commutator inclusion, and prove [W,H] = [W,K] from U = [U,K] and a marked
natural quotient U/W. The cohomology and cover comparisons used here are
proved results, rather than extra classification premises.

The unique natural factor now produces the literal central-cover witness from
`[W,K]`, including full commutator generation and indecomposability on `K`.
The source wrappers in `Extensions/SourceBranches.lean` retain the genuine
earlier setup and offender hypotheses for both strong branches.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, 13.8.25,
printed p.960, PDF p.977 (1 March 2004 manuscript).
-/

@[expose] public section

open Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections.Extensions

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

private lemma natural_actor_moves :
    ∃ g : alternatingGroup (Fin 8), ∃ v : natural (Fin 8),
      naturalRepresentation (Fin 8) g.val v ≠ v := by
  let g0 : Perm := Equiv.swap 0 1 * Equiv.swap 2 3
  have hg0 : g0 ∈ alternatingGroup (Fin 8) := by
    exact Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
      (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
      (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
  let g : alternatingGroup (Fin 8) := ⟨g0, hg0⟩
  let x : Full (Fin 8) := Pi.single 0 1 + Pi.single 2 1
  have hx : x ∈ core (Fin 8) := by
    change augmentation (Fin 8) x = 0
    decide +kernel
  let v : natural (Fin 8) := coreToNatural (Fin 8) ⟨x, hx⟩
  refine ⟨g, v, ?_⟩
  intro heq
  have hq : (constants (Fin 8)).mkQ (representation (Fin 8) g0 x) =
      (constants (Fin 8)).mkQ x := by
    have hh := congrArg Subtype.val heq
    change (constants (Fin 8)).mkQ (representation (Fin 8) g0 x) =
      (constants (Fin 8)).mkQ x at hh
    exact hh
  have hc : representation (Fin 8) g0 x - x ∈ constants (Fin 8) := by
    apply (Submodule.Quotient.mk_eq_zero (constants (Fin 8))).mp
    change (constants (Fin 8)).mkQ (representation (Fin 8) g0 x - x) = 0
    rw [map_sub, hq, sub_self]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hc
  have hc4 := congrFun hc (4 : Fin 8)
  have hc0 := congrFun hc (0 : Fin 8)
  simp [allOne, x, representation] at hc4 hc0
  exact zero_ne_one (hc4.symm.trans hc0)

private lemma component_normal_of_marking (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8)) : K.Normal := by
  have he : K = (alternatingGroup (Fin 8)).comap eH.toMonoidHom := by
    ext k
    change k ∈ K ↔ eH k ∈ alternatingGroup (Fin 8)
    rw [← hK]
    exact (Subgroup.mem_map_iff_mem eH.injective).symm
  rw [he]
  infer_instance

omit [FiniteDimensional (ZMod 2) U] in
private lemma natural_factor_noncentral (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    {L N : Subrepresentation ρ}
    (hN : IsEightNatural (sectionRepresentation ρ L N) eH) :
    ∃ k ∈ K, ∃ v, sectionRepresentation ρ L N k v ≠ v := by
  obtain ⟨e, he⟩ := hN
  obtain ⟨g, v, hgv⟩ := natural_actor_moves
  have hgmem : (g : Perm) ∈ alternatingGroup (Fin 8) := g.property
  have hmap : (g : Perm) ∈ K.map eH.toMonoidHom := by
    rw [hK]
    exact hgmem
  obtain ⟨k, hk, hek⟩ := hmap
  have hke : eH k = g := hek
  refine ⟨k, hk, e.symm v, ?_⟩
  intro hz
  apply hgv
  have hh := he k (e.symm v)
  rw [hz] at hh
  simpa [hke] using hh.symm

private theorem flag_witness_of_unique_natural
    (ρ : Representation (ZMod 2) H U) (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (s : NaturalCentralSeries ρ K eH) (i : ℕ) (hi : i < s.length)
    (hNi : IsEightNatural (sectionRepresentation ρ (s.space i) (s.space (i + 1))) eH)
    (huniq : ∀ j < s.length,
      IsEightNatural (sectionRepresentation ρ (s.space j) (s.space (j + 1))) eH → j = i)
    (hirr : IsIrreducible
      ((sectionRepresentation ρ (s.space i) (s.space (i + 1))).comp K.subtype)) :
    Nonempty (SingleNoncentralFlagWitness ρ K s.space i s.length) := by
  let : K.Normal := component_normal_of_marking eH K hK
  let : Group.IsPerfect K := perfect_component_of_marking eH K hK
  have hcentral : ∀ j < s.length, j ≠ i → ∀ k ∈ K, ∀ v,
      sectionRepresentation ρ (s.space j) (s.space (j + 1)) k v = v := by
    intro j hj hji
    rcases s.factors j hj with hfix | hnat
    · exact hfix
    · exact (hji (huniq j hj hnat)).elim
  exact singleNoncentralFlag ρ K s.space i s.length s.monotone s.first s.last hi
    hcentral hirr (natural_factor_noncentral ρ eH K hK hNi)

/-- The literal commutator subrepresentation obtained from a unique marked
natural factor, together with the full single-factor witness. -/
theorem natural_series_single_noncentral_flag
    (ρ : Representation (ZMod 2) H U) (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (s : NaturalCentralSeries ρ K eH) (i : ℕ) (hi : i < s.length)
    (hNi : IsEightNatural (sectionRepresentation ρ (s.space i) (s.space (i + 1))) eH)
    (huniq : ∀ j < s.length,
      IsEightNatural (sectionRepresentation ρ (s.space j) (s.space (j + 1))) eH → j = i)
    (hirr : IsIrreducible
      ((sectionRepresentation ρ (s.space i) (s.space (i + 1))).comp K.subtype)) :
    Nonempty (SingleNoncentralFlagWitness ρ K s.space i s.length) :=
  flag_witness_of_unique_natural ρ eH K hK s i hi hNi huniq hirr

/- The unique-natural-factor witness supplies a central-cover map onto the
actual section. Composing with its marked natural equivalence gives the map
used by the proved central-cover recognition theorem. -/
theorem commutator_model_of_unique_natural
    (ρ : Representation (ZMod 2) H U) (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (s : NaturalCentralSeries ρ K eH) (i : ℕ) (hi : i < s.length)
    (hNi : IsEightNatural (sectionRepresentation ρ (s.space i) (s.space (i + 1))) eH)
    (huniq : ∀ j < s.length,
      IsEightNatural (sectionRepresentation ρ (s.space j) (s.space (j + 1))) eH → j = i)
    (hirr : IsIrreducible
      ((sectionRepresentation ρ (s.space i) (s.space (i + 1))).comp K.subtype)) :
    IsCommutatorNaturalOrCover ρ K eH := by
  obtain ⟨w⟩ := flag_witness_of_unique_natural ρ eH K hK s i hi hNi huniq hirr
  obtain ⟨e, he⟩ := hNi
  let p : w.J.toSubmodule →ₗ[ZMod 2] natural (Fin 8) := e.toLinearMap.comp w.map
  have hp (g : H) (v : w.J.toSubmodule) :
      p (w.J.toRepresentation g v) =
        naturalRepresentation (Fin 8) (eH g) (p v) := by
    change e (w.map (w.J.toRepresentation g v)) =
      naturalRepresentation (Fin 8) (eH g) (e (w.map v))
    rw [w.map_equivariant, he]
  have hsur : Function.Surjective p := e.surjective.comp w.map_surjective
  have hker : p.ker ≤ fixedSpace w.J.toRepresentation K := by
    intro v hv k
    apply w.map_kernel_central
    have hz : e (w.map v) = 0 := hv
    exact e.injective (hz.trans (e.map_zero).symm)
  exact commutator_model_of_central_cover ρ eH K hK w.J w.J_eq_commutator p hp hsur hker
    w.commutator_eq_top

/- The ambient generation hypothesis is kept separate from the flag. This is
the source-specific deduction that turns the literal component commutator in
W into the whole-H commutator, while the same unique-factor witness gives the
actual natural-or-cover model on that literal commutator. -/
theorem whole_commutator_extension_of_unique_natural
    (ρ : Representation (ZMod 2) H U) (W : Subrepresentation ρ)
    (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hQ : IsEightNatural W.quotientRepresentation eH)
    (hgen : subspaceCommutator ρ ⊤ K = ⊤)
    (s : NaturalCentralSeries W.toRepresentation K eH) (i : ℕ) (hi : i < s.length)
    (hNi : IsEightNatural
      (sectionRepresentation W.toRepresentation (s.space i) (s.space (i + 1))) eH)
    (huniq : ∀ j < s.length,
      IsEightNatural
        (sectionRepresentation W.toRepresentation (s.space j) (s.space (j + 1))) eH →
      j = i)
    (hirr : IsIrreducible
      ((sectionRepresentation W.toRepresentation (s.space i) (s.space (i + 1))).comp
        K.subtype)) :
    subspaceCommutator ρ W.toSubmodule ⊤ =
        subspaceCommutator ρ W.toSubmodule K ∧
      IsCommutatorNaturalOrCover W.toRepresentation K eH := by
  refine ⟨whole_commutator_eq_component ρ W eH K hK hQ hgen, ?_⟩
  exact commutator_model_of_unique_natural W.toRepresentation eH K hK s i hi hNi huniq hirr

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections.Extensions

end
