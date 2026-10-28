module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.MinimumDegree

/-!
# Equality of the chief-factor counts in B.5.9

Each noncentral literal section has dimension at least 3m. Thus a flag term
of codimension at most 3m has at most one noncentral factor above it. If the
quotient action is nontrivial, perfectness ensures that some such factor
exists: the quotient images of an all-central flag would be centralized.

Applied to an invariant chief flag through C_V(B), where B=C_A(L), equality
in (!!) therefore gives exactly one noncentral factor above C_V(B) and c-1
below it. The parent argument proves the codimension equality and compares
this count with the single factor supplied by U=[C_V(B),L].

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108, the equality case of (!!).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
set_option backward.isDefEq.respectTransparency false
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

namespace InvariantChiefFlag
variable {ρ} {A L : Subgroup G} {S : Submodule (ZMod 2) V}

private theorem factorDimension_add_finrank [Module.Finite (ZMod 2) V]
    (f : InvariantChiefFlag ρ A L S) (i : ℕ) :
    f.factorDimension i + Module.finrank (ZMod 2) (f.term i).toSubmodule =
      Module.finrank (ZMod 2) (f.term (i + 1)).toSubmodule := by
  have hd := (sectionLower (ρ.comp L.subtype) (f.term i)
    (f.term (i + 1))).toSubmodule.finrank_quotient_add_finrank
  have he := (sectionLowerEquiv (ρ.comp L.subtype) (f.monotone (Nat.le_succ i))).finrank_eq
  change f.factorDimension i + _ = _ at hd
  rwa [he] at hd

/-- Above a flag term of codimension at most 3m, at most one section can
have the nontrivial component action, since each such section has dimension
at least 3m. -/
theorem noncentral_above_card_le_one [Finite G] [Module.Finite (ZMod 2) V]
    (s : NaturalSeed ρ A L) (hL : IsComponent G L)
    (f : InvariantChiefFlag ρ A L ⊤) (r : ℕ)
    (hbudget : Module.finrank (ZMod 2) V ≤
      3 * s.field.degree + Module.finrank (ZMod 2) (f.term r).toSubmodule) :
    (f.noncentral.filter (r ≤ ·)).card ≤ 1 := by
  classical
  have impossible {i j : ℕ} (hi : i ∈ f.noncentral) (hj : j ∈ f.noncentral)
      (hri : r ≤ i) (hij : i < j) : False := by
    have hdi := f.factorDimension_lower ρ s hL hi
    have hdj := f.factorDimension_lower ρ s hL hj
    have hei := f.factorDimension_add_finrank i
    have hej := f.factorDimension_add_finrank j
    have hri' := Submodule.finrank_mono
      (show (f.term r).toSubmodule ≤ (f.term i).toSubmodule from f.monotone hri)
    have hij' := Submodule.finrank_mono
      (show (f.term (i + 1)).toSubmodule ≤ (f.term j).toSubmodule from
        f.monotone (Nat.succ_le_of_lt hij))
    have hjtop := (f.term (j + 1)).toSubmodule.finrank_le
    have hm := s.field.degree_pos
    omega
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hi, hri⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj, hrj⟩ := Finset.mem_filter.mp hj
  rcases lt_trichotomy i j with hij | hij | hji
  · exact (impossible hi hj hri hij).elim
  · exact hij
  · exact (impossible hj hi hrj hji).elim

/-- A nontrivial quotient action of the perfect component survives on some
literal factor above the chosen term. Quotient images of the original flag
supply the central-flag argument; no splitting is used. -/
theorem noncentral_above_nonempty [Group.IsPerfect L]
    (f : InvariantChiefFlag ρ A L ⊤) {r : ℕ} (hr : r ≤ f.length)
    (hne : (f.term r).quotientRepresentation ≠ 1) :
    (f.noncentral.filter (r ≤ ·)).Nonempty := by
  classical
  by_contra hn
  let U := f.term r
  let τ := U.quotientRepresentation
  let c : ℕ → Subrepresentation τ := fun i => U.quotientImage (f.term (r + i))
  have hc0 : c 0 = ⊥ := by
    apply (U.quotientImage_eq_bot_iff _).mpr
    simp only [Nat.add_zero]
    exact le_rfl
  have hc (i : ℕ) (hi : i < f.length - r) (l : L) :
      ∀ v, sectionRepresentation τ (c i) (c (i + 1)) l v = v := by
    have ht : ∀ l v, sectionRepresentation (ρ.comp L.subtype)
        (f.term (r + i)) (f.term (r + i + 1)) l v = v := by
      by_contra ht
      apply hn
      exact ⟨r + i, Finset.mem_filter.mpr
        ⟨f.noncentral_mem.mpr ⟨by omega, ht⟩, by omega⟩⟩
    apply (sectionRepresentation_trivial_iff τ (c i) (c (i + 1)) l).mpr
    rintro _ ⟨v, hv, rfl⟩
    change v ∈ (f.term (r + (i + 1))).toSubmodule at hv
    have hv' : v ∈ (f.term (r + i + 1)).toSubmodule := by
      simpa only [Nat.add_assoc] using hv
    have hd := (sectionRepresentation_trivial_iff (ρ.comp L.subtype)
      (f.term (r + i)) (f.term (r + i + 1)) l).mp (ht l) v hv'
    exact ⟨ρ (l : G) v - v, hd, map_sub U.toSubmodule.mkQ _ _⟩
  let : Group.IsPerfect (⊤ : Subgroup L) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := L)).symm.toMonoidHom)
      Subgroup.topEquiv.symm.surjective
  have hfix := le_fixedSpace_of_central_flag τ ⊤ c hc0 (f.length - r)
    (fun i hi l _ => hc i hi l)
  have htop : c (f.length - r) = ⊤ := by
    apply (U.quotientImage_eq_top_iff _).mpr
    rw [show r + (f.length - r) = f.length by omega, f.stop, sup_top_eq]
  apply hne
  ext l : 1
  apply LinearMap.ext
  intro v
  apply hfix _ ⟨l, mem_top l⟩
  rw [htop]
  exact Submodule.mem_top

private theorem noncentral_below_eq (f : InvariantChiefFlag ρ A L S)
    {r : ℕ} (hr : r ≤ f.length) :
    f.noncentral.filter (· < r) = noncentralFactors (ρ.comp L.subtype) f.term r := by
  classical
  ext i
  simp only [Finset.mem_filter, f.noncentral_mem, noncentralFactors, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, ht⟩, hir⟩
    exact ⟨hir, ht⟩
  · rintro ⟨hir, ht⟩
    exact ⟨⟨hir.trans_le hr, ht⟩, hir⟩

/-- Equality in (!!) leaves exactly one noncentral factor above C_V(B),
and hence c-1 below it, for the literal adapted flag. -/
theorem centralizerFixed_counts_of_sharp_bound [Finite G] [Module.Finite (ZMod 2) V]
    (s : NaturalSeed ρ A L) (hL : IsComponent G L)
    (f : InvariantChiefFlag ρ A L ⊤) {r : ℕ} (hr : r ≤ f.length)
    (hstop : (f.term r).toSubmodule = fixedSpace ρ (A ⊓ centralizer (L : Set G)))
    (hcodim : fixedCodim ρ (A ⊓ centralizer (L : Set G)) = 3 * s.field.degree)
    (hne : (offenderCentralizerFixed ρ A L).quotientRepresentation ≠ 1) :
    (f.noncentral.filter (r ≤ ·)).card = 1 ∧
      (noncentralFactors (ρ.comp L.subtype) f.term r).card + 1 = f.noncentral.card ∧
      (noncentralFactors (ρ.comp L.subtype) f.term r).card = f.noncentral.card - 1 := by
  classical
  let : Group.IsPerfect L := hL.2.toIsPerfect
  have hbudget := fixedCodim_add_finrank ρ (A ⊓ centralizer (L : Set G))
  rw [hcodim, ← hstop] at hbudget
  have hle := f.noncentral_above_card_le_one s hL r hbudget.symm.le
  have he : f.term r = offenderCentralizerFixed ρ A L :=
    Subrepresentation.toSubmodule_injective hstop
  have hpos := Finset.card_pos.mpr (f.noncentral_above_nonempty hr (he.symm ▸ hne))
  have hone : (f.noncentral.filter (r ≤ ·)).card = 1 := by omega
  have hsum := Finset.card_filter_add_card_filter_not (s := f.noncentral) (fun i => i < r)
  simp only [Nat.not_lt] at hsum
  rw [f.noncentral_below_eq hr, hone] at hsum
  exact ⟨hone, hsum, by omega⟩

end InvariantChiefFlag
end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
