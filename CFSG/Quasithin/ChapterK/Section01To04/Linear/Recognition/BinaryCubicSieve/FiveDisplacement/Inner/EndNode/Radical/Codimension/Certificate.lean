module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Setup
/-!
# Root certificates in the common-fixed-space quotient

An extracting operator that starts with a radical-root difference kills the
radical's common fixed space. It therefore descends along the literal quotient
map. A triangular family of such operators proves independence of the cosets,
not just independence of their representatives in the original module.

This is the quotient criterion used by the end-radical root certificates in
Guralnick–Malle, Classification of 2F-modules II, Proposition 4.7 step 1,
pp.25–26; Aschbacher–Smith K.3.2, printed pp.454–455.
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Codimension
open Representation Representation.BinaryOffender
open Representation.SL5TenDimensional.Classification.Separated
open CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
open scoped BigOperators

private theorem independent_of_extractors
    {X Y : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    {n : ℕ} (f : Fin n → X) (D : Fin n → X →ₗ[ZMod 2] Y)
    (hzero : ∀ i j, j < i → D i (f j) = 0)
    (hne : ∀ i, D i (f i) ≠ 0) : LinearIndependent (ZMod 2) f := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  by_contra hj
  let s := Finset.univ.filter (fun i => c i ≠ 0)
  have hs : s.Nonempty := ⟨j, by simp [s, hj]⟩
  let i := s.max' hs
  have hi : c i ≠ 0 := (Finset.mem_filter.mp (s.max'_mem hs)).2
  have he := congrArg (D i) hc
  simp only [map_sum, map_smul, map_zero] at he
  have hh : ∑ k, c k • D i (f k) = c i • D i (f i) := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      by_cases hlt : k < i
      · rw [hzero i k hlt, smul_zero]
      · have hk : c k = 0 := by
          by_contra hk
          have hle : k ≤ i := s.le_max' k (by simp [s, hk])
          exact hki (le_antisymm hle (le_of_not_gt hlt))
        rw [hk, zero_smul]
    · simp
  rw [hh] at he
  exact (smul_ne_zero hi (hne i)) he

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V)

/-- Triangular extraction in the literal common-fixed-space quotient. -/
theorem fixedCodim_ge_of_triangular [FiniteDimensional (ZMod 2) V] {n : ℕ} (e : Fin 2)
    (f : Fin n → V) (D : Fin n → V →ₗ[ZMod 2] V)
    (hkill : ∀ i, fixedSpace σ (radicalRootGroup e) ≤ LinearMap.ker (D i))
    (hzero : ∀ i j, j < i → D i (f j) = 0)
    (hne : ∀ i, D i (f i) ≠ 0) : n ≤ fixedCodim σ (radicalRootGroup e) := by
  let W := fixedSpace σ (radicalRootGroup e)
  have hi : LinearIndependent (ZMod 2) (fun i => W.mkQ (f i)) := by
    apply independent_of_extractors _ (fun i => W.liftQ (D i) (hkill i))
    · exact hzero
    · exact hne
  simpa [fixedCodim, W] using hi.fintype_card_le_finrank

/-- A first radical difference annihilates the common fixed space. -/
theorem fixedSpace_le_ker_radical_difference (e : Fin 2) (i : Fin 4) (D : V →ₗ[ZMod 2] V) :
    fixedSpace σ (radicalRootGroup e) ≤
      LinearMap.ker (D.comp (difference σ (radicalRoot e i))) := by
  intro x hx
  have hh : σ (radicalRoot e i) x = x :=
    hx ⟨radicalRoot e i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  change D (σ (radicalRoot e i) x - x) = 0
  rw [hh, sub_self, map_zero]

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Codimension
