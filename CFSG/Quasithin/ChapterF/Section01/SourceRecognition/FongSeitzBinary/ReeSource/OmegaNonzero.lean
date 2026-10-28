module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.OmegaActions
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PerpendicularNonzero
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.SixFour

/-!
# Nonzero Omega commutators and the common terminal obstruction

Cartan transitivity on the actual shifted Omega turns every nonzero
commutator bounded by (6.4) into the whole Omega root. The proof applies to
both positive Suzuki parameters and Sz(2), using the original independent
panel markings and the already proved size-bound containment.

Positive-parameter Omega-and-reflection generation removes perpendicular
normalization as a separate condition: Omega centralization implies the
whole rank-one group normalizes that root. Combining this with the earlier
binary quintic argument leaves exactly the same Omega movement alternative
in every parameter. The alternative is retained explicitly; eliminating it,
and proving unconditional (6H)(b), still requires the preceding p.53 argument.

Source: Fong--Seitz I (1973), proof of (6H)(b), printed p.53. The new
OriginalOmegaNonzero leaf applies these results to both original endpoint
orientations and the literal Q.q. Pairing, odd degree, remaining (6H),
Section 10 and full marked Ree comparison remain part of the source task.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i j : Fin 2)
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (n : ℕ) (hn : 0 < n)
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))

include μ hB hn ν hC in
/-- Nonzero (6.4) fills the whole actual shifted Omega root, for every Suzuki parameter. -/
theorem source_six_four_eq_of_nonzero
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : (Nat.card (BinaryGaloisField n))^4 < (2^(2*m+1))^6)
    (hne : ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ ≠ ⊥) :
    ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ =
      omegaOneAmbient (rootAt Q split i (Q.simple j*Q.simple i)) := by
  have hle := source_six_four_le_omega Q split i j m μ hB n hn ν T hC hc hm hij hsize
  apply le_antisymm hle
  obtain ⟨⟨a,ha⟩,han⟩ := ne_bot_iff_exists_ne_one.mp hne
  apply suzuki_rootAt_omega_le_of_invariant Q split i m μ hB _ _ ?_ a (hle ha) ha
    (fun he => han (Subtype.ext he))
  intro h hh
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (torus_normalizes_simpleRoot Q split i hh),
    mem_normalizer_iff_map_conj_eq.mp (rootAt_torus_normalizes Q split j _ hh)]

include μ hB hn ν hC in
/-- In positive characteristic-two Suzuki degree, the source near equality follows
from Omega centralization of the perpendicular root; its normalization is derived. -/
theorem source_positive_near_eq_of_omega_perpendicular_commutes
    (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card (BinaryGaloisField n) ≤ 2^(2*m+1))
    (hΩ : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ =
      rootAt Q split j (Q.simple i) := by
  have hnrm := positive_perpendicular_normalizes_of_omega_normalizes Q split i m μ hB
    hmpos hm j hij ((commutator_eq_bot_iff_le_centralizer.mp hΩ).trans (Subgroup.centralizer_le_normalizer _))
  exact source_near_eq_of_nonzero Q split i j m μ hB n hn ν T hC hm hij
    (source_near_nonzero_of_perpendicular_normalizes Q split i j ν T hC m μ hB hc hm hij hsize
      (le_sup_left.trans hnrm))

include μ hB hn ν hC in
/-- Both parameter cases now have the same genuine remaining obstruction:
nontrivial Omega movement of the perpendicular root. This is not yet (6H)(b). -/
theorem source_near_eq_or_omega_perpendicular_nonzero
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card (BinaryGaloisField n) ≤ 2^(2*m+1)) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ = rootAt Q split j (Q.simple i) ∨
    ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ ≠ ⊥ := by
  by_cases hm0 : m = 0
  · subst m
    have htwo : Nat.card (BinaryGaloisField n) = 2 := by
      have hlo : 1 < Nat.card (BinaryGaloisField n) := Finite.one_lt_card
      norm_num at hsize
      omega
    exact source_binary_near_eq_or_omega_perpendicular_nonzero Q split i j n hn ν T hC μ hB hc hm hij htwo
  · by_cases hΩ : ⁅omegaOneAmbient (simpleRoot Q split i),
        rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥
    · exact Or.inl (source_positive_near_eq_of_omega_perpendicular_commutes Q split i j m μ hB n hn ν T hC
        (by omega) hc hm hij hsize hΩ)
    · exact Or.inr hΩ

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
