module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.BinaryPerpendicular
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalSixOne

/-!
# The terminal nonzero-commutator reductions in source (6H)(b)

Three independent root factors would give |C_V(U_i)| ≥ q_lin q_Sz⁴ if
both the near and perpendicular i-root commutators vanished. Source (6.1)
gives the incompatible upper bound q_lin⁴ when q_lin ≤ q_Sz. Normalization
of the perpendicular root forces its commutator to vanish geometrically.
The actual Cartan action then fills the intervening linear root whenever
the near commutator is nontrivial, including over the binary field.

In the binary row the quintic fixed-group argument reduces the remaining
normalization condition to centralization by Omega₁(U_i). The results are
honest disjunctions: either the desired full linear-root equality holds,
or the specified perpendicular normalization/Omega-centralization fails.
The positive and binary p.53 arguments eliminating these second alternatives
are still required; these reductions do not establish all of (6H)(b).

Source: Fong--Seitz I (1973), proof of (6H), pp.53--54. The main result
retains independent natural panel markings and the explicit size comparison.
OriginalPerpendicularNonzero applies it to the original endpoints and Q.q.
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
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P)
  (split : SplitData Q.tits) (i j : Fin 2)
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include ν hC μ hB in
/-- The two commutators used in the terminal p.53 contradiction cannot both vanish.
The field markings are independent; the source size comparison remains explicit. -/
theorem source_near_or_perpendicular_nonzero
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j) (hsize : Nat.card F ≤ 2^(2*m+1)) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ ≠ ⊥ ∨
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ ≠ ⊥ := by
  by_contra hh
  push Not at hh
  have hlo := octagon_centralizer_card_ge_of_two_commutators Q split hm i j hij
    (marked_suzuki_remainder_le_kernel Q split i m μ hB)
    (marked_linear_remainder_le_kernel Q split j ν T hC) hh.1 hh.2
  have hup := (source_six_one Q split i j ν T hC m μ hB hc hm hij hsize).1
  rw [Nat.card_congr (suzukiRootEquiv Q split i m μ hB).toEquiv,matrixRoot_card,
    Nat.card_congr (linearRootEquiv Q split j ν T hC).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F),←pow_mul] at hlo
  have hlarge : (Nat.card F)^4 < Nat.card F*(2^(2*m+1))^4 := by
    calc
      _ < Nat.card F*(Nat.card F)^4 := by
        have hp : 0 < (Nat.card F)^4 := pow_pos (Nat.card_pos (α := F)) _
        nlinarith [show 1 < Nat.card F from Finite.one_lt_card]
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize _)
  exact (not_lt_of_ge (hlo.trans hup)) hlarge

include ν hC μ hB in
/-- Once the perpendicular root is normalized, (6.1) forces the desired commutator to be nontrivial.
The positive and binary source arguments must still establish that normalization. -/
theorem source_near_nonzero_of_perpendicular_normalizes
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j) (hsize : Nat.card F ≤ 2^(2*m+1))
    (hn : simpleRoot Q split i ≤ normalizer
      (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D))) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ ≠ ⊥ := by
  exact (source_near_or_perpendicular_nonzero Q split i j ν T hC m μ hB hc hm hij hsize).resolve_right
    (not_not.mpr (perpendicular_commutator_eq_bot_of_normalizes Q split hm i j hij
      (marked_suzuki_remainder_le_kernel Q split i m μ hB) hn))

private theorem cartan_normalizes_commutator (A B : Subgroup (X ⧸ Q.D))
    (hA : Q.tits.B ⊓ Q.tits.N ≤ normalizer (A : Set (X ⧸ Q.D)))
    (hB : Q.tits.B ⊓ Q.tits.N ≤ normalizer (B : Set (X ⧸ Q.D))) :
    Q.tits.B ⊓ Q.tits.N ≤ normalizer ((⁅A,B⁆ : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) := by
  intro h hh
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hA hh),
    mem_normalizer_iff_map_conj_eq.mp (hB hh)]

omit F [Field F] [Finite F] [CharP F 2] ν T hC in
include μ hB in
/-- Every nontrivial near mixed commutator is the whole intervening linear root.
The actual Cartan action supplies the transitivity, also for the binary field. -/
theorem source_near_eq_of_nonzero (n : ℕ) (hn : 0 < n)
    (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hne : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ ≠ ⊥) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ = rootAt Q split j (Q.simple i) := by
  let D := ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆
  have hle := (source_six_three Q split i j m μ hB ν T hC hm hij).1
  have hD : Q.tits.B ⊓ Q.tits.N ≤ normalizer (D : Set (X ⧸ Q.D)) :=
    cartan_normalizes_commutator Q _ _ (torus_normalizes_simpleRoot Q split i)
      (torus_normalizes_rightConjugate (simpleRoot Q split i)
        (torus_normalizes_simpleRoot Q split i) (representative _))
  obtain ⟨⟨a,ha⟩,han⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have han : a ≠ 1 := fun he => han (Subtype.ext he)
  apply le_antisymm hle
  let A := rootAt Q split j (Q.simple i)
  let ρ := rootAction Q split j (Q.simple i)
  let := linear_rootAt_elementary Q split j n ν T hC (Q.simple i)
  let : IsCyclic ρ.range := linear_rootAction_cyclic Q split j n ν T hC hn
    (UnitarySource.actorReflection Q split j) (Q.simple i)
  intro b hb
  by_cases hb1 : b = 1
  · simpa only [hb1] using D.one_mem
  obtain ⟨c,hc,_⟩ := RootAction.regular_of_card ρ.range.subtype ρ.range.subtype_injective hn
    (linear_rootAction_card Q split j n ν T hC hn
      (UnitarySource.actorReflection Q split j) (Q.simple i))
    (linear_rootAt_card Q split j n ν T hC hn (Q.simple i))
    (⟨a,hle ha⟩ : A) ⟨b,hb⟩ (fun h => han (congrArg Subtype.val h))
    (fun h => hb1 (congrArg Subtype.val h))
  obtain ⟨h,hh⟩ := c.property
  have he : (h : X ⧸ Q.D)*a*(h : X ⧸ Q.D)⁻¹ = b := by
    have he := congrArg (fun f : MulAut A => (f ⟨a,hle ha⟩ : X ⧸ Q.D)) hh
    exact he.trans (congrArg Subtype.val hc)
  rw [←he]
  exact (mem_normalizer_iff.mp (hD h.property) a).mp ha

omit F [Field F] [Finite F] [CharP F 2] ν T hC in
include μ hB in
/-- The terminal reduction in both source parameter cases, with the whole linear root as output.
Eliminating the second alternative requires the further p.53 source argument. -/
theorem source_near_eq_or_perpendicular_not_normalized (n : ℕ) (hn : 0 < n)
    (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card (BinaryGaloisField n) ≤ 2^(2*m+1)) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ = rootAt Q split j (Q.simple i) ∨
    ¬ simpleRoot Q split i ≤ normalizer
      (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) := by
  by_cases hnormal : simpleRoot Q split i ≤ normalizer
      (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D))
  · exact Or.inl (source_near_eq_of_nonzero Q split i j m μ hB n hn ν T hC hm hij
      (source_near_nonzero_of_perpendicular_normalizes Q split i j ν T hC m μ hB hc hm hij hsize hnormal))
  · exact Or.inr hnormal

omit F [Field F] [Finite F] [CharP F 2] ν T hC m μ hB in
/-- The binary terminal reduction needs only to exclude Omega movement of the
perpendicular root. The order-five argument discharges its normalizer premise. -/
theorem source_binary_near_eq_or_omega_perpendicular_nonzero (n : ℕ) (hn : 0 < n)
    (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card (BinaryGaloisField n) = 2) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ = rootAt Q split j (Q.simple i) ∨
    ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ ≠ ⊥ := by
  by_cases hΩ : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥
  · have hlin : Nat.card (simpleRoot Q split j) = 2 := by
      rw [Nat.card_congr (linearRootEquiv Q split j ν T hC).toEquiv,
        Nat.card_congr (Multiplicative.toAdd : Multiplicative (BinaryGaloisField n) ≃ _),hsize]
    have hnorm := binary_perpendicular_normalizes_of_omega_commutes Q split i
      (marked_suzuki_remainder_le_kernel Q split i 0 μ hB) μ hB hc hm j hij
      (source_six_three Q split i j 0 μ hB ν T hC hm hij).2 hlin hΩ
    exact Or.inl ((source_near_eq_or_perpendicular_not_normalized Q split i j 0 μ hB n hn ν T hC
      hc hm hij (by simpa using hsize.le)).resolve_right (not_not.mpr hnorm))
  · exact Or.inr hΩ

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
