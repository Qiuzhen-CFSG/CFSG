module
public import Theory.GroupAction.SymplecticRankThree.RankThree
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.Irreducibility
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderFormulas
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.NormalGeneration
public import Mathlib.Tactic.Ring

/-!
# C₂ coset geometry and the full-quotient normal subgroup argument

All actions use the finite carrier X/D of the given marked quotient. The
right coset Pᵢx from Fong–Seitz is represented as the left coset x⁻¹Pᵢ, and
right multiplication becomes left action by the inverse. Parabolic maximality
and the original local characteristic-two condition prove primitivity and
faithfulness. Four equal root orders give |U|=q⁴.

The canonical conjugate U₂^{s₁} has the actual simple-root order q. Given its
literal fixation of the closed neighbor orbit and the source subdegrees, the
proved elementary Higman argument constructs incidence and all line sizes.
The subdegree calculation and fixation are still explicit source obligations.
No projective coordinates or symplectic model map is assumed or constructed.

Finally, a normal subgroup containing a subgroup of order |U| has odd index.
It contains U, and normal generation then makes it the entire quotient. This
is the full-group step of (7C), valid also for q=2 without any simplicity claim.

Sources: Fong–Seitz I (1H)–(1I), pp.5–6 and (6A)(a), pp.36–38;
Fong–Seitz II (7C), p.193 and (8A), p.197; Higman (1964), Theorem 2(i).
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree
open RootCoordinates
open Theory.GroupAction.SymplecticRankThree
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Left cosets of an actual marked parabolic in the finite quotient. -/
abbrev Points (i : Fin 2) := (X ⧸ Q.D) ⧸ Q.tits.standardParabolic {Q.simple i}

/-- Both coset spaces are nontrivial, since the marked parabolics are proper. -/
theorem points_nontrivial (i : Fin 2) : Nontrivial (Points Q i) := by
  have hex : ∃ x : X ⧸ Q.D, x ∉ Q.tits.standardParabolic {Q.simple i} := by
    by_contra! hn
    exact (Q.parabolic_isCoatom i).ne_top (top_unique (fun x _ => hn x))
  obtain ⟨x,hx⟩ := hex
  refine ⟨⟨QuotientGroup.mk x, QuotientGroup.mk 1, ?_⟩⟩
  intro he
  have hh := QuotientGroup.eq.mp he
  exact hx ((Q.tits.standardParabolic {Q.simple i}).inv_mem_iff.mp (by simpa using hh))

/-- Maximality gives primitivity of the same finite parabolic coset action. -/
theorem primitive (i : Fin 2) : MulAction.IsPreprimitive (X ⧸ Q.D) (Points Q i) := by
  let := points_nontrivial Q i
  apply (MulAction.isCoatom_stabilizer_iff_preprimitive (X ⧸ Q.D)
    (QuotientGroup.mk 1 : Points Q i)).mp
  rw [MulAction.stabilizer_quotient]
  exact Q.parabolic_isCoatom i

/-- Right-coset source convention translated by inversion to the left action. -/
def rightCosetPoint (i : Fin 2) (x : X ⧸ Q.D) : Points Q i := QuotientGroup.mk x⁻¹

/-- Equality is equality of right cosets Pᵢx and Pᵢy, without normality of Pᵢ. -/
theorem rightCosetPoint_eq_iff (i : Fin 2) (x y : X ⧸ Q.D) :
    rightCosetPoint Q i x = rightCosetPoint Q i y ↔
      x*y⁻¹ ∈ Q.tits.standardParabolic {Q.simple i} := by
  exact QuotientGroup.eq.trans (by rw [inv_inv])

/-- Right multiplication by y becomes left multiplication by y⁻¹. -/
theorem rightCosetPoint_mul (i : Fin 2) (x y : X ⧸ Q.D) :
    rightCosetPoint Q i (x*y) = y⁻¹ • rightCosetPoint Q i x := by
  change QuotientGroup.mk (x*y)⁻¹ = QuotientGroup.mk (y⁻¹*x⁻¹)
  rw [mul_inv_rev]

/-- The convention change retains the original quotient homomorphism. -/
theorem original_rightCosetPoint_mul (i : Fin 2) (x y : X) :
    rightCosetPoint Q i (Q.q (x*y)) = (Q.q y)⁻¹ • rightCosetPoint Q i (Q.q x) := by
  rw [map_mul, rightCosetPoint_mul]

include split in
/-- Local characteristic two makes the literal parabolic coset action faithful. -/
theorem faithful (i : Fin 2)
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
      Set (Q.tits.standardParabolic {Q.simple i})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple i})) :
    FaithfulSMul (X ⧸ Q.D) (Points Q i) := by
  have hi : Function.Injective (MulAction.toPermHom (X ⧸ Q.D) (Points Q i)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker]
    exact Q.parabolic_normalCore_eq_bot split i hc
  apply faithfulSMul_iff.mpr
  intro g hg
  apply hi
  ext x
  simpa using hg x

/-- Four alternating roots of equal actual order give |U|=q⁴. -/
theorem unipotent_card {q : ℕ} (hm : rotationOrder Q = 4)
    (hq0 : Nat.card (simpleRoot Q split 0) = q)
    (hq1 : Nat.card (simpleRoot Q split 1) = q) : Nat.card split.U = q^4 := by
  rw [unipotent_card_even Q split 2 hm, hq0, hq1]
  ring

/-- The source U₂^{s₁}, using the canonical representative of the same s₁. -/
@[expose] def kernelRoot : Subgroup (X ⧸ Q.D) :=
  rightConjugate (simpleRoot Q split 1) (representative (Q.simple 0) : X ⧸ Q.D)

/-- Conjugation preserves the actual simple-root order, for every field size. -/
theorem kernelRoot_card {q : ℕ} (hq1 : Nat.card (simpleRoot Q split 1) = q) :
    Nat.card (kernelRoot Q split) = q := by
  rw [kernelRoot, card_rightConjugate, hq1]

/-- The literal source root supplies the pointwise-kernel lower bound.
Its fixation of this block remains the original (6A)(a)/(7C) coset obligation. -/
theorem kernel_lower_bound {q : ℕ} (C : Set (Points Q 1))
    (hq1 : Nat.card (simpleRoot Q split 1) = q)
    (hfix : ∀ u ∈ kernelRoot Q split, ∀ c ∈ C, u • c = c) :
    q ≤ Nat.card (fixingSubgroup (X ⧸ Q.D) C) := by
  rw [← kernelRoot_card Q split hq1]
  apply card_le_of_le
  intro u hu
  exact (mem_fixingSubgroup_iff (X ⧸ Q.D)).mpr (hfix u hu)

/-- Apply condition (i)'s elementary geometry to the same source cosets.
The incidence construction and the root's pointwise fixation are explicit
remaining source obligations; this conclusion supplies all line sizes. -/
theorem all_lines_card_of_root_fixes {q : ℕ} (hq : 2 ≤ q)
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple 1}) :
      Set (Q.tits.standardParabolic {Q.simple 1})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple 1}))
    (D : PolarityDesign (Points Q 1) q)
    (hact : ∀ (g : X ⧸ Q.D) x y, D.incident (g • x) (g • y) ↔ D.incident x y)
    (hq1 : Nat.card (simpleRoot Q split 1) = q)
    (hfix : ∀ u ∈ kernelRoot Q split, ∀ c ∈ D.block (rightCosetPoint Q 1 1), u • c = c) :
    ∀ x y, x ≠ y → (D.line x y).ncard = q+1 := by
  let := faithful Q split 1 hc
  exact D.all_lines_card_of_kernel hact hq (rightCosetPoint Q 1 1)
    (kernel_lower_bound Q split (D.block (rightCosetPoint Q 1 1)) hq1 hfix)

/-- The complete elementary Higman chain on the original quotient action.
The remaining orbit-count and root-fixation hypotheses refer to this same
coset action; no projective geometry or model map is assumed. -/
theorem rank_three_lines_of_root_fixes {q : ℕ} (hq : 2 ≤ q)
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple 1}) :
      Set (Q.tits.standardParabolic {Q.simple 1})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple 1}))
    (b c : Points Q 1) (hab : rightCosetPoint Q 1 1 ≠ b)
    (t : X ⧸ Q.D) (hta : t • rightCosetPoint Q 1 1 = b)
    (htb : t • b = rightCosetPoint Q 1 1)
    (hcov : MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (rightCosetPoint Q 1 1)) c =
      (insert (rightCosetPoint Q 1 1)
        (MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (rightCosetPoint Q 1 1)) b))ᶜ)
    (hdegree : Nat.card (Points Q 1) = q^3+q^2+q+1)
    (hsubdegree : Nat.card
      (MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (rightCosetPoint Q 1 1)) b) = q*(q+1))
    (hq1 : Nat.card (simpleRoot Q split 1) = q)
    (hfix : ∀ u ∈ kernelRoot Q split,
      ∀ c ∈ insert (rightCosetPoint Q 1 1)
        (MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (rightCosetPoint Q 1 1)) b), u • c = c) :
    ∃ D : PolarityDesign (Points Q 1) q,
      (∀ x y, D.incident x y ↔ y = x ∨
        (MulAction.SwappedOrbital.graph (rightCosetPoint Q 1 1) b hab t hta htb).Adj x y) ∧
      D.block (rightCosetPoint Q 1 1) = insert (rightCosetPoint Q 1 1)
        (MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (rightCosetPoint Q 1 1)) b) ∧
      (∀ x y, x ≠ y → (D.line x y).ncard = q+1) := by
  let := faithful Q split 1 hc
  let := primitive Q 1
  let : Fintype (Points Q 1) := Fintype.ofFinite _
  exact Theory.GroupAction.SymplecticRankThree.condition_i_lines hq
    (rightCosetPoint Q 1 1) b c hab t hta htb hcov hdegree hsubdegree
    (kernel_lower_bound Q split _ hq1 hfix)

/-- A subgroup of full unipotent order inside K makes K have odd index. -/
theorem index_odd_of_full_order_subgroup
    (K V : Subgroup (X ⧸ Q.D)) (hVK : V ≤ K) (hcard : Nat.card V = Nat.card split.U) :
    Nat.Coprime 2 K.index := by
  have he : V.index = split.U.index := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := split.U))
    rw [← hcard, V.card_mul_index, hcard, split.U.card_mul_index]
  apply (Nat.prime_two.coprime_iff_not_dvd.mpr split.index_not_two).coprime_dvd_right
  rw [← he]
  exact index_dvd_of_le hVK

/-- The actual U lies in every normal subgroup containing a subgroup of
full unipotent order. This avoids simplicity of the unknown quotient. -/
theorem unipotent_le_normal_of_full_order_subgroup
    (K V : Subgroup (X ⧸ Q.D)) [K.Normal]
    (hVK : V ≤ K) (hcard : Nat.card V = Nat.card split.U) : split.U ≤ K := by
  have hK : split.unipotentClosure ≤ K := by
    rw [split.unipotentClosure_eq_primeToResidual]
    exact primeToResidual_le K (index_odd_of_full_order_subgroup Q split K V hVK hcard)
  exact (show split.U ≤ split.unipotentClosure from le_normalClosure).trans hK

/-- The post-recognition overgroup step in Fong–Seitz (7C): normal generation
and the full Sylow order force K=Y, retaining full Sp₄(2). -/
theorem normal_eq_top_of_full_order_subgroup
    (hgen : split.unipotentClosure = ⊤) (K V : Subgroup (X ⧸ Q.D)) [K.Normal]
    (hVK : V ≤ K) (hcard : Nat.card V = Nat.card split.U) : K = ⊤ := by
  apply top_unique
  rw [← hgen]
  exact normalClosure_le_normal
    (unipotent_le_normal_of_full_order_subgroup Q split K V hVK hcard)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree
