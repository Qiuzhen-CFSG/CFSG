module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.BinaryCartan

/-!
# Orthogonal source roots and the binary Borel--Weyl equations

In a hexagon the reflection s_j preserves the orthogonal root
U_i^(s_j s_i): its two defining unipotent intersections are exchanged.
If U_j centralizes that root, so does U_j^(s_j), hence the whole actual
rank-one group R_j does. Applied to FA and EC, this removes the separate
orthogonal-centralization premise from the existing positive consumer and
supplies both missing fixed-root Weyl equations over every field, including F₄.
The lower positive equations themselves are not proved by this reduction.

For F₂, every canonical root has order two. The same geometric normalizer
calculation therefore proves both fixed-root Weyl equations WITHOUT any
positive-commutation premise. Combining this with BinaryCartan gives all
Borel--Weyl relations from PartialPositiveData alone. The remaining source
obligation is to derive that lower positive data; no complete 6E(a) -> 9A
recognition is claimed. OrthogonalApplication applies the positive and full
presentation consumers to the original marked quotient and both endpoints.

Source: Fong--Seitz I (3G), printed pp.14--16, for root intersections;
II (9.5)--(9.6), printed p.212, for the passage from positive orthogonal
commutation to rank-one centralization. The binary fixed-root proof here
uses the actual order-two root groups instead of the nonbinary tensor
argument or Thomas recognition. Right-conjugated subgroup conventions
are converted to the consumer's left-conjugation equations explicitly.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure Atlas.G2.RootPresentationRecognition
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem simple_square (i : Fin 2) : Q.simple i * Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2

private theorem longest_six (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    longest Q = Q.simple j*Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i := by
  have h0 := alternatingWord_longest Q false
  have h1 := alternatingWord_longest Q true
  rw [hm] at h0 h1
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, mul_one, mul_assoc] using h1.symm
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, mul_one, mul_assoc] using h0.symm
  · exact (hij rfl).elim

private theorem rootAt_intersections (i : Fin 2) (w : Weyl Q) :
    rootAt Q split i w = unipotentConjugate split w ⊓
      unipotentConjugate split ((longest Q*Q.simple i)*w) := by
  change rightConjugate (split.U ⊓ unipotentConjugate split (longest Q*Q.simple i))
    (representative w : X ⧸ Q.D) = _
  rw [rightConjugate_inf,
    ← unipotentConjugate_eq split w (representative w) (representative_spec w),
    unipotentConjugate_right split _ w (representative w) (representative_spec w)]

/-- The orthogonal reflection interchanges the two defining U-intersections. -/
theorem orthogonal_root_stabilizer (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) =
      rootAt Q split i (Q.simple j*Q.simple i) := by
  rw [rootAt_intersections, rootAt_intersections, longest_six Q hm i j hij]
  have cancel (k : Fin 2) (w : Weyl Q) : Q.simple k*(Q.simple k*w) = w := by
    rw [← mul_assoc, simple_square, one_mul]
  simp only [mul_assoc, simple_square, cancel, mul_one]
  exact inf_comm _ _

/-- Every specified source lift normalizes the actual orthogonal root. -/
theorem orthogonal_root_normalizes (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (n : RootReflection Q split j) :
    (n.val : X ⧸ Q.D) ∈ normalizer
      (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) := by
  have he : rightConjugate (rootAt Q split i (Q.simple j*Q.simple i))
      (n.val : X ⧸ Q.D) = rootAt Q split i (Q.simple j*Q.simple i) := by
    rw [rootAt_right Q split _ _ _ n.val n.class_eq,
      orthogonal_root_stabilizer Q split hm i j hij]
  apply mem_normalizer_iff.mpr
  intro x
  exact (show (n.val : X ⧸ Q.D)*x*(n.val : X ⧸ Q.D)⁻¹ ∈
      rootAt Q split i (Q.simple j*Q.simple i) ↔
      x ∈ rootAt Q split i (Q.simple j*Q.simple i) from
        SetLike.ext_iff.mp he x).symm

/-- Orthogonal simple-root commutation extends to the whole source rank-one group. -/
theorem rankOne_centralizes_orthogonal_of_simple (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (n : RootReflection Q split j)
    (hc : simpleRoot Q split j ≤ centralizer
      (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D))) :
    rankOne Q split j ≤ centralizer
      (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) := by
  rw [rankOne_eq Q split j n.val n.class_eq]
  apply sup_le hc
  intro x hx
  apply mem_centralizer_iff.mpr
  intro y hy
  have hy' := (mem_normalizer_iff.mp
    (orthogonal_root_normalizes Q split hm i j hij n) y).mp hy
  change (n.val : X ⧸ Q.D)*x*(n.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split j at hx
  have he := mem_centralizer_iff.mp (hc hx) _ hy'
  apply (MulAut.conj (n.val : X ⧸ Q.D)).injective
  simpa only [map_mul, MulAut.conj_apply] using he

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)

private theorem short_ne_long (short : Fin 2) : short ≠ 1-short := by
  fin_cases short <;> decide

/-- FA commutation in the existing positive input supplies the separate short centralizer. -/
theorem aligned_short_centralizes (hm : rotationOrder Q = 6)
    (hc : (alignedSourceRoots Q split hK μ n short).CommutingRelations) :
    rankOne Q split short ≤ centralizer
      (positiveCarrier Q split short 0 : Set (X ⧸ Q.D)) := by
  apply rankOne_centralizes_orthogonal_of_simple Q split hm (1-short) short
    (short_ne_long short).symm (n short)
  intro x hx
  have hx' : x ∈ ((alignedSourceRoots Q split hK μ n short).root 5).range :=
    (alignedSourceRoots_range Q split hK μ n short 5).symm ▸ hx
  obtain ⟨z,rfl⟩ := hx'
  apply mem_centralizer_iff.mpr
  intro y hy
  have hy' : y ∈ ((alignedSourceRoots Q split hK μ n short).root 0).range :=
    (alignedSourceRoots_range Q split hK μ n short 0).symm ▸ hy
  obtain ⟨a,rfl⟩ := hy'
  exact (hc.fa z.toAdd a.toAdd).symm

/-- EC commutation supplies the long rank-one centralizer of the middle short root. -/
theorem aligned_long_centralizes (hm : rotationOrder Q = 6)
    (hc : (alignedSourceRoots Q split hK μ n short).CommutingRelations) :
    rankOne Q split (1-short) ≤ centralizer
      (positiveCarrier Q split short 2 : Set (X ⧸ Q.D)) := by
  apply rankOne_centralizes_orthogonal_of_simple Q split hm short (1-short)
    (short_ne_long short) (n (1-short))
  intro x hx
  have hx' : x ∈ ((alignedSourceRoots Q split hK μ n short).root 4).range :=
    (alignedSourceRoots_range Q split hK μ n short 4).symm ▸ hx
  obtain ⟨e,rfl⟩ := hx'
  apply mem_centralizer_iff.mpr
  intro y hy
  have hy' : y ∈ ((alignedSourceRoots Q split hK μ n short).root 2).range :=
    (alignedSourceRoots_range Q split hK μ n short 2).symm ▸ hy
  obtain ⟨c,rfl⟩ := hy'
  exact (hc.ec e.toAdd c.toAdd).symm

/-- The existing lower positive input suffices; orthogonal centralization is derived. -/
theorem aligned_positive_relations_of_partial (hm : rotationOrder Q = 6)
    (d : PartialPositiveData (alignedSourceRoots Q split hK μ n short)) :
    (alignedSourceRoots Q split hK μ n short).CharTwoRelations :=
  aligned_positive_relations Q split hK μ n short
    (aligned_short_centralizes Q split hK μ n short hm d.commuting) d

private theorem conjugate_eq_of_centralizes {A : Subgroup (X ⧸ Q.D)}
    {g x : X ⧸ Q.D} (hg : g ∈ centralizer (A : Set (X ⧸ Q.D))) (hx : x ∈ A) :
    g*x*g⁻¹ = x := by
  rw [← mem_centralizer_iff.mp hg x hx, mul_assoc, mul_inv_cancel, mul_one]

variable (hH : IsMulCommutative ↥(Q.tits.B ⊓ Q.tits.N))

/-- The short reflection fixes A, using the positive FA commutation already required. -/
theorem sourceBorelWeyl_sA (hm : rotationOrder Q = 6)
    (hc : (alignedSourceRoots Q split hK μ n short).CommutingRelations) (a : F) :
    let d := sourceBorelWeyl Q split hK μ n short hH
    d.s*d.x 0 a*d.s⁻¹ = d.x 0 a := by
  apply conjugate_eq_of_centralizes Q
    (aligned_short_centralizes Q split hK μ n short hm hc (n short).mem_rankOne)
  rw [← alignedSourceRoots_range Q split hK μ n short 0]
  exact ⟨.ofAdd a,rfl⟩

/-- The long reflection fixes C, using the positive EC commutation already required. -/
theorem sourceBorelWeyl_rC (hm : rotationOrder Q = 6)
    (hc : (alignedSourceRoots Q split hK μ n short).CommutingRelations) (a : F) :
    let d := sourceBorelWeyl Q split hK μ n short hH
    d.r*d.x 2 a*d.r⁻¹ = d.x 2 a := by
  apply conjugate_eq_of_centralizes Q
    (aligned_long_centralizes Q split hK μ n short hm hc (n (1-short)).mem_rankOne)
  rw [← alignedSourceRoots_range Q split hK μ n short 2]
  exact ⟨.ofAdd a,rfl⟩

/-- At q=2, geometric normalization alone forces the short reflection to fix A. -/
theorem binary_reflection_fixes_highest (hm : rotationOrder Q = 6)
    (hF : Nat.card F = 2) (a : F) :
    (n short).val * (alignedSourceRoots Q split hK μ n short).x 0 a *
      ((n short).val : X ⧸ Q.D)⁻¹ = (alignedSourceRoots Q split hK μ n short).x 0 a := by
  apply conjugate_eq_of_centralizes Q
    ((normalizer_le_centralizer_of_card_two _
      ((positiveCarrier_card Q split hK μ n short 0).trans hF))
        (orthogonal_root_normalizes Q split hm (1-short) short
          (short_ne_long short).symm (n short)))
  rw [← alignedSourceRoots_range Q split hK μ n short 0]
  exact ⟨.ofAdd a,rfl⟩

/-- At q=2, geometric normalization alone forces the long reflection to fix C. -/
theorem binary_reflection_fixes_middle (hm : rotationOrder Q = 6)
    (hF : Nat.card F = 2) (a : F) :
    (n (1-short)).val * (alignedSourceRoots Q split hK μ n short).x 2 a *
      ((n (1-short)).val : X ⧸ Q.D)⁻¹ = (alignedSourceRoots Q split hK μ n short).x 2 a := by
  apply conjugate_eq_of_centralizes Q
    ((normalizer_le_centralizer_of_card_two _
      ((positiveCarrier_card Q split hK μ n short 2).trans hF))
        (orthogonal_root_normalizes Q split hm short (1-short)
          (short_ne_long short) (n (1-short))))
  rw [← alignedSourceRoots_range Q split hK μ n short 2]
  exact ⟨.ofAdd a,rfl⟩

/-- All binary Borel--Weyl equations follow from the still-explicit lower positive data. -/
theorem binarySourceBorelWeyl_relations (hm : rotationOrder Q = 6)
    (hF : Nat.card F = 2) (hcore : Q.tits.B.normalCore = ⊥)
    (d₀ : PartialPositiveData (alignedSourceRoots Q split hK μ n short)) :
    (binarySourceBorelWeyl Q split hK μ n short hm hF hcore).Relations where
  toCharTwoRelations := aligned_positive_relations_of_partial Q split hK μ n short hm d₀
  torus_root := binarySourceBorelWeyl_torus_root Q split hK μ n short hm hF hcore
  r_sq := sourceBorelWeyl_r_sq Q split hK μ n short
    (binaryCartanCommutative Q split hK μ n short hm hF hcore)
  s_sq := sourceBorelWeyl_s_sq Q split hK μ n short
    (binaryCartanCommutative Q split hK μ n short hm hF hcore)
  braid := binarySourceBorelWeyl_braid Q split hK μ n short hm hF hcore
  r_torus := binarySourceBorelWeyl_r_torus Q split hK μ n short hm hF hcore
  s_torus := binarySourceBorelWeyl_s_torus Q split hK μ n short hm hF hcore
  rA := sourceBorelWeyl_rA Q split hK μ n short
    (binaryCartanCommutative Q split hK μ n short hm hF hcore)
  rB := sourceBorelWeyl_rB Q split hK μ n short
    (binaryCartanCommutative Q split hK μ n short hm hF hcore)
  rC := binary_reflection_fixes_middle Q split hK μ n short hm hF
  rD := sourceBorelWeyl_rD Q split hK μ n short
    (binaryCartanCommutative Q split hK μ n short hm hF hcore)
  rF := sourceBorelWeyl_rF Q split hK μ n short
    (binaryCartanCommutative Q split hK μ n short hm hF hcore)
  sA := binary_reflection_fixes_highest Q split hK μ n short hm hF
  sB := sourceBorelWeyl_sB Q split hK μ n short
    (binaryCartanCommutative Q split hK μ n short hm hF hcore)
  sC := sourceBorelWeyl_sC Q split hK μ n short
    (binaryCartanCommutative Q split hK μ n short hm hF hcore)
  sD := sourceBorelWeyl_sD Q split hK μ n short
    (binaryCartanCommutative Q split hK μ n short hm hF hcore)
  sE := sourceBorelWeyl_sE Q split hK μ n short
    (binaryCartanCommutative Q split hK μ n short hm hF hcore)
  long_word := sourceBorelWeyl_long_word Q split hK μ n short
    (binaryCartanCommutative Q split hK μ n short hm hF hcore)
  short_word := sourceBorelWeyl_short_word Q split hK μ n short
    (binaryCartanCommutative Q split hK μ n short hm hF hcore)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
