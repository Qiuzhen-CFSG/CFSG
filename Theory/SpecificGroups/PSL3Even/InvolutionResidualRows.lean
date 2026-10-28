module
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.FieldDescent
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.GraphConjugacy
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.GraphFieldDescent
public import Theory.SpecificGroups.PSL3Even.ResidualComparison
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.PSL3.FullParabolicProperness
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.GroupAction.AutomorphismFixedResidualTransport
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveGraphField

/-!
# Fixed two-residual rows for binary PSL₃

Quadratic semilinear descent identifies the field row with the derived PSL₃
of the fixed subfield. Graph conjugacy gives derived PSL₂, including the
nonperfect binary endpoint. Hermitian descent and unitary perfectness identify
the larger mixed rows, with the actual Frobenius and standard form retained.
Root conjugacy places the inner fixed group in a genuine proper point
parabolic and gives equality of embedded residuals.

The degree-two mixed row uses the checked GF(4) computation after an explicit
compatible marking. Constructing that marking for every twisted involution
remains a separate obligation; it is not assumed for the other rows.
Source: Aschbacher--Smith, 16.1.4(1),(4)--(6), printed pp.1170--1171,
and its uses in 16.4--16.5. All matrix descent proofs are reused from the
specific-group modules, with their original source attributions.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open Matrix.PSL3.OuterSolvable Matrix.PSL3.LinearThree
open Matrix.PSL3Even.OuterElementaryRank.FixedRanks
namespace Matrix.PSL3Even.InvolutionResidualRows
variable {F : Type*} [Field F] [Finite F]

private noncomputable def residualEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : pResidual 2 G ≃* pResidual 2 H :=
  ((pResidual 2 G).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_pResidual 2 e))

private theorem perfect_residual_eq_top (G : Type*) [Group G] [Finite G]
    [Group.IsPerfect G] : pResidual 2 G = ⊤ := by
  apply (pResidual_eq_top_iff 2 G).mpr
  intro N hN hP
  let := hN
  have : Subsingleton (G ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent _ hP.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The semilinear involution is conjugate to its actual coefficient action;
its fixed two-residual is the derived PSL₃ over the quadratic fixed subfield. -/
theorem field_row {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (g : GL (Fin 3) F) (σ : F ≃+* F) (hne : σ ≠ 1)
    (hs : (linearConj F g * fieldAction F σ) ^ 2 = 1) :
    ∃ m : ℕ, 0 < m ∧ n = 2 * m ∧
      Nat.card (FixedBy.subfield F σ) = 2 ^ m ∧ σ ^ 2 = 1 ∧
      (∃ c : GL (Fin 3) F, MulAut.congr (linearConj F c)
        (linearConj F g * fieldAction F σ) = fieldAction F σ) ∧
      Nonempty (pResidual 2 (linearConj F g * fieldAction F σ).fixedSubgroup ≃*
        commutator PSL(3, FixedBy.subfield F σ)) := by
  have hσ := field_part_sq g σ hs
  obtain ⟨m, hm, hnm, hK⟩ := fixedField_parameters hn hF σ hσ hne
  obtain ⟨c, hc⟩ := FieldDescent.exists_linear_conjugate_field g σ
    (orderOf_eq_prime hσ hne) hs
  obtain ⟨e⟩ := semilinear_field_fixed_equiv g σ hne hs
  let := Atlas.psl_perfect (F := FixedBy.subfield F σ) 3 (by decide)
  refine ⟨m, hm, hnm, hK, hσ, ⟨c, hc⟩, ⟨?_⟩⟩
  exact (residualEquiv e).trans
    (MulEquiv.subgroupCongr ((perfect_residual_eq_top _).trans
      Group.IsPerfect.commutator_eq_top.symm))

/-- The graph row keeps the derived PSL₂ endpoint at field order two. -/
theorem graph_row {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (g : GL (Fin 3) F) (hs : (linearConj F g * graph F) ^ 2 = 1) :
    (∃ c : MulAut PSL(3,F), MulAut.congr c (linearConj F g * graph F) = graph F) ∧
      Nonempty (pResidual 2 (linearConj F g * graph F).fixedSubgroup ≃*
        commutator PSL(2,F)) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨c, hc⟩ := graph_involution_conjugate hn hF g hs
  let e := ((MulAut.fixedSubgroupCongr c (linearConj F g * graph F)).trans
    (MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup hc))).trans
      ((Matrix.PSL3Four.GraphFixed.projectiveGraphFixedEquivSpecial F).trans
        ((Matrix.PSL3Four.GraphFixed.graphSLFixedEquivSL2 F).trans
          (Theory.PSL2.sl2QuotientEquiv F)))
  let : Fintype (BinaryGaloisField n) := Fintype.ofFinite _
  have hcard : Fintype.card F = Fintype.card (BinaryGaloisField n) := by
    simpa only [← Nat.card_eq_fintype_card,
      BenderSuzuki.Converse.card_binaryGaloisField n (Nat.ne_of_gt hn)] using hF
  let k := Atlas.fieldEquivPSL 2 (FiniteField.ringEquivOfCardEq hcard)
  have hr : pResidual 2 PSL(2,F) = commutator PSL(2,F) := by
    apply Subgroup.map_injective (f := k.toMonoidHom) k.injective
    rw [map_pResidual, Theory.PSL2.binary_twoResidual_eq_commutator hn,
      map_commutator_eq, MonoidHom.range_eq_top.mpr k.surjective]
    rfl
  exact ⟨⟨c, hc⟩, ⟨(residualEquiv e).trans (MulEquiv.subgroupCongr hr)⟩⟩

/-- The graph-field row above degree two is the actual PSU₃ of the
constructed Hermitian form; both field cardinalities are retained. -/
theorem graphField_large_row {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (hn2 : n ≠ 2) (g : GL (Fin 3) F) (σ : F ≃+* F) (hne : σ ≠ 1)
    (hs : (linearConj F g * fieldAction F σ * graph F) ^ 2 = 1) :
    ∃ (m : ℕ) (J : HermitianForm 3 F), 1 < m ∧ n = 2 * m ∧
      J.conj = σ ∧ J.form = !![0,0,1; 0,1,0; 1,0,0] ∧
      (∀ x, J.conj x = x ^ (2 ^ m)) ∧ Nat.card F = (2 ^ m) ^ 2 ∧
      Nat.card {x : F // J.conj x = x} = 2 ^ m ∧
      Nonempty (pResidual 2 (linearConj F g * fieldAction F σ * graph F).fixedSubgroup ≃*
        ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨m, hm, hnm, hK⟩ := fixedField_parameters hn hF σ
    (graphField_part_sq g σ hs) hne
  obtain ⟨J, hJ, ⟨e⟩⟩ := GraphFieldDescent.exists_fixed_equiv_unitary g σ hne hs
  have hm2 : 1 < m := by omega
  have hcard : Nat.card F = (2 ^ m) ^ 2 := by rw [hF, hnm, pow_mul']
  have hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ m := by rw [hJ]; exact hK
  let := J.projective_isPerfect_of_fixed_card (by
    exact (by decide : 2 < 2 ^ 2).trans_le
      (Nat.pow_le_pow_right (by decide) hm2)) hcard hfixed
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv _ e.toEquiv
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨d⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2 ^ m) hcard hfixed
  exact ⟨m, J₀, hm2, hnm, hJ, rfl,
    BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J₀ (2 ^ m) hcard hfixed,
    hcard, hfixed,
    ⟨(residualEquiv e).trans (((MulEquiv.subgroupCongr
      (perfect_residual_eq_top _)).trans topEquiv).trans d)⟩⟩

/-- The highest-root centralizer lies in the actual point stabilizer. -/
theorem root_centralizer_le_parabolic [CharP F 2] :
    Matrix.PSL3.EvenInnerCentralizers.centralizer F ≤ pointParabolic F := by
  rw [← Matrix.PSL3.EvenInnerCentralizers.centralizer_map]
  apply Subgroup.map_mono
  intro g hg
  obtain ⟨h10, h20, _, _⟩ := (Matrix.PSL3.EvenInnerCentralizers.mem_centralizerSL_iff F g).mp hg
  exact (mem_pointParabolicSL_iff F g).mpr ⟨h10,h20⟩

/-- Root conjugacy and the actual proper parabolic give the embedded
local-residual equality in the inner row, including field order two. -/
theorem inner_row {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (a : MulAut PSL(3,F)) (ha : orderOf a = 2) (hi : ∃ t, a = MulAut.conj t) :
    ∃ c : MulAut PSL(3,F), (∃ g : PSL(3,F), c = MulAut.conj g) ∧
      MulAut.congr c a = MulAut.conj (Matrix.PSL3.EvenInnerCentralizers.root F) ∧
      (pointParabolic F).comap c.toMonoidHom < ⊤ ∧
      a.fixedSubgroup ≤ (pointParabolic F).comap c.toMonoidHom ∧
      MulAut.embeddedFixedResidual 2 a =
        ((pResidual 2 (a.fixedSubgroup.subgroupOf ((pointParabolic F).comap c.toMonoidHom))).map
          (a.fixedSubgroup.subgroupOf ((pointParabolic F).comap c.toMonoidHom)).subtype).map
            ((pointParabolic F).comap c.toMonoidHom).subtype := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect PSL(3,F) := Atlas.psl_perfect 3 (by decide)
  obtain ⟨t, ht, he, _⟩ := MulAut.inner_involution_representative
    center_eq_bot_of_simple_perfect a ha hi
  have ht1 : t ≠ 1 := by intro h; simp [h] at ht
  obtain ⟨g, hg⟩ := isConj_iff.mp (ResidualComparison.involution_isConj_root_of_pos F hn hF
    t ht1 (ht ▸ pow_orderOf_eq_one t))
  let c : MulAut PSL(3,F) := MulAut.conj g
  have hc : MulAut.congr c a = MulAut.conj (Matrix.PSL3.EvenInnerCentralizers.root F) := by
    rw [he, MulAut.congr_conj, show c t = _ from hg]
  have hle : a.fixedSubgroup ≤ (pointParabolic F).comap c.toMonoidHom := by
    intro x hx
    apply root_centralizer_le_parabolic
    have hx' : c x ∈ (MulAut.congr c a).fixedSubgroup := by
      rw [MulAut.mem_fixedSubgroup]
      change c (a (c.symm (c x))) = c x
      rw [c.symm_apply_apply, (MulAut.mem_fixedSubgroup a x).mp hx]
    rw [hc, MulAut.fixedSubgroup_conj] at hx'
    exact hx'
  refine ⟨c, ⟨g, rfl⟩, hc, ?_, hle, MulAut.embeddedFixedResidual_eq_local 2 a _ hle⟩
  apply lt_top_iff_ne_top.mpr
  intro heq
  apply (Matrix.PSL3.RootPlaneGeometry.parabolic_lt_top F true).ne
  change pointParabolic F = ⊤
  apply eq_top_iff.mpr
  intro x _
  have hmem : c.symm x ∈ (pointParabolic F).comap c.toMonoidHom := heq.symm ▸ mem_top _
  simpa only [mem_comap, MulEquiv.coe_toMonoidHom, c.apply_symm_apply] using hmem
/-- The remaining degree-two action comparison. It specifies an actual
intertwining equivalence with the standard GF(4) graph-field action. -/
@[expose] def FourGraphFieldMarking (K : Type*) [Field K] : Prop :=
  Nat.card K = 4 → ∀ (g : GL (Fin 3) K) (σ : K ≃+* K), σ ≠ 1 →
    (linearConj K g * fieldAction K σ * graph K) ^ 2 = 1 →
    ∃ e : PSL(3,K) ≃* Matrix.PSL3Four.PSL, ∀ x,
      e ((linearConj K g * fieldAction K σ * graph K) x) =
        (graph Matrix.PSL3Four.F * Matrix.PSL3Four.pslFrobenius) (e x)

omit [Finite F] in
/-- The marked degree-two action has the checked E₉ residual, without repeating
the finite matrix computation. The marking remains an explicit premise. -/
theorem graphField_four_row (hmark : FourGraphFieldMarking F) (hF : Nat.card F = 4)
    (g : GL (Fin 3) F) (σ : F ≃+* F) (hne : σ ≠ 1)
    (hs : (linearConj F g * fieldAction F σ * graph F) ^ 2 = 1) :
    Nonempty (pResidual 2 (linearConj F g * fieldAction F σ * graph F).fixedSubgroup ≃*
      Multiplicative (Fin 2 → ZMod 3)) := by
  obtain ⟨e, he⟩ := hmark hF g σ hne hs
  exact ⟨(MulAut.fixedResidualEquivOfCompatible 2 e _ _ he).trans
    Matrix.PSL3Four.projectiveGraphFieldResidualEquiv⟩

end Matrix.PSL3Even.InvolutionResidualRows
