module
public import Theory.GroupAction.FourElementInvolutionLines
public import Theory.GroupAction.NormalizingActor

/-!
# A commuting involution's displacement on an elementary sixteen

Let R act through the literal automorphism subgroup of an elementary
abelian two-group W of order sixteen, with trivial common fixed subgroup.
Let U be an R-invariant subgroup of order four. If an automorphism t squares
to one, commutes with R, and fixes U pointwise, its cyclic displacement is
either trivial or exactly U. No separate faithfulness premise is needed.

The identity actor is immediate. For a nonidentity involution, rank-nullity
and U contained in the fixed subgroup bound the displacement order by four.
Commutation with R makes the displacement R-invariant. If its order were
two, its unique nonidentity element would be R-fixed, a contradiction.
The remaining nontrivial displacement and U both equal the order-four
fixed subgroup of t. The supplied invariant-action instance is retained;
the cardinal argument itself only uses that t fixes U pointwise.

This source-neutral elementary action result supplies the literal quotient
step in the cost-four branch of Stellmacher (8.6), Journal of Algebra
190 (1997). The graph consumer supplies the quotient W, the plane U, and
the actual residual and involution operators.
-/

open scoped IsMulCommutative

public theorem commutatorAction_eq_bot_or_four_plane_of_central_involution
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (R : Subgroup (MulAut W)) (U : Subgroup W) [IsInvariant R W U]
    (hW : Nat.card W = 16) (hU : Nat.card U = 4)
    (hfixed : FixedPoints.subgroup R W = ⊥)
    (t : MulAut W) (ht : t ^ 2 = 1)
    (htR : t ∈ Subgroup.centralizer (R : Set (MulAut W)))
    (hUfix : ∀ point ∈ U, t point = point) :
    commutatorAction (Subgroup.zpowers t) W = ⊥ ∨
      commutatorAction (Subgroup.zpowers t) W = U := by
  classical
  by_cases htrivial : t = 1
  · left
    apply bot_unique
    rw [commutatorAction_eq_closure,Subgroup.closure_le]
    rintro _ ⟨actor,point,rfl⟩
    have hactor : (actor : MulAut W) = 1 := by
      obtain ⟨power,hpower⟩ := actor.property
      simpa only [htrivial,one_zpow] using hpower.symm
    change point⁻¹ * (actor : MulAut W) point = 1
    rw [hactor]
    exact inv_mul_cancel point
  let T := Subgroup.zpowers t
  let C := FixedPoints.subgroup T W
  let D := commutatorAction T W
  let _ : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by rw [hW]; decide)
  have hTcard : Nat.card T = 2 := by
    rw [Nat.card_zpowers,orderOf_eq_prime ht htrivial]
  let generator : T := ⟨t,Subgroup.mem_zpowers t⟩
  have hgenerator : generator ≠ 1 ∧ generator ^ 2 = 1 :=
    ⟨fun heq => htrivial (congrArg Subtype.val heq),Subtype.ext ht⟩
  obtain ⟨hprod,hDC⟩ := card_two_action_fixed_commutator_card_data
    (U := W) generator hgenerator hTcard
  change Nat.card W = Nat.card C * Nat.card D at hprod
  rw [hW] at hprod
  have hUC : U ≤ C := by
    intro point hpoint actor
    exact smul_eq_self_of_mem_zpowers actor.property (hUfix point hpoint)
  have hClower : 4 ≤ Nat.card C := hU ▸ Subgroup.card_le_of_le hUC
  have hDupper : Nat.card D ≤ 4 := by nlinarith
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have hnormal : R ≤ Subgroup.normalizer (T : Set (MulAut W)) :=
    (Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr htR)).trans
      (Subgroup.centralizer_le_normalizer _)
  let _ : IsInvariant R W D := commutatorAction_isInvariant_of_normalizing_actor R T hnormal
  have hDnotTwo : Nat.card D ≠ 2 := by
    intro hDtwo
    obtain ⟨point,hpointNe,hunique⟩ := (Nat.card_eq_two_iff' (1 : D)).mp hDtwo
    have hpoint : (point : W) ≠ 1 := fun heq => hpointNe (Subtype.ext heq)
    have hpointFixed : (point : W) ∈ FixedPoints.subgroup R W := by
      intro actor
      have hmem : (actor : MulAut W) (point : W) ∈ D :=
        (IsInvariant.invariant (A := R) (G := W) (H := D) actor point).mp point.property
      have hne : (⟨(actor : MulAut W) point,hmem⟩ : D) ≠ 1 := by
        intro heq
        exact hpoint ((actor : MulAut W).injective
          ((congrArg Subtype.val heq).trans (map_one (actor : MulAut W)).symm))
      exact congrArg Subtype.val (hunique _ hne)
    rw [hfixed] at hpointFixed
    exact hpoint hpointFixed
  have hDcases : Nat.card D = 1 ∨ Nat.card D = 4 := by
    interval_cases h : Nat.card D
    all_goals omega
  rcases hDcases with hDone | hDfour
  · exact Or.inl (Subgroup.card_eq_one.mp hDone)
  · right
    have hCfour : Nat.card C = 4 := by rw [hDfour] at hprod; omega
    have hDCeq : D = C := Subgroup.eq_of_le_of_card_ge hDC (by rw [hDfour,hCfour])
    have hUCeq : U = C := Subgroup.eq_of_le_of_card_ge hUC (by rw [hU,hCfour])
    exact hDCeq.trans hUCeq.symm
