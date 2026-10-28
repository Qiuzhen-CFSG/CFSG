module

public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.NormalizingActor
public import Theory.GroupTheory.Commutator.ActionTriviality
public import Theory.ElementaryAbelian.Basic

/-!
# Common displacement under a full order-three action

Let J and C act on a finite elementary abelian two-group W, where C has
order three, centralizes J, and has full displacement. If the common
J-displacement has order four, every nonidentity actor in J has that
same displacement.

Coprime splitting makes the C-fixed subgroup trivial. Commutation makes
each cyclic displacement C-invariant. Orbit counting then gives its order
congruent to one modulo three; nontriviality and the bound four force equality.
-/

public theorem commutatorAction_zpowers_eq_of_full_three
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (J C : Subgroup (MulAut W))
    (hdisplacement : Nat.card (commutatorAction J W) = 4)
    (hCcard : Nat.card C = 3) (hCfull : commutatorAction C W = ⊤)
    (hCJ : ⁅C, J⁆ = ⊥) (actor : MulAut W) (hactor : actor ∈ J)
    (hne : actor ≠ 1) :
    commutatorAction (Subgroup.zpowers actor) W = commutatorAction J W := by
  let K := Subgroup.zpowers actor
  let D := commutatorAction K W
  have hKJ : K ≤ J := Subgroup.zpowers_le.mpr hactor
  have hCD : IsInvariant C W D := by
    apply commutatorAction_isInvariant_of_normalizing_actor
    apply le_trans _ (Subgroup.centralizer_le_normalizer (K : Set (MulAut W)))
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    exact (Subgroup.commutator_mono le_rfl hKJ).trans hCJ.le
  let : IsInvariant C W D := hCD
  have hcop : Nat.Coprime (Nat.card C) (Nat.card W) := by
    obtain ⟨dimension, hdimension⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    rw [hCcard, hdimension]
    exact (by decide : Nat.Coprime 3 2).pow_right dimension
  have hfixed : FixedPoints.subgroup C W = ⊥ := by
    have hcompl :=
      isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        (G := W) (A := C)
        (Group.isSolvable_of_comm fun left right =>
          (IsMulCommutative.is_comm (M := W)).comm left right) hcop inferInstance
    have hdisjoint := hcompl.disjoint.eq_bot
    simpa [hCfull] using hdisjoint
  have hfixedD : FixedPoints.subgroup C D = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro point hpoint
    apply Subtype.ext
    have hmem : (point : W) ∈ FixedPoints.subgroup C W := by
      intro central
      exact congrArg Subtype.val (hpoint central)
    simpa [hfixed] using hmem
  have hDle : D ≤ commutatorAction J W := by
    change commutatorAction K W ≤ commutatorAction J W
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    apply Subgroup.closure_mono
    rintro point ⟨generator, vector, rfl⟩
    exact ⟨⟨(generator : MulAut W), hKJ generator.property⟩, vector, rfl⟩
  have hDne : D ≠ ⊥ := by
    intro hbot
    apply hne
    ext point
    exact actsTrivially_of_commutatorAction_eq_bot hbot
      ⟨actor, Subgroup.mem_zpowers actor⟩ point
  have hDcardNe : Nat.card D ≠ 1 := by
    intro hcard
    exact hDne (Subgroup.card_eq_one.mp hcard)
  have hDcardLe : Nat.card D ≤ 4 := by
    simpa [hdisplacement] using Subgroup.card_le_of_le hDle
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCp : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by simpa using hCcard)
  have hmod : Nat.ModEq 3 (Nat.card D) 1 := by
    have hcount := hCp.card_modEq_card_fixedPoints D
    change Nat.ModEq 3 (Nat.card D) (Nat.card (FixedPoints.subgroup C D)) at hcount
    simpa [hfixedD] using hcount
  have hDcard : Nat.card D = 4 := by
    have hpos : 0 < Nat.card D := Nat.card_pos
    unfold Nat.ModEq at hmod
    omega
  exact Subgroup.eq_of_le_of_card_ge hDle (by rw [hdisplacement, hDcard])
