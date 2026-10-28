module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.Geometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.NineSections
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.NineGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.TorusGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.MaximalOvergroups
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.OddLocals

/-!
# Full semilinear escape for families containing linear four-groups

For an odd-prime subgroup normalized by the actual Sylow centralizer of A,
the general odd-commutator theorem produces intrinsic rank-one E-members.
Its construction takes the join with the full tau and proves the literal
Sylow intersection. It is not restricted to S₄ or dihedral local groups.

For an inner actor over the field of nine, an appropriately positioned
field-involution centralizer instead has a genuine S₃ quotient. The new
centralizer calculation supplies its ambient tau condition, and the
quotient calculation proves all intrinsic E1 clauses.

The final theorem `escape` discharges both geometric existence statements in
`Geometry`, using the prime-square PGL₂ maximal-overgroup classification for
the torus branch and the full four-group normalizer calculations over F₉.
It supplies the literal hlinear input of
`RankTwoFamilies.escape_of_linear_and_marked`, including p=3 and p=5.
The original family and its weak closure are preserved throughout.

Source: Aschbacher–Smith A.2.3(2), E.1.2, E.1.14(6), pp.33, 209–210, 214;
the last cites Aschbacher (1982), Lemma 4.10.
-/

public section
open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors
variable {F : Type*} [Field F] [Finite F] [Finite (PGammaL2 F)]

/-- The odd commutator construction uses the full ambient tau and keeps
the actor in the original family. All E1 and Sylow clauses are discharged
by the general odd-local theorem. -/
theorem escape_of_normalized_odd_commutator {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    (T : Sylow 2 (PGammaL2 F)) (Ω : Set (Subgroup (PGammaL2 F)))
    (hΩ : IsElementaryFamily Ω) (A : Subgroup (PGammaL2 F))
    (hAΩ : A ∈ Ω) (hAT : A ≤ (T : Subgroup _))
    {r : ℕ} (hr : r.Prime) (hro : Odd r) (X : Subgroup (PGammaL2 F))
    (hX : IsPGroup r X)
    (hn : (T : Subgroup _) ⊓ centralizer (A : Set (PGammaL2 F)) ≤ normalizer (X : Set _))
    (M : Subgroup (PGammaL2 F)) (hmove : ¬ ⁅X, A⁆ ≤ M) :
    ∃ B ∈ Ω, B ≤ (T : Subgroup _) ∧ ∃ H, IsEMemberAt 1 (T : Subgroup _) B H ∧ ¬ H ≤ M := by
  let := hΩ.1 A hAΩ
  let : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by rintro rfl; norm_num at hro
  have htau : tau (T : Subgroup _) A ≤ normalizer (X : Set _) := by
    rwa [full_tau_eq_inf_centralizer hp ho hF hlarge]
  obtain ⟨H, hH, hHM⟩ :=
    PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.exists_escaping_member_of_normalized_odd_commutator
      T A hAT hr2 X hX htau M hmove
  exact ⟨A, hAΩ, hAT, H, hH, hHM⟩

/-- Conditional assembly with exactly the parent's hlinear conclusion.
The unconditional theorem `escape` below discharges both geometric inputs,
including p=3 and p=5. -/
theorem escape_of_tori_and_nine {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    (htori : OddTorusPlacement F p) (hnine : p = 3 → NineFieldPlacement F) :
    ∀ (T : Sylow 2 (PGammaL2 F)) (Ω : Set (Subgroup (PGammaL2 F))),
      IsElementaryFamily Ω →
      (∀ A ∈ Ω, A ≤ (T : Subgroup _) → A ≠ ⊥ → Group.rank A = 2 ∨ Group.rank A = 3) →
      (∃ A ∈ Ω, A ≤ (T : Subgroup _) ∧ Group.rank A = 2 ∧ A ≤ pGammaL2PGLRange F) →
      ∀ M : Subgroup (PGammaL2 F), IsCoatom M → (T : Subgroup _) ≤ M →
        normalizer (weakClosure (T : Subgroup _) Ω : Set _) ≤ M →
        ∃ B ∈ Ω, B ≤ (T : Subgroup _) ∧ ∃ H, IsEMemberAt 1 (T : Subgroup _) B H ∧ ¬ H ≤ M := by
  intro T Ω hΩ _hrange hlinear M hM hTM _hNM
  obtain ⟨A, hAΩ, hAT, hr, hAL⟩ := hlinear
  by_cases hcase : 5 ≤ p ∨ ¬ A ≤ pGammaL2PSLRange F
  · obtain ⟨r, hrp, hro, X, hX, hn, hmove⟩ :=
      htori T A (hΩ.1 A hAΩ) hr hAL hAT hcase M hM hTM
    exact escape_of_normalized_odd_commutator hp ho hF hlarge T Ω hΩ A hAΩ hAT
      hrp hro X hX hn M hmove
  have hsmall : p < 5 := Nat.lt_of_not_ge (fun h => hcase (Or.inl h))
  have hinner : A ≤ pGammaL2PSLRange F := by
    by_contra h
    exact hcase (Or.inr h)
  have hp3 : p = 3 := by
    have := hp.two_le
    obtain ⟨k, hk⟩ := ho
    omega
  have hF9 : Nat.card F = 3 ^ 2 := hp3 ▸ hF
  obtain ⟨x, hx, hf, hc, hSyl, ha, hgen⟩ := hnine hp3 T A (hΩ.1 A hAΩ) hr hinner hAT
  refine ⟨A, hAΩ, hAT, centralizer ({x} : Set (PGammaL2 F)),
    isEMemberAt_nine_fieldCentralizer hF9 T A (hΩ.1 A hAΩ) hr hAL hAT
      x hx hf hc hSyl ha, ?_⟩
  intro hCM
  apply hM.ne_top
  apply top_unique
  rw [← hgen]
  exact sup_le hTM hCM

/-- Families containing a linear four-group admit an intrinsic rank-one
E-member escaping every maximal overgroup in the parent's hlinear contract.
Both geometric branches and the PGL₂ overgroup classification are discharged;
no generation or placement hypothesis is required. The full semilinear tau,
literal Sylow intersection, original family and weak closure are retained. -/
theorem escape {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2) :
    ∀ (T : Sylow 2 (PGammaL2 F)) (Ω : Set (Subgroup (PGammaL2 F))),
      IsElementaryFamily Ω →
      (∀ A ∈ Ω, A ≤ (T : Subgroup _) → A ≠ ⊥ → Group.rank A = 2 ∨ Group.rank A = 3) →
      (∃ A ∈ Ω, A ≤ (T : Subgroup _) ∧ Group.rank A = 2 ∧ A ≤ pGammaL2PGLRange F) →
      ∀ M : Subgroup (PGammaL2 F), IsCoatom M → (T : Subgroup _) ≤ M →
        normalizer (weakClosure (T : Subgroup _) Ω : Set _) ≤ M →
        ∃ B ∈ Ω, B ≤ (T : Subgroup _) ∧ ∃ H, IsEMemberAt 1 (T : Subgroup _) B H ∧ ¬ H ≤ M := by
  let : Fact p.Prime := ⟨hp⟩
  apply escape_of_tori_and_nine hp ho hF hlarge
  · exact oddTorusPlacement_of_sylowOvergroups hp ho hF hlarge
      (LinearWitnesses.DiagonalPlacement.MaximalOvergroups.sylowOvergroupModel_of_square_card
        ho hlarge hF)
  · intro hp3
    exact NineGeometry.nineFieldPlacement (hp3 ▸ hF)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors
