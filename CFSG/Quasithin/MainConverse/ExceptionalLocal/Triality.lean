module

public import CFSG.Quasithin.MainConverse.ExceptionalLocal.Triality.OddRankReduction
public import Theory.Quasithin.EvenCharacteristic
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.Triality.FullParabolicActions
public import Theory.SpecificGroups.Triality.TwoLocalCover

/-!
# Local assembly for genuine characteristic-two triality

The converse in Aschbacher--Smith, Theorem 0.1.2(1), printed pp.3--4
(repeated on pp.481--482), requires odd-prime rank at most two in every
maximal two-local and the intrinsic two-core centralizer condition in those
containing a Sylow two-subgroup.

The reductions below use the genuine pinned D4 graph-field carrier and its
two descended parabolics. Conjugate containment transfers the rank bound.
Because each parabolic normalizes its root-defined radical, a nonidentity
two-group radical upgrades containment of a maximal two-local to equality.
Relative self-centralization of the radical then implies self-centralization
of the intrinsic two-core. Only relative normality inside the parabolic is
used; the radical is not asserted to be normal in the ambient carrier.

The imported rank reduction derives the parabolic bounds from genuine PSL₂
quotients of the local factors and cyclic quotients of the full parabolics.

The final theorems discharge the conditional reductions using the proved
hexagon coverage, radical orders, cyclic torus quotients and faithful Levi
actions. Thus every genuine binary carrier satisfies QT and E, including
q = 2, with no simplicity or perfectness assumption. In fact every maximal
two-local has characteristic two. Actual group isomorphisms transfer this
result to `IsTrialityGroupAt (2^f)` and the full QTKE triality model family.
The local factor O^{2'} remains distinct from the full parabolic throughout.
The elementary fixed-point subgroup and the quotient by its own center
are retained by the definitions from `StandardModel` and `RootParabolics`.
-/

public section

namespace CFSG.Quasithin.MainConverse.TrialityLocal

open Subgroup Triality.Standard Triality.Standard.Parabolics

variable (P : Parameters)

/-- Odd-prime ranks transfer from the two full parabolics once they cover
conjugates of every maximal two-local. -/
theorem quasithin_of_maximal_parabolic_cover
    (hcover : ∀ M : Subgroup (Carrier P), IsMaximalTwoLocal M →
      ∃ (g : Carrier P) (a : Node),
        M.map (MulAut.conj g).toMonoidHom ≤ parabolic P a)
    (hrank : ∀ (a : Node) (p : ℕ), p.Prime → Odd p →
      primeRank p (parabolic P a) ≤ 2) : IsQuasithin (Carrier P) := by
  apply Theory.GroupTheory.isQuasithin_iff_maximalTwoLocal.mpr
  intro M hM p hp ho
  obtain ⟨g, a, hle⟩ := hcover M hM
  rw [Theory.GroupTheory.primeRank_equiv p ((MulAut.conj g).subgroupMap M)]
  exact (Theory.GroupTheory.primeRank_le_of_injective p (inclusion hle)
    (inclusion_injective hle)).trans (hrank a p hp ho)

/-- A maximal two-local contained in a parabolic equals that parabolic as
soon as the genuine radical is a nonidentity two-group. -/
theorem maximalTwoLocal_eq_parabolic_of_le (a : Node)
    (hR : radical P a ≠ ⊥) (hRtwo : IsPGroup 2 (radical P a))
    {M : Subgroup (Carrier P)} (hM : IsMaximalTwoLocal M)
    (hle : M ≤ parabolic P a) : M = parabolic P a := by
  have hnorm : parabolic P a ≤ normalizer (radical P a : Set (Carrier P)) :=
    (normal_subgroupOf_iff_le_normalizer (radical_le_parabolic P a)).mp
      (radical_normal P a)
  have hlocal : IsTwoLocal (normalizer (radical P a : Set (Carrier P))) :=
    ⟨radical P a, hR, hRtwo, rfl⟩
  exact le_antisymm hle (hnorm.trans (hM.2 hlocal (hle.trans hnorm)))

/-- Conjugate containment yields the exact catalogue of maximal two-locals,
using only relative normality and nontriviality of the radicals. -/
theorem maximalTwoLocal_conjugate_of_parabolic_cover
    (hcover : ∀ M : Subgroup (Carrier P), IsMaximalTwoLocal M →
      ∃ (g : Carrier P) (a : Node),
        M.map (MulAut.conj g).toMonoidHom ≤ parabolic P a)
    (hR : ∀ a : Node, radical P a ≠ ⊥)
    (hRtwo : ∀ a : Node, IsPGroup 2 (radical P a))
    (M : Subgroup (Carrier P)) (hM : IsMaximalTwoLocal M) :
    ∃ (g : Carrier P) (a : Node),
      M.map (MulAut.conj g).toMonoidHom = parabolic P a := by
  obtain ⟨g, a, hle⟩ := hcover M hM
  exact ⟨g, a, maximalTwoLocal_eq_parabolic_of_le P a (hR a) (hRtwo a)
    (Theory.Quasithin.isMaximalTwoLocal_map (MulAut.conj g) hM) hle⟩

/-- Centralization is tested inside the full parabolic. A self-centralizing
normal two-subgroup lies in its intrinsic two-core and forces characteristic two. -/
theorem parabolic_characteristicTwo_of_radical (a : Node)
    (hRtwo : IsPGroup 2 (radical P a))
    (hcent : parabolic P a ⊓ centralizer (radical P a : Set (Carrier P)) ≤
      radical P a) : HasCharacteristicTwo (parabolic P a) := by
  have hcore : (radical P a).subgroupOf (parabolic P a) ≤
      pCore 2 (parabolic P a) :=
    le_sSup ⟨radical_normal P a, hRtwo.comap_subtype⟩
  intro x hx
  apply hcore
  apply hcent
  refine ⟨x.property, ?_⟩
  intro y hy
  exact congrArg Subtype.val
    (hx ⟨y, radical_le_parabolic P a hy⟩ (hcore hy))

/-- The intrinsic two-core of every maximal two-local is self-centralizing
when coverage and the two root-radical calculations have been supplied. -/
theorem characteristicTwo_of_maximal_parabolic_cover
    (hcover : ∀ M : Subgroup (Carrier P), IsMaximalTwoLocal M →
      ∃ (g : Carrier P) (a : Node),
        M.map (MulAut.conj g).toMonoidHom ≤ parabolic P a)
    (hR : ∀ a : Node, radical P a ≠ ⊥)
    (hRtwo : ∀ a : Node, IsPGroup 2 (radical P a))
    (hcent : ∀ a : Node,
      parabolic P a ⊓ centralizer (radical P a : Set (Carrier P)) ≤ radical P a)
    (M : Subgroup (Carrier P)) (hM : IsMaximalTwoLocal M) :
    HasCharacteristicTwo M := by
  obtain ⟨g, a, heq⟩ :=
    maximalTwoLocal_conjugate_of_parabolic_cover P hcover hR hRtwo M hM
  have hc : HasCharacteristicTwo (M.map (MulAut.conj g).toMonoidHom) := by
    rw [heq]
    exact parabolic_characteristicTwo_of_radical P a (hRtwo a) (hcent a)
  exact hc.of_equiv ((MulAut.conj g).subgroupMap M).symm

/-- Conditional assembly of QT and E, with all remaining concrete geometric,
rank and radical inputs displayed. This is not yet the source converse. -/
theorem quasithin_evenCharacteristic_of_local_calculations
    (hcover : ∀ M : Subgroup (Carrier P), IsMaximalTwoLocal M →
      ∃ (g : Carrier P) (a : Node),
        M.map (MulAut.conj g).toMonoidHom ≤ parabolic P a)
    (hrank : ∀ (a : Node) (p : ℕ), p.Prime → Odd p →
      primeRank p (parabolic P a) ≤ 2)
    (hR : ∀ a : Node, radical P a ≠ ⊥)
    (hRtwo : ∀ a : Node, IsPGroup 2 (radical P a))
    (hcent : ∀ a : Node,
      parabolic P a ⊓ centralizer (radical P a : Set (Carrier P)) ≤ radical P a) :
    IsQuasithin (Carrier P) ∧ IsEvenCharacteristic (Carrier P) := by
  refine ⟨quasithin_of_maximal_parabolic_cover P hcover hrank, ?_⟩
  intro T M hM _
  exact characteristicTwo_of_maximal_parabolic_cover P hcover hR hRtwo hcent M hM

/-- The same conditional assembly for an arbitrary group at binary field order,
transported through the actual isomorphism to the specified genuine carrier. -/
theorem quasithin_evenCharacteristic_of_isTrialityGroupAt_of_local_calculations
    {G : Type*} [Group G] [Finite G] (f : ℕ) (hf : 0 < f)
    (hG : IsTrialityGroupAt (2 ^ f) G)
    (hcover : ∀ M : Subgroup (BinaryCarrier f hf), IsMaximalTwoLocal M →
      ∃ (g : BinaryCarrier f hf) (a : Node),
        M.map (MulAut.conj g).toMonoidHom ≤ parabolic (binaryParameters f hf) a)
    (hrank : ∀ (a : Node) (p : ℕ), p.Prime → Odd p →
      primeRank p (parabolic (binaryParameters f hf) a) ≤ 2)
    (hR : ∀ a : Node, radical (binaryParameters f hf) a ≠ ⊥)
    (hRtwo : ∀ a : Node, IsPGroup 2 (radical (binaryParameters f hf) a))
    (hcent : ∀ a : Node, parabolic (binaryParameters f hf) a ⊓
      centralizer (radical (binaryParameters f hf) a : Set (BinaryCarrier f hf)) ≤
        radical (binaryParameters f hf) a) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff G f hf).mp hG
  have hqt := quasithin_of_maximal_parabolic_cover (binaryParameters f hf) hcover hrank
  refine ⟨Theory.GroupTheory.isQuasithin_of_equiv e.symm hqt, ?_⟩
  intro T M hM _
  apply (Theory.Quasithin.centralizer_pCore_map_le_iff 2 e M).mp
  exact characteristicTwo_of_maximal_parabolic_cover (binaryParameters f hf)
    hcover hR hRtwo hcent _ (Theory.Quasithin.isMaximalTwoLocal_map e hM)

private theorem radical_ne_bot_of_char_two (P : Parameters) (hp : P.prime = 2) (a : Node) :
    radical P a ≠ ⊥ := by
  intro hbot
  have hcard := RadicalCoordinates.radical_card P hp a
  rw [hbot, Subgroup.card_bot] at hcard
  have hq : 1 < P.q := lt_of_lt_of_le (by decide : 1 < (2 : ℕ)) P.q_ge_two
  have hdim : RadicalCoordinates.fixedDimension a ≠ 0 := by cases a <;> decide
  exact (ne_of_gt (one_lt_pow₀ hq hdim)) hcard.symm

/-- Every maximal two-local of the genuine binary triality carrier is
conjugate to one of its two full root parabolics, including at q = 2. -/
theorem binaryCarrier_maximalTwoLocal_conjugate (f : ℕ) (hf : 0 < f)
    (M : Subgroup (BinaryCarrier f hf)) (hM : IsMaximalTwoLocal M) :
    ∃ (g : BinaryCarrier f hf) (a : Node),
      M.map (MulAut.conj g).toMonoidHom = parabolic (binaryParameters f hf) a :=
  maximalTwoLocal_conjugate_of_parabolic_cover (binaryParameters f hf)
    (TwoLocalCover.maximalTwoLocal_cover f hf)
    (radical_ne_bot_of_char_two _ rfl) (RadicalCoordinates.radical_isPGroup _ rfl) M hM

/-- The full maximal two-locals have odd-prime ranks at most two. -/
theorem binaryCarrier_maximalTwoLocal_primeRank_le_two (f : ℕ) (hf : 0 < f)
    (M : Subgroup (BinaryCarrier f hf)) (hM : IsMaximalTwoLocal M)
    {p : ℕ} (hprime : p.Prime) (hodd : Odd p) : primeRank p M ≤ 2 := by
  obtain ⟨g, a, heq⟩ := binaryCarrier_maximalTwoLocal_conjugate f hf M hM
  rw [Theory.GroupTheory.primeRank_equiv p ((MulAut.conj g).subgroupMap M)]
  change primeRank p (M.map (MulAut.conj g).toMonoidHom) ≤ 2
  rw [heq]
  exact parabolic_primeRank_le_two _ rfl a hprime hodd

/-- The intrinsic two-core of every maximal two-local is self-centralizing.
This also supplies the source condition for those containing a Sylow two-subgroup. -/
theorem binaryCarrier_maximalTwoLocal_characteristicTwo (f : ℕ) (hf : 0 < f)
    (M : Subgroup (BinaryCarrier f hf)) (hM : IsMaximalTwoLocal M) :
    HasCharacteristicTwo M :=
  characteristicTwo_of_maximal_parabolic_cover (binaryParameters f hf)
    (TwoLocalCover.maximalTwoLocal_cover f hf)
    (radical_ne_bot_of_char_two _ rfl) (RadicalCoordinates.radical_isPGroup _ rfl)
    (parabolic_centralizer_radical_le _ rfl) M hM

/-- The QT and E clauses of the converse for genuine ³D₄(2^f), for every f ≥ 1.
All concrete local premises have been discharged. -/
theorem binaryCarrier_quasithin_and_evenCharacteristic (f : ℕ) (hf : 0 < f) :
    IsQuasithin (BinaryCarrier f hf) ∧ IsEvenCharacteristic (BinaryCarrier f hf) := by
  refine ⟨Theory.GroupTheory.isQuasithin_iff_maximalTwoLocal.mpr ?_, ?_⟩
  · intro M hM p hp ho
    exact binaryCarrier_maximalTwoLocal_primeRank_le_two f hf M hM hp ho
  · intro T M hM _
    exact binaryCarrier_maximalTwoLocal_characteristicTwo f hf M hM

/-- The source converse for any isomorphic standard triality group at binary
field order. The isomorphism bridge retains the specified positive exponent. -/
theorem quasithin_and_evenCharacteristic_of_isTrialityGroupAt
    {G : Type*} [Group G] [Finite G] (f : ℕ) (hf : 0 < f)
    (hG : IsTrialityGroupAt (2 ^ f) G) : IsQuasithin G ∧ IsEvenCharacteristic G := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff G f hf).mp hG
  refine ⟨Theory.GroupTheory.isQuasithin_of_equiv e.symm
    (binaryCarrier_quasithin_and_evenCharacteristic f hf).1, ?_⟩
  intro T M hM _
  apply (Theory.Quasithin.centralizer_pCore_map_le_iff 2 e M).mp
  exact binaryCarrier_maximalTwoLocal_characteristicTwo f hf _
    (Theory.Quasithin.isMaximalTwoLocal_map e hM)

/-- The complete triality-family QT/E input for the exceptional converse assembly.
The model predicate supplies only an actual carrier isomorphism, not QT or E. -/
theorem quasithin_and_evenCharacteristic_of_isQTKETrialityModel
    {G : Type*} [Group G] [Finite G] (hG : Triality.IsQTKETrialityModel G) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  obtain ⟨f, hf, h⟩ := (Triality.isQTKETrialityModel_iff_fieldOrder G).mp hG
  exact quasithin_and_evenCharacteristic_of_isTrialityGroupAt f hf h

end CFSG.Quasithin.MainConverse.TrialityLocal
