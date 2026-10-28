module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.CoreAction
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.SmallActions.CodeRank
public import Theory.SpecificGroups.SL2.BinaryDihedral

/-!
# Excluding the cubic quotient in the M₂₄ code row

Apply the canonical conjugation action on the literal P/U in Y = RI.
The earlier B/U kernel, two-conjugate generation and E.2.14 centralizer
calculation give Y/O₂(Y) as the marked product of the original two-core
quotients. An L₂(2) marking supplies centerlessness internally. In the code
row the other factor is the actual nonsplit triple-A₆ model, so this
product contains an elementary subgroup of order 27, which lifts through
O₂(Y) and embeds into the prescribed N_G(U). This contradicts m₃(N_G(U))≤2.

The final selection theorem consumes, but does not prove, the independent
small-action sieve. Its discharge remains with the SmallActions assembly.
The faithful triple-cover marking and the earlier source local calculations
remain explicit inputs, as permitted by this conditional action task.

Source: Aschbacher–Smith, Proposition 8.2.8(6), opening paragraph on printed
p.719 (PDF p.736), with the canonical quotient conventions of `CoreAction`.
-/

public section
open scoped commutatorElement
open Subgroup Atlas.Codes Theory.SpecificGroups.BinaryDihedral
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.SmallActions
variable {G : Type*} [Group G] [Finite G]
variable (I U : Subgroup G) [I.Normal] [U.Normal]

/-- The canonical action yields an elementary cube in Y if its two factors
are the actual triple-A₆ and L₂(2) models. -/
theorem coreQuotientAction_code_cubic_cube
    (R V : Subgroup G)
    (hgen : R ⊔ I = ⊤) (h : G)
    (hP : (V ⊓ I.pCoreIn 2) ⊔
      (V ⊓ I.pCoreIn 2).map (MulAut.conj h⁻¹).toMonoidHom = I.pCoreIn 2)
    (hcomm : ⁅R, I⁆ ≤ R.pCoreIn 2)
    (hB : ∀ r : R,
      (∀ b : ↥(V ⊓ I.pCoreIn 2), ⁅(r : G), (b : G)⁆ ∈ U) ↔ r ∈ pCore 2 R)
    (hI : centralizerModulo I (I.pCoreIn 2) U = I.pCoreIn 2)
    (eR : (R ⧸ pCore 2 R) ≃* HexEvenAutomorphisms)
    (eI : (I ⧸ pCore 2 I) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2)) :
    ∃ E : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 27 := by
  have hz := center_eq_bot_of_psl2Two_model eI
  obtain ⟨e, _⟩ := coreQuotientAction_quotient_product I U R V hgen h hP hcomm hB hI hz
  exact exists_elementary_cube_of_code_cubic_quotient
    (e.trans (eR.prodCongr (eI.trans dihedralThreeEquivPSL2Two.symm)))

/-- The earlier m₃(N_G(U)) bound rules out the actual cubic quotient. The
homomorphism embeds the local group Y into that prescribed normalizer. -/
theorem coreQuotientAction_code_not_cubic
    (R V : Subgroup G)
    (hgen : R ⊔ I = ⊤) (h : G)
    (hP : (V ⊓ I.pCoreIn 2) ⊔
      (V ⊓ I.pCoreIn 2).map (MulAut.conj h⁻¹).toMonoidHom = I.pCoreIn 2)
    (hcomm : ⁅R, I⁆ ≤ R.pCoreIn 2)
    (hB : ∀ r : R,
      (∀ b : ↥(V ⊓ I.pCoreIn 2), ⁅(r : G), (b : G)⁆ ∈ U) ↔ r ∈ pCore 2 R)
    (hI : centralizerModulo I (I.pCoreIn 2) U = I.pCoreIn 2)
    (eR : (R ⧸ pCore 2 R) ≃* HexEvenAutomorphisms)
    {A : Type*} [Group A] [Finite A] (U₀ : Subgroup A)
    (j : G →* normalizer (U₀ : Set A)) (hj : Function.Injective j)
    (hrank : primeRank 3 (normalizer (U₀ : Set A)) ≤ 2) :
    ¬ Nonempty ((I ⧸ pCore 2 I) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2)) := by
  rintro ⟨eI⟩
  obtain ⟨E, hE, hEc⟩ := coreQuotientAction_code_cubic_cube I U R V hgen h hP hcomm hB hI eR eI
  let := hE
  let : IsElementaryAbelian 3 (E.map j) := IsElementaryAbelian.map j
  have hcard : Nat.card (E.map j) = 3 ^ 3 := by
    rw [card_map_of_injective hj, hEc]
    rfl
  have hl := IsElementaryAbelian.primeRank_ge_of_card (E.map j) hcard
  omega

/-- Once the independent finite-action sieve supplies its two genuine model
alternatives, the code row selects D₁₀. The rank obstruction is discharged
here; the small-action sieve is deliberately still an explicit premise. -/
theorem coreQuotientAction_code_dihedral_selection
    (R V : Subgroup G)
    (hgen : R ⊔ I = ⊤) (h : G)
    (hP : (V ⊓ I.pCoreIn 2) ⊔
      (V ⊓ I.pCoreIn 2).map (MulAut.conj h⁻¹).toMonoidHom = I.pCoreIn 2)
    (hcomm : ⁅R, I⁆ ≤ R.pCoreIn 2)
    (hB : ∀ r : R,
      (∀ b : ↥(V ⊓ I.pCoreIn 2), ⁅(r : G), (b : G)⁆ ∈ U) ↔ r ∈ pCore 2 R)
    (hI : centralizerModulo I (I.pCoreIn 2) U = I.pCoreIn 2)
    (eR : (R ⧸ pCore 2 R) ≃* HexEvenAutomorphisms)
    {A : Type*} [Group A] [Finite A] (U₀ : Subgroup A)
    (j : G →* normalizer (U₀ : Set A)) (hj : Function.Injective j)
    (hrank : primeRank 3 (normalizer (U₀ : Set A)) ≤ 2)
    (hsieve : Nonempty ((I ⧸ pCore 2 I) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2)) ∨
      Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 5)) :
    Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 5) := by
  exact hsieve.resolve_left
    (coreQuotientAction_code_not_cubic I U R V hgen h hP hcomm hB hI eR U₀ j hj hrank)

end CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.SmallActions
