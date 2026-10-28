module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryFrattini
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnequalLinearRadicals
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryFrattini
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnequalLinearRadicals

/-!
# The field orders of a mixed linear-unitary quadrangle

The unitary root center lies in the Frattini subgroup of its own radical.
The faithful SU3 action on the Frattini quotient has binary degree at least
six times the unitary degree, also at parameter two. Thus that radical has
order at least q^7. At the linear endpoint the reflection moves a nonzero
unitary derived root inside the derived radical. The two successive
Frattini degree bounds force the linear radical to have order at least
|F|^4. The actual three-root orders then force |F| = q^2.

The two import-all edges deliberately extend the internal quadrangle proof
family: they reuse its root-specialness, root-order and linear Frattini
lemmas without changing the established public boundaries. All new public
statements use the literal roots, actions and covers on the same quotient.
The original factor and Chapter 12 consumers remove the corresponding
field-ratio hypothesis; regularity is still needed at the binary unitary
endpoint. Source: Fong--Seitz I (4B), (4D), (6A)(c), pp.19--23,37.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The actual unitary cover forces radical order at least q^7, including q = 2. -/
theorem unitary_remainder_card_lower_of_cover
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split j)
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple j}) :
      Set (Q.tits.standardParabolic {Q.simple j})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple j}))
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (π : J.specialSubgroup →* rankOne Q split j) (hπ : Function.Surjective π)
    (hπν : ∀ a, ν (RootLocalCover.projection Q split j (π a)) = J.specialToProjective a) :
    (2^n)^7 ≤ Nat.card (simpleRemainder Q split j) := by
  let V := simpleRemainder Q split j
  let C := rootAt Q split j (Q.simple i)
  let Z := (center C).map C.subtype
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hE hconj
  have hspecial : _root_.commutator C = center C :=
    unitary_cross_root_special Q split J hn hE hfixed hJ j (Q.simple i) hVj ν
  have hCV : C ≤ V := cross_root_le_own_remainder Q split hm j i hij.symm
  have hZD : Z ≤ ⁅V,V⁆ := by
    rw [show Z = (center C).map C.subtype from rfl,←hspecial,map_subtype_commutator]
    exact commutator_mono hCV hCV
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  have hDΦ : ⁅V,V⁆ ≤ (frattini V).map V.subtype := by
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  have hZΦ := hZD.trans hDΦ
  have hZcard : Nat.card Z = 2^n := by
    rw [show Z = (center C).map C.subtype from rfl,card_map_of_injective C.subtype_injective]
    exact unitary_cross_center_card Q split J hn hE hfixed hJ j (Q.simple i) hVj ν
  let W := V ⧸ frattini V
  let : IsElementaryAbelian 2 W := isElementaryAbelian_quotient_frattini
  let ρ := elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)
  have hρ : Function.Injective ρ := by
    intro a b hab
    apply remainderFrattiniAction_injective Q split j s hVj hc
    ext v
    exact Additive.ofMul.injective
      (congrArg (fun f : Module.End (ZMod 2) (Additive W) => f (Additive.ofMul v)) hab)
  let σ := ρ.comp π
  have hσker : σ.ker ≤ J.specialToProjective.ker := by
    intro a ha
    have he : π a = 1 := hρ (ha.trans ρ.map_one.symm)
    rw [MonoidHom.mem_ker,←hπν,he,map_one,map_one]
  have hdcard : Nat.card W = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
    change Nat.card (Additive W) = _
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W))
  have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini V)
  have hdim : 6*n ≤ Module.finrank (ZMod 2) (Additive W) := by
    by_cases hn2 : 2 ≤ n
    · have hnt : ∃ a, σ a ≠ 1 := by
        obtain ⟨r,hr,hr1⟩ := (simpleRoot Q split j).bot_or_exists_ne_one.resolve_left
          (simpleRoot_ne_bot Q split j)
        let r' : rankOne Q split j := ⟨r,(show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left) hr⟩
        obtain ⟨a,ha⟩ := hπ r'
        refine ⟨a,fun he => hr1 ?_⟩
        have he' : ρ r' = 1 := by simpa only [σ,MonoidHom.comp_apply,ha] using he
        exact congrArg Subtype.val (hρ (he'.trans ρ.map_one.symm))
      exact Representation.SU3.BinaryDegree.finrank_ge J hn2 hE hconj σ hnt
    · have hn1 : n = 1 := by omega
      subst n
      by_cases hd : Module.finrank (ZMod 2) (Additive W) < 8
      · have hσ := small_unitary_faithful_of_scalar_kernel J (by simpa using hE)
          (by simpa using hconj) hJ σ hσker hd
        simpa only [mul_one] using small_special_unitary_faithful_degree J
          (by simpa using hE) (by simpa using hconj) hJ σ hσ
      · omega
  have hWlower : (2^n)^6 ≤ Nat.card W := by
    rw [hdcard,←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hZlower : 2^n ≤ Nat.card (frattini V) := by
    have hh := Nat.card_le_card_of_injective (inclusion hZΦ) (inclusion_injective hZΦ)
    rwa [hZcard,card_map_of_injective V.subtype_injective] at hh
  calc
    (2^n)^7 = (2^n)^6 * 2^n := by ring
    _ ≤ Nat.card W * Nat.card (frattini V) := Nat.mul_le_mul hWlower hZlower
    _ = Nat.card V := hprod.symm

/-- Two nontrivial linear Frattini actions bound the radical containing a
nonabelian opposite root, before any unitary field ratio is known. -/
theorem linear_remainder_card_lower_of_opposite_derived
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : rankOne Q split i ≃* SL(2,F))
    {a : ℕ} (ha : 1 < a) (hF : Nat.card F = 2^a)
    (hne : ⁅simpleRoot Q split j,simpleRoot Q split j⁆ ≠ ⊥) :
    Nat.card F ^ 4 ≤ Nat.card (simpleRemainder Q split i) := by
  let V := simpleRemainder Q split i
  let D := (⁅V,V⁆ : Subgroup (X ⧸ Q.D))
  have hp : IsPGroup 2 V := split.isTwo.to_le inf_le_left
  have hpD : IsPGroup 2 D := split.isTwo.to_le ((commutator_le_self V).trans inf_le_left)
  have hquot := linear_frattini_card_lower μ hp (remainderRankOneAction Q split i hVi)
    (remainder_action_moves_root Q split hm i j hij hVi) ha hF
  have hdquot := linear_frattini_card_lower μ hpD (remainderDerivedAction Q split i hVi)
    (remainderDerivedAction_nontrivial Q split hm i j hij hVi
      (UnitarySource.actorReflection Q split i) hne) ha hF
  have hd : Nat.card F ^ 2 ≤ Nat.card D := hdquot.trans
    (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (frattini D)))
  let : Fact (IsPGroup 2 V) := ⟨hp⟩
  have hDΦ : D ≤ (frattini V).map V.subtype := by
    rw [show D = ⁅V,V⁆ from rfl,←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  have hphi : Nat.card F ^ 2 ≤ Nat.card (frattini V) := by
    have hh := hd.trans (Nat.card_le_card_of_injective (inclusion hDΦ) (inclusion_injective hDΦ))
    rwa [card_map_of_injective V.subtype_injective] at hh
  calc
    Nat.card F ^ 4 = Nat.card F ^ 2 * Nat.card F ^ 2 := by ring
    _ ≤ Nat.card (V ⧸ frattini V) * Nat.card (frattini V) := Nat.mul_le_mul hquot hphi
    _ = Nat.card V := (Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini V)).symm

/-- The literal mixed linear-unitary factors force the exact quadratic
field relation, including unitary parameter two. -/
theorem mixed_unitary_field_order
    {F E : Type*} [Field F] [Finite F] [CharP F 2]
    [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split i ≃* SL(2,F))
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple j}) :
      Set (Q.tits.standardParabolic {Q.simple j})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple j}))
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (π : J.specialSubgroup →* rankOne Q split j) (hπ : Function.Surjective π)
    (hπν : ∀ a, ν (RootLocalCover.projection Q split j (π a)) = J.specialToProjective a)
    (hrj : Nat.card (simpleRoot Q split j) = (2^n)^3) :
    Nat.card F = (2^n)^2 := by
  let ξ := (localGroupEquivOfCenterless Q split i hVi μ
    Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot).trans
      Atlas.RankOneFieldAutomorphisms.slEquivPSL
  have hri := GTwoSource.simpleRoot_card Q split i hVi ξ
  have hci := remainder_card_four Q split hm i j hij
  have hcj := remainder_card_four Q split hm j i hij.symm
  rw [hri,hrj] at hci hcj
  let := Fintype.ofFinite F
  obtain ⟨a,_,ha⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2^(a : ℕ) := by simpa only [Nat.card_eq_fintype_card] using ha
  have hlow := unitary_remainder_card_lower_of_cover Q split J hn hE hconj hJ
    hm i j hij hVj (UnitarySource.actorReflection Q split j) hc ν π hπ hπν
  rw [hcj,hF,←pow_mul,←pow_mul,←pow_mul,←pow_add] at hlow
  have hdegreeLower := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hlow
  have ha' : 1 < (a : ℕ) := by omega
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hE hconj
  have hne := (simpleRoot_unitary_derived J hn hE hf hJ Q split j hVj ν).2.2
  have hupp := linear_remainder_card_lower_of_opposite_derived Q split hm i j hij hVi μ ha' hF hne
  rw [hci,hF,←pow_mul,←pow_mul,←pow_mul,←pow_add] at hupp
  have hdegreeUpper := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hupp
  have he : (a : ℕ) = n*2 := by omega
  rw [hF,he,pow_mul]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
