module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Setup
public import Theory.SpecificGroups.SL2.BinaryProjective
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The source contract for solvable Thompson factorization

This interface retains all of B.2.16, including the actual centralizer quotient,
the internal group and module decompositions, and the final rank assertions.
It asserts no existence theorem: the universal theorem is an explicit input to
the application on printed p.513. The exceptional factors are the actual
PSL₂(2), acting on their natural binary spaces through the canonical SL₂(2)
identification. The coordinate equations make both decompositions internal.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Theorem B.2.16,
printed p.79, and Definition B.2.11, printed p.77.
-/

@[expose] public section

open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative

namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.ThompsonSource

universe u
variable {H : Type u} [Group H]

/-- The source normal closure V = ⟨Ω₁(Z(S))ᴴ⟩. -/
def closure (S : Sylow 2 H) : Subgroup H :=
  normalClosure (omegaOneCenterAmbient (S : Subgroup H) : Set H)

instance closure_normal (S : Sylow 2 H) : (closure S).Normal :=
  inferInstanceAs (normalClosure _).Normal

/-- The literal quotient H* = H/C_H(V). -/
abbrev CentralQuotient (V : Subgroup H) [V.Normal] := H ⧸ centralizer (V : Set H)

/-- The quotient map defining the star notation. -/
def starMap (V : Subgroup H) [V.Normal] : H →* CentralQuotient V :=
  QuotientGroup.mk' (centralizer (V : Set H))

/-- R₂ consists of normal elementary abelian two-subgroups with two-reduced
centralizer quotient. Normality is supplied intrinsically, not in a larger group. -/
def IsR2 (V : Subgroup H) : Prop :=
  ∃ (_ : V.Normal), IsElementaryAbelian 2 V ∧ pCore 2 (CentralQuotient V) = ⊥

/-- The full second alternative of B.2.16, with no assumed positive factor count.
Nonemptiness of the family will follow from the noncentralization clause. -/
structure Exceptional (S : Sylow 2 H) [IsElementaryAbelian 2 (closure S)] where
  noncentral : ¬ elementaryAbelianMaxJ (S : Subgroup H) ≤
    centralizer (closure S : Set H)
  sylow : Chapter1.IsSylowIn 2
    ((elementaryAbelianMaxJ (S : Subgroup H)).map (starMap (closure S)))
    ((elementaryAbelianMaxJ (⊤ : Subgroup H)).map (starMap (closure S)))
  representation : Representation (ZMod 2) (CentralQuotient (closure S)) (Additive (closure S))
  conjugation : ∀ (h : H) (v : closure S),
    ((representation (starMap (closure S) h) (Additive.ofMul v)).toMul : H) =
      h * (v : H) * h⁻¹
  count : ℕ
  factor : Fin count → Subgroup (CentralQuotient (closure S))
  groupProduct : ((i : Fin count) → factor i) ≃*
    (elementaryAbelianMaxJ (⊤ : Subgroup H)).map (starMap (closure S))
  groupProduct_single : ∀ (i : Fin count) (g : factor i),
    (groupProduct (Pi.mulSingle i g) : CentralQuotient (closure S)) = g
  factorModel : ∀ i, factor i ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2)
  moduleSum :
    (Representation.BinaryOffender.fixedSpace representation
      ((elementaryAbelianMaxJ (⊤ : Subgroup H)).map (starMap (closure S))) ×
      ((i : Fin count) → subspaceCommutator representation ⊤ (factor i))) ≃ₗ[ZMod 2]
        Additive (closure S)
  moduleSum_fixed : ∀ v, moduleSum (v, 0) = v
  moduleSum_single : ∀ (i : Fin count)
      (v : subspaceCommutator representation ⊤ (factor i)),
    moduleSum (0, Pi.single i v) = v
  naturalEquiv : ∀ i, subspaceCommutator representation ⊤ (factor i) ≃ₗ[ZMod 2]
    (Fin 2 → ZMod 2)
  naturalEquiv_action : ∀ (i : Fin count) (g : factor i)
      (v : subspaceCommutator representation ⊤ (factor i)),
    representation (g : CentralQuotient (closure S)) (v : Additive (closure S)) =
      ((naturalEquiv i).symm
        (Representation.specialLinearNatural 2
          (Matrix.SpecialLinearGroup.sl2TwoEquivPSL2Two.symm (factorModel i g))
          (naturalEquiv i v)) : Additive (closure S))
  permutes : ∀ h : CentralQuotient (closure S), ∃ σ : Equiv.Perm (Fin count),
    (∀ i, (factor i).map (MulAut.conj h).toMonoidHom = factor (σ i)) ∧
    (∀ i, (subspaceCommutator representation ⊤ (factor i)).map (representation h) =
      subspaceCommutator representation ⊤ (factor (σ i)))

/-- Every clause of the conclusion of B.2.16. -/
structure Conclusion (S : Sylow 2 H) [Finite H] : Prop where
  elementary : IsElementaryAbelian 2 (closure S)
  reduced : pCore 2 (CentralQuotient (closure S)) = ⊥
  alternatives : letI := elementary
    (elementaryAbelianMaxJ (S : Subgroup H) ≤ centralizer (closure S : Set H) ∧
      (Set.univ : Set H) =
        (normalizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H) : Set H) *
        (centralizer (omegaOneCenterAmbient (S : Subgroup H) : Set H) : Set H)) ∨
    Nonempty (Exceptional S)
  rank : ChapterB.twoRank ((S : Subgroup H) ⊓ centralizer (closure S : Set H)) =
    ChapterB.twoRank (S : Subgroup H)
  thompson_le : elementaryAbelianMaxJ
      ((S : Subgroup H) ⊓ centralizer (closure S : Set H)) ≤
    elementaryAbelianMaxJ (S : Subgroup H)

/-- The exact universal source theorem, used as a parameter and never as an axiom. -/
def TheoremB216 : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], Group.IsSolvable H →
    Theory.GroupTheory.generalizedFitting H = pCore 2 H →
    ∀ S : Sylow 2 H, Conclusion S

/-- The normal closure belongs to the source family R₂(H). -/
theorem Conclusion.isR2 [Finite H] {S : Sylow 2 H} (h : Conclusion S) :
    IsR2 (closure S) := ⟨inferInstance, h.elementary, h.reduced⟩

private theorem l2_two_card :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  calc
    _ = Nat.card (Equiv.Perm (Fin 3)) := Nat.card_congr
      (Matrix.SpecialLinearGroup.sl2TwoEquivPSL2Two.symm.trans e).toEquiv
    _ = 6 := by rw [Nat.card_perm, Nat.card_fin]; decide

/-- Noncentralization rules out an empty family of factors. -/
theorem Exceptional.nonempty_factors {S : Sylow 2 H}
    [IsElementaryAbelian 2 (closure S)] (d : Exceptional S) :
    Nonempty (Fin d.count) := by
  by_contra hn
  let : IsEmpty (Fin d.count) := not_nonempty_iff.mp hn
  have : Subsingleton ((i : Fin d.count) → d.factor i) := inferInstance
  have : Subsingleton ((elementaryAbelianMaxJ (⊤ : Subgroup H)).map
      (starMap (closure S))) := d.groupProduct.symm.injective.subsingleton
  have hL := Subgroup.eq_bot_of_subsingleton
    ((elementaryAbelianMaxJ (⊤ : Subgroup H)).map (starMap (closure S)))
  obtain ⟨P, hP⟩ := d.sylow
  have hJ : (elementaryAbelianMaxJ (S : Subgroup H)).map (starMap (closure S)) = ⊥ := by
    apply bot_unique
    rw [← hP]
    exact hL ▸ map_subtype_le _
  apply d.noncentral
  have hk := (Subgroup.map_eq_bot_iff _).mp hJ
  simpa only [starMap, QuotientGroup.ker_mk'] using hk

/-- The failure alternative contains a nontrivial actual L₂(2) section. -/
theorem Exceptional.has_l2_section {S : Sylow 2 H}
    [IsElementaryAbelian 2 (closure S)] (d : Exceptional S) :
    ∃ D : Subgroup (CentralQuotient (closure S)), D ≠ ⊥ ∧
      Nonempty (D ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2)) := by
  obtain ⟨i⟩ := d.nonempty_factors
  let e := d.factorModel i
  refine ⟨d.factor i, ?_, ⟨e⟩⟩
  have hc : Nat.card (d.factor i) = 6 := (Nat.card_congr e.toEquiv).trans l2_two_card
  intro he
  rw [he, card_bot] at hc
  omega

/-- Divisibility passes from the L₂(2) factor through the centralizer quotient. -/
theorem Exceptional.three_dvd_card [Finite H] {S : Sylow 2 H}
    [IsElementaryAbelian 2 (closure S)] (d : Exceptional S) : 3 ∣ Nat.card H := by
  obtain ⟨D, _, ⟨e⟩⟩ := d.has_l2_section
  have hc : Nat.card D = 6 := (Nat.card_congr e.toEquiv).trans l2_two_card
  have hd : 3 ∣ Nat.card D := by rw [hc]; decide
  exact (hd.trans D.card_subgroup_dvd_card).trans
    (card_quotient_dvd_card (centralizer (closure S : Set H)))

/-- The complete source alternatives imply factorization when three is
coprime to the group order. The source theorem remains an explicit parameter. -/
theorem factorization_of_three_coprime [Finite H] (hB : TheoremB216.{u})
    (hsol : Group.IsSolvable H)
    (hF : Theory.GroupTheory.generalizedFitting H = pCore 2 H)
    (hthree : Nat.Coprime 3 (Nat.card H)) (S : Sylow 2 H) :
    (Set.univ : Set H) =
      (normalizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H) : Set H) *
      (centralizer (omegaOneCenterAmbient (S : Subgroup H) : Set H) : Set H) := by
  have h := hB H hsol hF S
  let := h.elementary
  have halt := h.alternatives
  cases halt with
  | inl hf => exact hf.2
  | inr he =>
    obtain ⟨d⟩ := he
    exact ((Nat.prime_three.coprime_iff_not_dvd.mp hthree) d.three_dvd_card).elim

end CFSG.Quasithin.Chapter1.RadicalNormalizers.ThompsonSource
