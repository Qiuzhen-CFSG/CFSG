module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.OuterSchurDegree.Model
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.OuterSchurDegree.Actors
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.OuterReduction

/-!
# Half-turn invariance of the actual symplectic tensor support

Self-centralization of the generalized Fitting subgroup makes an outer actor
noninner on the actual component. The cyclic outer quotient gives its exact
inner twist of the half-order graph power, including the cocycle equation.
Schur-linearity preserves the absolute character under this automorphism;
inner conjugation drops out of the character, and catalogue uniqueness forces
invariance of the tensor support under addition of the field degree modulo
twice that degree. No group cocycle descent or support selection is assumed.

Source: Guralnick--Malle, Classification of 2F-modules II, Section 3.5 and
Proposition 6.2(2--3); Aschbacher--Smith K.3.4, printed pp.451,456--457.
-/

@[expose] public section

open Representation Representation.FrobeniusTensor Fin.NatCast
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary

namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

/-- The support shift induced by the half-order exceptional graph power. -/
def halfTurnSupport {r : ℕ} [NeZero (2*r)] (S : Finset (Fin (2*r))) :
    Finset (Fin (2*r)) := S.image (fun j => j + (r : Fin (2*r)))

/-- The literal graph-twisted action shifts the tensor character's support. -/
theorem tensorModel_character_halfTurn {E : Type*} [Field E] {r : ℕ}
    [NeZero (2*r)] (hF : Nat.card F = 2^r)
    (e : F →+* E) (S : Finset (Fin (2*r))) (g : Derived F) :
    (tensorModel e (halfTurnSupport S)).character g =
      (tensorModel e S).character ((graphDerived F ^ r) g) := by
  classical
  rw [tensorModel_character, tensorModel_character, halfTurnSupport,
    Finset.prod_image (by intros a _ b _ h; exact add_right_cancel h)]
  apply Finset.prod_congr rfl
  intro j _
  have hp : graphDerived F ^ ((j + (r : Fin (2*r)) : Fin (2*r)) : ℕ) =
      graphDerived F ^ (j : ℕ) * graphDerived F ^ r := by
    rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod,
      ← pow_eq_pow_mod _ (graphDerived_pow_field hF), pow_add]
  rw [hp]
  rfl

/-- The proved tensor catalogue detects half-turn invariance of the character. -/
theorem halfTurnSupport_eq_of_character_fixed {E : Type*} [Field E] [IsAlgClosed E]
    {r : ℕ} [NeZero (2*r)] (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : F →+* E) (S : Finset (Fin (2*r)))
    (hfix : ∀ g, (tensorModel e S).character ((graphDerived F ^ r) g) =
      (tensorModel e S).character g) : halfTurnSupport S = S := by
  let cat := absoluteTensorCatalogue e hF (by omega)
  let : IsIrreducible (tensorModel e S) := cat.irreducible S
  let : IsIrreducible (tensorModel e (halfTurnSupport S)) := cat.irreducible _
  apply cat.distinguish
  apply (character_eq_iff_equiv_of_irreducible _ _).mp
  funext g
  rw [tensorModel_character_halfTurn hF, hfix]

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

omit [FiniteDimensional (ZMod 2) V] in
/-- Actual outerness gives a graph twist on the marked derived group, with its cocycle. -/
theorem source_outer_twist {K : GroupClass} (h : SourceHypothesis K ρ L) [L.Normal]
    {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (d : L ≃* Derived F) (t : G) (htL : t ∉ L) (ht2 : t^2 = 1) :
    ∃ x : Derived F,
      (∀ u : L, d (MulAut.conjNormal t u) =
        x * (graphDerived F ^ r) (d u) * x⁻¹) ∧
      x * (graphDerived F ^ r) x = 1 := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2^1) ▸ Nat.pow_lt_pow_right (by decide) hr
  let q := derivedEquivFull_of_card_gt_two hq
  let d' := d.trans q
  have hout : componentAction d' t ∉ MulAut.innerSubgroup (Sp F) := by
    rwa [componentAction_mem_inner_iff h d' t]
  have htord : orderOf (componentAction d' t) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ht2, map_one]
    · intro he
      exact hout (he ▸ (MulAut.innerSubgroup (Sp F)).one_mem)
  obtain ⟨x, hx, hc⟩ : ∃ x : Sp F,
      componentAction d' t = MulAut.conj x * ExceptionalGraph.graphAut ^ r ∧
        x * (ExceptionalGraph.graphAut ^ r) x = 1 := by
    rcases InvolutionNormalForms.involution_inner_or_twist hF hr
      SemilinearClassification.inner_field_of_preservesDiagram (componentAction d' t) htord
      with hi | ho
    · obtain ⟨g, _, hg⟩ := hi
      exact (hout ⟨g, hg.symm⟩).elim
    · exact ho
  have hval (m : ℕ) (z : Derived F) :
      ((graphDerived F ^ m) z).val = (ExceptionalGraph.graphAut ^ m) z.val := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', pow_succ']
      exact congrArg ExceptionalGraph.graphAut ih
  have hqg (z : Derived F) : q ((graphDerived F ^ r) z) =
      (ExceptionalGraph.graphAut ^ r) (q z) := by
    simpa only [q, derivedEquivFull_of_card_gt_two_apply] using hval r z
  refine ⟨q.symm x, ?_, ?_⟩
  · intro u
    apply q.injective
    have hh := DFunLike.congr_fun hx (d' u)
    have he : q (d (MulAut.conjNormal t u)) =
        x * (ExceptionalGraph.graphAut ^ r) (q (d u)) * x⁻¹ := by
      simpa [componentAction, MulAut.congr_apply, d'] using hh
    simpa only [map_mul, map_inv, q.apply_symm_apply, hqg] using he
  · apply q.injective
    simpa only [map_mul, map_one, hqg, q.apply_symm_apply] using hc

variable [IsIrreducible (ρ.comp L.subtype)] [L.Normal]

omit [Finite G] in
/-- The actual Schur-linear involution preserves the original absolute character. -/
theorem absolute_character_conjNormal (t : G) (ht : IsSchurLinear ρ L t)
    (ht2 : t^2 = 1) (u : L) :
    (absoluteRep (ρ.comp L.subtype)).character (MulAut.conjNormal t u) =
      (absoluteRep (ρ.comp L.subtype)).character u := by
  let T := absoluteActor ρ L t ht
  have hi := absoluteActor_intertwines ρ L t ht u
  have hsq : T * T = 1 := by
    simpa only [pow_two] using absoluteActor_square ρ L t ht ht2
  have he : T * absoluteRep (ρ.comp L.subtype) u * T =
      absoluteRep (ρ.comp L.subtype) (MulAut.conjNormal t u) := by
    rw [hi, mul_assoc, hsq, mul_one]
  change LinearMap.trace _ _ _ = LinearMap.trace _ _ _
  rw [← he, LinearMap.trace_mul_cycle, hsq, one_mul]

/-- An outer Schur-linear involution forces half-turn invariance of the actual support. -/
theorem source_halfTurnSupport {K : GroupClass} (h : SourceHypothesis K ρ L)
    {r : ℕ} [NeZero (2*r)] (hr : 1 < r) (hF : Nat.card F = 2^r)
    (d : L ≃* Derived F) (P : TensorParameters (ρ.comp L.subtype) d r)
    (t : G) (htL : t ∉ L) (ht2 : t^2 = 1) (ht : IsSchurLinear ρ L t) :
    halfTurnSupport P.support = P.support := by
  obtain ⟨x, hx, _⟩ := source_outer_twist h hr hF d t htL ht2
  obtain ⟨φ⟩ := P.equivalence
  have hχ (g : Derived F) :
      (absoluteRep (ρ.comp L.subtype)).character (d.symm g) =
        (tensorModel P.embedding P.support).character g := congrFun (char_iso φ) g
  apply halfTurnSupport_eq_of_character_fixed hr hF P.embedding P.support
  intro g
  have he := hx (d.symm g)
  rw [d.apply_symm_apply] at he
  have he' : d.symm (x * (graphDerived F ^ r) g * x⁻¹) =
      MulAut.conjNormal t (d.symm g) := by
    rw [← he, d.symm_apply_apply]
  calc
    (tensorModel P.embedding P.support).character ((graphDerived F ^ r) g) =
        (tensorModel P.embedding P.support).character
          (x * (graphDerived F ^ r) g * x⁻¹) := (char_conj _ _ _).symm
    _ = (absoluteRep (ρ.comp L.subtype)).character (MulAut.conjNormal t (d.symm g)) := by
      rw [← hχ, he']
    _ = (absoluteRep (ρ.comp L.subtype)).character (d.symm g) :=
      absolute_character_conjNormal t ht ht2 _
    _ = (tensorModel P.embedding P.support).character g := hχ g

end CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur
