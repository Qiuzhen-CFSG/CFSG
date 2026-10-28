module

public import CFSG.Quasithin.ClassificationModels.RankTwo

/-!
# Complete classification outputs and the terminal branch lists

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Theorem 0.1.2 (p.4), repeated as Theorem 0.1.1 (p.482),
Theorem 2.1.1 (p.518), Theorem D/14.8.2 (pp.1078–1079), and
Theorem E/15.4.25 and the Main Theorem assembly (pp.1165–1166).

`IsQTKEModel` is the complete Main Theorem output, including the genuine Ree
family ²F₄(2^(2m+1)), m ≥ 1. `IsTheorem211Model`, `IsTheoremDModel`, and
`IsTheoremEModel` are the complete terminal output lists.
`IsTheoremDExceptionalModel` is exactly D(2)–(3). The earlier predicates
`IsQTKEModelWithoutReeF4` and `IsTheoremDModelWithoutReeF4` remain explicitly
partial APIs; the decomposition theorems describe their precise difference
from the complete lists. `IsEvenTypeModel` adds exactly J₁ to the Main list.

Every inclusion below follows by embedding the actual model witness in the
corresponding Main Theorem branch. These are catalogue inclusions, not proofs
of the classification theorems. No QTKE hypothesis or desired conclusion is
hidden in a carrier. The parameter bound p > 7 belongs to 2.1.1, whereas the
Main Theorem permits every Fermat/Mersenne prime p ≥ 5. D(1) requires n > 1.
Exceptional overlaps are retained, including A₈ and L₄(2), and both the actual
small derived groups and the separately listed odd-characteristic models.

This module does not import `Models`, so that its owner can re-export the final
definitions there without a cycle. Compatibility with its existing partial API
is in `ClassificationModels.ConstructedInclusion`.
-/

@[expose] public section

universe u v

namespace CFSG.Quasithin.ClassificationModels

/-- The retained partial Main Theorem output, omitting the general Ree family. -/
inductive IsQTKEModelWithoutReeF4 (G : Type u) [Group G] : Prop
  | bender (model : IsBenderModel G)
  | rank_two (f : ℕ) (model : IsRankTwoModelWithoutReeF4 G f)
  | linear_binary (n : ℕ) (hn : n = 4 ∨ n = 5) (iso : ClassicalGroup.IsPSL G n 2)
  | symplectic_binary (iso : ClassicalGroup.IsPSp G 3 2)
  | alternating (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 9)
      (iso : Nonempty (G ≃* alternatingGroup (Fin n)))
  | linear_prime (p : ℕ) (hp : IsFermatOrMersennePrime p) (large : 5 ≤ p)
      (iso : ClassicalGroup.IsPSL G 2 p)
  | linear_three (n : ℕ) (hn : n = 3 ∨ n = 4) (iso : ClassicalGroup.IsPSL G n 3)
  | unitary_three (n : ℕ) (hn : n = 3 ∨ n = 4) (iso : ClassicalGroup.IsPSU G n 3)
  | g2_three (iso : IsG2At G 3)
  | sporadic (model : IsSporadicModel G)

/-- Exactly the output of Theorem 2.1.1, including its strict prime bound. -/
inductive IsTheorem211Model (G : Type u) [Group G] : Prop
  | bender (model : IsBenderModel G)
  | linear_prime (p : ℕ) (hp : IsFermatOrMersennePrime p) (large : 7 < p)
      (iso : ClassicalGroup.IsPSL G 2 p)
  | linear_three (iso : ClassicalGroup.IsPSL G 3 3)
  | mathieu_eleven (iso : Nonempty (G ≃* Sporadic.Mathieu.M11))

/-- The individual nongeneric alternatives D(2) and D(3). -/
inductive IsTheoremDExceptionalModel (G : Type u) [Group G] : Prop
  | linear_binary (n : ℕ) (hn : n = 4 ∨ n = 5) (iso : ClassicalGroup.IsPSL G n 2)
  | alternating_nine (iso : Nonempty (G ≃* alternatingGroup (Fin 9)))
  | sporadic (name : SporadicName)
      (hn : name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .he ∨
        name = .j4 ∨ name = .hs ∨ name = .ru)
      (iso : Nonempty (G ≃* name.Carrier))
  | symplectic_binary (iso : ClassicalGroup.IsPSp G 3 2)
  | unitary_binary (iso : ClassicalGroup.IsPSU G 4 2)
  | linear_three (iso : ClassicalGroup.IsPSL G 4 3)
  | unitary_three (iso : ClassicalGroup.IsPSU G 4 3)
  | g2_three (iso : IsG2At G 3)

/-- D(1)–(3) with only the general Ree part of D(1) missing. -/
inductive IsTheoremDModelWithoutReeF4 (G : Type u) [Group G] : Prop
  | rank_two (f : ℕ) (hf : 1 < f) (model : IsRankTwoModelWithoutReeF4 G f)
  | exceptional (model : IsTheoremDExceptionalModel G)

/-- Exactly the eight alternatives of Theorem E. G₂(2)′ is its actual derived
carrier, and ³D₄(2) uses the genuine graph-field construction. -/
inductive IsTheoremEModel (G : Type u) [Group G] : Prop
  | janko_two (iso : Nonempty (G ≃* Sporadic.LeechRelated.J2.Carrier))
  | janko_three (iso : Nonempty (G ≃* Sporadic.Janko3.Model))
  | triality (iso : Triality.Standard.IsTrialityGroupAt 2 G)
  | tits (iso : Nonempty (G ≃* Tits.ParrottGroup))
  | g2_derived (iso : Nonempty (G ≃* commutator (Atlas.G2.Model (ZMod 2))))
  | mathieu_twelve (iso : Nonempty (G ≃* Sporadic.Mathieu.M12))
  | linear_binary (iso : ClassicalGroup.IsPSL G 3 2)
  | alternating_six (iso : Nonempty (G ≃* alternatingGroup (Fin 6)))

variable {G : Type u} {H : Type v} [Group G] [Group H]

theorem IsTheorem211Model.toQTKEModelWithoutReeF4 (h : IsTheorem211Model G) :
    IsQTKEModelWithoutReeF4 G := by
  cases h with
  | bender h => exact .bender h
  | linear_prime p hp hlarge iso => exact .linear_prime p hp (by omega) iso
  | linear_three iso => exact .linear_three 3 (Or.inl rfl) iso
  | mathieu_eleven iso => exact .sporadic ⟨.m11, iso⟩

theorem IsTheoremDExceptionalModel.toQTKEModelWithoutReeF4
    (h : IsTheoremDExceptionalModel G) : IsQTKEModelWithoutReeF4 G := by
  cases h with
  | linear_binary n hn iso => exact .linear_binary n hn iso
  | alternating_nine iso => exact .alternating 9 (Or.inr (Or.inr (Or.inr rfl))) iso
  | sporadic name _ iso => exact .sporadic ⟨name, iso⟩
  | symplectic_binary iso => exact .symplectic_binary iso
  | unitary_binary iso => exact .rank_two 1 (.unitary_four (by decide) iso)
  | linear_three iso => exact .linear_three 4 (Or.inr rfl) iso
  | unitary_three iso => exact .unitary_three 4 (Or.inr rfl) iso
  | g2_three iso => exact .g2_three iso

theorem IsTheoremDModelWithoutReeF4.toQTKEModelWithoutReeF4
    (h : IsTheoremDModelWithoutReeF4 G) : IsQTKEModelWithoutReeF4 G := by
  cases h with
  | rank_two f _ h => exact .rank_two f h
  | exceptional h => exact h.toQTKEModelWithoutReeF4

theorem IsTheoremEModel.toQTKEModelWithoutReeF4 (h : IsTheoremEModel G) :
    IsQTKEModelWithoutReeF4 G := by
  cases h with
  | janko_two iso => exact .sporadic ⟨.j2, iso⟩
  | janko_three iso => exact .sporadic ⟨.j3, iso⟩
  | triality iso => exact .rank_two 1 (.triality (by decide) iso)
  | tits iso => exact .rank_two 1 (.tits rfl iso)
  | g2_derived iso => exact .rank_two 1 (.g2_derived rfl iso)
  | mathieu_twelve iso => exact .sporadic ⟨.m12, iso⟩
  | linear_binary iso => exact .rank_two 1 (.linear (by decide) iso)
  | alternating_six iso => exact .alternating 6 (Or.inr (Or.inl rfl)) iso

theorem IsQTKEModelWithoutReeF4.of_mulEquiv
    (h : IsQTKEModelWithoutReeF4 G) (e : H ≃* G) : IsQTKEModelWithoutReeF4 H := by
  cases h with
  | bender h => exact .bender (h.of_mulEquiv e)
  | rank_two f h => exact .rank_two f (h.of_mulEquiv e)
  | linear_binary n hn iso => exact .linear_binary n hn (iso.of_mulEquiv e)
  | symplectic_binary iso => exact .symplectic_binary (iso.of_mulEquiv e)
  | alternating n hn iso => exact .alternating n hn (iso.map fun a => e.trans a)
  | linear_prime p hp hlarge iso => exact .linear_prime p hp hlarge (iso.of_mulEquiv e)
  | linear_three n hn iso => exact .linear_three n hn (iso.of_mulEquiv e)
  | unitary_three n hn iso => exact .unitary_three n hn (iso.of_mulEquiv e)
  | g2_three iso => exact .g2_three (iso.of_mulEquiv e)
  | sporadic h => exact .sporadic (h.of_mulEquiv e)

theorem IsTheorem211Model.of_mulEquiv (h : IsTheorem211Model G) (e : H ≃* G) :
    IsTheorem211Model H := by
  cases h with
  | bender h => exact .bender (h.of_mulEquiv e)
  | linear_prime p hp hlarge iso => exact .linear_prime p hp hlarge (iso.of_mulEquiv e)
  | linear_three iso => exact .linear_three (iso.of_mulEquiv e)
  | mathieu_eleven iso => exact .mathieu_eleven (iso.map fun a => e.trans a)

theorem IsTheoremDExceptionalModel.of_mulEquiv
    (h : IsTheoremDExceptionalModel G) (e : H ≃* G) : IsTheoremDExceptionalModel H := by
  cases h with
  | linear_binary n hn iso => exact .linear_binary n hn (iso.of_mulEquiv e)
  | alternating_nine iso => exact .alternating_nine (iso.map fun a => e.trans a)
  | sporadic name hn iso => exact .sporadic name hn (iso.map fun a => e.trans a)
  | symplectic_binary iso => exact .symplectic_binary (iso.of_mulEquiv e)
  | unitary_binary iso => exact .unitary_binary (iso.of_mulEquiv e)
  | linear_three iso => exact .linear_three (iso.of_mulEquiv e)
  | unitary_three iso => exact .unitary_three (iso.of_mulEquiv e)
  | g2_three iso => exact .g2_three (iso.of_mulEquiv e)

theorem IsTheoremDModelWithoutReeF4.of_mulEquiv
    (h : IsTheoremDModelWithoutReeF4 G) (e : H ≃* G) : IsTheoremDModelWithoutReeF4 H := by
  cases h with
  | rank_two f hf h => exact .rank_two f hf (h.of_mulEquiv e)
  | exceptional h => exact .exceptional (h.of_mulEquiv e)

theorem IsTheoremEModel.of_mulEquiv (h : IsTheoremEModel G) (e : H ≃* G) :
    IsTheoremEModel H := by
  cases h with
  | janko_two iso => exact .janko_two (iso.map fun a => e.trans a)
  | janko_three iso => exact .janko_three (iso.map fun a => e.trans a)
  | triality iso => exact .triality (iso.of_mulEquiv e)
  | tits iso => exact .tits (iso.map fun a => e.trans a)
  | g2_derived iso => exact .g2_derived (iso.map fun a => e.trans a)
  | mathieu_twelve iso => exact .mathieu_twelve (iso.map fun a => e.trans a)
  | linear_binary iso => exact .linear_binary (iso.of_mulEquiv e)
  | alternating_six iso => exact .alternating_six (iso.map fun a => e.trans a)

theorem isQTKEModelWithoutReeF4_mulEquiv_iff (e : G ≃* H) :
    IsQTKEModelWithoutReeF4 G ↔ IsQTKEModelWithoutReeF4 H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem isTheorem211Model_mulEquiv_iff (e : G ≃* H) :
    IsTheorem211Model G ↔ IsTheorem211Model H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem isTheoremDExceptionalModel_mulEquiv_iff (e : G ≃* H) :
    IsTheoremDExceptionalModel G ↔ IsTheoremDExceptionalModel H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem isTheoremDModelWithoutReeF4_mulEquiv_iff (e : G ≃* H) :
    IsTheoremDModelWithoutReeF4 G ↔ IsTheoremDModelWithoutReeF4 H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem isTheoremEModel_mulEquiv_iff (e : G ≃* H) : IsTheoremEModel G ↔ IsTheoremEModel H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

/-- The complete actual-isomorphism output of Theorem 0.1.2 (printed p.4),
repeated as Theorem 0.1.1 (p.482). No model-property certificate is an input. -/
inductive IsQTKEModel (G : Type u) [Group G] : Prop
  | bender (model : IsBenderModel G)
  | rank_two (f : ℕ) (model : IsRankTwoModel G f)
  | linear_binary (n : ℕ) (hn : n = 4 ∨ n = 5) (iso : ClassicalGroup.IsPSL G n 2)
  | symplectic_binary (iso : ClassicalGroup.IsPSp G 3 2)
  | alternating (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 9)
      (iso : Nonempty (G ≃* alternatingGroup (Fin n)))
  | linear_prime (p : ℕ) (hp : IsFermatOrMersennePrime p) (large : 5 ≤ p)
      (iso : ClassicalGroup.IsPSL G 2 p)
  | linear_three (n : ℕ) (hn : n = 3 ∨ n = 4) (iso : ClassicalGroup.IsPSL G n 3)
  | unitary_three (n : ℕ) (hn : n = 3 ∨ n = 4) (iso : ClassicalGroup.IsPSU G n 3)
  | g2_three (iso : IsG2At G 3)
  | sporadic (model : IsSporadicModel G)

/-- Exactly D(1)–(3), with the strict field-exponent bound in D(1). -/
inductive IsTheoremDModel (G : Type u) [Group G] : Prop
  | rank_two (f : ℕ) (hf : 1 < f) (model : IsRankTwoModel G f)
  | exceptional (model : IsTheoremDExceptionalModel G)

/-- The even-type output (p.483): the complete Main Theorem list together
with the additional actual J₁ carrier. -/
def IsEvenTypeModel (G : Type u) [Group G] : Prop :=
  IsQTKEModel G ∨ IsEvenTypeAdditionalModel G

theorem IsQTKEModelWithoutReeF4.toQTKEModel (h : IsQTKEModelWithoutReeF4 G) :
    IsQTKEModel G := by
  cases h with
  | bender h => exact .bender h
  | rank_two f h => exact .rank_two f h.toRankTwoModel
  | linear_binary n hn iso => exact .linear_binary n hn iso
  | symplectic_binary iso => exact .symplectic_binary iso
  | alternating n hn iso => exact .alternating n hn iso
  | linear_prime p hp hlarge iso => exact .linear_prime p hp hlarge iso
  | linear_three n hn iso => exact .linear_three n hn iso
  | unitary_three n hn iso => exact .unitary_three n hn iso
  | g2_three iso => exact .g2_three iso
  | sporadic h => exact .sporadic h

theorem IsTheoremDModelWithoutReeF4.toTheoremDModel
    (h : IsTheoremDModelWithoutReeF4 G) : IsTheoremDModel G := by
  cases h with
  | rank_two f hf h => exact .rank_two f hf h.toRankTwoModel
  | exceptional h => exact .exceptional h

theorem IsTheorem211Model.toQTKEModel (h : IsTheorem211Model G) : IsQTKEModel G :=
  h.toQTKEModelWithoutReeF4.toQTKEModel

theorem IsTheoremDExceptionalModel.toQTKEModel (h : IsTheoremDExceptionalModel G) :
    IsQTKEModel G := h.toQTKEModelWithoutReeF4.toQTKEModel

theorem IsTheoremDModel.toQTKEModel (h : IsTheoremDModel G) : IsQTKEModel G := by
  cases h with
  | rank_two f _ h => exact .rank_two f h
  | exceptional h => exact h.toQTKEModel

theorem IsTheoremEModel.toQTKEModel (h : IsTheoremEModel G) : IsQTKEModel G :=
  h.toQTKEModelWithoutReeF4.toQTKEModel

/-- Every member of the general Ree family appears in D(1); its exponent
is at least three, so it satisfies D's strict bound. -/
theorem isTheoremDModel_of_reeF4 (h : ReeF4.IsReeF4Model G) : IsTheoremDModel G := by
  obtain ⟨m, hm, iso⟩ := h
  exact .rank_two (2 * m + 1) (by omega) (.ree_f4 m hm rfl iso)

theorem isQTKEModel_of_reeF4 (h : ReeF4.IsReeF4Model G) : IsQTKEModel G :=
  (isTheoremDModel_of_reeF4 h).toQTKEModel

/-- The complete Main list adds precisely the general Ree carriers to the
earlier list. No disjointness of isomorphism classes is asserted. -/
theorem isQTKEModel_iff_withoutReeF4_or_reeF4 :
    IsQTKEModel G ↔ IsQTKEModelWithoutReeF4 G ∨ ReeF4.IsReeF4Model G := by
  constructor
  · intro h
    cases h with
    | bender h => exact .inl (.bender h)
    | rank_two f h =>
        rcases isRankTwoModel_iff_withoutReeF4_or_reeF4.mp h with h | ⟨m, hm, _, iso⟩
        · exact .inl (.rank_two f h)
        · exact .inr ⟨m, hm, iso⟩
    | linear_binary n hn iso => exact .inl (.linear_binary n hn iso)
    | symplectic_binary iso => exact .inl (.symplectic_binary iso)
    | alternating n hn iso => exact .inl (.alternating n hn iso)
    | linear_prime p hp hlarge iso => exact .inl (.linear_prime p hp hlarge iso)
    | linear_three n hn iso => exact .inl (.linear_three n hn iso)
    | unitary_three n hn iso => exact .inl (.unitary_three n hn iso)
    | g2_three iso => exact .inl (.g2_three iso)
    | sporadic h => exact .inl (.sporadic h)
  · rintro (h | h)
    · exact h.toQTKEModel
    · exact isQTKEModel_of_reeF4 h

theorem isTheoremDModel_iff_withoutReeF4_or_reeF4 :
    IsTheoremDModel G ↔ IsTheoremDModelWithoutReeF4 G ∨ ReeF4.IsReeF4Model G := by
  constructor
  · intro h
    cases h with
    | rank_two f hf h =>
        rcases isRankTwoModel_iff_withoutReeF4_or_reeF4.mp h with h | ⟨m, hm, _, iso⟩
        · exact .inl (.rank_two f hf h)
        · exact .inr ⟨m, hm, iso⟩
    | exceptional h => exact .inl (.exceptional h)
  · rintro (h | h)
    · exact h.toTheoremDModel
    · exact isTheoremDModel_of_reeF4 h

theorem IsQTKEModel.of_mulEquiv (h : IsQTKEModel G) (e : H ≃* G) :
    IsQTKEModel H := by
  cases h with
  | bender h => exact .bender (h.of_mulEquiv e)
  | rank_two f h => exact .rank_two f (h.of_mulEquiv e)
  | linear_binary n hn iso => exact .linear_binary n hn (iso.of_mulEquiv e)
  | symplectic_binary iso => exact .symplectic_binary (iso.of_mulEquiv e)
  | alternating n hn iso => exact .alternating n hn (iso.map fun a => e.trans a)
  | linear_prime p hp hlarge iso => exact .linear_prime p hp hlarge (iso.of_mulEquiv e)
  | linear_three n hn iso => exact .linear_three n hn (iso.of_mulEquiv e)
  | unitary_three n hn iso => exact .unitary_three n hn (iso.of_mulEquiv e)
  | g2_three iso => exact .g2_three (iso.of_mulEquiv e)
  | sporadic h => exact .sporadic (h.of_mulEquiv e)

theorem IsTheoremDModel.of_mulEquiv (h : IsTheoremDModel G) (e : H ≃* G) :
    IsTheoremDModel H := by
  cases h with
  | rank_two f hf h => exact .rank_two f hf (h.of_mulEquiv e)
  | exceptional h => exact .exceptional (h.of_mulEquiv e)

theorem isQTKEModel_mulEquiv_iff (e : G ≃* H) : IsQTKEModel G ↔ IsQTKEModel H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem isTheoremDModel_mulEquiv_iff (e : G ≃* H) :
    IsTheoremDModel G ↔ IsTheoremDModel H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem IsQTKEModel.toEvenTypeModel (h : IsQTKEModel G) : IsEvenTypeModel G := Or.inl h

theorem IsEvenTypeAdditionalModel.toEvenTypeModel (h : IsEvenTypeAdditionalModel G) :
    IsEvenTypeModel G := Or.inr h

theorem IsEvenTypeModel.of_mulEquiv (h : IsEvenTypeModel G) (e : H ≃* G) :
    IsEvenTypeModel H := h.imp (fun h => h.of_mulEquiv e) (fun h => h.of_mulEquiv e)

theorem isEvenTypeModel_mulEquiv_iff (e : G ≃* H) :
    IsEvenTypeModel G ↔ IsEvenTypeModel H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

end CFSG.Quasithin.ClassificationModels
