module

public import CFSG.Quasithin.ChapterG.Section09.Basic
public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.NilpotentCover
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.Contracts

/-!
# The genuine covering-group input to G.9.4

B.5.2 supplies a new finite SQTK cover whose Fitting preimage is nilpotent.
Applying its normal-Sylow theorem to the literal three-core preimage produces
a normal three-subgroup mapping onto the three-core. Thus the rank restriction
is retained on the cover, where SQTK actually gives it; no quotient-rank
monotonicity is asserted.

The remaining three-core reductions below are specified as an output contract
for the separate reduction proof. Source: Aschbacher--Smith, B.5.2, printed
p.103, and the beginning of the proof of G.9.4, printed pp.354--355.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition

universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {A : Subgroup G} {m : ℕ}

/-- The earlier B.5.2 presentation; it contains no recognition conclusion. -/
structure NilpotentFittingCover (K : GroupClass.{u}) (G : Type u)
    [Group G] extends SQTKCover K G where
  nilpotent_preimage : Group.IsNilpotent ((fittingSubgroup G).comap projection)

/-- B.5.2 discharges the nilpotent-cover premise for the actual G.9.4 input. -/
theorem exists_nilpotentFittingCover (h : FittingHypothesis K ρ A m) :
    Nonempty (NilpotentFittingCover K G) := by
  obtain ⟨c⟩ := h.quotient
  obtain ⟨D, hD, hfin, f, hsqtk, hsurj, hnil, _⟩ :=
    ChapterB.NilpotentCover.exists_sqtk_cover c.sqtk c.projection c.surjective
  exact ⟨{
    Cover := D
    coverGroup := hD
    coverFinite := hfin
    sqtk := hsqtk
    projection := f
    surjective := hsurj
    nilpotent_preimage := hnil }⟩

/-- Each actual Sylow three-subgroup of the preimage is normal in the cover
and maps onto the three-core. This is the `B̂` used on printed p.355. -/
theorem NilpotentFittingCover.three_preimage (c : NilpotentFittingCover K G)
    (P : Sylow 3 ((pCore 3 G).comap c.projection)) :
    (P.map ((pCore 3 G).comap c.projection).subtype).Normal ∧
      (P.map ((pCore 3 G).comap c.projection).subtype).map c.projection = pCore 3 G := by
  let : Group.IsNilpotent ((fittingSubgroup G).comap c.projection) := c.nilpotent_preimage
  exact ChapterB.NilpotentCover.sylow_pCore_preimage c.projection c.surjective 3 P

/-- The actual normal three-group used in G.9.4 exists in an SQTK cover
and has three-rank at most two before quotienting. -/
theorem exists_rank_two_three_cover (h : FittingHypothesis K ρ A m) :
    ∃ (c : NilpotentFittingCover K G) (B : Subgroup c.Cover),
      B.Normal ∧ IsPGroup 3 B ∧ B.map c.projection = pCore 3 G ∧
        primeRank 3 B ≤ 2 := by
  obtain ⟨c⟩ := exists_nilpotentFittingCover h
  let P : Sylow 3 ((pCore 3 G).comap c.projection) := Classical.choice inferInstance
  let B := P.map ((pCore 3 G).comap c.projection).subtype
  obtain ⟨hn, he⟩ := c.three_preimage P
  exact ⟨c, B, hn, P.isPGroup'.map _, he,
    (primeRank_subgroup_le 3 B).trans
      (c.sqtk.stronglyQuasithin 3 Nat.prime_three (by decide))⟩

/-- The exact earlier G.9.2 theorem for restrictions of this module. Its
source hypotheses include the conditional sharper degree bound. -/
def NilpotentRigidityInput (ρ : Representation (ZMod 2) G V) : Prop :=
  ∀ (D X : Subgroup G) (r : ℕ), NilpotentRigidity.Hypothesis ρ D X r →
    NilpotentRigidity.Conclusion ρ D X r

/-- The rank consequence of A.1.5 for a faithful elementary two-actor on
an arbitrary finite three-group. This earlier input has no representation
or G.9.4 classification premise or conclusion. -/
def ThreeGroupRankInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (E B : Subgroup D) (r : ℕ),
    IsElementaryAbelian 2 E → Nat.card E = 2 ^ r → IsPGroup 3 B →
      E ≤ Subgroup.normalizer (B : Set D) →
        E ⊓ Subgroup.centralizer (B : Set D) = ⊥ → r ≤ primeRank 3 B

/-- Exactly the p=3 reducibility assertion of A.1.31(3), expressed by a
proper nonzero invariant subgroup of the elementary three-core. The rank
bound is on the source of the displayed surjection. Its assembly owner is
the earlier Section A.1 task, not the G.9.4 recognition branches. -/
def ThreeSectionReducibilityInput : Prop :=
  ∀ (D E : Type u) [Group D] [Finite D] [Group E] [Finite E]
    (f : D →* E), Function.Surjective f → primeRank 3 D ≤ 2 →
      Theory.GroupTheory.generalizedFitting E = pCore 3 E →
        IsElementaryAbelian 3 (pCore 3 E) → Nat.card (pCore 3 E) = 27 →
          1 < primeRank 2 E →
            ∃ R : Subgroup E, R.Normal ∧ R ≠ ⊥ ∧ R < pCore 3 E

/-- Output of the cubic Fitting reduction. In particular the three-rank
lower bound is on the actual three-core, not on its covering preimage. -/
structure ThreeCoreData (ρ : Representation (ZMod 2) G V)
    (A : Subgroup G) (m : ℕ) : Prop where
  faithful : A ⊓ Subgroup.centralizer (pCore 3 G : Set G) = ⊥
  actor_rank_le : m ≤ 2
  core_rank_ge : m ≤ primeRank 3 (pCore 3 G)
  moved_eq_top : NilpotentRigidity.movedSpace ρ (pCore 3 G) = ⊤
  even_degree : Even (Module.finrank (ZMod 2) V)

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition
