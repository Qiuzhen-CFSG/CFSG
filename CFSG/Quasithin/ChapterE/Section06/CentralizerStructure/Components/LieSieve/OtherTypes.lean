module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.BinaryAction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.BinaryGeometry
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.G2Geometry
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.ReeTitsGeometry
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.TrialityGeometry

/-!
# The remaining characteristic-two component cases of E.6.8

The invariant parabolics constructed in the four geometry leaves live in the
actual quotient (L Q_L)/O₂(L Q_L), with Q_L = N_Q(L). Their lifted joins with Q
have characteristic two and no relatively subnormal chi-zero blocks. Applying
the full E.6.7 input puts these lifts in M. Quotient generation and control of
the two-core then force L ≤ M, contradicting component escape.

This excludes PSL₅(2), G₂(2^f) for f ≥ 2, triality at every binary field order,
the Ree family, the genuine derived G₂(2)′ and Tits endpoints, and every central
two-cover of G₂(4). The triality branch keeps the universal 1.2.1(3) statement
explicit. All branches keep the full earlier local facts and E.6.7 input;
no additional model geometry is assumed.

For PSL₄(2), the same argument excludes the inner-action case. The surviving
outer action gives an actual isomorphism (LQ)/O₂(LQ) ≃ S₈. `BinaryAction`
supplies action corank and global weak-closure parameter one. The adequate
linear-four tuple retains precisely these conclusions. The unchanged full
`LinearFourAlternative` is obtained only by the explicitly conditional adapter
when U = C_V(L) is separately available.

`lieType_reduction` handles every constructor of the original `LieTypeComponent`
and passes the remaining actual models to the Borel and symplectic owners.
The parent characteristic-two sieve retains those branches and final assembly;
its source-theorem owner must discharge the earlier theorem inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), and 1.2.1(3), printed p.504
(PDF p.521).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes
open Chapter1.Section02.LocalModels InvariantSubspaces.BlockSelection

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G}

/-- The two invariant paired-flag parabolics exclude PSL₅(2) by E.6.7. -/
theorem not_linear_five (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (blocks : E67Input T M V) : ¬ ClassicalGroup.IsPSL L 5 2 := by
  intro hm
  obtain ⟨hN, ⟨family⟩⟩ := BinaryGeometry.five_component_geometry h hU hL hQ hm
  exact exclude_of_blockFreeQuotientFamily h earlier hU hL hQ hN blocks family

/-- The full nonbinary G₂ family is excluded with its original field bound. -/
theorem not_g2 (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (blocks : E67Input T M V) {f : ℕ} (hf : 2 ≤ f) :
    ¬ ClassificationModels.IsG2At L (2 ^ f) := by
  intro hm
  obtain ⟨hN, ⟨family⟩⟩ := G2Geometry.g2_geometry h hU hL hQ hf hm
  exact exclude_of_blockFreeQuotientFamily h earlier hU hL hQ hN blocks family

/-- The binary endpoint uses the actual derived G₂(2)′ carrier. -/
theorem not_g2_derived (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (blocks : E67Input T M V) :
    ¬ Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  intro hm
  obtain ⟨hN, ⟨family⟩⟩ := G2Geometry.derived_geometry h hU hL hQ hm
  exact exclude_of_blockFreeQuotientFamily h earlier hU hL hQ hN blocks family

/-- The quotient argument excludes every central two-cover of G₂(4). -/
theorem not_g2_cover (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (blocks : E67Input T M V) (hz : IsPGroup 2 (center L)) :
    ¬ ClassificationModels.IsG2At (L ⧸ center L) 4 := by
  intro hm
  obtain ⟨hN, ⟨family⟩⟩ := G2Geometry.cover_geometry h hU hL hQ hz hm
  exact exclude_of_blockFreeQuotientFamily h earlier hU hL hQ hN blocks family

/-- The graph-field triality family, including q = 2, is excluded by its
two actual quotient parabolics. The universal 1.2.1(3) input retains both
relative normality and the full nonnormal-component alternative. -/
theorem not_triality (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (blocks : E67Input T M V)
    (source : ∀ H : Subgroup G, H ∈ Chapter1.H G → ∀ B : Subgroup H,
      B.IsCComponent → B.Normal ∨ (normalizer (B : Set H)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel (B ⧸ pCore 2 B))
    {f : ℕ} (hf : 1 ≤ f) :
    ¬ _root_.Triality.Standard.IsTrialityGroupAt (2 ^ f) L := by
  intro hm
  obtain ⟨hN, ⟨family⟩⟩ := TrialityGeometry.triality_geometry h hU hL hQ source hf hm
  exact exclude_of_blockFreeQuotientFamily h earlier hU hL hQ hN blocks family

/-- The Ree family retains the exact fixed-group model and m ≥ 1. -/
theorem not_ree (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (blocks : E67Input T M V) {m : ℕ} (hm : 1 ≤ m) :
    ¬ IsReeF4At L m := by
  intro hmodel
  obtain ⟨hN, ⟨family⟩⟩ := ReeTitsGeometry.ree_geometry h hU hL hQ hm hmodel
  exact exclude_of_blockFreeQuotientFamily h earlier hU hL hQ hN blocks family

/-- The Tits endpoint is excluded on the genuine Parrott carrier. -/
theorem not_tits (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (blocks : E67Input T M V) : ¬ Nonempty (L ≃* Tits.ParrottGroup) := by
  intro hm
  obtain ⟨hN, ⟨family⟩⟩ := ReeTitsGeometry.tits_geometry h hU hL hQ hm
  exact exclude_of_blockFreeQuotientFamily h earlier hU hL hQ hN blocks family

/-- The inner-action parabolics contradict component escape. The remaining
binary branch gives an isomorphism of the literal core quotient with S₈. -/
theorem linear_four_quotient (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (blocks : E67Input T M V) (hm : ClassicalGroup.IsPSL L 4 2) :
    Nonempty ((↥(L ⊔ Q) ⧸ pCore 2 ↥(L ⊔ Q)) ≃* Equiv.Perm (Fin 8)) := by
  obtain ⟨hN, hcases⟩ := BinaryGeometry.four_component_geometry h hU hL hQ hm
  rcases hcases with hfamily | hsym
  · obtain ⟨family⟩ := hfamily
    exact (exclude_of_blockFreeQuotientFamily h earlier hU hL hQ hN blocks family).elim
  · exact hsym

/-- The adequate linear-four branch retains the actual S₈ quotient and
both rank-one equalities. It makes no assertion identifying U with C_V(L). -/
theorem linear_four_adequate (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (blocks : E67Input T M V) (hm : ClassicalGroup.IsPSL L 4 2) :
    ClassicalGroup.IsPSL L 4 2 ∧
      Nonempty ((↥(L ⊔ Q) ⧸ pCore 2 ↥(L ⊔ Q)) ≃* Equiv.Perm (Fin 8)) ∧
      actionCorank V L = 1 ∧ globalR V = 1 :=
  ⟨hm, linear_four_quotient h earlier hU hL hQ blocks hm,
    binary_component_rank_one h earlier hU hL (Or.inl rfl) hm⟩

/-- A conditional adapter to the unchanged full source record. The additional
fixed-space equality is explicit and is not supplied by the adequate theorem. -/
theorem linear_four_alternative_of_fixed (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (blocks : E67Input T M V) (hm : ClassicalGroup.IsPSL L 4 2)
    (hfixed : U = V ⊓ centralizer (L : Set G)) : LinearFourAlternative M V U Q L := by
  obtain ⟨hmodel, hquotient, hdimension, hrank⟩ :=
    linear_four_adequate h earlier hU hL hQ blocks hm
  exact ⟨hmodel, hquotient, hfixed, hdimension, hrank⟩

/-- All remaining rank-two constructors feed the linear-three and symplectic
owners. The original field bounds and the actual derived PSp₄(2)′ remain. -/
theorem rankTwo_reduction (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (blocks : E67Input T M V)
    (source : ∀ H : Subgroup G, H ∈ Chapter1.H G → ∀ B : Subgroup H,
      B.IsCComponent → B.Normal ∨ (normalizer (B : Set H)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel (B ⧸ pCore 2 B))
    (hm : RankTwoTheoremC L) :
    (∃ f, 1 ≤ f ∧ ClassicalGroup.IsPSL L 3 (2 ^ f)) ∨
      (∃ f, 2 ≤ f ∧ ClassicalGroup.IsPSp L 2 (2 ^ f)) ∨
      Nonempty (L ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  cases hm with
  | linear f hf iso => exact Or.inl ⟨f, hf, iso⟩
  | symplectic f hf iso => exact Or.inr (Or.inl ⟨f, hf, iso⟩)
  | g2 f hf iso => exact (not_g2 h earlier hU hL hQ blocks hf iso).elim
  | triality f hf iso => exact (not_triality h earlier hU hL hQ blocks source hf iso).elim
  | ree m hm iso => exact (not_ree h earlier hU hL hQ blocks hm iso).elim
  | symplectic_derived iso => exact Or.inr (Or.inr iso)
  | g2_derived iso => exact (not_g2_derived h earlier hU hL hQ blocks iso).elim
  | tits iso => exact (not_tits h earlier hU hL hQ blocks iso).elim

/-- The complete remaining-family reduction for the characteristic-two sieve.
Every original constructor is handled. The unresolved Borel and symplectic
branches retain their actual models, while the four-dimensional branch already
has its quotient and numerical conclusions. The E.6.8 parent supplies the
Borel/symplectic alternatives and discharges the earlier source inputs. -/
theorem lieType_reduction (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (blocks : E67Input T M V)
    (source : ∀ H : Subgroup G, H ∈ Chapter1.H G → ∀ B : Subgroup H,
      B.IsCComponent → B.Normal ∨ (normalizer (B : Set H)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel (B ⧸ pCore 2 B))
    (hm : LieTypeComponent L) :
    ClassificationModels.IsBenderModel L ∨
      (∃ f, 1 ≤ f ∧ ClassicalGroup.IsPSL L 3 (2 ^ f)) ∨
      (∃ f, 2 ≤ f ∧ ClassicalGroup.IsPSp L 2 (2 ^ f)) ∨
      Nonempty (L ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) ∨
      (IsPGroup 2 (center L) ∧ ClassicalGroup.IsPSL (L ⧸ center L) 3 4) ∨
      (ClassicalGroup.IsPSL L 4 2 ∧
        Nonempty ((↥(L ⊔ Q) ⧸ pCore 2 ↥(L ⊔ Q)) ≃* Equiv.Perm (Fin 8)) ∧
        actionCorank V L = 1 ∧ globalR V = 1) := by
  rcases hm with hB | hR | h4 | h5 | ⟨hz, h3 | hG⟩
  · exact Or.inl hB
  · rcases rankTwo_reduction h earlier hU hL hQ blocks source hR with h3 | hS | hS
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (Or.inl hS))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hS)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (linear_four_adequate h earlier hU hL hQ blocks h4)))))
  · exact (not_linear_five h earlier hU hL hQ blocks h5).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hz, h3⟩))))
  · exact (not_g2_cover h earlier hU hL hQ blocks hz hG).elim

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes
