module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.Marked
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.Prefix
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.SpecificGroups.PSL4Two.SchurMultiplier
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import Theory.AtlasPort.LinearGroups.G2.BinaryThreeRank
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.InvolutionCentralizer
public import Theory.GroupTheory.PrimeRankCubeFree
public import Theory.Alternating.PrimeRank
public import Theory.SpecificGroups.SymmetricSix.Parabolics

/-!
# Binary endpoint rows for the marked local sieve

The source row in 13.5.21 has three different groups which must not be
identified: the ambient quotient `X̂`, the generated actor `K̂ V̂`, and the
component `K̂`.  `MarkedActorRow` records this distinction.  Its marked
involution is an element of the ambient group and is central in the selected
Sylow subgroup; the actor and component are supplied by actual group
equivalences.  This lets the catalogue use a concrete model without replacing
the source configuration by a stronger abstract assertion.

The binary model facts below are the endpoint facts used by the local sieve.
The degree-four/five lower bound comes from the checked `SL₄(2) ≃ A₈`
comparison and its identity-block embedding.  The G₂ bound is stated both for
the full octonion group and for its genuine commutator subgroup.  The latter is
kept separate throughout.  Covering-kernel statements retain the actual
covering map and its universality hypotheses.

Source: Aschbacher--Smith, combined manuscript, 13.5.21 and B.4.2,
printed p.924 (PDF p.941).  Concrete model calculations are imported from the
licensed ATLAS ports cited in the component files.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels

/-! ### The source-faithful marked row -/

variable {H : Type*} [Group H] [Finite H]

/-- A generated component/actor row with the source Sylow mark.

`A`, `C`, and `V` are subgroups of the same ambient group `H`.  Thus a model
equivalence for `A` never silently becomes an equivalence for `H`, while the
Sylow and centrality fields live in the original ambient quotient. -/
structure MarkedActorRow (A C V : Subgroup H)
    (M N : Type*) [Group M] [Finite M] [Group N] [Finite N] where
  actor_model : A ≃* M
  component_model : C ≃* N
  actor_generated : C ⊔ V = A
  mark : H
  mark_mem_actor : mark ∈ A
  marked_subgroup : V = zpowers mark
  mark_ne_one : mark ≠ 1
  mark_square : mark ^ 2 = 1
  marked_sylow : Sylow 2 H
  mark_mem_sylow : mark ∈ marked_sylow
  mark_central_sylow : ∀ x, x ∈ marked_sylow → x * mark = mark * x

namespace MarkedActorRow

variable {A C V : Subgroup H} {M N : Type*} [Group M] [Finite M] [Group N] [Finite N]

omit [Finite H] in
theorem mark_order (r : MarkedActorRow A C V M N) : orderOf r.mark = 2 :=
  orderOf_eq_prime r.mark_square r.mark_ne_one

omit [Finite H] in
theorem mark_mem_marked (r : MarkedActorRow A C V M N) : r.mark ∈ V := by
  simpa only [r.marked_subgroup] using (mem_zpowers r.mark)

omit [Finite H] in
theorem marked_card (r : MarkedActorRow A C V M N) : Nat.card V = 2 := by
  rw [r.marked_subgroup, Nat.card_zpowers, r.mark_order]

theorem actor_primeRank_equiv (p : ℕ) (r : MarkedActorRow A C V M N) :
    primeRank p A = primeRank p M :=
  primeRank_congr p r.actor_model

theorem component_primeRank_equiv (p : ℕ) (r : MarkedActorRow A C V M N) :
    primeRank p C = primeRank p N :=
  primeRank_congr p r.component_model

/-- The component centralizer of the marked ambient involution.  In the
source A₆ row the mark may be outside the component, so its centralizer is
formed in `H` and then restricted to `C`. -/
def markedCentralizer (r : MarkedActorRow A C V M N) : Subgroup C :=
  (centralizer ({r.mark} : Set H)).comap C.subtype

/-- Relabel only the generated actor by an actual group equivalence.  The
ambient mark, Sylow, and component remain the original source data. -/
def relabelActor {M' : Type*} [Group M'] [Finite M']
    (r : MarkedActorRow A C V M N) (e : M ≃* M') :
    MarkedActorRow A C V M' N :=
  { actor_model := r.actor_model.trans e
    component_model := r.component_model
    actor_generated := r.actor_generated
    mark := r.mark
    mark_mem_actor := r.mark_mem_actor
    marked_subgroup := r.marked_subgroup
    mark_ne_one := r.mark_ne_one
    mark_square := r.mark_square
    marked_sylow := r.marked_sylow
    mark_mem_sylow := r.mark_mem_sylow
    mark_central_sylow := r.mark_central_sylow }

end MarkedActorRow

/-- An order condition used for the marked centralizers in B.4.2.  A
three-rank-two elementary abelian subgroup would force a factor nine in the
ambient order, so absence of that factor gives the required rank-one bound. -/
theorem primeRank_three_le_one_of_not_dvd_nine
    {Q : Type*} [Group Q] [Finite Q]
    (hQ : ¬ 9 ∣ Nat.card Q) : primeRank 3 Q ≤ 1 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply (primeRank_le_iff_elementary_card_le Q).mpr
  intro E hE
  obtain ⟨a, ha⟩ := (hE.isPGroup 3).exists_card_eq
  have hdiv : Nat.card E ∣ Nat.card Q :=
    Subgroup.card_dvd_of_injective E.subtype E.subtype_injective
  have ha_le : a ≤ 1 := by
    by_contra h
    have ha2 : 2 ≤ a := by omega
    apply hQ
    have hp : 9 ∣ Nat.card E := by
      rw [ha]
      simpa only [show (9 : ℕ) = 3 ^ 2 by norm_num] using (pow_dvd_pow 3 ha2)
    exact hp.trans hdiv
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> simp [ha]

theorem markedCentralizer_threeRank_le_one
    {A C V : Subgroup H} {M N : Type*} [Group M] [Finite M] [Group N] [Finite N]
    (r : MarkedActorRow A C V M N)
    (hQ : ¬ 9 ∣ Nat.card (MarkedActorRow.markedCentralizer r)) :
    primeRank 3 (MarkedActorRow.markedCentralizer r) ≤ 1 :=
  primeRank_three_le_one_of_not_dvd_nine hQ

/-! ### The literal source prefix -/

open CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
open Section08.Source

variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}

/-- The generated actor in the literal quotient `X/C_X(K*)`. -/
def markedActor (s : Selected D K) (h : D.Hypothesis)
    [(componentCentralizer s h).Normal] : Subgroup (Xhat s h) :=
  Khat s h ⊔ Vhat s h

theorem markedActor_component_le (s : Selected D K) (h : D.Hypothesis)
    [(componentCentralizer s h).Normal] : Khat s h ≤ markedActor s h :=
  le_sup_left

theorem markedActor_marked_le (s : Selected D K) (h : D.Hypothesis)
    [(componentCentralizer s h).Normal] : Vhat s h ≤ markedActor s h :=
  le_sup_right

/-- Build the marked row directly from the proved 13.5.19 prefix.  The
generator is retained as an element of `X̂`; the supplied equivalences are the
actual catalogue comparisons for the actor and component. -/
def MarkedActorRow.ofPrefix (s : Selected D K) (h : D.Hypothesis)
    [(componentCentralizer s h).Normal] (Y : Subgroup G)
    (p : Prefix s h Y)
    {M N : Type*} [Group M] [Finite M] [Group N] [Finite N]
    (actor_model : markedActor s h ≃* M)
    (component_model : Khat s h ≃* N)
    (v : Xhat s h) (hv : zpowers v = Vhat s h) :
    MarkedActorRow (markedActor s h) (Khat s h) (Vhat s h) M N := by
  have hvV : v ∈ Vhat s h := by
    rw [← hv]
    exact mem_zpowers v
  have hvT : v ∈ That s h := p.actor_le_sylow hvV
  have hov : orderOf v = 2 := by
    rw [← Nat.card_zpowers, hv, p.actor_card]
  have hv2 : v ^ 2 = 1 := by
    simpa [hov] using pow_orderOf_eq_one v
  have hv1 : v ≠ 1 := by
    intro hvone
    rw [hvone] at hov
    norm_num at hov
  let S : Sylow 2 (Xhat s h) := Classical.choose p.marked_sylow
  have hS : (S : Subgroup (Xhat s h)) = That s h :=
    Classical.choose_spec p.marked_sylow
  refine
    { actor_model := actor_model
      component_model := component_model
      actor_generated := rfl
      mark := v
      mark_mem_actor := markedActor_marked_le s h hvV
      marked_subgroup := hv.symm
      mark_ne_one := hv1
      mark_square := hv2
      marked_sylow := S
      mark_mem_sylow := ?_
      mark_central_sylow := ?_ }
  · change v ∈ (S : Subgroup (Xhat s h))
    rw [hS]
    exact hvT
  · intro x hx
    have hxT : x ∈ That s h := by
      rw [← hS]
      exact hx
    exact mem_centralizer_iff.mp (p.actor_central hvV) x hxT

/-! ### Binary component rank facts -/

open Matrix

variable {A C V : Subgroup H} {M N : Type*} [Group M] [Finite M] [Group N] [Finite N]

noncomputable def binaryLinear_three_model_equiv :
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  Matrix.PSL3Two.equiv

theorem binaryLinear_threeRank_le_one :
    primeRank 3 (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ≤ 1 := by
  rw [primeRank_equiv 3 Matrix.PSL3Two.equiv]
  apply primeRank_three_le_one_of_not_dvd_nine
  rw [Matrix.PSL3Two.card_PSL]
  decide

/-- The two binary linear endpoint degrees have the required component
three-rank.  The statement is deliberately conditional on the catalogue's
actual degree, so degree three is never silently included. -/
theorem binaryLinear_component_threeRank_ge_two {n : ℕ} (hn : n = 4 ∨ n = 5)
    (r : MarkedActorRow A C V (SpecialLinearGroup (Fin n) (ZMod 2)) N) :
    2 ≤ primeRank 3 A := by
  rw [r.actor_primeRank_equiv 3]
  exact BinaryLinear.SmallCubicRank.four_or_five hn

/-- The actual alternating-six component has three-rank exactly two. -/
theorem alternatingSix_threeRank :
    primeRank 3 (alternatingGroup (Fin 6)) = 2 := by
  simpa using (GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime
    6 3 (by decide) (by decide))

/-- The symmetric-six actor has three-rank at most two; this uses the literal
order 720 and the cube-free rank lemma, rather than an unproved identification
with its alternating subgroup. -/
theorem symmetricSix_threeRank_le_two :
    primeRank 3 (Equiv.Perm (Fin 6)) ≤ 2 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply primeRank_le_two_of_cube_not_dvd
  change ¬ 3 ^ 3 ∣ Nat.card Theory.SpecificGroups.SymmetricSix.S6
  rw [Theory.SpecificGroups.SymmetricSix.s6_order]
  decide

/-- The full octonion group and its genuine commutator subgroup are separate
models.  The first bound is the checked order-27 Sylow calculation. -/
theorem fullG2_threeRank_le_two :
    primeRank 3 (Atlas.G2.Model (ZMod 2)) ≤ 2 :=
  Atlas.G2.BinaryThreeRank.primeRank_le_two

theorem derivedG2_threeRank_le_two :
    primeRank 3 (commutator (Atlas.G2.Model (ZMod 2))) ≤ 2 := by
  exact (primeRank_subgroup_le 3 (commutator (Atlas.G2.Model (ZMod 2)))).trans
    fullG2_threeRank_le_two

theorem derivedG2_isSimple :
    IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
  Atlas.G2.isSimple_commutator_binary

/-! ### Marked G₂ involution and centralizer facts -/

theorem derivedG2_marked_involution_mem_sylow :
    Atlas.G2.BinaryParabolicPair.derivedInvolution ∈
      Atlas.G2.BinaryParabolicPair.derivedSylow :=
  Atlas.G2.BinaryParabolicPair.derivedInvolution_mem_sylow

theorem derivedG2_marked_involution_order :
    orderOf Atlas.G2.BinaryParabolicPair.derivedInvolution = 2 :=
  Atlas.G2.BinaryParabolicPair.derivedInvolution_order

theorem derivedG2_marked_involution_centralizer_eq_first :
    Subgroup.centralizer
        ({Atlas.G2.BinaryParabolicPair.derivedInvolution} :
          Set Atlas.G2.BinaryParabolicPair.DerivedModel) =
      Atlas.G2.BinaryParabolicPair.derivedFirst :=
  Atlas.G2.BinaryParabolicPair.centralizer_derivedInvolution_eq_first

theorem derivedG2_marked_involution_centralizer_solvable :
    Group.IsSolvable (Subgroup.centralizer
      ({Atlas.G2.BinaryParabolicPair.derivedInvolution} :
        Set Atlas.G2.BinaryParabolicPair.DerivedModel)) :=
  Atlas.G2.BinaryParabolicPair.isSolvable_centralizer_derivedInvolution

theorem derivedG2_marked_involution_centralizer_threeRank_le_one :
    primeRank 3 (Subgroup.centralizer
      ({Atlas.G2.BinaryParabolicPair.derivedInvolution} :
        Set Atlas.G2.BinaryParabolicPair.DerivedModel)) ≤ 1 := by
  rw [derivedG2_marked_involution_centralizer_eq_first]
  apply primeRank_three_le_one_of_not_dvd_nine
  rw [Atlas.G2.BinaryParabolicPair.card_derivedFirst]
  decide

/-! ### Catalogue constructors and covering centres -/

abbrev FullG2 := Atlas.G2.Model (ZMod 2)
abbrev DerivedG2 := commutator (Atlas.G2.Model (ZMod 2))
abbrev SymmetricEight := Equiv.Perm (Fin 8)
abbrev SymmetricSix := Equiv.Perm (Fin 6)
abbrev AlternatingSix := alternatingGroup (Fin 6)

/-- Preserve the source actor-generation and Sylow mark while changing an
abstract actor to the full binary G₂ model. -/
def fullG2Row (r : MarkedActorRow A C V M N) (e : M ≃* FullG2) :
    MarkedActorRow A C V FullG2 N :=
  r.relabelActor e

/-- The symmetric-eight catalogue constructor is a genuine actor equivalence;
it does not identify the ambient quotient with the permutation model. -/
def symmetricEightRow (r : MarkedActorRow A C V M N) (e : M ≃* SymmetricEight) :
    MarkedActorRow A C V SymmetricEight N :=
  r.relabelActor e

/-- The marked S₆/A₆ pair is represented by independent actor and component
equivalences. -/
def symmetricSixRow (r : MarkedActorRow A C V M N) (e : M ≃* SymmetricSix) :
    MarkedActorRow A C V SymmetricSix N :=
  r.relabelActor e

def alternatingSixRow (r : MarkedActorRow A C V M N) (e : M ≃* AlternatingSix) :
    MarkedActorRow A C V AlternatingSix N :=
  r.relabelActor e

theorem fullG2Row_threeRank_le_two (r : MarkedActorRow A C V FullG2 N) :
    primeRank 3 A ≤ 2 := by
  rw [r.actor_primeRank_equiv 3]
  exact fullG2_threeRank_le_two

omit [Finite H] in
theorem symmetricEightRow_preserves_mark (r : MarkedActorRow A C V M N)
    (e : M ≃* SymmetricEight) :
    (symmetricEightRow r e).mark = r.mark ∧
      (symmetricEightRow r e).marked_subgroup = r.marked_subgroup :=
  ⟨rfl, rfl⟩

theorem symmetricSixRow_threeRank_le_two (r : MarkedActorRow A C V SymmetricSix N) :
    primeRank 3 A ≤ 2 := by
  rw [r.actor_primeRank_equiv 3]
  exact symmetricSix_threeRank_le_two

theorem alternatingSixRow_component_threeRank (r : MarkedActorRow A C V M AlternatingSix)
    : primeRank 3 C = 2 := by
  rw [r.component_primeRank_equiv 3]
  exact alternatingSix_threeRank

/-! ### Actual covering kernels -/

open Theory.GroupTheory PerfectCentralCovering

noncomputable def binaryLinear_four_cover_kernel_equiv_two
    (F : Type*) [Field F] [Finite F] (hF : Nat.card F = 2)
    {S L : Type*} [Group S] [Finite S] [IsQuasisimple S]
    [Group L] [Finite L] [IsQuasisimple L]
    (e : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) F)
    (g : Covering L S) (hg : Covering.IsUniversal g) :
    g.toMonoidHom.ker ≃* Multiplicative (ZMod 2) :=
  Matrix.PSL4Two.kernelEquivTwo F hF e g hg

theorem binaryLinear_five_cover_kernel_eq_bot
    (F : Type*) [Field F] [Finite F] (hF : Nat.card F = 2) :
    (PerfectCentralCovering.universalProjection
      (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F)).ker = ⊥ :=
  Theory.SpecificGroups.PSL5Two.UniversalCover.field_universalProjection_ker_eq_bot F hF

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels
end
