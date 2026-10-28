module

public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs
public import CFSG.Quasithin.ChapterE.Section03.WeakClosure
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Transport.Foundations
public import Theory.GroupAction.SubgroupConjugation
public import Theory.Representation.ElementaryAbelianAction
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Faithful binary actions and parity bridges for critical pairs

This file contains the algebraic interfaces used by F.7.11.  The action on the
actual embedded seed is constructed first, and its image is used when a
faithful actor is required.  In particular, the quotient in
`sourceConjugationQuotient` is the literal kernel quotient of the conjugation
homomorphism; it is not the original actor with a possibly nontrivial kernel.

The parity statement is deliberately conditional.  The remaining source
argument is the symmetric offender calculation for the two critical modules,
which is supplied by the F.7 assembly owner.  The weak-closure statement keeps
the conjugate weak closure and its transport inclusion explicit, as required by
E.3.13 when the conjugating element lies outside the generated subgroup.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, F.7.9(4)
and F.7.11(7--8), printed pp.313--314 (PDF pp.324--325).
-/



@[expose] public section

open Subgroup
open Subgroup.CosetGeometry.RankTwo
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterF.Section07.Track
open CFSG.Quasithin.ChapterF.Section07.CriticalPairs
open Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Parity

variable {G : Type*} [Group G]

section Representation

variable {K A X : Type*} [Group A] [Group X] [CommGroup K]
  [Module (ZMod 2) (Additive K)] [MulDistribMulAction A K]

/-- The pointwise form of the quadratic bridge.  The map `q` is retained in
the statement so that the proof uses the same literal subgroup embedding as the
source conjugation action. -/
theorem quadratic_of_nested_commutator_vanishes
    (ρ : Representation (ZMod 2) A (Additive K)) (H : Subgroup A)
    (f : A →* X) (q : K →* X)
    (hact : ∀ a : A, ∀ x : K,
      ρ a (Additive.ofMul x) = Additive.ofMul (a • x))
    (hcomm : ∀ a : A, ∀ b : A, ∀ x : K,
      ⁅f a, ⁅f b, q x⁆⁆ = 1)
    (hq : Function.Injective q)
    (hcoe : ∀ a : A, ∀ x : K,
      q (a • x) = f a * q x * (f a)⁻¹) :
    IsQuadratic ρ H := by
  intro a ha b hb v
  rw [← ofMul_toMul v, map_sub]
  rw [hact b, hact a, hact a]
  apply Additive.ext
  apply hq
  have hc := hcomm a b v.toMul
  rw [commutatorElement_eq_one_iff_mul_comm] at hc
  have hc' := congrArg (fun z => z * (f a)⁻¹) hc
  simpa [commutatorElement_def, hcoe, div_eq_mul_inv, mul_assoc] using hc'

/-- The previous bridge for the actual source action on `D.seed`. -/
theorem source_seed_quadratic
    {F : Bool → Subgroup G} (D : SourceSetup F)
    (hcomm : ∀ a b : F false, ∀ x : D.seed,
      ⁅(a : G), ⁅(b : G), (x : G)⁆⁆ = 1) :
    let : IsElementaryAbelian 2 D.V := D.reduced.elementary
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : IsElementaryAbelian 2 D.seed := IsElementaryAbelian.map (F false).subtype
    let : CommGroup D.seed := IsMulCommutative.instCommGroup
    let : AddCommGroup (Additive D.seed) := inferInstance
    let : MulDistribMulAction (F false) D.seed :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (F false) D.seed D.seed_normalized
    IsQuadratic (Representation.ofElementaryAbelianAction :
      Representation (ZMod 2) (F false) (Additive D.seed))
      (⊤ : Subgroup (F false)) := by
  let : IsElementaryAbelian 2 D.V := D.reduced.elementary
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 D.seed := IsElementaryAbelian.map (F false).subtype
  let : CommGroup D.seed := IsMulCommutative.instCommGroup
  let : AddCommGroup (Additive D.seed) := inferInstance
  let : MulDistribMulAction (F false) D.seed :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (F false) D.seed D.seed_normalized
  apply quadratic_of_nested_commutator_vanishes
    (ρ := Representation.ofElementaryAbelianAction)
    (H := (⊤ : Subgroup (F false)))
    (f := (F false).subtype) (q := D.seed.subtype)
  · intro a x
    rfl
  · intro a b x
    exact hcomm a b x
  · exact D.seed.subtype_injective
  · intro a x
    exact Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
      (F false) D.seed D.seed_normalized a x

omit [MulDistribMulAction A K] in
/-- Quadraticity survives passage to the faithful image actor. -/
theorem IsQuadratic.imageRepresentation
    (ρ : Representation (ZMod 2) A (Additive K)) {H : Subgroup A}
    (h : IsQuadratic ρ H) :
    IsQuadratic (imageRepresentation ρ) (actionSubgroup ρ H) := by
  intro a ha b hb v
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  simpa only [imageRepresentation_actionHom] using h a' ha' b' hb' v


/-- The same quadratic bridge after replacing the actor by its faithful image.
This is the representation used by the offender definitions. -/
theorem source_seed_faithful_quadratic
    {F : Bool → Subgroup G} (D : SourceSetup F)
    (hcomm : ∀ a b : F false, ∀ x : D.seed,
      ⁅(a : G), ⁅(b : G), (x : G)⁆⁆ = 1) :
    let : IsElementaryAbelian 2 D.V := D.reduced.elementary
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : IsElementaryAbelian 2 D.seed := IsElementaryAbelian.map (F false).subtype
    let : CommGroup D.seed := IsMulCommutative.instCommGroup
    let : AddCommGroup (Additive D.seed) := inferInstance
    let : MulDistribMulAction (F false) D.seed :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (F false) D.seed D.seed_normalized
    let ρ : Representation (ZMod 2) (F false) (Additive D.seed) :=
      Representation.ofElementaryAbelianAction
    IsQuadratic (imageRepresentation ρ) (actionSubgroup ρ ⊤) := by
  let : IsElementaryAbelian 2 D.V := D.reduced.elementary
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 D.seed := IsElementaryAbelian.map (F false).subtype
  let : CommGroup D.seed := IsMulCommutative.instCommGroup
  let : AddCommGroup (Additive D.seed) := inferInstance
  let : MulDistribMulAction (F false) D.seed :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (F false) D.seed D.seed_normalized
  dsimp only
  exact IsQuadratic.imageRepresentation _ (source_seed_quadratic D hcomm)


end Representation

section SourceAction

variable {F : Bool → Subgroup G}

/-- The faithful image of the actual conjugation representation of `F false` on
the embedded seed.  Every instance in this dependent statement is the one used
to define the source action, including the additive group structure. -/
theorem sourceConjugationImage_injective (D : SourceSetup F) :
    let : IsElementaryAbelian 2 D.V := D.reduced.elementary
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : IsElementaryAbelian 2 D.seed := IsElementaryAbelian.map (F false).subtype
    let : CommGroup D.seed := IsMulCommutative.instCommGroup
    let : AddCommGroup (Additive D.seed) := inferInstance
    let : MulDistribMulAction (F false) D.seed :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (F false) D.seed D.seed_normalized
    let ρ : Representation (ZMod 2) (F false) (Additive D.seed) :=
      Representation.ofElementaryAbelianAction
    Function.Injective (imageRepresentation ρ) := by
  let : IsElementaryAbelian 2 D.V := D.reduced.elementary
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 D.seed := IsElementaryAbelian.map (F false).subtype
  let : CommGroup D.seed := IsMulCommutative.instCommGroup
  let : AddCommGroup (Additive D.seed) := inferInstance
  let : MulDistribMulAction (F false) D.seed :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (F false) D.seed D.seed_normalized
  dsimp only
  exact imageRepresentation_injective _

/-- The literal first-isomorphism quotient for the actual seed action. -/
noncomputable def sourceConjugationQuotient (D : SourceSetup F) :
    let : IsElementaryAbelian 2 D.V := D.reduced.elementary
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : IsElementaryAbelian 2 D.seed := IsElementaryAbelian.map (F false).subtype
    let : CommGroup D.seed := IsMulCommutative.instCommGroup
    let : AddCommGroup (Additive D.seed) := inferInstance
    let : MulDistribMulAction (F false) D.seed :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (F false) D.seed D.seed_normalized
    let ρ : Representation (ZMod 2) (F false) (Additive D.seed) :=
      Representation.ofElementaryAbelianAction
    (⊤ : Subgroup (F false)) ⧸ ((actionHom ρ).comp
      (⊤ : Subgroup (F false)).subtype).ker ≃* actionSubgroup ρ ⊤ := by
  let : IsElementaryAbelian 2 D.V := D.reduced.elementary
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 D.seed := IsElementaryAbelian.map (F false).subtype
  let : CommGroup D.seed := IsMulCommutative.instCommGroup
  let : AddCommGroup (Additive D.seed) := inferInstance
  let : MulDistribMulAction (F false) D.seed :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (F false) D.seed D.seed_normalized
  dsimp only
  exact actionQuotientEquiv _ ⊤

/-- The same quotient with the actor written literally as `F false`; this is
the form corresponding to `(F false) / C_(F false)(D.V)` in the source. -/
noncomputable def sourceConjugationQuotient_full (D : SourceSetup F) :
    let : IsElementaryAbelian 2 D.V := D.reduced.elementary
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : IsElementaryAbelian 2 D.seed := IsElementaryAbelian.map (F false).subtype
    let : CommGroup D.seed := IsMulCommutative.instCommGroup
    let : AddCommGroup (Additive D.seed) := inferInstance
    let : MulDistribMulAction (F false) D.seed :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (F false) D.seed D.seed_normalized
    let ρ : Representation (ZMod 2) (F false) (Additive D.seed) :=
      Representation.ofElementaryAbelianAction
    (F false) ⧸ (actionHom ρ).ker ≃* actionImage ρ := by
  let : IsElementaryAbelian 2 D.V := D.reduced.elementary
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 D.seed := IsElementaryAbelian.map (F false).subtype
  let : CommGroup D.seed := IsMulCommutative.instCommGroup
  let : AddCommGroup (Additive D.seed) := inferInstance
  let : MulDistribMulAction (F false) D.seed :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (F false) D.seed D.seed_normalized
  dsimp only
  exact QuotientGroup.quotientKerEquivOfSurjective _
    (Representation.ofElementaryAbelianAction :
      Representation (ZMod 2) (F false) (Additive D.seed)).asGroupHom.rangeRestrict_surjective

/-- The kernel in the literal quotient is the centralizer of the embedded seed,
written pointwise so that no ambient finiteness or quotient identification is
silently used. -/
theorem sourceConjugation_kernel_mem_iff (D : SourceSetup F) :
    let : IsElementaryAbelian 2 D.V := D.reduced.elementary
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : IsElementaryAbelian 2 D.seed := IsElementaryAbelian.map (F false).subtype
    let : CommGroup D.seed := IsMulCommutative.instCommGroup
    let : AddCommGroup (Additive D.seed) := inferInstance
    let : MulDistribMulAction (F false) D.seed :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (F false) D.seed D.seed_normalized
    let ρ : Representation (ZMod 2) (F false) (Additive D.seed) :=
      Representation.ofElementaryAbelianAction
    ∀ a : F false, a ∈ (actionHom ρ).ker ↔
      ∀ x : D.seed, ⁅(a : G), (x : G)⁆ = 1 := by
  let : IsElementaryAbelian 2 D.V := D.reduced.elementary
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 D.seed := IsElementaryAbelian.map (F false).subtype
  let : CommGroup D.seed := IsMulCommutative.instCommGroup
  let : AddCommGroup (Additive D.seed) := inferInstance
  let : MulDistribMulAction (F false) D.seed :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (F false) D.seed D.seed_normalized
  dsimp only
  intro a
  rw [MonoidHom.mem_ker, actionHom_eq_one_iff]
  constructor
  · intro h x
    have hs := congrArg (fun v : Additive D.seed => (v.toMul : G)) (h (Additive.ofMul x))
    change (a : G) * (x : G) * (a : G)⁻¹ = (x : G) at hs
    rw [commutatorElement_def, hs, mul_inv_cancel]
  · intro h v
    apply Additive.toMul.injective
    apply Subtype.ext
    change (a : G) * (v.toMul : G) * (a : G)⁻¹ = (v.toMul : G)
    have hc := commutatorElement_eq_one_iff_mul_comm.mp (h v.toMul)
    rw [hc, mul_inv_cancel_right]

end SourceAction

section SymmetricOffender

variable {V W B C : Type*} [Group B] [Group C]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- A symmetric rank/fixed-codimension comparison produces an offender on one
of the two actual action quotients.  The conclusion is a disjunction because
the source proof compares the two modules and then transports the winning side
through the faithful conjugation image. -/
theorem symmetric_offender_of_sum_bound
    (ρ : Representation (ZMod 2) B V) (σ : Representation (ZMod 2) C W)
    {A : Subgroup B} {D : Subgroup C}
    (hA : IsElementaryTwo A) (hD : IsElementaryTwo D)
    (hsum : fixedCodim ρ A + fixedCodim σ D ≤ rank A + rank D) :
    IsOffender ρ A ∨ IsOffender σ D := by
  by_cases hρ : fixedCodim ρ A ≤ rank A
  · exact Or.inl ⟨hA, hρ⟩
  · right
    refine ⟨hD, ?_⟩
    omega

/-- Transport the winning offender through an injective actor map and an
intertwining linear equivalence.  This is the step that carries an offender on
the conjugate module back to the literal seed quotient. -/
theorem offender_transport
    (ρ : Representation (ZMod 2) B V) (σ : Representation (ZMod 2) C W)
    (f : B →* C) (hf : Function.Injective f) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (f g) (E v))
    {A : Subgroup B} (hA : IsOffender ρ A) :
    IsOffender σ (A.map f) :=
  hA.map_equivariant ρ σ f hf E hE

end SymmetricOffender

section ConditionalParity

variable {F : Bool → Subgroup G}

/-- Conditional F.7.11(7): if every even critical endpoint supplies the
noncommuting pair used by the symmetric offender calculation, then failure of
FF forces the track distance to be odd. -/
theorem odd_track_of_not_ff_conditional
    (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U)
    (hnoncomm : ∀ v : Vertex F,
      (graph F).dist (base F false) v = D.track hne →
      Even (D.track hne) →
      ⁅D.seed, vertexModule F D.seed v⁆ ≠ ⊥)
    (hoffender : ∀ v : Vertex F,
      (hd : (graph F).dist (base F false) v = D.track hne) →
      (hb : Even (D.track hne)) →
      (vertexModule F D.seed v ≤ F false ∧
        ⁅D.seed, vertexModule F D.seed v⁆ ≤ D.seed ⊓ vertexModule F D.seed v) →
      ⁅D.seed, vertexModule F D.seed v⁆ ≠ ⊥ →
      IsFFModule ρ)
    (hnotff : ¬ IsFFModule ρ) :
    Odd (D.track hne) := by
  by_contra hodd
  have hev : Even (D.track hne) := (Nat.even_or_odd _).resolve_right hodd
  obtain ⟨v, hv, _⟩ := (D.critical_witness hne).1
  exact hnotff (hoffender v hv hev (even_pair_containments F D hne hv hev)
    (hnoncomm v hv hev))

end ConditionalParity

section WeakClosure

variable {F : Bool → Subgroup G}

/-- The transport identity from E.3.13 in the case in which the conjugator
normalizes the seed.  This records the change of both arguments in the indexed
construction and is the inclusion used by the conditional parity theorem. -/
theorem indexedWeakClosure_conjugate_seed_normalized
    (V T : Subgroup G) (g : G)
    (hV : V.map (MulAut.conj g).toMonoidHom = V) :
    indexedWeakClosure V (T.map (MulAut.conj g).toMonoidHom) 0 =
      (indexedWeakClosure V T 0).map (MulAut.conj g).toMonoidHom := by
  rw [indexedWeakClosure_map_conj, hV]

/-- F.7.9(4), with the source's conjugate weak-closure transport explicit.
The hypothesis `htransport` is the inclusion obtained from E.3.13 and local
Sylow conjugacy in the larger ambient group. -/
theorem even_track_of_weakClosure_core
    (D : SourceSetup F) (hne : D.V ≠ ⊥) (T : Subgroup G)
    (hW : indexedWeakClosure D.seed T 0 ≤ (F true).pCoreIn 2)
    (hgenerator : ∀ v : Vertex F,
      (graph F).dist (base F false) v = D.track hne →
      Odd (D.track hne) →
      ∃ g : G, D.seed ≤ T.map (MulAut.conj g).toMonoidHom)
    (htransport : ∀ v : Vertex F,
      (graph F).dist (base F false) v = D.track hne →
      Odd (D.track hne) →
      ∀ g : G, D.seed ≤ T.map (MulAut.conj g).toMonoidHom →
        indexedWeakClosure D.seed (T.map (MulAut.conj g).toMonoidHom) 0 ≤
          indexedWeakClosure D.seed T 0)
    (hcore_ball : ∀ v : Vertex F,
      (graph F).dist (base F false) v = D.track hne →
      Odd (D.track hne) →
      (F true).pCoreIn 2 ≤ ballKernel F v 1) :
    Even (D.track hne) := by
  by_contra hodd
  have hodd' : Odd (D.track hne) := (Nat.even_or_odd _).resolve_left hodd
  obtain ⟨v, hv, hcrit⟩ := (D.critical_witness hne).1
  obtain ⟨g, hg⟩ := hgenerator v hv hodd'
  have hself := self_le_weakClosure_zero hg
  have hle := hself.trans ((htransport v hv hodd' g hg).trans hW)
  exact hcrit (hle.trans (hcore_ball v hv hodd'))

end WeakClosure

section Radius

variable {F : Bool → Subgroup G}

/-- Local transitivity is used in the source proof to establish the following
neighbor-kernel condition.  Once it is available at every neighbor of the
first base, the predecessor argument extends it to the whole radius-two ball. -/
theorem seed_le_ball_two_of_neighbor_kernels
    (D : SourceSetup F) (_hne : D.V ≠ ⊥)
    (hneighbor : ∀ u : Vertex F, (graph F).Adj (base F false) u →
      D.seed ≤ ballKernel F u 1) :
    D.seed ≤ ballKernel F (base F false) 2 := by
  intro x hx w hw
  rw [mem_ball_iff F D.generates (base F false) w 2] at hw
  by_cases hle : (graph F).dist (base F false) w ≤ 1
  · exact (D.seed_le_first_kernel hx w
      ((mem_ball_iff F D.generates (base F false) w 1).mpr hle))
  · have hd : (graph F).dist (base F false) w = 2 := by omega
    have hne' : base F false ≠ w := by
      intro h
      subst w
      simp at hd
    obtain ⟨u, huw, hu⟩ := exists_predecessor F D.generates (base F false) w hne'
    have hu1 : (graph F).dist (base F false) u = 1 := by omega
    have hbu : (graph F).Adj (base F false) u :=
      SimpleGraph.dist_eq_one_iff_adj.mp hu1
    exact (hneighbor u hbu hx w
      ((mem_ball_one F u w).mpr (Or.inl huw.symm)))

/-- Relative-normality form of the neighbor-kernel input.  The edge
containment is the local-core statement; `normal_le_ballKernel_one_iff` and
local transitivity then turn it into pointwise fixing of the adjacent ball. -/
theorem neighbor_kernel_of_relative_normality
    (D : SourceSetup F)
    (hnormal : ∀ u : Vertex F, ∀ _hu : (graph F).Adj (base F false) u,
      ((D.seed.subgroupOf (stabilizer F u)).Normal))
    (hedge : ∀ u : Vertex F, ∀ _hu : (graph F).Adj (base F false) u,
      D.seed ≤ stabilizer F u ⊓ stabilizer F (base F false)) :
    ∀ u : Vertex F, (graph F).Adj (base F false) u →
      D.seed ≤ ballKernel F u 1 := by
  intro u hu
  let : ((D.seed.subgroupOf (stabilizer F u)).Normal) := hnormal u hu
  intro x hx
  have hsub : D.seed.subgroupOf (stabilizer F u) ≤
      (stabilizer F u ⊓ stabilizer F (base F false)).subgroupOf (stabilizer F u) := by
    intro y hy
    exact ⟨(hedge u hu hy).1, (hedge u hu hy).2⟩
  have hn := (normal_le_ballKernel_one_iff F hu.symm
    (D.seed.subgroupOf (stabilizer F u))).2 hsub
  exact hn (show (⟨x, (hedge u hu hx).1⟩ : stabilizer F u) ∈
    D.seed.subgroupOf (stabilizer F u) from hx)

/-- The radius-one-to-radius-two part of F.7.11(8).  Once local transitivity
has shown that the seed fixes the radius-two ball, the track specification gives
`1 < b` without any finiteness or parity assumption. -/
theorem one_lt_track_of_seed_le_ball_two
    (D : SourceSetup F) (hne : D.V ≠ ⊥)
    (hfix : D.seed ≤ ballKernel F (base F false) 2) :
    1 < D.track hne := by
  have htwo : 2 ≤ D.track hne :=
    ((D.track_spec hne).2.2.2 2).mp hfix
  omega

/-- The p-core form used by F.7.11(8), keeping the local-transitivity bridge
as an explicit premise for the surrounding geometry module. -/
theorem one_lt_track_of_true_core
    (D : SourceSetup F) (hne : D.V ≠ ⊥)
    (hcore : D.seed ≤ (F true).pCoreIn 2)
    (hneighbor : ∀ u : Vertex F, (graph F).Adj (base F false) u →
      D.seed ≤ (F true).pCoreIn 2 → D.seed ≤ ballKernel F u 1) :
    1 < D.track hne :=
  one_lt_track_of_seed_le_ball_two D hne
    (seed_le_ball_two_of_neighbor_kernels D hne (fun u hu => hneighbor u hu hcore))

/-- F.7.11(8) with the local-transitivity and relative-normality premises
spelled out for the assembly owner. -/
theorem one_lt_track_of_true_core_of_relative_normality
    (D : SourceSetup F) (hne : D.V ≠ ⊥)
    (hcore : D.seed ≤ (F true).pCoreIn 2)
    (hnormal : ∀ u : Vertex F, ∀ _hu : (graph F).Adj (base F false) u,
      ((D.seed.subgroupOf (stabilizer F u)).Normal))
    (hedge : ∀ u : Vertex F, ∀ _hu : (graph F).Adj (base F false) u,
      D.seed ≤ stabilizer F u ⊓ stabilizer F (base F false)) :
    1 < D.track hne := by
  apply one_lt_track_of_true_core D hne hcore
  intro u hu _
  exact neighbor_kernel_of_relative_normality D hnormal hedge u hu

end Radius

end CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Parity
