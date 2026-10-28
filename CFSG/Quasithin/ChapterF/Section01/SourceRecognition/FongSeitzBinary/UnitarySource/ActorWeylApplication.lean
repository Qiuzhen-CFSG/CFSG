module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorWeyl
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.Generation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.MarkedLocal
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.MarkedWeyl
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.EightCells

/-!
# Constructed source Weyl lifts, central kernels and original generation

The two actual root actors generate the same finite quotient under the
original F.1.1 hypotheses, also with a geometric marking. For quadrangles,
one Sylow subgroup of N constructs both Weyl involutions and their exact
dihedral relation. The lifts lie in their corresponding root actors and
pull back to involutions in the whole original endpoints, with Q.q retained.
The actual actor kernel is central of odd order; its centrality also pulls
back to the original endpoint without erasing a possible SU3 scalar kernel.

These constructed lifts discharge full generation in either unitary
presentation once the positive maps cover U. The tensor realization gives
that coverage for U4. A full Cartan parametrization then supplies both whole
endpoint equalities and the common Borel with the same orientation and lifts.

This is source progress, not completed unitary recognition. Regularity and
remainder containment, the (6A) module realizations and common-field labels,
remaining U5 equations, and compatibility of these lifts with the labelled
torus and rank-one matrix equations remain with this source owner.

Source: Fong--Seitz I (5C), pp.25--26; I (6A), pp.36--38;
II §§8B--C, pp.197--210; AS F.1.1--3; DGS Theorem D, p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

/-- The two actual root-generated actors generate the same marked quotient. -/
theorem marked_rootActors_generate
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (h : HypothesisF11 L S) (split : SplitData Q.tits) :
    rootActor Q split 0 ⊔ rootActor Q split 1 = ⊤ := by
  rw [rootActors_sup_eq_weylRootSpan]
  exact marked_weylRootSpan_eq_top Q e h split

variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (hm : rotationOrder Q = 4)

/-- Both endpoint orientations use the SAME homomorphic Weyl section. -/
@[expose] def quadrangleLifts (i : Fin 2) : MarkedWeyl.Lifts Q i where
  s := actorWeylSection Q split (weyl_isTwo_of_quadrangle Q hm) (Q.simple (1-i))
  t := actorWeylSection Q split (weyl_isTwo_of_quadrangle Q hm) (Q.simple i)
  s_class := actorWeylSection_class Q split _ _
  t_class := actorWeylSection_class Q split _ _

theorem quadrangleLifts_actor (i : Fin 2) :
    ((quadrangleLifts Q split hm i).s : X ⧸ Q.D) ∈ rootActor Q split (1-i) ∧
    ((quadrangleLifts Q split hm i).t : X ⧸ Q.D) ∈ rootActor Q split i :=
  ⟨actorWeylSection_simple_mem Q split _ _,actorWeylSection_simple_mem Q split _ _⟩

/-- These are actual equations in N, before any model identification. -/
theorem quadrangleLifts_equations (i : Fin 2) :
    (quadrangleLifts Q split hm i).s^2 = 1 ∧
    (quadrangleLifts Q split hm i).t^2 = 1 ∧
    ((quadrangleLifts Q split hm i).s*(quadrangleLifts Q split hm i).t)^4 = 1 := by
  refine ⟨actorWeylSection_simple_square Q split _ _,
    actorWeylSection_simple_square Q split _ _, ?_⟩
  let f := actorWeylSection Q split (weyl_isTwo_of_quadrangle Q hm)
  have he : (f (Q.simple 0)*f (Q.simple 1))^4 = 1 := by
    rw [← hm]
    exact actorWeylSection_rotation Q split _
  fin_cases i
  · change (f (Q.simple 1)*f (Q.simple 0))^4 = 1
    calc
      _ = f (Q.simple 1)*(f (Q.simple 0)*f (Q.simple 1))^4*(f (Q.simple 1))⁻¹ := by
        simp only [pow_succ,pow_zero]
        group
      _ = 1 := by rw [he]; group
  · exact he

/-- The constructed lifts discharge the generation field of either unitary
presentation as soon as the actual positive maps cover U. -/
theorem marked_positive_fullGenerated
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (h : HypothesisF11 L S) (i : Fin 2)
    {RA RD RC RB H : Type*} [Group RA] [Group RD] [Group RC] [Group RB] [Group H]
    (r : PositiveMaps (X ⧸ Q.D) RA RD RC RB) (cartan : H →* (X ⧸ Q.D))
    (hU : r.generated = split.U) :
    ReflectionLaws.fullGenerated r cartan
      ((quadrangleLifts Q split hm i).s : X ⧸ Q.D)
      ((quadrangleLifts Q split hm i).t : X ⧸ Q.D) = ⊤ := by
  apply marked_generate_of_unipotent_and_lifts Q e h split
    (fun j => actorWeylSection Q split (weyl_isTwo_of_quadrangle Q hm) (Q.simple j))
    (fun j => actorWeylSection_class Q split _ _) _
  · rw [← hU]
    exact (show r.generated ≤ r.borel cartan from le_sup_left).trans
      (fun x hx => Subgroup.subset_closure (Or.inl hx))
  · intro j
    apply Subgroup.subset_closure
    apply Or.inr
    fin_cases i <;> fin_cases j
    · exact Or.inr (Set.mem_singleton _)
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr (Set.mem_singleton _)

variable (Q : SourceQuotient L S) (split : SplitData Q.tits) (hm : rotationOrder Q = 4)

/-- Pull the constructed reflection back to the corresponding WHOLE original
endpoint; its quotient representative is retained below. -/
@[expose] def originalActorWeyl (i : Fin 2) : parabolic L S i :=
  (MarkedLocal.endpoint Q (originalMarkedIso Q) i).symm
    ⟨actorWeylSection Q split (weyl_isTwo_of_quadrangle Q hm) (Q.simple i),
      rootActor_le_endpoint Q split i (actorWeylSection_simple_mem Q split _ i)⟩

private theorem original_endpoint_quotient (i : Fin 2) (g : parabolic L S i) :
    Q.q ⟨g,parabolic_le_generated i g.property⟩ =
      (MarkedLocal.endpoint Q (originalMarkedIso Q) i g : (generated L S) ⧸ Q.D) := by
  fin_cases i
  · exact (originalMarkedIso_left_apply Q g).symm
  · exact (originalMarkedIso_right_apply Q g).symm

theorem originalActorWeyl_quotient (i : Fin 2) :
    Q.q ⟨originalActorWeyl Q split hm i,
      parabolic_le_generated i (originalActorWeyl Q split hm i).property⟩ =
      (actorWeylSection Q split (weyl_isTwo_of_quadrangle Q hm) (Q.simple i) :
        (generated L S) ⧸ Q.D) := by
  rw [original_endpoint_quotient,originalActorWeyl,MulEquiv.apply_symm_apply]

@[simp] theorem originalActorWeyl_square (i : Fin 2) : (originalActorWeyl Q split hm i)^2 = 1 := by
  apply (MarkedLocal.endpoint Q (originalMarkedIso Q) i).injective
  rw [map_pow,map_one,originalActorWeyl,MulEquiv.apply_symm_apply]
  apply Subtype.ext
  exact congrArg (fun n : Q.tits.N => (n : (generated L S) ⧸ Q.D))
    (actorWeylSection_simple_square Q split _ i)

/-- The central kernel commutes with the actual actor after pullback to
the original endpoint, using precisely the quotient representatives. -/
theorem original_actor_kernel_commutes (i : Fin 2) (a b : parabolic L S i)
    (ha : Q.q ⟨a,parabolic_le_generated i a.property⟩ ∈
      rootActor Q split i ⊓ HexagonStructure.localKernel Q i)
    (hb : Q.q ⟨b,parabolic_le_generated i b.property⟩ ∈ rootActor Q split i) :
    a*b = b*a := by
  apply (MarkedLocal.endpoint Q (originalMarkedIso Q) i).injective
  rw [map_mul,map_mul]
  apply Subtype.ext
  change (MarkedLocal.endpoint Q (originalMarkedIso Q) i a : (generated L S) ⧸ Q.D) *
    (MarkedLocal.endpoint Q (originalMarkedIso Q) i b : (generated L S) ⧸ Q.D) =
    (MarkedLocal.endpoint Q (originalMarkedIso Q) i b : (generated L S) ⧸ Q.D) *
    (MarkedLocal.endpoint Q (originalMarkedIso Q) i a : (generated L S) ⧸ Q.D)
  rw [← original_endpoint_quotient,← original_endpoint_quotient]
  exact (rootActor_inf_localKernel_centralizes Q split i ha _ hb).symm

/-- No perfectness, root-field or source regularity premise is used. -/
theorem original_rootActors_generate (h : HypothesisF11 L S) :
    rootActor Q split 0 ⊔ rootActor Q split 1 = ⊤ :=
  marked_rootActors_generate Q (originalMarkedIso Q) h split

/-- The original S and the images of constructed original endpoint
involutions generate Y, with its literal quotient map. -/
theorem originalS_actorWeyl_generate (h : HypothesisF11 L S) :
    (S.subgroupOf (generated L S)).map Q.q ⊔ closure (Set.range (fun i =>
      Q.q ⟨originalActorWeyl Q split hm i,
        parabolic_le_generated i (originalActorWeyl Q split hm i).property⟩)) = ⊤ := by
  simp_rw [originalActorWeyl_quotient]
  exact originalS_and_lifts_generate Q split _ (fun i => actorWeylSection_class Q split _ (Q.simple i)) h

/-- Once the positive and full Cartan ranges have been constructed, both
whole original endpoints and their common Borel use these SAME lifts. -/
theorem original_quadrangle_full_placements
    {RA RD RC RB H : Type*} [Group RA] [Group RD] [Group RC] [Group RB] [Group H]
    (r : PositiveMaps ((generated L S) ⧸ Q.D) RA RD RC RB)
    (cartan : H →* ((generated L S) ⧸ Q.D))
    (h : HypothesisF11 L S) (i : Fin 2) (hU : r.generated = split.U)
    (hcartan : cartan.range = Q.tits.B ⊓ Q.tits.N) :
    r.borel cartan = ((commonBorel L S).subgroupOf (generated L S)).map Q.q ∧
    r.borel cartan ⊔ closure {((quadrangleLifts Q split hm i).s : (generated L S) ⧸ Q.D)} =
      ((parabolic L S (1-i)).subgroupOf (generated L S)).map Q.q ∧
    r.borel cartan ⊔ closure {((quadrangleLifts Q split hm i).t : (generated L S) ⧸ Q.D)} =
      ((parabolic L S i).subgroupOf (generated L S)).map Q.q := by
  have he := original_full_placements Q split
    (fun j => actorWeylSection Q split (weyl_isTwo_of_quadrangle Q hm) (Q.simple j))
    (fun j => actorWeylSection_class Q split _ _) r h hU cartan hcartan
  exact ⟨he.1,he.2 (1-i),he.2 i⟩

/-- The actual tensor module placements imply the full generation required
by FourData, using the constructed common Weyl section. -/
theorem four_tensor_fullGenerated {E H : Type*} [Field E] [Group H]
    (σ : E ≃+* E) (hσ : Function.Involutive σ)
    (l : Matrix.SpecialLinearGroup (Fin 2) E →* ((generated L S) ⧸ Q.D))
    (v : Multiplicative (FourTensor.Core E σ hσ) →* ((generated L S) ⧸ Q.D))
    (cartan : H →* ((generated L S) ⧸ Q.D))
    (h : HypothesisF11 L S) (i : Fin 2)
    (hA : (FourTensor.roots E σ hσ l v).A.range = simpleRoot Q split i)
    (hV : v.range = simpleRemainder Q split i) :
    ReflectionLaws.fullGenerated (FourTensor.roots E σ hσ l v) cartan
      ((quadrangleLifts Q split hm i).s : (generated L S) ⧸ Q.D)
      ((quadrangleLifts Q split hm i).t : (generated L S) ⧸ Q.D) = ⊤ :=
  marked_positive_fullGenerated Q split hm (originalMarkedIso Q) h i _ cartan
    (four_generated_eq_unipotent Q split σ hσ l v i hA hV)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
