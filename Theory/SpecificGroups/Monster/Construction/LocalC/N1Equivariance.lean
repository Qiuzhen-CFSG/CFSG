module
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.NaturalAction

/-!
# Full triality equivariance of the source Leech comparison

The checked loop and standard-automorphism equations are closed under
multiplication and the concrete `N1` normal form. They produce integral
Leech isometries which intertwine both the genuine natural representation
and the conjugation action on `Q1`. Faithfulness of the real Leech action
makes each lift unique and proves the homomorphism laws. Thus no abstract
choice of an isometry of binary quadratic spaces is used.

Source: Aschbacher, *Sporadic Groups*, Lemma 27.2 and the generator
comparison on printed pp. 147–148. Products here act on the left.
-/

public section
noncomputable section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin

/-- The real action specifies a lattice lift uniquely. -/
theorem natural_lift_unique (g : N1) (h k : LeechIsometryGroup)
    (hh : ∀ v, realLeechRepresentation h (naturalLeechComparison v) =
      naturalLeechComparison (NaturalAction.representation g v))
    (hk : ∀ v, realLeechRepresentation k (naturalLeechComparison v) =
      naturalLeechComparison (NaturalAction.representation g v)) : h = k := by
  apply realLeechRepresentation_faithful
  apply LinearEquiv.ext
  intro w
  obtain ⟨v,rfl⟩ := naturalLeechComparison.surjective w
  exact (hh v).trans (hk v).symm

private def Lift (g : N1) (h : LeechIsometryGroup) : Prop :=
  (∀ v, realLeechRepresentation h (naturalLeechComparison v) =
    naturalLeechComparison (NaturalAction.representation g v)) ∧
  (∀ q, (sourceQ1LatticeHom (q1Conjugation g q)).toAdd =
    leechModTwoRepresentation h (sourceQ1LatticeHom q).toAdd)

private theorem lift_mul {g g' : N1} {h h' : LeechIsometryGroup}
    (hg : Lift g h) (hg' : Lift g' h') : Lift (g * g') (h * h') := by
  constructor
  · intro v
    rw [map_mul]
    change realLeechRepresentation h (realLeechRepresentation h' (naturalLeechComparison v)) = _
    rw [hg'.1, hg.1, map_mul]
    rfl
  · intro q
    rw [map_mul]
    change (sourceQ1LatticeHom (q1Conjugation g (q1Conjugation g' q))).toAdd = _
    rw [hg.2, hg'.2, map_mul]
    rfl

private theorem lift_psi1 (d : ParkerLoop) :
    Lift ⟨psi1N d,psi1N_mem_N1 d⟩ 1 := by
  constructor
  · intro v
    rw [map_one]
    exact (naturalLeechComparison_psi1 d v).symm
  · intro q
    rw [map_one]
    exact sourceQ1LatticeHom_conjugation_psi1 d q

private theorem lift_psi2 (d : ParkerLoop) :
    Lift ⟨psi2N d,psi2N_mem_N1 d⟩ (signIsometry d.1) := by
  exact ⟨fun v => (naturalLeechComparison_psi2 d v).symm,
    sourceQ1LatticeHom_conjugation_psi2 d⟩

private theorem lift_psiAut1 (α : ParkerStandardGroup) :
    Lift ⟨psiAut1N α,psiAut1N_mem_N1 α⟩ (permutationEmbedding (parkerStandardProjection α)) := by
  exact ⟨fun v => (naturalLeechComparison_psiAut1 α v).symm,
    sourceQ1LatticeHom_conjugation_psiAut1 α⟩

private theorem lift_normalForm (d e : ParkerLoop) (α : ParkerStandardGroup) :
    Lift (normalForm d e α)
      (permutationEmbedding (parkerStandardProjection α) * signIsometry e.1) := by
  have hword : normalForm d e α =
      (⟨psiAut1N α,psiAut1N_mem_N1 α⟩ : N1) * ⟨psi2N e,psi2N_mem_N1 e⟩ *
        ⟨psi1N d,psi1N_mem_N1 d⟩ := by
    apply Subtype.ext
    rfl
  rw [hword]
  simpa only [mul_one] using lift_mul (lift_mul (lift_psiAut1 α) (lift_psi2 e)) (lift_psi1 d)

private theorem lift_exists (g : N1) : ∃ h, Lift g h := by
  obtain ⟨⟨d,e,α⟩,rfl⟩ := normalForm_bijective.surjective g
  exact ⟨_,lift_normalForm d e α⟩

/-- The actual natural action preserves the integral Leech lattice. -/
def n1LeechRepresentation : N1 →* LeechIsometryGroup where
  toFun g := (lift_exists g).choose
  map_one' := natural_lift_unique 1 _ 1 (lift_exists 1).choose_spec.1
    (fun v => by rw [map_one, map_one]; rfl)
  map_mul' g h := natural_lift_unique (g*h) _ _ (lift_exists (g*h)).choose_spec.1
    (lift_mul (lift_exists g).choose_spec (lift_exists h).choose_spec).1

/-- Equivariance for the actual twenty-four dimensional signed representation. -/
theorem n1LeechRepresentation_natural (g : N1) (v : SignedModules.Natural.B1_24) :
    realLeechRepresentation (n1LeechRepresentation g) (naturalLeechComparison v) =
      naturalLeechComparison (NaturalAction.representation g v) :=
  (lift_exists g).choose_spec.1 v

/-- Source 27.2 is equivariant for every element of the actual `N1`. -/
theorem sourceQ1LatticeHom_equivariant (g : N1) (q : Q1) :
    (sourceQ1LatticeHom (q1Conjugation g q)).toAdd =
      leechModTwoRepresentation (n1LeechRepresentation g) (sourceQ1LatticeHom q).toAdd :=
  (lift_exists g).choose_spec.2 q

/-- The concrete integral formula on collected triality words. -/
theorem n1LeechRepresentation_normalForm (d e : ParkerLoop) (α : ParkerStandardGroup) :
    n1LeechRepresentation (normalForm d e α) =
      permutationEmbedding (parkerStandardProjection α) * signIsometry e.1 :=
  natural_lift_unique _ _ _ (n1LeechRepresentation_natural _) (lift_normalForm d e α).1

end Sporadic.Monster.Construction.LocalC
