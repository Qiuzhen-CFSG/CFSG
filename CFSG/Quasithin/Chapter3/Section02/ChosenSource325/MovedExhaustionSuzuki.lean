module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.Multiplicity.SuzukiEndpoint
public import Theory.Representation.BinaryOffender.Homogeneous.AutomorphismTwist

/-!
# Excluding normalized Suzuki support in the chosen-seed orbit

For a homogeneous Irr+ seed, an elementary actor with odd outer image acts
by inner automorphisms. The existing central-quotient twist equivalence
therefore makes the seed invariant. This constructs the invariant Suzuki
constituent required by D.3.8 rather than assuming its existence.

If a perfect fixed-free subgroup K commutes with the moved support X, a
fixed-space supplement to such a constituent would make it all of [U,X].
The cyclic linear centralizer would then make K fix that nonzero space.
D.2.7 consequently gives a strict ratio drop on the constituent. For a
normalized Suzuki component, the proved Chapter K endpoint gives the
opposite bound two, excluding this case.

The support argument adapts the general proofs in Chapter11's
`Multiplicity/SupportObstruction`; its public Suzuki endpoint is reused.
`SeedAlternativesMovedExhaustionSuzuki` supplies the actual component and
classification hypotheses. Excluding a component permuted by the actor,
the normal three-rank-one component and the FF sections, and final Source325
assembly, remain with qt-baumann-fsu.
Source: Aschbacher--Smith A.1.41--42, D.2.7--8, D.3.8--9 and K.3.6,
printed pp.31--32,179--180,199--201,457; application 3.2.5, p.580.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W)

/-- A fixed-space supplement forces the constituent to be the whole moved space. -/
private theorem moved_eq_of_invariant_supplement {X A B : Subgroup H}
    {I : Submodule (ZMod 2) W} (hI : IsIrrPlus ρ X I)
    (hAI : A ≤ subspaceStabilizer ρ I) (hBA : B ≤ A)
    (hXB : ⁅X,B⁆ = X) (hs : I ⊔ fixedSpace ρ A = ⊤) :
    subspaceCommutator ρ ⊤ X = I := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,v,_,rfl⟩
    obtain ⟨i,hi,c,hc,rfl⟩ := Submodule.mem_sup.mp (show v ∈ I ⊔ fixedSpace ρ A by rw [hs]; trivial)
    have hdiff := differences_mem_of_invariant_mod_fixed ρ hI.choose (hBA.trans hAI)
      (show X ≤ subspaceStabilizer ρ (fixedSpace ρ A ⊔ I) by
        rw [sup_comm,hs]; exact le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      (fixedSpace_antitone ρ hBA) hXB c hc x hx
    have he : ρ x (i+c) - (i+c) = (ρ x i-i)+(ρ x c-c) := by rw [map_add]; abel
    rw [he]
    exact I.add_mem (I.sub_mem ((hI.choose hx i).2 hi) hi) hdiff
  · rw [← hI.choose_spec.1]
    exact subspaceCommutator_mono_left ρ le_top X

variable [FiniteDimensional (ZMod 2) W]

/-- A fixed-free perfect commuting actor excludes an Irr⁺ moved space. -/
private theorem not_irrPlus_moved_of_commuting_perfect {K X : Subgroup H}
    [Group.IsPerfect K] (hK : fixedSpace ρ K = ⊥)
    (hXK : X ≤ centralizer (K : Set H)) :
    ¬ IsIrrPlus ρ X (subspaceCommutator ρ ⊤ X) := by
  intro hI
  have hKI : K ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ X) :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      ((le_centralizer_iff.mp hXK).trans (Subgroup.centralizer_le_normalizer _))
  exact hI.ne_bot ρ (bot_unique (hK ▸ hI.le_fixedSpace_of_perfect_centralizes ρ
    (le_centralizer_iff.mp hXK) hKI))

/-- The faithful-span alternative is impossible, so D.2.7 gives strict ratio decrease. -/
private theorem starred_constituent_ratio_drop [Finite H] {K X A B : Subgroup H}
    [Group.IsPerfect K] (hK : fixedSpace ρ K = ⊥)
    (hXK : X ≤ centralizer (K : Set H)) (hA : A ∈ ChapterD.QhatStar ρ)
    (hBA : B ≤ A) (hXB : ⁅X,B⁆ = X)
    {I : Submodule (ZMod 2) W} (hI : IsIrrPlus ρ X I)
    (hAI : A ≤ subspaceStabilizer ρ I) :
    restrictedSubgroup ρ I A ∈ ChapterD.Qhat (subspaceImageRepresentation ρ I) ∧
      actionRatio (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A) < cubicRatio ρ := by
  have hn : ¬ I ≤ fixedSpace ρ A := by
    intro hi
    apply hI.not_le_fixedSpace ρ
    rw [← hXB]
    exact le_fixedSpace_commutator_of_invariant ρ hI.choose (hi.trans (fixedSpace_antitone ρ hBA))
  rcases (ChapterD.QhatStar.restriction_alternatives ρ hA I hAI hn).2.2 with hd | ⟨_,hs⟩
  · exact hd
  · have he := moved_eq_of_invariant_supplement ρ hI hAI hBA hXB hs
    exact (not_irrPlus_moved_of_commuting_perfect ρ hK hXK (he.symm ▸ hI)).elim


omit [FiniteDimensional (ZMod 2) W] in
/-- Odd outer order makes each homogeneous seed invariant under the elementary actor. -/
theorem homogeneous_invariant_of_odd_outer [Finite H]
    {X A : Subgroup H} {I : Submodule (ZMod 2) W}
    (hI : IsIrrPlusWith ρ X A I) (hA : IsElementaryAbelian 2 A)
    (ho : Odd (Nat.card (MulAut.Outer X))) : A ≤ subspaceStabilizer ρ I := by
  let := hA
  intro a ha
  apply (subspace_map_eq_iff ρ I a).mp
  let t : A := ⟨a,ha⟩
  let n : normalizer (X : Set H) := ⟨a⁻¹,hI.normalizes (A.inv_mem ha)⟩
  have hn : n ^ 2 = 1 := by
    apply Subtype.ext
    change (a⁻¹) ^ 2 = 1
    rw [inv_pow,elemPow_eq_one_of_isElementaryAbelian a ha,inv_one]
  obtain ⟨u,hu⟩ := involution_inner_of_odd_outer ho (X.normalizerMonoidHom n)
    (by rw [← map_pow,hn,map_one])
  let σ := (quotientImage ρ X I hI.invariant).toRepresentation
  let c := LinearMap.GeneralLinearGroup.toLinearEquiv (σ.asGroupHom u)
  apply hI.map_eq_of_central_twist ρ t c
  intro x v
  change σ u (σ x v) = σ (X.normalizerMonoidHom n x) (σ u v)
  rw [← hu]
  change σ u (σ x v) = σ (u * x * u⁻¹) (σ u v)
  simp only [← Module.End.mul_apply,← map_mul,mul_assoc,inv_mul_cancel,mul_one]

/-- Construct the invariant constituent rather than assuming one in the endpoint argument. -/
theorem exists_invariant_irrPlus_of_suzuki [Finite H]
    (hf : Function.Injective ρ)
    (X A : Subgroup H) [Group.IsPerfect X] (hX : X ≠ ⊥)
    (hA : IsElementaryAbelian 2 A) (hn : A ≤ normalizer (X : Set H))
    {r : ℕ} (hr : 0 < r)
    (e : X ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) :
    ∃ I : Submodule (ZMod 2) W, IsIrrPlus ρ X I ∧ A ≤ subspaceStabilizer ρ I := by
  let := hA
  obtain ⟨I,hI⟩ := Homogeneous.exists_isIrrPlusWith_of_faithful ρ hf X A hX hn
    (IsElementaryAbelian.isPGroup 2 A)
  have ho : Odd (Nat.card (MulAut.Outer X)) := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact BenderSuzuki.MatrixGroups.suzuki_odd_outer_index r (by omega)
  exact ⟨I,hI.isIrrPlus,homogeneous_invariant_of_odd_outer ρ hI hA ho⟩

/-- A starred elementary actor cannot move a normalized Suzuki component
commuting with a fixed-free perfect subgroup. -/
theorem no_normalized_suzuki_support [Finite H]
    (hf : Function.Injective ρ) (K J A B : Subgroup H)
    [Group.IsPerfect K] [IsQuasisimple J]
    (hK : fixedSpace ρ K = ⊥) (hJC : J ≤ centralizer (K : Set H))
    (hJ : IsSQTK KnownSimple.IsKnownSimple J)
    (hJn : J ≠ ⊥) (hAJ : A ≤ normalizer (J : Set H))
    (hA : A ∈ ChapterD.QhatStar ρ) (hBA : B ≤ A) (hJB : ⁅J,B⁆ = J)
    {r : ℕ} (hr : 0 < r)
    (e : J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) : False := by
  obtain ⟨I,hI,hAI⟩ := exists_invariant_irrPlus_of_suzuki ρ hf J A hJn
    hA.1.2.1.2 hAJ hr e
  have hs := starred_constituent_ratio_drop ρ hK hJC hA hBA hJB hI hAI
  have hl := Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.SuzukiSupport.restricted_actor_ratio_ge_two
    ρ hJ hI hAI hAJ hA.1.2.1.2 hr e hs.1
  exact (not_lt_of_ge hl) (hs.2.trans_le hA.1.1)

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
