module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SourceContracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.SectionPlacement
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks

/-!
# The source's xi normalization cannot be omitted

Held 2.8 explicitly replaces xi by pi*xi when necessary. The corrected
`Source.SixLocalData` retains fixed coordinates, so its existence cannot
hold for every centralizer isomorphism in the proposed construction.

The centralizer automorphism below multiplies an element by pi precisely
when it swaps the two fixed points of pi. It fixes all the marked local
generators except xi, which it sends to pi*xi. In particular it fixes mu,
so changing the given centralizer isomorphism by this automorphism leaves
the section and the nonfusion hypothesis unchanged.

The supplied normal A₆ is the solvable residual of C_G(mu). Any candidate
six-point A₆ is perfect and lies in C_G(mu), hence lies in that residual.
If both xi markings admitted six-point data, the residual would contain
both mu'*xi and mu'*(pi*xi), hence pi. It also contains pi*mu and would
therefore contain mu, contradicting its trivial center. Thus at least one
of the two centralizer isomorphisms fails the fixed-coordinate contract.
This is an obstruction to that contract, not to Held's normalized source.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 2.8 (p.229) and Lemma 4.2 (pp.232–235).
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry
namespace SixConstruction

private abbrev H := CentralizerModels.a10Centralizer

private theorem last_pair (g : H) :
    (g.1.1 8 = 8 ∧ g.1.1 9 = 9) ∨ (g.1.1 8 = 9 ∧ g.1.1 9 = 8) := by
  obtain ⟨a, rfl⟩ := NoncentralAnalysis.Coordinates.word_bijective.surjective g
  exact (show ∀ a : NoncentralAnalysis.Coordinates.Code,
    ((NoncentralAnalysis.Coordinates.word a).1.1 8 = 8 ∧
      (NoncentralAnalysis.Coordinates.word a).1.1 9 = 9) ∨
    ((NoncentralAnalysis.Coordinates.word a).1.1 8 = 9 ∧
      (NoncentralAnalysis.Coordinates.word a).1.1 9 = 8) by decide +kernel) a

private def xiTwist (g : H) : H :=
  if g.1.1 8 = 8 then g else modelCentralInvolution * g

private theorem xiTwist_mul (g h : H) : xiTwist (g * h) = xiTwist g * xiTwist h := by
  have hc := mem_center_iff.mp modelCentralInvolution_mem_center g
  have hs : modelCentralInvolution * modelCentralInvolution = 1 := by decide +kernel
  rcases last_pair g with ⟨hg8, hg9⟩ | ⟨hg8, hg9⟩ <;>
    rcases last_pair h with ⟨hh8, hh9⟩ | ⟨hh8, hh9⟩
  all_goals simp only [xiTwist, Subgroup.coe_mul, Perm.mul_apply, hh8, hg8, hg9]
  all_goals simp only [show (9 : Fin 10) ≠ 8 from by decide, if_false, if_true]
  · rw [← mul_assoc g, hc, mul_assoc]
  · exact (mul_assoc _ _ _).symm
  · rw [← mul_assoc, ← hc, mul_assoc g, hs, mul_one]

private theorem xiTwist_involutive : Function.Involutive xiTwist := by
  intro g
  have hs : modelCentralInvolution * modelCentralInvolution = 1 := by decide +kernel
  have h9 : modelCentralInvolution.1.1 9 = 9 := by decide +kernel
  rcases last_pair g with ⟨hg8, hg9⟩ | ⟨hg8, hg9⟩
  · simp [xiTwist, hg8]
  · simp [xiTwist, hg8, Subgroup.coe_mul, Perm.mul_apply, h9, ← mul_assoc, hs]

/-- Central transvection exchanging xi and pi*xi and fixing the other marks. -/
public def xiTwistEquiv :
    CentralizerModels.a10Centralizer ≃* CentralizerModels.a10Centralizer where
  toFun := xiTwist
  invFun := xiTwist
  left_inv := xiTwist_involutive
  right_inv := xiTwist_involutive
  map_mul' := xiTwist_mul

public theorem xiTwistEquiv_generators : ∀ i : Fin 8,
    xiTwistEquiv (modelElement i) =
      if i = 7 then modelElement 0 * modelElement 7 else modelElement i := by
  decide +kernel

public theorem xiTwistEquiv_pi : xiTwistEquiv (modelElement 0) = modelElement 0 := by decide +kernel
public theorem xiTwistEquiv_mu : xiTwistEquiv (modelElement 1) = modelElement 1 := by decide +kernel
public theorem xiTwistEquiv_mu' : xiTwistEquiv (modelElement 2) = modelElement 2 := by decide +kernel
public theorem xiTwistEquiv_xi : xiTwistEquiv (modelElement 7) = modelElement 0 * modelElement 7 := by
  decide +kernel

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (s : NoncentralAnalysis.AlternatingSixSection
    (centralizer ({D.a10NoncentralInvolution e} : Set G)))

public theorem mu_twist : mu D (e.trans xiTwistEquiv) = mu D e := by
  change D.a10ModelEmbedding e (xiTwistEquiv.symm (modelElement 1)) = _
  rw [show xiTwistEquiv.symm (modelElement 1) = modelElement 1 from by decide +kernel]
  rfl

public theorem mu'_twist : mu' D (e.trans xiTwistEquiv) = mu' D e := by
  change D.a10ModelEmbedding e (xiTwistEquiv.symm (modelElement 2)) = _
  rw [show xiTwistEquiv.symm (modelElement 2) = modelElement 2 from by decide +kernel]
  rfl

public theorem xi_twist : xi D (e.trans xiTwistEquiv) = pi D e * xi D e := by
  change D.a10ModelEmbedding e (xiTwistEquiv.symm (modelElement 7)) = _
  rw [show xiTwistEquiv.symm (modelElement 7) = modelElement 0 * modelElement 7
    from by decide +kernel, map_mul]
  rfl

public theorem source_subgroup_le_section (L : Source.SixLocalData D e) :
    L.A ≤ s.ambientSubgroup := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect L.A := Group.IsPerfect.ofSurjective
    (f := L.alternatingEquiv.symm.toMonoidHom) L.alternatingEquiv.symm.surjective
  apply s.perfect_le_ambientSubgroup
  intro a ha
  exact mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_iff.mp (L.A_centralizes ha) (mu D e) (by simp)).symm)

include s in
/-- The two xi normalizations cannot both realize the fixed source contract. -/
public theorem incompatible_xi_normalizations
    (L : Source.SixLocalData D e)
    (L' : Source.SixLocalData D (e.trans xiTwistEquiv)) : False := by
  have hA := source_subgroup_le_section D e s L
  have hA' : L'.A ≤ s.ambientSubgroup := by
    let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    let : Group.IsPerfect L'.A := Group.IsPerfect.ofSurjective
      (f := L'.alternatingEquiv.symm.toMonoidHom) L'.alternatingEquiv.symm.surjective
    apply s.perfect_le_ambientSubgroup
    intro a ha
    have hc := (mem_centralizer_iff.mp (L'.A_centralizes ha)
      (mu D (e.trans xiTwistEquiv)) (by simp)).symm
    rw [mu_twist] at hc
    exact mem_centralizer_singleton_iff.mpr hc
  have hx := hA L.mu'_xi_mem
  have hx' := hA' L'.mu'_xi_mem
  rw [mu'_twist, xi_twist] at hx'
  have hp : pi D e ∈ s.ambientSubgroup := by
    have hm := s.ambientSubgroup.div_mem hx' hx
    have he : (mu' D e * (pi D e * xi D e)) / (mu' D e * xi D e) = pi D e := by
      rw [← mul_assoc, ← (commute_pi D e 2).eq, mul_assoc, mul_div_cancel_right]
    rwa [he] at hm
  have hm := s.ambientSubgroup.mul_mem (s.ambientSubgroup.inv_mem hp) (hA L.pi_mu_mem)
  rw [inv_mul_cancel_left] at hm
  exact mu_not_mem_section D e s hm

include s in
/-- A bad marking exists even after the noncentral involution is fixed. -/
public theorem exists_equiv_without_source_six :
    ∃ e' : D.centralizer ≃* CentralizerModels.a10Centralizer,
      D.a10NoncentralInvolution e' = D.a10NoncentralInvolution e ∧
      ¬ Nonempty (Source.SixLocalData D e') := by
  classical
  by_cases h : Nonempty (Source.SixLocalData D e)
  · refine ⟨e.trans xiTwistEquiv, mu_twist D e, ?_⟩
    rintro ⟨L'⟩
    exact incompatible_xi_normalizations D e s h.some L'
  · exact ⟨e, rfl, h⟩

include s in
/-- The obstruction preserves all mathematical inputs of the proposed
construction: G and D are unchanged, as are mu, its nonfusion and its section. -/
public theorem exists_equiv_preserving_inputs_without_source_six
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) :
    ∃ e' : D.centralizer ≃* CentralizerModels.a10Centralizer,
      D.a10NoncentralInvolution e' = D.a10NoncentralInvolution e ∧
      ¬ IsConj D.z (D.a10NoncentralInvolution e') ∧
      Nonempty (NoncentralAnalysis.AlternatingSixSection
        (centralizer ({D.a10NoncentralInvolution e'} : Set G))) ∧
      ¬ Nonempty (Source.SixLocalData D e') := by
  obtain ⟨e', hmu, hbad⟩ := exists_equiv_without_source_six D e s
  refine ⟨e', hmu, ?_, ?_, hbad⟩
  · rwa [hmu]
  · rw [hmu]
    exact ⟨s⟩

end SixConstruction
end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry
