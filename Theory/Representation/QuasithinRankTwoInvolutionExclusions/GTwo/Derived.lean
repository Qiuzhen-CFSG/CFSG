module
public import Theory.Representation.G2BinaryDerivedRatios
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.GTwo

/-!
# Moved-plane transitivity inside the derived binary G2 group

The explicit long-root cubic has cube one and therefore lies in the actual
index-two derived subgroup. Conjugating it preserves that membership.
Every derived involution is a long root, so this cubic makes its moved-plane
stabilizer transitive in every intermediate group containing G2(2)'.
The ambient conjugator need not belong to that intermediate group.

This supplies the derived-group case for the original strict action in
`ChapterG.Section11.WholeBinaryG2`. Source: Aschbacher--Smith B.4.5--6,
G.11.7 and 6.2.19, printed pp.87--90,367,691.
-/

public noncomputable section
open Subgroup Representation
namespace Representation.RankTwo.GTwo
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.BinaryNormalizer

private theorem cube_mem_derived (c : G) (hc : c^3=1) : c ∈ commutator G := by
  have hi : (commutator G).index=2 := by
    rw [BinaryParabolicPair.commutator_eq_longRootClosure]
    exact BinaryException.index_H
  have hs := Subgroup.sq_mem_of_index_two hi (c^2)
  have he : (c^2)^2=c := by
    rw [←pow_mul,show 2*2=3+1 by decide,pow_succ,hc,one_mul]
  exact he ▸ hs

private def conjugateCoordinates (g : G) : V ≃ₗ[K] V :=
  LinearMap.GeneralLinearGroup.toLinearEquiv ((action K).asGroupHom g)

private theorem conjugateCoordinates_intertwines (g x : G) (v : V) :
    conjugateCoordinates g (action K x v) =
      action K (MulAut.conj g x) (conjugateCoordinates g v) := by
  change action K g (action K x v) = action K (g*x*g⁻¹) (action K g v)
  simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]

/-- The long-root cubic already belongs to the derived subgroup, even when
its conjugating element is in the full binary group. -/
theorem exists_derived_cubic_of_long_root (a : G)
    (ha : ShortRootProducts.IsLongRootElement a) :
    ∃ c ∈ commutator G, Commute c a ∧ c^3=1 ∧
      ∀ z ∈ movedSpace (action K) a, action K c z=z → z=0 := by
  obtain ⟨r,hr,g,he⟩ := ha
  have hr1 : r=1 := by
    have hh : ∀ r : ZMod 2, r=0 ∨ r=1 := by decide
    exact (hh r).resolve_left hr
  subst r
  subst a
  let c := MulAut.conj g cycleActor
  have hc : c^3=1 := by rw [←map_pow,cycleActor_cube,map_one]
  refine ⟨c,cube_mem_derived c hc,cycleActor_commute.map (MulAut.conj g),hc,?_⟩
  intro z hz hfix
  let E := conjugateCoordinates g⁻¹
  have hea : MulAut.conj g⁻¹ (MulAut.conj g (rootA 1))=rootA 1 := by
    change g⁻¹*(g*rootA 1*g⁻¹)*g=rootA 1
    group
  have hec : MulAut.conj g⁻¹ c=cycleActor := by
    change g⁻¹*(g*cycleActor*g⁻¹)*g=cycleActor
    group
  have hz' : E z ∈ movedSpace (action K) (rootA 1) := by
    rw [←hea]
    exact (movedSpace_transport (action K) (action K) (MulAut.conj g⁻¹) E
      (conjugateCoordinates_intertwines g⁻¹) _ z).mpr hz
  have hf' : action K cycleActor (E z)=E z := by
    have hh := conjugateCoordinates_intertwines g⁻¹ c z
    rw [hec,hfix] at hh
    exact hh.symm
  exact E.injective ((cycleActor_fixed_moved_eq_zero (E z) hz' hf').trans E.map_zero.symm)

/-- Every intermediate group containing G2(2)' is transitive on the moved
plane of each of its involutions in the derived group. -/
theorem stabilizerTransitive_intermediate_derived
    (J : Subgroup G) (hJ : commutator G ≤ J) (a : J)
    (ha : a^2=1) (hne : a≠1) (had : (a:G) ∈ commutator G)
    (hr : Module.finrank K (movedSpace ((action K).comp J.subtype) a)=2) :
    StabilizerTransitive ((action K).comp J.subtype)
      (movedSpace ((action K).comp J.subtype) a) := by
  have hl := derived_involution_long ⟨a,had⟩ (Subtype.ext (congrArg (fun x : J => (x:G)) ha))
    (fun hh => hne (Subtype.ext (congrArg (fun x : commutator G => (x:G)) hh)))
  obtain ⟨c,hc,hcomm,hcube,hfix⟩ := exists_derived_cubic_of_long_root a hl
  exact stabilizerTransitive_of_order_three ((action K).comp J.subtype) a ⟨c,hJ hc⟩
    hr (Subtype.ext hcomm.eq) (Subtype.ext hcube) hfix
end Representation.RankTwo.GTwo

