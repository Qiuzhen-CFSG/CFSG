module

public import Theory.SpecificGroups.BinaryLinear.FourResidual
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceResiduals

/-!
# The rank-four component and the source residual

The selected local component is perfect. Its actual SL₄(2) two-core
quotient therefore makes it its own O^{3′}. Relative subnormality and
prime-to-three index identify its image with O^{3′}(Gᵥ). This discharges
the residual premise of the earlier plane/Thompson contradiction, without
assuming normality in G or confusing O^{3′}, O³ and O_{3′}.

The source rank-four identification, relative subnormality, index and
orthogonal Thompson comparison remain explicit. Their construction is
needed before this can complete 13.6.23 or the surrounding source argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.23 and the following paragraph, printed p.933.
-/

public section
open Subgroup Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal
open ComponentSelection
variable {G : Type*} [Group G] [Finite G]

private theorem twoPerfect_of_perfect (H : Type*) [Group H] [Finite H]
    [Group.IsPerfect H] : IsPPerfect 2 H := by
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (H ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (H ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (H ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (H ⧸ N) inferInstance

/-- The residual identification uses relative subnormality in C_G(v)
and the real linear quotient of K. Normality is derived by residual theory. -/
theorem component_eq_primeToResidual (T K : Subgroup G) (v : G)
    (hK : K ∈ Chapter1.LIn (Gv v) (Tv T v))
    (e : K ⧸ pCore 2 K ≃* SL(4, ZMod 2))
    (hsub : (K.subgroupOf (Gv v)).IsSubnormal)
    (hindex : Nat.Coprime 3 (K.subgroupOf (Gv v)).index) :
    K = (primeToResidual 3 (Gv v)).map (Gv v).subtype := by
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hK.2
  have hres := BinaryLinear.primeToResidual_three_eq_top_of_four_quotient
    (twoPerfect_of_perfect K) e
  let f := (subgroupOfEquivOfLe hK.1).symm
  have hf : primeToResidual 3 (K.subgroupOf (Gv v)) = ⊤ := by
    have hh := map_primeToResidual (p := 3) f
    rw [hres, map_top_of_surjective _ f.surjective] at hh
    exact hh.symm
  rw [primeToResidual_eq_of_subnormal_coprime_index 3 _ hsub hf hindex,
    map_subgroupOf_eq_of_le hK.1]

/-- Apply the residual calculation to the literal plane and Thompson
subgroups. `Source.plane_eq_of_flagMarking` supplies the plane identity in
the marked source configuration. -/
theorem false_of_plane_and_linearFour_comparison
    (T : Sylow 2 G) (K V₂ : Subgroup G) (z v : G)
    (hK : K ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v))
    (e : K ⧸ pCore 2 K ≃* SL(4, ZMod 2))
    (hsub : (K.subgroupOf (Gv v)).IsSubnormal)
    (hindex : Nat.Coprime 3 (K.subgroupOf (Gv v)).index)
    (hV₂ : V₂ = zpowers z ⊔ zpowers v)
    (hT : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hvT : v ∈ T) (hv : v ≠ 1)
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (hJ : elementaryAbelianMaxJ ((Source.orthogonalResidual K z ⊔
      Tv (T : Subgroup G) v).pCoreIn 2) =
      elementaryAbelianMaxJ ((K ⊔ Tv (T : Subgroup G) v).pCoreIn 2))
    (h16 : (K ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥) : False := by
  have hres : K = (primeToResidual 3 (Gv v)).map (Gv v).subtype :=
    component_eq_primeToResidual (T : Subgroup G) K v hK e hsub hindex
  exact Source.false_of_residual_thompson_comparison T K V₂ z v
    hres hV₂ hT hvT hv hidx hJ h16

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal
