module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Normalizer
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Intrinsic
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Calculus

/-!
# The rank of the original tensor actor

Faithful tensor coordinates identify the kernel of the maximal-local action
with the literal centralizer of the original full module. Thus the rank of
an actor image is the corank of its centralizer kernel. If an actor has
corank at most one in a conjugate module which the original module does not
normalize, global rank greater than three forces actor rank at least three.

This is the rank entrance to Aschbacher–Smith 9.4.5, printed p.737.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

theorem maximalAction_eq_one_iff (a : D.maximalLocal) :
    m.maximalAction a = 1 ↔ (a : G) ∈ centralizer (D.fullModule : Set G) := by
  constructor
  · intro ha v hv
    have he := m.maximalAction_coordinates a ⟨v,hv⟩
    rw [ha] at he
    have hh := congrArg (fun x : D.fullModule => (x : G))
      (m.coordinates_injective (Multiplicative.toAdd.injective he.symm))
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro ha
    apply LinearEquiv.ext
    intro u
    obtain ⟨v,hv⟩ := m.sectionData.onto (Multiplicative.ofAdd u)
    have hv' : (m.sectionData.coordinates v).toAdd = u := congrArg Multiplicative.toAdd hv
    have he := m.maximalAction_coordinates a v
    have hvfix : D.fullModule.normalizerMonoidHom
        ⟨(a : G),D.maximalLocal_normalizes_fullModule a.property⟩ v = v := by
      apply Subtype.ext
      change (a : G) * (v : G) * (a : G)⁻¹ = v
      rw [← ha v v.property,mul_inv_cancel_right]
    rw [hvfix,hv'] at he
    exact he

theorem maximalAction_ker :
    m.maximalAction.ker = (centralizer (D.fullModule : Set G)).subgroupOf D.maximalLocal := by
  ext a
  exact m.maximalAction_eq_one_iff a

/-- The literal tensor-action image has the rank of the actor modulo its
centralizer of the original module. -/
theorem rank_maximalAction_image {A : Subgroup G} (hAM : A ≤ D.maximalLocal) :
    BinaryOffender.rank ((A.subgroupOf D.maximalLocal).map m.maximalAction) =
      subgroupCorank A (A ⊓ centralizer (D.fullModule : Set G)) := by
  unfold BinaryOffender.rank subgroupCorank
  rw [← relIndex_ker,m.maximalAction_ker,relIndex_subgroupOf hAM,inf_relIndex_left]

/-- Nonnormalization forces rank at least three in the actual tensor-action image. -/
theorem tensor_actor_rank_ge_three (hr : 3 < globalR D.fullModule)
    (g : G) {A : Subgroup G}
    (hAW : A ≤ D.fullModule.map (MulAut.conj g).toMonoidHom)
    (hcor : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom) A ≤ 1)
    (hAT : A ≤ (T : Subgroup G))
    (hnot : ¬ D.fullModule ≤ normalizer
      (D.fullModule.map (MulAut.conj g).toMonoidHom : Set G)) :
    3 ≤ BinaryOffender.rank ((A.subgroupOf D.maximalLocal).map m.maximalAction) := by
  by_contra hbad
  have hrank : BinaryOffender.rank
      ((A.subgroupOf D.maximalLocal).map m.maximalAction) ≤ 2 := by omega
  let W := D.fullModule.map (MulAut.conj g).toMonoidHom
  let K := A ⊓ centralizer (D.fullModule : Set G)
  let := m.fullModule_elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hKA : K ≤ A := inf_le_left
  have hAM : A ≤ D.maximalLocal := hAT.trans (le_normalizer_componentOrbit L T)
  have hcA : subgroupCorank A K ≤ 2 := by
    rw [← m.rank_maximalAction_image hAM]
    exact hrank
  have hcW : subgroupCorank W K ≤ 3 := by
    rw [offender_corank_add hKA hAW]
    omega
  have hrW : 3 < globalR W := by
    rw [globalR_map_equiv]
    exact hr
  have hCN : centralizer (K : Set G) ≤ normalizer (W : Set G) :=
    centralizer_le_normalizer_of_corank_lt_globalR (hKA.trans hAW)
      ((show (subgroupCorank W K : ℕ∞) ≤ 3 by exact_mod_cast hcW).trans_lt hrW)
  exact hnot ((le_centralizer_iff.mpr (show K ≤ centralizer (D.fullModule : Set G)
    from inf_le_right)).trans hCN)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
