module
public import Theory.Representation.BinaryOffender.IrreducibleQuotientDiagonal
public import Theory.Representation.BinaryOffender.MinimalPlane
public import Theory.Representation.BinaryOffender.PerfectCentralizer
public import Theory.Representation.BinaryOffender.TwoPerfectPlane
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# A binary seed distinguishes a moved component

A two-perfect group acts irreducibly on any binary plane on which it acts
nontrivially. Thus the plane containing a minimal offender's displacement
lies in the entire moved module of its component. For an Irr⁺ moved module,
a distinct component centralizes this plane. A conjugate preserving the plane
would then make the original component centralize it too, contradicting
perfectness, faithfulness and the prescribed component commutator.

The final contradiction is proved on the quotient by the component's fixed
space; it does not assume the moved and fixed spaces are disjoint.
This provides a structural route to Aschbacher–Smith 13.7.15(3), retaining
the original two-dimensional seed and whole moved-module Irr⁺ hypothesis.
-/

public section
open Subgroup Theory.GroupTheory
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem moved_not_fixed_of_perfect_commutator {K A : Subgroup G} [Group.IsPerfect K]
    (hf : Function.Injective ρ) (hK : K ≠ ⊥) (hc : ⁅K,A⁆ = K) :
    ¬ subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ K := by
  intro hd
  let N := normalizer (K : Set G)
  let τ := normalizerQuotientRepresentation ρ K
  have hAN : A ≤ N := le_normalizer_iff_commutator_le_left.mpr hc.le
  have hcom : ⁅K.subgroupOf N,A.subgroupOf N⁆ = K.subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le K.le_normalizer,
      map_subgroupOf_eq_of_le hAN, hc]
  have hAfixed : (⊤ : Submodule (ZMod 2) (V ⧸ fixedSpace ρ K)) ≤
      fixedSpace τ (A.subgroupOf N) := by
    intro v _ a
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      apply (Submodule.Quotient.eq _).mpr
      exact hd (Submodule.subset_span ⟨a.val.val,a.property,v,Submodule.mem_top,rfl⟩)
  have hKfixed : (⊤ : Submodule (ZMod 2) (V ⧸ fixedSpace ρ K)) ≤
      fixedSpace τ (K.subgroupOf N) := by
    rw [← hcom]
    exact le_fixedSpace_commutator_of_invariant τ
      (le_subspaceStabilizer τ ⊤ (by intros; trivial)) hAfixed
  have hcentral : subspaceCommutator ρ ⊤ K ≤ fixedSpace ρ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,v,_,rfl⟩
    exact (Submodule.Quotient.eq _).mp
      (hKfixed (show (fixedSpace ρ K).mkQ v ∈ (⊤ : Submodule (ZMod 2) _) from Submodule.mem_top)
        ⟨⟨k,K.le_normalizer hk⟩,hk⟩)
  have hall := le_fixedSpace_of_commutator_le_fixedSpace ρ K ⊤
    (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hcentral
  apply hK
  apply bot_unique
  intro k hk
  change k=1
  apply hf
  apply LinearMap.ext
  intro v
  exact (hall Submodule.mem_top ⟨k,hk⟩).trans (by simp)

omit [Finite G] in
/-- Every nonzero invariant intersection fills a nontrivial two-perfect binary plane. -/
theorem twoPerfect_plane_le_of_intersection {J : Subgroup G} (hJ : IsPPerfect 2 J)
    (P D : Submodule (ZMod 2) V) (hP : J ≤ subspaceStabilizer ρ P)
    (hD : J ≤ subspaceStabilizer ρ D) (hd : Module.finrank (ZMod 2) P=2)
    (hn : ¬ P ≤ fixedSpace ρ J) (hw : ∃ w : V, w∈P ∧ w∈D ∧ w≠0) : P ≤ D := by
  by_contra hnot
  let I := P ⊓ D
  have hlt : I < P := lt_of_le_of_ne inf_le_left (by
    intro he
    exact hnot (he ▸ inf_le_right))
  have hdim : Module.finrank (ZMod 2) I ≤ 1 := by
    have hdim := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hI : J ≤ subspaceStabilizer ρ I := by
    apply le_subspaceStabilizer
    intro j hj v hv
    exact ⟨(hP hj v).2 hv.1,(hD hj v).2 hv.2⟩
  obtain ⟨w,hwP,hwD,hwn⟩ := hw
  let τ : Representation (ZMod 2) J I := Representation.subrepresentation (ρ.comp J.subtype) I
    (fun j v hv => (hI j.property v).2 hv)
  let : MulAction J I := {
    smul := fun j v => τ j v
    one_smul := fun v => by change τ 1 v=v; rw [map_one]; rfl
    mul_smul := fun j k v => by change τ (j*k) v=τ j (τ k v); rw [map_mul]; rfl }
  have hcard : Nat.card I ≤ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact (Nat.pow_le_pow_right (by decide : 0<2) hdim).trans_eq (by decide)
  let : Finite I := Module.finite_of_finite (ZMod 2)
  have hfix (j : J) : ρ j w=w := congrArg Subtype.val
    (MulAction.fixed_of_twoPerfect_of_card_le_two hJ hcard j (⟨w,hwP,hwD⟩ : I))
  let σ : Representation (ZMod 2) J P := Representation.subrepresentation (ρ.comp J.subtype) P
    (fun j v hv => (hP j.property v).2 hv)
  have hh := BinaryPlaneNormalizer.twoPerfect_plane_fixed σ hJ hd
    (⟨w,hwP⟩ : P) (fun he => hwn (congrArg Subtype.val he)) (fun j => Subtype.ext (hfix j))
  apply hn
  intro v hv j
  exact congrArg Subtype.val (LinearMap.congr_fun (hh j) (⟨v,hv⟩ : P))

/-- A marked nontrivial binary seed prevents its stabilizer from permuting
the component moved by a minimal plane offender. -/
theorem component_normalized_of_minimal_seed_plane
    (hf : Function.Injective ρ) {K B J S : Subgroup G}
    (hK : IsComponent G K) (hi : IsIrrPlus ρ K (subspaceCommutator ρ ⊤ K))
    (hB : IsMinimalBestOffender ρ B) (hc : ⁅K,B⁆=K)
    (hJ : IsPPerfect 2 J) (hJK : J ≤ normalizer (K : Set G))
    (P : Submodule (ZMod 2) V) (hP : J ≤ subspaceStabilizer ρ P)
    (hd : Module.finrank (ZMod 2) P=2) (hn : ¬ P ≤ fixedSpace ρ J)
    (hm : subspaceCommutator ρ ⊤ B ≤ P) (hSP : S ≤ subspaceStabilizer ρ P) :
    S ≤ normalizer (K : Set G) := by
  let : IsQuasisimple K := hK.2
  let W := subspaceCommutator ρ ⊤ K
  have hKn : K≠⊥ := by
    intro he
    apply hi.not_le_fixedSpace ρ
    rw [he]
    simp
  have hBK : subspaceCommutator ρ ⊤ B ≤ W := hB.moved_le_moved_perfect ρ hf hKn
    ((Submodule.finrank_mono hm).trans_eq hd) hc
  have hPW : P ≤ W := by
    apply twoPerfect_plane_le_of_intersection ρ hJ P W hP
      (subspaceCommutator_invariant_normalizer ρ
        (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hJK) hd hn
    have hnot := moved_not_fixed_of_perfect_commutator ρ hf hKn hc
    by_contra! hz
    apply hnot
    intro v hv
    rw [hz v (hm hv) (hBK hv)]
    exact (fixedSpace ρ K).zero_mem
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hne
  let C := K.map (MulAut.conj t).toMonoidHom
  have hC : IsComponent G C := hK.map_conj t
  let : IsQuasisimple C := hC.2
  have hCK : C ≤ centralizer (K : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hC.commutator_eq_bot_of_ne hK hne)
  have hCW : C ≤ subspaceStabilizer ρ W :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      (hCK.trans (centralizer_le_normalizer _))
  have hPC : P ≤ fixedSpace ρ C := hPW.trans (hi.le_fixedSpace_of_perfect_centralizes ρ hCK hCW)
  have hPK : P ≤ fixedSpace ρ K := by
    intro v hv k
    have htv : ρ t v ∈ P := (hSP ht v).2 hv
    have he := hPC htv ⟨t*k.val*t⁻¹,mem_map_of_mem (MulAut.conj t).toMonoidHom k.property⟩
    change ρ (t*k.val*t⁻¹) (ρ t v) = ρ t v at he
    have hh := congrArg (ρ t⁻¹) he
    change ρ k.val v = v
    simpa only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one, map_one, Module.End.one_apply] using hh
  exact (moved_not_fixed_of_perfect_commutator ρ hf hKn hc) (hm.trans hPK)
end Representation.BinaryOffender
