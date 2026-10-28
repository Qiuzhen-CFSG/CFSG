module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import Theory.GroupAction.SylowPointwiseInner.Ambient
public import Theory.GroupAction.SylowPointwiseInnerTransport
public import Theory.SpecificGroups.BinaryLinear.SylowPointwiseInner
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.PointwiseFixer

/-!
# Inner markings of the actual linear component

The marked Sylow subgroup of X̂ restricts to a Sylow subgroup of K̂. The
PSL₂ and PSL₃ pointwise-fixer theorems, together with C_X̂(K̂)=1, put the
actual generator of V̂ in K̂. Its order, cyclic subgroup and Sylow
centralization are retained for subsequent field and residual exclusions.
No root marking or centerlessness of a covering SL₃ is assumed.

Source: Aschbacher–Smith, 13.5.21(i), printed pp.923–924.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields
open Configuration
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}
  (s : Selected D K) (h : D.Hypothesis) [(componentCentralizer s h).Normal]

/-- The actual marked involution inside the component, with an intrinsic
Sylow subgroup which it centralizes. -/
structure ComponentMarking where
  generator : Khat s h
  generates : zpowers (generator : Xhat s h) = Vhat s h
  order : orderOf generator = 2
  sylow : Sylow 2 (Khat s h)
  central : ∀ x ∈ sylow, x * generator = generator * x

private theorem marking_of_fixers (Y : Subgroup G)
    (p : Prefix s h Y)
    (fixers : ∀ (P : Sylow 2 (Khat s h)) (a : MulAut (Khat s h)),
      (∀ x ∈ P, a x = x) → ∃ z ∈ P, a = MulAut.conj z) :
    Nonempty (ComponentMarking s h) := by
  let : (Khat s h).Normal := p.khat_fitting ▸ inferInstance
  let : IsSimpleGroup (generalizedFitting (Xhat s h)) :=
    p.khat_fitting.symm ▸ p.khat_simple
  let : Group.IsPerfect (generalizedFitting (Xhat s h)) :=
    p.khat_fitting.symm ▸ Khat_perfect s h
  have hfaith : centralizer (Khat s h : Set (Xhat s h)) = ⊥ := by
    simpa only [p.khat_fitting] using SimpleSocle.centralizer_eq_bot
      (Group.IsPerfect.not_isMulCommutative (generalizedFitting (Xhat s h)))
  have hcyc : IsCyclic (Vhat s h) := isCyclic_of_prime_card p.actor_card
  obtain ⟨v, hv⟩ := (Vhat s h).isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  have hvV : v ∈ Vhat s h := hv ▸ mem_zpowers v
  obtain ⟨S, hS⟩ := p.marked_sylow
  have hc : ∀ x ∈ S, x * v = v * x := by
    intro x hx
    exact mem_centralizer_iff.mp (p.actor_central hvV) x (hS ▸ hx)
  have hvK := mem_normal_of_centralizes_sylow (Khat s h) hfaith fixers S v hc
  let vK : Khat s h := ⟨v, hvK⟩
  obtain ⟨P, _, hP⟩ := exists_sylow_centralized_of_ambient (Khat s h) S vK hc
  have ho : orderOf v = 2 := by rw [← Nat.card_zpowers, hv, p.actor_card]
  exact ⟨⟨vK, hv, (orderOf_injective (Khat s h).subtype Subtype.coe_injective vK).symm.trans ho,
    P, hP⟩⟩

/-- Sylow centrality forces the PSL₂ marking in the original quotient. -/
theorem source_linearTwo_marking (Y : Subgroup G) (p : Prefix s h Y)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (e : Khat s h ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    Nonempty (ComponentMarking s h) := by
  apply marking_of_fixers s h Y p
  exact MulAut.fixing_sylow_inner_of_equiv e Theory.PSL2.aut_fixing_sylow_inner

/-- The PSL₃ fixer calculation applies to K̂, leaving the cover untouched. -/
theorem source_linearThree_marking (Y : Subgroup G) (p : Prefix s h Y)
    (F : Type*) [Field F] [Finite F] {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n)
    (e : Khat s h ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :
    Nonempty (ComponentMarking s h) := by
  apply marking_of_fixers s h Y p
  intro P a ha
  obtain ⟨z, hz, he⟩ := Matrix.PSL3.LinearThree.exists_sylow_center_conj_of_equiv
    F hn hF e P a ha
  exact ⟨z, (map_subtype_le _ hz), he⟩

/-- The already binary B.4.2 linear-four and linear-five rows have the same
actual inner marking; no pair assumption is needed for these fixed fields. -/
theorem source_binaryHigher_marking (Y : Subgroup G) (p : Prefix s h Y)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : Khat s h ≃* Matrix.ProjectiveSpecialLinearGroup (Fin d) (ZMod 2)) :
    Nonempty (ComponentMarking s h) := by
  apply marking_of_fixers s h Y p
  exact MulAut.fixing_sylow_inner_of_equiv
    (e.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega)))
    (BinaryLinear.OuterCyclic.sylow_fixing_inner hd)

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields
