module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityKernelHigher
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Sylow

/-!
# The central-factor bound in dimensions four and five

The marked action of L carries its actual Sylow intersection to a linear
Sylow. Its fixed space is one binary line, so |C_V(T)| ≤ 2. The literal
kernel decomposition then puts C_T(I) and C_T(L) in C_V(T)C_T(L).
They are disjoint and have the same order; counting their product gives
|C_T(L)| ≤ 2. This supplies the cardinality field of 12.2.25 in the
higher-dimensional branch, without a Sylow-factor disjointness premise.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
original 12.2.25, printed p.805. The common-centralizers owner retains the
dimension-three branch, Sylow disjointness and Thompson normalization;
qt-d-12213-local-rigidity owns final source-theorem assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}
namespace RigidityKernel

private theorem component_sylow (D : ChosenModule T L V) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup G).subgroupOf L := by
  let J := L ⊔ (T : Subgroup G)
  have hLJ : L ≤ J := le_sup_left
  let : (L.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  obtain ⟨S,hS⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal
    (L.subgroupOf J)
  let e := subgroupOfEquivOfLe hLJ
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (S : Subgroup _).map e.toMonoidHom = _
  rw [hS]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨⟨x,hLJ x.property⟩,x.property⟩,hx,rfl⟩

/-- The original Sylow fixes at most one binary line in the marked module. -/
theorem chosen_sylow_fixed_card
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d) :
    Nat.card ↥(V ⊓ centralizer (T : Set G)) ≤ 2 := by
  obtain ⟨e,f,hf⟩ := A.natural
  obtain ⟨S,hS⟩ := component_sylow D
  let a := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let b := (BinaryLinear.OuterCyclic.slEquivLinear d).toMonoidHom.comp a
  have ha : Function.Surjective a := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hb : Function.Surjective b := (BinaryLinear.OuterCyclic.slEquivLinear d).surjective.comp ha
  let B := S.mapSurjective (f := b) hb
  obtain ⟨x,hx,hfixed⟩ := BinaryNaturalDual.VectorStabilizers.Pure.linear_sylow_fixed_line
    (V := Fin d → ZMod 2) (by simpa using (show 0 < d by have := A.dimension; omega)) B
  let F := V ⊓ centralizer (T : Set G)
  have hmem (v : F) : (f ⟨v,v.property.1⟩).toAdd ∈ BinaryLinear.fixedSpace (B : Subgroup (BinaryLinear.GL (Fin d → ZMod 2))) := by
    intro g hg
    obtain ⟨l,hl,rfl⟩ := hg
    have hlT : (l : G) ∈ (T : Subgroup G) := by
      have hh : l ∈ (T : Subgroup G).subgroupOf L := hS ▸ hl
      exact hh
    have hcomm : (l : G) * (v : G) * (l : G)⁻¹ = v := by
      rw [v.property.2 l hlT, mul_inv_cancel_right]
    have hh := hf l (⟨v,v.property.1⟩ : V)
    rw [hcomm] at hh
    have hs : f.symm (Multiplicative.ofAdd
        (Representation.specialLinearNatural d (a l) (f ⟨v,v.property.1⟩).toAdd)) =
        (⟨v,v.property.1⟩ : V) := Subtype.ext hh
    have hh' := congrArg (fun w : V => (f w).toAdd) hs
    simpa [b, a, BinaryLinear.OuterCyclic.slEquivLinear_apply,
      Representation.specialLinearNatural_apply] using hh'
  let j : F → BinaryLinear.fixedSpace (B : Subgroup (BinaryLinear.GL (Fin d → ZMod 2))) := fun v => ⟨(f ⟨v,v.property.1⟩).toAdd,hmem v⟩
  have hj : Function.Injective j := by
    intro v w hvw
    have he := congrArg (fun z : BinaryLinear.fixedSpace (B : Subgroup (BinaryLinear.GL (Fin d → ZMod 2))) => Multiplicative.ofAdd z.val) hvw
    exact Subtype.ext (congrArg (fun y : V => (y : G)) (f.injective he))
  have hc : Nat.card (BinaryLinear.fixedSpace (B : Subgroup (BinaryLinear.GL (Fin d → ZMod 2)))) = 2 := by
    rw [hfixed, Module.natCard_eq_pow_finrank (K := ZMod 2),
      finrank_span_singleton hx, Nat.card_zmod, pow_one]
  exact (Nat.card_le_card_of_injective j hj).trans hc.le

/-- The source's order-two bound for the two common central factors in the
higher-dimensional branch. -/
theorem higher_component_centralizer_card
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 4 ≤ d) :
    Nat.card ↥((T : Subgroup G) ⊓ centralizer (L : Set G)) ≤ 2 := by
  let E := (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let F := V ⊓ centralizer (T : Set G)
  have hZT : Z ≤ centralizer (T : Set G) := higher_component_centralizer_central h D structural A C hnone hd
  have hET : E ≤ centralizer (T : Set G) := higher_pair_centralizer_central h D structural A C hnone hd
  have hEZ : Disjoint E Z := disjoint_iff.mpr (by rw [inf_comm]; exact common_trivial h D C)
  have hFZ : Disjoint F Z := (kernel_disjoint D A).mono_left inf_le_left
  have hZE : Z ≤ normalizer (E : Set G) :=
    ((le_centralizer_iff.mp hET).trans' inf_le_left).trans (Subgroup.centralizer_le_normalizer _)
  have hZF : Z ≤ normalizer (F : Set G) :=
    (le_centralizer_iff.mp ((inf_le_left.trans D.le_sylow).trans (le_centralizer_iff.mp hZT))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hEQ : E ≤ (T : Subgroup G) ⊓ centralizer (V : Set G) :=
    le_inf inf_le_left (hET.trans (centralizer_le D.le_sylow))
  have hEZF : E ≤ Z ⊔ F := by
    have hh : E ≤ (Z ⊔ V) ⊓ centralizer (T : Set G) := by
      rw [sup_comm Z V, ← higher_kernel_split D A C hd]
      exact le_inf hEQ hET
    change E ≤ (Z ⊔ V) ⊓ centralizer (((T : Subgroup G) : Set G)) at hh
    rwa [inf_centralizer_sup_of_centralizing Z V (T : Subgroup G)
      (hZT.trans (centralizer_le D.le_sylow) |>.trans (Subgroup.centralizer_le_normalizer _)) hZT] at hh
  have hcard : Nat.card E * Nat.card Z ≤ Nat.card F * Nat.card Z := by
    rw [← card_sup_eq_mul_of_normalizes_of_disjoint E Z hZE hEZ,
      ← card_sup_eq_mul_of_normalizes_of_disjoint F Z hZF hFZ]
    have hi : E ⊔ Z ≤ F ⊔ Z := sup_le (hEZF.trans_eq (sup_comm Z F)) le_sup_right
    exact Nat.card_le_card_of_injective (inclusion hi) (inclusion_injective hi)
  have he : Nat.card E ≤ Nat.card F := Nat.le_of_mul_le_mul_right hcard Nat.card_pos
  rw [higher_central_factors_card h D structural A C hnone hd]
  exact he.trans (chosen_sylow_fixed_card D A)

end RigidityKernel
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
