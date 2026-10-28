module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Sections
public import Theory.GroupTheory.PCoreImage
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional.Action
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The point-image kernel is central modulo the original two-core

An actor in L fixing V₁ and V/V₁ is a two-element: its natural action is
a shear whose square is the identity, and the kernel of the full natural
action is O₂(L). Thus the point-image kernel N meets L₁ in a two-group.
The preceding normalizer calculation makes N∩L₁ normal in N; relative
normality then puts it in O₂(K). The resulting commutator bound with L₁
propagates through its original G₁-conjugate span to all of K.

The special-structure identity C_U(L₁)=Z(U) supplies point fixation,
since G.2 puts V₁ in Z(U). This proves C_K(Ũ)≤O₂,Z(K) without a kernel
premise, model-family tag, or replacement of the solvable residual.
Source: Aschbacher--Smith 11.5.7, refs/quasithin.pdf, printed p.782.
-/

public noncomputable section
open Subgroup Matrix
open scoped commutatorElement
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
include d

set_option backward.isDefEq.respectTransparency false in

/-- A subgroup of L fixing V₁ and V/V₁ is a two-group. -/
theorem isPGroup_of_point_shear (A : Subgroup G) (hAL : A ≤ L)
    (hfix : A ≤ centralizer (E.V₁ : Set G))
    (hshear : ∀ a ∈ A, ∀ v ∈ V, ⁅a,v⁆ ∈ E.V₁) : IsPGroup 2 A := by
  let f : A →* (setup E).star L := (starProjection (setup E)).comp (inclusion hAL)
  have hker : IsPGroup 2 f.ker := by
    have he : f.ker = (pCore 2 L).comap (inclusion hAL) := by
      rw [show f = (starProjection (setup E)).comp (inclusion hAL) from rfl,
        ← MonoidHom.comap_ker,starProjection_ker E]
    rw [he]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  intro a
  have hsq : a ^ 2 ∈ f.ker := by
    apply MonoidHom.mem_ker.mpr
    apply d.model.injective
    rw [map_one]
    apply Matrix.SpecialLinearGroup.toLin'_injective
    rw [map_one]
    ext w : 1
    obtain ⟨v,rfl⟩ := d.coordinates.surjective (Multiplicative.ofAdd w)
    let l : L := inclusion hAL a
    change (d.model (starProjection (setup E) (l ^ 2))).val *ᵥ (d.coordinates v).toAdd =
      (d.coordinates v).toAdd
    rw [← d.equivariant (l ^ 2) v]
    congr 2
    apply Subtype.ext
    change (a : G) ^ 2 * (v : G) * ((a : G) ^ 2)⁻¹ = (v : G)
    let c : G := ⁅(a : G),(v : G)⁆
    have hc : c ∈ E.V₁ := hshear a a.property v v.property
    have hcc : c * (a : G) = (a : G) * c := hfix a.property c hc
    have hc2 : c * c = 1 := by
      let := D.elementary
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) c (E.V₁_le hc)
    have hcv : c * (v : G) = (a : G) * (v : G) * (a : G)⁻¹ := by
      dsimp [c]
      rw [commutatorElement_def]
      group
    calc
      _ = (a : G) * ((a : G) * (v : G) * (a : G)⁻¹) * (a : G)⁻¹ := by
        simp only [pow_two,_root_.mul_inv_rev]
        group
      _ = (a : G) * (c * (v : G)) * (a : G)⁻¹ := by rw [hcv]
      _ = c * ((a : G) * (v : G) * (a : G)⁻¹) := by rw [← mul_assoc,← hcc]; group
      _ = c * (c * (v : G)) := by rw [hcv]
      _ = (v : G) := by rw [← mul_assoc,hc2,one_mul]
  obtain ⟨n,hn⟩ := hker ⟨a ^ 2,hsq⟩
  refine ⟨n+1,?_⟩
  have hn' : (a ^ 2) ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  rw [pow_succ,Nat.mul_comm,pow_mul]
  exact hn'


/-- The original point-image kernel is central modulo O₂(K). -/
theorem pointAction_kernel_le_coreCentral
    (hfix : E.L₁ ≤ centralizer (E.V₁ : Set G)) :
    (pointAction E).ker ≤ centralPreimage (pCore 2 E.K) := by
  let N := (pointAction E).ker.map E.K.subtype
  have hNK : N ≤ E.K := map_subtype_le _
  have hGN : E.G₁ ≤ normalizer (N : Set G) := pointAction_kernel_normalized E
  have hKN : E.K ≤ normalizer (N : Set G) := E.K_le_G₁.trans hGN
  have hNL : N ≤ normalizer (E.L₁ : Set G) := pointAction_kernel_normalizes_residual E
  have hA : IsPGroup 2 (N ⊓ E.L₁ : Subgroup G) := by
    apply isPGroup_of_point_shear E d _ (inf_le_right.trans E.L₁_le)
      (inf_le_right.trans hfix)
    intro a ha v hv
    obtain ⟨k,hk,rfl⟩ := ha.1
    exact (mem_pointAction_kernel_iff E k).mp hk v
      (le_conjugateSpanBy V E.G₁ hv)
  have hbound : N ⊓ E.L₁ ≤ E.K.pCoreIn 2 :=
    (le_pCoreIn_of_normalizes hA inf_le_left
      ((le_inf N.le_normalizer hNL).trans inf_normalizer_le_normalizer_inf)).trans
        (pCoreIn_mono_of_normalizes hNK hKN)
  have hc : ⁅E.L₁,N⁆ ≤ E.K.pCoreIn 2 :=
    (le_inf
      (le_normalizer_iff_commutator_le_right.mp ((pointResidual_le_K E).trans hKN))
      (le_normalizer_iff_commutator_le_left.mp hNL)).trans hbound
  have hGQ : E.G₁ ≤ normalizer (E.K.pCoreIn 2 : Set G) :=
    E.G₁_normalizes_K.trans (normalizer_le_normalizer_characteristic_image E.K (pCore 2 E.K))
  have hKQ := E.K_le_G₁.trans hGQ
  have hspan : E.K ≤ commutatorPreimage E.K N (E.K.pCoreIn 2) :=
    conjugateSpanBy_le (le_commutatorPreimage (pointResidual_le_K E) hc)
      (commutatorPreimage_normalized E.K N (E.K.pCoreIn 2) E.G₁ hKQ
        E.G₁_normalizes_K hGN hGQ)
  have hcomm : ⁅E.K,N⁆ ≤ E.K.pCoreIn 2 :=
    (commutator_mono hspan le_rfl).trans
      (commutator_commutatorPreimage_le E.K N (E.K.pCoreIn 2) hKQ)
  intro k hk
  apply mem_center_iff.mpr
  intro a
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 E.K) a
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← map_commutatorElement]
  apply (QuotientGroup.eq_one_iff _).mpr
  obtain ⟨c,hc,he⟩ := hcomm (commutator_mem_commutator a.property
    (mem_map_of_mem E.K.subtype hk))
  exact (Subtype.ext he : c = ⁅a,k⁆) ▸ hc

/-- The point is central in the closure, using the marked G.2 setup. -/
theorem point_le_closureCenter : E.V₁ ≤ closureCenter E := by
  intro v hv
  refine ⟨⟨v,Outside.point_le_closure E hv⟩,?_,rfl⟩
  apply mem_center_iff.mpr
  intro u
  apply Subtype.ext
  exact (d.setup.toBaseHypothesis.U_le_centralizer_point u.property v hv).symm

/-- The special-structure fixed-space equality supplies the point fixation
needed for the original action kernel bound. -/
theorem pointAction_kernel_le_of_special_fixed
    (hfixed : E.W ⊓ centralizer (E.L₁ : Set G) = closureCenter E) :
    (pointAction E).ker ≤ centralPreimage (pCore 2 E.K) := by
  apply pointAction_kernel_le_coreCentral E d
  apply le_centralizer_iff.mp
  exact ((point_le_closureCenter E d).trans_eq hfixed.symm).trans inf_le_right

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional
