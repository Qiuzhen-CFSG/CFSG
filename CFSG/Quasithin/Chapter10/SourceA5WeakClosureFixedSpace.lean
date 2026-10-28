module
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosureLowerBound
public import CFSG.Quasithin.ChapterE.Section03.Parameters.UniformOutsideFixed

/-!
# The fixed-space inequality for the literal original A₅ offender

The source's identity (*) says that every actor outside the conjugated
component-fixed subgroup has the common fixed space of A_i. With A_i
normalizing W and acting nontrivially, the actual image Aut_(A_i)(W)
therefore lies in the (4-k)-th fixed-space family of Aut_M(W).
The lower bound |W:C_W(L)|≥16 and the original offender corank≤k
supply the entire index calculation.

This isolates the remaining source geometry honestly: normalization,
nontriviality of the chosen factor action, and (*) are explicit. The
model-specific moduleA bound must be supplied on the same full local
automizer; identifying its abstract A₅ component is insufficient.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
10.2.12, the argument ending at (*) on p.754 and its use on p.755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- The exact source index calculation behind membership in A_(4-k). -/
theorem source_a5_offender_factor_fixed_index
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (g : G) {k : ℕ} (hk : k ≤ 2)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ k) :
    2 ^ (4-k) ≤ (centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)).relIndex
      ((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) := by
  let V := D.fullModule.map (MulAut.conj g).toMonoidHom
  let W := (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom
  let A := W ⊓ D.maximalLocal
  let C := centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  have hidx (P Q : Subgroup G) : P.relIndex Q ≠ 0 := by
    change Nat.card (Q ⧸ P.subgroupOf Q) ≠ 0
    exact Nat.card_ne_zero.mpr ⟨inferInstance,inferInstance⟩
  have hLV : L ≤ normalizer (D.fullModule : Set G) :=
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  have hWV : W ≤ V := map_mono (le_normalizer_iff_commutator_le_left.mp hLV)
  have hMV : D.maximalLocal.relIndex V ≤ 2^k := by
    have he : D.maximalLocal.relIndex V = 2 ^ subgroupCorank V (V ⊓ D.maximalLocal) := by
      rw [subgroupCorank_eq_quotient_finrank, relIndex_eq_two_pow_quotient_finrank V D.maximalLocal]
      congr 1
      rw [inf_subgroupOf_left]
    rw [he]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hsmall
  have hAW : A.relIndex W ≤ 2^k := by
    rw [show A = W ⊓ D.maximalLocal from rfl, inf_relIndex_left]
    exact (relIndex_le_of_le_right hWV (hidx _ _)).trans hMV
  have hCW : 16 ≤ C.relIndex W := source_a5_conjugate_full_moved_fixed_quotient_card D e g
  have hmul := relIndex_inf_mul_relIndex C A W
  rw [inf_of_le_left (show A ≤ W from inf_le_left)] at hmul
  have hprod : 16 ≤ C.relIndex A * A.relIndex W :=
    hCW.trans ((relIndex_le_of_le_left (show C ⊓ A ≤ C from inf_le_left) (hidx _ _)).trans_eq hmul.symm)
  have hb : 16 ≤ C.relIndex A * 2^k := hprod.trans (Nat.mul_le_mul_left _ hAW)
  change 2^(4-k) ≤ C.relIndex A
  interval_cases k <;> norm_num at hb ⊢ <;> omega

/-- The source's actual fixed-space identity supplies the lower parameter bound.
All index, elementary-abelian and automizer-image premises are discharged here. -/
theorem source_a5_offender_local_moduleA_lower
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (g : G) {k : ℕ} (hk : k ≤ 2)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ k) :
    let W := ⁅D.fullModule,L⁆
    let A := W.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal
    let C := centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)
    let _ := source_full_moved_elementary D
    A ≤ normalizer (W : Set G) → ¬ A ≤ centralizer (W : Set G) →
    (∀ a ∈ A, a ∉ C → W ⊓ centralizer ({a} : Set G) ≤ centralizer (A : Set G)) →
    ((4-k : ℕ) : ℕ∞) ≤ moduleA
      ((automizerRepresentation W).comp (inducedAutomizer W D.maximalLocal).subtype) := by
  dsimp only
  let W := ⁅D.fullModule,L⁆
  let A := W.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal
  let C := centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)
  let := source_full_moved_elementary D
  let : IsElementaryAbelian 2 (W.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := offender_elementary_of_le (show A ≤ W.map (MulAut.conj g).toMonoidHom from inf_le_left)
  intro hAN hactive hfix
  exact moduleA_localAutomizer_ge_of_uniform_outside W A C D.maximalLocal hAN inf_le_right
    hactive (by omega) (source_a5_offender_factor_fixed_index D e g hk hsmall) hfix

end CFSG.Quasithin.Chapter10
