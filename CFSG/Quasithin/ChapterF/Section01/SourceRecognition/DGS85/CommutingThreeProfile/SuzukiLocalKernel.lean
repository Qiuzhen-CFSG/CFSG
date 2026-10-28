module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CoreGeneration
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CoreGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.KernelControl
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import BenderSuzuki.MatrixGroups.SuzukiZero
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The full local kernel inside a Suzuki starred endpoint

The literal base-neighbor stabilizer in the starred group is its Sylow
normalizer. Its normal subgroup in the full radius-one kernel therefore
maps to a normal subgroup of the Suzuki quotient inside a proper Sylow
normalizer. For q > 2 simplicity kills this image. For Sz(2), divisibility
by five would force the normalizer to have order twenty; the image is
therefore a normal two-subgroup and vanishes in the two-core quotient.

Consequently the intersection of the starred endpoint with the full
radius-one kernel is exactly the embedded vertex two-core. The full
kernel itself is not identified with that core. Combined with source
(8.1)(c), this gives exact core control of the action on the actual center
span, used in the literal quotient action in (12.6).

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(6.1), (8.1)(c), and (12.5)--(12.6), printed pp.118,133,182--183.
The Suzuki marking remains the separate (12.5) selection obligation.
The implementation import reuses the base Sylow-normalizer identification
within this source family without changing its public interface.
-/

@[expose] public noncomputable section
open Subgroup
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile

private theorem suzuki_normal_in_normalizer
    {A : Type*} [Group A] [Finite A] {m : ℕ}
    (e : (A ⧸ pCore 2 A) ≃* SuzukiMatrixGroup m)
    (T : Sylow 2 (SuzukiMatrixGroup m))
    (N : Subgroup (SuzukiMatrixGroup m)) [N.Normal]
    (hN : N ≤ normalizer (T : Set (SuzukiMatrixGroup m))) : N = ⊥ := by
  have hp : normalizer (T : Set (SuzukiMatrixGroup m)) < ⊤ :=
    (suzuki_rankOneSylowFacts m T).proper
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h5 : ¬ 5 ∣ Nat.card N := by
      intro h5
      have h4 : 4 ∣ Nat.card (normalizer (T : Set (SuzukiMatrixGroup 0))) :=
        (T.pow_dvd_card_of_pow_dvd_card (n := 2) (by rw [suzukiZero_card]; decide)).trans
          (card_dvd_of_le (le_normalizer (H := (T : Subgroup (SuzukiMatrixGroup 0)))))
      have h20 : 20 ∣ Nat.card (normalizer (T : Set (SuzukiMatrixGroup 0))) :=
        (by decide : Nat.Coprime 4 5).mul_dvd_of_dvd_of_dvd h4
          (h5.trans (card_dvd_of_le hN))
      have he : normalizer (T : Set (SuzukiMatrixGroup 0)) = ⊤ :=
        eq_of_le_of_card_ge le_top (by
          rw [Nat.card_congr (topEquiv : (⊤ : Subgroup (SuzukiMatrixGroup 0)) ≃* _).toEquiv,
            suzukiZero_card]
          exact Nat.le_of_dvd Nat.card_pos h20)
      exact hp.ne he
    have hn : IsPGroup 2 N := IsPGroup.of_card_dvd_pow (n := 2)
      (((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h5).symm.dvd_of_dvd_mul_right
        (show Nat.card N ∣ 2^2 * 5 by simpa [suzukiZero_card] using N.card_subgroup_dvd_card))
    have hcore : pCore 2 (SuzukiMatrixGroup 0) = ⊥ := by
      rw [← pCore_map_iso 2 e, pCore_quotient_pCore_eq_bot, Subgroup.map_bot]
    exact bot_unique ((le_sSup ⟨inferInstance, hn⟩ : N ≤ pCore 2 _).trans hcore.le)
  · let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
    exact (inferInstance : N.Normal).eq_bot_or_eq_top.resolve_right
      (fun he => hp.not_ge (he ▸ hN))

open Subgroup.CosetGeometry.RankTwo Reduction Theory.GroupTheory.AmalgamGraph
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- In the Suzuki row, only the vertex two-core of the star fixes all neighbors. -/
theorem source_suzuki_star_kernel (h : HypothesisF11 L S) (i : Bool) {m : ℕ}
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup m) :
    star L S i ⊓ U (reducedFamily L S) (base (reducedFamily L S) i) =
      Q (reducedFamily L S) (base (reducedFamily L S) i) := by
  let F := reducedFamily L S
  let A := star L S i
  let v := base F i
  let w := base F (!i)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer i))
    (inclusion_injective _)
  have hadj : (graph F).Adj v w :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  let eA := (originalQuotient h i).symm.trans e
  let f := eA.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := eA.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 A := by
    ext x
    change eA (QuotientGroup.mk' (pCore 2 A) x) = 1 ↔ _
    rw [map_eq_one_iff _ eA.injective]
    exact QuotientGroup.eq_one_iff x
  let N := (U F v).subgroupOf A
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    ((star_le_stabilizer i).trans (stabilizer_le_normalizer_ballKernel F v 1))
  obtain ⟨T,hT⟩ := base_star_sylow_normalizer h i
  let R := T.mapSurjective hf
  have hRT : (R : Subgroup (SuzukiMatrixGroup m)).comap f = (T : Subgroup A) := by
    apply comap_map_eq_self
    rw [hk]
    exact pCore_isPGroup.le_sylow_of_normal T
  have hN : N ≤ normalizer (T : Set A) := by
    rw [←hT]
    exact comap_mono ((ballKernel_one_le_edge F hadj).trans inf_le_right)
  have him : N.map f ≤ normalizer (R : Set (SuzukiMatrixGroup m)) := by
    apply map_le_iff_le_comap.mpr
    change N ≤ (normalizer ((R : Subgroup (SuzukiMatrixGroup m)) : Set _)).comap f
    rw [comap_normalizer_eq_of_surjective _ hf, hRT]
    exact hN
  let : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hbot := suzuki_normal_in_normalizer eA R (N.map f) him
  have hncore : N ≤ pCore 2 A := by
    rw [←hk]
    exact (Subgroup.map_eq_bot_iff _).mp hbot
  apply le_antisymm
  · intro x hx
    rw [←star_core h i]
    exact mem_map_of_mem A.subtype (hncore (show (⟨x,hx.1⟩ : A) ∈ N from hx.2))
  · exact le_inf ((star_core h i).symm ▸ pCoreIn_le 2 A)
      (source_Z_Q_U (reduced_triple h) v).2

/-- The actual span centralizer in the star lies in its intrinsic two-core.
This applies to both the nonbinary Suzuki groups and Sz(2). -/
theorem source_suzuki_span_centralizer_le_core (h : HypothesisF11 L S) (i : Bool) {m : ℕ}
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup m) :
    (centralizer (V (reducedFamily L S) (base (reducedFamily L S) i) 1 :
      Set (G₀ L S))).subgroupOf (star L S i) ≤ pCore 2 (star L S i) := by
  let F := reducedFamily L S
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  intro a ha
  have hU : (a : G₀ L S) ∈ U F (base F i) :=
    CommutingNontrivial.source_span_centralizer_le_kernel (reduced_triple h) hadj
      ⟨star_le_stabilizer i a.property,ha⟩
  have hQ : (a : G₀ L S) ∈ Q F (base F i) :=
    (source_suzuki_star_kernel h i e).le ⟨a.property,hU⟩
  rw [←star_core h i] at hQ
  obtain ⟨b,hb,he⟩ := hQ
  exact (show b = a from Subtype.ext he) ▸ hb

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
