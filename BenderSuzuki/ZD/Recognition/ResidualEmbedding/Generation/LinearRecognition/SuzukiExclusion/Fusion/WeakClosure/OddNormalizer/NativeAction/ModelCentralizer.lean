module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.NativeAction.ModelCentralizer.RootTorus
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.NativeAction.CentralizerReduction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.LocalStructure.SuzukiBorel
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.LocalStructure.Normalizers

/-!
# The actual Suzuki pair-torus centralizer

Write L for the residual generated subgroup, D for the pair stabilizer,
K for the residual commutator and J = C_G(L). A Borel conjugation adjusts the
genuine Suzuki marking so that its root and split torus map to the local
two-core and K. Conjugation by an element of C_D(K) preserves that root and
fixes that torus pointwise. The intrinsic automorphism theorem makes it a
torus conjugation on L, so removing the torus factor leaves an element of J.
Thus C_D(K) ≤ KJ. The existing ambient reduction then gives
C_{N_G(S) ∩ D}(K) = KU from the source embedding J → L and |U| = 2.

Sources: GLS, Volume 4, Chapter 4, Lemma 3.2(e), and its application in
Chapter 2, Lemma 14.9; `refs/KGroup/GLS4/Chapter4.tex`, lines 360–373,
and `refs/KGroup/GLS4/Chapter2.tex`, lines 2600–2620.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- A genuine marking sends the standard root group to the local Borel
 two-core and the standard split torus to the literal residual commutator. -/
public theorem Context.suzuki_root_torus_marking (d : Context Z M z t m) :
    ∃ e : SuzukiMatrixGroup m ≃* residualGenerated M z t,
      let φ := (residualGenerated M z t).subtype.comp e.toMonoidHom
      (SuzukiRootSubgroup m).map φ = borelTwoCore M z t ∧
      (SuzukiSplitTorus m).map φ = residualCommutator M t := by
  obtain ⟨f, u, hft, hu, huB, hB, hU, hE⟩ := residualGenerated_suzuki_pair_marking
    d.minimal.disconnected d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper d.parameter_pos d.model
  obtain ⟨b, hb, hbu⟩ := suzukiBorel_conj_weyl m d.parameter_pos u hu huB
  have hbU : (SuzukiRootSubgroup m).map (MulAut.conj b).toMonoidHom =
      SuzukiRootSubgroup m := mem_normalizer_iff_map_conj_eq.mp
        (show b ∈ normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) by
          rwa [suzukiRootSubgroup_normalizer m d.parameter_pos])
  refine ⟨(MulAut.conj b).trans f, ?_, ?_⟩
  · change (SuzukiRootSubgroup m).map
        (((residualGenerated M z t).subtype.comp f.toMonoidHom).comp
          (MulAut.conj b).toMonoidHom) = _
    rw [← map_map, hbU]
    exact hU
  · change (SuzukiSplitTorus m).map
        (((residualGenerated M z t).subtype.comp f.toMonoidHom).comp
          (MulAut.conj b).toMonoidHom) = _
    rw [← map_map, ← suzukiBorel_pair_eq_map m d.parameter_pos b u hb hbu,
      hE, d.torus_eq_local_pair]

/-- GLS4, Chapter 4, Lemma 3.2(e), in the source Suzuki context:
`C_D(K) ≤ K C_G(L)`, with the literal pair stabilizer and residual torus. -/
public theorem Context.pair_torus_centralizer_le (d : Context Z M z t m) :
    residualPairStabilizer M t ⊓ centralizer (residualCommutator M t : Set G) ≤
      residualCommutator M t ⊔ centralizer (residualGenerated M z t : Set G) := by
  obtain ⟨e, hU, hT⟩ := d.suzuki_root_torus_marking
  let L := residualGenerated M z t
  let φ := L.subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.injective
  change (SuzukiRootSubgroup m).map φ = borelTwoCore M z t at hU
  change (SuzukiSplitTorus m).map φ = residualCommutator M t at hT
  intro x hx
  let a := L.normalizerMonoidHom ⟨x, d.pair_le_residual_normalizer hx.1⟩
  let α : MulAut (SuzukiMatrixGroup m) := (e.trans a).trans e.symm
  have hα (v : SuzukiMatrixGroup m) : φ (α v) = x * φ v * x⁻¹ := by
    change ((e (e.symm (a (e v)))) : G) = _
    rw [e.apply_symm_apply]
    rfl
  have hroot : (SuzukiRootSubgroup m).map α.toMonoidHom = SuzukiRootSubgroup m := by
    apply eq_of_le_of_card_ge
    · rintro y ⟨v, hv, rfl⟩
      have hvP : φ v ∈ borelTwoCore M z t := hU ▸ mem_map_of_mem φ hv
      have hxP : x ∈ normalizer (borelTwoCore M z t : Set G) :=
        residual_pair_le_normalizer_borel_twoCore d.pair_le_residual_normalizer hx.1
      have hh : φ (α v) ∈ borelTwoCore M z t := by
        rw [hα]
        exact (mem_normalizer_iff.mp hxP _).mp hvP
      rw [← hU] at hh
      obtain ⟨w, hw, heq⟩ := hh
      exact hφ heq ▸ hw
    · rw [card_map_of_injective α.injective]
  have hfix (v : SuzukiMatrixGroup m) (hv : v ∈ SuzukiSplitTorus m) : α v = v := by
    apply hφ
    rw [hα]
    have hvK : φ v ∈ residualCommutator M t := hT ▸ mem_map_of_mem φ hv
    exact mul_inv_eq_iff_eq_mul.mpr (hx.2 _ hvK).symm
  obtain ⟨s, hs⟩ := suzukiAut_eq_torus_conj_of_root_preserving_torus_fixed m d.parameter_pos α hroot hfix
  have hsK : φ s ∈ residualCommutator M t := hT ▸ mem_map_of_mem φ s.property
  have hj : (φ s)⁻¹ * x ∈ centralizer (L : Set G) := by
    intro v hv
    obtain ⟨w, hw⟩ := e.surjective (⟨v, hv⟩ : L)
    have hwv : φ w = v := congrArg Subtype.val hw
    have heq := hα w
    rw [hs, MulAut.conj_apply, map_mul, map_mul, map_inv, hwv] at heq
    calc
      v * ((φ s)⁻¹ * x) = (φ s)⁻¹ * (φ s * v * (φ s)⁻¹) * x := by group
      _ = (φ s)⁻¹ * (x * v * x⁻¹) * x := by rw [heq]
      _ = (φ s)⁻¹ * x * v := by group
  have hh := mul_mem_sup hsK hj
  simpa only [mul_inv_cancel_left] using hh

namespace OddNormalizer

/-- The unconditional model application in GLS4, Chapter 2, Lemma 14.9:
`C_{N_G(S) ∩ D}(K) = KU`. The embedding and order-two hypotheses are the
source local inputs; no automorphism-centralizer premise remains. -/
public theorem normalizer_pair_torus_centralizer
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (hU : Nat.card g.U = 2) :
    (normalizer (g.S : Set G) ⊓ residualPairStabilizer M t) ⊓
      centralizer (residualCommutator M t : Set G) = residualCommutator M t ⊔ g.U :=
  normalizer_pair_torus_centralizer_of_model d g s f hf hU d.pair_torus_centralizer_le

end OddNormalizer
end BenderSuzuki.ZD.SuzukiExclusion
