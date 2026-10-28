module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.NativeAction.Construction
public import Theory.SpecificGroups.Suzuki.RankOneRoots
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The ambient centralizer reduction for the Suzuki odd normalizer

The genuine embedding J → L ≃ Sz(q) places the centralizer of the
nonidentity element of U in a two-group. Since |U| = 2, its normalizer
centralizes it; Sylow maximality therefore gives N_J(U) = U. Intersecting
S with J then gives N_G(S) ∩ J = U.

Consequently the source model inclusion C_D(K) ≤ KJ implies the literal
identity C_{N∩D}(K) = KU. That automorphism-theoretic model inclusion remains
an explicit premise, and is not inferred from an outer-order bound.
Source: GLS4, Chapter 2, Lemma 14.9 and Chapter 4, Lemma 3.2(e),
refs/KGroup/GLS4/Chapter2.tex and Chapter4.tex.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion.OddNormalizer
open Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- The order-two Sylow subgroup is self-normalizing in the actual centralizer J. -/
public theorem centralizer_inf_normalizer_U (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (hU : Nat.card g.U = 2) :
    centralizer (residualGenerated M z t : Set G) ⊓ normalizer (g.U : Set G) = g.U := by
  let J := centralizer (residualGenerated M z t : Set G)
  let φ := d.model.toMonoidHom.comp f
  have hφ : Function.Injective φ := d.model.injective.comp hf
  have hne : g.U ≠ ⊥ := (one_lt_card_iff_ne_bot _).mp (by omega)
  obtain ⟨u, hu, hu1⟩ := g.U.bot_or_exists_ne_one.resolve_left hne
  let uJ : J := ⟨u, g.U_le_centralizer hu⟩
  have hu2 : uJ ^ 2 = 1 := by
    apply Subtype.ext
    have h := pow_card_eq_one' (x := (⟨u, hu⟩ : g.U))
    rw [hU] at h
    change u ^ 2 = 1
    exact congrArg (fun a : g.U => (a : G)) h
  have huφ : orderOf (φ uJ) = 2 := orderOf_eq_prime (by rw [← map_pow, hu2, map_one])
    (fun h => hu1 (congrArg Subtype.val (hφ (h.trans (map_one φ).symm))))
  obtain ⟨_, _, _, _, _, hC⟩ := suzuki_involution_root_geometry m
    (by have := d.parameter_pos; omega) (φ uJ) huφ
  have hCJ : IsPGroup 2 (centralizer ({uJ} : Set J)) := by
    have hle : centralizer ({uJ} : Set J) ≤ (centralizer ({φ uJ} : Set (SuzukiMatrixGroup m))).comap φ := by
      intro x hx
      exact mem_centralizer_singleton_iff.mpr
        ((show Commute x uJ from mem_centralizer_singleton_iff.mp hx).map φ).eq
    exact (hC.comap_of_injective φ hφ).to_le hle
  let R := (normalizer (g.U : Set G)).subgroupOf J
  have hR : IsPGroup 2 R := hCJ.to_le (by
    intro x hx
    have hc := normalizer_le_centralizer_of_card_two g.U hU hx
    exact mem_centralizer_singleton_iff.mpr
      (Subtype.ext (hc u hu).symm))
  obtain ⟨V, hV⟩ := g.U_sylow_centralizer
  have hVR : (V : Subgroup J) ≤ R := by
    intro x hx
    exact g.U.le_normalizer (hV ▸ mem_map_of_mem J.subtype hx)
  have hRV := V.is_maximal' hR hVR
  apply le_antisymm
  · intro x hx
    have hxR : (⟨x, hx.1⟩ : J) ∈ R := hx.2
    rw [hRV] at hxR
    exact hV ▸ mem_map_of_mem J.subtype hxR
  · exact le_inf g.U_le_centralizer g.U.le_normalizer

/-- Intersecting the centralizer J with the source normalizer gives precisely U. -/
public theorem normalizer_S_inf_centralizer (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (hU : Nat.card g.U = 2) :
    normalizer (g.S : Set G) ⊓ centralizer (residualGenerated M z t : Set G) = g.U := by
  let J := centralizer (residualGenerated M z t : Set G)
  have hSJ : g.S ⊓ J = g.U := by
    apply le_antisymm
    · exact (inf_le_inf_left g.S d.residual_centralizer_le_pair).trans g.S_inf_pair.le
    · exact le_inf g.U_le_S g.U_le_centralizer
  apply le_antisymm
  · intro x hx
    have hN : x ∈ normalizer (g.U : Set G) := by
      rw [← hSJ]
      exact inf_normalizer_le_normalizer_inf ⟨hx.1, J.le_normalizer hx.2⟩
    exact centralizer_inf_normalizer_U d g f hf hU ▸ ⟨hx.2, hN⟩
  · exact le_inf (g.U_le_S.trans g.S.le_normalizer) g.U_le_centralizer

/-- Source C_{N∩D}(K)=KU, reduced to the automorphism-theoretic inclusion
C_D(K) ≤ KJ. The latter remains an independent model input. -/
public theorem normalizer_pair_torus_centralizer_of_model
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (hU : Nat.card g.U = 2)
    (hmodel : residualPairStabilizer M t ⊓ centralizer (residualCommutator M t : Set G) ≤
      residualCommutator M t ⊔ centralizer (residualGenerated M z t : Set G)) :
    (normalizer (g.S : Set G) ⊓ residualPairStabilizer M t) ⊓
      centralizer (residualCommutator M t : Set G) = residualCommutator M t ⊔ g.U := by
  let K := residualCommutator M t
  let J := centralizer (residualGenerated M z t : Set G)
  have hKL : K ≤ residualGenerated M z t := le_sup_right
  have hJK : J ≤ centralizer (K : Set G) := centralizer_le hKL
  have hKN := d.torus_le_normalizer_S g s
  have hKD : K ≤ residualPairStabilizer M t := by
    dsimp [K]
    rw [d.torus_eq_local_pair]
    exact inf_le_left
  have hUK : g.U ≤ centralizer (K : Set G) := g.U_le_centralizer.trans hJK
  apply le_antisymm
  · intro x hx
    have hp := hmodel ⟨hx.1.2, hx.2⟩
    have hprod : x ∈ (K : Set G) * (J : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left K J
        (hJK.trans (Subgroup.centralizer_le_normalizer _))]
      exact hp
    obtain ⟨k, hk, j, hj, rfl⟩ := hprod
    have hjN : j ∈ normalizer (g.S : Set G) := by
      simpa only [inv_mul_cancel_left] using
        (normalizer (g.S : Set G)).mul_mem
          ((normalizer (g.S : Set G)).inv_mem (hKN hk)) hx.1.1
    have hjU : j ∈ g.U := normalizer_S_inf_centralizer d g f hf hU ▸ ⟨hjN, hj⟩
    exact mul_mem_sup hk hjU
  · apply sup_le
    · apply le_inf (le_inf hKN hKD)
      let : IsCyclic K := d.torus_cyclic
      intro x hx k hk
      exact congrArg Subtype.val (mul_comm (⟨k, hk⟩ : K) ⟨x, hx⟩)
    · exact le_inf (le_inf (g.U_le_S.trans g.S.le_normalizer)
        (g.U_le_centralizer.trans d.residual_centralizer_le_pair)) hUK
end BenderSuzuki.ZD.SuzukiExclusion.OddNormalizer
