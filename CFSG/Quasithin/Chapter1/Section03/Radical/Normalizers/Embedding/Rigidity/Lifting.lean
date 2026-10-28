module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Marked

/-!
# Recovering a radical Xi subgroup from its quotient image

If T normalizes K, its two-core lies in the ambient Sylow subgroup T.
Thus O₂(K) normalizes the Xi subgroup X, and X is the two-residual of
XO₂(K). An identification of its quotient image with Ω₁(O_p(K/O₂(K)))
therefore identifies X with the characteristic subgroup Ξ_p(K).
The final lemma records the resulting contradiction for a normal component
of an escaping normalizer. Identifying the omega image is a separate
structural obligation; no nonnormality assertion is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Proposition 1.3.8, printed p.513.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Rigidity
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem core_le_sylow (T : Sylow 2 G) {K : Subgroup G}
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    K.pCoreIn 2 ≤ (T : Subgroup G) := by
  have hn : K ⊔ (T : Subgroup G) ≤ normalizer (K : Set G) :=
    sup_le K.le_normalizer hTK
  have hcore := pCoreIn_mono_of_normalizes (p := 2) le_sup_left hn
  have hs := pCoreIn_le_sylow (K ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  exact hcore.trans (by simpa only [Sylow.coe_subtype,
    map_subgroupOf_eq_of_le le_sup_right] using hs)

omit [Finite G] in
theorem eq_XiP_of_image_eq_omega (p : ℕ) (T : Sylow 2 G) {X K : Subgroup G}
    (hX : XiMember T X) (hXK : X ≤ K)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (himage : (X.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) =
      xiOmegaCore p K) : X = XiP p K := by
  have hp : IsPPerfect 2 (X.subgroupOf K) :=
    hX.perfect.of_surjective (subgroupOfEquivOfLe hXK).symm.toMonoidHom
      (subgroupOfEquivOfLe hXK).symm.surjective
  have hn : pCore 2 K ≤ normalizer (X.subgroupOf K : Set K) := by
    rw [← subgroupOf_normalizer_eq hXK]
    intro x hx
    exact hX.invariant (core_le_sylow T hTK (mem_map_of_mem K.subtype hx))
  have he : xiPPreimage p K = X.subgroupOf K ⊔ pCore 2 K := by
    rw [xiPPreimage, ← himage, comap_map_eq, QuotientGroup.ker_mk']
  have hr := embedded_pResidual_join_pGroup (X.subgroupOf K) (pCore 2 K)
    hp pCore_isPGroup hn
  have hi : xiPIn p K = X.subgroupOf K := by
    unfold xiPIn
    rw [he]
    exact hr
  rw [XiP, hi, map_subgroupOf_eq_of_le hXK]

omit [Finite G] in
theorem characteristic_of_image_eq_omega (p : ℕ) (T : Sylow 2 G)
    {X K : Subgroup G} (hX : XiMember T X) (hXK : X ≤ K)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (himage : (X.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) =
      xiOmegaCore p K) : (X.subgroupOf K).Characteristic := by
  rw [eq_XiP_of_image_eq_omega p T hX hXK hTK himage]
  infer_instance

omit [Finite G] in
theorem image_ne_omega_of_escape (p : ℕ) (T : Sylow 2 G)
    {X K N M : Subgroup G} (hX : XiMember T X) (hXK : X ≤ K)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKN : K ≤ N) (hK : (K.subgroupOf N).Normal)
    (hM : normalizer (X : Set G) = M) (hescape : ¬ N ≤ M) :
    (X.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) ≠ xiOmegaCore p K := by
  intro he
  have hn : N ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKN).mp hK
  have hx := eq_XiP_of_image_eq_omega p T hX hXK hTK he
  apply hescape
  rw [← hM, hx]
  exact hn.trans (normalizer_le_normalizer_XiP p K)

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Rigidity
