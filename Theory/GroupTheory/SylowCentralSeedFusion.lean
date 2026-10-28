module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Stellmacher.OmegaOneCenterMap

/-!
# Extending fusion on a central Sylow seed

Let J contain a Sylow two-subgroup T. Suppose conjugation by J on every
subgroup of Ω₁Z(T) is realized in M, and N_G(T) lies in M. Frattini
factorization in N_G(J) writes a transporter as j b with j in J and b
normalizing T. The image under b still lies in Ω₁Z(T), so the original
fusion statement applies to that image. Thus M realizes conjugation by
all of N_G(J) on these subgroups.

The intermediate image is essential: TI under the separate factors alone
would not justify TI under their product. The consumer is the C_K H
normalizer in Aschbacher–Smith 5.1.17, printed p.640
(refs/quasithin.pdf), via OddSetupResidualFusion.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem central_seed_conj_mul (Z : Subgroup G) (a b : G) :
    Z.map (MulAut.conj (a*b)).toMonoidHom =
      (Z.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply,mul_assoc]

private theorem normalizer_sylow_factorization (T : Sylow 2 G) (J : Subgroup G)
    (hTJ : (T : Subgroup G) ≤ J) :
    normalizer (J : Set G) = J ⊔
      (normalizer (J : Set G) ⊓ normalizer (T : Set G)) := by
  let N := normalizer (J : Set G)
  have hTN : (T : Subgroup G) ≤ N := hTJ.trans J.le_normalizer
  let J' := J.subgroupOf N
  let : J'.Normal := normal_subgroupOf_of_le_normalizer (show N ≤ normalizer (J : Set G) from le_rfl)
  let S := T.subtype hTN
  have hS : (S : Subgroup N) ≤ J' := fun _ ht => hTJ ht
  have hf := congrArg (map N.subtype) (S.normalizer_sup_eq_top' hS)
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le J.le_normalizer,
    ←MonoidHom.range_eq_map,range_subtype] at hf
  have hm : (S : Subgroup N).map N.subtype = T := by
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN]
  have hn := (S : Subgroup N).le_normalizer_map N.subtype
  rw [hm] at hn
  apply le_antisymm _ (sup_le J.le_normalizer inf_le_left)
  exact hf.ge.trans (sup_le (le_sup_of_le_right (le_inf (map_subtype_le _) hn)) le_sup_left)

/-- Fusion on all subgroups of a central Sylow seed extends to the full
normalizer of a Sylow overgroup. -/
theorem normalizer_fusion_on_omegaCenter
    (T : Sylow 2 G) (J M : Subgroup G) (hTJ : (T : Subgroup G) ≤ J)
    (hTM : normalizer (T : Set G) ≤ M)
    (hf : ∀ (Z : Subgroup G), Z ≤ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ∀ g ∈ J, ∃ b ∈ M,
        Z.map (MulAut.conj g).toMonoidHom = Z.map (MulAut.conj b).toMonoidHom)
    (Z : Subgroup G) (hZ : Z ≤ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    {g : G} (hg : g ∈ normalizer (J : Set G)) :
    ∃ b ∈ M, Z.map (MulAut.conj g).toMonoidHom = Z.map (MulAut.conj b).toMonoidHom := by
  let B := normalizer (J : Set G) ⊓ normalizer (T : Set G)
  have hp : g ∈ (J : Set G) * (B : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left J B inf_le_left,
      ←normalizer_sylow_factorization T J hTJ]
    exact hg
  obtain ⟨j,hj,b,hb,rfl⟩ := hp
  have hΩ : (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)).map
      (MulAut.conj b).toMonoidHom = Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
    rw [←Stellmacher.omegaOneCenterAmbient_map_injective _ (MulAut.conj b).injective]
    exact congrArg Stellmacher.omegaOneCenterAmbient
      (show (T : Subgroup G).map (MulAut.conj b).toMonoidHom = T from
        mem_normalizer_iff_map_conj_eq.mp hb.2)
  obtain ⟨a,ha,he⟩ := hf (Z.map (MulAut.conj b).toMonoidHom)
    ((map_mono hZ).trans_eq hΩ) j hj
  refine ⟨a*b,M.mul_mem ha (hTM hb.2),?_⟩
  rw [central_seed_conj_mul,central_seed_conj_mul,he]
end Subgroup
