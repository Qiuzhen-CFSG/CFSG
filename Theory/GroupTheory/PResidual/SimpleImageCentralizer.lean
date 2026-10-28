module
public import Theory.GroupTheory.PResidual.PrimeSection
public import Theory.GroupTheory.CommutatorPreimage
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Propagating section centralization through a simple quotient

Suppose a surjection has a two-group kernel and simple image. A subgroup
with nontrivial image that centralizes C/V forces every two-perfect
subgroup to centralize C/V. The section centralizer is normal, hence its
image is the whole simple quotient; two-perfectness removes the two-group
supplement. No elementary abelianness of C/V is needed.

Source application: Aschbacher–Smith, 13.8.31(1), printed p.965.
-/

public section
open Subgroup
namespace Subgroup
variable {G S : Type*} [Group G] [Group S] [IsSimpleGroup S]
theorem commutator_le_of_nontrivial_simple_image
    (f : G →* S) (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (K C V B : Subgroup G) [C.Normal] [V.Normal]
    (hK : IsPPerfect 2 K) (hB : ⁅B,C⁆ ≤ V) (hne : ¬ B ≤ f.ker) :
    ⁅K,C⁆ ≤ V := by
  let D := commutatorPreimage ⊤ C V
  let : D.Normal := normalizer_eq_top_iff.mp (top_unique
    (commutatorPreimage_normalized ⊤ C V ⊤ le_normalizer_of_normal
      le_normalizer_of_normal le_normalizer_of_normal le_normalizer_of_normal))
  have hBD : B ≤ D := le_commutatorPreimage le_top hB
  let : (D.map f).Normal := Normal.map inferInstance f hf
  have hDt : D.map f = ⊤ := by
    rcases (inferInstance : (D.map f).Normal).eq_bot_or_eq_top with hb | ht
    · exact (hne (hBD.trans ((map_eq_bot_iff D).mp hb))).elim
    · exact ht
  have hcover : K ≤ D ⊔ f.ker := by
    rw [← comap_map_eq, hDt, comap_top]
    exact le_top
  have hKD := le_normal_of_isPPerfect_of_le_sup_pGroup K D f.ker hK hp hcover
  exact (commutator_mono hKD le_rfl).trans
    (commutator_commutatorPreimage_le ⊤ C V le_normalizer_of_normal)
end Subgroup
