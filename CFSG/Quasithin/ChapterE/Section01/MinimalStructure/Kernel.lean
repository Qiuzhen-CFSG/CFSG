module

public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.Frattini
public import Theory.GroupTheory.MinimalSylowSupplementKernel

/-!
# Solvability of the kernel of a minimal Sylow supplement

For a genuine minimal supplement `K` over the prescribed Sylow two-subgroup
`T`, the kernel of its map to `G/Y` is `Y.subgroupOf K`. The Frattini argument
makes its Sylow intersection normal in `K`. Minimality descends to the
quotient by that intersection; the remaining kernel lies in the nilpotent
Frattini subgroup. Thus the original kernel is solvable.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.10 proof, printed p.211. This proves the solvable-kernel input used in
parts (3) and (4), using minimality rather than odd-order solvability.
-/

public section
namespace CFSG.Quasithin.ChapterE
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The kernel of a minimal supplement over a Sylow two-subgroup is solvable,
with the kernel viewed intrinsically as a subgroup of the supplement. -/
theorem IsMinimalSupplement.isSolvable_kernel (T : Sylow 2 G)
    {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K) :
    Group.IsSolvable (Y.subgroupOf K) := by
  let f := (QuotientGroup.mk' Y).subgroupMap K
  have hf := (QuotientGroup.mk' Y).subgroupMap_surjective K
  have hker : f.ker = Y.subgroupOf K := by
    ext k
    change (f k = 1) ↔ (k : G) ∈ Y
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (k : G)
  have hn := h.normal_inf_preimage T ⊥ IsPGroup.of_bot
  change ((T : Subgroup G).subgroupOf K ⊓ (⊥ : Subgroup _).comap f).Normal at hn
  rw [MonoidHom.comap_bot, hker] at hn
  apply Sylow.isSolvable_of_minimal_supplement (T.subtype h.1.1) (Y.subgroupOf K) hn
  intro L hTL hLN
  apply h.eq_top_of_map_eq_top L hTL
  have hNmap : (Y.subgroupOf K).map f = ⊥ := by
    rw [← hker]
    exact Subgroup.map_ker_self f
  have he := congrArg (Subgroup.map f) hLN
  rw [Subgroup.map_sup, hNmap, sup_bot_eq, map_top_of_surjective f hf] at he
  exact he

end CFSG.Quasithin.ChapterE
