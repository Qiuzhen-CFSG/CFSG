module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Quotients

/-!
# The local index of U C_T(V)

Conjugation on the literal V has kernel C_T(V). The inverse image of the
U-action image is therefore U C_T(V). The earlier orthogonal action has
|Aut_T(V)| = 8 and |Aut_U(V)| = 4, so this inverse image has index two in T.
These orders concern actual conjugation images, independently of O²(H).
The residual assembly uses the resulting index only after proving that
U and C_T(V) lie in K.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.2(1), 15.3.51(2a), and 15.3.53(1), printed pp.1121 and 1145–1146;
the transfer subgroup is used on printed pp.1150–1151.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian

variable {G : Type*} [Group G]

/-- Conjugation by T on V, restricted from the actual normalizer action. -/
def conjugationOnV (T V : Subgroup G) (hTV : T ≤ normalizer (V : Set G)) :
    T →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion hTV)

/-- The action uses ambient conjugation on every element of V. -/
theorem conjugationOnV_apply (T V : Subgroup G) (hTV : T ≤ normalizer (V : Set G))
    (t : T) (v : V) :
    (conjugationOnV T V hTV t v : G) = (t : G) * (v : G) * (t : G)⁻¹ := rfl

/-- The kernel is the centralizer inside T, without ambient normality of V. -/
theorem conjugationOnV_ker (T V : Subgroup G) (hTV : T ≤ normalizer (V : Set G)) :
    (conjugationOnV T V hTV).ker = (centralizer (V : Set G)).subgroupOf T := by
  rw [conjugationOnV, ← MonoidHom.comap_ker, normalizerMonoidHom_ker]
  rfl

/-- The earlier conjugation-image orders give the local index through the
literal kernel and inverse image; no residual containment is assumed. -/
theorem transfer_index_of_conjugation_orders [Finite G] (T Z ZS V : Subgroup G)
    (hUT : closureU Z ZS ≤ T) (hTV : T ≤ normalizer (V : Set G))
    (hT : Nat.card (conjugationOnV T V hTV).range = 8)
    (hU : Nat.card (((closureU Z ZS).subgroupOf T).map (conjugationOnV T V hTV)) = 4) :
    ((closureU Z ZS ⊔ (T ⊓ centralizer (V : Set G))).subgroupOf T).index = 2 := by
  let f := conjugationOnV T V hTV
  let A := (closureU Z ZS).subgroupOf T
  have he : ((closureU Z ZS ⊔ (T ⊓ centralizer (V : Set G))).subgroupOf T) =
      (A.map f).comap f := by
    rw [subgroupOf_sup hUT inf_le_left, comap_map_eq, conjugationOnV_ker,
      inf_subgroupOf_left]
  rw [he, index_comap]
  have hc := ((A.map f).subgroupOf f.range).card_mul_index
  have hec : Nat.card ((A.map f).subgroupOf f.range) = Nat.card (A.map f) :=
    Nat.card_congr (subgroupOfEquivOfLe (A.map_le_range f)).toEquiv
  rw [hec, hU, hT] at hc
  change ((A.map f).subgroupOf f.range).index = 2
  omega

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
