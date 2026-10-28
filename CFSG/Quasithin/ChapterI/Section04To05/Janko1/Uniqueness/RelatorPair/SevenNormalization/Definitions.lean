module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Basic

/-!
# The local configuration for Janko's matrix normalization

Gorenstein, *Finite Groups*, §16.6, pp.482–483, describes a complement
`H = Y:U` to the elementary Sylow subgroup S in its normalizer, with
`|Y| = 7`, `|U| = 3`, and `C_S(U) = ⟨x⟩` of order two. We mark generators
so that direct conjugation by u squares y; replacing u by its inverse
interchanges the two faithful actions of the cubic complement.

The second structure adds the involution w normalizing H, centralizing U,
inverting Y, and satisfying equation (6.2), `(xw)^5 = 1`. Neither structure
contains a matrix-normalization conclusion, a model isomorphism for G, or
generation of G. Existence of the second structure is a separate source
obligation. These interfaces use actual subgroups of the original G, with
all normalizers and centralizers taken there.
-/

namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization
open Subgroup
variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)

/-- The marked `7:3` complement and its cubic fixed involution in the
source Sylow subgroup. The action field uses direct, left conjugation. -/
public structure NormalizerFrame where
  H : Subgroup G
  y : G
  u : G
  x : G
  card_H : Nat.card H = 21
  H_le : H ≤ normalizer (h.sylow : Set G)
  disjoint : Disjoint H (h.sylow : Subgroup G)
  sup_eq : H ⊔ (h.sylow : Subgroup G) = normalizer (h.sylow : Set G)
  y_mem : y ∈ H
  u_mem : u ∈ H
  order_y : orderOf y = 7
  order_u : orderOf u = 3
  generated : zpowers y ⊔ zpowers u = H
  action : u * y * u⁻¹ = y ^ 2
  x_mem : x ∈ (h.sylow : Subgroup G)
  order_x : orderOf x = 2
  fixed : (h.sylow : Subgroup G) ⊓ centralizer (zpowers u : Set G) = zpowers x

/-- The full local configuration preceding the source matrix computation.
Its existence is not assumed in the eventual source normalization theorem. -/
public structure BruhatFrame extends NormalizerFrame h where
  w : G
  order_w : orderOf w = 2
  w_normalizes : w ∈ normalizer (H : Set G)
  w_centralizes : Commute w u
  w_inverts : w * y * w⁻¹ = y⁻¹
  product_fifth : (x * w) ^ 5 = 1

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization
