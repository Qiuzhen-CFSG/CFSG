module

public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.PGroupCore

/-!
# Odd automorphisms: the quotient interface and rank obstruction in A.2.6

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), Notation A.2.5 and Corollary A.2.6, pp. 33–34.

The displayed corollary assumes a strongly quasithin K-group `G`, a normal
subgroup `L` with `L/O₂(L)` quasisimple of Lie type in characteristic two, and
an odd-order element `x`. Its conclusion describes the induced automorphism
on `L/Z(L)` as a product of inner-diagonal and field automorphisms. The proof
passes to `G/O₂,Z(L)` and invokes Theorems A and C, GLS98 2.5.12, and I.1.3.
Notation A.2.5 explicitly permits odd graph automorphisms of twisted `³D₄`.

Here `twoCoreCenter` is the preimage in `L` of `Z(L/O₂(L))`. The imported API
constructs actual conjugation automorphisms and the equivariant projection
from `L/Z(L)` onto `L/twoCoreCenter`. This projection is not silently treated
as an isomorphism: injectivity is precisely equality of the two kernels.
The meaning of the displayed automorphism conclusion across this projection
still requires the finite Lie-type automorphism interface.

The elementary obstruction is complete: an outer element of order three
centralizing an elementary abelian subgroup of order nine in `L` yields an
elementary abelian subgroup of order 27 in `C_L(x)⟨x⟩`, so `m₃(G) ≥ 3`.
The imported full-rank centralizer and prime-power lifting lemmas also give
the source's 3-prime centralizer and order-three reductions from concrete
witnesses. The finite `³D₄` fixed subgroup witness and exhaustive odd
outer-automorphism alternative are not asserted here.
-/

namespace CFSG.Quasithin.ChapterA.Section02

open Subgroup

variable {G : Type*} [Group G]

/-- `O₂,Z(L)`, as a subgroup of `L`, before mapping into the ambient group. -/
@[expose] public def twoCoreCenter (L : Type*) [Group L] : Subgroup L :=
  centralPreimage (pCore 2 L)

public instance twoCoreCenter_characteristic (L : Type*) [Group L] :
    (twoCoreCenter L).Characteristic :=
  inferInstanceAs (centralPreimage (pCore 2 L)).Characteristic

/-- The semisimple quotient used by the proof is the central quotient of `L/O₂(L)`. -/
public noncomputable def twoCoreCenterQuotientEquiv (L : Type*) [Group L] :
    L ⧸ twoCoreCenter L ≃* (L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L) :=
  centralPreimageQuotientEquiv (pCore 2 L)

/-- Precise compatibility between the displayed central quotient and the quotient
used in the proof of A.2.6. -/
public theorem twoCoreCenter_projection_equivariant (L : Subgroup G) [L.Normal]
    (x : G) (q : L ⧸ center L) :
    centralQuotientProjection (pCore 2 L) (normalQuotientAction L (center L) x q) =
      normalQuotientAction L (twoCoreCenter L) x
        (centralQuotientProjection (pCore 2 L) q) :=
  centralQuotientProjection_equivariant L (pCore 2 L) x q

/-- Identifying the two quotients would in particular require the two-core to
be central; the hypotheses of A.2.6 must not be replaced by this extra premise. -/
public theorem twoCore_le_center_of_projection_injective (L : Type*) [Group L]
    (h : Function.Injective (centralQuotientProjection (pCore 2 L))) :
    pCore 2 L ≤ center L := by
  rw [(centralQuotientProjection_injective_iff (pCore 2 L)).mp h]
  exact le_centralPreimage (pCore 2 L)

/-- A concrete triality fixed subgroup supplies the elementary subgroup in the
source's `C_L(x)⟨x⟩`; no automorphism label substitutes for that witness. -/
public theorem elementary_twenty_seven_in_fixed_join [Finite G]
    (L E : Subgroup G) [IsElementaryAbelian 3 E]
    (hEL : E ≤ L) (hE : Nat.card E = 9) (x : G)
    (hx : orderOf x = 3) (hxL : x ∉ L)
    (hfix : E ≤ centralizer ({x} : Set G)) :
    ∃ A : Subgroup G, IsElementaryAbelian 3 A ∧ Nat.card A = 27 ∧
      A ≤ (L ⊓ centralizer ({x} : Set G)) ⊔ zpowers x := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨he, hc⟩ := IsElementaryAbelian.fixed_join_card (n := 2) E x hx
    (E.disjoint_zpowers_of_prime_order_not_mem x hx (fun h => hxL (hEL h)))
    hfix (by simpa using hE)
  exact ⟨E ⊔ zpowers x, he, by simpa using hc,
    sup_le_sup (le_inf hEL hfix) le_rfl⟩

/-- The order-27 fixed-join witness contradicts the `p = 3` part of strong
quasithinness. -/
public theorem fixed_join_contradicts_three_rank [Finite G]
    (hrank : primeRank 3 G ≤ 2)
    (L E : Subgroup G) [IsElementaryAbelian 3 E]
    (hEL : E ≤ L) (hE : Nat.card E = 9) (x : G)
    (hx : orderOf x = 3) (hxL : x ∉ L)
    (hfix : E ≤ centralizer ({x} : Set G)) : False := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨A, hA, hcard, _⟩ := elementary_twenty_seven_in_fixed_join L E hEL hE x hx hxL hfix
  let := hA
  have h := IsElementaryAbelian.primeRank_ge_of_card (p := 3) (n := 3) A (by simpa using hcard)
  omega

/-- The contradiction also lifts from the quotient used in A.2.6 back to the
original group, provided the quotient kernel has order prime to three. -/
public theorem quotient_fixed_join_contradicts_three_rank [Finite G]
    {H : Type*} [Group H] (f : G →* H) (hf : Function.Surjective f)
    (hk : Nat.Coprime 3 (Nat.card f.ker)) (hrank : primeRank 3 G ≤ 2)
    (L E : Subgroup H) [IsElementaryAbelian 3 E]
    (hEL : E ≤ L) (hE : Nat.card E = 9) (x : H)
    (hx : orderOf x = 3) (hxL : x ∉ L)
    (hfix : E ≤ centralizer ({x} : Set H)) : False := by
  let : Finite H := Finite.of_surjective f hf
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨A, hA, hcard, _⟩ := elementary_twenty_seven_in_fixed_join L E hEL hE x hx hxL hfix
  let := hA
  have h := IsElementaryAbelian.primeRank_ge_of_coprime_quotient (p := 3) (n := 3)
    f hf hk A (by simpa using hcard)
  omega

end CFSG.Quasithin.ChapterA.Section02
