module

public import Mathlib.GroupTheory.Sylow
public import Theory.GroupTheory.AmalgamExtensionFaithfulness
public import Theory.GroupTheory.Centralizer

/-!
# Local centralizers in Sylow subgroups

If `N` is normal in `H`, and both `H / N` and `Z(N)` are p-groups, then
`C_H(N)` is a normal p-subgroup and lies in every Sylow p-subgroup of `H`.
Restricting the quotient map to the centralizer has kernel `Z(N)` and image
in the p-group quotient. The extension property for p-groups proves the claim.
The general criterion does not require finiteness.

We provide subgroup-type and ambient-subgroup forms, an index-at-most-two
specialization, and a faithfulness consequence for compatible extension actions.

Source: the local kernel argument for Aschbacher–Smith, *The Classification
of Quasithin Groups*, F.4.23(5), applied to the extension in F.2.11.
Here `H = Y_d`, `N = X_d`, and the supplied Sylow subgroup is `Y_e`.
Faithfulness on `Y_e` alone does not control a kernel in all of `Y_d`;
the centralizer containment proved here supplies that additional step.
-/

namespace Theory.GroupTheory

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

/-- The centralizer of a normal subgroup is a p-group if its center and the
ambient quotient are p-groups. -/
public theorem isPGroup_centralizer_of_quotient_center
    (N : Subgroup G) [N.Normal]
    (hq : IsPGroup p (G ⧸ N)) (hz : IsPGroup p (center N)) :
    IsPGroup p (centralizer (N : Set G)) := by
  let C := centralizer (N : Set G)
  let f : C →* G ⧸ N := (QuotientGroup.mk' N).comp C.subtype
  have hk : IsPGroup p f.ker := by
    apply ((hz.map N.subtype).comap_subtype (K := C)).to_le
    intro x hx
    have hxN : (x : G) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
    change (x : G) ∈ (center N).map N.subtype
    refine ⟨⟨x, hxN⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro n
    apply Subtype.ext
    exact x.property n n.property
  have ht := (hq.to_subgroup ⊤).comap_of_ker_isPGroup f hk
  rw [Subgroup.comap_top] at ht
  exact ht.of_equiv Subgroup.topEquiv

/-- The local centralizer lies in every Sylow p-subgroup. -/
public theorem centralizer_le_sylow_of_quotient_center
    (N : Subgroup G) [N.Normal]
    (hq : IsPGroup p (G ⧸ N)) (hz : IsPGroup p (center N))
    (S : Sylow p G) : centralizer (N : Set G) ≤ S :=
  (isPGroup_centralizer_of_quotient_center N hq hz).le_sylow_of_normal S

/-- The complete local criterion: normality, the p-group property, and
containment in a specified Sylow subgroup. -/
public theorem centralizer_normal_isPGroup_le_sylow
    (N : Subgroup G) [N.Normal]
    (hq : IsPGroup p (G ⧸ N)) (hz : IsPGroup p (center N))
    (S : Sylow p G) :
    (centralizer (N : Set G)).Normal ∧
      IsPGroup p (centralizer (N : Set G)) ∧ centralizer (N : Set G) ≤ S :=
  ⟨inferInstance, isPGroup_centralizer_of_quotient_center N hq hz,
    centralizer_le_sylow_of_quotient_center N hq hz S⟩

/-- Ambient-subgroup form: `C_H(N)` is contained in the ambient image of
any Sylow p-subgroup of `H`. Normality is required only inside `H`. -/
public theorem subgroupCentralizerIn_le_sylow_of_quotient_center
    (H N : Subgroup G) (hNH : N ≤ H) [(N.subgroupOf H).Normal]
    (hq : IsPGroup p (H ⧸ N.subgroupOf H)) (hz : IsPGroup p (center N))
    (S : Sylow p H) :
    subgroupCentralizerIn H N ≤ (S : Subgroup H).map H.subtype := by
  have hz' : IsPGroup p (center (N.subgroupOf H)) :=
    hz.of_equiv (Subgroup.centerCongr (subgroupOfEquivOfLe hNH).symm)
  have hC := centralizer_le_sylow_of_quotient_center (N.subgroupOf H) hq hz' S
  intro x hx
  refine ⟨⟨x, hx.1⟩, hC ?_, rfl⟩
  intro n hn
  exact Subtype.ext (hx.2 n hn)

/-- An index at most two makes the quotient a two-group, so a two-group
center forces the centralizer into every Sylow two-subgroup. -/
public theorem centralizer_le_sylow_of_index_le_two
    [Finite G] (N : Subgroup G) [N.Normal]
    (hi : N.index ≤ 2) (hz : IsPGroup 2 (center N)) (S : Sylow 2 G) :
    centralizer (N : Set G) ≤ S := by
  apply centralizer_le_sylow_of_quotient_center N ?_ hz S
  change Nat.card (G ⧸ N) ≤ 2 at hi
  have hpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  have heq : Nat.card (G ⧸ N) = 1 ∨ Nat.card (G ⧸ N) = 2 := by omega
  rcases heq with h | h
  · exact IsPGroup.of_card (n := 0) (by simpa using h)
  · exact IsPGroup.of_card (n := 1) (by simpa using h)

/-- A compatible extension action faithful on a Sylow subgroup is faithful
on the whole group when the normal subgroup's center and quotient are p-groups. -/
public theorem automorphismHom_injective_of_sylow_quotient_center
    {Y : Type*} [Group Y] (N : Subgroup Y) [N.Normal]
    (hq : IsPGroup p (Y ⧸ N)) (hz : IsPGroup p (center N)) (S : Sylow p Y)
    (mu : N →* G) (hmu : Function.Injective mu) (rho : Y →* MulAut G)
    (hcompat : ∀ (y : Y) (n : N), mu (MulAut.conjNormal y n) = rho y (mu n))
    (hS : Function.Injective (rho.comp (S : Subgroup Y).subtype)) :
    Function.Injective rho :=
  automorphismHom_injective_of_local_centralizer (S : Subgroup Y) N mu hmu rho
    hcompat (centralizer_le_sylow_of_quotient_center N hq hz S) hS

end Theory.GroupTheory
