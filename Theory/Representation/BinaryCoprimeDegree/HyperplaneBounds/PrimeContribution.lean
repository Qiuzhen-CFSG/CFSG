module

public import Theory.Representation.BinaryCoprimeDegree.HyperplaneBounds.Counting
public import Theory.Representation.BinaryPrimeDegree
public import Mathlib.RepresentationTheory.Maschke
import Mathlib.Tactic

/-!
# The degree of a nonzero hyperplane contribution

For an elementary abelian odd-order subgroup `P` and a hyperplane `H`,
`P/H` acts on `C_V(H)`, with fixed space exactly `C_V(P)`. Maschke's theorem
provides an invariant complement to that fixed space. If the complement
is nonzero, the prime-order quotient acts faithfully on it. The binary
prime-degree bound therefore bounds the dimension difference from below.

This is the summand estimate in Aschbacher--Smith, *The Classification of
Quasithin Groups*, G.7.1(3), printed p.347. No vanishing of `C_V(P)` is
assumed, and no unrestricted direct-product assertion from A.1.17 is used.
-/

public section

namespace Representation.BinaryCoprimeDegree

private theorem prime_order_le_moving_finrank
    {Q W : Type*} [Group Q] [Finite Q]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (sigma : Representation (ZMod 2) Q W) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hcard : Nat.card Q = p)
    (hm : Module.finrank (ZMod 2) sigma.invariants < Module.finrank (ZMod 2) W) :
    orderOf (2 : ZMod p) ≤
      Module.finrank (ZMod 2) W - Module.finrank (ZMod 2) sigma.invariants := by
  have hn : (Nat.card Q : ZMod 2) ≠ 0 := by
    rw [hcard]
    intro hz
    have h := (ZMod.natCast_eq_zero_iff p 2).mp hz
    exact hp2 (((Nat.dvd_prime (Fact.out : p.Prime)).mp h).resolve_left (by decide)).symm
  let : NeZero (Nat.card Q : ZMod 2) := ⟨hn⟩
  let S : Subrepresentation sigma :=
    ⟨sigma.invariants, fun g v hv => by rw [hv g]; exact hv⟩
  obtain ⟨T, hT⟩ := exists_isCompl S
  have hT' : IsCompl sigma.invariants T.toSubmodule :=
    IsCompl.of_eq (congrArg Subrepresentation.toSubmodule hT.inf_eq_bot)
      (congrArg Subrepresentation.toSubmodule hT.sup_eq_top)
  have hdim := Submodule.finrank_add_eq_of_isCompl hT'
  have hTpos : 0 < Module.finrank (ZMod 2) T.toSubmodule := by omega
  let : IsSimpleGroup Q := isSimpleGroup_of_prime_card hcard
  have hinj : Function.Injective T.toRepresentation := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rcases (inferInstance : T.toRepresentation.ker.Normal).eq_bot_or_eq_top with h | h
    · exact h
    exfalso
    have hz : T.toSubmodule = ⊥ := by
      apply le_bot_iff.mp
      intro v hv
      have hfix : v ∈ sigma.invariants := by
        intro g
        have hker : g ∈ T.toRepresentation.ker := h ▸ Subgroup.mem_top g
        exact congrArg Subtype.val (LinearMap.congr_fun (MonoidHom.mem_ker.mp hker) ⟨v, hv⟩)
      exact hT'.inf_eq_bot ▸ (show v ∈ sigma.invariants ⊓ T.toSubmodule from ⟨hfix, hv⟩)
    rw [hz, finrank_bot] at hTpos
    omega
  have hb := BinaryPrimeDegree.orderOf_le_finrank T.toRepresentation hinj
    (Fact.out : p.Prime) hp2 (hcard ▸ dvd_refl p)
  omega

open scoped IsMulCommutative

private noncomputable def quotientFixedEquiv
    {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (P : Subgroup G) [IsMulCommutative P]
    (H : Subgroup P) :
    (quotientToInvariants (rho.comp P.subtype) H).invariants ≃ₗ[F]
      (invariants (rho.comp P.subtype)) where
  toFun v := ⟨v.val.val, fun g => by
    have hv := v.property (QuotientGroup.mk' H g)
    exact congrArg Subtype.val hv⟩
  invFun v := ⟨⟨v.val, fun h => v.property h.val⟩, by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H q
    exact Subtype.ext (v.property g)⟩
  left_inv v := rfl
  right_inv v := rfl
  map_add' v w := rfl
  map_smul' c v := rfl

/-- Every nonzero hyperplane contribution has at least the odd-prime degree.
The common fixed space is removed by an invariant complement. -/
theorem orderOf_le_hyperplaneMultiplicity
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) G V) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (P : Subgroup G) [IsElementaryAbelian p P]
    (H : Subgroup P) (hH : H.index = p)
    (hm : 0 < hyperplaneMultiplicity rho P H) :
    orderOf (2 : ZMod p) ≤ hyperplaneMultiplicity rho P H := by
  let sigma := quotientToInvariants (rho.comp P.subtype) H
  have hfixed : Module.finrank (ZMod 2) sigma.invariants =
      Module.finrank (ZMod 2) (invariants (rho.comp P.subtype)) :=
    (quotientFixedEquiv rho P H).finrank_eq
  have hdim : Module.finrank (ZMod 2) sigma.invariants <
      Module.finrank (ZMod 2) (invariants (rho.comp (P.subtype.comp H.subtype))) := by
    rw [hfixed]
    exact Nat.sub_pos_iff_lt.mp hm
  have hb := prime_order_le_moving_finrank sigma hp2
    ((Subgroup.index_eq_card H).symm.trans hH) hdim
  change orderOf (2 : ZMod p) ≤
    Module.finrank (ZMod 2) (invariants (rho.comp (P.subtype.comp H.subtype))) -
      Module.finrank (ZMod 2) sigma.invariants at hb
  rw [hfixed] at hb
  exact hb

end Representation.BinaryCoprimeDegree
