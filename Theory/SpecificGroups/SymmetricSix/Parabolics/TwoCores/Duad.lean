module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Models
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Coordinates
import Mathlib.Tactic

/-!
# Duad parabolic two-cores in S₆ and A₆

The actual stabilizer of `{0,1}` is S₂ × S₄. Its even subgroup is S₄, with
the first coordinate determined by the sign of the second. Transporting the
four-letter conjugation action on double transpositions identifies both
intrinsic two-cores and gives their S₃ quotients. Their centralizers in the
parabolics are precisely the cores, so the induced quotient actions are
faithful. The A₆ action is irreducible; the S₆ action has the central two-letter
factor as a proper invariant subgroup of order two.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.7,
printed pp. 420–421. This is the local duad calculation used there, including
the S₆ exception, not an assertion of the other geometric clauses of I.5.7.
-/

public section

namespace Theory.SpecificGroups.SymmetricSix
open DuadCalculation
private theorem elementary_of_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) [IsElementaryAbelian 2 H] : IsElementaryAbelian 2 G where
  is_comm.comm := by
    intro x y
    apply e.injective
    simpa only [map_mul] using IsMulCommutative.is_comm.comm (e x) (e y)
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply e.injective
    simpa only [map_pow, map_one] using
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 H) (e x)

private noncomputable def coreTransport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : pCore 2 G ≃* pCore 2 H :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))

private theorem mem_core_transport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (x : G) : e x ∈ pCore 2 H ↔ x ∈ pCore 2 G := by
  rw [← pCore_map_iso 2 e, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, he⟩
    exact e.injective he ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

private theorem centralizer_transport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H)
    (hc : Subgroup.centralizer (pCore 2 H : Set H) = pCore 2 H) :
    Subgroup.centralizer (pCore 2 G : Set G) = pCore 2 G := by
  ext x
  rw [← mem_core_transport e x, ← hc, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    obtain ⟨z, rfl⟩ := e.surjective y
    have hz := hx z ((mem_core_transport e z).mp hy)
    simpa only [map_mul] using congrArg e hz
  · intro hx y hy
    apply e.injective
    simpa only [map_mul] using hx (e y) ((mem_core_transport e y).mpr hy)

/-- The actual eight-group core, identified through the two disjoint letter blocks. -/
noncomputable def duadCoreEquiv : pCore 2 duadStabilizer ≃* productCore :=
  (coreTransport duadProductEquiv.symm).trans (MulEquiv.subgroupCongr productCore_eq.symm)

/-- The actual Klein four core of the even duad stabilizer. -/
noncomputable def a6DuadCoreEquiv : pCore 2 a6DuadStabilizer ≃* core :=
  (coreTransport a6DuadModelEquiv.symm).trans (MulEquiv.subgroupCongr core_eq.symm)

/-- Explicit binary coordinates on the actual S₆ duad core. -/
noncomputable def duadCoreBinaryEquiv :
    pCore 2 duadStabilizer ≃* Multiplicative (Fin 3 → ZMod 2) :=
  duadCoreEquiv.trans binaryEightEquiv.symm

/-- Explicit binary coordinates on the actual A₆ duad core. -/
noncomputable def a6DuadCoreBinaryEquiv :
    pCore 2 a6DuadStabilizer ≃* Multiplicative (Fin 2 → ZMod 2) :=
  a6DuadCoreEquiv.trans binaryFourEquiv.symm

theorem duadCore_elementary : IsElementaryAbelian 2 (pCore 2 duadStabilizer) :=
  elementary_of_equiv duadCoreEquiv

theorem a6DuadCore_elementary : IsElementaryAbelian 2 (pCore 2 a6DuadStabilizer) :=
  elementary_of_equiv a6DuadCoreEquiv

theorem duadCore_card : Nat.card (pCore 2 duadStabilizer) = 8 :=
  (Nat.card_congr duadCoreEquiv.toEquiv).trans productCore_card

theorem a6DuadCore_card : Nat.card (pCore 2 a6DuadStabilizer) = 4 :=
  (Nat.card_congr a6DuadCoreEquiv.toEquiv).trans core_card

/-- Intrinsic membership in the core: the complementary four-letter permutation
is even and has square one; the two-letter permutation is unrestricted. -/
theorem mem_duadCore_iff (g : duadStabilizer) :
    g ∈ pCore 2 duadStabilizer ↔
      (duadProductEquiv.symm g).2.sign = 1 ∧ (duadProductEquiv.symm g).2 ^ 2 = 1 := by
  rw [← mem_core_transport duadProductEquiv.symm, ← productCore_eq]
  change (True ∧ _ ∈ core) ↔ _
  rw [true_and, core_mem_iff]

/-- Intrinsic membership in the even duad core in the actual four-letter model. -/
theorem mem_a6DuadCore_iff (g : a6DuadStabilizer) :
    g ∈ pCore 2 a6DuadStabilizer ↔
      (a6DuadModelEquiv.symm g).sign = 1 ∧ (a6DuadModelEquiv.symm g) ^ 2 = 1 := by
  rw [← mem_core_transport a6DuadModelEquiv.symm, ← core_eq, core_mem_iff]

noncomputable def duadQuotientHom : duadStabilizer →* Equiv.Perm (Fin 3) :=
  productQuotientHom.comp duadProductEquiv.symm.toMonoidHom

noncomputable def a6DuadQuotientHom : a6DuadStabilizer →* Equiv.Perm (Fin 3) :=
  quotientHom.comp a6DuadModelEquiv.symm.toMonoidHom

theorem duadQuotientHom_surjective : Function.Surjective duadQuotientHom :=
  productQuotientHom_surjective.comp duadProductEquiv.symm.surjective

theorem a6DuadQuotientHom_surjective : Function.Surjective a6DuadQuotientHom :=
  quotientHom_surjective.comp a6DuadModelEquiv.symm.surjective

private theorem ker_transport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (f : H →* Equiv.Perm (Fin 3)) (hf : f.ker = pCore 2 H) :
    (f.comp e.toMonoidHom).ker = pCore 2 G := by
  ext x
  change f (e x) = 1 ↔ _
  rw [← MonoidHom.mem_ker, hf, mem_core_transport]

theorem duadQuotientHom_ker : duadQuotientHom.ker = pCore 2 duadStabilizer :=
  ker_transport duadProductEquiv.symm _ (productQuotientHom_ker.trans productCore_eq)

theorem a6DuadQuotientHom_ker : a6DuadQuotientHom.ker = pCore 2 a6DuadStabilizer :=
  ker_transport a6DuadModelEquiv.symm _ core_eq

noncomputable def duadCoreQuotientEquiv :
    duadStabilizer ⧸ pCore 2 duadStabilizer ≃* Equiv.Perm (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq duadQuotientHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ duadQuotientHom_surjective)

noncomputable def a6DuadCoreQuotientEquiv :
    a6DuadStabilizer ⧸ pCore 2 a6DuadStabilizer ≃* Equiv.Perm (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq a6DuadQuotientHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ a6DuadQuotientHom_surjective)

/-- Kernel of the actual conjugation action on the eight-group core. -/
theorem duadCore_centralizer :
    Subgroup.centralizer (pCore 2 duadStabilizer : Set duadStabilizer) =
      pCore 2 duadStabilizer :=
  centralizer_transport duadProductEquiv.symm (by
    rw [← productCore_eq]; exact centralizer_productCore)

/-- Kernel of the actual conjugation action on the Klein four core. -/
theorem a6DuadCore_centralizer :
    Subgroup.centralizer (pCore 2 a6DuadStabilizer : Set a6DuadStabilizer) =
      pCore 2 a6DuadStabilizer :=
  centralizer_transport a6DuadModelEquiv.symm (by rw [← core_eq]; exact centralizer_core)

/-- Irreducibility uses normality in the parabolic, not normality in `A₆`. -/
theorem a6DuadCore_irreducible (N : Subgroup a6DuadStabilizer) [N.Normal]
    (hle : N ≤ pCore 2 a6DuadStabilizer) :
    N = ⊥ ∨ N = pCore 2 a6DuadStabilizer := by
  let e := a6DuadModelEquiv.symm
  let M := N.map e.toMonoidHom
  have : M.Normal := Subgroup.Normal.map inferInstance _ e.surjective
  have hm : M ≤ core := by
    rw [core_eq, ← pCore_map_iso 2 e]
    exact Subgroup.map_mono hle
  rcases normal_subgroup_core M hm with h | h
  · left
    apply e.mapSubgroup.injective
    simpa only [MulEquiv.coe_mapSubgroup, Subgroup.map_bot] using h
  · right
    apply e.mapSubgroup.injective
    simpa only [MulEquiv.coe_mapSubgroup, pCore_map_iso, ← core_eq] using h

/-- The two-letter factor is the invariant line responsible for the S₆ exception. -/
noncomputable def duadInvariantLine : Subgroup duadStabilizer := centralFactor.map duadProductEquiv.toMonoidHom

instance : duadInvariantLine.Normal :=
  Subgroup.Normal.map inferInstance _ duadProductEquiv.surjective

theorem duadInvariantLine_card : Nat.card duadInvariantLine = 2 :=
  (Nat.card_congr (duadProductEquiv.subgroupMap centralFactor).toEquiv).symm.trans
    centralFactor_card

theorem duadInvariantLine_ne_bot : duadInvariantLine ≠ ⊥ := by
  intro h
  have := duadInvariantLine_card
  rw [h, Nat.card_eq_fintype_card] at this
  simp at this

theorem duadInvariantLine_lt_core : duadInvariantLine < pCore 2 duadStabilizer := by
  rw [← pCore_map_iso 2 duadProductEquiv, ← productCore_eq]
  exact duadProductEquiv.mapSubgroup.strictMono centralFactor_lt_core

theorem duadInvariantLine_bot_lt : (⊥ : Subgroup duadStabilizer) < duadInvariantLine :=
  bot_lt_iff_ne_bot.mpr duadInvariantLine_ne_bot

end Theory.SpecificGroups.SymmetricSix
