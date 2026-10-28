module
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank.Automorphisms
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.MatrixIdentification

/-!
# Strict elementary bounds outside the inner symplectic automorphisms

An elementary subgroup containing an outer involution has inner kernel of
rank at most `2*n`: it embeds in that involution's fixed group. The cyclic
outer quotient contributes at most one generator. Since `n > 1`, its order
is strictly less than `2^(3*n)`, the order of a symplectic Sylow wing.

Semilinear coverage is supplied by the proved diagram classification. The
Suzuki fixed-group equivalence is constructed from the actual fixed matrices
and compatible coefficient-field transport. Only the field and graph
cocycle descents remain explicit, in exactly their normal-form conventions.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927 (PDF p.944),
using the outer involution fixed groups in 16.1.4, printed pp.1170–1173.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour.EvenTwoRank.OuterMaximum
open DiagramAutomorphisms DiagramAutomorphisms.InvolutionNormalForms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The actual odd graph-power fixed group, over any field of the given order. -/
noncomputable def suzukiFixedEquiv (m : ℕ) (hF : Nat.card F = 2 ^ (2 * m + 1)) :
    (ExceptionalGraph.graphAut (F := F) ^ (2 * m + 1)).fixedSubgroup ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m :=
  GraphFieldFixedResidual.fixedEquivOfBinaryModel m hF
    (GraphFieldFixedResidual.fixedSuzukiEquiv m)

private theorem elementary_rank_le_of_fixed {n : ℕ}
    [IsCyclic (MulAut.Outer (Sp F))]
    (hfixed : ∀ a : MulAut (Sp F), orderOf a = 2 → a ∉ MulAut.innerSubgroup (Sp F) →
      primeRank 2 a.fixedSubgroup ≤ 2 * n)
    (E : Subgroup (MulAut (Sp F))) (hE : IsElementaryAbelian 2 E)
    (hi : ¬ E ≤ MulAut.innerSubgroup (Sp F)) :
    primeRank 2 E ≤ 2 * n + 1 := by
  let := hE
  let : CommGroup E := IsMulCommutative.instCommGroup
  let ie : Sp F ≃* MulAut.innerSubgroup (Sp F) :=
    MonoidHom.ofInjective inner_injective
  have hout : primeRank 2 (MulAut.Outer (Sp F)) ≤ 1 := by
    let P := Classical.choice (inferInstance : Nonempty (Sylow 2 (MulAut.Outer (Sp F))))
    exact P.primeRank_le_one_of_isCyclic inferInstance
  obtain ⟨a, haE, ha⟩ := SetLike.not_le_iff_exists.mp hi
  have hao : orderOf a = 2 := by
    have hs : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := E) a haE
    have hne : a ≠ 1 := fun h => ha (h ▸ (MulAut.innerSubgroup (Sp F)).one_mem)
    exact orderOf_eq_prime_iff.mpr ⟨hs, hne⟩
  let π : E →* MulAut.Outer (Sp F) :=
    (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))).comp E.subtype
  let j : π.ker →* MulAut.innerSubgroup (Sp F) := {
    toFun x := ⟨x.val.val, (QuotientGroup.eq_one_iff _).mp x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let k : π.ker →* Sp F := ie.symm.toMonoidHom.comp j
  have hk (x : π.ker) : MulAut.conj (k x) = x.val.val := by
    exact congrArg Subtype.val (ie.apply_symm_apply (j x))
  let f : π.ker →* a.fixedSubgroup := k.codRestrict _ (fun x => by
    rw [MulAut.mem_fixedSubgroup]
    apply inner_injective
    have he : a * MulAut.conj (k x) * a⁻¹ = MulAut.conj (a (k x)) := by
      ext y
      simp
    rw [← he, hk]
    have hc := congrArg Subtype.val (mul_comm (⟨a, haE⟩ : E) x.val)
    change a * x.val.val = x.val.val * a at hc
    rw [hc, mul_assoc, mul_inv_cancel, mul_one])
  have hf : Function.Injective f := by
    intro x y h
    have hxy := congrArg (fun z : a.fixedSubgroup => MulAut.conj z.val) h
    change MulAut.conj (k x) = MulAut.conj (k y) at hxy
    rw [hk, hk] at hxy
    exact Subtype.ext (Subtype.ext hxy)
  have hker := (primeRank_le_of_injective 2 f hf).trans (hfixed a hao ha)
  have hb := primeRank_le_ker_add (p := 2) π
  omega

variable {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hfield : Even n → ∀ g : Sp F,
      g * fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) g = 1 →
      ∃ h : Sp F, g = h * (fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) h)⁻¹)
    (hgraph : Odd n → ∀ g : Sp F,
      g * (ExceptionalGraph.graphAut ^ n) g = 1 →
      ∃ h : Sp F, g = h * ((ExceptionalGraph.graphAut ^ n) h)⁻¹)

include hF hn hfield hgraph

/-- An elementary group containing a noninner automorphism has rank at most `2*n+1`. -/
theorem elementary_outer_rank_le
    (E : Subgroup (MulAut (Sp F))) (hE : IsElementaryAbelian 2 E)
    (hi : ¬ E ≤ MulAut.innerSubgroup (Sp F)) :
    primeRank 2 E ≤ 2 * n + 1 := by
  have hclass := SemilinearClassification.inner_field_of_preservesDiagram (F := F)
  let := ExceptionalGraph.outer_isCyclic_of_card hF (by omega) hclass
  apply elementary_rank_le_of_fixed (n := n) ?_ E hE hi
  intro a ha hi
  rcases involution_normalForms_of_coboundaries hF hn hclass hfield hgraph a ha
    with hinner | houter
  · obtain ⟨g, _, rfl⟩ := hinner
    exact False.elim (hi ⟨g, rfl⟩)
  · apply outer_fixed_rank_le_of_models hF (by omega) ?_ a houter
    intro m hm
    subst n
    exact ⟨suzukiFixedEquiv m hF⟩

/-- Every such group has strictly smaller order than a symplectic Sylow wing. -/
theorem elementary_outer_card_lt
    (E : Subgroup (MulAut (Sp F))) (hE : IsElementaryAbelian 2 E)
    (hi : ¬ E ≤ MulAut.innerSubgroup (Sp F)) :
    Nat.card E < 2 ^ (3 * n) := by
  have hr := elementary_outer_rank_le hF hn hfield hgraph E hE hi
  let := hE
  have htop : IsElementaryAbelian 2 (⊤ : Subgroup E) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) x.val)) }
  have hc := (primeRank_le_iff_elementary_card_le E).mp hr ⊤ htop
  have hc' : Nat.card E ≤ 2 ^ (2 * n + 1) := by
    simpa only [Nat.card_congr Subgroup.topEquiv.toEquiv] using hc
  exact hc'.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
end Theory.SpecificGroups.SymplecticFour.EvenTwoRank.OuterMaximum
