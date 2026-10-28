module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.SimpleCoordinates

/-!
# The actual simple root chart on a punctured endpoint panel

For each original endpoint Pᵢ and any representative nᵢ in the actual N,
the map r ↦ r nᵢ B carries the same simple root Xᵢ bijectively onto the
literal coset space Pᵢ/B with its base coset removed. Injectivity follows
from Xᵢ ∩ B^sᵢ = 1; the proved index formula gives surjectivity by finite
counting. The chart is independent of the chosen representative modulo
the entire H. These are equivalences of sets, with no normality of B in
Pᵢ and no group structure on the panel being asserted.

Source: Carter §2.5, especially 2.5.11 and the simple Bruhat cell, in
`refs/KGroup/GLS3/Chapter2Ca2.tex`. This is the actual root/panel regularity
input consumed by the marked quotient recognition argument, not merely
an abstract equality of group orders. Right conjugation is retained.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (d : MarkedQuotient P) (split : SplitData d.tits)

theorem simpleRoot_disjoint_conjugateBorel (i : Fin 2) :
    Disjoint (simpleRoot d split i) (borelConjugate (d.simple i)) := by
  apply disjoint_iff.mpr
  apply eq_bot_iff.mpr
  intro x hx
  let n₀ := representative (longest d)
  let ns := representative (d.simple i)
  have hxR := hx.1.2
  rw [unipotentConjugate_eq split _ (n₀*ns)
    (by rw [map_mul, representative_spec, representative_spec])] at hxR
  have hzero : (ns : X ⧸ d.D) * x * (ns : X ⧸ d.D)⁻¹ ∈
      d.tits.B ⊓ unipotentConjugate split (longest d) := by
    refine ⟨hx.2, ?_⟩
    change (n₀ : X ⧸ d.D) * ((ns : X ⧸ d.D) * x * (ns : X ⧸ d.D)⁻¹) *
      (n₀ : X ⧸ d.D)⁻¹ ∈ split.U
    change ((n₀ : X ⧸ d.D) * (ns : X ⧸ d.D)) * x *
      ((n₀ : X ⧸ d.D) * (ns : X ⧸ d.D))⁻¹ ∈ split.U at hxR
    simpa only [mul_inv_rev, mul_assoc] using hxR
  rw [borel_inf_opposite_unipotent d split, mem_bot] at hzero
  apply (MulAut.conj (ns : X ⧸ d.D)).injective
  simpa only [MulAut.conj_apply, map_one] using hzero

/-- The literal panel is the coset space of the entire Borel inside Pᵢ. -/
abbrev Panel (i : Fin 2) := d.tits.standardParabolic {d.simple i} ⧸
  d.tits.B.subgroupOf (d.tits.standardParabolic {d.simple i})

/-- The original Borel coset, removed for the root-group chart. -/
def panelBase (i : Fin 2) : Panel d i := QuotientGroup.mk 1

/-- The punctured literal panel, with no quotient-normality assertion. -/
abbrev PuncturedPanel (i : Fin 2) := {c : Panel d i // c ≠ panelBase d i}

private def panelRepresentative (i : Fin 2) (n : d.tits.N)
    (hn : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) n = d.simple i)
    (r : simpleRoot d split i) : d.tits.standardParabolic {d.simple i} :=
  ⟨(r : X ⧸ d.D) * n, (d.tits.standardParabolic {d.simple i}).mul_mem
    (d.tits.B_le_standardParabolic _ (split.U_le r.property.1))
    (d.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
      (d.tits.representative_mem_bruhatCell _ n hn))⟩

private theorem panelRepresentative_ne_base (i : Fin 2) (n : d.tits.N)
    (hn : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) n = d.simple i)
    (r : simpleRoot d split i) :
    QuotientGroup.mk (panelRepresentative d split i n hn r) ≠ panelBase d i := by
  intro he
  have hm := QuotientGroup.eq.mp he.symm
  change (1 : X ⧸ d.D)⁻¹ * ((r : X ⧸ d.D) * n) ∈ d.tits.B at hm
  simp only [inv_one, one_mul] at hm
  have hnB : (n : X ⧸ d.D) ∈ d.tits.B := by
    have h := d.tits.B.mul_mem (d.tits.B.inv_mem (split.U_le r.property.1)) hm
    simpa only [inv_mul_cancel_left] using h
  have hq := (QuotientGroup.eq_one_iff n).mpr
    (show n ∈ (d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N from ⟨hnB,n.property⟩)
  exact (d.tits.involutions _ (d.simple_mem i)).1 (hn.symm.trans hq)

/-- The root chart is literally `r ↦ r*n*B` for any lift of the original sᵢ. -/
def simplePanelMap (i : Fin 2) (n : d.tits.N)
    (hn : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) n = d.simple i) :
    simpleRoot d split i → PuncturedPanel d i :=
  fun r => ⟨QuotientGroup.mk (panelRepresentative d split i n hn r),
    panelRepresentative_ne_base d split i n hn r⟩

@[simp] theorem simplePanelMap_apply (i : Fin 2) (n : d.tits.N)
    (hn : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) n = d.simple i)
    (r : simpleRoot d split i)
    (hP : (r : X ⧸ d.D) * n ∈ d.tits.standardParabolic {d.simple i}) :
    (simplePanelMap d split i n hn r).val = QuotientGroup.mk
      (⟨(r : X ⧸ d.D) * n, hP⟩ :
        d.tits.standardParabolic {d.simple i}) := by rfl

theorem simplePanelMap_injective (i : Fin 2) (n : d.tits.N)
    (hn : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) n = d.simple i) :
    Function.Injective (simplePanelMap d split i n hn) := by
  intro r t he
  have hm := QuotientGroup.eq.mp (congrArg Subtype.val he)
  change ((r : X ⧸ d.D) * n)⁻¹ * ((t : X ⧸ d.D) * n) ∈ d.tits.B at hm
  have hni : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) n⁻¹ = d.simple i := by
    rw [map_inv, hn]
    exact inv_eq_of_mul_eq_one_right
      (by simpa only [pow_two] using (d.tits.involutions _ (d.simple_mem i)).2)
  have hb : (r : X ⧸ d.D)⁻¹ * t ∈ borelConjugate (d.simple i) := by
    rw [borelConjugate_eq _ n⁻¹ hni]
    change (n : X ⧸ d.D)⁻¹ * ((r : X ⧸ d.D)⁻¹ * t) * ((n : X ⧸ d.D)⁻¹)⁻¹ ∈ d.tits.B
    simpa only [mul_inv_rev, mul_assoc, inv_inv] using hm
  have hz : (r : X ⧸ d.D)⁻¹ * t = 1 := by
    apply mem_bot.mp
    rw [← disjoint_iff.mp (simpleRoot_disjoint_conjugateBorel d split i)]
    exact ⟨(simpleRoot d split i).mul_mem ((simpleRoot d split i).inv_mem r.property) t.property, hb⟩
  exact Subtype.ext (inv_mul_eq_one.mp hz)

private theorem nat_card_ne {A : Type*} [Finite A] (a : A) :
    Nat.card {x : A // x ≠ a} = Nat.card A - 1 := by
  classical
  let : Fintype A := Fintype.ofFinite A
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

theorem puncturedPanel_card (i : Fin 2) :
    Nat.card (PuncturedPanel d i) = Nat.card (simpleRoot d split i) := by
  rw [nat_card_ne]
  change (d.tits.B.subgroupOf (d.tits.standardParabolic {d.simple i})).index - 1 = _
  rw [singleton_parabolic_root_index d split i]
  omega

/-- Actual root regularity on the punctured panel, stronger than cardinal equality. -/
theorem simplePanelMap_bijective (i : Fin 2) (n : d.tits.N)
    (hn : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) n = d.simple i) :
    Function.Bijective (simplePanelMap d split i n hn) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  exact ⟨simplePanelMap_injective d split i n hn, (puncturedPanel_card d split i).symm⟩

/-- The root chart on the actual literal panel as an equivalence of types. -/
def simplePanelCoordinates (i : Fin 2) (n : d.tits.N)
    (hn : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) n = d.simple i) :
    simpleRoot d split i ≃ PuncturedPanel d i :=
  Equiv.ofBijective (simplePanelMap d split i n hn) (simplePanelMap_bijective d split i n hn)

@[simp] theorem simplePanelCoordinates_apply (i : Fin 2) (n : d.tits.N)
    (hn : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) n = d.simple i)
    (r : simpleRoot d split i) :
    simplePanelCoordinates d split i n hn r = simplePanelMap d split i n hn r := by rfl

/-- Changing the chosen lift by the entire original H leaves the chart unchanged. -/
theorem simplePanelMap_independent (i : Fin 2) (n m : d.tits.N)
    (hn : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) n = d.simple i)
    (hm : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) m = d.simple i) :
    simplePanelMap d split i n hn = simplePanelMap d split i m hm := by
  funext r
  apply Subtype.ext
  apply QuotientGroup.eq.mpr
  have hnm := QuotientGroup.eq.mp (hn.trans hm.symm)
  change ((n : X ⧸ d.D)⁻¹ * m) ∈ d.tits.B ⊓ d.tits.N at hnm
  change ((r : X ⧸ d.D)*n)⁻¹ * ((r : X ⧸ d.D)*m) ∈ d.tits.B
  simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using
    (show (n : X ⧸ d.D)⁻¹*m ∈ d.tits.B from hnm.1)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
