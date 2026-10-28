module

public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Parabolics
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Coverage
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.LocalClassification

/-!
# Native classification of solvable-normal Sylow overgroups in M₂₂

A subgroup containing an ambient Sylow two-subgroup and a relatively normal
solvable subgroup of order divisible by three is conjugate to one of the two
native hexad parabolics. It has order 384, contains the pointwise kernel of
an invariant hexad, and is an ordinary maximal subgroup of that hexad's
stabilizer. Its normalizer in the full design group stabilizes the same hexad.

The solvable normal seed rules out transitivity in degree 22. Geometric
coverage then places the overgroup in a pair or hexad stabilizer, and the
genuine S₅ or A₆ restriction quotient gives order 384 and hexad placement.
The two A₆ parabolics lift through the pointwise kernel to actual M₂₂
conjugates. The pair–hexad intersection and the three-pair stabilizer are
not conjugate in M₂₂; both alternatives are retained. Uniqueness of the
invariant hexad gives the full design-normalizer containment.

Source: the native subgroup step of Aschbacher–Smith 13.8.21(2), printed
p.956 (PDF p.973). Transport from the source's component quotient and its
outer supplement remains with the source assembly.
-/

public section
open Subgroup MulAction
open scoped Pointwise
namespace Sporadic.Mathieu.M22SolvableSylow

/-- The solvable normal seed excludes the full simple Mathieu group. -/
theorem ne_top_of_solvable_normal_three (X D : Subgroup M22) (hle : D ≤ X)
    (hn : (D.subgroupOf X).Normal) (hs : Group.IsSolvable D) (hthree : 3 ∣ Nat.card D) :
    X ≠ ⊤ := by
  intro he
  have hnorm : D.Normal := by
    apply normalizer_eq_top_iff.mp
    have h := (normal_subgroupOf_iff_le_normalizer hle).mp hn
    rw [he] at h
    exact top_le_iff.mp h
  let := m22_isSimpleGroup
  rcases hnorm.eq_bot_or_eq_top with hbot | htop
  · rw [hbot, Subgroup.card_bot] at hthree
    norm_num at hthree
  · let := hs
    let : Group.IsSolvable M22 := Group.isSolvable_of_surjective
      (f := ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).toMonoidHom)
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).surjective
    have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr
      (inferInstance : Group.IsSolvable M22)
    have h := congrArg Subtype.val (hcomm m22GeneratorAInM22 m22GeneratorBInM22)
    exact (by decide +kernel : m22GeneratorA * m22GeneratorB ≠
      m22GeneratorB * m22GeneratorA) h


/-- The geometric conclusions follow from placement and the order calculation. -/
theorem hexad_conclusions_of_card {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (X : Subgroup M22) (hX : X ≤ stabilizer M22 B) (hc : Nat.card X = 384)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) :
    IsCoatom (X.subgroupOf (stabilizer M22 B)) ∧
    m22HexadPointwiseKernel B ≤ X ∧
    normalizer (X.map M22ValueBound.Concrete.inclusion : Set m22DesignAut) ≤
      stabilizer m22DesignAut B := by
  obtain ⟨U, hU⟩ := hU
  have hk := (kernel_le_of_sylow hB U (hU.trans hX)).trans hU
  exact ⟨isCoatom_of_card_384 hB X hX hk hc, hk,
    normalizer_le_hexad_stabilizer hB X hX hk⟩

/-- The native inputs alone force order 384, in both geometric branches. -/
theorem card_eq_384_of_solvable_normal_three (X D : Subgroup M22) (hle : D ≤ X)
    (hn : (D.subgroupOf X).Normal) (hs : Group.IsSolvable D) (hthree : 3 ∣ Nat.card D)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) : Nat.card X = 384 :=
  LocalClassification.order_of_geometric_placement X D hle hn hs hthree hU
    (geometric_coverage X D hle hn hs hthree hU)

/-- The entire Sylow overgroup is solvable. -/
theorem solvable_of_solvable_normal_three (X D : Subgroup M22) (hle : D ≤ X)
    (hn : (D.subgroupOf X).Normal) (hs : Group.IsSolvable D) (hthree : 3 ∣ Nat.card D)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) : Group.IsSolvable X :=
  solvable_of_card_384 X (card_eq_384_of_solvable_normal_three X D hle hn hs hthree hU) hU

/-- Every native Sylow overgroup with the stated solvable normal seed is an
actual M₂₂ conjugate of one of the two distinct hexad parabolics. No geometric
placement or order is assumed. -/
theorem conjugacy_of_solvable_normal_three (X D : Subgroup M22) (hle : D ≤ X)
    (hn : (D.subgroupOf X).Normal) (hs : Group.IsSolvable D) (hthree : 3 ∣ Nat.card D)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) :
    ∃ g : M22, X = pairHexad.map (MulAut.conj g).toMonoidHom ∨
      X = M22ValueBound.Concrete.second.map (MulAut.conj g).toMonoidHom :=
  LocalClassification.conjugacy_of_geometric_placement X D hle hn hs hthree hU
    (geometric_coverage X D hle hn hs hthree hU)

/-- Native parabolic placement, ordinary maximality, kernel containment and
order, with the normalizer in the full design group preserving the same hexad.
Normality of the solvable seed is required only inside X. -/
theorem hexad_of_solvable_normal_three (X D : Subgroup M22) (hle : D ≤ X)
    (hn : (D.subgroupOf X).Normal) (hs : Group.IsSolvable D) (hthree : 3 ∣ Nat.card D)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) :
    ∃ B ∈ m22Blocks, X ≤ stabilizer M22 B ∧
      IsCoatom (X.subgroupOf (stabilizer M22 B)) ∧
      m22HexadPointwiseKernel B ≤ X ∧ Nat.card X = 384 ∧
      normalizer (X.map M22ValueBound.Concrete.inclusion : Set m22DesignAut) ≤
        stabilizer m22DesignAut B := by
  have hplace := geometric_coverage X D hle hn hs hthree hU
  obtain ⟨B, hB, hXB⟩ :=
    LocalClassification.hexad_of_geometric_placement X D hle hn hs hthree hU hplace
  have hc := LocalClassification.order_of_geometric_placement X D hle hn hs hthree hU hplace
  obtain ⟨hmax, hk, hnB⟩ := hexad_conclusions_of_card hB X hXB hc hU
  exact ⟨B, hB, hXB, hmax, hk, hc, hnB⟩

end Sporadic.Mathieu.M22SolvableSylow
