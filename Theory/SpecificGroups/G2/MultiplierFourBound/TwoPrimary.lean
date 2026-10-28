module

public import Theory.SpecificGroups.G2.FiniteUniversalCover
public import Theory.SpecificGroups.G2.MultiplierFourBound.TwoPrimary.RootDefects
public import Theory.SpecificGroups.G2.MultiplierOrdinary.UnipotentSection
public import Theory.GroupTheory.PerfectCentralCoverLocalSplitting

/-!
# The local splitting reduction for the G₂(4) two-primary bound

The literal six-root unipotent subgroup has odd index. If quotienting a
perfect central cover by a kernel subgroup D of order at most two makes its
positive-root multiplication lift, transfer shows that the quotient kernel
has odd order. The exact cardinality comparison then excludes divisibility
by four in the original kernel, without any assumption on its odd part.

The final theorem specializes this reduction to the canonical universal
projection on the actual octonion model. The exceptional lifted relations
and the construction of D are still explicit premises. The ordinary-field
root-lifting theorem excludes GF(4), so it cannot supply these premises.

Source: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407 (PDF p.418), and
GLS III §6.1, Tables 6.1.2–6.1.3. The remaining exceptional calculation is
in R. L. Griess, *Schur multipliers of finite simple groups of Lie type*,
Trans. AMS 183 (1973), 355–421, especially pp.357–371,
DOI 10.1090/S0002-9947-1973-0338148-0.
The imported octonion roots retain their ATLAS attribution.
-/

namespace Atlas.G2.FiniteCover.MultiplierFourBound.TwoPrimary

open PerfectCentralCovering MultiplierOrdinary

variable {E : Type*} [Group E] [Finite E]

/-- Splitting the actual positive-unipotent subgroup modulo a small central
kernel subgroup bounds the two-primary part of the full kernel. -/
public theorem not_four_dvd_card_kernel_of_quotient_section
    (c : Cover E FourBase) (D : Subgroup E) [D.Normal]
    (hD : D ≤ c.toMonoidHom.ker) (hcard : Nat.card D ≤ 2)
    (s : unipotent (K := FourField) →* E ⧸ D)
    (hs : (c.quotientKernelSubgroup D hD).toMonoidHom.comp s =
      (unipotent (K := FourField)).subtype) :
    ¬ 4 ∣ Nat.card c.toMonoidHom.ker := by
  intro h
  have hd : 4 ∣ Nat.card D :=
    (c.prime_pow_dvd_kernel_iff_of_quotient_section D hD
      (unipotent (K := FourField))
      LieParabolicSetup.unipotent_index_odd.not_two_dvd_nat s hs 2).mp h
  have hpos : 0 < Nat.card D := Nat.card_pos
  have := Nat.le_of_dvd hpos hd
  omega

/-- The existing ordered six-root normal form turns compatible lifted
relations in the quotient into the local section required by transfer. -/
public theorem not_four_dvd_card_kernel_of_quotient_positive_relations
    (c : Cover E FourBase) (D : Subgroup E) [D.Normal]
    (hD : D ≤ c.toMonoidHom.ker) (hcard : Nat.card D ≤ 2)
    (L : RootSections (c.quotientKernelSubgroup D hD).toMonoidHom)
    (hL : L.ProductCompatible) :
    ¬ 4 ∣ Nat.card c.toMonoidHom.ker := by
  obtain ⟨s, hs⟩ := L.exists_unipotent_section hL
  exact not_four_dvd_card_kernel_of_quotient_section c D hD hcard s hs

/-- The reduction on the literal universal kernel. Its extra local lifting
premises remain to be constructed; this is not the unconditional table entry. -/
public theorem not_four_dvd_card_universal_kernel_of_quotient_positive_relations
    (D : Subgroup FourCover) [D.Normal]
    (hD : D ≤ (universalProjection FourBase).ker) (hcard : Nat.card D ≤ 2)
    (L : RootSections ((universalCover FourBase).quotientKernelSubgroup D hD).toMonoidHom)
    (hL : L.ProductCompatible) :
    ¬ 4 ∣ Nat.card (Kernel FourField) :=
  not_four_dvd_card_kernel_of_quotient_positive_relations
    (universalCover FourBase) D hD hcard L hL

end Atlas.G2.FiniteCover.MultiplierFourBound.TwoPrimary
