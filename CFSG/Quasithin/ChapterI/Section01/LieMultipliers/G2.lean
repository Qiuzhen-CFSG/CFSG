module

public import Theory.SpecificGroups.G2.FiniteUniversalCover
public import Theory.SpecificGroups.G2.MultiplierFourBound
public import Theory.GroupTheory.CoveringKernelTwo
public import Theory.GroupTheory.CoveringKernelEquiv

/-!
# G₂ universal covers and the field-four multiplier reduction

The finite universal covers use the actual split-octonion automorphism model.
For the quasisimple source group L in I.2.2(5), its given identification
L/Z(L) ≃ G₂(4) defines a surjective covering with kernel exactly Z(L).
If the universal kernel has order at most two, the nontriviality of Z(L)
forces this covering to be universal with cyclic kernel of order two.
Comparison then identifies the kernel of the canonical universal cover too.

The upper bound remains an explicit independent mathematical input. For the
unconditional I.1.3(1) table entry one must also construct a nontrivial cover;
the I.2.2 consumer already supplies such an L. Neither task is replaced by
the existence of the finite universal cover proved in the imported module.

Source: Aschbacher–Smith, A.2.2–A.2.4, printed p.33 (PDF p.44), and
I.1.3(1), I.1.4(2), I.2.2(5), printed pp.407–411 (PDF pp.418–422).
The other required rows remain the C₃ multiplier of G₂(3), trivial kernels
for G₂(2^f), f ≥ 3, and G₂(p), odd prime p > 3. The G₂(2)′ endpoint uses
the actual PSU₃(3) comparison, never the nonsimple full group G₂(2).
-/

namespace CFSG.Quasithin.ChapterI.LieMultipliers.G2

open Theory.GroupTheory PerfectCentralCovering Atlas.G2.FiniteCover

universe w

variable {L : Type} [Group L] [Finite L] [IsQuasisimple L]

/-- The source covering retains the literal quotient map by the center. -/
@[expose] public noncomputable def fourSourceCover (e : L ⧸ Subgroup.center L ≃* FourBase) :
    Covering L FourBase where
  toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)

/-- Its kernel is precisely the source center, without a splitting assumption. -/
public theorem fourSourceCover_ker (e : L ⧸ Subgroup.center L ≃* FourBase) :
    (fourSourceCover e).toMonoidHom.ker = Subgroup.center L :=
  (fourSourceCover e).ker_eq_center_of_isSimple

/-- Conditional I.2.2(5) application: the upper bound alone suffices when
the source already gives an actual quasisimple group with nontrivial center. -/
public theorem fourSourceCover_universal_of_bound
    (e : L ⧸ Subgroup.center L ≃* FourBase) (hZ : Subgroup.center L ≠ ⊥)
    (hbound : Nat.card (Kernel FourField) ≤ 2) :
    Covering.IsUniversal.{0, 0, w} (fourSourceCover e) ∧
      Nonempty (Subgroup.center L ≃* Multiplicative (ZMod 2)) := by
  have hne : (fourSourceCover e).toMonoidHom.ker ≠ ⊥ := by
    rwa [fourSourceCover_ker e]
  obtain ⟨hu, ⟨a⟩⟩ := Covering.isUniversal_and_kernel_equiv_two_of_bound
    (fourSourceCover e) hne hbound
  exact ⟨hu, ⟨(MulEquiv.subgroupCongr (fourSourceCover_ker e).symm).trans a⟩⟩

/-- The same source cover supplies the lower bound for the canonical kernel.
The nontrivial-cover construction and upper-bound proof are independent inputs. -/
public theorem fourKernel_equiv_two_of_source_cover
    (e : L ⧸ Subgroup.center L ≃* FourBase) (hZ : Subgroup.center L ≠ ⊥)
    (hbound : Nat.card (Kernel FourField) ≤ 2) :
    Nonempty (Kernel FourField ≃* Multiplicative (ZMod 2)) := by
  obtain ⟨hu, ⟨a⟩⟩ := fourSourceCover_universal_of_bound.{0} e hZ hbound
  let k := (cover_isUniversal FourField).kerMulEquiv hu (MulEquiv.refl FourBase)
  exact ⟨k.trans ((MulEquiv.subgroupCongr (fourSourceCover_ker e)).trans a)⟩

/-- The primary reduction discharges every prime other than 2, 3 and 5.
The odd exclusions and the two-primary bound remain separate source inputs. -/
public theorem fourSourceCover_universal_of_primary_bounds
    (e : L ⧸ Subgroup.center L ≃* FourBase) (hZ : Subgroup.center L ≠ ⊥)
    (h3 : ¬ 3 ∣ Nat.card (Kernel FourField))
    (h5 : ¬ 5 ∣ Nat.card (Kernel FourField))
    (h4 : ¬ 4 ∣ Nat.card (Kernel FourField)) :
    Covering.IsUniversal.{0, 0, w} (fourSourceCover e) ∧
      Nonempty (Subgroup.center L ≃* Multiplicative (ZMod 2)) :=
  fourSourceCover_universal_of_bound e hZ
    (MultiplierFourBound.card_kernel_le_two_of_primary_bounds h3 h5 h4)

end CFSG.Quasithin.ChapterI.LieMultipliers.G2
