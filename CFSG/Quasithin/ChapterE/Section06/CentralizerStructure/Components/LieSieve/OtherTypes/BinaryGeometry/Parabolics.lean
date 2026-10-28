module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.BinaryGeometry.ModelAction
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.Defs

/-!+# The binary parabolics and their actual quotient images

In dimension four the two end parabolics stabilize a line and a hyperplane
of one complete flag. In dimension five the two partial flags have dimensions
(1,4) and (2,3); both sets of cuts are preserved by diagram reversal.
Their images below are taken through the actual inclusion of L into LQ_L
and its two-core quotient, after the binary model comparison.

The generation calculation and the exclusion of relatively subnormal blocks
can be proved independently for these fixed subgroups. The definitions do
not assert either property. The final conversion theorem joins those two
inputs into the precise family required by OtherTypes.Setup.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), the invariant-parabolic argument.
-/

@[expose] public section

open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.BinaryGeometry

/-- The actual line and hyperplane stabilizers of a binary four-dimensional flag. -/
noncomputable def fourEndParabolic (b : BinaryLinear.InvariantNodeActions.Basis 3)
    (i : Fin 2) : Subgroup (LinearGroup 4) :=
  BinaryLinear.parabolic (BinaryLinear.InvariantNodeActions.cutSpace b
    (if i = 0 then 0 else 2))

/-- The two partial flags invariant under reversal in binary five-space. -/
noncomputable def fivePairedParabolic (b : BinaryLinear.FiveFlagGeometry.FiveBasis)
    (i : Fin 2) : Subgroup (LinearGroup 5) :=
  BinaryLinear.FiveFlagGeometry.flagStabilizer b
    (if i = 0 then {0, 3} else {1, 2})

variable {G : Type*} [Group G] {Q L : Subgroup G} {n : ℕ}

/-- Map the binary model into the literal component quotient. -/
noncomputable def modelQuotientMap (Q : Subgroup G) (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL L n 2) : LinearGroup n →* ComponentQuotient Q L :=
  (quotientMap Q L).comp
    ((inclusion (show L ≤ componentExtension Q L from le_sup_left)).comp
      (binaryEquiv hn hm).symm.toMonoidHom)

/-- The quotient subgroup retains its embedding, rather than only its isomorphism type. -/
noncomputable def quotientParabolic (Q : Subgroup G) (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL L n 2) (P : Subgroup (LinearGroup n)) :
    Subgroup (ComponentQuotient Q L) := P.map (modelQuotientMap Q hn hm)

theorem modelQuotientMap_range (Q : Subgroup G) (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL L n 2) :
    (modelQuotientMap Q hn hm).range = componentImage Q L := by
  rw [modelQuotientMap, MonoidHom.range_comp, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (binaryEquiv hn hm).symm.surjective,
    ← MonoidHom.range_eq_map, inclusion_range]
  rfl

theorem quotientParabolic_le_component (Q : Subgroup G) (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL L n 2) (P : Subgroup (LinearGroup n)) :
    quotientParabolic Q hn hm P ≤ componentImage Q L := by
  rw [← modelQuotientMap_range Q hn hm]
  exact map_le_range (modelQuotientMap Q hn hm) P

/-- Model generation transports through the actual component quotient map. -/
theorem quotientParabolic_generate (Q : Subgroup G) (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL L n 2) {ι : Sort*} (P : ι → Subgroup (LinearGroup n))
    (hgen : (⨆ i, P i) = ⊤) : componentImage Q L ≤ ⨆ i, quotientParabolic Q hn hm (P i) := by
  rw [← modelQuotientMap_range Q hn hm, MonoidHom.range_eq_map, ← hgen, Subgroup.map_iSup]
  exact le_rfl

/-- Assemble the geometric calculation and the independent block exclusion.
The final source theorem must construct all four supplied properties. -/
noncomputable def blockFreeFamilyOfParabolics (Q : Subgroup G) (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL L n 2) {k : ℕ} (P : Fin k → Subgroup (LinearGroup n))
    (hgen : (⨆ i, P i) = ⊤)
    (hinv : ∀ i, sylowImage Q L ≤
      normalizer (quotientParabolic Q hn hm (P i) : Set (ComponentQuotient Q L)))
    (hchar : ∀ i, HasCharacteristicTwo
      ↥(quotientPreimage Q L (quotientParabolic Q hn hm (P i)) ⊔ Q))
    (hfree : ∀ i, NoChiZeroBlocks
      (quotientPreimage Q L (quotientParabolic Q hn hm (P i)) ⊔ Q)) :
    BlockFreeQuotientFamily Q L where
  count := k
  subgroup i := quotientParabolic Q hn hm (P i)
  le_component i := quotientParabolic_le_component Q hn hm (P i)
  invariant := hinv
  characteristic_two := hchar
  no_blocks := hfree
  generate := quotientParabolic_generate Q hn hm P hgen

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.BinaryGeometry
