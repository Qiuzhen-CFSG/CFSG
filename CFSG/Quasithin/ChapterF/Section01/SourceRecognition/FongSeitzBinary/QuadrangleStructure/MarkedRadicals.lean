module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.RootCommutators
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.MarkedCores

/-!
# Original Sylow quotients and marked quadrangle radicals

The full original S maps isomorphically to the specified split U. The
same map carries each full original parabolic two-core onto the marked
core. Projecting a canonical simple root into S/O₂(P_i) is injective:
the kernel lies in the complementary section and that section is disjoint
from the root. Thus elementary Sylow quotients give elementary actual roots
without perfectness or a restriction on the local field order.

In a quadrangle, the root commutator is then exactly the image of the
original opposite parabolic core's derived subgroup. The earlier derived
order, together with the full-Borel index, gives equality with the required
crossed root. These are literal transports through the supplied endpoint
and overlap maps, also valid for an independently marked geometric quotient.

Source: DGS (11.5), (11.7), pp.173--175, and reduction pp.95--96;
Fong--Seitz I (3G), (5C), (6A), pp.14--16,26,37--38. The Chapter 11
quotient clauses remain earlier-source premises. The general derived-order
premise is a separate local obligation: the nonzero containment of (11.3)
does not establish it without an additional action argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

omit Q e h split in
/-- Normality is relative to the original S, not asserted in the ambient group. -/
theorem original_core_normal_in_sylow (i : Fin 2) :
    (((parabolic L S i).pCoreIn 2).subgroupOf S).Normal := by
  have hn : parabolic L S i ≤ normalizer ((parabolic L S i).pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 (parabolic L S i)).le_normalizer_map (parabolic L S i).subtype
  exact normal_subgroupOf_of_le_normalizer
    ((show S ≤ parabolic L S i from le_sup_right.trans le_sup_left).trans hn)

private theorem sylowMap_injective : Function.Injective (MarkedLocal.sylowMap Q e h) :=
  Q.tits.B.subtype_injective.comp
    (((MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm).trans e.middle).injective.comp
      (inclusion_injective _))

/-- The actual full-overlap marking restricted to the original Sylow subgroup. -/
def markedSylowEquiv : S ≃* split.U :=
  (MonoidHom.ofInjective (sylowMap_injective Q e h)).trans
    (MulEquiv.subgroupCongr (MarkedLocal.sylow_range Q e h split))

@[simp] theorem markedSylowEquiv_apply (s : S) :
    (markedSylowEquiv Q e h split s : X ⧸ Q.D) = MarkedLocal.sylowMap Q e h s := by rfl

include e h in
/-- The full original core follows the very same S map. -/
theorem marked_sylow_core_map (i : Fin 2) :
    (((parabolic L S i).pCoreIn 2).subgroupOf S).map (MarkedLocal.sylowMap Q e h) =
      (Q.tits.standardParabolic {Q.simple i}).pCoreIn 2 := by
  rw [← marked_core_map Q e i]
  ext x
  constructor
  · rintro ⟨s,hs,rfl⟩
    exact ⟨⟨s,(show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) s.property⟩,
      hs,MarkedLocal.endpoint_sylow Q e h i s⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨a,h.parabolic_core_le_S i ha⟩,ha,
      (MarkedLocal.endpoint_sylow Q e h i ⟨a,h.parabolic_core_le_S i ha⟩).symm⟩

include e h in
/-- Elementary abelianness comes from the original Sylow quotient, without perfectness. -/
theorem marked_simpleRoot_elementary_of_original_quotient (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (hc : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S)) :
    IsElementaryAbelian 2 (simpleRoot Q split i) := by
  let := original_core_normal_in_sylow (L := L) (S := S) i
  let := hc
  let a := markedSylowEquiv Q e h split
  let f : simpleRoot Q split i →* S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S :=
    (QuotientGroup.mk' _).comp (a.symm.toMonoidHom.comp (inclusion (simpleRoot_le Q split i)))
  apply IsElementaryAbelian.of_injective f
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply eq_bot_iff.mpr
  intro r hr
  have hs : a.symm ⟨r,simpleRoot_le Q split i r.property⟩ ∈
      ((parabolic L S i).pCoreIn 2).subgroupOf S := (QuotientGroup.eq_one_iff _).mp hr
  have hcore : (r : X ⧸ Q.D) ∈ (Q.tits.standardParabolic {Q.simple i}).pCoreIn 2 := by
    rw [← marked_sylow_core_map Q e h i]
    refine ⟨a.symm ⟨r,simpleRoot_le Q split i r.property⟩,hs,?_⟩
    change (a (a.symm ⟨r,simpleRoot_le Q split i r.property⟩) : X ⧸ Q.D) = r
    rw [a.apply_symm_apply]
  have hrem : (r : X ⧸ Q.D) ∈ simpleRemainder Q split i :=
    (marked_remainder_eq_core Q e h split i hV).symm ▸ hcore
  apply Subtype.ext
  exact (disjoint_iff.mp (simpleRoot_disjoint_remainder Q split i)).le ⟨r.property,hrem⟩

include e h in
/-- The original core-derived subgroup maps onto the exact root commutator. -/
theorem marked_core_derived_map (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hQj : letI := original_core_normal_in_sylow (L := L) (S := S) j
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S j).pCoreIn 2).subgroupOf S)) :
    (⁅((parabolic L S i).pCoreIn 2).subgroupOf S,
      ((parabolic L S i).pCoreIn 2).subgroupOf S⁆).map (MarkedLocal.sylowMap Q e h) =
        ⁅simpleRoot Q split j, rootAt Q split j (Q.simple i)⁆ := by
  rw [map_commutator, marked_sylow_core_map Q e h i,
    ← marked_remainder_eq_core Q e h split i hVi]
  exact (Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.remainder_derived_frattini
    Q split hm i j hij hVi hVj
    (marked_simpleRoot_elementary_of_original_quotient Q e h split i hVi hQi)
    (marked_simpleRoot_elementary_of_original_quotient Q e h split j hVj hQj)).1
include e h in
/-- The derived order belongs to the original full core, with no central kernel lost. -/
theorem marked_remainder_derived_card (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    Nat.card (⁅simpleRemainder Q split i, simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) =
      Nat.card (⁅(parabolic L S i).pCoreIn 2,(parabolic L S i).pCoreIn 2⁆ : Subgroup G) := by
  let A := ((parabolic L S i).pCoreIn 2).subgroupOf S
  have hm : A.map (MarkedLocal.sylowMap Q e h) = simpleRemainder Q split i :=
    (marked_sylow_core_map Q e h i).trans (marked_remainder_eq_core Q e h split i hV).symm
  have ha : A.map S.subtype = (parabolic L S i).pCoreIn 2 :=
    map_subgroupOf_eq_of_le (h.parabolic_core_le_S i)
  calc
    Nat.card (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) =
        Nat.card ((⁅A,A⁆ : Subgroup S).map (MarkedLocal.sylowMap Q e h)) := by rw [map_commutator,hm]
    _ = Nat.card (⁅A,A⁆ : Subgroup S) := card_map_of_injective (sylowMap_injective Q e h)
    _ = Nat.card ((⁅A,A⁆ : Subgroup S).map S.subtype) := (card_map_of_injective S.subtype_injective).symm
    _ = _ := by rw [map_commutator,ha]

include e h in
/-- The complementary section has the order of the full original core. -/
theorem marked_remainder_card (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    Nat.card (simpleRemainder Q split i) = Nat.card ((parabolic L S i).pCoreIn 2) := by
  rw [marked_remainder_eq_core Q e h split i hV, ← marked_sylow_core_map Q e h i,
    card_map_of_injective (sylowMap_injective Q e h)]
  exact Nat.card_congr (subgroupOfEquivOfLe (h.parabolic_core_le_S i)).toEquiv

include e h in
/-- The original derived order and quotient-elementarity clauses give the
exact crossed-root equality in the same marked quotient. -/
theorem marked_cross_root_commutator_eq (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hQj : letI := original_core_normal_in_sylow (L := L) (S := S) j
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S j).pCoreIn 2).subgroupOf S))
    (q : ℕ)
    (hindex : (commonBorel L S).relIndex (parabolic L S i) = q + 1)
    (hderived : Nat.card (⁅(parabolic L S i).pCoreIn 2,
      (parabolic L S i).pCoreIn 2⁆ : Subgroup G) = q) :
    ⁅simpleRoot Q split j, rootAt Q split j (Q.simple i)⁆ = rootAt Q split i (Q.simple j) := by
  have hroot : Nat.card (simpleRoot Q split i) = q := by
    have hidx := marked_commonBorel_root_index Q e h split i
    omega
  exact Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.cross_root_commutator_eq_of_derived_card
    Q split hm i j hij hVi hVj
    (marked_simpleRoot_elementary_of_original_quotient Q e h split i hVi hQi)
    (marked_simpleRoot_elementary_of_original_quotient Q e h split j hVj hQj)
    ((marked_remainder_derived_card Q e h split i hVi).trans (hderived.trans hroot.symm))

omit Q e h split in
/-- The two literal original-source bounds needed for (6A)(c), with the
intrinsic center embedded into the same quotient and both orientations allowed. -/
theorem original_quadrangle_center_bounds
    (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hm : rotationOrder Q₀ = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
    (hVj : simpleRemainder Q₀ split₀ j ≤ localKernel Q₀ j) :
    ⁅simpleRoot Q₀ split₀ j,rootAt Q₀ split₀ j (Q₀.simple i)⁆ ≤
        rootAt Q₀ split₀ i (Q₀.simple j) ∧
      ⁅simpleRoot Q₀ split₀ i,rootAt Q₀ split₀ i (Q₀.simple j)⁆ ≤
        (center (rootAt Q₀ split₀ j (Q₀.simple i))).map
          (rootAt Q₀ split₀ j (Q₀.simple i)).subtype :=
  ⟨Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.cross_root_commutator_le
      Q₀ split₀ hm j i hij.symm hVj,
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.cross_root_commutator_le_center
      Q₀ split₀ hm i j hij hVi hVj⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
