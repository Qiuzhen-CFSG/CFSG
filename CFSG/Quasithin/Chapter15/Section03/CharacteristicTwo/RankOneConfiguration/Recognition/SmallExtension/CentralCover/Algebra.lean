module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralAction
public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.Representation.FirstCohomologyDuality

/-!
# The literal central coefficient module in 15.3.31

For Q = [O₂(L),L], retain Z(Q) and its full L-central subgroup.
The module model below identifies their actual quotient, equivariantly, with
an action of the actual quotient L/O₂(L). Faithfulness of this model gives
the needed bound C_L(Q) ≤ O₂(L). Perfectness eliminates commutators in the
central layer; it does not permit deleting that layer from the input.

Source: Aschbacher--Smith, proof of 15.3.31, printed p.1132, and C.1.7.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover

variable {G : Type*} [Group G]

/-- Z(Q), embedded in the original ambient group. -/
def coreCenter (L : Subgroup G) : Subgroup G :=
  extensionCore L ⊓ centralizer (extensionCore L : Set G)

theorem extensionCore_le (L : Subgroup G) : extensionCore L ≤ L := by
  change ⁅L.pCoreIn 2, L⁆ ≤ L
  exact le_normalizer_iff_commutator_le_right.mp
    ((pCoreIn_le 2 L).trans L.le_normalizer)

theorem coreCenter_le (L : Subgroup G) : coreCenter L ≤ L :=
  inf_le_left.trans (extensionCore_le L)

theorem normalizes_coreCenter (L : Subgroup G) : L ≤ normalizer (coreCenter L : Set G) :=
  le_normalizer_inf (normalizes_extensionCore L.le_normalizer)
    ((normalizes_extensionCore L.le_normalizer).trans (normalizer_le_normalizer_centralizer _))

/-- C_Z(Q)(L), intrinsically inside Z(Q). -/
def centerKernel (L : Subgroup G) : Subgroup (coreCenter L) :=
  (centralizer (L : Set G)).subgroupOf (coreCenter L)

instance centerKernel_normal (L : Subgroup G) : (centerKernel L).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((coreCenter_le L).trans (L.le_normalizer.trans (normalizer_le_normalizer_centralizer _)))

/-- The full coefficient quotient, with no central submodule discarded. -/
abbrev CenterQuotient (L : Subgroup G) := coreCenter L ⧸ centerKernel L

/-- The actual conjugation in the center of the commutator core. -/
def centerConjugate (L : Subgroup G) (l : L) (z : coreCenter L) : coreCenter L :=
  ⟨l * (z : G) * (l : G)⁻¹, (normalizes_coreCenter L l.property z).mp z.property⟩

variable {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]

/-- A genuine realization of Z(Q)/C_Z(Q)(L), including both quotient
isomorphisms and the literal conjugation compatibility. The separate whole-center
condition records that O₂(L) acts trivially on Z(Q), as it does in the surviving
MS configurations. It is stronger than merely killing its action on the quotient. -/
structure CenterModel (L : Subgroup G) (ρ : Representation (ZMod 2) A V) where
  quotientIso : (L ⧸ pCore 2 L) ≃* A
  moduleIso : CenterQuotient L ≃* Multiplicative V
  intertwining : ∀ (l : L) (z : coreCenter L),
    moduleIso (QuotientGroup.mk' (centerKernel L) (centerConjugate L l z)) =
      Multiplicative.ofAdd (ρ (quotientIso (QuotientGroup.mk' (pCore 2 L) l))
        (Multiplicative.toAdd (moduleIso (QuotientGroup.mk' (centerKernel L) z))))
  core_centralizes : L.pCoreIn 2 ≤ centralizer (coreCenter L : Set G)

namespace CenterModel

variable {L : Subgroup G} {ρ : Representation (ZMod 2) A V} (m : CenterModel L ρ)

/-- The quotient map to the actual model actor. -/
def actorMap : L →* A := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

/-- Coordinates on the whole center, retaining the literal central kernel. -/
def coordinates : coreCenter L →* Multiplicative V :=
  m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (centerKernel L))

theorem actorMap_surjective : Function.Surjective m.actorMap :=
  m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)

theorem coordinates_surjective : Function.Surjective m.coordinates :=
  m.moduleIso.surjective.comp (QuotientGroup.mk'_surjective _)

theorem actorMap_ker : m.actorMap.ker = pCore 2 L := by
  ext l
  change m.quotientIso (QuotientGroup.mk' (pCore 2 L) l) = 1 ↔ _
  rw [map_eq_one_iff _ m.quotientIso.injective]
  exact QuotientGroup.eq_one_iff _

theorem coordinates_eq_one_iff (z : coreCenter L) :
    m.coordinates z = 1 ↔ (z : G) ∈ centralizer (L : Set G) := by
  change m.moduleIso (QuotientGroup.mk' (centerKernel L) z) = 1 ↔ _
  rw [map_eq_one_iff _ m.moduleIso.injective]
  exact QuotientGroup.eq_one_iff _

theorem coordinates_conjugate (l : L) (z : coreCenter L) :
    m.coordinates (centerConjugate L l z) =
      Multiplicative.ofAdd (ρ (m.actorMap l) (Multiplicative.toAdd (m.coordinates z))) :=
  m.intertwining l z

include m in
/-- Faithfulness of the identified natural coefficient module forces the
model-dependent centralizer bound. This works for a pair of natural summands too. -/
theorem centralizer_core_le (hfaith : Function.Injective ρ) :
    L ⊓ centralizer (extensionCore L : Set G) ≤ L.pCoreIn 2 := by
  intro l hl
  let lL : L := ⟨l, hl.1⟩
  have hact : ρ (m.actorMap lL) = 1 := by
    ext v
    obtain ⟨z, hz⟩ := m.coordinates_surjective (Multiplicative.ofAdd v)
    have hc : centerConjugate L lL z = z := by
      apply Subtype.ext
      change l * (z : G) * l⁻¹ = z
      rw [← mem_centralizer_iff.mp hl.2 z z.property.1, mul_inv_cancel_right]
    have he := m.coordinates_conjugate lL z
    rw [hc, hz] at he
    exact (congrArg Multiplicative.toAdd he).symm
  have hk : lL ∈ pCore 2 L := by
    rw [← m.actorMap_ker]
    exact hfaith (by simpa using hact)
  exact mem_map.mpr ⟨lL, hk, rfl⟩

end CenterModel

/-- Perfectness removes an error already known to centralize L, by the
three-subgroup lemma. This supplies injectivity after removing C_Z(Q)(L). -/
theorem centralizes_of_commutator_centralizes {D L : Subgroup G}
    (hperfect : Group.IsPerfect L) (h : ⁅D,L⁆ ≤ centralizer (L : Set G)) :
    D ≤ centralizer (L : Set G) := by
  have h₁ : ⁅⁅D,L⁆,L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr h
  have h₂ : ⁅⁅L,D⁆,L⁆ = ⊥ := by rwa [commutator_comm L D]
  have h₃ := commutator_commutator_eq_bot_of_rotate h₂ h₁
  rw [Subgroup.isPerfect_iff.mp hperfect, commutator_comm] at h₃
  exact commutator_eq_bot_iff_le_centralizer.mp h₃

/-- In a surviving MS model, a centralizing actor's commutators with O₂(L)
lie in the retained central kernel. Hence its coefficient cocycle descends
to the actual quotient L/O₂(L). -/
theorem commutator_core_centralizes {D L : Subgroup G}
    (hDZ : ⁅D,L⁆ ≤ coreCenter L)
    (hDQ : D ≤ centralizer (extensionCore L : Set G))
    (hPZ : L.pCoreIn 2 ≤ centralizer (coreCenter L : Set G)) :
    ⁅D,L.pCoreIn 2⁆ ≤ centralizer (L : Set G) := by
  have h₁ : ⁅⁅L.pCoreIn 2,L⁆,D⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hDQ)
  have h₂ : ⁅⁅L,D⁆,L.pCoreIn 2⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [commutator_comm L D]
    exact hDZ.trans (le_centralizer_iff.mp hPZ)
  exact commutator_eq_bot_iff_le_centralizer.mp
    (commutator_commutator_eq_bot_of_rotate h₁ h₂)

/-- The elementary-center conclusion in the block alternatives comes from
the actual block definition, transported through the subgroup embedding. -/
theorem coreCenter_elementary_of_short {L : Subgroup G} (h : ChapterC.IsShort L) :
    IsElementaryAbelian 2 (coreCenter L) := by
  have he : (ChapterC.blockU L).map L.subtype = extensionCore L := by
    rw [ChapterC.blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  let := h.elementary
  have helem : IsElementaryAbelian 2 (extensionCore L) :=
    he ▸ IsElementaryAbelian.map_subtype
  let := helem
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · exact le_centralizer_iff_isMulCommutative.mp
      (inf_le_right.trans (centralizer_le (show coreCenter L ≤ extensionCore L from inf_le_left)))
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro z
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (z : G) z.property.1

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover
