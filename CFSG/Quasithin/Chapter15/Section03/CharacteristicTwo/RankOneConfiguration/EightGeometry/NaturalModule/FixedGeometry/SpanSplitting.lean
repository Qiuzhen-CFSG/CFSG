module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.LocalSpan
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.InternalModule
public import Theory.GroupTheory.NormalClosureCommutatorSupplement

/-!
# Applying B.2.14 to the genuine local span

The source's universal splitting clause remains an explicit upstream theorem
input. Its local application uses U_I=⟨Z^I⟩, identified with the internal
normal closure in I. We verify nontriviality, Sylow omega-center membership
and characteristic two. Relative normality of L and I=LS identify
[U_I,I] with U_L, giving U_I=U_L C_{U_I}(I).

The elementary span lies in O₂(I)≤S. Thus its I-fixed summand lies in
Ω₁(Z(S))=Z_S. No local splitting or desired centralizer is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the splitting
assertion of B.2.14(1) on p.78 and its use in 15.3.32 on p.1133.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry
universe u

/-- The universal splitting clause of source B.2.14(1), for the normal closure
of any nontrivial subgroup of a Sylow omega-center in characteristic two.
It is an explicit upstream theorem input, not a local decomposition witness. -/
def SourceB214Splitting : Prop :=
  ∀ (H : Type u) [Group H] [Finite H],
    Theory.GroupTheory.generalizedFitting H = pCore 2 H →
    ∀ (P : Sylow 2 H) (Z : Subgroup H), Z ≠ ⊥ →
      Z ≤ Stellmacher.omegaOneCenterAmbient (P : Subgroup H) →
      let U := normalClosure (Z : Set H)
      U = ⁅U, (⊤ : Subgroup H)⁆ ⊔ (U ⊓ center H)

variable {G : Type u} [Group G] [Finite G]

/-- Normality and I=LS identify the full span commutator with U_L. -/
theorem span_commutator_eq_componentModule (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S) : ⁅d.UI I, I⁆ = d.componentModule I c.L := by
  let _ := hnormal
  have hSI : d.S ≤ I := hI ▸ le_sup_right
  have hZI : d.Z ≤ I := (d.Z_le_S
    (d.action.le_sylow d.T d.sylow_le (localModule_le d.T d.sylow_le))).trans hSI
  have hLS : c.L.subgroupOf I ⊔ d.S.subgroupOf I = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (component_le c),
      map_subgroupOf_eq_of_le hSI, ← MonoidHom.range_eq_map, range_subtype]
    exact hI.symm
  have hZC : d.Z.subgroupOf I ≤ centralizer (d.S.subgroupOf I : Set I) := by
    intro z hz s hs
    exact Subtype.ext (d.Z_le_centralizer_S hz s hs)
  have h := commutator_normalClosure_eq_of_normal_supplement
    (d.Z.subgroupOf I) ((d.UI I).subgroupOf I) (c.L.subgroupOf I) (d.S.subgroupOf I)
    (comap_mono (le_conjugateSpanBy d.Z I)) (d.UI_subgroupOf_eq_normalClosure hZI)
    hZC hLS
  have hm := congrArg (Subgroup.map I.subtype) h
  rw [map_commutator, map_commutator, map_subgroupOf_eq_of_le (span_le d hSI),
    map_subgroupOf_eq_of_le (component_le c), ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm

/-- B.2.14 applied to the genuine U_I, with every local hypothesis checked. -/
theorem span_split_of_source (hB : SourceB214Splitting.{u})
    (d : LocalData G) {I : Subgroup G} (hchar : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S) (hZ : Nat.card d.Z = 2) :
    d.UI I = d.componentModule I c.L ⊔ (d.UI I ⊓ centralizer (I : Set G)) := by
  have hSI : d.S ≤ I := hI ▸ le_sup_right
  have hZS : d.Z ≤ d.S := d.Z_le_S
    (d.action.le_sylow d.T d.sylow_le (localModule_le d.T d.sylow_le))
  have hZI := hZS.trans hSI
  have hn : d.Z.subgroupOf I ≠ ⊥ := by
    intro h
    have he := congrArg (Subgroup.map I.subtype) h
    rw [map_subgroupOf_eq_of_le hZI, Subgroup.map_bot] at he
    rw [he, Subgroup.card_bot] at hZ
    contradiction
  have hZo : d.Z.subgroupOf I ≤ Stellmacher.omegaOneCenterAmbient (P : Subgroup I) := by
    intro z hz
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    have hzP : z ∈ (P : Subgroup I) := by
      obtain ⟨w, hw, he⟩ := hP.ge (hZS hz)
      exact (Subtype.ext he : w = z) ▸ hw
    refine ⟨hzP, ?_, ?_⟩
    · exact Subtype.ext
        ((Stellmacher.mem_omegaOneCenterAmbient_iff (d.T : Subgroup G) (z : G)).mp hz).2.1
    · intro s hs
      exact Subtype.ext (d.Z_le_centralizer_S hz s (hP ▸ mem_map_of_mem I.subtype hs))
  have hb := hB I hchar P (d.Z.subgroupOf I) hn hZo
  rw [← d.UI_subgroupOf_eq_normalClosure hZI] at hb
  have hcenter : (((d.UI I).subgroupOf I) ⊓ center I).map I.subtype =
      d.UI I ⊓ centralizer (I : Set G) := by
    ext x
    constructor
    · rintro ⟨w, ⟨hwU, hwC⟩, rfl⟩
      exact ⟨hwU, fun i hi => congrArg Subtype.val (mem_center_iff.mp hwC ⟨i, hi⟩)⟩
    · intro hx
      refine ⟨⟨x, span_le d hSI hx.1⟩, ⟨hx.1, ?_⟩, rfl⟩
      exact mem_center_iff.mpr fun i => Subtype.ext (hx.2 i i.property)
  have hm := congrArg (Subgroup.map I.subtype) hb
  rw [Subgroup.map_sup, map_commutator, map_subgroupOf_eq_of_le (span_le d hSI),
    ← MonoidHom.range_eq_map, range_subtype, hcenter,
    span_commutator_eq_componentModule d c hnormal hI] at hm
  exact hm

/-- The fixed summand in U_I lies in the actual omega-center Z_S. -/
theorem span_fixed_le_ZS (d : LocalData G) {I : Subgroup G}
    (hchar : HasCharacteristicTwo I) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hOmega : d.ZS = Stellmacher.omegaOneCenterAmbient d.S) :
    d.UI I ⊓ centralizer (I : Set G) ≤ d.ZS := by
  let _ := span_elementary d hchar P hP
  have hUS : d.UI I ≤ d.S := (span_le_core d hchar P hP).trans (hP ▸ pCoreIn_le_sylow I P)
  have hSI : d.S ≤ I := hP ▸ map_subtype_le _
  intro x hx
  rw [hOmega]
  exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨hUS hx.1, elemPow_eq_one_of_isElementaryAbelian x hx.1, fun s hs => hx.2 s (hSI hs)⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry

end
