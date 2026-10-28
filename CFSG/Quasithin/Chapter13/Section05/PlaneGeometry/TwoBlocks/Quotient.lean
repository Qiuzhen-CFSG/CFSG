module
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.BlockLayer
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# The original permutation quotient after block recognition

For an actual A₆ block, the quotient by O₂(L) has trivial center, so the
original central-core quotient has exactly the two-core as kernel.
The resulting map to S₆ retains the source coordinates and has image A₆.
This is the map through which the native cubic axes are lifted in13.5.6.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
open Section08.SourceCompletion Section07.NaturalAction
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)

noncomputable def localMap : L →* Equiv.Perm (Fin 6) :=
  (alternatingGroup (Fin 6)).subtype.comp
    (d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L)))

theorem localMap_range : (localMap d).range=alternatingGroup (Fin 6) := by
  rw [localMap,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr
    (d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _)),
    ←MonoidHom.range_eq_map,range_subtype]

omit [Finite G] in
theorem centralCore_eq_twoCore (hb:ChapterC.IsAlternatingBlock L 6) : centralCore L=pCore 2 L := by
  obtain ⟨e⟩ := hb.2.2.quotient_iso
  have hz : center (L ⧸ pCore 2 L)=⊥ := by
    apply card_eq_one.mp
    rw [Nat.card_congr (centerCongr e).toEquiv,
      alternatingGroup.center_eq_bot (by norm_num : 4≤Nat.card (Fin 6)),card_bot]
  change (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L))=pCore 2 L
  rw [hz]
  exact QuotientGroup.ker_mk' _

theorem localMap_kernel (hb:ChapterC.IsAlternatingBlock L 6) :
    (localMap d).ker=pCore 2 L := by
  suffices hk : (localMap d).ker=centralCore L from hk.trans (centralCore_eq_twoCore hb)
  ext l
  change ((d.local_quotient (QuotientGroup.mk' (centralCore L) l)):Equiv.Perm (Fin 6))=1 ↔ _
  constructor
  · intro h
    have h' : d.local_quotient (QuotientGroup.mk' (centralCore L) l)=1 := Subtype.ext h
    exact (QuotientGroup.eq_one_iff l).mp (d.local_quotient.injective (h'.trans (map_one _).symm))
  · intro hl
    have hh : QuotientGroup.mk' (centralCore L) l=1 := (QuotientGroup.eq_one_iff l).mpr hl
    rw [hh,map_one]
    rfl

theorem localMap_kernel_two (hb:ChapterC.IsAlternatingBlock L 6) : IsPGroup 2 (localMap d).ker := by
  rw [localMap_kernel d hb]
  exact pCore_isPGroup
end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
