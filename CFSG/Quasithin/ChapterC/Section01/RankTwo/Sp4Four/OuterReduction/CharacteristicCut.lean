module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.CharacteristicReduction
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Reduction

/-!
# Characteristic spans and the minimum centralizer cut

The orbit span under every automorphism of the actual radical, joined with
its central omega subgroup, is characteristic. So is its centralizer. The
literal cut supplied by the graph forces this centralizer to be the whole
minimum replacement, using the existing generic minimum-order theorem.
The identification of the initial source seed and the graph cut are separate.

Source: MS93 (3.4) and Section 7, pp.868–869 and932–933.
-/

public section
open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

variable {J : Type*} [Group J]

noncomputable def automorphismSpan (Y : Subgroup J) : Subgroup J :=
  ⨆ a : MulAut J, Y.map a.toMonoidHom

theorem le_automorphismSpan (Y : Subgroup J) : Y ≤ automorphismSpan Y := by
  intro x hx
  exact (le_iSup (fun a : MulAut J => Y.map a.toMonoidHom) (MulEquiv.refl J))
    (mem_map.mpr ⟨x,hx,rfl⟩)

theorem automorphismSpan_le_iff (Y N : Subgroup J) :
    automorphismSpan Y ≤ N ↔ ∀ a : MulAut J, Y.map a.toMonoidHom ≤ N :=
  iSup_le_iff

theorem map_le_automorphismSpan (Y : Subgroup J) (a : MulAut J) :
    Y.map a.toMonoidHom ≤ automorphismSpan Y :=
  le_iSup (fun a : MulAut J => Y.map a.toMonoidHom) a

instance automorphismSpan_characteristic (Y : Subgroup J) :
    (automorphismSpan Y).Characteristic := by
  apply characteristic_iff_map_le.mpr
  intro a
  rw [automorphismSpan, Subgroup.map_iSup]
  apply iSup_le
  intro b
  rw [map_map]
  exact le_iSup_of_le (b.trans a) le_rfl

noncomputable def starSpan (T : Subgroup J) (Y : Subgroup T) : Subgroup T :=
  automorphismSpan Y ⊔ ((omega₁ (center T) (p := 2)).map (center T).subtype)

theorem starSpan_map_subtype (T : Subgroup J) (Y : Subgroup T) :
    (starSpan T Y).map T.subtype = (automorphismSpan Y).map T.subtype ⊔ omegaCenter T := by
  rw [starSpan, Subgroup.map_sup]
  rfl

theorem le_starSpan (T : Subgroup J) (Y : Subgroup T) : Y ≤ starSpan T Y :=
  (le_automorphismSpan Y).trans le_sup_left

instance starSpan_characteristic (T : Subgroup J) (Y : Subgroup T) :
    (starSpan T Y).Characteristic := by
  dsimp only [starSpan]
  let : (omega₁ (center T) (p := 2)).Characteristic := omega₁_characteristic _
  infer_instance

noncomputable def starCentralizer (T : Subgroup J) (Y : Subgroup T) : Subgroup T :=
  centralizer (starSpan T Y : Set T)

instance starCentralizer_characteristic (T : Subgroup J) (Y : Subgroup T) :
    (starCentralizer T Y).Characteristic := by
  dsimp only [starCentralizer]
  infer_instance

theorem starCentralizer_map (T : Subgroup J) (Y : Subgroup T) :
    (starCentralizer T Y).map T.subtype =
      T ⊓ centralizer ((starSpan T Y).map T.subtype : Set J) := by
  ext x
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.property,?_⟩
    rintro z ⟨z,hz,rfl⟩
    exact congrArg Subtype.val (hx z hz)
  · rintro ⟨hx,hc⟩
    refine ⟨⟨x,hx⟩,?_,rfl⟩
    intro z hz
    exact Subtype.ext (hc z (mem_map_of_mem T.subtype hz))

theorem starCentralizer_eq_top_of_minimal
    (A T : Subgroup J) (hmin : CharacteristicMinimal A T) (Y : Subgroup T)
    (hcut : (A ⊔ (T ⊓ centralizer ((starSpan T Y).map T.subtype : Set J))) ⊓ pCore 2 J ≤
      T ⊓ centralizer ((starSpan T Y).map T.subtype : Set J)) :
    starCentralizer T Y = ⊤ := by
  apply hmin _ inferInstance
  simpa only [starCentralizer_map] using hcut

theorem star_span_central_of_minimal
    (A T : Subgroup J) (hmin : CharacteristicMinimal A T) (Y : Subgroup T)
    (hcut : (A ⊔ (T ⊓ centralizer ((starSpan T Y).map T.subtype : Set J))) ⊓ pCore 2 J ≤
      T ⊓ centralizer ((starSpan T Y).map T.subtype : Set J)) :
    T ≤ centralizer ((starSpan T Y).map T.subtype : Set J) := by
  have he := congrArg (fun C : Subgroup T => C.map T.subtype)
    (starCentralizer_eq_top_of_minimal A T hmin Y hcut)
  rw [starCentralizer_map, ← MonoidHom.range_eq_map, range_subtype] at he
  exact he.ge.trans inf_le_right

variable [Finite J] {A T : Subgroup J}
theorem replacement_starCentralizer_eq_top
    (d : CharacteristicReduction A T) [A.Normal] (hAT : A ⊔ T = ⊤)
    (Y : Subgroup d.radical)
    (hcut : ((A.subgroupOf d.overgroup) ⊔
      (d.radical ⊓ centralizer ((starSpan d.radical Y).map d.radical.subtype : Set d.overgroup))) ⊓
        pCore 2 d.overgroup ≤
      d.radical ⊓ centralizer ((starSpan d.radical Y).map d.radical.subtype : Set d.overgroup)) :
    starCentralizer d.radical Y = ⊤ :=
  starCentralizer_eq_top_of_minimal _ _
    (NaturalSixControl.SymplecticSetup.Reduction.reduced_minimal d inferInstance hAT) Y hcut

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
