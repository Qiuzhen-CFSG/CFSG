module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.Components
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.ActionTransfer
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Ambient MS conditions for the point parabolic

A Sylow subgroup supplements O²(P); hence a point parabolic containing
S∩L satisfies O²(P)S = PS. The original S remains Sylow, and PS inherits
the genuine SQTK and generalized-Fitting hypotheses from I. Once P is
S-invariant, the residual and S form a literal product. Its proper Sylow
subgroup itself witnesses the odd-index radical clause of C.1.31(MS2).

The last transport preserves characteristic subgroups of the original S
and normality in PS. In particular 15.3.11(12), after the proved action
transfer, supplies exactly MS3. Projected noncentrality and S-invariance
are not asserted here; their construction belongs to the remaining local
and geometric arguments.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.11(1),(12), 15.3.24, printed pp.1123–1124 and 1129–1130;
C.1.31(MS1)–(MS3), printed p.135.
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic
open scoped Pointwise

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization

universe u
variable {G : Type u} [Group G] {d : LocalData G} {L I : Subgroup G}

/-- The source's two-residual overgroup is exactly PS, by the Sylow supplement theorem. -/
theorem residualOvergroup_eq_join [Finite G] (h : NaturalDual d L) (x : Space 4)
    (hS : Chapter1.IsSylowIn 2 (d.S ⊓ L) L)
    (hSP : d.S ⊓ L ≤ point h x) :
    residualOvergroup h x = point h x ⊔ d.S := by
  obtain ⟨T, hT⟩ := hS.restrict hSP (point_le h x)
  have he := congrArg (map (point h x).subtype) (pResidual_sup_sylow_eq_top T)
  rw [Subgroup.map_sup, hT, ← MonoidHom.range_eq_map, range_subtype] at he
  change Stellmacher.twoResidualAmbient (point h x) ⊔ d.S = _
  rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  apply le_antisymm
  · exact sup_le_sup_right (map_subtype_le _) _
  · apply sup_le _ le_sup_right
    exact he.ge.trans (sup_le_sup_left (show d.S ⊓ L ≤ d.S from inf_le_left) _)

/-- Both factors of the proposed MS group are contained in the original I. -/
theorem residualOvergroup_le (h : NaturalDual d L) (x : Space 4)
    (hLI : L ≤ I) (hSI : d.S ≤ I) : residualOvergroup h x ≤ I :=
  sup_le ((map_subtype_le _).trans ((point_le h x).trans hLI)) hSI

/-- The original S remains Sylow in the actual residual overgroup. -/
theorem residualOvergroup_sylow (h : NaturalDual d L) (x : Space 4)
    (hLI : L ≤ I) (hS : Chapter1.IsSylowIn 2 d.S I) :
    Chapter1.IsSylowIn 2 d.S (residualOvergroup h x) :=
  hS.restrict le_sup_right
    (residualOvergroup_le h x hLI (Chapter1.isSylowIn_iff.mp hS).2.1)

/-- Generalized Fitting equality is inherited through the Sylow overgroup. -/
theorem residualOvergroup_fitting [Finite G] (h : NaturalDual d L) (x : Space 4)
    (hLI : L ≤ I) (hS : Chapter1.IsSylowIn 2 d.S I) (hf : HasCharacteristicTwo I) :
    Theory.GroupTheory.generalizedFitting (residualOvergroup h x) =
      pCore 2 (residualOvergroup h x) :=
  characteristicTwo_of_sylow_overgroup hS
    (residualOvergroup_le h x hLI (Chapter1.isSylowIn_iff.mp hS).2.1) le_sup_right hf

/-- Both strong quasithinness and the full subgroup-section K-condition restrict to PS. -/
theorem residualOvergroup_sqtk [Finite G] {κ : GroupClass.{u}}
    (h : NaturalDual d L) (x : Space 4) (hLI : L ≤ I) (hSI : d.S ≤ I)
    (hq : IsSQTK κ I) : IsSQTK κ (residualOvergroup h x) := by
  let f := inclusion (residualOvergroup_le h x hLI hSI)
  exact ⟨hq.stronglyQuasithin.of_injective f (inclusion_injective _),
    hq.isKGroup.of_injective f (inclusion_injective _)⟩

/-- S-invariance of P gives the literal product required in MS1. -/
theorem residualComponent_product [Finite G] (h : NaturalDual d L) (x : Space 4)
    (hn : d.S ≤ normalizer (point h x : Set G)) :
    ∀ j : residualOvergroup h x, ∃ l ∈ residualComponent h x,
      ∃ r ∈ sylowPart h x, l * r = j := by
  have hn' : d.S ≤ normalizer (Stellmacher.twoResidualAmbient (point h x) : Set G) := by
    rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
    exact hn.trans (normalizer_le_normalizer_characteristic_image
      (point h x) (pResidual 2 (point h x)))
  intro j
  have hj : (j : G) ∈ (Stellmacher.twoResidualAmbient (point h x) : Set G) * (d.S : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hn']
    exact j.property
  obtain ⟨l, hl, r, hr, he⟩ := hj
  exact ⟨⟨l, mem_sup_left hl⟩, hl, ⟨r, mem_sup_right hr⟩, hr, Subtype.ext he⟩

/-- The proper Sylow subgroup itself witnesses the odd-index radical condition. -/
theorem sylowPart_oddIndexRadical [Finite G] (h : NaturalDual d L) (x : Space 4)
    (hs : Chapter1.IsSylowIn 2 d.S (residualOvergroup h x))
    (hc : (residualComponent h x).IsCComponent) :
    ChapterC.MSOddIndexRadical (sylowPart h x) := by
  obtain ⟨T, hT⟩ := hs
  have he : sylowPart h x = (T : Subgroup (residualOvergroup h x)) := by
    apply map_injective (residualOvergroup h x).subtype_injective
    exact (map_subgroupOf_eq_of_le (show d.S ≤ residualOvergroup h x from le_sup_right)).trans hT.symm
  rw [he]
  have hne : (T : Subgroup (residualOvergroup h x)) ≠ ⊤ := by
    intro ht
    have hp : IsPGroup 2 (residualComponent h x) :=
      T.isPGroup'.to_le (by rw [ht]; exact le_top)
    let := hp.isNilpotent
    exact hc.not_isSolvable inferInstance
  refine ⟨T, lt_top_iff_ne_top.mpr hne, ?_, ?_⟩
  · exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using T.not_dvd_index)
  · have he : pCore 2 (T : Subgroup (residualOvergroup h x)) = ⊤ := by
      apply top_unique
      exact le_sSup ⟨inferInstance, T.isPGroup'.to_subgroup ⊤⟩
    rw [he, ← MonoidHom.range_eq_map, range_subtype]

private theorem characteristic_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (C : Subgroup A) (hC : C.Characteristic) :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y, hy, rfl⟩ := hx
  let b : MulAut A := e.trans (a.trans e.symm)
  exact ⟨b y, (characteristic_iff_le_comap.mp hC b) hy, e.apply_symm_apply _⟩

/-- Transfer the original characteristic-subgroup exclusion to the same S inside the MS group. -/
theorem sylowPart_characteristic (h : NaturalDual d L) (x : Space 4)
    (hno : ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
      ¬ ((C.map d.S.subtype).subgroupOf (residualOvergroup h x)).Normal) :
    ChapterC.MSCharacteristicCondition (sylowPart h x) := by
  intro C hC hne hn
  let e : sylowPart h x ≃* d.S := subgroupOfEquivOfLe le_sup_right
  let D : Subgroup d.S := C.map e.toMonoidHom
  have hD : D.Characteristic := characteristic_map_equiv e C hC
  have hDne : D ≠ ⊥ := fun hz => hne ((map_eq_bot_iff_of_injective C e.injective).mp hz)
  have he : (D.map d.S.subtype).subgroupOf (residualOvergroup h x) =
      C.map (sylowPart h x).subtype := by
    apply map_injective (residualOvergroup h x).subtype_injective
    rw [map_subgroupOf_eq_of_le (show D.map d.S.subtype ≤ residualOvergroup h x from
      (map_subtype_le D).trans le_sup_right), map_map, map_map]
    rfl
  exact hno D hD hDne (he.symm ▸ hn)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization

end
