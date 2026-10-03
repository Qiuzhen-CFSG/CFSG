module

public import Stellmacher.SectionNine.DistanceOneOddCoreOrder
public import Stellmacher.UniqueMaximalContainingMap
public import Stellmacher.UniqueMaximalContainingTransport

/-!
# Inputs for the faithful initial wreath recognition

The actual distance-one quotient witness satisfies the Section One action
hypotheses, has elementary module of order sixteen and odd core of order nine,
and contains an elementary subgroup of order four. A quotient Sylow supplements
the odd core and has a unique maximal overgroup. The latter assertion descends
from the genuine local P-family by surjective subgroup correspondence; the
nontrivial odd core ensures that the Sylow image is proper.

These are the inputs for the remaining group recognition in Stellmacher (9.1),
relation (8), printed p.47 of `refs/files/stellmacher-n-group.pdf`. The theorem
does not assert the wreath classification or the later initial-core equality.
The graph stays in G, while the ambient context and embedding stay in H.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem distance_one_faithful_recognition_setup
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneActionData ctx)
    [IsElementaryAbelian 2 (ZAt ctx.Γ ctx.criticalPath.a)]
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer
        (ZAt ctx.Γ ctx.criticalPath.a : Set G)) (ZAt ctx.Γ ctx.criticalPath.a)) :
    let _ := w.groupX
    let _ := w.finiteX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    SectionOne.Hypotheses w.X (ZAt ctx.Γ ctx.criticalPath.a) ∧
      Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 16 ∧
      Nat.card (SectionOne.oddCore w.X) = 9 ∧
      (∃ R : Sylow 2 w.X,
        SectionOne.oddCore w.X ⊔ (R : Subgroup w.X) = ⊤ ∧
        IsUniqueMaximalContaining (R : Subgroup w.X) ⊤) ∧
      ∃ X : Subgroup w.X, IsElementaryAbelian 2 X ∧ Nat.card X = 4 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom (ZAt Γ cp.a) w.action
  have hsetup := SectionEight.local_quotient_sylow_action_setup ctx.sectionSeven Γ cp w
  have hcard := distance_one_initial_center_card_sixteen ctx hb data w
  have hodd := (distance_one_faithful_odd_core_order ctx hb data w).1
  refine ⟨hsetup.1, hcard, hodd, ?_, ?_⟩
  · have hlocal := (pFamily_iff_pSet _ _ _).mp
      (edge_local_data ctx.sectionSeven Γ cp).1.1
    obtain ⟨localSylow, hmap⟩ := hlocal.1.2.1
    have huniq : IsUniqueMaximalContaining (localSylow : Subgroup P) ⊤ :=
      native_uniqueMaximalContaining P (localSylow : Subgroup P)
        (by rw [hmap]; exact hlocal.2)
    let R := localSylow.mapSurjective w.surjective
    have hproper : (R : Subgroup w.X) ≠ ⊤ := by
      intro htop
      have hcore : (⊤ : Subgroup w.X) ≤ pCore 2 w.X :=
        le_sSup ⟨inferInstance, htop ▸ R.isPGroup'⟩
      have htrivial : (⊤ : Subgroup w.X) = ⊥ :=
        bot_unique (hcore.trans_eq hsetup.1.twoCore_eq_bot)
      have hoddtrivial : SectionOne.oddCore w.X = ⊥ :=
        bot_unique (le_top.trans_eq htrivial)
      simp only [hoddtrivial, Subgroup.card_bot] at hodd
      omega
    exact ⟨R, hsetup.2 localSylow,
      uniqueMaximalContaining_map_of_ne_top w.projection w.surjective
        (localSylow : Subgroup P) huniq hproper⟩
  · let next := Γ.act data.x⁻¹ cp.a
    let V := (z Γ cp.a ⊓ stabilizer Γ next) ⊔ (z Γ next ⊓ stabilizer Γ cp.a)
    exact ⟨(V.subgroupOf P).map w.projection,
      distance_one_image_elementary ctx data w,
      (distance_one_relative_odd_order ctx hb data w).2⟩

end Stellmacher.SectionNine
