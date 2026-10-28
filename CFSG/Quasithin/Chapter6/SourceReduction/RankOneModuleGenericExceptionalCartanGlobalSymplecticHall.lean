module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall.SymplecticCovered
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even

/-!
# The literal right Hall group in the symplectic source row

In the single symplectic row of E.2.2, the original component image in
X/O₂(X) is a perfect central cover of the marked Sp₄(F) model. Triviality
of the symplectic multiplier makes that very projection an isomorphism.
Thus the original component overlap, modulo its two-core, is the split
torus Fˣ × Fˣ, with the original Borel marking retained.

Every prescribed odd Hall subgroup of the maximal overgroup lies in this
overlap: the quotient by the component is a two-group. It complements the
normal Sylow two-subgroup of the overlap and hence is isomorphic to the
same split torus. This supplies the order-nine Hall calculation used in
5.2.2 when the marked field has order four; it does not identify this field
parameter with that of the original left component.

Source: Aschbacher–Smith E.2.2(2b), pp.215–216, and 5.1.10, 5.2.2,
printed pp.634,648–649; I.1.3 for the symplectic central-cover calculation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open DiagramHall SymplecticCovered
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.SymplecticCartan
variable {X : Type*} [Group X] [Finite X]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The original covered component Borel has the literal split torus quotient. -/
theorem overlap_quotient
    (S : Sylow 2 X) (hP : ChapterB.IsMinimalParabolicOver S ⊤) {K : Subgroup X}
    (hK : K.IsCComponent) (hc : SingleClauses (ChapterB.minimalParabolicMax S hP) K S)
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : sourceImage (ChapterB.minimalParabolicMax S hP) K ≃* Sp4Derived F)
    (he : (componentOverlap (ChapterB.minimalParabolicMax S hP) K).map e.toMonoidHom =
      sp4DerivedBorel F) :
    Nonempty ((K.subgroupOf (ChapterB.minimalParabolicMax S hP) ⧸
      pCore 2 (K.subgroupOf (ChapterB.minimalParabolicMax S hP))) ≃* (Fˣ × Fˣ)) := by
  have hq : 3 < Nat.card F := by
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ f by omega)
    omega
  let ef := derivedEquivFull_of_card_gt_two (F := F) (by omega)
  let a := actorToModel S hP e
  let c : PerfectCentralCovering.Cover (actorImage K) (Sp F) := {
    toMonoidHom := ef.toMonoidHom.comp a
    surjective := ef.surjective.comp (actorToModel_surjective S hP e)
    isPerfect := by
      let := hK.perfect
      exact Group.IsPerfect.ofSurjective ((QuotientGroup.mk' (pCore 2 X)).subgroupMap_surjective K)
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ ef.injective]
      exact actorToModel_central S hP hc e }
  have ha : Function.Injective a := by
    intro x y hxy
    apply CentralCovers.Even.cover_injective hq c
    exact congrArg ef hxy
  let eb : ((sp4DerivedBorel F).comap a) ≃* sp4DerivedBorel F :=
    MulEquiv.ofBijective (a.subgroupComap (sp4DerivedBorel F))
      ⟨fun x y hxy => Subtype.ext (ha (congrArg Subtype.val hxy)),
        a.subgroupComap_surjective_of_surjective _ (actorToModel_surjective S hP e)⟩
  let bd : sp4DerivedBorel F →* borel (F := F) := {
    toFun b := ⟨b.val.val,b.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let ed : sp4DerivedBorel F ≃* borel (F := F) := MulEquiv.ofBijective bd ⟨by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : borel (F := F) => z.val) hxy, by
      intro b
      obtain ⟨g,hg⟩ := ef.surjective b.val
      dsimp only [ef] at hg
      rw [derivedEquivFull_of_card_gt_two_apply] at hg
      refine ⟨⟨g,?_⟩,Subtype.ext hg⟩
      change (g : Sp F) ∈ borel
      rw [hg]
      exact b.property⟩
  exact ⟨((overlapToCover S hP e he).pCoreQuotientEquiv
    (overlapToCover_surjective S hP e he) (overlapToCover_kernel_two S hP e he)).trans
    ((QuotientGroup.congr _ _ (eb.trans ed) (pCore_map_iso 2 (eb.trans ed))).trans
      (EvenBorelTorus.quotientTorusEquiv hF))⟩

/-- Every supplied odd Hall subgroup is the full split torus under the source marking. -/
theorem hall_equiv
    (S : Sylow 2 X) (hP : ChapterB.IsMinimalParabolicOver S ⊤) {K : Subgroup X}
    (hK : K.IsCComponent) (hc : SingleClauses (ChapterB.minimalParabolicMax S hP) K S)
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : sourceImage (ChapterB.minimalParabolicMax S hP) K ≃* Sp4Derived F)
    (he : (componentOverlap (ChapterB.minimalParabolicMax S hP) K).map e.toMonoidHom =
      sp4DerivedBorel F)
    (Y : Subgroup (ChapterB.minimalParabolicMax S hP))
    (hY : IsHallSubgroup OddHall.oddPrimes Y) : Nonempty (Y ≃* (Fˣ × Fˣ)) := by
  let M := ChapterB.minimalParabolicMax S hP
  let N := K.subgroupOf M
  let : K.Normal := single_component_normal S hK hc
  have hYN : Y ≤ N := OddHall.odd_subgroup_le N Y
    (single_overlap_quotient_two S (ChapterB.minimalParabolicMax_spec S hP).2 hc)
    (OddHall.odd_hall_odd hY)
  obtain ⟨eN⟩ := overlap_quotient S hP hK hc hf hF e he
  have ho : Odd (pCore 2 N).index := by
    rw [index_eq_card,Nat.card_congr eN.toEquiv]
    exact Nat.coprime_two_left.mp (EvenBorelTorus.torus_odd hF)
  let P : Sylow 2 N := pCore_isPGroup.toSylow
    (Nat.not_even_iff_odd.mpr ho ∘ even_iff_two_dvd.mpr)
  have hcY : (Y.subgroupOf N).IsComplement' (pCore 2 N) :=
    (OddHall.sylow_complement_of_hall P (hY.subgroupOf hYN)).symm
  exact ⟨((subgroupOfEquivOfLe hYN).symm.trans hcY.QuotientMulEquiv.symm).trans eN⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.SymplecticCartan
