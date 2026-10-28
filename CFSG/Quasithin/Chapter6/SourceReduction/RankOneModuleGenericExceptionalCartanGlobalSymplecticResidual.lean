module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalSymplecticHall
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.SymplecticFour
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NormalClauses
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Constructing the symplectic Hall marking from the residual quotient

Assume the literal quotient O²(X)/O₂(O²(X)) is PSp₄(2ᶠ), f > 1.
The residual is a genuine normal C-component by its perfect two-core
quotient. Its image in X/O₂(X) is centerless, so the original E.2.2 center
identity proves core_X(M) = O₂(X). The minimal-parabolic symplectic theorem
then marks the actual maximal overlap as the flag Borel, on the original
Sylow and via the same component equivalence.

Applying the proved marked Hall calculation identifies each prescribed
odd Hall subgroup of M with Fˣ × Fˣ. In particular, the later order-nine
application needs no additional component, field identification or Borel
marking. The internal ChapterB import retains its existing maximal-core
convention without changing a public boundary.

Source: Aschbacher–Smith E.2.2(2b), pp.215–216; 5.1.10 and the final
paragraph of 5.2.2, printed pp.634,648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.SymplecticCartan
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open DiagramHall SymplecticCovered
variable {X : Type*} [Group X] [Finite X]

/-- Construct the marking and Hall torus from the literal intrinsic residual quotient. -/
theorem residual_hall_equiv (S : Sylow 2 X)
    (hP : ChapterB.IsMinimalParabolicOver S ⊤) (hs : ¬ Group.IsSolvable X)
    {f : ℕ} (hf : 1 < f)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 X) ⧸ pCore 2 (pResidual 2 X)) 2 (2 ^ f))
    (Y : Subgroup (ChapterB.minimalParabolicMax S hP))
    (hY : IsHallSubgroup OddHall.oddPrimes Y) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ f ∧ Nonempty (Y ≃* (Fˣ × Fˣ)) := by
  let K := pResidual 2 X
  let M := ChapterB.minimalParabolicMax S hP
  obtain ⟨F,hF,hfin,hcard,⟨er⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hq : 3 < Nat.card F := by
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ f by omega)
    omega
  let e0 : (K ⧸ pCore 2 K) ≃* Sp F := er.trans EvenProjective.equiv.symm
  let : IsQuasisimple (Sp F) := CentralCovers.Even.isQuasisimple hq
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv e0.symm
  have hK : K.IsCComponent := isCComponent_of_isPPerfect_of_quasisimple_core_quotient
    (inferInstance : K.Normal).isSubnormal (isPPerfect_pResidual 2)
  have hc := source_single_clauses S hP hs K hK inferInstance (pResidual_sup_sylow_eq_top S)
  let ea : actorImage K ≃* Sp F := (coreQuotientEquivImage 2 K).symm.trans e0
  have hz : center (actorImage K) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr ea ⟨x,hx⟩).property
    change ea x ∈ center (Sp F) at hh
    rw [EvenProjective.center_eq_bot,mem_bot] at hh
    exact ea.map_eq_one_iff.mp hh
  have hj : sourceKernel M = pCore 2 X := by
    apply le_antisymm _ (twoCore_le_sourceKernel S hP)
    have he := hc.kernel_center
    rw [hz,Subgroup.map_bot] at he
    simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he
  have hi : Function.Injective (actorToSource S hP K) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    rintro ⟨x,hxK⟩ hx
    obtain ⟨k,hk,rfl⟩ := hxK
    apply Subtype.ext
    have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    change QuotientGroup.mk' (sourceKernel M) k = 1 at hh
    apply (QuotientGroup.eq_one_iff _).mpr
    exact hj ▸ (QuotientGroup.eq_one_iff _).mp hh
  let ec := MulEquiv.ofBijective (actorToSource S hP K)
    ⟨hi,actorToSource_surjective S hP K⟩
  let eS : sourceImage M K ≃* Sp F := ec.symm.trans ea
  let q := QuotientGroup.mk' (sourceKernel M)
  let T := S.mapSurjective (QuotientGroup.mk'_surjective (sourceKernel M))
  let C := sourceImage M K
  have hsource := ChapterE.Structure.source_normal_simple_image S hP hs K hK
    (pResidual_sup_sylow_eq_top S)
  let : C.Normal := hsource.2.2.1
  have hmin := (ChapterE.Structure.source_star_minimal_core_free S hP).1
  have hmax : ChapterB.minimalParabolicMax T hmin = M.map q :=
    (ChapterB.minimalParabolicMax_map_core S hP q (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk'];exact le_rfl)).symm
  obtain ⟨g,_,_,hB⟩ := ChapterE.Structure.SymplecticFour.source_diagram_and_borel
    hcard hf T hmin C eS hsource.2.2.2
  let e' := eS.trans (MulAut.conj g)
  let ed := e'.trans (derivedEquivFull_of_card_gt_two (F := F) (by omega)).symm
  let ef := derivedEquivFull_of_card_gt_two (F := F) (by omega)
  have hctop : commutator (Sp F) = ⊤ := by
    let := perfect_of_card_gt_two (F := F) (by omega)
    exact Group.IsPerfect.commutator_eq_top
  have hefc : ef.toMonoidHom = (commutator (Sp F)).subtype := by
    apply MonoidHom.ext
    intro x
    exact derivedEquivFull_of_card_gt_two_apply _ x
  have hbf : (sp4DerivedBorel F).map ef.toMonoidHom = borel (F := F) := by
    rw [hefc]
    change ((borel (F := F)).subgroupOf (commutator (Sp F))).map
      (commutator (Sp F)).subtype = _
    simp only [subgroupOf_map_subtype,hctop,inf_top_eq]
  have hcomp : ef.toMonoidHom.comp ed.toMonoidHom = e'.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    simp [ef,ed]
  have he : (componentOverlap M K).map ed.toMonoidHom = sp4DerivedBorel F := by
    apply map_injective (f := ef.toMonoidHom) ef.injective
    rw [map_map,hcomp,hbf,source_overlap_coordinate]
    change ((M.map q).subgroupOf C).map e'.toMonoidHom = borel (F := F)
    rw [←hB,hmax]
    exact (comap_equiv_eq_map_symm e'.symm _).symm
  exact ⟨F,hF,hfin,inferInstance,hcard,hall_equiv S hP hK hc hf hcard ed he Y hY⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.SymplecticCartan
