module
public import Mathlib.GroupTheory.IndexNormal
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelFixed
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSelectors

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBorelThompson
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer

/-!
# Compatible Borel selectors on the original critical path

For a prescribed critical transposition, two even six-letter selectors give
paired quadratic plane movers generating S₆. Each selected Borel also generates
S₆ with that same transposition, and the original Borel generates with either
selected mover. Connected chains of transpositions certify these identities.
When the critical transposition lies in the original plane, the switch
normalizes that plane. A common square lies in every index-two subgroup of
the Borel. Its two selected conjugates and the critical transposition give
a connected chain of transpositions, so the same selectors also give joint
generation for every such subgroup.

The coprime normalizer lifting theorem lifts the switch inside the original
component through the actual cubic kernel E, with |E/Q| = 3. The no-supplement
lemma lifts the six generation identities and the paired opposite-subgroup identity. Transport to the actual first edge
of the unchanged critical path gives central fixed parts in its whole edge
seed, normalization of its Thompson mover, and containment of both opposite
seeds in that mover. Its quadratic action on the full starting seed then gives
the required triple-commutator identity. Both moving-cover orders 16 and 32
are retained.

The strengthened export retains an actual first-edge transporter and joint
generation for every index-two edge subgroup containing the starting core.
The original selector export is preserved. These are constructed selectors
for a small critical image. Large critical-image comparisons, compatible
backward critical paths and terminal contradictions (5.11)--(5.12) remain
necessary for exhaustion.
No conclusion about the whole intrinsic block or source distance four is made.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the selections and generation in (5.5)--(5.6), printed pp.915--918,
and their use in (5.7), p.919; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterB.Offenders.Six
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance.CubicFull
namespace BorelSelection
open PlaneSelection
private def step : alternatingGroup (Fin 6) := shift⁻¹

private def squareRoot : S := swap23 * (Equiv.swap 2 4 * Equiv.swap 3 5)
private def square : S := swap23 * swap45
private theorem square_in_index_two (H : Subgroup S) (hi : H.relIndex borel = 2) :
    square ∈ H := by
  let : (H.subgroupOf borel).Normal := normal_of_index_eq_two hi
  have hr : squareRoot ∈ Theory.SpecificGroups.SymmetricSix.borel := by decide
  have hp := (H.subgroupOf borel).pow_index_mem ⟨squareRoot,hr⟩
  change squareRoot ^ H.relIndex borel ∈ H at hp
  rw [hi,show squareRoot ^ 2 = square by decide] at hp
  exact hp

private theorem square_pair_generates (H : Subgroup S) (hi : H.relIndex borel = 2) :
    let P := H.map (MulAut.conj position.val).toMonoidHom
    (P ⊔ P.map (MulAut.conj step.val).toMonoidHom) ⊔ zpowers swap01 = ⊤ := by
  dsimp only
  let P := H.map (MulAut.conj position.val).toMonoidHom
  let F := (P ⊔ P.map (MulAut.conj step.val).toMonoidHom) ⊔ zpowers swap01
  let b := position.val*square*position.val⁻¹
  let d := step.val*b*step.val⁻¹
  have hb : b ∈ F := (le_sup_left.trans le_sup_left : P ≤ F)
    (mem_map_of_mem _ (square_in_index_two H hi))
  have hd : d ∈ F := (le_sup_right.trans le_sup_left : P.map _ ≤ F)
    (mem_map_of_mem _ (mem_map_of_mem _ (square_in_index_two H hi)))
  have ht : swap01 ∈ F := mem_sup_right (mem_zpowers _)
  let star (i : Fin 5) : S := (b*d)^i.val*swap01*((b*d)^i.val)⁻¹
  have hs (i : Fin 5) : star i ∈ F :=
    F.mul_mem (F.mul_mem (F.pow_mem (F.mul_mem hb hd) _) ht)
      (F.inv_mem (F.pow_mem (F.mul_mem hb hd) _))
  apply chain_generates F 1
  have cert : ∀ i : Fin 5, ∃ j k : Fin 5,
      star j*star k*star j = Equiv.swap i.castSucc i.succ := by
    intro i
    fin_cases i
    · exact ⟨0,0,by decide +kernel⟩
    · exact ⟨0,2,by decide +kernel⟩
    · exact ⟨2,3,by decide +kernel⟩
    · exact ⟨3,4,by decide +kernel⟩
    · exact ⟨4,1,by decide +kernel⟩
  intro i
  obtain ⟨j,k,hjk⟩ := cert i
  change Equiv.swap i.castSucc i.succ ∈ F
  rw [←hjk]
  exact F.mul_mem (F.mul_mem (hs j) (hs k)) (hs j)

private def coordinateVectors : Fin 15 → Fin 6 → Fin 6 :=
  ![![0,1,2,3,4,5],
    ![0,2,3,1,4,5],
    ![0,3,2,1,5,4],
    ![0,4,2,1,3,5],
    ![0,5,3,1,2,4],
    ![1,2,3,0,5,4],
    ![1,3,2,0,4,5],
    ![1,4,3,0,2,5],
    ![1,5,2,0,3,4],
    ![2,3,0,1,4,5],
    ![2,4,0,3,1,5],
    ![2,5,1,3,0,4],
    ![3,4,1,2,0,5],
    ![3,5,0,2,1,4],
    ![4,5,0,1,2,3]]

private def inverseCoordinates : Fin 15 → Fin 6 → Fin 6 :=
  ![![0,1,2,3,4,5],
    ![0,3,1,2,4,5],
    ![0,3,2,1,5,4],
    ![0,3,2,4,1,5],
    ![0,3,4,2,5,1],
    ![3,0,1,2,5,4],
    ![3,0,2,1,4,5],
    ![3,0,4,2,1,5],
    ![3,0,2,4,5,1],
    ![2,3,0,1,4,5],
    ![2,4,0,3,1,5],
    ![4,2,0,3,5,1],
    ![4,2,3,0,1,5],
    ![2,4,3,0,5,1],
    ![2,3,4,5,0,1]]

private def firstChains : Fin 15 → Fin 6 → Fin 6 :=
  ![![0,1,4,5,3,2],
    ![0,1,5,4,2,3],
    ![0,1,4,5,3,2],
    ![0,1,5,4,3,2],
    ![0,1,4,5,2,3],
    ![0,1,3,2,5,4],
    ![0,1,2,3,4,5],
    ![0,1,3,2,4,5],
    ![0,1,2,3,5,4],
    ![0,1,5,4,3,2],
    ![0,1,4,5,3,2],
    ![0,1,2,3,4,5],
    ![0,1,3,2,5,4],
    ![0,1,5,4,2,3],
    ![0,1,3,2,5,4]]

private def secondChains : Fin 15 → Fin 6 → Fin 6 :=
  ![![0,1,3,2,5,4],
    ![0,1,2,3,5,4],
    ![0,1,3,2,4,5],
    ![0,1,4,5,2,3],
    ![0,1,5,4,3,2],
    ![0,1,5,4,3,2],
    ![0,1,4,5,2,3],
    ![0,1,2,3,5,4],
    ![0,1,3,2,4,5],
    ![0,1,3,2,4,5],
    ![0,1,2,3,4,5],
    ![0,1,4,5,3,2],
    ![0,1,5,4,2,3],
    ![0,1,3,2,5,4],
    ![0,1,5,4,2,3]]

private def coordinate (k : Fin 15) : S :=
  { toFun := coordinateVectors k
    invFun := inverseCoordinates k
    left_inv := by decide +revert
    right_inv := by decide +revert }
private theorem coordinate_even (k : Fin 15) : coordinate k ∈ alternatingGroup (Fin 6) := by
  have h : ∀ k : Fin 15, coordinate k ∈ alternatingGroup (Fin 6) := by decide
  exact h k
private def firstChain (k : Fin 15) : S :=
  Equiv.ofBijective (firstChains k) (by decide +revert)
private def secondChain (k : Fin 15) : S :=
  Equiv.ofBijective (secondChains k) (by decide +revert)

private theorem coordinate_complete (a : S) (ha : a.IsSwap) :
    ∃ k, coordinate k * swap01 * (coordinate k)⁻¹ = a := by
  obtain ⟨i,j,hij,rfl⟩ := ha
  have cert : ∀ i j : Fin 6, i ≠ j → ∃ k : Fin 15,
      coordinate k * swap01 * (coordinate k)⁻¹ = Equiv.swap i j := by decide
  exact cert i j hij

private theorem roots_eq (j : Fin 3) :
    roots j = Equiv.swap (![0,2,4] j) (![1,3,5] j) := by fin_cases j <;> rfl

private def stepRootChain : S := Equiv.ofBijective
  (![2,0,1,4,5,3] : Fin 6 → Fin 6) (by decide)
private def stepPairChain : S := Equiv.ofBijective
  (![0,2,5,3,1,4] : Fin 6 → Fin 6) (by decide)

private theorem step_generators :
    let P := D.map (MulAut.conj position.val).toMonoidHom
    (P ⊔ zpowers swap01) ⊔ zpowers (step.val*swap01*step.val⁻¹) = ⊤ ∧
      P ⊔ P.map (MulAut.conj step.val).toMonoidHom = ⊤ := by
  dsimp only
  constructor
  · let H := (D.map (MulAut.conj position.val).toMonoidHom ⊔ zpowers swap01) ⊔
      zpowers (step.val*swap01*step.val⁻¹)
    apply chain_generates H stepRootChain
    have cert : ∀ i : Fin 5,
        (∃ j : Fin 3, position.val*roots j*position.val⁻¹ =
          Equiv.swap (stepRootChain i.castSucc) (stepRootChain i.succ)) ∨
        swap01 = Equiv.swap (stepRootChain i.castSucc) (stepRootChain i.succ) ∨
        step.val*swap01*step.val⁻¹ = Equiv.swap (stepRootChain i.castSucc) (stepRootChain i.succ) := by decide
    intro i
    rcases cert i with ⟨j,hj⟩ | he | he
    · rw [←hj]
      exact (le_sup_left.trans le_sup_left : D.map (MulAut.conj position.val).toMonoidHom ≤ H)
        (mem_map_of_mem _ (roots_mem j))
    · rw [←he]
      exact (le_sup_right.trans le_sup_left : zpowers swap01 ≤ H) (mem_zpowers _)
    · rw [←he]
      exact (le_sup_right : zpowers (step.val*swap01*step.val⁻¹) ≤ H) (mem_zpowers _)
  · let H := D.map (MulAut.conj position.val).toMonoidHom ⊔
      (D.map (MulAut.conj position.val).toMonoidHom).map (MulAut.conj step.val).toMonoidHom
    apply chain_generates H stepPairChain
    have cert : ∀ i : Fin 5, ∃ j : Fin 3,
        position.val*roots j*position.val⁻¹ = Equiv.swap (stepPairChain i.castSucc) (stepPairChain i.succ) ∨
        step.val*(position.val*roots j*position.val⁻¹)*step.val⁻¹ =
          Equiv.swap (stepPairChain i.castSucc) (stepPairChain i.succ) := by decide
    intro i
    obtain ⟨j,hj | hj⟩ := cert i
    · rw [←hj]
      exact mem_sup_left (mem_map_of_mem _ (roots_mem j))
    · rw [←hj]
      exact mem_sup_right (mem_map_of_mem _ (mem_map_of_mem _ (roots_mem j)))

private def crossFirst : S := Equiv.swap 0 2 * (Equiv.swap 1 3 * Equiv.swap 4 5)
private def crossSecond : S := Equiv.swap 0 4 * (Equiv.swap 1 5 * Equiv.swap 2 3)
private def borelSecondChain : S := Equiv.ofBijective
  (![2,5,4,0,1,3] : Fin 6 → Fin 6) (by decide)

private theorem step_borel_generators :
    let B := borel.map (MulAut.conj position.val).toMonoidHom
    B ⊔ zpowers swap01 = ⊤ ∧
      B.map (MulAut.conj step.val).toMonoidHom ⊔ zpowers swap01 = ⊤ := by
  dsimp only
  have hP : D.map (MulAut.conj position.val).toMonoidHom ≤
      borel.map (MulAut.conj position.val).toMonoidHom := map_mono BorelCalculation.plane_le_borel
  constructor
  · let H := borel.map (MulAut.conj position.val).toMonoidHom ⊔ zpowers swap01
    have hv : crossFirst ∈ borel.map (MulAut.conj position.val).toMonoidHom := by
      refine ⟨position.val⁻¹*crossFirst*position.val,?_,?_⟩
      · obtain ⟨i,hi⟩ : ∃ i : Fin 16, BorelCalculation.words i =
            position.val⁻¹*crossFirst*position.val := by decide
        rw [←hi]
        exact BorelCalculation.words_in_borel i
      ·
        change position.val*(position.val⁻¹*crossFirst*position.val)*position.val⁻¹=crossFirst
        group
    have he : crossFirst*swap01*crossFirst⁻¹ = shift.val*swap01*shift.val⁻¹ := by decide
    apply top_unique
    rw [←standard_generators.1]
    refine sup_le (sup_le (hP.trans le_sup_left) le_sup_right) (zpowers_le.mpr ?_)
    rw [←he]
    exact H.mul_mem (H.mul_mem (mem_sup_left hv) (mem_sup_right (mem_zpowers _)))
      (H.inv_mem (mem_sup_left hv))
  · let B := (borel.map (MulAut.conj position.val).toMonoidHom).map (MulAut.conj step.val).toMonoidHom
    let H := B ⊔ zpowers swap01
    have hv : crossSecond ∈ B := by
      refine ⟨step.val⁻¹*crossSecond*step.val,?_,?_⟩
      · refine ⟨position.val⁻¹*(step.val⁻¹*crossSecond*step.val)*position.val,?_,?_⟩
        · obtain ⟨i,hi⟩ : ∃ i : Fin 16, BorelCalculation.words i =
              position.val⁻¹*(step.val⁻¹*crossSecond*step.val)*position.val := by decide
          rw [←hi]
          exact BorelCalculation.words_in_borel i
        ·
          change position.val*(position.val⁻¹*(step.val⁻¹*crossSecond*step.val)*position.val)*position.val⁻¹=_
          group
      · change step.val*(step.val⁻¹*crossSecond*step.val)*step.val⁻¹=_
        group
    have he : crossSecond*swap01*crossSecond⁻¹=swap45 := by decide
    have h45 : swap45 ∈ H := by
      rw [←he]
      exact H.mul_mem (H.mul_mem (mem_sup_left hv) (mem_sup_right (mem_zpowers _)))
        (H.inv_mem (mem_sup_left hv))
    apply chain_generates H borelSecondChain
    have cert : ∀ i : Fin 5,
        (∃ j : Fin 3, step.val*(position.val*roots j*position.val⁻¹)*step.val⁻¹ =
          Equiv.swap (borelSecondChain i.castSucc) (borelSecondChain i.succ)) ∨
        swap01 = Equiv.swap (borelSecondChain i.castSucc) (borelSecondChain i.succ) ∨
        swap45 = Equiv.swap (borelSecondChain i.castSucc) (borelSecondChain i.succ) := by decide
    intro i
    rcases cert i with ⟨j,hj⟩ | he | he
    · rw [←hj]
      exact mem_sup_left ((map_mono hP) (mem_map_of_mem _ (mem_map_of_mem _ (roots_mem j))))
    · rw [←he]
      exact mem_sup_right (mem_zpowers _)
    · rwa [←he]

private theorem fixed_generators (k : Fin 15) :
    let c := coordinate k
    let P := D.map (MulAut.conj (c*position.val)).toMonoidHom
    let x := c*step.val*c⁻¹
    D ⊔ P = ⊤ ∧ D ⊔ P.map (MulAut.conj x).toMonoidHom = ⊤ := by
  dsimp only
  constructor
  · let H := D ⊔ D.map (MulAut.conj (coordinate k*position.val)).toMonoidHom
    apply chain_generates H (firstChain k)
    have cert : ∀ k : Fin 15, ∀ i : Fin 5, ∃ j : Fin 3,
        roots j = Equiv.swap (firstChain k i.castSucc) (firstChain k i.succ) ∨
        (coordinate k*position.val)*roots j*(coordinate k*position.val)⁻¹ =
          Equiv.swap (firstChain k i.castSucc) (firstChain k i.succ) := by
      simp only [roots_eq, ←Equiv.swap_apply_apply]
      decide
    intro i
    obtain ⟨j,hj | hj⟩ := cert k i
    · rw [←hj]
      exact mem_sup_left (roots_mem j)
    · rw [←hj]
      exact mem_sup_right (mem_map_of_mem _ (roots_mem j))
  · rw [map_conj_comp]
    have he : (coordinate k*step.val*(coordinate k)⁻¹)*(coordinate k*position.val) =
        coordinate k*step.val*position.val := by group
    rw [he]
    let H := D ⊔ D.map (MulAut.conj (coordinate k*step.val*position.val)).toMonoidHom
    apply chain_generates H (secondChain k)
    have cert : ∀ k : Fin 15, ∀ i : Fin 5, ∃ j : Fin 3,
        roots j = Equiv.swap (secondChain k i.castSucc) (secondChain k i.succ) ∨
        (coordinate k*step.val*position.val)*roots j*(coordinate k*step.val*position.val)⁻¹ =
          Equiv.swap (secondChain k i.castSucc) (secondChain k i.succ) := by
      simp only [roots_eq, ←Equiv.swap_apply_apply]
      decide
    intro i
    obtain ⟨j,hj | hj⟩ := cert k i
    · rw [←hj]
      exact mem_sup_left (roots_mem j)
    · rw [←hj]
      exact mem_sup_right (mem_map_of_mem _ (roots_mem j))

private theorem coordinate_normalizes (k : Fin 15)
    (hk : coordinate k * swap01 * (coordinate k)⁻¹ ∈ D) :
    coordinate k ∈ normalizer (D : Set S) := by
  rw [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq] at hk
  obtain ⟨i,hi⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) _).mp hk
  have cert : ∀ k : Fin 15, ∀ i : Fin 8,
      dWords i = coordinate k * swap01 * (coordinate k)⁻¹ →
      ∀ j : Fin 3, ∃ m : Fin 3,
        coordinate k * roots j * (coordinate k)⁻¹ = roots m := by
    simp only [roots_eq, ←Equiv.swap_apply_apply]
    decide
  have hr : ∀ j : Fin 3, coordinate k * roots j * (coordinate k)⁻¹ ∈ D := by
    intro j
    obtain ⟨m,hm⟩ := cert k i hi j
    rw [hm]
    exact roots_mem m
  rw [mem_normalizer_iff_map_conj_eq]
  apply eq_of_le_of_card_ge
  · rw [map_le_iff_le_comap,D,closure_le]
    intro a ha
    rcases ha with rfl | rfl | rfl
    · exact hr 0
    · exact hr 1
    · exact hr 2
  · rw [card_map_of_injective (MulAut.conj (coordinate k)).injective]

private theorem choices (u a : S) (ha : a.IsSwap) :
    ∃ k x : alternatingGroup (Fin 6),
      let E := D.map (MulAut.conj u).toMonoidHom
      let P := E.map (MulAut.conj k.val).toMonoidHom
      (P ⊔ zpowers a) ⊔ (zpowers a).map (MulAut.conj x.val).toMonoidHom = ⊤ ∧
        P ⊔ P.map (MulAut.conj x.val).toMonoidHom = ⊤ ∧
        E ⊔ P = ⊤ ∧ E ⊔ P.map (MulAut.conj x.val).toMonoidHom = ⊤ ∧
        (borel.map (MulAut.conj u).toMonoidHom).map (MulAut.conj k.val).toMonoidHom ⊔ zpowers a = ⊤ ∧
        ((borel.map (MulAut.conj u).toMonoidHom).map (MulAut.conj k.val).toMonoidHom).map
          (MulAut.conj x.val).toMonoidHom ⊔ zpowers a = ⊤ ∧
        (a ∈ E → x.val ∈ normalizer (E : Set S)) ∧
        (∀ H : Subgroup S, H.relIndex (borel.map (MulAut.conj u).toMonoidHom) = 2 →
          let H₁ := H.map (MulAut.conj k.val).toMonoidHom
          (H₁ ⊔ H₁.map (MulAut.conj x.val).toMonoidHom) ⊔ zpowers a = ⊤) := by
  let b := u⁻¹*a*u
  have hb : b.IsSwap := by
    obtain ⟨i,j,hij,rfl⟩ := ha
    change (u⁻¹*Equiv.swap i j*(u⁻¹)⁻¹).IsSwap
    rw [←Equiv.swap_apply_apply]
    exact ⟨_,_,u.symm.injective.ne hij,rfl⟩
  obtain ⟨t,hc⟩ := coordinate_complete b hb
  let c : alternatingGroup (Fin 6) := ⟨coordinate t,coordinate_even t⟩
  let w := u*c.val
  let k : alternatingGroup (Fin 6) := MulAut.conjNormal u (c*position)
  let x : alternatingGroup (Fin 6) := MulAut.conjNormal w step
  let f := (MulAut.conj w).toMonoidHom
  let fu := (MulAut.conj u).toMonoidHom
  have ha' : f swap01 = a := by
    change (u*c.val)*swap01*(u*c.val)⁻¹=a
    calc
      _ = u*(c.val*swap01*c.val⁻¹)*u⁻¹ := by group
      _ = a := by rw [show c.val*swap01*c.val⁻¹=b from hc]; dsimp [b]; group
  have hP (B : Subgroup S) : (B.map (MulAut.conj u).toMonoidHom).map (MulAut.conj k.val).toMonoidHom =
      (B.map (MulAut.conj position.val).toMonoidHom).map f := by
    rw [map_conj_comp,map_conj_comp]
    congr 3
    change (u*(c.val*position.val)*u⁻¹)*u=(u*c.val)*position.val
    group
  have hPx (A : Subgroup S) : (A.map f).map (MulAut.conj x.val).toMonoidHom =
      (A.map (MulAut.conj step.val).toMonoidHom).map f := by
    rw [map_conj_comp,map_conj_comp]
    congr 3
    change (w*step.val*w⁻¹)*w=w*step.val
    group
  refine ⟨k,x,?_⟩
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hP]
    have hh := congrArg (Subgroup.map f) step_generators.1
    rw [Subgroup.map_sup,Subgroup.map_sup,MonoidHom.map_zpowers,ha',
      map_top_of_surjective f (MulAut.conj w).surjective] at hh
    have hz' : (zpowers a).map (MulAut.conj x.val).toMonoidHom =
        (zpowers (step.val*swap01*step.val⁻¹)).map f := by
      rw [←ha',←MonoidHom.map_zpowers,hPx,MonoidHom.map_zpowers]
      rfl
    rwa [hz']
  · rw [hP,hPx]
    have hh := congrArg (Subgroup.map f) step_generators.2
    rwa [Subgroup.map_sup,map_top_of_surjective f (MulAut.conj w).surjective] at hh
  · have hh := congrArg (Subgroup.map fu) (fixed_generators t).1
    rw [Subgroup.map_sup,map_top_of_surjective fu (MulAut.conj u).surjective] at hh
    convert hh using 1
    rw [map_conj_comp,map_conj_comp]
    congr 4
    change (u*(c.val*position.val)*u⁻¹)*u=u*(coordinate t*position.val)
    dsimp only [c]
    group
  · have hh := congrArg (Subgroup.map fu) (fixed_generators t).2
    rw [Subgroup.map_sup,map_top_of_surjective fu (MulAut.conj u).surjective] at hh
    convert hh using 1
    rw [map_conj_comp,map_conj_comp,map_conj_comp,map_conj_comp]
    congr 4
    change (w*step.val*w⁻¹)*((u*(c.val*position.val)*u⁻¹)*u) =
      u*(coordinate t*step.val*(coordinate t)⁻¹)*(coordinate t*position.val)
    dsimp only [w,c]
    group
  · rw [hP]
    have hh := congrArg (Subgroup.map f) step_borel_generators.1
    rwa [Subgroup.map_sup,MonoidHom.map_zpowers,ha',
      map_top_of_surjective f (MulAut.conj w).surjective] at hh
  · rw [hP,hPx]
    have hh := congrArg (Subgroup.map f) step_borel_generators.2
    rwa [Subgroup.map_sup,MonoidHom.map_zpowers,ha',
      map_top_of_surjective f (MulAut.conj w).surjective] at hh

  · intro haE
    have hbD : b ∈ D := by
      obtain ⟨d,hd,he⟩ := haE
      have hback : b=d := by dsimp [b]; rw [←he]; change u⁻¹*(u*d*u⁻¹)*u=d; group
      rwa [hback]
    have hcN : c.val ∈ normalizer (D : Set S) := by
      apply coordinate_normalizes t
      rwa [hc]
    have hstep : step.val ∈ normalizer (D : Set S) :=
      (normalizer (D : Set S)).inv_mem shift_normalizes
    have hcx : c.val*step.val*c.val⁻¹ ∈ normalizer (D : Set S) :=
      (normalizer (D : Set S)).mul_mem
        ((normalizer (D : Set S)).mul_mem hcN hstep)
        ((normalizer (D : Set S)).inv_mem hcN)
    rw [mem_normalizer_iff_map_conj_eq] at hcx ⊢
    change (D.map (MulAut.conj u).toMonoidHom).map (MulAut.conj x.val).toMonoidHom = _
    change D.map (MulAut.conj (c.val*step.val*c.val⁻¹)).toMonoidHom = D at hcx
    rw [map_conj_comp]
    have he : x.val*u=u*(c.val*step.val*c.val⁻¹) := by
      change ((u*c.val)*step.val*(u*c.val)⁻¹)*u=u*(c.val*step.val*c.val⁻¹)
      group
    rw [he,←map_conj_comp,hcx]

  · intro H hi
    let H₀ := H.map (MulAut.conj u⁻¹).toMonoidHom
    have hH : H₀.map (MulAut.conj u).toMonoidHom = H := by
      dsimp only [H₀]
      rw [map_conj_comp,mul_inv_cancel]
      change H.map (MonoidHom.id S) = H
      exact map_id H
    have hhi : H₀.relIndex borel = 2 := by
      have hh := relIndex_map_map_of_injective
        (f := (MulAut.conj u).toMonoidHom) H₀ borel (MulAut.conj u).injective
      rw [hH] at hh
      exact hh.symm.trans hi
    rw [←hH,hP,hPx]
    have hh := congrArg (Subgroup.map f) (square_pair_generates H₀ hhi)
    rwa [Subgroup.map_sup,Subgroup.map_sup,MonoidHom.map_zpowers,ha',
      map_top_of_surjective f (MulAut.conj w).surjective] at hh

end BorelSelection
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf M
local notation "Rg" => edge L R
local notation "W" => (⁅centralOmega L R,K⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem borel_plane_lifts (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup M) (a : S) (ha : a.IsSwap) (hA : A.map π = zpowers a)
    (hAF : A.map π ≤ (borelPlane h e hz hk u).map π) :
    ∃ g ∈ K, ∃ r ∈ K,
      let F := borelPlane h e hz hk u
      let P := F.map (MulAut.conj g).toMonoidHom
      (P ⊔ A) ⊔ A.map (MulAut.conj r).toMonoidHom = ⊤ ∧
        P ⊔ P.map (MulAut.conj r).toMonoidHom = ⊤ ∧
        Rg ⊔ P = ⊤ ∧ Rg ⊔ P.map (MulAut.conj r).toMonoidHom = ⊤ ∧
        (Rg).map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ ∧
        ((Rg).map (MulAut.conj g).toMonoidHom).map (MulAut.conj r).toMonoidHom ⊔ A = ⊤ ∧
        r ∈ normalizer (F : Set M) ∧
        (∀ J : Subgroup M, pCore 2 M ≤ J → J ≤ Rg → J.relIndex Rg = 2 →
          let J₁ := J.map (MulAut.conj g).toMonoidHom
          (J₁ ⊔ J₁.map (MulAut.conj r).toMonoidHom) ⊔ A = ⊤) := by
  obtain ⟨k,x,hgen,hpair,hfirst,hsecond,hBfirst,hBsecond,hpos,hopposite⟩ := BorelSelection.choices u a ha
  obtain ⟨g,hg,hgk⟩ : k.val ∈ (K).map π := by
    rw [CubicAction.component_image h e hz hk]
    exact k.property
  have hpos' : x.val ∈ normalizer ((borelPlane h e hz hk u).map π : Set S) := by
    rw [borelPlane_image h e hz hk u hR]
    apply hpos
    have hh := hAF
    rw [hA,borelPlane_image h e hz hk u hR] at hh
    exact hh (mem_zpowers _)
  obtain ⟨r,hr,hrN,hrx⟩ := cubic_two_normalizer_component_lift h e hz hk
    (borelPlane h e hz hk u) (h.relative_radical.isPGroup.to_le inf_le_left)
    (borelPlane_core_le h e hz hk u) x hpos'
  let F := borelPlane h e hz hk u
  let P := F.map (MulAut.conj g).toMonoidHom
  have hFm : F.map π = D.map (MulAut.conj u).toMonoidHom :=
    borelPlane_image h e hz hk u hR
  have hPm : P.map π = (D.map (MulAut.conj u).toMonoidHom).map
      (MulAut.conj k.val).toMonoidHom := by
    rw [selection_map_conj,hFm,hgk]
  have hQP : pCore 2 M ≤ P := by
    have hQ : (pCore 2 M).map (MulAut.conj g).toMonoidHom = pCore 2 M :=
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
    rw [←hQ]
    exact map_mono (borelPlane_core_le h e hz hk u)
  have lift (B : Subgroup M) (hQB : pCore 2 M ≤ B) (hB : B.map π = ⊤) : B = ⊤ := by
    have hBE : B ⊔ extensionKernel h = ⊤ := by
      have he := congrArg (Subgroup.comap π) hB
      rwa [comap_map_eq,CubicAction.projection_kernel h e hz hk,comap_top] at he
    have hEB := extensionKernel_no_supplement h B (hBE ▸ (le_top : K ≤ ⊤))
    rw [extensionKernel_twoCore h,sup_of_le_left hQB] at hEB
    rwa [sup_of_le_left hEB] at hBE
  refine ⟨g,hg,r,hr,?_,?_,?_,?_,?_,?_,hrN,?_⟩
  · apply lift _ (hQP.trans (le_sup_left.trans le_sup_left))
    rw [Subgroup.map_sup,Subgroup.map_sup,selection_map_conj π A r,hPm,hA,hrx]
    exact hgen
  · apply lift _ (hQP.trans le_sup_left)
    rw [Subgroup.map_sup,selection_map_conj π P r,hPm,hrx]
    exact hpair
  · apply lift _ (h.relative_radical.twoCore_le.trans le_sup_left)
    rw [Subgroup.map_sup,hR,hPm]
    apply top_unique
    rw [←hfirst]
    exact sup_le_sup (map_mono BorelCalculation.plane_le_borel) le_rfl
  · apply lift _ (h.relative_radical.twoCore_le.trans le_sup_left)
    rw [Subgroup.map_sup,hR,selection_map_conj π P r,hPm,hrx]
    apply top_unique
    rw [←hsecond]
    exact sup_le_sup (map_mono BorelCalculation.plane_le_borel) le_rfl
  · have hQR : pCore 2 M ≤ (Rg).map (MulAut.conj g).toMonoidHom := by
      have hQ : (pCore 2 M).map (MulAut.conj g).toMonoidHom = pCore 2 M :=
        mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
      rw [←hQ]
      exact map_mono h.relative_radical.twoCore_le
    apply lift _ (hQR.trans le_sup_left)
    rw [Subgroup.map_sup,selection_map_conj π Rg g,hR,hA,hgk]
    exact hBfirst
  · have hQR : pCore 2 M ≤
        ((Rg).map (MulAut.conj g).toMonoidHom).map (MulAut.conj r).toMonoidHom := by
      have hQ (v : M) : (pCore 2 M).map (MulAut.conj v).toMonoidHom = pCore 2 M :=
        mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top v)
      rw [←hQ r]
      apply map_mono
      rw [←hQ g]
      exact map_mono h.relative_radical.twoCore_le
    apply lift _ (hQR.trans le_sup_left)
    rw [Subgroup.map_sup,selection_map_conj π _ r,selection_map_conj π Rg g,hR,hA,hgk,hrx]
    exact hBsecond

  · intro J hQJ hJR hi
    have hji : (J.map π).relIndex ((Rg).map π) = 2 := by
      have hm := relIndex_mul_relIndex (⊥ : Subgroup S) (J.map π) ((Rg).map π)
        bot_le (map_mono hJR)
      rw [relIndex_bot_left,relIndex_bot_left,
        CubicAction.permutation_image_card_of_two h e hz hk J
        (h.relative_radical.isPGroup.to_le hJR),
        CubicAction.permutation_image_card_of_two h e hz hk Rg h.relative_radical.isPGroup] at hm
      have hn := relIndex_mul_relIndex (pCore 2 M) J Rg hQJ hJR
      rw [hi] at hn
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (index_ne_zero_of_finite))
        (hm.trans hn.symm)
    have hQJ₁ : pCore 2 M ≤ J.map (MulAut.conj g).toMonoidHom := by
      have hQ : (pCore 2 M).map (MulAut.conj g).toMonoidHom = pCore 2 M :=
        mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
      rw [←hQ]
      exact map_mono hQJ
    dsimp only
    apply lift _ (hQJ₁.trans (le_sup_left.trans le_sup_left))
    rw [Subgroup.map_sup,Subgroup.map_sup,selection_map_conj π _ r,
      selection_map_conj π J g,hgk,hrx,hA]
    exact hopposite (J.map π) (hR ▸ hji)

include h e hz hk in
/-- The compatible selectors when the critical path starts along the base edge. -/
private theorem borel_small_critical_seed_selectors_base (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hfirst : p.walk.getVert 1 = beta Rg) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ K,
      let x := (embedM Rg r)⁻¹
      let J := edgeOffenderJoin (alpha Rg) t
      let J' := edgeOffenderJoin (alpha Rg) (act Rg x t)
      (J ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        J ⊔ J' = stabilizer Rg (alpha Rg) ∧
        Q Rg (beta Rg) ⊔ J = stabilizer Rg (alpha Rg) ∧
        Q Rg (beta Rg) ⊔ J' = stabilizer Rg (alpha Rg) ∧
        Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
        Q Rg (act Rg x t) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
        Z Rg (beta Rg) ⊓ centralizer (J : Set (FreeAmalgam Rg)) ≤
          centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
        Z Rg (beta Rg) ⊓ centralizer (J' : Set (FreeAmalgam Rg)) ≤
          centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
        x ∈ normalizer (edgeOffenderJoin (alpha Rg) (beta Rg) : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (beta Rg) ∧
        ∃ y ∈ stabilizer Rg (alpha Rg), act Rg y (beta Rg) = t ∧
          ∀ J₀ : Subgroup (FreeAmalgam Rg), Q Rg (alpha Rg) ≤ J₀ →
            J₀ ≤ Q Rg (beta Rg) → J₀.relIndex (Q Rg (beta Rg)) = 2 →
            let J₁ := J₀.map (MulAut.conj y⁻¹).toMonoidHom
            (J₁ ⊔ J₁.map (MulAut.conj x⁻¹).toMonoidHom) ⊔ Z Rg z =
              stabilizer Rg (alpha Rg) := by
  let i := embedM Rg
  let F := borelPlane h e hz hk u
  let A := (Z Rg z).comap i
  have hAm : A.map i = Z Rg z := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base Rg))
  obtain ⟨a,ha,hA⟩ := small_critical_image_eq_swap h e hz hk p hsmall
  have hZedge : Z Rg z ≤ Q Rg (beta Rg) := by
    rw [←hfirst]
    apply Z_le_Q_of_dist_lt Rg z ((sourceGeometry h).exists_critical z p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(sourceGeometry h).distance_constant z p.end_color]
    change p.walk.length-1<(sourceGeometry h).b Rg
    rw [←p.length_eq_b]
    have hp : 0 < p.walk.length := p.length_eq_b ▸ sourceDistance_pos h
    omega
  have hAT : A ≤ Rg := by
    apply (map_le_map_iff_of_injective (embedM_injective Rg)).mp
    change A.map i ≤ (Rg).map i
    rw [hAm,←Q_beta]
    exact hZedge
  have hAF := remaining_small_image_le_plane h e hz hk u (Or.inr hR) A hAT a ha hA
  obtain ⟨g,hg,r,hr,hgen,hpair,hfirst,hsecond,hBfirst,hBsecond,hrN,hopposite⟩ :=
    borel_plane_lifts h e hz hk u hR A a ha hA hAF
  let f := (i g)⁻¹
  let x := (i r)⁻¹
  let t := act Rg f (beta Rg)
  have fixed (v : M) : act Rg ((i v)⁻¹) (alpha Rg) = alpha Rg := by
    have hv : (i v)⁻¹ ∈ stabilizer Rg (alpha Rg) := by
      change (i v)⁻¹ ∈ stabilizer Rg (mVertex Rg 1)
      rw [stabilizer_m_base]
      exact ⟨v⁻¹,by simp only [i,map_inv]⟩
    exact hv
  have hat : Adjacent Rg (alpha Rg) t := by
    rw [←fixed g]
    exact (adjacent_act_iff Rg f (alpha Rg) (beta Rg)).mpr (base_adjacent Rg)
  have hat' : Adjacent Rg (alpha Rg) (act Rg x t) := by
    rw [←fixed r]
    exact (adjacent_act_iff Rg x (alpha Rg) t).mpr hat
  have chart (v : M) : edgeOffenderJoin (alpha Rg) (act Rg ((i v)⁻¹) (beta Rg)) =
      (F.map (MulAut.conj v).toMonoidHom).map i := by
    let j := i.comp (MulAut.conj v).toMonoidHom
    have hadj : Adjacent Rg (alpha Rg) (act Rg ((i v)⁻¹) (beta Rg)) := by
      rw [←fixed v]
      exact (adjacent_act_iff Rg ((i v)⁻¹) (alpha Rg) (beta Rg)).mpr (base_adjacent Rg)
    have hQ : (pCore 2 M).map (MulAut.conj v).toMonoidHom = pCore 2 M :=
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top v)
    have hW : (W).map (MulAut.conj v).toMonoidHom = W := by
      let := h.relative_normal
      exact mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top v)
    have hJR : (Rg).map j = Q Rg (act Rg ((i v)⁻¹) (beta Rg)) := by
      rw [Q_act,Q_beta,inv_inv]
      change (Rg).map (i.comp (MulAut.conj v).toMonoidHom) = _
      rw [←map_map]
      exact selection_map_conj i Rg v
    have hJQ : (pCore 2 M).map j = Q Rg (alpha Rg) := by
      rw [←map_map,hQ,Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    have hJW : (W).map j = U Rg (alpha Rg) := by
      rw [←map_map,hW,graph_U_map h e hz]
    have hh := remaining_join_in_chart h e hz hk u (Or.inr hR) rfl hadj j
      ((embedM_injective Rg).comp (MulAut.conj v).injective) hJR hJQ hJW
    simpa only [j,map_map] using hh
  have ht : edgeOffenderJoin (alpha Rg) t = (F.map (MulAut.conj g).toMonoidHom).map i := chart g
  have htt : act Rg x t = act Rg ((i (r*g))⁻¹) (beta Rg) := by
    dsimp [t,x,f]
    rw [map_mul,mul_inv_rev,act_mul]
  have ht' : edgeOffenderJoin (alpha Rg) (act Rg x t) =
      ((F.map (MulAut.conj g).toMonoidHom).map (MulAut.conj r).toMonoidHom).map i := by
    rw [htt,chart]
    congr 1
    rw [map_map]
    congr 1
    apply MonoidHom.ext
    intro v
    change (r*g)*v*(r*g)⁻¹=r*(g*v*g⁻¹)*r⁻¹
    group
  have map_top (B : Subgroup M) (hB : B = ⊤) : B.map i = stabilizer Rg (alpha Rg) := by
    rw [hB,←MonoidHom.range_eq_map]
    exact (stabilizer_m_base Rg).symm
  have hG := map_top _ hgen
  rw [Subgroup.map_sup,Subgroup.map_sup,selection_map_conj i A r,hAm,←ht] at hG
  have hZ : (Z Rg z).map (MulAut.conj (i r)).toMonoidHom = Z Rg (act Rg x z) := by
    rw [Z_act,show x⁻¹=i r from inv_inv _]
  rw [hZ] at hG
  have hJJ := map_top _ hpair
  rw [Subgroup.map_sup,←ht,←ht'] at hJJ
  have hfirst' := map_top _ hfirst
  rw [Subgroup.map_sup,←Q_beta Rg,←ht] at hfirst'
  have hsecond' := map_top _ hsecond
  rw [Subgroup.map_sup,←Q_beta Rg,←ht'] at hsecond'
  have hQt : ((Rg).map (MulAut.conj g).toMonoidHom).map i = Q Rg t := by
    rw [Q_act,Q_beta,inv_inv]
    exact selection_map_conj i Rg g
  have hQt' : (((Rg).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj r).toMonoidHom).map i = Q Rg (act Rg x t) := by
    rw [Q_act,show x⁻¹=i r from inv_inv _,←hQt]
    exact selection_map_conj i _ r
  have hBfirst' := map_top _ hBfirst
  rw [Subgroup.map_sup,hQt,hAm] at hBfirst'
  have hBsecond' := map_top _ hBsecond
  rw [Subgroup.map_sup,hQt',hAm] at hBsecond'
  have fixed_seed (J₀ : Subgroup (FreeAmalgam Rg))
      (hgen₀ : Q Rg (beta Rg) ⊔ J₀ = stabilizer Rg (alpha Rg)) :
      Z Rg (beta Rg) ⊓ centralizer (J₀ : Set (FreeAmalgam Rg)) ≤
        centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
    have hseed : Z Rg (beta Rg) ≤ centralizer (Q Rg (beta Rg) : Set (FreeAmalgam Rg)) := by
      intro v hv
      rw [Z,if_neg (by change true ≠ false; decide)] at hv
      exact (mem_omegaCenter_iff.mp hv).2.2
    rintro v ⟨hv,hvJ⟩
    apply le_centralizer_iff.mp ?_ (show v ∈ zpowers v from mem_zpowers _)
    rw [←hgen₀]
    exact sup_le (le_centralizer_iff.mp (zpowers_le.mpr (hseed hv)))
      (le_centralizer_iff.mp (zpowers_le.mpr hvJ))
  have hF : edgeOffenderJoin (alpha Rg) (beta Rg) = F.map i := by
    exact remaining_join_in_chart h e hz hk u (Or.inr hR) rfl (base_adjacent Rg) i
      (embedM_injective Rg) (Q_beta Rg).symm
      (Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le).symm
      (graph_U_map h e hz)
  have hxN : x ∈ normalizer (edgeOffenderJoin (alpha Rg) (beta Rg) : Set (FreeAmalgam Rg)) := by
    rw [hF]
    exact (normalizer (F.map i : Set (FreeAmalgam Rg))).inv_mem
      (F.le_normalizer_map i (mem_map_of_mem _ hrN))
  have hAF' : A ≤ F := by
    exact le_inf hAT (map_le_iff_le_comap.mp (by
      rw [←borelPlane_image h e hz hk u hR]
      exact hAF))
  have hZJ : Z Rg z ≤ edgeOffenderJoin (alpha Rg) (beta Rg) := by
    rw [hF,←hAm]
    exact map_mono hAF'
  have hZxJ : Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (beta Rg) := by
    rw [Z_act]
    exact (map_mono hZJ).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp
        ((normalizer (edgeOffenderJoin (alpha Rg) (beta Rg) : Set (FreeAmalgam Rg))).inv_mem hxN))
  refine ⟨t,hat,r,hr,hG,hJJ,hfirst',hsecond',hBfirst',hBsecond',
    fixed_seed _ hfirst',fixed_seed _ hsecond',hxN,sup_le hZJ hZxJ,
    f,fixed g,rfl,?_⟩
  intro J₀ hQJ hJR hi
  let Jm := J₀.comap i
  have hJm : Jm.map i = J₀ := map_comap_eq_self
    (hJR.trans (by rw [Q_beta]; exact map_le_range (f := i) (H := Rg)))
  have hQJm : pCore 2 M ≤ Jm := by
    apply map_le_iff_le_comap.mp
    rw [←Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact hQJ
  have hJmR : Jm ≤ Rg := by
    apply (map_le_map_iff_of_injective (embedM_injective Rg)).mp
    rw [hJm,←Q_beta]
    exact hJR
  have hiJm : Jm.relIndex Rg = 2 := by
    have hh := relIndex_map_map_of_injective (f := i) Jm Rg (embedM_injective Rg)
    rw [hJm,←Q_beta] at hh
    exact hh.symm.trans hi
  have hh := map_top _ (hopposite Jm hQJm hJmR hiJm)
  rw [Subgroup.map_sup,Subgroup.map_sup,selection_map_conj i _ r,
    selection_map_conj i Jm g,hJm,hAm] at hh
  simpa only [f,x,inv_inv] using hh

include h e hz hk in
/-- Paired Borel movers with the same opposite seed, normalized on the actual
first edge of the critical path. All fixed-subgroup comparisons use full seeds. -/
theorem borel_small_critical_seed_selectors_with_opposite (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ K,
      let x := (embedM Rg r)⁻¹
      let J := edgeOffenderJoin (alpha Rg) t
      let J' := edgeOffenderJoin (alpha Rg) (act Rg x t)
      let b := p.walk.getVert 1
      (J ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        J ⊔ J' = stabilizer Rg (alpha Rg) ∧
        Q Rg b ⊔ J = stabilizer Rg (alpha Rg) ∧
        Q Rg b ⊔ J' = stabilizer Rg (alpha Rg) ∧
        Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
        Q Rg (act Rg x t) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
        Z Rg b ⊓ centralizer (J : Set (FreeAmalgam Rg)) ≤
          centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
        Z Rg b ⊓ centralizer (J' : Set (FreeAmalgam Rg)) ≤
          centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
        x ∈ normalizer (edgeOffenderJoin (alpha Rg) b : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) b ∧
        ⁅⁅Z Rg (alpha Rg),Z Rg z ⊔ Z Rg (act Rg x z)⁆,
          edgeOffenderJoin (alpha Rg) b⁆ = ⊥ ∧
        ∃ y ∈ stabilizer Rg (alpha Rg), act Rg y b = t ∧
          ∀ J₀ : Subgroup (FreeAmalgam Rg), Q Rg (alpha Rg) ≤ J₀ →
            J₀ ≤ Q Rg b → J₀.relIndex (Q Rg b) = 2 →
            let J₁ := J₀.map (MulAut.conj y⁻¹).toMonoidHom
            (J₁ ⊔ J₁.map (MulAut.conj x⁻¹).toMonoidHom) ⊔ Z Rg z =
              stabilizer Rg (alpha Rg) := by
  have hat₁ : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  obtain ⟨g,hg,hgβ⟩ := stabilizer_transitive_neighbors Rg (alpha Rg)
    (base_adjacent Rg) hat₁
  change act Rg g (beta Rg) = p.walk.getVert 1 at hgβ
  have hga : act Rg g (alpha Rg) = alpha Rg := hg
  have hgia : act Rg g⁻¹ (alpha Rg) = alpha Rg :=
    (stabilizer Rg (alpha Rg)).inv_mem hg
  have hgib : act Rg g⁻¹ (p.walk.getVert 1) = beta Rg := by
    rw [←hgβ,←act_mul,mul_inv_cancel,act_one]
  have hp0 : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ (alpha Rg)) (act Rg g⁻¹ z),
      p₀.walk.getVert 1 = act Rg g⁻¹ (p.walk.getVert 1) :=
    ⟨p.act g⁻¹,by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hgia,hgib] at hp0
  obtain ⟨p₀,hp₀⟩ := hp0
  have hsmall₀ : (Q Rg (act Rg g⁻¹ z)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hgia,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹⁻¹).injective]
    exact hsmall
  obtain ⟨t₀,hat₀,r₀,hr₀,hgen,hpair,hfirst,hsecond,hBfirst,hBsecond,_,_,hnorm,hcontained,y₀,hy₀,hyt₀,hopposite⟩ :=
    borel_small_critical_seed_selectors_base h e hz hk u hR p₀ hsmall₀ hp₀
  have hgm : g ∈ (embedM Rg).range := by
    change g ∈ Mbar Rg
    rwa [←stabilizer_m_base Rg]
  obtain ⟨m,hm⟩ := hgm
  let r := m⁻¹*r₀*m
  have hr : r ∈ K := by
    let := h.relative_normal
    exact (inferInstance : (K).Normal).conj_mem' r₀ hr₀ m
  let x₀ := (embedM Rg r₀)⁻¹
  let x := (embedM Rg r)⁻¹
  have hx : x = g⁻¹*x₀*g := by
    dsimp only [x,r,x₀]
    rw [map_mul,map_mul,map_inv,hm]
    group
  have hact (v : Vertex Rg) : act Rg x (act Rg g v) = act Rg g (act Rg x₀ v) := by
    rw [hx,←act_mul,←act_mul]
    congr 1
    group
  have hcancel (v : Vertex Rg) : act Rg g (act Rg g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hat : Adjacent Rg (alpha Rg) (act Rg g t₀) := by
    rw [←hga]
    exact (adjacent_act_iff Rg g _ _).mpr hat₀
  have hxt₀ : Adjacent Rg (alpha Rg) (act Rg x₀ t₀) := by
    have hx₀ : act Rg x₀ (alpha Rg) = alpha Rg := by
      change (embedM Rg r₀)⁻¹ ∈ stabilizer Rg (mVertex Rg 1)
      rw [stabilizer_m_base]
      exact ⟨r₀⁻¹,by rw [map_inv]⟩
    rw [←hx₀]
    exact (adjacent_act_iff Rg x₀ _ _).mpr hat₀
  have chart (t : Vertex Rg) (ht : Adjacent Rg (alpha Rg) t) :
      edgeOffenderJoin (alpha Rg) (act Rg g t) =
        (edgeOffenderJoin (alpha Rg) t).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [hga] using remaining_edge_join_act h e hz hk u (Or.inr hR) rfl ht g
  have hstab : (stabilizer Rg (alpha Rg)).map (MulAut.conj g⁻¹).toMonoidHom =
      stabilizer Rg (alpha Rg) := by
    rw [←stabilizer_act,hga]
  have hgen' := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
  rw [Subgroup.map_sup,Subgroup.map_sup,←chart t₀ hat₀,←Z_act,←Z_act,hcancel,
    ←hact,hcancel,hstab] at hgen'
  have hpair' := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hpair
  rw [Subgroup.map_sup,←chart t₀ hat₀,←chart (act Rg x₀ t₀) hxt₀,←hact,hstab] at hpair'
  have hfirst' := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hfirst
  rw [Subgroup.map_sup,←Q_act,hgβ,←chart t₀ hat₀,hstab] at hfirst'
  have hsecond' := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hsecond
  rw [Subgroup.map_sup,←Q_act,hgβ,←chart (act Rg x₀ t₀) hxt₀,←hact,hstab] at hsecond'
  have hBfirst' := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hBfirst
  rw [Subgroup.map_sup,←Q_act,←Z_act,hcancel,hstab] at hBfirst'
  have hBsecond' := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hBsecond
  rw [Subgroup.map_sup,←Q_act,←hact,←Z_act,hcancel,hstab] at hBsecond'
  have fixed_seed (J₀ : Subgroup (FreeAmalgam Rg))
      (hgen₀ : Q Rg (p.walk.getVert 1) ⊔ J₀ = stabilizer Rg (alpha Rg)) :
      Z Rg (p.walk.getVert 1) ⊓ centralizer (J₀ : Set (FreeAmalgam Rg)) ≤
        centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
    have hb : color Rg (p.walk.getVert 1) = true := by
      rw [←hgβ,action_preserves_color]
      rfl
    have hseed : Z Rg (p.walk.getVert 1) ≤
        centralizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg)) := by
      intro v hv
      rw [Z,if_neg (by simp [hb])] at hv
      exact (mem_omegaCenter_iff.mp hv).2.2
    rintro v ⟨hv,hvJ⟩
    apply le_centralizer_iff.mp ?_ (show v ∈ zpowers v from mem_zpowers _)
    rw [←hgen₀]
    exact sup_le (le_centralizer_iff.mp (zpowers_le.mpr (hseed hv)))
      (le_centralizer_iff.mp (zpowers_le.mpr hvJ))
  refine ⟨act Rg g t₀,hat,r,hr,hgen',hpair',hfirst',hsecond',hBfirst',hBsecond',
    fixed_seed _ hfirst',fixed_seed _ hsecond',?_,?_,?_,?_⟩
  · rw [←hgβ,chart (beta Rg) (base_adjacent Rg)]
    have hh := (edgeOffenderJoin (alpha Rg) (beta Rg)).le_normalizer_map
      (MulAut.conj g⁻¹).toMonoidHom (mem_map_of_mem _ hnorm)
    change g⁻¹*x₀*g⁻¹⁻¹ ∈ normalizer ((edgeOffenderJoin (alpha Rg) (beta Rg)).map
      (MulAut.conj g⁻¹).toMonoidHom : Set (FreeAmalgam Rg)) at hh
    simpa only [inv_inv,←hx] using hh
  · have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hcontained
    rw [Subgroup.map_sup,←Z_act,←Z_act,hcancel,←hact,hcancel,
      ←chart (beta Rg) (base_adjacent Rg),hgβ] at hh
    exact hh
  · apply le_bot_iff.mp
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hcontained
    rw [Subgroup.map_sup,←Z_act,←Z_act,hcancel,←hact,hcancel,
      ←chart (beta Rg) (base_adjacent Rg),hgβ] at hh
    exact (commutator_mono (commutator_mono le_rfl hh) le_rfl).trans_eq
      (remaining_edge_full_seed_quadratic h e hz hk u (Or.inr hR) rfl hat₁)
  · let y := g⁻¹*y₀*g
    have hy : y ∈ stabilizer Rg (alpha Rg) :=
      (stabilizer Rg (alpha Rg)).mul_mem
        ((stabilizer Rg (alpha Rg)).mul_mem
          ((stabilizer Rg (alpha Rg)).inv_mem hg) hy₀) hg
    have hyt : act Rg y (p.walk.getVert 1) = act Rg g t₀ := by
      rw [←hgβ]
      dsimp only [y]
      rw [←act_mul]
      have he : g*(g⁻¹*y₀*g)=y₀*g := by group
      rw [he,act_mul,hyt₀]
    refine ⟨y,hy,hyt,?_⟩
    intro J₀ hQJ hJR hi
    let Jb := J₀.map (MulAut.conj g).toMonoidHom
    have hQb : Q Rg (alpha Rg) ≤ Jb := by
      have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hQJ
      rw [←show g⁻¹⁻¹=g from inv_inv g,←Q_act,hgia] at hh
      simpa only [inv_inv] using hh
    have hJb : Jb ≤ Q Rg (beta Rg) := by
      have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hJR
      rw [←show g⁻¹⁻¹=g from inv_inv g,←Q_act,hgib] at hh
      simpa only [inv_inv] using hh
    have hib : Jb.relIndex (Q Rg (beta Rg)) = 2 := by
      rw [←hgib,Q_act,inv_inv]
      exact (relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        J₀ (Q Rg (p.walk.getVert 1)) (MulAut.conj g).injective).trans hi
    have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom)
      (hopposite Jb hQb hJb hib)
    rw [Subgroup.map_sup,Subgroup.map_sup,←Z_act,hcancel,hstab] at hh
    have hyJ : (Jb.map (MulAut.conj y₀⁻¹).toMonoidHom).map
        (MulAut.conj g⁻¹).toMonoidHom = J₀.map (MulAut.conj y⁻¹).toMonoidHom := by
      dsimp only [Jb]
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro v
      change g⁻¹*(y₀⁻¹*(g*v*g⁻¹)*y₀⁻¹⁻¹)*g⁻¹⁻¹ = y⁻¹*v*y⁻¹⁻¹
      dsimp only [y]
      group
    have hxJ (B : Subgroup (FreeAmalgam Rg)) :
        (B.map (MulAut.conj x₀⁻¹).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom =
        (B.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro v
      change g⁻¹*(x₀⁻¹*v*x₀⁻¹⁻¹)*g⁻¹⁻¹ = x⁻¹*(g⁻¹*v*g⁻¹⁻¹)*x⁻¹⁻¹
      rw [hx]
      group
    rwa [hxJ,hyJ] at hh

include h e hz hk in
/-- Paired Borel movers with the same opposite seed, normalized on the actual
first edge of the critical path. All fixed-subgroup comparisons use full seeds. -/
theorem borel_small_critical_seed_selectors (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ K,
      let x := (embedM Rg r)⁻¹
      let J := edgeOffenderJoin (alpha Rg) t
      let J' := edgeOffenderJoin (alpha Rg) (act Rg x t)
      let b := p.walk.getVert 1
      (J ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        J ⊔ J' = stabilizer Rg (alpha Rg) ∧
        Q Rg b ⊔ J = stabilizer Rg (alpha Rg) ∧
        Q Rg b ⊔ J' = stabilizer Rg (alpha Rg) ∧
        Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
        Q Rg (act Rg x t) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
        Z Rg b ⊓ centralizer (J : Set (FreeAmalgam Rg)) ≤
          centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
        Z Rg b ⊓ centralizer (J' : Set (FreeAmalgam Rg)) ≤
          centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
        x ∈ normalizer (edgeOffenderJoin (alpha Rg) b : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) b ∧
        ⁅⁅Z Rg (alpha Rg),Z Rg z ⊔ Z Rg (act Rg x z)⁆,
          edgeOffenderJoin (alpha Rg) b⁆ = ⊥ := by
  obtain ⟨t,ht,r,hr,hgen,hpair,hfirst,hsecond,hBfirst,hBsecond,
    hfix,hfix',hnorm,hcontained,hquad,_⟩ :=
    borel_small_critical_seed_selectors_with_opposite h e hz hk u hR p hsmall
  exact ⟨t,ht,r,hr,hgen,hpair,hfirst,hsecond,hBfirst,hBsecond,
    hfix,hfix',hnorm,hcontained,hquad⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
