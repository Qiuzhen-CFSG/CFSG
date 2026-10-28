module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SixPathBinaryReflection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CriticalRadiusThree
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneTreeSource
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathRootCover

/-!
# The critical-pair source of the binary six-path correction

The original noncommuting critical pair at b=2 forces its middle center
subgroup to fix the whole radius-three ball. The literal universal-to-reduced
coset covering lifts this fixation for every element fixing the marked
endpoint. The covering itself is valid under F.1.11; no b=1 path profile is
used.

For a binary six-path root element x, the correction word (x t_i)^3 already
fixes the endpoint. Its original middle-center membership therefore discharges
the radius-three premise of the completed dihedral reflection correction.
The conclusion retains the exact corrected reflection, the entire original
root, its trivial generated two-core, and the full-Borel twist separation.

The final consumer accepts the D12/D24 product-order alternatives. The
original center image makes the cube have square one, and injectivity on the
endpoint stabilizer excludes product order twelve before applying the
reflection correction.

The source of the D12/D24 alternatives, placement of the central word in Z_i,
seven-path profile and equality of the replacement path root remain separate
source obligations. This theorem does not replace an r=6 profile by an r=4
profile or claim the final apartment exchange.
Source: DGS, Groups and Graphs (1985), (10.6), (14.17),
printed pp.157--158 and 222--223.
-/

public section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original critical middle center supplies radius-three fixation on the
literal universal source tree. -/
theorem source_bTwo_middle_radius_three
    (h : HypothesisF11 L S) (i : Bool)
    {v w : RankTwo.Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v,Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 2)
    (hvm : (RankTwo.graph (reducedFamily L S)).Adj v (RankTwo.base (reducedFamily L S) i))
    (hmw : (RankTwo.graph (reducedFamily L S)).Adj (RankTwo.base (reducedFamily L S) i) w)
    (z : (reducedAmalgam L S).Universal)
    (hzfix : z • base (Universal.cosetFamily (reducedAmalgam L S)) i =
      base (Universal.cosetFamily (reducedAmalgam L S)) i)
    (hz : bOne_tree_map h z ∈ Z (reducedFamily L S) (RankTwo.base (reducedFamily L S) i)) :
    z ∈ graphBallFixer (sourceGraph (reducedAmalgam L S))
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) 3 := by
  have hf := reduced_bTwo_middle_radius_three h hc hne hb hvm hmw hz
  have hf' : bOne_tree_map h z ∈ RankTwo.ballKernel (reducedFamily L S)
      ((bOne_tree_cover h).vertex (base (Universal.cosetFamily (reducedAmalgam L S)) i)) 3 := by
    rw [(bOne_tree_cover h).vertex_base]
    intro u hu
    exact (mem_graphBallFixer _ _ 3 _).mp hf u hu
  have hu := (bOne_tree_cover h).ballKernel_lift
    (base (Universal.cosetFamily (reducedAmalgam L S)) i) 3 z hzfix hf'
  rw [mem_graphBallFixer]
  exact fun u hu' => hu u hu'

/-- The exact source center image of the cube excludes product order twelve.
Injectivity is used only on the marked endpoint stabilizer. -/
theorem source_order_six_of_central_cube
    (h : HypothesisF11 L S) (i : Bool) (y : (reducedAmalgam L S).Universal)
    (hy : y • base (Universal.cosetFamily (reducedAmalgam L S)) i =
      base (Universal.cosetFamily (reducedAmalgam L S)) i)
    (hz : bOne_tree_map h (y^3) ∈ Z (reducedFamily L S) (RankTwo.base (reducedFamily L S) i))
    (ho : orderOf y=6 ∨ orderOf y=12) : orderOf y=6 := by
  have him : (bOne_tree_map h (y^3))^2=1 :=
    ((mem_omegaCenterIn_iff _ _).mp
      ((source_Z_Q_U (reduced_triple h) (RankTwo.base (reducedFamily L S) i)).1 hz)).2.2
  have hpim : bOne_tree_map h (y^6)=1 := by
    simpa only [map_pow,←pow_mul] using him
  have hp : y^6=1 := by
    let H := RankTwo.stabilizer (Universal.cosetFamily (reducedAmalgam L S))
      (base (Universal.cosetFamily (reducedAmalgam L S)) i)
    have hyp : y^6∈H := H.pow_mem hy 6
    have he := (bOne_tree_cover h).stabilizerHom_bijective
      (base (Universal.cosetFamily (reducedAmalgam L S)) i)
    have heq := he.1 (a₁ := (⟨y^6,hyp⟩ : H)) (a₂ := 1) (Subtype.ext (by
      change bOne_tree_map h (y^6)=bOne_tree_map h 1
      simpa only [map_one] using hpim))
    exact congrArg Subtype.val heq
  rcases ho with ho | ho
  · exact ho
  · have hd := orderOf_dvd_of_pow_eq_one hp
    norm_num [ho] at hd

variable (c : CompatibleCartans L (reducedSylow L S))
variable (t : Bool → (reducedAmalgam L S).Universal)
variable (htfix : ∀ j, t j • base (Universal.cosetFamily (reducedAmalgam L S)) j =
  base (Universal.cosetFamily (reducedAmalgam L S)) j)
variable (htmove : ∀ j, t j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j) ≠
  base (Universal.cosetFamily (reducedAmalgam L S)) (!j))
variable (htsq : ∀ j, t j*t j=1)
variable (htnorm : ∀ j, t j∈normalizer (cartan c : Set (reducedAmalgam L S).Universal))


include htfix htmove htsq htnorm in
/-- Apply the binary six-path correction with its ball-fixation premise proved
from the original critical pair and the central word's actual source image. -/
theorem source_six_binary_reflection_change_of_critical_center
    (h : HypothesisF11 L S) (i : Bool) (hK : cartan c=⊥)
    (hcard : Nat.card (pathRoot (X := (reducedAmalgam L S).Universal)
      (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk)=2)
    (x : (reducedAmalgam L S).Universal)
    (hx : x∈pathRoot (X := (reducedAmalgam L S).Universal)
      (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk)
    (hproduct : orderOf (x*t i)=6)
    {v w : RankTwo.Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v,Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 2)
    (hvm : (RankTwo.graph (reducedFamily L S)).Adj v (RankTwo.base (reducedFamily L S) i))
    (hmw : (RankTwo.graph (reducedFamily L S)).Adj (RankTwo.base (reducedFamily L S) i) w)
    (hz : bOne_tree_map h ((x*t i)^3) ∈
      Z (reducedFamily L S) (RankTwo.base (reducedFamily L S) i))
    (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S)) 7)
    (hthick : ∀ j, ∃ v, (sourceGraph (reducedAmalgam L S)).Adj
      (base (Universal.cosetFamily (reducedAmalgam L S)) j) v ∧
      v≠base (Universal.cosetFamily (reducedAmalgam L S)) (!j) ∧
      v≠t j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j))
    (hodd : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
      p.IsPath → p.length=7 →
        Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p))) :
    ∃ (t' : Bool → (reducedAmalgam L S).Universal)
      (htfix' : ∀ j, t' j • base (Universal.cosetFamily (reducedAmalgam L S)) j =
        base (Universal.cosetFamily (reducedAmalgam L S)) j)
      (htmove' : ∀ j, t' j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j) ≠
        base (Universal.cosetFamily (reducedAmalgam L S)) (!j))
      (_htsq' : ∀ j, t' j*t' j=1)
      (htnorm' : ∀ j, t' j∈normalizer (cartan c : Set (reducedAmalgam L S).Universal)),
      t' i=(x*t i)^3*t i ∧ t' (!i)=t (!i) ∧ orderOf (x*t' i)=3 ∧
      Nonempty ((zpowers x ⊔ zpowers (t' i) : Subgroup (reducedAmalgam L S).Universal) ≃*
        DihedralGroup 3) ∧
      centerIn (zpowers x ⊔ zpowers (t' i))=⊥ ∧
      pCore 2 (pathRoot (X := (reducedAmalgam L S).Universal)
        (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk ⊔
          zpowers (t' i) : Subgroup (reducedAmalgam L S).Universal)=⊥ ∧
      (∀ z∈originalMiddle (reducedAmalgam L S),
        z • (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk.reverse.getVert 2 ≠
          (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk.reverse.getVert 2 →
        (pathRoot (X := (reducedAmalgam L S).Universal)
          (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk).map
            (MulAut.conj z).toMonoidHom ≠
          pathRoot (X := (reducedAmalgam L S).Universal)
            (reflectionPath c t' htfix' htmove' htnorm' 6 (by decide) i).walk) := by
  have hxfix := (pathRoot_fixes
    (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk hx).1
  have htmem : t i ∈ MulAction.stabilizer (reducedAmalgam L S).Universal
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) := htfix i
  have hwordfix := (MulAction.stabilizer (reducedAmalgam L S).Universal
      (base (Universal.cosetFamily (reducedAmalgam L S)) i)).pow_mem
    (mul_mem hxfix htmem) 3
  have hball := source_bTwo_middle_radius_three h i hc hne hb hvm hmw
    ((x*t i)^3) hwordfix hz
  exact source_six_binary_dihedral_reflection_change c t htfix htmove htsq htnorm
    h i hK hcard x hx hproduct hball htrans hthick hodd

include htfix htmove htsq htnorm in
/-- The literal D12/D24 product-order alternatives feed the binary correction:
the cube's original center placement excludes D24 and proves ball fixation. -/
theorem source_six_binary_reflection_change_of_order_alternatives
    (h : HypothesisF11 L S) (i : Bool) (hK : cartan c=⊥)
    (hcard : Nat.card (pathRoot (X := (reducedAmalgam L S).Universal)
      (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk)=2)
    (x : (reducedAmalgam L S).Universal)
    (hx : x∈pathRoot (X := (reducedAmalgam L S).Universal)
      (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk)
    (hproduct : orderOf (x*t i)=6 ∨ orderOf (x*t i)=12)
    {v w : RankTwo.Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v,Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 2)
    (hvm : (RankTwo.graph (reducedFamily L S)).Adj v (RankTwo.base (reducedFamily L S) i))
    (hmw : (RankTwo.graph (reducedFamily L S)).Adj (RankTwo.base (reducedFamily L S) i) w)
    (hz : bOne_tree_map h ((x*t i)^3) ∈
      Z (reducedFamily L S) (RankTwo.base (reducedFamily L S) i))
    (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S)) 7)
    (hthick : ∀ j, ∃ v, (sourceGraph (reducedAmalgam L S)).Adj
      (base (Universal.cosetFamily (reducedAmalgam L S)) j) v ∧
      v≠base (Universal.cosetFamily (reducedAmalgam L S)) (!j) ∧
      v≠t j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j))
    (hodd : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
      p.IsPath → p.length=7 →
        Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p))) :
    ∃ (t' : Bool → (reducedAmalgam L S).Universal)
      (htfix' : ∀ j, t' j • base (Universal.cosetFamily (reducedAmalgam L S)) j =
        base (Universal.cosetFamily (reducedAmalgam L S)) j)
      (htmove' : ∀ j, t' j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j) ≠
        base (Universal.cosetFamily (reducedAmalgam L S)) (!j))
      (_htsq' : ∀ j, t' j*t' j=1)
      (htnorm' : ∀ j, t' j∈normalizer (cartan c : Set (reducedAmalgam L S).Universal)),
      t' i=(x*t i)^3*t i ∧ t' (!i)=t (!i) ∧ orderOf (x*t' i)=3 ∧
      Nonempty ((zpowers x ⊔ zpowers (t' i) : Subgroup (reducedAmalgam L S).Universal) ≃*
        DihedralGroup 3) ∧
      centerIn (zpowers x ⊔ zpowers (t' i))=⊥ ∧
      pCore 2 (pathRoot (X := (reducedAmalgam L S).Universal)
        (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk ⊔
          zpowers (t' i) : Subgroup (reducedAmalgam L S).Universal)=⊥ ∧
      (∀ z∈originalMiddle (reducedAmalgam L S),
        z • (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk.reverse.getVert 2 ≠
          (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk.reverse.getVert 2 →
        (pathRoot (X := (reducedAmalgam L S).Universal)
          (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk).map
            (MulAut.conj z).toMonoidHom ≠
          pathRoot (X := (reducedAmalgam L S).Universal)
            (reflectionPath c t' htfix' htmove' htnorm' 6 (by decide) i).walk) := by
  have hxfix := (pathRoot_fixes
    (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk hx).1
  have htmem : t i ∈ MulAction.stabilizer (reducedAmalgam L S).Universal
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) := htfix i
  have horder := source_order_six_of_central_cube h i (x*t i)
    (mul_mem hxfix htmem) hz hproduct
  exact source_six_binary_reflection_change_of_critical_center c t htfix htmove htsq htnorm
    h i hK hcard x hx horder hc hne hb hvm hmw hz htrans hthick hodd


end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
