module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.LineGeometry
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePairTransport

/-!
# Native reductions for the all-row-two pure-first branch

Excluding every ambient conjugate of the native row-seven pair forces every
independent ordered pair to be census row two. Equivalently, every such pair
has displacement-product rank sixteen in the actual native module. If the
marked involution belongs to the group, the whole group lies in the kernel of
the certified first-centralizer quotient. Conjugation gives simultaneous
8192-word coordinates and exact transport of the whole normalizer.

An actual row-two four-subgroup also puts the whole group and its full
centralizer into one conjugate of max4, using the certified plane centralizer.
This does not make the selected plane invariant. The common-eight assertion
and the whole-normalizer conclusion at maximal-two-local level remain to be
proved; neither is a premise or conclusion of this reduction.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Table 1,
Corollary 1.2.2(a), and Section 2.1, printed pp.487--489. The proof uses the
existing native census, quotient-kernel coordinates, and max4 certificates;
it introduces no new exhaustive computation or abstract family identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo
open ElementaryNormalizerCover ElementaryNormalizerCover.PureTwoA.NativePair
open Cardinality.LocalInvolutionCensus Cardinality.LocalInvolutionCensus.Coordinates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
attribute [local irreducible] modelGroup matrixA matrixB

private theorem map_conj_mul (A : Subgroup Model) (g k : Model) :
    (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*k)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem undo_conj (A : Subgroup Model) (g : Model) :
    (A.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A := by
  rw [map_conj_mul,mul_inv_cancel]
  have he : (MulAut.conj (1 : Model)).toMonoidHom = MonoidHom.id Model := by ext x; simp
  rw [he,map_id]

/-- Excluding the literal native pair excludes every conjugate of census row seven. -/
theorem no_row_seven (X : Subgroup Model)
    (hno : ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X)
    (g : Model) : ¬ (firstFourGroup 7).map (MulAut.conj g).toMonoidHom ≤ X := by
  intro hg
  obtain ⟨k,hk,_,_⟩ := row_seven_geometry
  apply hno
  refine ⟨g*k⁻¹, ?_⟩
  rw [hk,map_conj_mul]
  simpa only [inv_mul_cancel_right] using hg

/-- The exclusion is preserved when the whole subgroup is conjugated. -/
theorem no_native_pair_map (X : Subgroup Model)
    (hno : ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X)
    (g : Model) :
    ¬ ∃ k : Model, nativePair.map (MulAut.conj k).toMonoidHom ≤
      X.map (MulAut.conj g).toMonoidHom := by
  rintro ⟨k,hk⟩
  have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hk
  rw [map_conj_mul] at hh
  have hu : (X.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = X := by simpa using undo_conj X g⁻¹
  rw [hu] at hh
  exact hno ⟨g⁻¹*k,hh⟩

/-- Every ordered independent pair has row two, with one ambient conjugator. -/
theorem pair_coverage (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X)
    (x y : Model) (hx : x ∈ X) (hy : y ∈ X)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) :
    ∃ g : Model, (MulAut.conj g) a = x ∧
      (MulAut.conj g) (eH (representative 2)) = y := by
  have hc : Commute x y := congrArg Subtype.val (mul_comm (⟨x,hx⟩ : X) ⟨y,hy⟩)
  have hprod : x*y ≠ 1 := by
    intro he
    have hy2 : y*y = 1 := by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hy
    exact hxy (mul_right_cancel (he.trans hy2.symm))
  obtain ⟨i,g,hi,hg,hk⟩ := pure_first_pair_coverage x y hc
    (hpure x hx hx1) (hpure y hy hy1) (hpure _ (X.mul_mem hx hy) hprod)
  rcases hi with rfl | rfl
  · exact ⟨g,hg,hk⟩
  · exfalso
    apply no_row_seven X hno g
    rw [firstFourGroup,MonoidHom.map_closure,Set.image_pair]
    apply (closure_le _).mpr
    rintro v (rfl | rfl)
    · exact hg ▸ hx
    · exact hk ▸ hy

/-- Row-two exclusion gives the literal displacement rank on every independent
ordered pair in X. This retains the actual 112-dimensional native action. -/
theorem pair_rank (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X)
    (x y : Model) (hx : x ∈ X) (hy : y ∈ X)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) : pairRank x y = 16 := by
  obtain ⟨g,hg,hk⟩ := pair_coverage X hpure hno x y hx hy hx1 hy1 hxy
  rw [← hg,← hk,pairRank_conj,row_two_pairRank]

/-- A rank-sixteen test on all independent pairs is equivalent to the literal
native-pair exclusion. In particular a finite check must control all pairs,
not only the pairs in one chosen basis. -/
theorem no_native_pair_iff_pair_rank (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x) :
    (¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X) ↔
      ∀ x ∈ X, ∀ y ∈ X, x ≠ 1 → y ≠ 1 → x ≠ y → pairRank x y = 16 := by
  constructor
  · intro hn x hx y hy hx1 hy1 hxy
    exact pair_rank X hpure hn x y hx hy hx1 hy1 hxy
  · intro hr
    rintro ⟨g,hg⟩
    let u : Model := LinearFive.kernelValue 818
    let v : Model := LinearFive.kernelValue 1449
    have hfirst_ne : ∀ w : Model, IsConj a w → w ≠ 1 := by
      intro w hw he
      have ha : a = 1 := isConj_one_left.mp (he ▸ hw)
      have ho := orderOf_a
      simp [ha] at ho
    have hu : u ≠ 1 := hfirst_ne u first_is_first
    have hv : v ≠ 1 := hfirst_ne v second_is_first
    have huv : u ≠ v := by
      intro he
      have hh := LinearFive.kernelValue_injective (m := 818) (n := 1449)
        (by decide) (by decide) (Subtype.ext he)
      omega
    have huX : (MulAut.conj g) u ∈ X :=
      hg (mem_map_of_mem _ (subset_closure (by simp [u])))
    have hvX : (MulAut.conj g) v ∈ X :=
      hg (mem_map_of_mem _ (subset_closure (by simp [v])))
    have hh := hr _ huX _ hvX
      (fun he => hu ((MulAut.conj g).injective (he.trans (map_one _).symm)))
      (fun he => hv ((MulAut.conj g).injective (he.trans (map_one _).symm)))
      (fun he => huv ((MulAut.conj g).injective he))
    rw [pairRank_conj] at hh
    have hn : pairRank u v = 20 := native_pairRank
    omega

/-- Every four-subgroup is a conjugate of the certified plane. This does not
assert that a plane is invariant under the normalizer of the whole subgroup. -/
theorem four_group_plane (X Y : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X)
    (hYX : Y ≤ X) (hcard : Nat.card Y = 4) :
    ∃ g : Model, Y = max4Plane.map (MulAut.conj g).toMonoidHom := by
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_le hYX
  obtain ⟨i,g,hi,hY,_,_⟩ := pure_first_four_group_geometry Y hcard
    (fun y hy => hpure y (hYX hy))
  rcases hi with rfl | rfl
  · obtain ⟨k,hk⟩ := first_four_two_conjugate_plane
    refine ⟨g*k⁻¹,?_⟩
    rw [← hk,map_conj_mul]
    simpa only [inv_mul_cancel_right] using hY
  · exact (no_row_seven X hno g (hY ▸ hYX)).elim

/-- The literal kernel of the certified first-centralizer quotient, embedded
in the ambient matrix group. -/
@[expose] def firstKernel : Subgroup Model := q.ker.map eH

private theorem q_lift_zero : q (lift 0) = 1 := by
  change q (sourceSubgroupEquivLocal 1) = 1
  rw [map_one,map_one]

private theorem q_zH : q zH = 1 := by
  apply Subtype.ext
  exact localQuotientMap_zH

/-- With the distinguished involution in X, every local lift has trivial
image in the actual quotient, rather than merely in its outer character. -/
theorem marked_lift_kernel (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X)
    (ha : a ∈ X) (u : H) (hu : eH u ∈ X) : q u = 1 := by
  by_cases hu1 : u = 1
  · rw [hu1,map_one]
  by_cases huz : u = zH
  · rw [huz,q_zH]
  have hne : eH u ≠ 1 := by
    intro hh
    exact hu1 (eH_injective (hh.trans eH.map_one.symm))
  have hup : eH (u*zH) ≠ 1 := by
    intro hh
    have he : eH u * a = 1 := by simpa only [map_mul,eH_zH] using hh
    have haa : a*a = 1 := by simpa only [pow_two] using a_pow_two
    exact huz (eH_injective (mul_right_cancel (he.trans haa.symm)))
  have huc : u ∈ aa := ⟨hpure _ hu hne,
    hpure _ (by simpa only [map_mul,eH_zH] using X.mul_mem hu ha) hup⟩
  rcases aa_coverage Cardinality.Thompson.max2_card.le huc with hc | hc
  · have hh := q.map_isConj hc
    rw [q_representative] at hh
    change IsConj (q (lift 0)) (q u) at hh
    rw [q_lift_zero] at hh
    exact isConj_one_right.mp hh
  · obtain ⟨k,hk⟩ := isConj_iff.mp hc
    exfalso
    apply no_row_seven X hno (eH k)
    rw [firstFourGroup,MonoidHom.map_closure,Set.image_pair]
    apply (closure_le _).mpr
    rintro v (rfl | rfl)
    · change eH k * a * (eH k)⁻¹ ∈ X
      have hc : eH k * a = a * eH k := (eH_commute_z k).eq
      rw [hc,mul_inv_cancel_right]
      exact ha
    · have he : (MulAut.conj (eH k)) (eH (representative 7)) = eH u := by
        simpa only [map_mul,map_inv,MulAut.conj_apply] using congrArg eH hk
      change (MulAut.conj (eH k)) (eH (representative 7)) ∈ X
      rw [he]
      exact hu

/-- The whole subgroup lies in the actual first-centralizer kernel. -/
theorem marked_le_kernel (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X)
    (ha : a ∈ X) : X ≤ firstKernel := by
  intro x hx
  have hc : x*a = a*x := congrArg Subtype.val (mul_comm (⟨x,hx⟩ : X) ⟨a,ha⟩)
  let v : InvolutionCentralizers.First.centralizer :=
    ⟨x,mem_centralizer_singleton_iff.mpr hc⟩
  obtain ⟨u,hu⟩ := Cardinality.Thompson.max2EquivCentralizer.surjective v
  have he : eH u = x := by
    simpa only [Cardinality.Thompson.max2EquivCentralizer_coe] using congrArg Subtype.val hu
  exact ⟨u,marked_lift_kernel X hpure hno ha u (he ▸ hx),he⟩

/-- Each involution of X supplies a kernel containing the whole X, with any
chosen ambient conjugator taking the marked involution to that element. -/
theorem le_kernel_of_conjugator (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X)
    (g : Model) (ha : (MulAut.conj g) a ∈ X) :
    X ≤ firstKernel.map (MulAut.conj g).toMonoidHom := by
  let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hp : ∀ y ∈ Y, y ≠ 1 → IsConj a y := by
    rintro y ⟨z,hz,rfl⟩ hy
    apply (hpure z hz (fun he => hy (by simp [he]))).trans
    exact isConj_iff.mpr ⟨g⁻¹,rfl⟩
  have haY : a ∈ Y := by
    refine ⟨(MulAut.conj g) a,ha,?_⟩
    simp [mul_assoc]
  have hY := marked_le_kernel Y hp (no_native_pair_map X hno g⁻¹) haY
  have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hY
  rwa [undo_conj] at hm

/-- Exhaustive coordinates in the actual kernel, using the pre-existing
8192-word theorem rather than an unchecked matrix lookup. -/
theorem mem_firstKernel_iff (x : Model) :
    x ∈ firstKernel ↔ ∃ i : Fin 8192, eH (localKernelProduct i) = x := by
  constructor
  · rintro ⟨u,hu,rfl⟩
    have hq : localQuotientMap u = localQuotientMap 1 := by
      have he := congrArg (fun z : Q => z.val) hu
      simpa only [coe_q,map_one,Subgroup.coe_one] using he
    obtain ⟨i,hi⟩ := local_fiber Cardinality.Thompson.max2_card.le u 1 hq
    exact ⟨i,by rw [hi,mul_one]⟩
  · rintro ⟨i,rfl⟩
    exact mem_map_of_mem eH (q_localKernelProduct i)

/-- An actual ambient conjugator places the entire nontrivial all-row-two
group in the certified first-centralizer kernel. -/
theorem kernel_placement (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hX : X ≠ ⊥) (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X) :
    ∃ g : Model, X ≤ firstKernel.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨x,hx⟩ := ne_bot_iff_exists_ne_one.mp hX
  have hx1 : (x : Model) ≠ 1 := fun he => hx (Subtype.ext he)
  obtain ⟨g,hg⟩ := isConj_iff.mp (hpure x x.property hx1)
  exact ⟨g,le_kernel_of_conjugator X hpure hno g (show (MulAut.conj g) a ∈ X by change g*a*g⁻¹ ∈ X; rw [hg]; exact x.property)⟩

private theorem independent_pair (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hcard : 4 < Nat.card X) :
    ∃ x ∈ X, ∃ y ∈ X, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  have hX : X ≠ ⊥ := by intro he; simp [he] at hcard
  obtain ⟨x,hx⟩ := ne_bot_iff_exists_ne_one.mp hX
  have hx1 : (x : Model) ≠ 1 := fun he => hx (Subtype.ext he)
  have hx2 : orderOf (x : Model) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ x.property) hx1
  have hn : ¬ X ≤ zpowers (x : Model) := by
    intro hh
    have h := Nat.le_of_dvd Nat.card_pos (card_dvd_of_le hh)
    rw [Nat.card_zpowers,hx2] at h
    omega
  obtain ⟨y,hy,hyn⟩ := SetLike.not_le_iff_exists.mp hn
  exact ⟨x,x.property,y,hy,hx1,
    (fun he => hyn (he ▸ one_mem _)),
    (fun he => hyn (he ▸ mem_zpowers (x : Model)))⟩

/-- Select a row-two four-subgroup inside the entire original group. -/
theorem row_two_marking (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hcard : 4 < Nat.card X) (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X) :
    ∃ g : Model, (firstFourGroup 2).map (MulAut.conj g).toMonoidHom ≤ X := by
  obtain ⟨x,hx,y,hy,hx1,hy1,hxy⟩ := independent_pair X hcard
  obtain ⟨g,hg,hk⟩ := pair_coverage X hpure hno x y hx hy hx1 hy1 hxy
  refine ⟨g,?_⟩
  rw [firstFourGroup,MonoidHom.map_closure,Set.image_pair]
  apply (closure_le _).mpr
  rintro v (rfl | rfl)
  · exact hg ▸ hx
  · exact hk ▸ hy

/-- Simultaneous native reduction of the whole subgroup: a row-two marking,
8192-word coordinates for every element, and transport of the full normalizer.
No invariance of the selected four-group is assumed or asserted. -/
theorem marked_kernel_reduction (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hcard : 4 < Nat.card X) (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X) :
    ∃ g : Model,
      (firstFourGroup 2).map (MulAut.conj g).toMonoidHom ≤ X ∧
      X ≤ firstKernel.map (MulAut.conj g).toMonoidHom ∧
      (∀ x ∈ X, ∃ i : Fin 8192,
        (MulAut.conj g⁻¹) x = eH (localKernelProduct i)) ∧
      normalizer (X.map (MulAut.conj g⁻¹).toMonoidHom : Set Model) =
        (normalizer (X : Set Model)).map (MulAut.conj g⁻¹).toMonoidHom := by
  obtain ⟨g,hg⟩ := row_two_marking X hcard hpure hno
  have ha : (MulAut.conj g) a ∈ X :=
    hg (mem_map_of_mem _ (subset_closure (by simp)))
  have hK := le_kernel_of_conjugator X hpure hno g ha
  refine ⟨g,hg,hK,?_,(map_equiv_normalizer_eq X (MulAut.conj g⁻¹)).symm⟩
  intro x hx
  obtain ⟨u,hu,he⟩ := hK hx
  obtain ⟨i,hi⟩ := (mem_firstKernel_iff u).mp hu
  refine ⟨i,?_⟩
  rw [← he]
  simpa [mul_assoc] using hi.symm

/-- One ambient conjugator places the whole group and its full centralizer in
max4, and places an actual four-subgroup on the certified plane. Containment
of the whole normalizer remains the additional line-geometry obligation. -/
theorem max4_group_placement (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hcard : 4 < Nat.card X) (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X) :
    ∃ g : Model, max4Plane.map (MulAut.conj g).toMonoidHom ≤ X ∧
      X ≤ SymmetricLinear.max4Subgroup.map (MulAut.conj g).toMonoidHom ∧
      centralizer (X : Set Model) ≤
        SymmetricLinear.max4Subgroup.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := row_two_marking X hcard hpure hno
  obtain ⟨k,hk⟩ := first_four_two_conjugate_plane
  have hplane : max4Plane.map (MulAut.conj (g*k⁻¹)).toMonoidHom ≤ X := by
    rw [← hk,map_conj_mul]
    simpa only [inv_mul_cancel_right] using hg
  have hC : centralizer (X : Set Model) ≤
      SymmetricLinear.max4Subgroup.map (MulAut.conj (g*k⁻¹)).toMonoidHom := by
    calc
      _ ≤ centralizer (max4Plane.map (MulAut.conj (g*k⁻¹)).toMonoidHom : Set Model) :=
        centralizer_le hplane
      _ = (centralizer (max4Plane : Set Model)).map
          (MulAut.conj (g*k⁻¹)).toMonoidHom :=
        (map_centralizer_equiv (max4Plane : Set Model) (MulAut.conj (g*k⁻¹))).symm
      _ ≤ _ := map_mono (max4Plane_centralizer_le_of_marking Max4EightCentralizer.marking)
  exact ⟨g*k⁻¹,hplane,X.le_centralizer.trans hC,hC⟩

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo
