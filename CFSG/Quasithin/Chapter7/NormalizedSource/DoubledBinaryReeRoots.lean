module
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.TailRelations.BaseIntervals.ShortExchanges
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.RootBlocks
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.UnipotentCenter
import all Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.MiddleElimination
import all Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.UnipotentCenter.TailIdentification
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.Replacement.Centralizers
public import Theory.GroupTheory.PerfectHalfOrderImage

/-!
# Small centralizers in the original positive Ree subgroup

An abelian image kills all six interior main root curves. The two middle
curves are linked by the Tits automorphism; its square is Frobenius, so a
nonbinary field parameter forces both images to vanish. Consequently an
index-at-most-two centralizer contains all six curves. The existing split
coordinate tests leave only the Y₃Y₅ plane. A nonzero X₈ parameter in the
centralizer eliminates Y₃, leaving the full Sylow center Y₅.

The `import all` dependencies deliberately reuse the internal middle and
tail coordinate tests in this extension of the same calculation, without
widening their public interfaces. No new matrix certificate is needed.
The companion placement module applies the result to the canonical inner
image in the original component Sylow of source 7.7.6.

Source: Aschbacher–Smith 7.7.6, printed p.706, refs/quasithin.pdf;
GLS3 Table 2.4 and §2.4.5(d) for the actual Ree commutator conventions.
-/

public noncomputable section
open Subgroup ReeF4 ReeF4.Parabolics
open ReeF4.NormalizedRootCentralizers.CenterExponent
open ReeF4.ElementaryTwoBound ReeF4.ElementaryTwoBound.RootCalculations
open ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open ReeF4.CentralCovers.TwoPrimary.TailRelations.BaseIntervals
open ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryReeRoots

private def mainU (m : ℕ) (i : Fin 8) (t : CoefficientField m) : unipotent m :=
  ⟨mainElement m i t, mainElement_mem_unipotent m i t⟩
private def centralU (m : ℕ) (i : Fin 8) (t : CoefficientField m) : unipotent m :=
  ⟨centralElement m i t, Y_le_unipotent m i (centralElement_mem_Y m i t)⟩

private theorem mapped_relation {J : Type*} [CommGroup J] (m : ℕ)
    (f : unipotent m →* J) (i j : Fin 8) (t u : CoefficientField m)
    (z : unipotent m)
    (h : (rootWord m i t)⁻¹ * (rootWord m j u)⁻¹ * rootWord m i t * rootWord m j u =
      toSplitGroup m z.val) : f z = 1 := by
  have he : (mainU m i t)⁻¹ * (mainU m j u)⁻¹ * mainU m i t * mainU m j u = z := by
    apply Subtype.ext
    apply toSplitGroup_injective m
    simpa only [map_mul,map_inv,mainU,coe_mul,coe_inv,mainElement_coe] using h
  rw [←he]
  simp only [map_mul,map_inv]
  rw [mul_right_comm _ _ (f (mainU m i t)),inv_mul_cancel,one_mul,inv_mul_cancel]

attribute [local irreducible] mainU centralU

private theorem interior_image {J : Type*} [CommGroup J] (m : ℕ) (hm : 1 ≤ m)
    (f : unipotent m →* J) : ∀ i : Fin 8, 1 ≤ i.val → i.val ≤ 6 →
      ∀ t, f (mainU m i t) = 1 := by
  let a (i : Fin 8) (t : CoefficientField m) := f (mainU m i t)
  let c (i : Fin 8) (t : CoefficientField m) := f (centralU m i t)
  have h1 (t) : a 1 t = 1 := by
    exact mapped_relation m f 0 2 t 1 (mainU m 1 t)
      (by simpa only [mul_one,mainU,centralU,mainElement_coe,centralElement_coe] using rootWord_commutator_0_2 m t 1)
  have h3 (t) : a 3 t = 1 := by
    exact mapped_relation m f 2 4 t 1 (mainU m 3 t)
      (by simpa only [mul_one,mainU,centralU,mainElement_coe,centralElement_coe] using rootWord_commutator_2_4 m t 1)
  have h5 (t) : a 5 t = 1 := by
    exact mapped_relation m f 4 6 t 1 (mainU m 5 t)
      (by simpa only [mul_one,mainU,centralU,mainElement_coe,centralElement_coe] using rootWord_commutator_4_6 m t 1)
  have hc2 (t) : c 2 t = 1 := by
    exact mapped_relation m f 1 4 t 1 (centralU m 2 t)
      (by simpa only [mul_one,mainU,centralU,mainElement_coe,centralElement_coe] using rootWord_commutator_1_4 m t 1)
  have hc4 (t) : c 4 t = 1 := by
    exact mapped_relation m f 2 5 t 1 (centralU m 4 t)
      (by simpa only [mul_one,mainU,centralU,mainElement_coe,centralElement_coe] using rootWord_commutator_2_5 m t 1)
  have h24 (t u) : a 2 (titsEnd m t * u) = a 4 (t * titsEnd m u) := by
    have hh := mapped_relation m f 0 6 t u
      ((mainU m 2 (titsEnd m t * u))⁻¹ *
        mainU m 3 ((t * titsEnd m t) * (u * titsEnd m u)) * mainU m 4 (t * titsEnd m u))
      (by simpa only [map_mul,map_inv,coe_mul,coe_inv,mainU,mainElement_coe]
        using rootWord_first_seventh_commutator m t u)
    simp only [map_mul,map_inv] at hh
    change (a 2 (titsEnd m t * u))⁻¹ * a 3 _ * a 4 _ = 1 at hh
    rw [h3,mul_one] at hh
    exact inv_mul_eq_one.mp hh
  have h2add (t u) : a 2 (t+u) = a 2 t * a 2 u := by
    have he : mainU m 2 t * mainU m 2 u =
        mainU m 2 (t+u) * centralU m 2 (titsEnd m t * u) := by
      apply Subtype.ext
      simpa only [mainU,centralU,coe_mul] using ReeF4.CentralCovers.TwoPrimary.main_mul m 2 (by decide) t u
    have hh := congrArg f he
    simp only [map_mul] at hh
    change a 2 t * a 2 u = a 2 (t+u) * c 2 _ at hh
    simpa only [hc2,mul_one] using hh.symm
  have h20 : a 2 0 = 1 := by
    have hz : mainU m 2 0 = 1 := by unfold mainU; exact Subtype.ext (mainElement_zero m 2)
    change f _ = 1
    rw [hz,map_one]
  have hmul (t u) : a 2 (t*u) = a 2 (t*u^2) := by
    obtain ⟨s,rfl⟩ := (Finite.surjective_of_injective (titsEnd m).injective) t
    have hleft := h24 s u
    have hright := h24 (s * titsEnd m u) 1
    simp only [map_one,map_mul,mul_one,titsEnd_twice] at hright
    exact hleft.trans hright.symm
  have hq : 2 < Nat.card (CoefficientField m) := by
    rw [field_card]
    exact (by norm_num : 2 < 2^3).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  let : Nontrivial (CoefficientField m)ˣ := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [Nat.card_units]; omega)
  obtain ⟨v,hv⟩ := exists_ne (1 : (CoefficientField m)ˣ)
  let u : CoefficientField m := v
  have hu : u + u^2 ≠ 0 := by
    intro hz
    have he : u * (u+1) = 0 := by
      calc
        _ = u + u^2 := by ring
        _ = 0 := hz
    have hu1 : u = 1 := by
      have hh := (mul_eq_zero.mp he).resolve_left (Units.ne_zero v)
      simpa only [CharTwo.neg_eq] using (eq_neg_of_add_eq_zero_left hh)
    exact hv (Units.ext hu1)
  have h2 (t) : a 2 t = 1 := by
    let b := t / (u+u^2)
    have hz : b*(u+u^2) = t := div_mul_cancel₀ t hu
    rw [←hz,mul_add,h2add,hmul b u,←h2add,CharTwo.add_self_eq_zero,h20]
  have h4 (t) : a 4 t = 1 := by
    have hh := h24 t 1
    simpa only [map_one,mul_one,h2] using hh.symm
  have h6 (t) : a 6 t = 1 := by
    have hh := mapped_relation m f 0 7 1 t
      (mainU m 1 ((1 ^ 2 * titsEnd m 1) * t) *
        (mainU m 2 ((1 * titsEnd m 1) * t))⁻¹ *
        mainU m 3 ((1 ^ 2 * titsEnd m 1 ^ 2) * (t * titsEnd m t)) *
        centralU m 4 ((1 ^ 3 * titsEnd m 1 ^ 2) * (t ^ 2 * titsEnd m t)) *
        mainU m 5 ((1 ^ 2 * titsEnd m 1) * (t * titsEnd m t)) * mainU m 6 (1*t))
      (by simpa only [map_mul,map_inv,coe_mul,coe_inv,mainU,centralU,
        mainElement_coe,centralElement_coe] using rootWord_first_eighth_commutator m 1 t)
    simp only [map_mul,map_inv] at hh
    change a 1 _ * (a 2 _)⁻¹ * a 3 _ * c 4 _ * a 5 _ * a 6 _ = 1 at hh
    simpa only [h1,h2,h3,h5,hc4,inv_one,one_mul] using hh
  intro i hi hi' t
  fin_cases i
  all_goals solve | exact h1 t | exact h2 t | exact h3 t | exact h4 t | exact h5 t | exact h6 t | norm_num at hi | norm_num at hi'

/-- All six interior Ree root curves belong to the derived positive subgroup. -/
theorem interior_root_mem_commutator (m : ℕ) (hm : 1 ≤ m)
    (i : Fin 8) (hi : 1 ≤ i.val) (hi' : i.val ≤ 6) (t : CoefficientField m) :
    mainElement m i t ∈ (_root_.commutator (unipotent m)).map (unipotent m).subtype := by
  refine ⟨mainU m i t,?_,by simp only [mainU,coe_subtype]⟩
  rw [←Abelianization.ker_of]
  exact interior_image m hm Abelianization.of i hi hi' t

private theorem interior_commute (m : ℕ) (hm : 1 ≤ m) (x : unipotent m)
    (hi : (centralizer ({x} : Set (unipotent m))).index ≤ 2)
    (i : Fin 8) (h1 : 1 ≤ i.val) (h6 : i.val ≤ 6) (t : CoefficientField m) :
    Commute (toSplitGroup m x.val) (rootWord m i t) := by
  have hd : mainU m i t ∈ _root_.commutator (unipotent m) := by
    rw [←Abelianization.ker_of]
    exact interior_image m hm Abelianization.of i h1 h6 t
  have hc := Theory.GroupTheory.PerfectHalfOrderImage.commutator_le_of_index_le_two
    (centralizer ({x} : Set (unipotent m))) hi hd
  have hh := (show Commute (mainU m i t) x from mem_centralizer_singleton_iff.mp hc).symm
  have hh' := (hh.map (unipotent m).subtype).map (toSplitGroup m)
  simpa only [mainU,coe_subtype,mainElement_coe] using hh'

private theorem root_plane_of_index_two (m : ℕ) (hm : 1 ≤ m) (x : unipotent m)
    (hi : (centralizer ({x} : Set (unipotent m))).index ≤ 2) :
    ∃ a b : CoefficientField m,
      x.val = centralElement m 4 a * centralElement m 2 b := by
  open ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination in
  obtain ⟨p,hp⟩ := exists_positiveWord m x.val x.property
  have hcomm (i : Fin 8) (h1 : 1 ≤ i.val) (h6 : i.val ≤ 6) (t) :
      Commute (positiveWord m p) (rootWord m i t) := by
    rw [←hp]
    exact interior_commute m hm x hi i h1 h6 t
  open ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination in
  have ho : OuterCoordinatesZero p := by
    let v := parameters m p
    have h (i : Fin 8) (h1 : 1 ≤ i.val) (h6 : i.val ≤ 6) :
        Commute (splitWord m v) (rootWord m i 1) := by
      rw [←positiveWord_split]
      exact hcomm i h1 h6 1
    obtain ⟨h0,h18⟩ := detect_fourth m v (h 3 (by decide) (by decide))
    have hm0 : p.main 0 = 0 := h0
    have hm2 : p.main 2 = 0 := h18
    have h1 : v 1 = 0 := by change halfFrobenius m (p.main 0) = 0; rw [hm0,map_zero]
    have h19 : v 19 = 0 := by change halfFrobenius m (p.main 2) = 0; rw [hm2,map_zero]
    have h22 := detect_second m v h0 h1 h18 h19 (h 1 (by decide) (by decide))
    have hp0 : p.pair 0 = 0 := h22
    have h23 : v 23 = 0 := by change halfFrobenius m (p.pair 0) = 0; rw [hp0,map_zero]
    obtain ⟨hp1,hc0⟩ := detect_seventh m v h0 h1 h18 h19 h22 h23
      (h 6 (by decide) (by decide))
    exact ⟨hp0,hp1,hm0,hm2,hc0⟩
  have hm3 := MiddleElimination.main_third_zero m p ho (hcomm 4 (by decide) (by decide) 1)
  have hm1 := MiddleElimination.main_fifth_zero m p ho hm3 (hcomm 2 (by decide) (by decide) 1)
  open ReeF4.EvenInvolutionGeometry.UnipotentCenter in
  have htail : p.pair 2 = 0 ∧ p.pair 3 = 0 ∧ p.central 2 = 0 := by
    have hc (i : Fin 8) (h1 : 1 ≤ i.val) (h6 : i.val ≤ 6) :
        Commute (tailSplitWord m (OuterElimination.parameters m p)) (rootWord m i 1) := by
      rw [←positiveWord_tail m p ho hm1 hm3]
      exact hcomm i h1 h6 1
    exact ⟨detect_pairsixth m _ (hc 2 (by decide) (by decide)),
      detect_pairfourth m _ (hc 6 (by decide) (by decide)),
      detect_centralseventh m _ (hc 1 (by decide) (by decide))⟩
  refine ⟨p.central 1,p.central 3,toSplitGroup_injective m ?_⟩
  rw [hp,map_mul,centralElement_coe,centralElement_coe]
  simp [positiveWord,positive_pair_indices,positive_quartet_indices,
    pairCount,quartetCount,
    List.ofFn_succ,Matrix.cons_val_zero,
    ho.pair_eighth,ho.pair_second,ho.main_first,ho.main_seventh,ho.central_first,
    hm1,hm3,htail.1,htail.2.1,htail.2.2,rootWord_zero,centralWord_zero,one_mul,mul_one]

private theorem index_comap_le {X Y : Type*} [Group X] [Group Y] [Finite Y]
    (C : Subgroup Y) (f : X →* Y) : (C.comap f).index ≤ C.index := by
  rw [C.index_comap]
  exact (relIndex_le_of_le_right (H := C) (le_top : f.range ≤ ⊤)
    (by simpa using C.index_ne_zero_of_finite)).trans_eq C.relIndex_top_right

/-- Centralizer index at most two forces centrality in the actual positive Ree group. -/
theorem ree_coordinate_central (m : ℕ) (hm : 1 ≤ m) (x : unipotent m)
    (hi : (centralizer ({x} : Set (unipotent m))).index ≤ 2) : x ∈ center (unipotent m) := by
  obtain ⟨a,b,hx⟩ := root_plane_of_index_two m hm x hi
  let f : Multiplicative (CoefficientField m) →* unipotent m :=
    (pairHom m 7 (by decide)).codRestrict _
      (fun t => mainElement_mem_unipotent m 7 t.toAdd)
  let C := (centralizer ({x} : Set (unipotent m))).comap f
  have hC : C.index ≤ 2 := (index_comap_le _ _).trans hi
  have hn : C ≠ ⊥ := by
    intro hh
    rw [hh,index_bot] at hC
    have hq : 2 < Nat.card (Multiplicative (CoefficientField m)) := by
      rw [Nat.card_congr Multiplicative.toAdd,field_card]
      exact (by norm_num : 2 < 2^3).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    omega
  obtain ⟨t,ht,htne⟩ := C.bot_or_exists_ne_one.resolve_left hn
  have ht0 : t.toAdd ≠ 0 := fun hh => htne (congrArg Multiplicative.ofAdd hh)
  have hcomm : Commute (mainElement m 7 t.toAdd) x.val := by
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp ht)
  have ha : Commute (centralElement m 4 a) (mainElement m 7 t.toAdd) := by
    apply toSplitGroup_injective m
    simpa only [map_mul,centralElement_coe,mainElement_coe] using
      (ReeF4.ReplacementCentralizerRoots.main_central_4 m 7 t.toAdd a).symm.eq
  have hb : Commute (centralElement m 2 b) (mainElement m 7 t.toAdd) := by
    have hh := ha.inv_left.mul_left (hx ▸ hcomm.symm)
    simpa only [inv_mul_cancel_left] using hh
  have he : centralElement m 4 (b*t.toAdd) = 1 := by
    have hh : centralElement m 2 b * mainElement m 7 t.toAdd =
        mainElement m 7 t.toAdd * centralElement m 2 b * centralElement m 4 (b*t.toAdd) := by
      apply toSplitGroup_injective m
      simpa only [map_mul,centralElement_coe,mainElement_coe] using
        ReeF4.ReplacementCentralizerRoots.central_eighth m b t.toAdd
    rw [hb.eq] at hh
    exact (mul_left_cancel ((mul_one _).trans hh)).symm
  have hb0 : b = 0 := by
    have hh : b*t.toAdd = 0 := ReeF4.ElementaryTwoBound.Replacement.CentralizerGeometry.centralElement_four_injective m
      (he.trans (centralElement_zero m 4).symm)
    exact (mul_eq_zero.mp hh).resolve_right ht0
  have hroot : x.val = ReeF4.EvenInvolutionGeometry.longRootElement m a := by
    rw [hx,hb0,centralElement_zero,mul_one]
    apply toSplitGroup_injective m
    rw [centralElement_coe,ReeF4.EvenInvolutionGeometry.longRootElement_coe]
  have hh : x.val ∈ ReeF4.EvenInvolutionGeometry.longRootGroup m :=
    (ReeF4.EvenInvolutionGeometry.mem_longRootGroup m _).mpr ⟨a,hroot.symm⟩
  rw [←ReeF4.EvenInvolutionGeometry.unipotent_center_eq_longRootGroup m hm] at hh
  obtain ⟨y,hy,he⟩ := hh
  exact (Subtype.ext he : y = x) ▸ hy
end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryReeRoots
