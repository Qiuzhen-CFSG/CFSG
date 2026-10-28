module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticHyperplanes
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.EndpointKernels
public import Theory.Representation.BinaryConjugationSection.DualHyperplanes
public import Theory.GroupTheory.PrimeIndexCentralizer

/-!
# Actual kernel radicals at the quintic critical pair

The full quotient D₁₀ or Sz(2) forces every nontrivial involution to move
at least two binary dimensions. Hence both index-two core intersections
move the entire opposite central point. Their mutual commutation then
identifies the centralizers of the hyperplanes, and a binary commutator row
computes the intersection of each critical module with the full opposite
radius-two kernel. That intersection has index four, and order eight or
sixteen. No faithfulness of the full radius-two kernel is assumed.

Source: Aschbacher--Smith F.9.7 and F.9.13--17, pp.321--324, applied to
the original quintic alternatives of14.2.21, p.988, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter13.Section08.SourceCompletion
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
variable {G : Type*} [Group G] [Finite G]

private theorem critical_denominator_eq
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (hUV : D.UH = D.VH) (i : h.CriticalEndpoint) (hb : 3 ≤ h.b) :
    commutatorPreimage D.UH (i.conjugate D.UH) (i.conjugate D.V₁) =
      D.UH ⊓ i.conjugate D.QH := by
  have hback : D.UH.conjBy i.representative⁻¹ ≤ D.H := by
    have hh := map_mono (f := (MulAut.conj i.representative⁻¹).toMonoidHom)
      (hUV ▸ i.reverse_le hb)
    change D.UH.conjBy i.representative⁻¹ ≤
      (D.H.conjBy i.representative).conjBy i.representative⁻¹ at hh
    rwa [conjBy_inv] at hh
  have he := congrArg (fun A : Subgroup G => A.map
      (MulAut.conj i.representative).toMonoidHom)
    (f9_commutatorPreimage_eq D h (D.UH.conjBy i.representative⁻¹) hback)
  rw [map_commutatorPreimage_equiv _ _ _ _
    (hback.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))),
    map_inf _ _ _ (MulAut.conj i.representative).injective] at he
  change commutatorPreimage ((D.UH.conjBy i.representative⁻¹).conjBy i.representative)
    (i.conjugate D.UH) (i.conjugate D.V₁) =
    (D.UH.conjBy i.representative⁻¹).conjBy i.representative ⊓ i.conjugate D.QH at he
  rwa [conjBy_inv'] at he

private theorem critical_denominator_moves_point
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH]
    (hm : Nonempty ((D.H ⧸ pCore 2 D.H) ≃* DihedralGroup 5) ∨
      Nonempty ((D.H ⧸ pCore 2 D.H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0))
    (hUV : D.UH = D.VH) (i : h.CriticalEndpoint) (hb : 3 ≤ h.b)
    (himage : Nat.card (((i.conjugate D.UH).subgroupOf D.H).map
      (QuotientGroup.mk' (pCore 2 D.H))) = 2)
    (hindex : (D.UH ⊓ i.conjugate D.QH).relIndex D.UH = 2) :
    ⁅D.UH ⊓ i.conjugate D.QH,i.conjugate D.UH⁆ = i.conjugate D.V₁ := by
  let A := D.UH ⊓ i.conjugate D.QH
  let W := i.conjugate D.UH
  let Zg := i.conjugate D.V₁
  have hWH : W ≤ D.H := by simpa only [W,hUV] using i.large_le hb
  have hnorm : D.UH ≤ normalizer (Zg : Set G) := by
    have hn := map_mono (f := (MulAut.conj i.representative).toMonoidHom)
      (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    rw [map_equiv_normalizer_eq] at hn
    exact (hUV ▸ i.reverse_le hb).trans hn
  have hden := critical_denominator_eq h hUV i hb
  have hcomm : ⁅A,W⁆ ≤ Zg := by
    change ⁅D.UH ⊓ i.conjugate D.QH,W⁆ ≤ Zg
    rw [←hden]
    exact commutator_commutatorPreimage_le D.UH W Zg hnorm
  have hZg : Nat.card Zg = 2 :=
    (card_map_of_injective (MulAut.conj i.representative).injective).trans h.point_card
  have hZA : D.V₁ ≤ A := by
    change D.V₁ ≤ D.UH ⊓ i.conjugate D.QH
    rw [←hden]
    apply le_commutatorPreimage (h.point_lt.le.trans (le_conjugateSpanBy _ _))
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hWH.trans h.H_centralizes))).le.trans bot_le
  let : (D.V₁.subgroupOf D.UH).Normal := normal_of_isMulCommutative _
  obtain ⟨σ,c,hσ,_⟩ := h.faithful_UH_section
  let π := QuotientGroup.mk' (pCore 2 D.H)
  let I := (W.subgroupOf D.H).map π
  have hI : Nat.card I = 2 := himage
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := I) 2 (by rw [hI])
  have ht' : orderOf (t : D.H ⧸ pCore 2 D.H) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hIt : zpowers (t : D.H ⧸ pCore 2 D.H) = I := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr t.property)
    rw [Nat.card_zpowers,ht',hI]
  obtain ⟨x,hx⟩ := Theory.SpecificGroups.exists_order_five_commutator_of_quintic_model
    hm (t : D.H ⧸ pCore 2 D.H) ht'
  have hl := two_le_displacement_of_commutator_order_five σ hσ
    (t : D.H ⧸ pCore 2 D.H) x hx
  rw [←fixedCodim_zpowers_eq_displacement_rank,hIt] at hl
  have hn : ¬ ⁅A,W⁆ ≤ D.V₁ := by
    intro hc
    have hfix := Representation.BinaryConjugationSection.fixedCodim_le_one_of_fixed_index
      D.H D.UH D.V₁ W A σ π c inf_le_left hZA
      (by simpa only [commutator_comm] using hc) hindex.le
    change fixedCodim σ I ≤ 1 at hfix
    omega
  have hd : Nat.card (⁅A,W⁆ : Subgroup G) ∣ 2 := hZg ▸ card_dvd_of_le hcomm
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact (hn ((card_eq_one.mp h1).le.trans bot_le)).elim
  · exact eq_of_le_of_card_ge hcomm (by rw [h2,hZg])

omit [Finite G] in
private theorem centralizer_hyperplane_eq
    (U A B Z : Subgroup G) (hAU : A ≤ U)
    (hi : A.relIndex U = 2) (hc : ⁅A,B⁆ = ⊥)
    (hm : ⁅U,B⁆ = Z) (hZ : Nat.card Z = 2) : U ⊓ centralizer (B : Set G) = A := by
  have hAC : A ≤ U ⊓ centralizer (B : Set G) :=
    le_inf hAU (commutator_eq_bot_iff_le_centralizer.mp hc)
  have hh := relIndex_mul_relIndex A (U ⊓ centralizer (B : Set G)) U hAC inf_le_left
  rw [hi] at hh
  rcases Nat.prime_mul_iff.mp (hh ▸ Nat.prime_two) with hp | hp
  · have hu : U ≤ centralizer (B : Set G) := (relIndex_eq_one.mp hp.2).trans inf_le_right
    have hz : Z = ⊥ := hm.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hu)
    have hh1 := hZ
    rw [hz,card_bot] at hh1
    omega
  · exact le_antisymm (relIndex_eq_one.mp hp.2) hAC

omit [Finite G] in
private theorem binary_row_index_two
    (A W B Z : Subgroup G) [IsMulCommutative A]
    (hBW : B ≤ W) (hi : B.relIndex W = 2)
    (hAB : ⁅A,B⁆ = ⊥) (hAW : ⁅A,W⁆ = Z)
    (hZA : Z ≤ A) (hZ : Nat.card Z = 2) :
    (centralizer (W : Set G)).relIndex A = 2 := by
  classical
  have hnot : ¬ W ≤ B := by
    intro hh
    have he := le_antisymm hBW hh
    rw [he,relIndex_self] at hi
    omega
  obtain ⟨w,hw,hwB⟩ := Set.not_subset.mp hnot
  have hvalue (a : A) : ⁅(a : G),w⁆ ∈ Z :=
    hAW ▸ commutator_mem_commutator a.property hw
  let f : A →* Z := {
    toFun a := ⟨⁅(a:G),w⁆,hvalue a⟩
    map_one' := Subtype.ext (by simp)
    map_mul' a b := by
      apply Subtype.ext
      change ⁅(a:G)*(b:G),w⁆ = ⁅(a:G),w⁆ * ⁅(b:G),w⁆
      rw [commutatorElement_mul_left_eq_conj_mul,
        ←setLike_mul_comm (hZA (hvalue b)) a.property,mul_inv_cancel_right]
      exact setLike_mul_comm (hZA (hvalue b)) (hZA (hvalue a)) }
  have he := inf_centralizer_eq_of_prime_index_supplement A B W hBW Nat.prime_two hi
    (commutator_eq_bot_iff_le_centralizer.mp hAB) w hw hwB
  have hk : f.ker = (centralizer (W : Set G)).subgroupOf A := by
    ext a
    change (⟨⁅(a:G),w⁆,hvalue a⟩ : Z) = 1 ↔ (a:G) ∈ centralizer (W : Set G)
    rw [Subtype.ext_iff]
    change ⁅(a:G),w⁆ = 1 ↔ _
    rw [commutatorElement_eq_one_iff_mul_comm]
    constructor
    · intro hh
      exact (he ▸ (show (a:G) ∈ A ⊓ centralizer ({w} : Set G) from
        ⟨a.property,mem_centralizer_singleton_iff.mpr hh⟩)).2
    · intro hh
      exact (hh w hw).symm
  have hn : f.range ≠ ⊥ := by
    intro hz
    have hAC : A ≤ centralizer (W : Set G) := by
      intro a ha
      have hf : f ⟨a,ha⟩ = 1 := mem_bot.mp (hz ▸ (show f ⟨a,ha⟩ ∈ f.range from ⟨⟨a,ha⟩,rfl⟩))
      exact (show (⟨a,ha⟩ : A) ∈ (centralizer (W : Set G)).subgroupOf A from
        hk ▸ hf)
    have hz' : Z = ⊥ := hAW.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hAC)
    have h1 := hZ
    rw [hz',card_bot] at h1
    omega
  have hr : Nat.card f.range = 2 := by
    have hd := f.range.card_subgroup_dvd_card
    rw [hZ] at hd
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (fun h => hn (card_eq_one.mp h))
  change ((centralizer (W : Set G)).subgroupOf A).index = 2
  rw [←hk,index_ker,hr]

private theorem critical_kernel_indices
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH] (hUV : D.UH = D.VH)
    (i : h.CriticalEndpoint) (hb : 3 ≤ h.b)
    (hAidx : (D.UH ⊓ i.conjugate D.QH).relIndex D.UH = 2)
    (hBidx : (i.conjugate D.UH ⊓ D.QH).relIndex (i.conjugate D.UH) = 2)
    (hAB : ⁅D.UH ⊓ i.conjugate D.QH,i.conjugate D.UH ⊓ D.QH⁆ = ⊥)
    (hpoint : ⁅i.conjugate D.UH ⊓ D.QH,D.UH⁆ = D.V₁) :
    let C := D.H ⊓ centralizer (D.UH : Set G)
    (C ⊓ i.conjugate D.UH).relIndex (i.conjugate D.UH ⊓ D.QH) = 2 ∧
      (C ⊓ i.conjugate D.UH).relIndex (i.conjugate D.UH) = 4 := by
  let W := i.conjugate D.UH
  let A := D.UH ⊓ i.conjugate D.QH
  let B := W ⊓ D.QH
  let C := D.H ⊓ centralizer (D.UH : Set G)
  let R := C ⊓ W
  have hWH : W ≤ D.H := by simpa only [W,hUV] using i.large_le hb
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (show B ≤ W from inf_le_left)
  have hmut : ⁅D.UH,W⁆ ≤ D.UH ⊓ W := by
    simpa only [W,←hUV] using i.commutator hb
  have hZB : D.V₁ ≤ B := by
    apply le_inf ?_ ((h.point_lt.le.trans (le_conjugateSpanBy _ _)).trans h.UH_le_QH)
    calc
      D.V₁ = ⁅B,D.UH⁆ := hpoint.symm
      _ ≤ ⁅W,D.UH⁆ := commutator_mono inf_le_left le_rfl
      _ ≤ W := (commutator_comm W D.UH).le.trans (hmut.trans inf_le_right)
  have hrow := binary_row_index_two B D.UH A D.V₁ inf_le_left hAidx
    ((commutator_comm _ _).trans hAB) hpoint hZB h.point_card
  have hRB : R ≤ B := by
    change R ≤ W ⊓ D.QH
    rw [←f9_commutatorPreimage_eq D h W hWH]
    apply le_commutatorPreimage inf_le_right
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (show R ≤ centralizer (D.UH : Set G) from inf_le_left.trans inf_le_right)).le.trans bot_le
  have hk : R.subgroupOf B = (centralizer (D.UH : Set G)).subgroupOf B := by
    ext b
    change ((b:G) ∈ C ∧ (b:G) ∈ W) ↔ (b:G) ∈ centralizer (D.UH : Set G)
    exact ⟨fun hh => hh.1.2,fun hh => ⟨⟨hWH b.property.1,hh⟩,b.property.1⟩⟩
  have htwo : R.relIndex B = 2 := by
    change (R.subgroupOf B).index = 2
    rw [hk]
    exact hrow
  have hfour := relIndex_mul_relIndex R B W hRB inf_le_left
  rw [htwo,hBidx] at hfour
  exact ⟨htwo,hfour.symm⟩

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

/-- The actual quintic hyperplanes move precisely the opposite point lines,
and each is the full centralizer of its partner inside its original module. -/
theorem source_quintic_hyperplane_point_actions
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH.1
    ∀ i : h.CriticalEndpoint,
      ⁅D.UH ⊓ i.conjugate D.QH,i.conjugate D.UH⁆ = i.conjugate D.V₁ ∧
      ⁅i.conjugate D.UH ⊓ D.QH,D.UH⁆ = D.V₁ ∧
      D.UH ⊓ centralizer (i.conjugate D.UH ⊓ D.QH : Set G) = D.UH ⊓ i.conjugate D.QH ∧
      i.conjugate D.UH ⊓ centralizer (D.UH ⊓ i.conjugate D.QH : Set G) =
        i.conjugate D.UH ⊓ D.QH := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH.1
  let : IsElementaryAbelian 2 D.UH :=
    (Section02.SolvableAmalgam.source_index_five_closure_structure
      hG T hempty hM hu hmany hcard e H hH.1 hi).1
  have hm := Section02.SolvableAmalgam.source_index_five_models
    hG T hempty hM hu hmany hcard e H hH.1 hi
  obtain ⟨hb,_,_,hall⟩ := source_quintic_reciprocal_core_hyperplanes
    hG T hempty hM hu hmany hcard e hab H hH hi
  change ∀ i : h.CriticalEndpoint, _
  intro i
  obtain ⟨j,hj,_,himage,hidx,hidx',hcomm,_⟩ := hall i
  have hpoint := critical_denominator_moves_point h hm rfl i hb himage hidx
  obtain ⟨_,_,_,hjimage,hjidx,_,_,_⟩ := hall j
  have hjpoint := critical_denominator_moves_point h hm rfl j hb hjimage hjidx
  have hUN : H ≤ normalizer (D.UH : Set G) := le_normalizer_conjugateSpanBy _ _
  have hreverse : ⁅i.conjugate D.UH ⊓ D.QH,D.UH⁆ = D.V₁ := by
    apply map_injective (f := (MulAut.conj j.representative).toMonoidHom)
      (MulAut.conj j.representative).injective
    rw [map_commutator,map_inf _ _ _ (MulAut.conj j.representative).injective,
      hj D.UH hUN]
    exact hjpoint
  refine ⟨hpoint,hreverse,?_,?_⟩
  · exact centralizer_hyperplane_eq D.UH (D.UH ⊓ i.conjugate D.QH)
      (i.conjugate D.UH ⊓ D.QH) D.V₁
      inf_le_left hidx hcomm
      ((commutator_comm _ _).trans hreverse) h.point_card
  · exact centralizer_hyperplane_eq (i.conjugate D.UH) (i.conjugate D.UH ⊓ D.QH)
      (D.UH ⊓ i.conjugate D.QH) (i.conjugate D.V₁)
      inf_le_left hidx' ((commutator_comm _ _).trans hcomm)
      ((commutator_comm _ _).trans hpoint)
      ((card_map_of_injective (MulAut.conj i.representative).injective).trans h.point_card)

/-- Each original critical module intersects the full opposite radius-two
kernel in index four, and its core hyperplane in index two. These are the
literal kernels, with the same conjugator and paired radical orders retained. -/
theorem source_quintic_full_kernel_radicals
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH.1
    let C := H ⊓ centralizer (D.UH : Set G)
    ∀ i : h.CriticalEndpoint,
      (C ⊓ i.conjugate D.UH).relIndex (i.conjugate D.UH ⊓ D.QH) = 2 ∧
      (i.conjugate C ⊓ D.UH).relIndex (D.UH ⊓ i.conjugate D.QH) = 2 ∧
      (C ⊓ i.conjugate D.UH).relIndex (i.conjugate D.UH) = 4 ∧
      (i.conjugate C ⊓ D.UH).relIndex D.UH = 4 ∧
      ((Nat.card (C ⊓ i.conjugate D.UH : Subgroup G) = 8 ∧
        Nat.card (i.conjugate C ⊓ D.UH : Subgroup G) = 8) ∨
       (Nat.card (C ⊓ i.conjugate D.UH : Subgroup G) = 16 ∧
        Nat.card (i.conjugate C ⊓ D.UH : Subgroup G) = 16)) := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH.1
  let C := H ⊓ centralizer (D.UH : Set G)
  obtain ⟨hel,hsize⟩ := Section02.SolvableAmalgam.source_index_five_closure_structure
    hG T hempty hM hu hmany hcard e H hH.1 hi
  let : IsElementaryAbelian 2 D.UH := hel
  obtain ⟨hb,_,_,hall⟩ := source_quintic_reciprocal_core_hyperplanes
    hG T hempty hM hu hmany hcard e hab H hH hi
  have hlocal (k : h.CriticalEndpoint) :
      (C ⊓ k.conjugate D.UH).relIndex (k.conjugate D.UH ⊓ D.QH) = 2 ∧
      (C ⊓ k.conjugate D.UH).relIndex (k.conjugate D.UH) = 4 := by
    obtain ⟨_,_,_,_,ha,hb',hc,_⟩ := hall k
    have hp := (source_quintic_hyperplane_point_actions
      hG T hempty hM hu hmany hcard e hab H hH hi k).2.1
    exact critical_kernel_indices h rfl k hb ha hb' hc hp
  have hCN : H ≤ normalizer (C : Set G) :=
    (le_inf H.le_normalizer ((le_normalizer_conjugateSpanBy _ _).trans
      (normalizer_le_normalizer_centralizer D.UH))).trans inf_normalizer_le_normalizer_inf
  have hQN : H ≤ normalizer (D.QH : Set G) :=
    ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := D)
  change ∀ i : h.CriticalEndpoint, _
  intro i
  obtain ⟨j,hj,_,_,_,_,_,_⟩ := hall i
  obtain ⟨hri,hfi⟩ := hlocal i
  obtain ⟨hrj,hfj⟩ := hlocal j
  have hm2 := relIndex_map_map_of_injective (f := (MulAut.conj j.representative).toMonoidHom)
    (i.conjugate C ⊓ D.UH) (D.UH ⊓ i.conjugate D.QH)
    (MulAut.conj j.representative).injective
  rw [map_inf _ _ _ (MulAut.conj j.representative).injective,
    map_inf _ _ _ (MulAut.conj j.representative).injective,hj C hCN,hj D.QH hQN] at hm2
  have hri' : (i.conjugate C ⊓ D.UH).relIndex (D.UH ⊓ i.conjugate D.QH) = 2 :=
    hm2.symm.trans hrj
  have hm4 := relIndex_map_map_of_injective (f := (MulAut.conj j.representative).toMonoidHom)
    (i.conjugate C ⊓ D.UH) D.UH (MulAut.conj j.representative).injective
  rw [map_inf _ _ _ (MulAut.conj j.representative).injective,hj C hCN] at hm4
  have hfi' : (i.conjugate C ⊓ D.UH).relIndex D.UH = 4 := hm4.symm.trans hfj
  have hc1 := relIndex_mul_card_of_le
    (show C ⊓ i.conjugate D.UH ≤ i.conjugate D.UH from inf_le_right)
  have hc2 := relIndex_mul_card_of_le
    (show i.conjugate C ⊓ D.UH ≤ D.UH from inf_le_right)
  rw [hfi,card_map_of_injective (MulAut.conj i.representative).injective] at hc1
  rw [hfi'] at hc2
  refine ⟨hri,hri',hfi,hfi',?_⟩
  change Nat.card D.UH = 32 ∨ Nat.card D.UH = 64 at hsize
  rcases hsize with hs | hs
  · exact Or.inl ⟨Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) (hc1.trans hs),
      Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) (hc2.trans hs)⟩
  · exact Or.inr ⟨Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) (hc1.trans hs),
      Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) (hc2.trans hs)⟩

end CFSG.Quasithin.Chapter14.Section06
