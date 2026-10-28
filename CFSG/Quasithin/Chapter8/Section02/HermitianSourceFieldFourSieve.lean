module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourNonsolvable
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddDegreeThree.SmallExclusion
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddLinearTwo.SmallImage
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import GorensteinWalter.LinearRingEquiv
public import Theory.SpecificGroups.PSL2.ThreeFiveInverters
public import Theory.GroupAction.InvertedOddLift
public import Theory.SpecificGroups.PSL3.DefiningRank
public import Theory.SpecificGroups.SU3.OddDefiningRank
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The nonsolvable Hermitian source sieve

The marked involution fixes the full maximal-core kernel. Its inverted odd
rotations therefore lift with their exact orders, carrying the 3/5 restriction
from the actual two-core quotient into the full maximal-core quotient.
In the odd degree-three rows a defining-prime root forces p=3 or 5, contrary
to the rank-two root plane and the original odd-rank bounds. For PSL₂ the
reflected torus calculation leaves only fields seven and thirty-one. The
literal PSL₂(7) ≃ PSL₃(2) comparison supplies the binary diagram marking.

The final theorem retains the same normal quasisimple residual, its entire
center, maximal overlap and automizer/diagram data. It is the model inspection
in Aschbacher–Smith 8.2.9, printed pp.720–721, refs/quasithin.pdf
(1 March 2004 manuscript). The later chief-section exclusion is still needed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X] [Finite X]
set_option backward.isDefEq.respectTransparency false

omit [Finite X] in
/-- The marked 3/5 rotation restriction survives the full maximal-core quotient. -/
theorem parabolic_star_small_rotations
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (W : Subgroup X) [IsElementaryAbelian 2 W]
    (hcent : minimalParabolicMax S hP ≤ centralizer (W : Set X))
    (hrot : ∀ (v r : X), v ∈ W → v ≠ 1 → v*r*v⁻¹=r⁻¹ →
      ∀ p a : ℕ, p.Prime → p ≠ 2 → 0 < a → orderOf r = p^a →
        orderOf r = 3 ∨ orderOf r = 5) :
    let q := QuotientGroup.mk' (minimalParabolicCore S hP)
    ∀ (v r : X ⧸ minimalParabolicCore S hP), v ∈ W.map q → v ≠ 1 →
      v*r*v⁻¹=r⁻¹ → ∀ p a : ℕ, p.Prime → p ≠ 2 → 0 < a →
        orderOf r = p^a → orderOf r = 3 ∨ orderOf r = 5 := by
  let J := minimalParabolicCore S hP
  let q := QuotientGroup.mk' J
  dsimp only
  intro v r hv hv1 hi p a hp hp2 ha hr
  obtain ⟨w,hw,rfl⟩ := hv
  have hw1 : w ≠ 1 := fun he => hv1 (by rw [he,map_one])
  have hw2 : w^2=1 := elemPow_eq_one_of_isElementaryAbelian w hw
  have hker : ∀ x ∈ q.ker, MulAut.conj w x=x := by
    intro x hx
    have hxJ : x ∈ J := by simpa only [q,QuotientGroup.ker_mk'] using hx
    have hc := hcent ((minimalParabolicMax S hP).normalCore_le hxJ) w hw
    change w*x*w⁻¹=x
    rw [hc,mul_inv_cancel_right]
  obtain ⟨x,hx,hix⟩ := MulAut.exists_inverted_odd_of_fixed_kernel
    (MulAut.conj w) (MulAut.conj (q w)) q (QuotientGroup.mk'_surjective J)
    (fun x => by simp only [MulAut.conj_apply,map_mul,map_inv])
    (by rw [←map_pow,hw2,map_one]) hker (hp.odd_of_ne_two hp2).pow r hr hi
  rcases hrot w x hw hw1 hix p a hp hp2 ha hx with h | h
  · exact Or.inl (hr.trans (hx.symm.trans h))
  · exact Or.inr (hr.trans (hx.symm.trans h))

private theorem star_rank_le_one (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hb : primeRank p X ≤ 1) :
    primeRank p (X ⧸ minimalParabolicCore S hP) ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let P : Sylow p X := Classical.choice inferInstance
  exact P.primeRank_quotient_le_one (P.isCyclic_of_odd_of_primeRank_le_one ho hb) _

/-- Neither odd degree-three source row satisfies the original rank and rotation bounds. -/
theorem parabolic_not_odd_rank_three_of_small_rotations
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (hs : ¬Group.IsSolvable X)
    (K : Subgroup X) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (S : Subgroup X) = ⊤)
    (W : Subgroup X) [IsElementaryAbelian 2 W] (hWS : W ≤ S)
    (hout : ¬W ≤ minimalParabolicCore S hP)
    (hMW : minimalParabolicMax S hP ≤ normalizer (W : Set X))
    (hcard : Nat.card W = 2) (h3 : primeRank 3 X ≤ 1) (h5 : primeRank 5 X ≤ 1)
    (hrot : ∀ (v r : X), v ∈ W → v ≠ 1 → v*r*v⁻¹=r⁻¹ →
      ∀ p a : ℕ, p.Prime → p ≠ 2 → 0 < a → orderOf r = p^a →
        orderOf r = 3 ∨ orderOf r = 5)
    (hm : SingleOddRankThreeModel (minimalParabolicMax S hP) K (S : Subgroup X)) :
    False := by
  let J := minimalParabolicCore S hP
  let q := QuotientGroup.mk' J
  have hcent := hMW.trans (normalizer_le_centralizer_of_card_two W hcard)
  have hWN : (W.subgroupOf (S : Subgroup X)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hWS).mpr
      ((minimalParabolicMax_spec S hP).2.trans hMW)
  have hres : (pResidual 2 (minimalParabolicMax S hP)).map
      (minimalParabolicMax S hP).subtype ≤ centralizer (W : Set X) :=
    (map_subtype_le _).trans hcent
  have hrotq := parabolic_star_small_rotations S hP W hcent hrot
  obtain ⟨p,hp,ho,_,hu | hl⟩ := hm
  · obtain ⟨hmod,hm⟩ := hu
    obtain ⟨_,_,t,ht,htW⟩ := Witnesses.OddDegreeThree.unitary_source_image_involution
      S hP hs K hK hgen hp ho hm W hWS hWN hout hres
    obtain ⟨F,hF,hfin,A,hsize,hconj,⟨e⟩⟩ := hm
    have hp2 : p≠2 := by intro he; rw [he] at ho; norm_num at ho
    obtain ⟨r,hr,hi⟩ := BenderSuzuki.MatrixGroups.HermitianForm.OddInvolutionRoot.exists_inverted_root
      A hp hp2 hsize hconj (e t) ((e.orderOf_eq t).trans ht)
    let j := (K.map q).subtype.comp e.symm.toMonoidHom
    have hj : Function.Injective j := Subtype.val_injective.comp e.symm.injective
    have hjt : j (e t) = (t : X ⧸ J) := by
      change (e.symm (e t)).val=t.val
      rw [e.symm_apply_apply]
    have ht1 : (t : X ⧸ J) ≠ 1 := by
      intro he
      have ht1 : t=1 := Subtype.ext he
      simp [ht1] at ht
    have hir : (t : X ⧸ J)*j r*(t : X ⧸ J)⁻¹=(j r)⁻¹ := by
      simpa only [map_mul,map_inv,hjt] using congrArg j hi
    have horder : orderOf (j r)=p := (orderOf_injective j hj r).trans hr
    have hp35 := hrotq t (j r) htW ht1 hir p 1 hp hp2 (by decide) (by simpa using horder)
    rw [horder] at hp35
    have hp5 : p=5 := by omega
    rcases hp5 with rfl
    let : Fact (Nat.Prime 5) := ⟨hp⟩
    have hlo := BenderSuzuki.MatrixGroups.HermitianForm.OddDefiningRank.two_mul_fieldExponent_le_primeRank
      A (by decide : 5≠2) (by decide : 0<1)
      (by simpa only [pow_one] using hsize) (by simpa only [pow_one] using hconj)
    have hup := (primeRank_subgroup_le 5 (K.map q)).trans (star_rank_le_one S hP hp ho h5)
    have hup' := (primeRank_equiv 5 e).ge.trans hup
    omega
  · obtain ⟨hmod,F,hF,hfin,hsize,e,_⟩ := hl
    have hm : ClassicalGroup.IsPSL (K.map q) 3 p := ⟨F,hF,hfin,hsize,⟨e⟩⟩
    obtain ⟨_,t,ht,htW⟩ := Witnesses.OddDegreeThree.linear_source_image_involution
      S hP hs K hK hgen hp ho hm W hWS hWN hout hres
    obtain ⟨r,hr,hi⟩ := Matrix.PSL3.OddInvolutionRoot.exists_inverted_root
      hp ho hsize (e t) ((e.orderOf_eq t).trans ht)
    let j := (K.map q).subtype.comp e.symm.toMonoidHom
    have hj : Function.Injective j := Subtype.val_injective.comp e.symm.injective
    have hjt : j (e t) = (t : X ⧸ J) := by
      change (e.symm (e t)).val=t.val
      rw [e.symm_apply_apply]
    have ht1 : (t : X ⧸ J) ≠ 1 := by
      intro he
      have ht1 : t=1 := Subtype.ext he
      simp [ht1] at ht
    have hir : (t : X ⧸ J)*j r*(t : X ⧸ J)⁻¹=(j r)⁻¹ := by
      simpa only [map_mul,map_inv,hjt] using congrArg j hi
    have horder : orderOf (j r)=p := (orderOf_injective j hj r).trans hr
    have hp2 : p≠2 := by intro he; rw [he] at ho; norm_num at ho
    have hp35 := hrotq t (j r) htW ht1 hir p 1 hp hp2 (by decide) (by simpa using horder)
    rw [horder] at hp35
    have hp3 : p=3 := by omega
    rcases hp3 with rfl
    let : Fact (Nat.Prime 3) := ⟨hp⟩
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 3 := charP_of_card_eq_prime_pow
      (by simpa only [pow_one,Nat.card_eq_fintype_card] using hsize : Fintype.card F = 3^1)
    have hlo := Matrix.PSL3.DefiningRank.two_mul_fieldExponent_le_primeRank F
      (by simpa only [pow_one] using hsize : Nat.card F = 3^1)
    have hup := (primeRank_subgroup_le 3 (K.map q)).trans (star_rank_le_one S hP hp ho h3)
    have hup' := (primeRank_equiv 3 e).ge.trans hup
    omega

/-- The odd linear row gives PSL₂(31) or the actual binary PSL₃(2) diagram model. -/
theorem parabolic_odd_linear_small_rotations_models
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (hs : ¬Group.IsSolvable X)
    (K : Subgroup X) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (S : Subgroup X) = ⊤)
    (W : Subgroup X) [IsElementaryAbelian 2 W] (hWS : W ≤ S)
    (hout : ¬W ≤ minimalParabolicCore S hP)
    (hMW : minimalParabolicMax S hP ≤ normalizer (W : Set X))
    (hcard : Nat.card W = 2)
    (hrot : ∀ (v r : X), v ∈ W → v ≠ 1 → v*r*v⁻¹=r⁻¹ →
      ∀ p a : ℕ, p.Prime → p ≠ 2 → 0 < a → orderOf r = p^a →
        orderOf r = 3 ∨ orderOf r = 5)
    (hm : SingleOddLinearModel (minimalParabolicMax S hP) K (S : Subgroup X)) :
    ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax S hP) K) 2 31 ∨
      ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax S hP) K) 3 2 ∧
        DiagramModel (minimalParabolicMax S hP) K (S : Subgroup X) 1 := by
  obtain ⟨p,d,hp,hp3,hd,hd2,hmod,F,hF,hfin,hsize,e,_⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  have hd' : d=1 ∨ d=2 := by omega
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  by_cases hseven : p^d=7
  · let := Fintype.ofFinite F
    let eF : ZMod 7 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
      (by simpa only [Nat.card_eq_fintype_card,hseven] using hsize)
    let e' := (e.trans (GorensteinWalter.psl2RingEquiv eF).symm).trans
      Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two
    have hbinary : ClassicalGroup.IsPSL
        (sourceImage (minimalParabolicMax S hP) K) 3 2 :=
      ⟨ZMod 2,inferInstance,inferInstance,by simp,⟨e'⟩⟩
    exact Or.inr ⟨hbinary,source_binary_linear_three_model S hP hs K hK hgen
      (by decide : 0<1) (by simpa only [pow_one] using hbinary)⟩
  · have hlarge : 9<p^d := by
      rcases hd' with rfl | rfl
      · simp only [pow_one] at hmod hseven ⊢
        have hp9 : p≠9 := by intro he; exact (by decide : ¬Nat.Prime 9) (he ▸ hp)
        omega
      · nlinarith
    let J := minimalParabolicCore S hP
    let q := QuotientGroup.mk' J
    have hWN : (W.subgroupOf (S : Subgroup X)).Normal :=
      (normal_subgroupOf_iff_le_normalizer hWS).mpr
        ((minimalParabolicMax_spec S hP).2.trans hMW)
    have hcore : W ≤ (minimalParabolicMax S hP).pCoreIn 2 :=
      le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 W)
        (hWS.trans (minimalParabolicMax_spec S hP).2) hMW
    obtain ⟨_,t,ht,htW⟩ := Witnesses.OddLinearTwo.source_odd_image_involution
      S hP hs K hK hgen hp ho hp3 hd' hlarge ⟨F,hF,hfin,hsize,⟨e⟩⟩
      W hWS hWN hcore hout
    have hcent := hMW.trans (normalizer_le_centralizer_of_card_two W hcard)
    have hrotq := parabolic_star_small_rotations S hP W hcent hrot
    let j := (K.map q).subtype.comp e.symm.toMonoidHom
    have hj : Function.Injective j := Subtype.val_injective.comp e.symm.injective
    have hjt : j (e t) = (t : X ⧸ J) := by
      change (e.symm (e t)).val=t.val
      rw [e.symm_apply_apply]
    have ht1 : (t : X ⧸ J) ≠ 1 := by
      intro he
      have ht1 : t=1 := Subtype.ext he
      simp [ht1] at ht
    have hb : ∀ r : PSL(2,F), e t*r*(e t)⁻¹=r⁻¹ → ∀ r₀ a : ℕ,
        r₀.Prime → r₀≠2 → 0<a → orderOf r=r₀^a → orderOf r=3 ∨ orderOf r=5 := by
      intro r hi r₀ a hr₀ hr2 ha hr
      have hir : (t : X ⧸ J)*j r*(t : X ⧸ J)⁻¹=(j r)⁻¹ := by
        simpa only [map_mul,map_inv,hjt] using congrArg j hi
      have hord := orderOf_injective j hj r
      simpa only [hord] using hrotq t (j r) htW ht1 hir r₀ a hr₀ hr2 ha (hord.trans hr)
    have hq := Theory.PSL2.ThreeFiveInverters.field_card_eq_seven_or_thirty_one hp3 hd' hsize
      (by simpa only [hsize] using hmod) (e t) ((e.orderOf_eq t).trans ht) hb
    have hq31 : Nat.card F=31 := hq.resolve_left (fun he => hseven (hsize.symm.trans he))
    exact Or.inl ⟨F,hF,hfin,hq31,⟨e⟩⟩

/-- The full two-core quotient retains only the two marked nonsolvable source images. -/
theorem parabolic_quotient_small_rotation_models
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (hs : ¬Group.IsSolvable X)
    (W : Subgroup X) [IsElementaryAbelian 2 W] (hWS : W ≤ S)
    (hout : ¬W ≤ minimalParabolicCore S hP)
    (hMW : minimalParabolicMax S hP ≤ normalizer (W : Set X))
    (hcard : Nat.card (W.map (QuotientGroup.mk' (pCore 2 X))) = 2)
    (h3 : primeRank 3 X ≤ 1) (h5 : primeRank 5 X ≤ 1)
    (hrot : let q := QuotientGroup.mk' (pCore 2 X)
      ∀ (v r : X ⧸ pCore 2 X), v ∈ W.map q → v ≠ 1 → v*r*v⁻¹=r⁻¹ →
        ∀ p a : ℕ, p.Prime → p ≠ 2 → 0 < a → orderOf r = p^a →
          orderOf r = 3 ∨ orderOf r = 5) :
    let q := QuotientGroup.mk' (pCore 2 X)
    let M := (minimalParabolicMax S hP).map q
    let T := (S : Subgroup X).map q
    ∃ K : Subgroup (X ⧸ pCore 2 X), IsComponent (X ⧸ pCore 2 X) K ∧
      K.IsCComponent ∧ K.Normal ∧ pResidual 2 (X ⧸ pCore 2 X) = K ∧
      (minimalParabolicCore S hP).map q = (center K).map K.subtype ∧
      K ⊔ T = ⊤ ∧ SingleClauses M K T ∧
      ((ClassicalGroup.IsPSL (sourceImage M K) 2 31 ∧ SingleOddLinearModel M K T) ∨
       ClassicalGroup.IsPSL (sourceImage M K) 3 2 ∧ DiagramModel M K T 1) := by
  obtain ⟨K,hcomp,hK,hn,hres,hcenter,hgen,hclauses,hmodels⟩ :=
    parabolic_quotient_normal_component_models hX S hP hs W hWS hout hMW hcard h3
  let := hn
  let N := pCore 2 X
  let q := QuotientGroup.mk' N
  let R := S.mapSurjective (QuotientGroup.mk'_surjective N)
  let A := W.map q
  have hk : q.ker ≤ (S : Subgroup X) := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal S
  have hPq := minimalParabolic_surjective S hP q (QuotientGroup.mk'_surjective N) hk
  have hJpre : (minimalParabolicCore R hPq).comap q = minimalParabolicCore S hP := by
    rw [←minimalParabolicCore_map S hP q (QuotientGroup.mk'_surjective N) hk,
      comap_map_eq,QuotientGroup.ker_mk',
      sup_eq_left.mpr (minimalParabolicTwoCore_le_core S hP)]
  have hmax : minimalParabolicMax R hPq = (minimalParabolicMax S hP).map q :=
    (minimalParabolicMax_map_core S hP q (QuotientGroup.mk'_surjective N)
      (by simpa only [q,QuotientGroup.ker_mk'] using minimalParabolicTwoCore_le_core S hP)).symm
  have hAR : A ≤ (R : Subgroup (X ⧸ N)) := map_mono hWS
  have hN : minimalParabolicMax R hPq ≤ normalizer (A : Set (X ⧸ N)) := by
    rw [hmax]
    exact (map_mono hMW).trans (le_normalizer_map q)
  have houtq : ¬A ≤ minimalParabolicCore R hPq := by
    intro ha
    apply hout
    have hh := map_le_iff_le_comap.mp ha
    rwa [hJpre] at hh
  let : Group.IsNilpotent N := (pCore_isPGroup (p := 2) (G := X)).isNilpotent
  have hsq : ¬Group.IsSolvable (X ⧸ N) := fun hh =>
    hs ((Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance,hh⟩)
  have h3q : primeRank 3 (X ⧸ N) ≤ 1 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) N pCore_isPGroup).trans h3
  have h5q : primeRank 5 (X ⧸ N) ≤ 1 :=
    (primeRank_quotient_le_of_isTwoGroup 5 (by decide) N pCore_isPGroup).trans h5
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map q
  refine ⟨K,hcomp,hK,hn,hres,hcenter,hgen,hclauses,?_⟩
  rcases hmodels with hlin | hthree | hbinary
  · have hl := hlin
    rw [←hmax] at hl
    rcases parabolic_odd_linear_small_rotations_models R hPq hsq K hK hgen
      A hAR houtq hN hcard hrot hl with h31 | h2
    · rw [hmax] at h31
      exact Or.inl ⟨h31,hlin⟩
    · rw [hmax] at h2
      exact Or.inr h2
  · rw [←hmax] at hthree
    exact (parabolic_not_odd_rank_three_of_small_rotations R hPq hsq K hK hgen
      A hAR houtq hN hcard h3q h5q hrot hthree).elim
  · exact Or.inr hbinary

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
