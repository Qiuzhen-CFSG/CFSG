module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddLinearTwo.SmallImage
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Involution.SmallPrimePower
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThree.BinarySmallExclusion
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import Theory.SpecificGroups.PSL2.LargeOddInverter
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import GorensteinWalter.LinearRingEquiv
-- Internal source adapter: identify the marked maximal core with the original J.
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# Excluding the original odd linear-two small-automizer row

The original quotient image of V has order two and contains an involution
of the actual normal PSL₂ component. For every parameter above seven, a
reflected torus supplies an odd prime-power element of order greater than
three inverted by that involution. The original small quaternion pair
forces the same order to equal three, a contradiction. The parameter seven
is carried through the proved PSL₂(7) ≃ PSL₃(2) isomorphism and excluded by
the binary linear-three source theorem.

The complete marked-row consumer takes the original quotient, maximal core,
and action. It leaves no inverter, field, placement, or model-action premise.
Source: Aschbacher–Smith E.2.17, printed pp.229–230.
-/
public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.OddLinearTwo
open Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]

theorem source_nonexceptional_odd_small_automizer_false
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {p n : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hn : n=1 ∨ n=2)
    (hlarge : 9 < p^n) (hmod : p^n % 8 = 1 ∨ p^n % 8 = 7)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (p^n))
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk)) : False := by
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)
  obtain ⟨hcard,t,ht,htV⟩ := source_odd_image_involution T hP hs K hK hgen hp ho hp3 hn
    hlarge hm V hVT hvn hcore hout
  obtain ⟨F,hF,hfin,hsize,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨r,a,hr,hr2,ha,hbig,x,hx,hinv⟩ := Theory.PSL2.exists_large_odd_prime_power_inverted
    ho hsize (by omega) (by simpa only [hsize] using hmod) (e t) ((e.orderOf_eq t).trans ht)
  let y : K.map q := e.symm x
  have hy : orderOf (y : H ⧸ ChapterB.minimalParabolicCore T hP) = r^a := by
    rw [Subgroup.orderOf_coe]
    exact (e.symm.orderOf_eq x).trans hx
  have hi : (t : H ⧸ ChapterB.minimalParabolicCore T hP) * y * t⁻¹ = y⁻¹ := by
    change (K.map q).subtype (t*y*t⁻¹) = (K.map q).subtype y⁻¹
    congr 1
    apply e.injective
    simpa only [y,map_mul,map_inv,e.apply_symm_apply] using hinv
  have ht1 : (t : H ⧸ ChapterB.minimalParabolicCore T hP) ≠ 1 := by
    intro he
    have ht1 : t = 1 := Subtype.ext he
    rw [ht1,orderOf_one] at ht
    omega
  have hh := Involution.source_prime_power_inverter_eq_three T hP V hVT hvn hcore hout
    hfit hV U hTU hU f hf hk hD hratio hcard hr hr2 ha t y htV ht1 hy hi
  omega

theorem source_odd_linear_small_automizer_false
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : SingleOddLinearModel (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H))
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk))
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) : False := by
  obtain ⟨p,n,hp,hp3,hn,hnt,hmod,F,hF,hfin,hsize,e,_,_,_⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  have hn' : n=1 ∨ n=2 := by omega
  by_cases hseven : p^n = 7
  · let := Fintype.ofFinite F
    let eF : ZMod 7 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
      (by simpa only [Nat.card_eq_fintype_card,hseven] using hsize)
    let e' := (e.trans (GorensteinWalter.psl2RingEquiv eF).symm).trans
      Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two
    have hbinary : ClassicalGroup.IsPSL
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 2 :=
      ⟨ZMod 2,inferInstance,inferInstance,by simp,⟨e'⟩⟩
    exact LinearThree.source_binary_small_automizer_false T hP hs K hK hgen hbinary V
      hVT hvn hcore hout hfit hV U hTU hU f hf hk hD hratio hres
  · have hlarge : 9 < p^n := by
      rcases hn' with rfl | rfl
      · simp only [pow_one] at hmod hseven ⊢
        have hp9 : p ≠ 9 := by intro hh; subst p; norm_num at hp
        omega
      · nlinarith
    exact source_nonexceptional_odd_small_automizer_false T hP hs K hK hgen hp hp3 hn'
      hlarge hmod ⟨F,hF,hfin,hsize,⟨e⟩⟩ V hVT hvn hcore hout hfit hV U hTU hU
      f hf hk hD hratio
end CFSG.Quasithin.ChapterE.Witnesses.OddLinearTwo
