module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.OmegaStructure.FixedPoints
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.CentralSpan


/-!
# The precise layers for Campbell's involution argument

The genuine natural quotient detects every individual displacement:
if [g,v] is central for v in the actual moved module, fixed-point lifting
forces [g,v]=1. The source version constructs the natural model internally
and uses Campbell's literal V.

The paired core-span and Frattini bounds are also recorded without a
noncontainment condition. If F′≤F, its conjugate span is elementary and
centralizes J(O₂(H)); otherwise the proved comparison theorem supplies the
bound. These are the two branches of Campbell II.6.1, and the displacement
statement is the exact II.4.3 consequence used in II.6.2.
Source: Campbell, *Pushing up in Finite Groups* (1979), printed pp.25,29–30.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}
 {F : Type} [Field F] [Finite F] [CharP F 2]

theorem InLocalClass.central_moved_displacement_eq_one (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (g w : H) (hw : w ∈ moved e)
    (hc : ⁅g,w⁆ ∈ center H) : ⁅g,w⁆ = 1 := by
  obtain ⟨q,f,hq,hk,hf,he⟩ := h.exists_campbell_projection hB m
  let v : moved e := ⟨w,hw⟩
  let z := movedConjugate e g v * v⁻¹
  have hz : (z : H)=⁅g,w⁆ := rfl
  have hzker : z ∈ f.ker := by
    rw [h.natural_projection_kernel hB m q hq f hf he]
    exact hc
  have hze : f (movedConjugate e g v)=f v := by
    change f z=1 at hzker
    change f (movedConjugate e g v * v⁻¹)=1 at hzker
    rw [map_mul,map_inv,mul_inv_eq_one] at hzker
    exact hzker
  have hfix := h.natural_projection_fixed_lift hB m q hq hk f hf he g v hze
  have hgw : g*w*g⁻¹=w := congrArg Subtype.val hfix
  change g*w*g⁻¹*w⁻¹=1
  rw [hgw,mul_inv_cancel]

theorem InLocalClass.central_campbell_displacement_eq_one (h : InLocalClass e) (hB : IsBaumannFixed B)
    (g w : H) (hw : w ∈ Campbell.V H) (hc : ⁅g,w⁆ ∈ center H) : ⁅g,w⁆ = 1 := by
  obtain ⟨n,hn,F,_,_,_,hcard,⟨m⟩⟩ := h.natural
  rw [h.campbellV_eq_moved hB m] at hw
  exact InLocalClass.central_moved_displacement_eq_one h hB m g w hw hc

variable {J H' B' : Type*} [Group J] [Group H'] [Finite H'] [Group B'] [Finite B']
  {e' : B' →* H'} {F' : Type} [Field F'] [Finite F'] [CharP F' 2]
theorem InLocalClass.paired_span_core_frattini_all (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hS : (d.sylow : Subgroup H) = e.range) (hS' : (d'.sylow : Subgroup H') = e'.range)
    (hV : d.transfer d' (Campbell.V H') ≤ pCore 2 H) :
    let Y := d.transfer d' (Campbell.F H')
    let Z := d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H'))
    let W := conjugateSpanBy Y (Campbell.J (⊤ : Subgroup H))
    W ≤ Campbell.J (pCore 2 H) ∧ ⁅W,Campbell.J (pCore 2 H)⁆ ≤ Z ∧
      (frattini W).map W.subtype ≤ Z := by
  by_cases hF : d.transfer d' (Campbell.F H') ≤ Campbell.F H
  · let Y := d.transfer d' (Campbell.F H')
    let K := Campbell.J (⊤ : Subgroup H)
    let W := conjugateSpanBy Y K
    let Z := d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H'))
    let : (Campbell.F H).Normal := Campbell.F_normal
    have hWF : W ≤ Campbell.F H := conjugateSpanBy_le hF le_normalizer_of_normal
    have hFR : Campbell.F H ≤ Campbell.J (pCore 2 H) :=
      fun x hx => ((mem_omegaOneCenterAmbient_iff _ x).mp hx).1
    have hFC : Campbell.F H ≤ centralizer (Campbell.J (pCore 2 H) : Set H) :=
      fun x hx => ((mem_omegaOneCenterAmbient_iff _ x).mp hx).2.2
    have hWR := hWF.trans hFR
    have hcomm : ⁅W,Campbell.J (pCore 2 H)⁆ ≤ Z :=
      (commutator_eq_bot_iff_le_centralizer.mpr (hWF.trans hFC)).le.trans bot_le
    let : IsElementaryAbelian 2 (Campbell.F H) := omegaOneCenterAmbient_elementaryAbelian _
    let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_le hF
    have hWQ : W ≤ pCore 2 H := hWF.trans Campbell.F_le_pCore
    have hWp : IsPGroup 2 W := pCore_isPGroup.of_injective (inclusion hWQ) (inclusion_injective hWQ)
    exact ⟨hWR,hcomm,frattini_conjugateSpan_le_of_commutator Y K Z hWp
      ((commutator_mono le_rfl hWR).trans hcomm)⟩
  · exact h.paired_span_core_frattini hB m h' hB' m' d d' hS hS' hV hF

end CFSG.Quasithin.ChapterC.GlaubermanNiles
