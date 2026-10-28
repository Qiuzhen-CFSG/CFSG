module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureFullActor
import Theory.Frattini.PGroup

/-!
# The whole original central closure is elementary abelian

The full action on W/<z> is transitive on its nonzero vectors. The original
four-group V1 contains an involution representing the distinguished quotient
point. Thus every element of W outside <z> differs from a conjugate of that
involution by an element of the central group <z>. Both factors square to
one and commute. Every element of the original W consequently squares to
one, so W is elementary abelian and its Frattini subgroup is trivial.

Source: Aschbacher--Smith12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Elementary abelianness of the whole original W, with its literal
central closure and the original inner-automizer hypotheses unchanged. -/
theorem original_tripleSix_central_closure_elementary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (hinner : inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K) :
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))
    IsElementaryAbelian 2 W ∧ frattini W=⊥ := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let Z := zpowers (z:G)
  obtain ⟨hHW,hZN,hrest⟩ := original_tripleSix_central_closure_full_actor
    h structural D a z hz hzT hnot hinner
  let : (Z.subgroupOf W).Normal := hZN
  obtain ⟨he,φ,hformula,_,_,_,x,hx,hpoint,horbit,_,_,hfull,hdecomp,hlocal,_,hone,_,_,_,_⟩ := hrest
  let := he
  let q := QuotientGroup.mk' (Z.subgroupOf W)
  have hp := tripleSixPoint_properties D a z hz
  let : IsElementaryAbelian 2 V1 := hp.2.2.2.1
  let : IsElementaryAbelian 2 U := D.elementary
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.zpowers_of_pow_eq_one
    (elemPow_eq_one_of_isElementaryAbelian (z:G) z.property)
  have hZV : Z≤V1 := zpowers_le.mpr hp.1
  have hVW : V1≤W := le_conjugateSpanBy V1 R
  have hZW : Z≤W := hZV.trans hVW
  have hHC : H≤C :=
    (original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot).1
  have hWH : W≤H := (conjugateSpanBy_le_self
    (hp.2.1.trans (le_conjugateSpanBy U C))).trans (le_sup_left.trans le_sup_left)
  have hZC : Z≤centralizer (W : Set G) := zpowers_le.mpr (mem_centralizer_iff.mpr (by
    intro w hw
    exact mem_centralizer_singleton_iff.mp (hHC (hWH hw))))
  have hxV : x.toMul∈(V1.subgroupOf W).map q := by
    have hh := hpoint ▸ Submodule.mem_span_singleton_self x
    exact hh
  obtain ⟨v,hv,hvx⟩ := hxV
  have hv2 : (v:G)^2=1 := elemPow_eq_one_of_isElementaryAbelian (v:G) (show (v:G)∈V1 from hv)
  have hspan : Submodule.span (ZMod 2) (MulAction.orbit φ.range x)=⊤ := by
    have heq : MulAction.orbit φ.range x=Set.range (fun g : φ.range => g.val x) := by
      ext y
      exact MulAction.mem_orbit_iff
    rwa [heq]
  obtain ⟨hspaces,_,_⟩ := ChapterG.Section03.spanning_one_block_actor hfull hdecomp hspan hone
  let i : ChapterG.Section03.OrbitBlock φ.range (MulAction.orbit φ.range x) :=
    ⟨MulAction.orbit (BinaryTransvectionGroups.generated φ.range (MulAction.orbit φ.range x)) x,
      x,MulAction.mem_orbit_self x,rfl⟩
  have hsq (w : W) : w^2=1 := by
    let y := Additive.ofMul (q w)
    by_cases hy : y=0
    · apply Subtype.ext
      have hwZ : (w:G)∈Z := (QuotientGroup.eq_one_iff w).mp hy
      exact elemPow_eq_one_of_isElementaryAbelian (w:G) hwZ
    · have hyi : y∈i.val := by
        rw [hlocal.all_points i]
        exact ⟨(hspaces i).symm ▸ Submodule.mem_top,hy⟩
      obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp hyi
      obtain ⟨b,hb⟩ := BinaryTransvectionGroups.generated_le φ.range
        (MulAction.orbit φ.range x) g.property
      let c : W := ⟨(b:G)*(v:G)*(b:G)⁻¹,
        (mem_normalizer_iff.mp (hHW b.property) v).mp v.property⟩
      have hcq : q c=q w := by
        apply Additive.ofMul.injective
        calc
          Additive.ofMul (q c)=φ b (Additive.ofMul (q v)) := (hformula b v).symm
          _ = φ b x := by rw [hvx]; rfl
          _ = y := by rw [hb]; exact hg
      have hc2 : (c:G)^2=1 := by
        change ((b:G)*(v:G)*(b:G)⁻¹)^2=1
        rw [conj_pow,hv2,mul_one,mul_inv_cancel]
      have hd : w/c∈Z.subgroupOf W :=
        (QuotientGroup.eq_iff_div_mem (N := Z.subgroupOf W)).mp hcq.symm
      have hdZ : ((w / c : W):G)∈Z := hd
      have hd2 : (((w / c : W):G))^2=1 :=
        elemPow_eq_one_of_isElementaryAbelian _ hdZ
      have hdc : Commute (((w / c : W):G)) (c:G) := (hZC hdZ c c.property).symm
      apply Subtype.ext
      change (w:G)^2=1
      have hprod := hdc.mul_pow 2
      rw [hd2,hc2,one_mul] at hprod
      simpa only [coe_div,div_mul_cancel] using hprod
  have hinv (w : W) : w⁻¹=w := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hsq w)
  let : IsMulCommutative W := ⟨⟨fun v w => by simpa only [hinv] using mul_inv_rev v w⟩⟩
  let hW : IsElementaryAbelian 2 W :=
    { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }
  let : Fact (IsPGroup 2 W) := ⟨IsElementaryAbelian.isPGroup 2 W⟩
  exact ⟨hW,frattini_eq_bot_of_isElementaryAbelian (p := 2)⟩

end CFSG.Quasithin.Chapter12.Section07
