module
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.SourceGraph
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.SourceWitness
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.Alignment

/-!
# Source E-alignment from the actual centralizer splitting

The central graph comparison produces a marked z-conjugate outside B if E is
not in R1. The original weak-closure witness excludes it. Consequently the
original E centralizes O²(C_K(t)). Every ambient source premise is discharged;
the concrete marked D8×S4 splitting remains the genuine earlier natural-module
input, with its independent producer retaining final discharge.
Source: Aschbacher--Smith, 13.9.10, printed p.973.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath FusionAlignment
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

/-- All weak-closure inputs are discharged for the original E, from the actual
marked dihedral/S4 splitting supplied by the natural S5 module. -/
theorem terminalFour_le_split_factor
    {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (f g:D8→*G) (X:Subgroup G) (hf:Function.Injective f) (eX:X≃*S4)
    (hfJ:f.range≤m.dihedralBase) (hgJ:g.range≤m.dihedralBase)
    (hft:f (DihedralGroup.r 2)=m.t) (hgt:g (DihedralGroup.r 2)=m.t*m.z)
    (hfg:∀a b,Commute (f a) (g b))
    (hdisj:Disjoint f.range X) (hcomm:f.range≤centralizer (X:Set G))
    (hXK:X≤normalizer (m.B:Set G)) (hVB:X.pCoreIn 2≤m.B)
    (hfusion:∀x∈X.pCoreIn 2,x≠1→IsConj m.t x) : m.terminalFour≤f.range := by
  by_contra hn
  obtain ⟨a,ha,hout⟩:=m.exists_alignment_conjugate f g hf hfJ hgJ hft hgt hfg hn
  exact m.false_of_alignment_split_witness hG a f.range X (MonoidHom.ofInjective hf).symm eX
    hdisj hcomm (hfJ.trans (m.dihedralBase_le_sylow.trans m.sylow_le_normalizer_B)) hXK
    ha hout hVB hfusion

/-- The actual source E centralizes O²(C_K(t)); the quotient/model recognition
needed here is exactly the genuine earlier natural-module splitting. -/
theorem terminalFour_centralizes_normalizer_residual_of_split
    {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (f g:D8→*G) (X:Subgroup G) (hf:Function.Injective f) (eX:X≃*S4)
    (hfJ:f.range≤m.dihedralBase) (hgJ:g.range≤m.dihedralBase)
    (hft:f (DihedralGroup.r 2)=m.t) (hgt:g (DihedralGroup.r 2)=m.t*m.z)
    (hfg:∀a b,Commute (f a) (g b))
    (hdisj:Disjoint f.range X) (hcomm:f.range≤centralizer (X:Set G))
    (hXK:X≤normalizer (m.B:Set G)) (hVB:X.pCoreIn 2≤m.B)
    (hfusion:∀x∈X.pCoreIn 2,x≠1→IsConj m.t x)
    (split:normalizerCentralizer m.B m.t≃*f.range×X)
    (hcoordinates:∀x:normalizerCentralizer m.B m.t,
      (x:G)=((split x).1:G)*((split x).2:G)) :
    m.terminalFour≤centralizer (normalizerCentralizerResidual m.B m.t:Set G) := by
  have hE:=m.terminalFour_le_split_factor hG f g X hf eX hfJ hgJ hft hgt hfg hdisj hcomm hXK hVB hfusion
  have hRp:IsPGroup 2 f.range := (IsPGroup.of_card (by rw [DihedralGroup.nat_card];norm_num : Nat.card D8=2^3)).of_equiv
    (MonoidHom.ofInjective hf)
  exact hE.trans (hcomm.trans (centralizer_le
    (residual_le_second_factor m.B f.range X m.t split hRp hcoordinates)))
end CFSG.Quasithin.Chapter13.Section09.Marking
