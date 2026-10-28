module
public import Theory.SpecificGroups.G2.TernaryLevi
public import Theory.AtlasPort.LinearGroups.G2.LieParabolicCells

/-!
# The entire ternary Borel inside both Atlas endpoints

The positive-root group has order 729 and is Sylow at three. In each full
parabolic its normalizer is exactly the order-2916 Borel. The proof uses
the two Bruhat cells and direct root evaluations to exclude each Weyl
reflection from the normalizer; it works here in characteristic three.
The order-four split torus is Sylow at two inside the whole Borel.

These are the concrete inputs for matching the original I.4.5 middle and
torus under the two already constructed endpoint isomorphisms. No agreement
of their restrictions is assumed or asserted by these model calculations.
Source: Aschbacher–Smith I.4.5, p.417, and F.4.26, p.288. The imported
split-octonion coordinates retain the ATLAS attribution and license in
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section
open Subgroup Atlas.G2 Atlas.G2.Explicit Atlas.G2.LieParabolicSetup Atlas.SplitOctonion
namespace Atlas.G2.TernaryBorel

abbrev U : Subgroup (Model (ZMod 3)) := unipotent
abbrev B : Subgroup (Model (ZMod 3)) := borel
abbrev A : Subgroup (Model (ZMod 3)) := splitTorus
abbrev P (side : Bool) : Subgroup (Model (ZMod 3)) := TernaryLevi.endpoint side

theorem unipotent_card : Nat.card U=729 := by
  rw [card_unipotent]
  norm_num [Nat.card_eq_fintype_card]

theorem borel_card : Nat.card B=2916 := by
  rw [card_borel]
  norm_num [Nat.card_eq_fintype_card]

theorem torus_card : Nat.card A=4 := by
  rw [card_splitTorus]
  norm_num [Nat.card_eq_fintype_card]

theorem borel_le_endpoint (side : Bool) : B≤P side := by
  cases side
  · exact borel_le_parabolic₁
  · exact borel_le_parabolic₂

theorem borel_normalizes : B≤normalizer (U:Set (Model (ZMod 3))) :=
  sup_le U.le_normalizer (le_normalizer_iff.mpr (fun _ ht _ hu => torus_normalizes_unipotent ht hu))

private theorem short_weyl_not_normalizes :
    (weylS:Model (ZMod 3))∉normalizer (U:Set (Model (ZMod 3))) := by
  intro h
  have hF : (rootF 1:Model (ZMod 3))∈U := subset_closure (by simp)
  have hconj := (mem_normalizer_iff.mp h (rootF 1)).mp hF
  have hp := parabolic_le_pointStabilizer
    (borel_le_parabolic₂ (show weylS*rootF 1*weylS⁻¹∈B from mem_sup_left hconj))
  obtain ⟨a,ha⟩ := (mem_pointStabilizer_iff _).mp hp
  have hh := congrFun ha 1
  norm_num [weylS,weylSEquiv,weylSLinear,weylSApply,
    rootF,rootFEquiv,rootFLinear,rootFApply,basisVector,Units.smul_def] at hh

private theorem long_weyl_not_normalizes :
    (weylR:Model (ZMod 3))∉normalizer (U:Set (Model (ZMod 3))) := by
  intro h
  have hE : (rootE 1:Model (ZMod 3))∈U := subset_closure (by simp)
  have hconj := (mem_normalizer_iff.mp h (rootE 1)).mp hE
  have hp := borel_le_shortPlaneStabilizer (show weylR*rootE 1*weylR⁻¹∈B from mem_sup_left hconj)
  have hh := hp.1 (basisVector 1) (basis_mem_shortPlane 1 (by decide)) 2 (by decide)
  have hev : (weylR*rootE 1*weylR⁻¹:Model (ZMod 3)).val (basisVector 1) 2 = -1 := by
    decide +kernel
  rw [hev] at hh
  norm_num at hh

theorem endpoint_inf_normalizer (side : Bool) :
    P side ⊓ normalizer (U:Set (Model (ZMod 3)))=B := by
  apply le_antisymm _ (le_inf (borel_le_endpoint side) borel_normalizes)
  rintro g ⟨hg,hn⟩
  cases side
  · rcases ParabolicCells.short_cells g hg with hb | ⟨a,b,hb,he⟩
    · exact hb
    · exfalso
      apply short_weyl_not_normalizes
      have ha : (rootF a:Model (ZMod 3))∈B := mem_sup_left (subset_closure (by simp))
      have hh := (normalizer (U:Set (Model (ZMod 3)))).mul_mem
        ((normalizer (U:Set (Model (ZMod 3)))).mul_mem
          (inv_mem (borel_normalizes ha)) hn) (inv_mem (borel_normalizes hb))
      rw [he] at hh
      simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hh
  · rcases ParabolicCells.long_cells g hg with hb | ⟨a,ha,b,hb,he⟩
    · exact hb
    · exfalso
      apply long_weyl_not_normalizes
      have hh := (normalizer (U:Set (Model (ZMod 3)))).mul_mem
        ((normalizer (U:Set (Model (ZMod 3)))).mul_mem
          (inv_mem (borel_normalizes ha)) hn) (inv_mem (borel_normalizes hb))
      rw [he] at hh
      simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hh

noncomputable def sylow : Sylow 3 (Model (ZMod 3)) :=
  (IsPGroup.of_card (p:=3) (n:=6) unipotent_card).toSylow
    (by rw [unipotent_index]; norm_num [Nat.card_eq_fintype_card])

@[simp] theorem sylow_coe : (sylow:Subgroup (Model (ZMod 3)))=U := rfl

noncomputable def endpointSylow (side : Bool) : Sylow 3 (P side) :=
  sylow.subtype ((show U≤B from le_sup_left).trans (borel_le_endpoint side))

@[simp] theorem endpointSylow_coe (side : Bool) :
    (endpointSylow side:Subgroup (P side))=U.subgroupOf (P side) := rfl

theorem endpointSylow_normalizer (side : Bool) :
    normalizer (endpointSylow side:Set (P side))=B.subgroupOf (P side) := by
  rw [show (endpointSylow side:Set (P side))=(U.subgroupOf (P side):Set (P side)) from rfl,
    ←subgroupOf_normalizer_eq ((show U≤B from le_sup_left).trans (borel_le_endpoint side))]
  rw [←endpoint_inf_normalizer side,inf_subgroupOf_left]

/-- The split torus is the full Sylow two-subgroup of the ternary Borel. -/
noncomputable def torusSylow : Sylow 2 B := by
  have hc : Nat.card (A.subgroupOf B)=4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show A≤B from le_sup_right)).toEquiv,torus_card]
  apply (IsPGroup.of_card (p:=2) (n:=2) hc).toSylow
  have hh := (A.subgroupOf B).card_mul_index
  rw [hc,borel_card] at hh
  have hi : (A.subgroupOf B).index=729 := by omega
  rw [hi]
  decide

@[simp] theorem torusSylow_coe : (torusSylow:Subgroup B)=A.subgroupOf B := rfl

end Atlas.G2.TernaryBorel
