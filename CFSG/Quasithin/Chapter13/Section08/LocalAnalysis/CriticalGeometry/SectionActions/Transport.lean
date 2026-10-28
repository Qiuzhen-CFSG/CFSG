module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.SectionActions.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Endpoint

/-!
# Transport at the genuine critical-pair endpoint

The inverse of the chosen endpoint conjugator gives the group and binary
linear equivalences Vγ/Uγ ≃ VH/UH and Uγ/A₁ ≃ UH/V₁. Their intertwining
identities use actual quotient conjugation on both sides. The second action
factors through the literal H/O₂(H) using the explicit earlier core bound.

For 13.8.18(4), an axis action descends to Uγ/A₁. Strict D_H<U_H forces
some quotient actor to remain nonidentity; endpoint transport gives a forbidden
transvection in the actual H* action. This proves the independent implication,
without assuming the conclusion of 13.8.18 or reorientation.

Earlier inputs are the F.9 normalization of V₁, the bound [UH,O₂(H)]≤V₁,
UH≤Gγ, and the strict denominator supplied by 13.8.8. Elementary abelianness
at γ is inherited by conjugation from that at H.

Source: Aschbacher–Smith 13.8.9, 13.8.11 and 13.8.18, combined manuscript
(1 March 2004), printed pp.949–950 and 953.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.SectionActions
variable {G : Type*} [Group G]

noncomputable def vAction (H V V₃ : Subgroup G) [IsElementaryAbelian 2 (Source.VH H V)] :
    H →* MulAut (Source.Vsection H V V₃) :=
  quotientAction H (Source.VH H V) (Source.UH H V₃)
    (le_normalizer_conjugateSpanBy V H) (le_normalizer_conjugateSpanBy V₃ H)

noncomputable def uAction (H V₃ V₁ : Subgroup G) [IsElementaryAbelian 2 (Source.UH H V₃)]
    (hz : H ≤ normalizer (V₁ : Set G)) : H →* MulAut (Source.Utilde H V₃ V₁) :=
  quotientAction H (Source.UH H V₃) V₁ (le_normalizer_conjugateSpanBy V₃ H) hz

/-- The actual H-action factors through the actual H/O₂(H). -/
noncomputable def uStarAction (H V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (hz : H ≤ normalizer (V₁ : Set G)) (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁) :
    Source.Hstar H →* MulAut (Source.Utilde H V₃ V₁) :=
  QuotientGroup.lift (pCore 2 H) (uAction H V₃ V₁ hz) (by
    have hk := quotient_conjugation_action_kills_commutator_layer
      H (Source.UH H V₃) V₁ (Source.QH H) inferInstance
      (le_normalizer_conjugateSpanBy V₃ H) hQ (uAction H V₃ V₁ hz)
      (quotientAction_apply H (Source.UH H V₃) V₁ _ hz)
    intro q hq
    exact hk (mem_map_of_mem H.subtype hq))

theorem uStarAction_mk (H V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (hz : H ≤ normalizer (V₁ : Set G)) (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁)
    (h : H) : uStarAction H V₃ V₁ hz hQ (QuotientGroup.mk' (pCore 2 H) h) =
      uAction H V₃ V₁ hz h := QuotientGroup.lift_mk _ _ h

namespace CriticalPair
variable {L T H V : Subgroup G} (c : CriticalPair L T H V)

def returnActor (P : Subgroup G) (hPJ : P ≤ vertexGroup L T H c.gamma) (p : P) : H :=
  ((MulAut.conj (c.gb : G)).subgroupMap H).symm
    ⟨p, by
      change (p : G) ∈ H.map (MulAut.conj (c.gb : G)).toMonoidHom
      rw [← c.vertexGroup_gamma]
      exact hPJ p.property⟩

theorem returnActor_conj (P : Subgroup G) (hPJ : P ≤ vertexGroup L T H c.gamma) (p : P) :
    MulAut.conj (c.gb : G) (returnActor c P hPJ p : G) = (p : G) :=
  congrArg Subtype.val (((MulAut.conj (c.gb : G)).subgroupMap H).apply_symm_apply _)

theorem normalizes_Aone (V₁ : Subgroup G) (hz : H ≤ normalizer (V₁ : Set G)) :
    vertexGroup L T H c.gamma ≤ normalizer (c.Aone V₁ : Set G) := by
  apply le_normalizer_iff_commutator_le_left.mpr
  rw [c.vertexGroup_gamma, CriticalGeometry.CriticalPair.Aone, ← map_commutator]
  exact map_mono (le_normalizer_iff_commutator_le_left.mp hz)

/-- Endpoint conjugation identifies Vγ/Uγ with VH/UH. -/
def vSectionEquiv (V₃ : Subgroup G)
    [IsElementaryAbelian 2 (Source.VH H V)] [IsElementaryAbelian 2 c.Vgamma] :
    (c.Vgamma ⧸ (c.Ugamma V₃).subgroupOf c.Vgamma) ≃* Source.Vsection H V V₃ :=
  (sectionEquiv (MulAut.conj (c.gb : G)) (Source.VH H V) (Source.UH H V₃)).symm

/-- The other endpoint quotient is Uγ/A₁, with the conjugate denominator. -/
def uSectionEquiv (V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (c.Ugamma V₃)] :
    (c.Ugamma V₃ ⧸ (c.Aone V₁).subgroupOf (c.Ugamma V₃)) ≃* Source.Utilde H V₃ V₁ :=
  (sectionEquiv (MulAut.conj (c.gb : G)) (Source.UH H V₃) V₁).symm

def vLinearEquiv (V₃ : Subgroup G)
    [IsElementaryAbelian 2 (Source.VH H V)] [IsElementaryAbelian 2 c.Vgamma] :
    Additive (c.Vgamma ⧸ (c.Ugamma V₃).subgroupOf c.Vgamma) ≃ₗ[ZMod 2]
      Additive (Source.Vsection H V V₃) := binaryEquiv (vSectionEquiv c V₃)

def uLinearEquiv (V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (c.Ugamma V₃)] :
    Additive (c.Ugamma V₃ ⧸ (c.Aone V₁).subgroupOf (c.Ugamma V₃)) ≃ₗ[ZMod 2]
      Additive (Source.Utilde H V₃ V₁) := binaryEquiv (uSectionEquiv c V₃ V₁)

theorem vSectionEquiv_intertwines (V₃ P : Subgroup G)
    [IsElementaryAbelian 2 (Source.VH H V)] [IsElementaryAbelian 2 c.Vgamma]
    (hPJ : P ≤ vertexGroup L T H c.gamma) (p : P)
    (w : c.Vgamma ⧸ (c.Ugamma V₃).subgroupOf c.Vgamma) :
    vSectionEquiv c V₃ (quotientAction P c.Vgamma (c.Ugamma V₃)
      (hPJ.trans (c.normalizes_Ugamma V)) (hPJ.trans (c.normalizes_Ugamma V₃)) p w) =
      vAction H V V₃ (returnActor c P hPJ p) (vSectionEquiv c V₃ w) := by
  let e := sectionEquiv (MulAut.conj (c.gb : G)) (Source.VH H V) (Source.UH H V₃)
  have hi := sectionEquiv_intertwines_actor (MulAut.conj (c.gb : G)) H P
    (Source.VH H V) (Source.UH H V₃) (le_normalizer_conjugateSpanBy V H)
    (le_normalizer_conjugateSpanBy V₃ H) (hPJ.trans (c.normalizes_Ugamma V))
    (hPJ.trans (c.normalizes_Ugamma V₃)) (returnActor c P hPJ p) p
    (returnActor_conj c P hPJ p) (e.symm w)
  apply e.symm_apply_eq.mpr
  exact (congrArg (quotientAction P c.Vgamma (c.Ugamma V₃)
    (hPJ.trans (c.normalizes_Ugamma V)) (hPJ.trans (c.normalizes_Ugamma V₃)) p)
    (e.apply_symm_apply w).symm).trans hi.symm

theorem uSectionEquiv_intertwines (V₃ V₁ P : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (c.Ugamma V₃)]
    (hz : H ≤ normalizer (V₁ : Set G))
    (hPJ : P ≤ vertexGroup L T H c.gamma) (p : P)
    (w : c.Ugamma V₃ ⧸ (c.Aone V₁).subgroupOf (c.Ugamma V₃)) :
    uSectionEquiv c V₃ V₁ (quotientAction P (c.Ugamma V₃) (c.Aone V₁)
      (hPJ.trans (c.normalizes_Ugamma V₃)) (hPJ.trans (normalizes_Aone c V₁ hz)) p w) =
      uAction H V₃ V₁ hz (returnActor c P hPJ p) (uSectionEquiv c V₃ V₁ w) := by
  let e := sectionEquiv (MulAut.conj (c.gb : G)) (Source.UH H V₃) V₁
  have hi := sectionEquiv_intertwines_actor (MulAut.conj (c.gb : G)) H P
    (Source.UH H V₃) V₁ (le_normalizer_conjugateSpanBy V₃ H) hz
    (hPJ.trans (c.normalizes_Ugamma V₃)) (hPJ.trans (normalizes_Aone c V₁ hz))
    (returnActor c P hPJ p) p (returnActor_conj c P hPJ p) (e.symm w)
  apply e.symm_apply_eq.mpr
  exact (congrArg (quotientAction P (c.Ugamma V₃) (c.Aone V₁)
    (hPJ.trans (c.normalizes_Ugamma V₃)) (hPJ.trans (normalizes_Aone c V₁ hz)) p)
    (e.apply_symm_apply w).symm).trans hi.symm

/-- Nonidentity transvections on the endpoint section are actual H-elements. -/
theorem v_transport_nonidentity (V₃ P : Subgroup G)
    [IsElementaryAbelian 2 (Source.VH H V)] [IsElementaryAbelian 2 c.Vgamma]
    (hPJ : P ≤ vertexGroup L T H c.gamma) (p : P)
    (hn : quotientAction P c.Vgamma (c.Ugamma V₃)
      (hPJ.trans (c.normalizes_Ugamma V)) (hPJ.trans (c.normalizes_Ugamma V₃)) p ≠ 1)
    (ht : binaryLinear (quotientAction P c.Vgamma (c.Ugamma V₃)
      (hPJ.trans (c.normalizes_Ugamma V)) (hPJ.trans (c.normalizes_Ugamma V₃)) p) ∈
      LinearEquiv.transvections (ZMod 2) (Additive (c.Vgamma ⧸ (c.Ugamma V₃).subgroupOf c.Vgamma))) :
    ∃ h : H, vAction H V V₃ h ≠ 1 ∧ binaryLinear (vAction H V V₃ h) ∈
      LinearEquiv.transvections (ZMod 2) (Additive (Source.Vsection H V V₃)) := by
  exact ⟨returnActor c P hPJ p, transport_nonidentity (vSectionEquiv c V₃) _ _
    (vSectionEquiv_intertwines c V₃ P hPJ p) hn ht⟩

end CriticalPair
end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.SectionActions

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.SectionActions.CriticalPair
variable {G : Type*} [Group G] {L T H V : Subgroup G} (c : CriticalPair L T H V)

/-- The independent action implication used in 13.8.18(4). -/
theorem no_axis_of_no_uStar_transvection (V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (c.Ugamma V₃)]
    (hz : H ≤ normalizer (V₁ : Set G))
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁)
    (hUJ : Source.UH H V₃ ≤ vertexGroup L T H c.gamma)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hno : ∀ h : Source.Hstar H, uStarAction H V₃ V₁ hz hQ h ≠ 1 →
      binaryLinear (uStarAction H V₃ V₁ hz hQ h) ∉
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ V₁))) :
    ¬ HasTransvectionAxis (Source.UH H V₃) (c.Ugamma V₃)
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁)
      (hUJ.trans (c.normalizes_Ugamma V₃)) := by
  intro haxis
  let P := Source.UH H V₃
  let U := c.Ugamma V₃
  let Z := c.Aone V₁
  let hn := hUJ.trans (c.normalizes_Ugamma V₃)
  let hnz := hUJ.trans (normalizes_Aone c V₁ hz)
  let a := quotientAction P U Z hn hnz
  have hex : ∃ p : P, a p ≠ 1 := by
    by_contra hh
    have hall : ∀ p, a p = 1 := by simpa only [not_exists, not_not] using hh
    have hb := (quotientAction_all_eq_one_iff P U Z hn hnz).mp hall
    exact hDH.not_ge (le_commutatorPreimage le_rfl hb)
  obtain ⟨p, hp⟩ := hex
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  have hi (w : Additive U) : binaryMap q (binaryLinear (conjugationAction P U hn p) w) =
      binaryLinear (a p) (binaryMap q w) := by
    change q (conjugationAction P U hn p w.toMul) = a p (q w.toMul)
    rw [quotientAction_apply]
    rfl
  have ht := transvection_of_surjective_intertwiner (binaryMap q)
    (QuotientGroup.mk'_surjective (Z.subgroupOf U))
    (binaryLinear (conjugationAction P U hn p)) (binaryLinear (a p)) hi (haxis.2.2 p)
  have htransport := transport_nonidentity (uSectionEquiv c V₃ V₁) (a p)
    (uAction H V₃ V₁ hz (returnActor c P hUJ p))
    (uSectionEquiv_intertwines c V₃ V₁ P hz hUJ p) hp ht
  have hbad := hno (QuotientGroup.mk' (pCore 2 H) (returnActor c P hUJ p))
  rw [uStarAction_mk] at hbad
  exact hbad htransport.1 htransport.2

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.SectionActions.CriticalPair

end
