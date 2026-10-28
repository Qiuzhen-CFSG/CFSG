module

public import CFSG.Quasithin.Chapter13.Section08.LinearFour.RankOneModels
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SectionDisplacement
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# G.6.4 on the literal sections in the linear-four endgame

Let S/E be a faithful irreducible binary H/O₂(H)-section inside H_C/V_H.
The source index |Uγ : Uγ ∩ Q_H| = 2 supplies an element of Uγ outside
Q_H. Its image under the canonical quotient map is a nonidentity involution.
The actual commutator and intersection bounds give displacement rank at
most one on S/E; faithfulness makes this rank exactly one. Irreducibility
supplies generation, and quotienting by O₂(H) supplies the trivial two-core.
The full known-simple G.6.4 then identifies the section with the marked
natural binary four-space.

The final theorem obtains the commutator bound from the existing source
centralizer calculation, so it takes no G.6.4, transvection, generation or
model-classification callback. It retains the earlier local index and
geometry inputs, including those of 13.8.32, and the faithful irreducible
section. It does not assume H_C/V_H is elementary abelian. Constructing the
chief sections, proving that at most one is noncentral, and discharging the
13.8.29–32 inputs remain necessary for Theorem 13.8.28.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), proof of 13.8.28, printed pp.965–966.
-/

public section
open Subgroup Representation
open BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open ChapterG.Section06
universe u v
variable {G : Type u} [Group G] [Finite G]
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

/-- The actual two-core quotient and a source binary section supply a marked
four-dimensional model from the order-two commutator-image bound. -/
theorem section_four_model
    (H QH HC VH Uγ S E : Subgroup G)
    [IsElementaryAbelian 2 Uγ]
    (hQH : QH = H.pCoreIn 2)
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    [IsIrreducible σ] (hf : Function.Injective σ)
    (d : BinaryConjugationSection H S E (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hVE : VH ≤ E) (hSC : S ≤ HC) (hCQ : HC ≤ QH)
    (hU : Nat.card Uγ = 32) (hstar : QH.relIndex Uγ = 2)
    (hintersection : 8 ≤ Nat.card (Uγ ⊓ VH : Subgroup G))
    (hcomm : ⁅HC, Uγ⁆ ≤ HC ⊓ Uγ) (hUH : Uγ ≤ H)
    (hcover : IsSQTK KnownSimple.IsKnownSimple H)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4) :
    HasModelOn σ ⊤ ⊤ (binaryLinearAction 4) ∧ Module.finrank (ZMod 2) W = 4 := by
  let : Finite W := Finite.of_surjective
    (fun s : S => (d.coordinates s).toAdd) (fun w => d.onto (Multiplicative.ofAdd w))
  have hnot : ¬ Uγ ≤ QH := by
    intro hu
    have hi : QH.relIndex Uγ = 1 := relIndex_eq_one.mpr hu
    omega
  obtain ⟨a, ha, hna⟩ := SetLike.not_le_iff_exists.mp hnot
  let aH : H := ⟨a, hUH ha⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  have hna' : q aH ≠ 1 := by
    intro hz
    have hm : aH ∈ pCore 2 H := (QuotientGroup.eq_one_iff aH).mp hz
    apply hna
    rw [hQH]
    exact mem_map_of_mem H.subtype hm
  have ha2 : (q aH) ^ 2 = 1 := by
    rw [← map_pow]
    have he : aH ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian a ha)
    rw [he, map_one]
  have hr := section_displacement_le_one d Uγ HC VH QH hVE hSC hCQ hU hstar
    hintersection hcomm hUH aH ha
  have hm : HasModelOn σ ⊤ ⊤ (binaryLinearAction 4) :=
    irreducible_linearFour_model q (QuotientGroup.mk'_surjective _) hcover
      (pCore_quotient_pCore_eq_bot 2) hf e ha2 hna' hr
  refine ⟨hm, ?_⟩
  obtain ⟨_, eW, _, _⟩ := hm
  have hd := (Submodule.topEquiv.symm.trans eW).finrank_eq
  simpa only [Module.finrank_fin_fun] using hd

/-- Apply the source centralizer chain and full G.6.4 to the same H_C/V_H
section. The earlier source geometry remains explicit. -/
theorem source_final_section_four_model
    (H Q QH HC V3 V VH R A1 Uγ Gγ S E : Subgroup G)
    [IsElementaryAbelian 2 Uγ]
    (hQH : QH = H.pCoreIn 2)
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    [IsIrreducible σ] (hf : Function.Injective σ)
    (d : BinaryConjugationSection H S E (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hVE : VH ≤ E) (hSC : S ≤ HC)
    (hQR : QH ≤ R) (hindex : Q.relIndex R = 4)
    (hcent : Q ⊓ QH ≤ centralizer (V3 : Set G))
    (hdual : (QH ⊓ centralizer (V3 : Set G)).relIndex QH = 4)
    (hHCQH : HC ≤ QH) (hHCV3 : HC ≤ centralizer (V3 : Set G))
    (hHHC : H ≤ normalizer (HC : Set G))
    (hQV : Q ≤ centralizer (V : Set G))
    (hVH : VH = conjugateSpanBy V H) (hA1 : A1 ≤ VH)
    (hGγ : Gγ = centralizer (A1 : Set G))
    (hGγUγ : Gγ ≤ normalizer (Uγ : Set G)) (hUγH : Uγ ≤ H)
    (hU : Nat.card Uγ = 32) (hstar : QH.relIndex Uγ = 2)
    (hintersection : 8 ≤ Nat.card (Uγ ⊓ VH : Subgroup G))
    (hcover : IsSQTK KnownSimple.IsKnownSimple H)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4) :
    HasModelOn σ ⊤ ⊤ (binaryLinearAction 4) ∧ Module.finrank (ZMod 2) W = 4 := by
  obtain ⟨_, _, _, hc⟩ := final_centralizer_chain H Q QH HC V3 V VH R A1 Uγ Gγ
    hQR hindex hcent hdual hHCQH hHCV3 hHHC hQV hVH hA1 hGγ hGγUγ hUγH
  exact section_four_model H QH HC VH Uγ S E hQH σ hf d hVE hSC hHCQH
    hU hstar hintersection hc hUγH hcover e

end CFSG.Quasithin.Chapter13.Section08.LinearFour
