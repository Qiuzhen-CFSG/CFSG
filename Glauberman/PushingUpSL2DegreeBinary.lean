module
public import Glauberman.PushingUpSL2DegreeTwoStepFactors
public import Theory.Representation.SL2.NaturalExtensionSection

/-!
# Characteristic-two exclusion of the Niles class-three branch

The literal reduced core modulo the full ambient center is elementary,
with two marked natural factors and a fixed subgroup of relative order q².
The binary natural-extension theorem makes its Sylow action quadratic.
An elementary interval supplements the core, so the Sylow third commutator
is ambient central. Its characteristic normal exclusion makes it trivial,
contradicting class three. The original power reduction consequently gives
class at most two at every original nonbinary field degree.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 3.4, pp.37--39,
Theorem 6.9, p.58. The original F₀/Baumann consumer and central-kernel lift
are in `NonbinarySymplectic.CriticalReduction.RootProductNilesBinary`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport Representation
open scoped MatrixGroups IsMulCommutative
namespace Glauberman
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
local instance binaryExclusionAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

private theorem class_two_of_central_triple
    (S : Sylow 2 G) (Q E : Subgroup G) [Q.Normal]
    (hgen : Q ⊔ E = (S : Subgroup G)) (hE : IsMulCommutative E)
    (htriple : ⁅⁅Q,(S : Subgroup G)⁆,(S : Subgroup G)⁆ ≤ center G)
    (hno : NoCharacteristicNormal (S : Subgroup G)) :
    (S : Subgroup G).lowerCentralSeries 2 = ⊥ := by
  have hQS : Q ≤ (S : Subgroup G) := le_sup_left.trans hgen.le
  have hES : E ≤ (S : Subgroup G) := le_sup_right.trans hgen.le
  have hn : (S : Subgroup G) ≤ normalizer ((⁅Q,(S : Subgroup G)⁆ : Subgroup G) : Set G) :=
    normalizer_commutator_ge_right _ _
  have hEE : ⁅E,E⁆ = ⊥ := commutator_self_eq_bot_iff.mpr hE
  have hcommE : ⁅E,(S : Subgroup G)⁆ ≤ ⁅Q,(S : Subgroup G)⁆ := by
    rw [commutator_comm]
    have hh := commutator_sup_le_of_relative_normal (S : Subgroup G) Q E E
      ⁅Q,(S : Subgroup G)⁆ hn hQS hES (commutator_mono le_rfl hES)
      (hEE.le.trans bot_le)
    rwa [hgen] at hh
  have hcomm : ⁅(S : Subgroup G),(S : Subgroup G)⁆ ≤ ⁅Q,(S : Subgroup G)⁆ := by
    have hh := commutator_sup_le_of_relative_normal (S : Subgroup G) Q E (S : Subgroup G)
      ⁅Q,(S : Subgroup G)⁆ hn hQS hES le_rfl hcommE
    rwa [hgen] at hh
  have hclass : (S : Subgroup G).lowerCentralSeries 2 ≤ center G := by
    simp only [Subgroup.lowerCentralSeries_succ,Subgroup.lowerCentralSeries_zero]
    exact (commutator_mono hcomm le_rfl).trans htriple
  have hb := characteristic_eq_bot_of_residual_centralizes S hno (center G)
    (le_centralizer_iff.mpr (center_le_centralizer _))
    ((⊤ : Subgroup S).lowerCentralSeries 2) (by
      rw [top_subtype_lowerCentralSeries]
      exact hclass)
  rw [←top_subtype_lowerCentralSeries,hb,Subgroup.map_bot]

/-- Characteristic two excludes the literal reduced class-three diagram. -/
theorem sl2_no_two_step_class_three
    (e : (G ⧸ pCore 2 G) ≃* SL(2,F)) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) (g : G)
    (hgen : (S : Subgroup G) ⊔ (S : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊤)
    (hinter : (S : Subgroup G) ⊓ (S : Subgroup G).map (MulAut.conj g).toMonoidHom = pCore 2 G)
    (hd : NilesTwoStepDiagram (Nat.card F) (S : Subgroup G) α g)
    (hclass : Group.nilpotencyClass ((S : Subgroup G).map (MulAut.conj g).toMonoidHom) = 3) :
    False := by
  let T := S.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  let φ := twistedConjugacy (S : Subgroup G) α g
  let X := intervalDiagram φ 6
  let _ := T.isPGroup'.isNilpotent
  have hne : (T : Subgroup G).lowerCentralSeries 2 ≠ ⊥ := by
    intro hh
    have ht : (⊤ : Subgroup T).lowerCentralSeries 2 = ⊥ := by
      apply map_injective (f := (T : Subgroup G).subtype) (Subtype.val_injective)
      rw [top_subtype_lowerCentralSeries,Subgroup.map_bot]
      exact hh
    have hc := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp ht
    change Group.nilpotencyClass ((S : Subgroup G).map (MulAut.conj g).toMonoidHom) ≤ 2 at hc
    omega
  have hnc : ¬ ⁅(T : Subgroup G),(T : Subgroup G)⁆ ≤ centerIn (T : Subgroup G) := by
    intro hh
    apply hne
    simp only [Subgroup.lowerCentralSeries_succ,Subgroup.lowerCentralSeries_zero]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hh.trans inf_le_right)
  have hfull := sl2_two_step_full_diagram e hn hF S α hfit hno g hgen hinter hd
  obtain ⟨⟨cV⟩,⟨cQ⟩⟩ := sl2_two_step_natural_factors e hn hF S α hfit hno g hgen hinter hfull hnc
  obtain ⟨_,helem,_,_,_,_⟩ := two_step_core_sections φ hfull hinter
  obtain ⟨hDQ,hSD,hi,hgenS⟩ := two_step_left_fixed_section φ hfull hinter
  let _ := helem
  let Q := pCore 2 G
  let Z := center G
  let V := centerIn Q
  obtain ⟨_,_,hshort,_,_,_,hzq,hzg,_⟩ := hfull
  change V = X 2 4 at hzq
  change Z = X 3 3 at hzg
  have hzv : Z ≤ V := by
    rw [hzg,hzq]
    exact intervalDiagram_mono φ (by decide) (by decide)
  let qQ := (QuotientGroup.mk' Z).comp Q.subtype
  have hkQ : qQ.ker = Z.subgroupOf Q := by
    ext x
    exact QuotientGroup.eq_one_iff x.val
  have hrQ : qQ.range = Q.map (QuotientGroup.mk' Z) := by
    rw [MonoidHom.range_comp,range_subtype]
  let E₀ : (Q ⧸ Z.subgroupOf Q) ≃* Q.map (QuotientGroup.mk' Z) :=
    (QuotientGroup.quotientMulEquivOfEq hkQ.symm).trans
      ((QuotientGroup.quotientKerEquivRange qQ).trans (MulEquiv.subgroupCongr hrQ))
  let : IsElementaryAbelian 2 (Q ⧸ Z.subgroupOf Q) :=
    IsElementaryAbelian.of_injective E₀.toMonoidHom E₀.injective
  let f := e.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = Q := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have htriple := Representation.SL2.triple_commutator_le_of_natural_factors
    Q V Z inf_le_left hzv f hf hk cV cQ hn hF S (X 1 3) hDQ hSD hi
  have he : IsElementaryAbelian 2 (X 0 3) := hshort 0 3 (by decide) (by decide)
  let _ := he
  have hc := class_two_of_central_triple S Q (X 0 3) hgenS inferInstance htriple hno.noCharacteristicNormal
  apply hne
  change ((S : Subgroup G).map (MulAut.conj g).toMonoidHom).lowerCentralSeries 2 = ⊥
  rw [←Subgroup.map_lowerCentralSeries,hc,Subgroup.map_bot]


/-- The original-degree Main Hypothesis has Sylow class at most two in
characteristic two; the power-reduction alternative is discharged. -/
theorem original_sl2_class_two
    (e : (G ⧸ pCore 2 G) ≃* SL(2,F)) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup G) ⊤)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) :
    (S : Subgroup G).lowerCentralSeries 2 = ⊥ ∧ Group.nilpotencyClass S ≤ 2 := by
  have htwo : (S : Subgroup G).lowerCentralSeries 2 = ⊥ := by
    rcases original_sl2_power_reduction e hn hF S α hu hfit hno with hc | hp
    · exact hc
    obtain ⟨g,hg,hgen,hinter,w,hw,Z,hZomega,hZthird,s,hs,hLQ,hres,hfitL,huL,hcl,
      ⟨e',he'⟩,hZmap,γ,hγ,hnoγ,hescγ,hdiagram⟩ := hp
    let L := (NilesRankOneKernel.invariantNormalKernel (S : Subgroup G) (α^w)).map (S : Subgroup G).subtype
    let q := QuotientGroup.mk' L
    have hLS : L ≤ (S : Subgroup G) := map_subtype_le _
    have hpL : IsPGroup 2 L := S.isPGroup'.of_injective (inclusion hLS) (inclusion_injective hLS)
    have hqker : IsPGroup 2 q.ker := by
      change IsPGroup 2 (QuotientGroup.mk' L).ker
      rw [QuotientGroup.ker_mk']
      exact hpL
    have hcoremap : (pCore 2 G).map q = pCore 2 (G ⧸ L) := by
      rw [←q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective L) hqker,
        map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective L)]
    have hconj : ((S : Subgroup G).map (MulAut.conj g).toMonoidHom).map q =
        ((S : Subgroup G).map q).map (MulAut.conj (q g)).toMonoidHom := by
      rw [map_map,map_map]
      congr 1
    have hgen' : (S : Subgroup G).map q ⊔
        ((S : Subgroup G).map q).map (MulAut.conj (q g)).toMonoidHom = ⊤ := by
      rw [←hconj,←Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective L)]
    have hinter' : (S : Subgroup G).map q ⊓
        ((S : Subgroup G).map q).map (MulAut.conj (q g)).toMonoidHom = pCore 2 (G ⧸ L) := by
      rw [←hconj,inf_comm,←map_inf_of_ker_le q _ _ (by
        rw [QuotientGroup.ker_mk']; exact hLS),inf_comm,hinter,hcoremap]
    have hcl' : Group.nilpotencyClass
        (((S : Subgroup G).map q).map (MulAut.conj (q g)).toMonoidHom) = 3 := by
      rw [←hconj]
      exact hcl
    exact (sl2_no_two_step_class_three e' hn hF
      (S.mapSurjective (QuotientGroup.mk'_surjective L)) γ hfitL hnoγ (q g)
      hgen' hinter' hdiagram hcl').elim
  let _ := S.isPGroup'.isNilpotent
  refine ⟨htwo,Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp ?_⟩
  apply map_injective (f := (S : Subgroup G).subtype) Subtype.val_injective
  rw [top_subtype_lowerCentralSeries,Subgroup.map_bot]
  exact htwo

end Glauberman
