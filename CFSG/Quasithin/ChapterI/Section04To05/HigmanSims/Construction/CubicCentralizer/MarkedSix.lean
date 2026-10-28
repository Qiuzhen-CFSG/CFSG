module
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.OddCoreQuotient
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.CubicConjugatingCore
public import Theory.GroupTheory.MarkedSixCentralizer

/-!
# An actual marked S3 in the original cubic-centralizer quotient

The original full sixteen-normalizer contributes its cubic centralizer of
order eighteen. Its image under the original odd-core quotient has order
six and contains a marked seed involution. The full marked centralizer has
order eight, so this literal image is S3 and the ambient quotient cannot
be S4. The paired source construction supplies the required marked seed
point as the square of its actual cubic-centralizing cyclic-four element.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The actual image of the full sixteen-normalizer cubic centralizer is
a marked S3 in the original odd-core quotient, excluding the S4 alternative. -/
theorem TypeAt.cubic_quotient_marked_six (h : TypeAt z V)
    {A : Subgroup G} [IsElementaryAbelian 2 A] (d : NaturalEndpointData A)
    (t : G) (htz : t∈involutionCentralizer z) (ht : t∈d.carrier) (ht3 : orderOf t=3)
    (hzN : z∈normalizer (A : Set G)) :
    let C := centralizer ({t} : Set G)
    let O := pPrimeCore 2 C
    let X := C⧸O
    let q := QuotientGroup.mk' O
    let E := normalizer (A : Set G)⊓C
    let H := (E.subgroupOf C).map q
    ∃ zC : C, (zC : G)=z ∧ orderOf (q zC)=2 ∧
      Nat.card (centralizer ({q zC} : Set X))=8 ∧
      Nat.card H=6 ∧ q zC∈H ∧ Nonempty (H≃*Equiv.Perm (Fin 3)) ∧
      ¬Nonempty (X≃*Equiv.Perm (Fin 4)) := by
  let C := centralizer ({t} : Set G)
  let O := pPrimeCore 2 C
  let X := C⧸O
  let q := QuotientGroup.mk' O
  let E := normalizer (A : Set G)⊓C
  let D := E.subgroupOf C
  let H := D.map q
  obtain ⟨zC,hz,hz2,_,hO,_,hC8,_,_⟩ := h.cubic_centralizer_oddCore_quotient t htz ht3
  have hO3 : Nat.card O=3 := by
    rw [←card_map_of_injective C.subtype_injective,hO,Nat.card_zpowers,ht3]
  have hOD : O≤D := by
    intro x hx
    have hxt : (x : G)∈zpowers t := hO ▸ mem_map_of_mem C.subtype hx
    exact ⟨zpowers_le.mpr (d.normalizes ht) hxt,x.property⟩
  have hD18 : Nat.card D=18 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show E≤C from inf_le_right)).toEquiv).trans
      (d.cubic_full_normalizer_centralizer t ht ht3).1
  let f : D→*X := q.comp D.subtype
  have hk : f.ker=O.subgroupOf D := by
    ext x
    change q (x : C)=1 ↔ (x : C)∈O
    exact QuotientGroup.eq_one_iff _
  have hk3 : Nat.card f.ker=3 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe hOD).toEquiv,hO3]
  have hr : f.range=H := by rw [MonoidHom.range_comp,range_subtype]
  have hH6 : Nat.card H=6 := by
    have hh := f.ker.card_mul_index
    rw [hk3,index_ker,hr,hD18] at hh
    change 3*Nat.card H=18 at hh
    omega
  have hzD : zC∈D := by
    refine ⟨?_,zC.property⟩
    change (zC : G)∈normalizer (A : Set G)
    rw [hz]
    exact hzN
  have hzH : q zC∈H := mem_map_of_mem q hzD
  exact ⟨zC,hz,hz2,hC8,hH6,hzH,
    marked_six_equiv_perm_three H hH6 (q zC) hzH hC8,
    not_perm_four_of_marked_six H hH6 (q zC) hzH hz2 hC8⟩

/-- Original TypeAt data supply the seed-class marked involution in the
same order-eighteen normalizer centralizer. The full original quotient map
and its literal order-six S3 image are retained. -/
theorem TypeAt.exists_marked_cubic_quotient_six (h : TypeAt z V) :
    ∃ (A : Subgroup G) (hAE : IsElementaryAbelian 2 A), letI := hAE
    ∃ (d : NaturalEndpointData A) (t u c : G), Nat.card A=16 ∧
      u∈V ∧ u≠1 ∧ IsConj u z ∧ TypeAt u V ∧
      c∈(normalizer (V : Set G)).pCoreIn 2 ∧ c^2=u ∧ orderOf c=4 ∧ Commute c t ∧
      t∈d.carrier ∧ orderOf t=3 ∧ u∈normalizer (A : Set G)⊓centralizer ({t} : Set G) ∧
      let C := centralizer ({t} : Set G)
      let O := pPrimeCore 2 C
      let X := C⧸O
      let q := QuotientGroup.mk' O
      let E := normalizer (A : Set G)⊓C
      let H := (E.subgroupOf C).map q
      ∃ uC : C, (uC : G)=u ∧ orderOf (q uC)=2 ∧
        Nat.card (centralizer ({q uC} : Set X))=8 ∧
        Nat.card H=6 ∧ q uC∈H ∧ Nonempty (H≃*Equiv.Perm (Fin 3)) ∧
        ¬Nonempty (X≃*Equiv.Perm (Fin 4)) := by
  obtain ⟨W,A,B,p,t,hAE,hBE,hAB,hBA,hWV,hW4,hA16,hB16,hp,hpW,hB,hAP,hBP,hCA,hCB,
    hi,hcomm,h64,hC,hpureA,hpureB,hpointsA,hpointsB,ht3,htW,hdis,h192,d,dB,hBd,
    _,htd,_,_,_⟩ := h.exists_paired_natural_endpoints
  let := hAE
  have hWA : W≤A := hi ▸ (show A⊓B≤A from inf_le_left)
  have hAC : A≤centralizer (W : Set G) := le_sup_left.trans hC
  obtain ⟨u,c,huV,hu1,_,huT,_,hcP,hc2,hc4,hct,_,_⟩ :=
    h.paired_endpoint_cubic_conjugating_core W A B hWV hW4 hA16 hWA hAC hAP
      p hp hpW hB d t htd.1 htW ht3
  have hu2 : u^2=1 := huT.involution ▸ pow_orderOf_eq_one u
  have huN : u∈normalizer (A : Set G) :=
    (h.plane_radical_core_normalizer W A hWV hW4 hA16 hWA hAC hAP u
      (hc2 ▸ pow_mem hcP 2)).mpr (hu2 ▸ W.one_mem)
  have hut : Commute u t := hc2 ▸ hct.pow_left 2
  have htu : t∈involutionCentralizer u := mem_centralizer_singleton_iff.mpr hut.symm.eq
  have huz : IsConj u z := by
    obtain ⟨g,hg⟩ := h.seed_transitive (⟨u,huV⟩ : V) ⟨z,h.involution_mem_seed⟩
      (fun he => hu1 (congrArg Subtype.val he))
      (fun he => by
        have hz1 : z=1 := congrArg Subtype.val he
        have hh := h.involution
        simp [hz1] at hh)
    exact isConj_iff.mpr ⟨g,congrArg Subtype.val hg⟩
  refine ⟨A,hAE,d,t,u,c,hA16,huV,hu1,huz,huT,hcP,hc2,hc4,hct,htd.1,ht3,
    ⟨huN,mem_centralizer_singleton_iff.mpr hut.eq⟩,?_⟩
  exact huT.cubic_quotient_marked_six d t htu htd.1 ht3 huN

end CFSG.Quasithin.HigmanSims
