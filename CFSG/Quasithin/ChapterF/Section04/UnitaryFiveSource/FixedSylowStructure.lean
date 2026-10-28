module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.GraphDescent
public import Theory.SpecificGroups.SymplecticFour.Sylow

/-!
# Saturated inner fixed-Sylow order on the same unitary-five marking

An injective middle map carries the original inner centralizer exactly onto
the intersection specified by the native saturation clause. Matrix descent
identifies the represented graph twist's inner centralizer with Sp₄(4),
whose Sylow two-subgroups have order 256. The explicit subgroup-map equality
keeps the inner part distinct from the full fixed Sylow, including outer actors.

Source: Aschbacher--Smith F.4.37(1) and the comparison preceding F.4.38,
printed pp.293--294 of refs/quasithin.pdf. The Chapter6 consumer combines
this exact inner count with the original index-divides-four bound.
-/

/-!
# The saturated inner fixed Sylow of a represented U₅(4) actor

The same extension and base map identify the inner centralizer with Sp₄(4).
Inner saturation therefore identifies the original fixed two-subgroup with
its four-root unipotent group. This equivalence records group structure;
it makes no assertion about a selected root or endpoint marking.

Source: Aschbacher–Smith F.4.37, printed p.293 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
open Theory.SpecificGroups.UnitaryFive.Descent Theory.SpecificGroups.UnitaryFive.GraphFixed
variable (U : GreenBook.UnitaryFive.Model 4) (E : FiveExtension U)

private theorem inner_centralizer_map {D : Type*} [Group D]
    (e : D ≃* E.middle) (S : Subgroup D) (P : Subgroup E.middle)
    (hinner : P ⊓ (inner U.Carrier).comap E.middle.subtype = S.map e.toMonoidHom)
    (t : D) :
    let j := inclusion (inf_le_left.trans E.left_le : E.middle ≤ E.carrier)
    (S ⊓ centralizer ({t} : Set D)).map (j.comp e.toMonoidHom) =
      P.map j ⊓ (E.baseHom.range ⊓ centralizer ({j (e t)} : Set E.carrier)) := by
  let j := inclusion (inf_le_left.trans E.left_le : E.middle ≤ E.carrier)
  let φ := j.comp e.toMonoidHom
  have hφ : Function.Injective φ := (inclusion_injective (inf_le_left.trans E.left_le)).comp e.injective
  ext a
  constructor
  · rintro ⟨x,⟨hx,hxt⟩,rfl⟩
    have hm : e x ∈ P ⊓ (inner U.Carrier).comap E.middle.subtype := by
      rw [hinner]
      exact mem_map_of_mem _ hx
    refine ⟨⟨e x,hm.1,rfl⟩,?_,?_⟩
    · obtain ⟨v,hv⟩ := hm.2
      exact ⟨v,Subtype.ext hv⟩
    · exact mem_centralizer_singleton_iff.mpr (by
        simpa only [φ,j,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,map_mul] using congrArg φ (mem_centralizer_singleton_iff.mp hxt))
  · rintro ⟨⟨z,hz,rfl⟩,⟨v,hv⟩,hzt⟩
    have hzinner : z.val ∈ inner U.Carrier := ⟨v,congrArg Subtype.val hv⟩
    have hzS : z ∈ S.map e.toMonoidHom := hinner ▸ ⟨hz,hzinner⟩
    obtain ⟨x,hx,rfl⟩ := hzS
    refine ⟨x,⟨hx,?_⟩,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply hφ
    simpa only [φ,j,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,map_mul] using mem_centralizer_singleton_iff.mp hzt

theorem five_represented_inner_sylow_equiv {D : Type*} [Group D]
    (e : D ≃* E.middle) (S : Subgroup D) (P : Sylow 2 E.middle)
    (hinner : (P : Subgroup E.middle) ⊓ (inner U.Carrier).comap E.middle.subtype =
      S.map e.toMonoidHom)
    (t : D) (ht : t^2=1) (u : U.form.unitarySubgroup)
    (hf : (e t).val=unitaryConj U.form u*projectiveAut U.form U.matrix)
    (hsat : let j := inclusion (inf_le_left.trans E.left_le : E.middle ≤ E.carrier)
      ∃ R : Sylow 2 (E.baseHom.range ⊓ centralizer ({j (e t)} : Set E.carrier) : Subgroup E.carrier),
        (R : Subgroup _).map (E.baseHom.range ⊓ centralizer ({j (e t)} : Set E.carrier)).subtype =
          ((P : Subgroup E.middle).map j) ⊓
            (E.baseHom.range ⊓ centralizer ({j (e t)} : Set E.carrier))) :
    Nonempty ((S ⊓ centralizer ({t} : Set D) : Subgroup D) ≃*
      Theory.SpecificGroups.SymplecticFour.unipotent (F := FixedBy.subfield U.F U.form.conj)) := by
  let j := inclusion (inf_le_left.trans E.left_le : E.middle ≤ E.carrier)
  let f := j (e t)
  let C := E.baseHom.range ⊓ centralizer ({f} : Set E.carrier)
  let φ := j.comp e.toMonoidHom
  have hφ : Function.Injective φ :=
    (inclusion_injective (inf_le_left.trans E.left_le)).comp e.injective
  have hf2 : f^2=1 := by
    change (j (e t))^2=1
    rw [←map_pow,←map_pow,ht,map_one,map_one]
  obtain ⟨v,hv⟩ := exists_graph_conjugator_of_unitary_twist U E f hf2 u hf
  obtain ⟨R,hR⟩ := hsat
  let a := conjugateGraphInnerCentralizerEquiv U E f (unitaryConj U.form v) hv
  let Q := R.mapSurjective (f := a.toMonoidHom) a.surjective
  have hm : (S ⊓ centralizer ({t} : Set D)).map φ = (R : Subgroup C).map C.subtype := by
    exact (inner_centralizer_map U E e S (P : Subgroup E.middle) hinner t).trans hR.symm
  let b : (S ⊓ centralizer ({t} : Set D) : Subgroup D) ≃* R :=
    (((S ⊓ centralizer ({t} : Set D)).equivMapOfInjective φ hφ).trans
      (MulEquiv.subgroupCongr hm)).trans
      ((R : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective).symm
  let c : R ≃* Q := (R : Subgroup C).equivMapOfInjective a.toMonoidHom a.injective
  let Q₀ := Theory.SpecificGroups.SymplecticFour.unipotentSylow
    (n := 2) U.graph_fixed_field_card (by decide)
  exact ⟨b.trans (c.trans (Q.equiv Q₀))⟩

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
