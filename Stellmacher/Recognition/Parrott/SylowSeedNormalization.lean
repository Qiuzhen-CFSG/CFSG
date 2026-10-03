module

public import Stellmacher.Recognition.Parrott.SylowSeedData
public import Theory.SpecificGroups.Tits.RecognitionSylowSeedTransport

/-!
# Case 2 normalization with the original local subgroups

The printed substitution first sends (u,w,a,b,c,d,x) to
(u,wu,a,abt,c,cdu,x⁻¹) and temporarily replaces v by vt. Conjugating all entries
by x restores z,t,v. The elementary bases and the generating sets of J,T have
unchanged closures before conjugation. Since x lies in the actual T, it
normalizes F,T and also the characteristic core and derived core of H.
Thus the new witnesses lie in precisely the original four subgroups.

Source: Parrott (1972), §3, pp.679–680. The extra conjugation makes explicit
the marked-element preservation not supplied by the abstract isomorphism sentence.
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

private theorem ambient_core_normalized :
    centralizer ({z} : Set G) ≤ normalizer
      (((pCore 2 (centralizer ({z} : Set G))).map
        (centralizer ({z} : Set G)).subtype) : Set G) := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  have hh := le_normalizer_map (H := J) H.subtype
  rw [normalizer_eq_top] at hh
  simpa only [← MonoidHom.range_eq_map, range_subtype] using hh

private theorem ambient_derived_normalized :
    centralizer ({z} : Set G) ≤ normalizer
      (((commutator (pCore 2 (centralizer ({z} : Set G)))).map
        ((centralizer ({z} : Set G)).subtype.comp
          (pCore 2 (centralizer ({z} : Set G))).subtype)) : Set G) := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := (commutator J).map J.subtype
  have hh := le_normalizer_map (H := D) H.subtype
  rw [normalizer_eq_top] at hh
  simpa only [← MonoidHom.range_eq_map, range_subtype, D, map_map] using hh

namespace ParrottSylowSeedData

/-- Convert the primed equations to the unprimed ones, fixing the supplied
z,t,v,F,T and the original core and derived subgroup literally. -/
public def normalizeCaseTwo (f : ParrottSylowSeedData n true) :
    ParrottSylowSeedData n false := by
  let μ := MulAut.conj f.x
  have hm := f.relations.marked_conjugates
  have hxT := f.x_mem_sylow
  have hxH : f.x ∈ centralizer ({z} : Set G) := by
    change f.x ∈ (e.sylow : Subgroup G) at hxT
    rw [e.sylow_map] at hxT
    exact map_subtype_le _ hxT
  have hF := mem_normalizer_iff_map_conj_eq.mp (e.sylow_le_normalizer f.x_mem_sylow)
  have hT := mem_normalizer_iff_map_conj_eq.mp ((e.sylow : Subgroup G).le_normalizer f.x_mem_sylow)
  have hJ := mem_normalizer_iff_map_conj_eq.mp (ambient_core_normalized hxH)
  have hE := mem_normalizer_iff_map_conj_eq.mp (ambient_derived_normalized hxH)
  refine {
    u := μ f.u
    w := μ (f.w*f.u)
    a := μ f.a
    b := μ (f.a*f.b*n.t)
    c := μ f.c
    d := μ (f.c*f.d*f.u)
    x := μ f.x⁻¹
    derived_basis := ?_
    elementary_basis := ?_
    core_generators := ?_
    sylow_generators := ?_
    relations := f.relations.caseTwo_corrected }
  · have he := Tits.ParrottSylowSeedRelations.caseTwo_derived_closure
      (z := z) (t := n.t) (v := n.v) (u := f.u) (w := f.w)
    rw [f.derived_basis] at he
    have hh := congrArg (fun L : Subgroup G => L.map μ.toMonoidHom) he
    simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, μ, hm.1, hm.2.1, hm.2.2, hE] using hh
  · have he := Tits.ParrottSylowSeedRelations.caseTwo_elementary_closure
      (z := z) (t := n.t) (v := n.v) (u := f.u) (a := f.a)
    rw [f.elementary_basis] at he
    have hh := congrArg (fun L : Subgroup G => L.map μ.toMonoidHom) he
    simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, μ, hm.1, hm.2.1, hm.2.2, hF] using hh
  · have he := f.relations.caseTwo_core_closure
    rw [f.core_generators] at he
    have hh := congrArg (fun L : Subgroup G => L.map μ.toMonoidHom) he
    simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, μ, hJ] using hh
  · have he := f.relations.caseTwo_sylow_closure
    rw [f.sylow_generators] at he
    have hh := congrArg (fun L : Subgroup G => L.map μ.toMonoidHom) he
    simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, μ, hT] using hh

/-- Either printed case supplies an unprimed seed on the same local witnesses. -/
public def normalize {caseTwo : Bool} (f : ParrottSylowSeedData n caseTwo) :
    ParrottSylowSeedData n false := by
  cases caseTwo
  · exact f
  · exact f.normalizeCaseTwo

end ParrottSylowSeedData
end Stellmacher.Recognition
