module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.OutsideWitness.Source
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Solvable.Fitting
/-!
# The actual E.2.9 generalized-Fitting inheritance clause

Restrict the original Sylow subgroup and elementary generator to H. Mapping
the literal pair-generation equation from I into H identifies the same I as
the join of the two H-conjugates. The ambient two-core therefore normalizes I,
and characteristic-two inheritance proves the requested Fitting equality.
No solvability or dihedral model premise is used in this clause; construction
of the member remains the separate existence part of E.2.9.
Source: Aschbacher–Smith E.2.9(1–2), printed pp.221–222, and 15.4.2(4).
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.RatioSource.OutsideWitness
universe u
variable {X : Type u} [Group X] [Finite X]
variable {T : Sylow 2 X} {H N V I : Subgroup X}

theorem SolvableMember.generalizedFitting_eq_twoCore (c : Configuration T H N V)
    (w : SolvableMember T H N V I) (hfit : generalizedFitting H = pCore 2 H) :
    generalizedFitting I = pCore 2 I := by
  let S := T.subtype (c.sylow_le_maximal.trans c.maximal.le)
  let U := V.subgroupOf H
  let K := I.subgroupOf H
  let f : I →* H := inclusion w.le_H
  have hVH : V ≤ H := w.le_I.trans w.le_H
  have hUT : U ≤ (S : Subgroup H) := comap_mono c.le_sylow
  have hTV : (S : Subgroup H) ≤ normalizer (U : Set H) := by
    rw [show U = V.subgroupOf H from rfl, ← subgroupOf_normalizer_eq hVH]
    exact comap_mono ((normal_subgroupOf_iff_le_normalizer c.le_sylow).mp c.normal_in_sylow)
  have hUmap : (V.subgroupOf I).map f = U := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x,w.le_I hx⟩,hx,rfl⟩
  have hrange : f.range = K := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x,hx⟩,rfl⟩
  have hgen : U ⊔ U.map (MulAut.conj (f w.conjugator)).toMonoidHom = K := by
    have hh := congrArg (fun A : Subgroup I => A.map f) w.generate
    rw [Subgroup.map_sup,hUmap,← MonoidHom.range_eq_map,hrange,map_map] at hh
    have he : f.comp (MulAut.conj w.conjugator).toMonoidHom =
        (MulAut.conj (f w.conjugator)).toMonoidHom.comp f := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,map_mul,map_inv]
    rw [he,← map_map,hUmap] at hh
    exact hh
  have hnorm : pCore 2 H ≤ normalizer (K : Set H) :=
    hgen ▸ ChapterE.twoCore_le_normalizer_conjugate_join S U hTV (f w.conjugator)
  have hK := generalizedFitting_eq_pCore_of_normalized_by_pCore K hfit hnorm
  let e : K ≃* I := subgroupOfEquivOfLe w.le_H
  have hm := congrArg (fun A : Subgroup K => A.map e.toMonoidHom) hK
  rwa [map_generalizedFitting_equiv, pCore_map_iso] at hm
end CFSG.Quasithin.Chapter15.Section04.RatioSource.OutsideWitness
