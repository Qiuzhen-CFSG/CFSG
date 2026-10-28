module
public import Theory.GroupTheory.ConjugacyFamilySpan
public import Theory.GroupTheory.WeakClosureFrattini

/-!
# Relative Frattini generation for subgroup families

A conjugation-invariant family generates a subgroup normal in each ambient
overgroup. Its span in a Sylow subgroup is weakly closed. Applying the
weak-closure Frattini argument inside the overgroup, then mapping back to the
original group, gives generation by the span and its Sylow span's normalizer.

This is the relative-normality step in Aschbacher–Smith, *The Classification
of Quasithin Groups*, Proposition E.5.2, printed p.243 (1 March 2004).
-/

open Subgroup
namespace SubgroupFamily
variable {G : Type*} [Group G] [Finite G]

/-- A relative Frattini argument for a conjugation-invariant family. -/
public theorem relative_frattini {p : ℕ} [Fact p.Prime]
    {family : Set (Subgroup G)} (hf : ConjugationInvariant family)
    (H : Subgroup G) (S : Sylow p H) :
    H ≤ normalizer (span family ((S : Subgroup H).map H.subtype) : Set G) ⊔
      span family H := by
  let J := span family ((S : Subgroup H).map H.subtype)
  let N := span family H
  have hSH : (S : Subgroup H).map H.subtype ≤ H := map_subtype_le _
  have hJH : J ≤ H := (span_le _ _).trans hSH
  have hNH : N ≤ H := span_le _ _
  have hJN : J ≤ N := span_mono family hSH
  have hJS : J.subgroupOf H ≤ (S : Subgroup H) := by
    have h := comap_mono (f := H.subtype) (span_le family ((S : Subgroup H).map H.subtype))
    simpa only [J, Subgroup.subgroupOf, comap_map_eq_self_of_injective H.subtype_injective] using h
  let _ : (N.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (H.le_normalizer.trans (normalizer_le_span_normalizer hf H))
  have hweak (g : H)
      (hg : (J.subgroupOf H).map (MulAut.conj g).toMonoidHom ≤ S) :
      (J.subgroupOf H).map (MulAut.conj g).toMonoidHom = J.subgroupOf H := by
    have hcomp : H.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp H.subtype := by ext x; rfl
    have hm : ((J.subgroupOf H).map (MulAut.conj g).toMonoidHom).map H.subtype =
        J.map (MulAut.conj (g : G)).toMonoidHom := by
      rw [map_map, hcomp, ← map_map, map_subgroupOf_eq_of_le hJH]
    apply (map_injective H.subtype_injective)
    rw [hm, map_subgroupOf_eq_of_le hJH]
    apply span_weakly_closed hf _ (g : G)
    have h := map_mono (f := H.subtype) hg
    rwa [hm] at h
  have he := normalizer_sup_eq_top_of_weakly_closed S (N.subgroupOf H)
    (J.subgroupOf H) hJS (comap_mono hJN) hweak
  have hm := congrArg (fun U : Subgroup H => U.map H.subtype) he
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hNH, ← MonoidHom.range_eq_map, range_subtype] at hm
  apply hm.ge.trans
  apply sup_le_sup_right _
  have hn := (J.subgroupOf H).le_normalizer_map H.subtype
  rwa [map_subgroupOf_eq_of_le hJH] at hn
end SubgroupFamily
