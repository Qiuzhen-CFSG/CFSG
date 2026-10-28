module
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.ConditionalInput
/-!
# The actual strict enlargement with its original pushing data

The contrary component-normalizer configuration supplies an ambient normal
C-component properly containing the opposite A₅ factor. The exact subgroup
retains both odd-rank bounds, its outside-M property, and the proved C.2.3
setup for the original `R = O₂(L₀T)`. This is the direct consumer joining the
strict enlargement to the source pushing setup.

Source: Aschbacher–Smith, Lemma 10.2.6, printed pp.748–749.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
/-- Ambient form of the actual strict opposite enlargement, with all geometric source input. -/
theorem source_a5_strict_component_pushing_enlargement
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (L : Set G) ≤ D.maximalLocal) :
    ∃ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) ∧
      localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom ∧
      ∃ K : Subgroup G, K ∈ cComponentsIn (normalizer (L : Set G)) ∧
        (K.subgroupOf (normalizer (L : Set G))).Normal ∧
        L.map (MulAut.conj t).toMonoidHom < K ∧
        ¬ K ≤ D.maximalLocal ∧ primeRank 3 K ≤ 1 ∧ primeRank 5 K ≤ 1 ∧
        Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple
          (normalizer (L : Set G)) ((localJoin T L).pCoreIn 2)
          (normalizer (L : Set G) ⊓ D.maximalLocal) := by
  let N := normalizer (L : Set G)
  obtain ⟨t,ht,htn,hpair,I,hI,hIN,hBI,_,h3,h5⟩ :=
    source_a5_escaping_component_normalizer_enlargement D e hn hout
  let B := L.map (MulAut.conj t).toMonoidHom
  let K := I.map N.subtype
  have hKN : K ≤ N := map_subtype_le I
  have hBK : B < K := by
    have hh := (map_lt_map_iff_of_injective N.subtype_injective).mpr hBI
    have hBN : B ≤ N :=
      (le_sup_right.trans hpair.ge).trans (source_nonnormal_orbit_le_normalizer D hn)
    have hmapB : (B.subgroupOf N).map N.subtype = B :=
      map_subgroupOf_eq_of_le hBN
    rw [hmapB] at hh
    exact hh
  have hKI : K.subgroupOf N = I := by
    exact comap_map_eq_self_of_injective N.subtype_injective I
  have hKc : K ∈ cComponentsIn N := ⟨hKN, hKI.symm ▸ hI⟩
  have hKn : (K.subgroupOf N).Normal := hKI.symm ▸ hIN
  have he := I.equivMapOfInjective N.subtype N.subtype_injective
  refine ⟨t,ht,htn,hpair,K,hKc,hKn,hBK,
    source_strict_conjugate_component_outside D ht hKc hBK,?_,?_,
    source_nonnormal_component_normalizer_pushing_setup D hn⟩
  · exact (primeRank_congr 3 he).symm.trans_le h3
  · exact (primeRank_congr 5 he).symm.trans_le h5
end CFSG.Quasithin.Chapter10
