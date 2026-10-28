module

public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.SeedReduction
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow

/-!
# The literal pair behind a moved Cartan seed

The source orbit bound gives index two for the normalizer of a moved
component inside H. Choose its mover in the original Sylow T. The two
conjugates generate exactly the original two-residual, are both relative
C-components of H, and conjugation by the mover exchanges them. The proof
transports through H's inclusion and does not assume the mover is an involution.

Source: Aschbacher--Smith, 1.2.1(3) and 5.1.10--12, pp.504,634--635.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem map_conj_subtype (H : Subgroup G) (K : Subgroup H) (t : H) :
    (K.map (MulAut.conj t).toMonoidHom).map H.subtype =
      (K.map H.subtype).map (MulAut.conj (t : G)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

/-- A moved source seed gives a literal pair exchanged by an element of T.
Both factors are components relative to the original H. -/
theorem moved_seed_pair {T : Sylow 2 G} {K H : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hH : H ∈ Chapter1.H G) (hK : (K.subgroupOf H).IsCComponent)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hmoved : K ≠ residual H) :
    ∃ t ∈ (T : Subgroup G), K.map (MulAut.conj t).toMonoidHom ≠ K ∧
      residual H = K ⊔ K.map (MulAut.conj t).toMonoidHom ∧
      ((K.map (MulAut.conj t).toMonoidHom).subgroupOf H).IsCComponent ∧
      (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = K := by
  have hnot : ¬ (T : Subgroup G) ≤ normalizer (K : Set G) := by
    intro hn
    apply hmoved
    exact (le_antisymm (iSup_conjugates_le_of_le_normalizer K T K le_rfl hn)
      (le_componentOrbit K T)).symm.trans horbit
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hnot
  have hne : K.map (MulAut.conj t).toMonoidHom ≠ K :=
    fun he => htn (mem_normalizer_iff_map_conj_eq.mpr he)
  let S := T.subtype hTH
  let A := K.subgroupOf H
  let s : H := ⟨t, hTH ht⟩
  have hA : A.map H.subtype = K := map_subgroupOf_eq_of_le hKH
  have hs : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hTH
  have hi : (normalizer (A : Set H)).index = 2 := by
    rcases Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
      (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hH) hK with hn | ⟨hi, _⟩
    · exact (hnot (hTH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn))).elim
    · exact hi
  have hsm : A.map (MulAut.conj s).toMonoidHom ≠ A := by
    intro he
    apply hne
    have hh := congrArg (map H.subtype) he
    simpa only [map_conj_subtype, hA] using hh
  have hp : componentOrbit A (S : Subgroup H) = A ⊔ A.map (MulAut.conj s).toMonoidHom := by
    apply le_antisymm
    · apply iSup_le
      intro x
      rcases NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi hsm (x : H) with he | he
      · exact he.le.trans le_sup_left
      · exact he.le.trans le_sup_right
    · exact sup_le (le_componentOrbit A S)
        (le_iSup (fun x : (S : Subgroup H) => A.map (MulAut.conj (x : H)).toMonoidHom)
          ⟨s, ht⟩)
  have hpG : componentOrbit K (T : Subgroup G) = K ⊔ K.map (MulAut.conj t).toMonoidHom := by
    have hh := congrArg (map H.subtype) hp
    simpa only [map_componentOrbit, hA, hs, Subgroup.map_sup, map_conj_subtype] using hh
  have hc : ((K.map (MulAut.conj t).toMonoidHom).subgroupOf H).IsCComponent := by
    have hh := hK.map_equiv (MulAut.conj s)
    have he : (A.map (MulAut.conj s).toMonoidHom).map H.subtype =
        K.map (MulAut.conj t).toMonoidHom := by rw [map_conj_subtype, hA]
    rw [← he]
    change ((A.map (MulAut.conj s).toMonoidHom).map H.subtype |>.comap H.subtype).IsCComponent
    simpa only [comap_map_eq_self_of_injective H.subtype_injective] using hh
  have hss : s * s ∈ normalizer (A : Set H) := mul_self_mem_of_index_two hi s
  have hsquare : (A.map (MulAut.conj s).toMonoidHom).map (MulAut.conj s).toMonoidHom = A := by
    calc
      _ = A.map (MulAut.conj (s * s)).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      _ = A := mem_normalizer_iff_map_conj_eq.mp hss
  refine ⟨t, ht, hne, horbit.symm.trans hpG, hc, ?_⟩
  have hh := congrArg (map H.subtype) hsquare
  simpa only [map_conj_subtype, hA] using hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
