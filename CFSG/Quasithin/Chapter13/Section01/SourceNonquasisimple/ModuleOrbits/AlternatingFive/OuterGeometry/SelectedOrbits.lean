module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive.OuterGeometry.Kernel
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive.OuterGeometry.ComponentOrbits
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerOrbits.SymmetricFive.Source

/-!
# Selected orbit lengths on the original A₅ cover

The actual component-centralizer index is one or fifteen. The faithful
S₅ image therefore gives LT-indices one or two, respectively fifteen or
thirty. Local Sylow selection forces the nontrivial T-index to divide the
LT-index, excluding the odd alternatives. All centralizers are taken in
the original group, and normality and Sylow selection remain relative to
the normalizer of L.

Source: Aschbacher--Smith, proof of 13.1.12, printed p.872. The lengths two
and thirty concern the selected vectors, not the entire six-space.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
open Chapter1 Chapter1.Section02 Chapter12.Section02
open Representation.SL2FourNatural

private theorem symmetricFive_index_alternatives (H : Subgroup (Equiv.Perm (Fin 5))) :
    H.index = H.relIndex (alternatingGroup (Fin 5)) ∨
      H.index = 2 * H.relIndex (alternatingGroup (Fin 5)) := by
  let A := alternatingGroup (Fin 5)
  change H.index = H.relIndex A ∨ H.index = 2 * H.relIndex A
  have he := (relIndex_mul_index (show H ⊓ A ≤ A from inf_le_right)).trans
    (relIndex_mul_index (show H ⊓ A ≤ H from inf_le_left)).symm
  simp only [inf_relIndex_right, inf_relIndex_left] at he
  have hA : A.index = 2 := alternatingGroup.index_eq_two
  rw [hA] at he
  have hd : A.relIndex H ∣ 2 := hA ▸ relIndex_dvd_index_of_normal A H
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hd | hd
  · rw [hd, one_mul] at he
    exact Or.inr (by omega)
  · rw [hd] at he
    exact Or.inl (by omega)

namespace Marking
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  {T : Sylow 2 G} {L : Subgroup G} (d : Marking T L W)

omit [Finite G] in
/-- An actual S₅ marking gives exactly the possible LT-orbit sizes, before
the local Sylow selection removes the odd possibilities. -/
theorem centralizer_index_alternatives (q : OuterMarking T L)
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L) (u : normalizerMoved L) :
    let k := if d.projection (d.coordinates u).toAdd = 0 then 1 else 15
    (centralizer ({(u : G)} : Set G)).relIndex (L ⊔ (T : Subgroup G)) = k ∨
      (centralizer ({(u : G)} : Set G)).relIndex (L ⊔ (T : Subgroup G)) = 2 * k := by
  let M := L ⊔ (T : Subgroup G)
  let C := centralizer ({(u : G)} : Set G)
  let C' := C.subgroupOf M
  let H := C'.map q.quotient
  have hk : q.quotient.ker ≤ C' := by
    rw [q.kernel]
    intro a ha x hx
    have hx' : x = (u : G) := Set.mem_singleton_iff.mp hx
    subst x
    exact ha u u.property
  have hi : H.index = C.relIndex M := index_map_eq C' q.onto hk
  have hl : H.relIndex (alternatingGroup (Fin 5)) = C.relIndex L := by
    rw [← q.component, ← relIndex_comap, comap_map_eq, sup_of_le_left hk]
    exact relIndex_subgroupOf le_sup_left
  have hr := symmetricFive_index_alternatives H
  rw [hi,hl,d.component_centralizer_index hmoved u] at hr
  exact hr

/-- The literal selected orbit lengths 2 and 30 in source13.1.12.
The input is an actual quotient identification, with the exact action kernel;
no stabilizer, orbit or cover dimension conclusion is assumed. -/
theorem selected_centralizer_index (q : OuterMarking T L)
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)))
    (hmove : ¬ (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G)) :
    (centralizer ({(u : G)} : Set G)).relIndex (L ⊔ (T : Subgroup G)) =
      if d.projection (d.coordinates u).toAdd = 0 then 2 else 30 := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hT : IsSylowIn 2 (T : Subgroup G) (L ⊔ (T : Subgroup G)) := by
    apply isSylowIn_iff.mpr
    exact ⟨T.isPGroup',le_sup_right,fun A hA hTA _ => T.is_maximal' hA hTA⟩
  have hlocal' := hlocal.restrict
    (inf_le_inf_right (centralizer ({(u : G)} : Set G)) le_sup_right)
    (inf_le_inf_right (centralizer ({(u : G)} : Set G)) (sup_le L.le_normalizer hTL))
  have halts := d.centralizer_index_alternatives q (source_moved_commutator h hL hn) u
  dsimp only at halts
  have hfour : ¬ 4 ∣ (centralizer ({(u : G)} : Set G)).relIndex
      (L ⊔ (T : Subgroup G)) := by
    split_ifs at halts <;> rcases halts with he | he <;> rw [he] <;> decide
  have hsmall := SourceCentralizerOrbits.SymmetricFive.sylow_intersection_index_le_two
    (T : Subgroup G) (L ⊔ (T : Subgroup G))
    (centralizer ({(u : G)} : Set G)) hT hlocal' hfour
  have htwo : (centralizer ({(u : G)} : Set G)).relIndex (T : Subgroup G) = 2 := by
    have hpos : 0 < (centralizer ({(u : G)} : Set G)).relIndex (T : Subgroup G) :=
      Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hne : (centralizer ({(u : G)} : Set G)).relIndex (T : Subgroup G) ≠ 1 :=
      fun he => hmove (relIndex_eq_one.mp he)
    omega
  have hd := SourceCentralizerOrbits.SymmetricFive.sylow_intersection_index_dvd
    (T : Subgroup G) (L ⊔ (T : Subgroup G))
    (centralizer ({(u : G)} : Set G)) hT hlocal'
  rw [htwo] at hd
  split_ifs at halts ⊢ with hp <;> rcases halts with he | he
  · rw [he] at hd; norm_num at hd
  · exact he
  · rw [he] at hd; norm_num at hd
  · exact he


include d in
/-- The selected orbit computation supplies the literal Sylow index bound
of 13.1.12(2), including the already central branch. -/
theorem centralizer_sylow_index_le_two (q : OuterMarking T L)
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    (centralizer ({(u : G)} : Set G)).relIndex (T : Subgroup G) ≤ 2 := by
  by_cases hm : (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G)
  · rw [relIndex_eq_one.mpr hm]
    decide
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hT : IsSylowIn 2 (T : Subgroup G) (L ⊔ (T : Subgroup G)) := by
    apply isSylowIn_iff.mpr
    exact ⟨T.isPGroup',le_sup_right,fun A hA hTA _ => T.is_maximal' hA hTA⟩
  have hlocal' := hlocal.restrict
    (inf_le_inf_right (centralizer ({(u : G)} : Set G)) le_sup_right)
    (inf_le_inf_right (centralizer ({(u : G)} : Set G)) (sup_le L.le_normalizer hTL))
  apply SourceCentralizerOrbits.SymmetricFive.sylow_intersection_index_le_two
    (T : Subgroup G) (L ⊔ (T : Subgroup G)) _ hT hlocal'
  rw [d.selected_centralizer_index q h hL hn u hlocal hm]
  split_ifs <;> decide

end Marking
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
