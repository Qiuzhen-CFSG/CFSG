module
public import Theory.GroupTheory.SylowCentralizerConjugacy
/-!
# Maximal Sylow-centralizer order implies Sylow placement

Conjugate a Sylow subgroup of C_G(s) into the specified ambient Sylow.
Its image lies in the centralizer of a conjugate of s. If every such
centralizer has at most the original order, equality forces the original
intersection to be Sylow in C_G(s). This is the cardinal form of the
Sylow-placement step used in Aschbacher–Smith 2.4.23(4).
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
theorem exists_sylow_centralizer_of_maximal_conjugate_card
    (T : Sylow p G) (s : G) (hs : s ∈ T)
    (hmax : ∀ t ∈ T, IsConj s t →
      Nat.card ((T : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) ≤
        Nat.card ((T : Subgroup G) ⊓ centralizer ({s} : Set G) : Subgroup G)) :
    ∃ P : Sylow p (centralizer ({s} : Set G)),
      (P : Subgroup (centralizer ({s} : Set G))).map (centralizer ({s} : Set G)).subtype =
        (T : Subgroup G) ⊓ centralizer ({s} : Set G) := by
  let C := centralizer ({s} : Set G)
  let E := (T : Subgroup G) ⊓ C
  obtain ⟨P,hEP⟩ := ((T.isPGroup'.to_le (show E≤(T:Subgroup G) from inf_le_left)).comap_subtype (K:=C)).exists_le_sylow
  let V := (P : Subgroup C).map C.subtype
  have hEV : E ≤ V := by
    rw [←map_subgroupOf_eq_of_le (show E≤C from inf_le_right)]
    exact map_mono hEP
  obtain ⟨Q,hVQ⟩ := (P.isPGroup'.map C.subtype).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G Q T
  let e := MulAut.conj g
  have hVT : V.map e.toMonoidHom ≤ (T : Subgroup G) := by
    rw [←hg]
    exact map_mono hVQ
  have hsV : s ∈ V := hEV ⟨hs,mem_centralizer_singleton_iff.mpr rfl⟩
  have ht : e s ∈ T := hVT (mem_map_of_mem _ hsV)
  have hmap : V.map e.toMonoidHom ≤ (T : Subgroup G) ⊓ centralizer ({e s}:Set G) := by
    refine le_inf hVT ?_
    rintro _ ⟨v,hv,rfl⟩
    have hh := congrArg e (mem_centralizer_singleton_iff.mp ((map_subtype_le _) hv))
    exact mem_centralizer_singleton_iff.mpr (by
      change e v * e s = e s * e v
      simpa only [map_mul] using hh)
  have hcard : Nat.card V ≤ Nat.card E := by
    calc Nat.card V = Nat.card (V.map e.toMonoidHom) := (card_map_of_injective e.injective).symm
         _ ≤ Nat.card ((T : Subgroup G) ⊓ centralizer ({e s}:Set G) : Subgroup G) := card_le_of_le hmap
         _ ≤ Nat.card E := hmax (e s) ht (isConj_iff.mpr ⟨g,rfl⟩)
  exact ⟨P,(eq_of_le_of_card_ge hEV hcard).symm⟩
end Subgroup
