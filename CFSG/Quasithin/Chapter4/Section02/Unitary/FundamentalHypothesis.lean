module
public import CFSG.Quasithin.Chapter4.Section01.ModuleControl
public import CFSG.Quasithin.Chapter4.Section04.OddActorCounterexample
public import Theory.GroupTheory.NormalizedSupCard
import Mathlib.Tactic
/-!
# The normalized Fundamental Setup satisfies the pushing-up hypothesis

The covering family in4.1.1 contains a Sylow subgroup: its section-centralizer
index is odd and equals its index in M. Conjugating that Sylow inside M
transports the genuine uniqueness of XT, while preserving the normal X.
The original Section12.2 hypothesis provides perfection of L, so with
M=N(L) no additional pushing-up hypothesis remains.
Source: Aschbacher--Smith,4.2.2, printed p.608, in the normalized case.
-/

public section
namespace CFSG.Quasithin.Chapter4
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

private theorem relativeIndex_of_cover {C I M : Subgroup G}
    (hCM : C ≤ M) (hIM : I ≤ M) (hMC : M ≤ normalizer (C : Set G))
    (hcover : (M : Set G) = (C : Set G) * (I : Set G)) :
    I.relIndex M = (C ⊓ I).relIndex C := by
  have he : C ⊔ I = M := by
    apply le_antisymm (sup_le hCM hIM)
    intro m hm
    obtain ⟨c,hc,i,hi,rfl⟩ := hcover ▸ (show m ∈ (M : Set G) from hm)
    exact mul_mem_sup hc hi
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes C I (hIM.trans hMC)
  rw [he] at hp
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) I M bot_le hIM
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (C ⊓ I) C bot_le inf_le_left
  simp only [relIndex_bot_left] at hi hc
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (Nat.card_pos (α := (C ⊓ I : Subgroup G)))
    (Nat.card_pos (α := I)))
  calc
    (Nat.card (C ⊓ I : Subgroup G) * Nat.card I) * I.relIndex M =
        Nat.card (C ⊓ I : Subgroup G) * Nat.card M := by rw [mul_assoc,hi]
    _ = Nat.card C * Nat.card I := hp.symm
    _ = (Nat.card (C ⊓ I : Subgroup G) * Nat.card I) * (C ⊓ I).relIndex C := by
      rw [← hc]; ring

private theorem aligned_section_sylow {T : Sylow 2 G} {M X : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hMX : M ≤ normalizer (X : Set G)) :
    ∃ S : Sylow 2 (sectionCentralizerIn M X),
      (S : Subgroup (sectionCentralizerIn M X)).map (sectionCentralizerIn M X).subtype =
        sectionCentralizerIn (T : Subgroup G) X := by
  let C := sectionCentralizerIn M X
  have hCM : C ≤ M := inf_le_left
  let C' := C.subgroupOf M
  let : C'.Normal := (normal_subgroupOf_iff_le_normalizer hCM).mpr
    (sectionCentralizerIn_normalized hMX)
  obtain ⟨U,hU⟩ := (T.subtype hTM).exists_subgroupOf_eq_of_normal C'
  let e : C' ≃* C := subgroupOfEquivOfLe hCM
  refine ⟨U.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((U : Subgroup C').map e.toMonoidHom).map C.subtype = _
  rw [hU,map_map]
  ext x
  constructor
  · rintro ⟨c,hc,rfl⟩
    exact ⟨hc,c.property.2⟩
  · intro hx
    exact ⟨⟨⟨x,hTM hx.1⟩,⟨hTM hx.1,hx.2⟩⟩,hx.1,rfl⟩

private theorem exists_sylow_in_cover {T : Sylow 2 G} {M X I : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hMX : M ≤ normalizer (X : Set G))
    (hIM : I ≤ M) (hTI : sectionCentralizerIn (T : Subgroup G) X ≤ I)
    (hcover : (M : Set G) = (sectionCentralizerIn M X : Set G) * (I : Set G)) :
    ∃ P : Sylow 2 M, (P : Subgroup M).map M.subtype ≤ I := by
  let C := sectionCentralizerIn M X
  obtain ⟨S,hS⟩ := aligned_section_sylow hTM hMX
  have hSC : (S : Subgroup C).map C.subtype ≤ C ⊓ I :=
    le_inf (map_subtype_le _) (hS ▸ hTI)
  have hsindex : ¬ 2 ∣ ((S : Subgroup C).map C.subtype).relIndex C := by
    have he : ((S : Subgroup C).map C.subtype).relIndex C = (S : Subgroup C).index := by
      simpa only [← MonoidHom.range_eq_map,C.range_subtype,relIndex_top_right] using
        relIndex_map_map_of_injective (S : Subgroup C) ⊤ C.subtype_injective
    rw [he]
    exact S.not_dvd_index
  have hindex : ¬ 2 ∣ I.relIndex M := by
    rw [relativeIndex_of_cover inf_le_left hIM (sectionCentralizerIn_normalized hMX) hcover]
    intro hd
    apply hsindex
    have hdiv : (C ⊓ I).relIndex C ∣ ((S : Subgroup C).map C.subtype).relIndex C :=
      dvd_of_mul_left_eq _ (relIndex_mul_relIndex _ (C ⊓ I) C hSC inf_le_left)
    exact hd.trans hdiv
  let P : Sylow 2 (I.subgroupOf M) := Sylow.nonempty.some
  have hp : ¬ 2 ∣ ((P : Subgroup (I.subgroupOf M)).map (I.subgroupOf M).subtype).index := by
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul P.not_dvd_index hindex
  let U : Sylow 2 M := (P.isPGroup'.map (I.subgroupOf M).subtype).toSylow hp
  refine ⟨U,?_⟩
  rintro x ⟨y,hy,rfl⟩
  change y ∈ (P : Subgroup (I.subgroupOf M)).map (I.subgroupOf M).subtype at hy
  exact map_subtype_le (P : Subgroup (I.subgroupOf M)) hy

omit [Finite G] in
private theorem unique_map {I M : Subgroup G} (h : UniqueMaximalOvergroup I M)
    (e : G ≃* G) :
    UniqueMaximalOvergroup (I.map e.toMonoidHom) (M.map e.toMonoidHom) := by
  refine ⟨Theory.Quasithin.isMaximalTwoLocal_map e h.1,map_mono h.2.1,?_⟩
  intro N hN hIN
  have hh : I ≤ N.map e.symm.toMonoidHom := by
    simpa [map_map] using map_mono (f := e.symm.toMonoidHom) hIN
  have he := h.2.2 _ (Theory.Quasithin.isMaximalTwoLocal_map e.symm hN) hh
  simpa [map_map] using congrArg (fun A : Subgroup G => A.map e.toMonoidHom) he

/-- Normalized L and genuine uniqueness of LT give the actual general
pushing-up hypothesis4.1.1; no stronger uniqueness family is assumed. -/
theorem hypothesis411_of_normal_unique_sylow_join {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} (hG : IsSimpleQTKE K G)
    (hunique : UniqueMaximalOvergroup (X ⊔ (T : Subgroup G)) M)
    (hMX : M ≤ normalizer (X : Set G)) (hX : IsPPerfect 2 X) :
    Hypothesis411 K T M X := by
  have hXM : X ≤ M := le_sup_left.trans hunique.2.1
  have hTM : (T : Subgroup G) ≤ M := le_sup_right.trans hunique.2.1
  refine ⟨hG,hunique.1,hTM,hXM,(normal_subgroupOf_iff_le_normalizer hXM).mpr hMX,hX,?_⟩
  intro I hIM hXI hcover
  obtain ⟨P,hPI⟩ := exists_sylow_in_cover hTM hMX hIM (le_sup_right.trans hXI) hcover
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M (T.subtype hTM) P
  have hTg : (T : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom =
      (P : Subgroup M).map M.subtype := by
    rw [← hg]
    change _ = (((T : Subgroup G).subgroupOf M).map (MulAut.conj g).toMonoidHom).map M.subtype
    rw [map_map]
    have he : (M.subtype.comp (MulAut.conj g).toMonoidHom) =
        (MulAut.conj (g : G)).toMonoidHom.comp M.subtype := rfl
    rw [he,← map_map,map_subgroupOf_eq_of_le hTM]
  have hXg := mem_normalizer_iff_map_conj_eq.mp (hMX g.property)
  have hMg := mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer g.property)
  change X.map (MulAut.conj (g : G)).toMonoidHom = X at hXg
  change M.map (MulAut.conj (g : G)).toMonoidHom = M at hMg
  have hu := unique_map hunique (MulAut.conj (g : G))
  rw [Subgroup.map_sup,hXg,hTg,hMg] at hu
  have hsub : X ⊔ (P : Subgroup M).map M.subtype ≤ I :=
    sup_le (le_sup_left.trans hXI) hPI
  exact ⟨hunique.1,hIM,fun N hN hIN => hu.2.2 N hN (hsub.trans hIN)⟩
/-- The normalized Section12.2 source supplies4.1.1 from exactly its
original unique maximal two-local over LT. -/
theorem source_hypothesis411 {K : GroupClass} {T : Sylow 2 G} {L : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 K T L)
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G))) :
    Hypothesis411 K T (normalizer (L : Set G)) L := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  apply hypothesis411_of_normal_unique_sylow_join h.simpleQTKE hM le_rfl
  intro N hN hp
  let := hN
  have hs : Subsingleton (L ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
end CFSG.Quasithin.Chapter4
