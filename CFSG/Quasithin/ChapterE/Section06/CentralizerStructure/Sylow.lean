module

public import CFSG.Quasithin.ChapterE.Section06.Basic
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.CharacteristicCentralizerSylow

/-!
# Sylow subgroups and characteristic normalizers of escaping centralizers

For U in the obstruction family, every two-subgroup of C_M(U) is killed
by its action on V, since O^{2′}(C_M(U)) centralizes V. The Sylow
intersection theorem first identifies C_T(V) as Sylow in C_G(V).
The normalizer condition then promotes local maximality to C_G(U).
Uniqueness controls normalizers of subgroups characteristic inside Q,
including their intrinsic normalizers inside H = C_G(U).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.5,
printed pp.245–246 (PDF pp.256–257). No classification input is needed.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U : Subgroup G}

theorem HypothesisE61.sylow_centralizer (h : HypothesisE61 K T M V) :
    ∃ S : Sylow 2 (centralizer (V : Set G)),
      (S : Subgroup (centralizer (V : Set G))).map
        (centralizer (V : Set G)).subtype = sylowCentralizer (T : Subgroup G) V := by
  let N := normalizer (V : Set G)
  let C := (centralizer (V : Set G)).subgroupOf N
  let TN := T.subtype h.sylow_le_normalizer
  obtain ⟨S, hS⟩ := TN.exists_subgroupOf_eq_of_normal C
  let e : C ≃* centralizer (V : Set G) :=
    subgroupOfEquivOfLe (centralizer_le_normalizer (V : Set G))
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((S : Subgroup C).map e.toMonoidHom).map _ = _
  rw [hS]
  ext x
  constructor
  · rintro ⟨c, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨hs, s.property⟩
  · rintro ⟨hxT, hxC⟩
    let s : C := ⟨⟨x, centralizer_le_normalizer (V : Set G) hxC⟩, hxC⟩
    exact ⟨e s, ⟨s, hxT, rfl⟩, rfl⟩


theorem HypothesisE61.sylowCentralizer_maximal (h : HypothesisE61 K T M V)
    {P : Subgroup G} (hp : IsPGroup 2 P)
    (hQP : sylowCentralizer (T : Subgroup G) V ≤ P)
    (hPC : P ≤ centralizer (V : Set G)) :
    P = sylowCentralizer (T : Subgroup G) V := by
  obtain ⟨S, hS⟩ := h.sylow_centralizer
  have he := S.is_maximal' hp.comap_subtype (by
    intro s hs
    exact hQP (hS ▸ mem_map_of_mem _ hs))
  have hm := congrArg (fun R : Subgroup (centralizer (V : Set G)) =>
    R.map (centralizer (V : Set G)).subtype) he
  change (P.subgroupOf (centralizer (V : Set G))).map _ = _ at hm
  rwa [map_subgroupOf_eq_of_le hPC, hS] at hm

omit [Finite G] in
theorem oddCentralizerCondition.two_subgroup_centralizes
    (ho : oddCentralizerCondition M V U) {P : Subgroup G}
    (hp : IsPGroup 2 P) (hP : P ≤ M ⊓ centralizer (U : Set G)) :
    P ≤ centralizer (V : Set G) := by
  intro x hx
  obtain ⟨n, hn⟩ := hp.exists_pow_pow_eq_one ⟨x, hx⟩
  have hnG : x ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  have hnC : (⟨x, hP hx⟩ : ↥(M ⊓ centralizer (U : Set G))) ^ (2 ^ n) = 1 :=
    Subtype.ext hnG
  exact (ho (mem_map_of_mem _ (mem_primeToResidual_of_pow hnC))).2

/-- E.6.5(1), retaining the actual ambient image of the Sylow subgroup. -/
theorem HypothesisE61.sylow_obstruction (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) :
    ∃ S : Sylow 2 (centralizer (U : Set G)),
      (S : Subgroup (centralizer (U : Set G))).map
        (centralizer (U : Set G)).subtype = sylowCentralizer (T : Subgroup G) V := by
  let Q := sylowCentralizer (T : Subgroup G) V
  have hQp : IsPGroup 2 Q := T.isPGroup'.to_le inf_le_left
  have hQH : Q ≤ centralizer (U : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le hU.1)
  have hQr : IsPGroup 2 (Q.subgroupOf (centralizer (U : Set G))) := hQp.comap_subtype
  obtain ⟨S, hS⟩ := hQr.exists_le_sylow
  refine ⟨S, ?_⟩
  apply prime_overgroup_eq_of_normalizer_control (p := 2) Q (centralizer (U : Set G)) M
    h.normalizer_sylowCentralizer_le
  · intro P hp hQP hPH hPM
    exact h.sylowCentralizer_maximal hp hQP
      (hU.2.2.2.two_subgroup_centralizes hp (le_inf hPM hPH))
  · exact S.isPGroup'.map _
  · rw [← map_subgroupOf_eq_of_le hQH]
    exact map_mono hS
  · exact map_subtype_le _

theorem HypothesisE61.characteristic_normalizers_le (h : HypothesisE61 K T M V) :
    (sylowCentralizer (T : Subgroup G) V).characteristicNormalizerClosure ≤ M := by
  exact characteristicNormalizerClosure_le_of_unique_maximalTwoLocal h.unique
    (T.isPGroup'.to_le inf_le_left) inf_le_right

omit [Finite G] in
theorem local_intersection_lt
    (hU : U ∈ obstructionFamily M V) :
    centralizer (U : Set G) ⊓ M < centralizer (U : Set G) :=
  lt_of_le_of_ne inf_le_left (fun he => hU.2.2.1 (he ▸ inf_le_right))


/-- E.6.5(2): the intrinsic characteristic-normalizer closure C(H,Q) lies in M_H.
Together with `local_intersection_lt`, this includes the strict containment M_H < H. -/
theorem HypothesisE61.characteristic_normalizers_obstruction
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V) :
    ((sylowCentralizer (T : Subgroup G) V).subgroupOf
      (centralizer (U : Set G))).characteristicNormalizerClosure ≤
      M.subgroupOf (centralizer (U : Set G)) := by
  let H := centralizer (U : Set G)
  let Q := sylowCentralizer (T : Subgroup G) V
  have hQH : Q ≤ H := inf_le_right.trans (Subgroup.centralizer_le hU.1)
  have hQp : IsPGroup 2 Q := T.isPGroup'.to_le inf_le_left
  apply (characteristicNormalizerClosure_le_iff _ _).mpr
  intro D hD hDne
  let _ := hD
  let E := (D.map (Q.subgroupOf H).subtype).map H.subtype
  have hEp : IsPGroup 2 E :=
    ((hQp.comap_subtype.to_subgroup D).map _).map _
  have hEne : E ≠ ⊥ := by
    intro he
    exact hDne ((D.map_eq_bot_iff_of_injective
      (f := H.subtype.comp (Q.subgroupOf H).subtype)
      ((H.subtype_injective).comp (Q.subgroupOf H).subtype_injective)).mp
        (by simpa only [E, map_map] using he))
  have hn : normalizer (Q : Set G) ≤ normalizer (E : Set G) := by
    simpa only [map_subgroupOf_eq_of_le hQH] using
      normalizer_le_normalizer_characteristic_map H.subtype H.subtype_injective
        (Q.subgroupOf H) D
  have hbound := normalizer_le_of_unique_maximalTwoLocal h.unique hEp hEne
    (inf_le_right.trans hn)
  intro x hx
  exact hbound ((le_normalizer_map H.subtype) (mem_map_of_mem H.subtype hx))

end CFSG.Quasithin.ChapterE.Section06
