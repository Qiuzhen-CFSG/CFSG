module

public import CFSG.Quasithin.ChapterF.Section01.SourceCartan.Defs
public import CFSG.Quasithin.ChapterF.Section01.SourceIncidence
public import Theory.GroupTheory.Hall.Conjugacy

/-!
# Compatible Cartan complements before the commutation argument

Source: Aschbacher–Smith, F.1.3(5), printed p.260. Choose an odd Hall
subgroup of the finite solvable common Borel, and intersect it with the two
normal local Borels. Hall conjugacy and the rank-one Borel theorems make
the intersections abelian complements. Normality gives their mutual
normalization. The product index formula shows their join is Hall in B:
its index in B₁B₂ and the index of B₁B₂ in B both divide |S|.

The joint subgroup is an actual complement to S. Its commutativity remains
the separate rank-one automorphism step, and is not claimed here.
-/

public section
open Subgroup Subgroup.OddHall
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
private theorem localSylow_subgroupOf_borel (i : Fin 2) :
    (S ⊓ L i).subgroupOf (borel (L i) S) = S.subgroupOf (borel (L i) S) := by
  ext x
  exact and_iff_left (borel_le _ _ x.property)

private theorem localHall_complement (h : HypothesisF11 L S) (i : Fin 2)
    {D : Subgroup G} (hd : IsHallSubgroup oddPrimes (D.subgroupOf (borel (L i) S))) :
    ((S ⊓ L i).subgroupOf (borel (L i) S)).IsComplement'
      (D.subgroupOf (borel (L i) S)) := by
  let := h.finite_local i
  let : Finite (borel (L i) S) := Finite.of_injective (inclusion (borel_le _ _)) (inclusion_injective _)
  rw [localSylow_subgroupOf_borel]
  exact sylow_complement_of_hall
    (h.S_isP.comap_subtype.toSylow (h.local_borel_odd_index i)) hd

private theorem localHall_abelian (h : HypothesisF11 L S) (i : Fin 2)
    {D : Subgroup G} (hD : D ≤ borel (L i) S)
    (hd : IsHallSubgroup oddPrimes (D.subgroupOf (borel (L i) S))) :
    IsMulCommutative D := by
  let := h.finite_local i
  let : Finite (borel (L i) S) := Finite.of_injective (inclusion (borel_le _ _)) (inclusion_injective _)
  let : Finite (S ⊓ L i : Subgroup G) := Finite.of_injective (inclusion inf_le_right) (inclusion_injective _)
  obtain ⟨E, hE, ho, ha, _, hs⟩ := (h.rankOneBorelFacts i).abelian_odd_complement
  let : Finite E := Finite.of_injective (inclusion hE) (inclusion_injective _)
  let := ha
  have he : IsHallSubgroup oddPrimes (E.subgroupOf (borel (L i) S)) :=
    oddHall_of_normalized_sup (h.S_isP.of_injective (inclusion inf_le_left) (inclusion_injective _))
      ho (hE.trans inf_le_right) hs
  obtain ⟨g, hg⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable
    (h.rankOneBorelFacts i).solvable he hd
  have hc : IsMulCommutative (D.subgroupOf (borel (L i) S)) := by
    rw [hg]
    infer_instance
  let := hc
  let e := subgroupOfEquivOfLe hD
  exact ⟨⟨fun x y => e.symm.injective (by simp only [map_mul, mul_comm'])⟩⟩

/-- The compatible Hall complements exist under the exact source hypotheses.
Joint commutativity is not included. -/
theorem HypothesisF11.exists_compatibleCartans (h : HypothesisF11 L S) :
    Nonempty (CompatibleCartans L S) := by
  classical
  let B := commonBorel L S
  let := h.finite_commonBorel
  let := h.finite_S
  let _ : MulDistribMulAction Unit B := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_one _ := rfl
    smul_mul _ _ _ := rfl }
  obtain ⟨H, hH, _⟩ := exists_isHallSubgroup_isInvariant
    (G := B) (A := Unit) h.commonBorel_solvable (by simp) oddPrimes
  let D := H.map B.subtype
  have hDB : D ≤ B := map_subtype_le _
  let : Finite D := Finite.of_injective (inclusion hDB) (inclusion_injective _)
  have hD : IsHallSubgroup oddPrimes (D.subgroupOf B) := by
    have he : D.subgroupOf B = H := comap_map_eq_self_of_injective B.subtype_injective H
    rwa [he]
  have hoddD : Nat.Coprime 2 (Nat.card D) := by
    apply Nat.prime_two.coprime_iff_not_dvd.mpr
    intro hd
    apply hD.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ _ rfl
    rwa [Nat.card_congr (subgroupOfEquivOfLe hDB).toEquiv]
  let Di : Fin 2 → Subgroup G := fun i => D ⊓ borel (L i) S
  have hDi (i : Fin 2) : Di i ≤ borel (L i) S := inf_le_right
  have hDiD (i : Fin 2) : Di i ≤ D := inf_le_left
  have hDiB (i : Fin 2) : Di i ≤ B := (hDi i).trans (borel_le_commonBorel i)
  have hhall (i : Fin 2) : IsHallSubgroup oddPrimes ((Di i).subgroupOf (borel (L i) S)) := by
    dsimp [Di]
    rw [inf_subgroupOf_right]
    exact hall_restrict_of_normalizes hD hDB (borel_le_commonBorel i)
      (hDB.trans (h.commonBorel_normalizes_borel i))
  have hcomp (i : Fin 2) := localHall_complement h i (hhall i)
  have hloc (i : Fin 2) : (S ⊓ L i) ⊔ Di i = borel (L i) S := by
    have he := congrArg (Subgroup.map (borel (L i) S).subtype) (hcomp i).sup_eq_top
    simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le (localSylow_le_borel _ _),
      map_subgroupOf_eq_of_le (hDi i), ← MonoidHom.range_eq_map, range_subtype] using he
  have hnorm (i : Fin 2) : Di i ≤ normalizer (Di (other i) : Set G) :=
    (le_inf ((hDiD i).trans D.le_normalizer)
      ((hDiB i).trans (h.commonBorel_normalizes_borel (other i)))).trans
        inf_normalizer_le_normalizer_inf
  let C := borel (L 0) S ⊔ borel (L 1) S
  let U := (S ⊓ L 0) ⊔ (S ⊓ L 1)
  let K := Di 0 ⊔ Di 1
  have hUS : U ≤ S := sup_le inf_le_left inf_le_left
  have hKD : K ≤ D := sup_le (hDiD 0) (hDiD 1)
  have hKC : K ≤ C := sup_le ((hDi 0).trans le_sup_left) ((hDi 1).trans le_sup_right)
  have hCB : C ≤ B := le_sup_left
  let : Finite K := Finite.of_injective (inclusion hKD) (inclusion_injective _)
  have hC : U ⊔ K = C := by
    dsimp [C, U, K]
    rw [← hloc 0, ← hloc 1]
    ac_rfl
  have hKN : K ≤ normalizer (U : Set G) :=
    ((le_inf (h.commonBorel_normalizes_localSylow 0) (h.commonBorel_normalizes_localSylow 1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)) |>.trans' (hKD.trans hDB)
  have hSN : S ≤ normalizer (C : Set G) :=
    (le_inf (h.S_normalizes_borel 0) (h.S_normalizes_borel 1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hKidx : K.relIndex C ∣ Nat.card S := by
    rw [← hC, relIndex_sup_of_normalizes U K hKN]
    exact (relIndex_dvd_card (H := K) (K := U)).trans (card_dvd_of_le hUS)
  have hCidx : C.relIndex B ∣ Nat.card S := by
    change C.relIndex (C ⊔ S) ∣ Nat.card S
    rw [relIndex_normalized_sup C S hSN]
    exact relIndex_dvd_card C S
  have hKhall : IsHallSubgroup oddPrimes (K.subgroupOf B) := by
    refine ⟨?_, ?_⟩
    · intro p hp he
      have hp2 : p.val = 2 := he
      rw [Nat.card_congr (subgroupOfEquivOfLe (hKD.trans hDB)).toEquiv, hp2] at hp
      exact Nat.prime_two.coprime_iff_not_dvd.mp hoddD (hp.trans (card_dvd_of_le hKD))
    · intro p hp hp2
      change p.val ∣ K.relIndex B at hp
      rw [← relIndex_mul_relIndex K C B hKC hCB] at hp
      have hpS : p.val ∣ Nat.card S :=
        (p.property.dvd_mul.mp hp).elim (fun ha => ha.trans hKidx) (fun hb => hb.trans hCidx)
      obtain ⟨n, hn⟩ := h.S_isP.exists_card_eq
      rw [hn] at hpS
      exact hp2 (Nat.prime_eq_prime_of_dvd_pow p.property Nat.prime_two hpS)
  refine ⟨⟨Di, hDi, ?_, ?_, hhall, hcomp, hnorm, hKhall, ?_⟩⟩
  · intro i
    exact hoddD.of_dvd_right (card_dvd_of_le (hDiD i))
  · intro i
    exact localHall_abelian h i (hDi i) (hhall i)
  · obtain ⟨T, hT⟩ := h.sylow_commonBorel
    have hTS : (T : Subgroup B) = S.subgroupOf B := by
      apply map_injective B.subtype_injective
      rw [map_subgroupOf_eq_of_le (show S ≤ B from le_sup_right)]
      exact hT
    rw [← hTS]
    exact sylow_complement_of_hall T hKhall
end CFSG.Quasithin.ChapterF.Source
