module

public import Stellmacher.Recognition.NormalEightSeparatedTransport
public import Stellmacher.Recognition.SimpleInvolutionFusion
public import Theory.GroupTheory.PGroup.NormalFourFusion
public import Theory.GroupTheory.NormalFourWeakClosureClass
public import Theory.GroupTheory.CoprimeCentralizerConjugate

/-!
# Returning fours in the separated case

Weak closure confines returning conjugates of the central involution to the
normal four. Separation and Z-star contradict this, producing a distinct
returning four. The local odd-core factorization controls returning conjugates
through noncentral involutions. Together with central-omega transport, this
makes the two fours disjoint; the centralizer transport argument makes them
commute.

Source: Janko–Thompson, Math. Z. 113 (1970), §6, first half of printed p.395.
Only normal elementary subgroups are bounded.
-/

namespace Stellmacher.Recognition.NormalEightSeparatedReturning

open Subgroup NormalFourCentralOmegaTwo NormalEightSeparatedFusion
open NormalEightSeparatedTransport

variable {G : Type*} [Group G] [Finite G]

/-- Z-star excludes weak closure of the separated normal four. -/
public theorem exists_distinct_returning_conjugate_four [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hno : ¬ ∃ B : Subgroup S, B.Normal ∧ IsElementaryAbelian 2 B ∧ 8 ≤ Nat.card B)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (z : S) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (hsep : Separated S W z) :
    ∃ g : G,
      (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
        (S : Subgroup G) ∧
      (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≠
        W.map (S : Subgroup G).subtype := by
  classical
  by_contra hnone
  have hweak (g : G)
      (hg : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
        (S : Subgroup G)) :
      (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom =
        W.map (S : Subgroup G).subtype := by
    by_contra hne
    exact hnone ⟨g, hg, hne⟩
  obtain ⟨t, htz, hzt⟩ := exists_distinct_isConj_in_sylow hns S z hz
  exact htz (hsep t
    (S.mem_four_of_isConj_of_weakly_closed_of_no_normal_eight
      hno hZ A hA W hW hweak z t hzC hz hzt) hzt)

/-- The local factorization fixes returning conjugates whose conjugator
centralizes a noncentral involution of the four. -/
public theorem conjugate_four_eq_of_mem_involution_centralizer
    (S : Sylow 2 G) (W : Subgroup S) [IsElementaryAbelian 2 W]
    (hfactor : CentralizerFactorization S W)
    (i : S) (hiW : i ∈ W) (hi : orderOf i = 2) (hiC : i ∉ center S)
    (g : G) (hg : g ∈ centralizer ({(i : G)} : Set G))
    (hreturn : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (S : Subgroup G)) :
    (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom =
      W.map (S : Subgroup G).subtype := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := centralizer ({(i : G)} : Set G)
  let W₀ := W.map (S : Subgroup G).subtype
  let WC := W₀.subgroupOf C
  let P := (S : Subgroup G).subgroupOf C
  let gC : C := ⟨g, hg⟩
  have hWC : W₀ ≤ C := by
    rintro w ⟨a, ha, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (W.le_centralizer ha i hiW).symm)
  have hWP : WC ≤ P := fun _ hx => (map_subtype_le W) hx
  have hconjP : WC.map (MulAut.conj gC).toMonoidHom ≤ P := by
    rintro x ⟨w, hw, rfl⟩
    exact hreturn (mem_map_of_mem (MulAut.conj g).toMonoidHom hw)
  have heq := map_conj_eq_of_coprime_centralizer_supplement WC (pPrimeCore 2 C) P
    pPrimeCore_coprime_card (hfactor i hiW hi hiC)
    (S.isPGroup'.comap_of_injective C.subtype C.subtype_injective) hWP gC hconjP
  have hmaps : (WC.map (MulAut.conj gC).toMonoidHom).map C.subtype =
      (WC.map C.subtype).map (MulAut.conj g).toMonoidHom := by
    rw [map_map, map_map]
    rfl
  have hout := congrArg (Subgroup.map C.subtype) heq
  rw [hmaps, map_subgroupOf_eq_of_le hWC] at hout
  exact hout


private theorem central_involution_eq
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (z i : S) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (hiC : i ∈ center S) (hi : orderOf i = 2) : i = z := by
  let Z := centralOmega S
  let : IsCyclic Z := isCyclic_of_prime_card ((card_centralOmega S).trans hZ)
  have hzZ : (z : G) ∈ Z := by
    rw [show Z = zpowers (z : G) from centralOmega_eq_zpowers S hZ z hzC hz]
    exact mem_zpowers _
  have hiZ : (i : G) ∈ Z := by
    rw [show Z = zpowers (i : G) from centralOmega_eq_zpowers S hZ i hiC hi]
    exact mem_zpowers _
  have heq := IsCyclic.eq_of_orderOf_eq_two
    (x := (⟨(i : G), hiZ⟩ : Z)) (y := (⟨(z : G), hzZ⟩ : Z))
    (by simpa only [← orderOf_coe] using (orderOf_coe i).trans hi)
    (by simpa only [← orderOf_coe] using (orderOf_coe z).trans hz)
  exact Subtype.ext (congrArg (fun a : Z => (a : G)) heq)

/-- Distinct returning conjugates in the separated case are disjoint.
A common noncentral involution adjusts the conjugator into its centralizer;
the odd-core factorization then fixes the returning four. -/
public theorem disjoint_of_distinct_returning_conjugate_four
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(fourImage S W).Normal]
    (z : S) (hzW : z ∈ W) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (hsep : Separated S W z) (hfactor : CentralizerFactorization S W)
    (g : G)
    (hVS : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (S : Subgroup G))
    (hne : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≠
      W.map (S : Subgroup G).subtype) :
    Disjoint (W.map (S : Subgroup G).subtype)
      ((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom) := by
  let W₀ := W.map (S : Subgroup G).subtype
  let V := W₀.map (MulAut.conj g).toMonoidHom
  apply disjoint_iff.mpr
  apply eq_bot_iff.mpr
  intro x hx
  change x = 1
  by_contra hx1
  obtain ⟨u, hu, rfl⟩ := hx.1
  obtain ⟨_, ⟨i, hiW, rfl⟩, hgi⟩ := hx.2
  change (MulAut.conj g) (i : G) = (u : G) at hgi
  have hu1 : u ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hi1 : i ≠ 1 := by
    intro h
    have hh : (u : G) = 1 := hgi.symm.trans (by simp [h])
    exact hu1 (Subtype.ext hh)
  have hu2 : orderOf u = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu) hu1
  have hi2 : orderOf i = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) i hiW) hi1
  have huz : u ≠ z := by
    intro h
    apply hne
    apply conjugate_four_eq_of_mem_central_involution S hno hZ W hW hunique
      g hVS z hzC hz
    rw [← h]
    exact mem_map.mpr ⟨i, mem_map_of_mem _ hiW, hgi⟩
  have hiz : i ≠ z := by
    intro h
    apply huz
    apply hsep u hu
    rw [h] at hgi
    exact isConj_iff.mpr ⟨g, hgi⟩
  have huC : u ∉ center S := fun h => huz (central_involution_eq S hZ z u hzC hz h hu2)
  obtain ⟨s, hs⟩ := isConj_iff.mp
    (isConj_of_mem_normal_four_of_ne_central_involution W hW
      (four_not_le_center_of_card_omega_one_center_eq_two hZ W hW)
      z u i hzW hzC (by intro h; simp [h] at hz) hu hiW hu1 hi1 huz hiz)
  let k : G := g * (s : G)
  have hku : (MulAut.conj k) (u : G) = u := by
    calc
      _ = (MulAut.conj g) ((MulAut.conj (s : G)) (u : G)) := by
        simp [k, MulAut.conj_apply, mul_assoc]
      _ = (MulAut.conj g) (i : G) := congrArg (MulAut.conj g) (congrArg Subtype.val hs)
      _ = u := hgi
  have hWN : (S : Subgroup G) ≤ normalizer (W₀ : Set G) := by
    simpa only [W.normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      W.le_normalizer_map (S : Subgroup G).subtype
  have hWs : W₀.map (MulAut.conj (s : G)).toMonoidHom = W₀ :=
    mem_normalizer_iff_map_conj_eq.mp (hWN s.property)
  have hmap : W₀.map (MulAut.conj k).toMonoidHom = V := by
    have hcomp : (MulAut.conj k).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp (MulAut.conj (s : G)).toMonoidHom := by
      ext y
      simp [k, MulAut.conj_apply, mul_assoc]
    rw [hcomp, ← map_map, hWs]
  exact hne (hmap.symm.trans
    (conjugate_four_eq_of_mem_involution_centralizer S W hfactor u hu hu2 huC k
      (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hku))
      (hmap ▸ hVS)))

/-- The separated case supplies a disjoint commuting returning four. -/
public theorem exists_disjoint_commuting_returning_conjugate_four [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hno : ¬ ∃ B : Subgroup S, B.Normal ∧ IsElementaryAbelian 2 B ∧ 8 ≤ Nat.card B)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(fourImage S W).Normal]
    (z : S) (hzW : z ∈ W) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (hsep : Separated S W z)
    (hfactor : CentralizerFactorization S W) (hcontrol : LocalCentralizerControl S W) :
    ∃ g : G,
      (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
        (S : Subgroup G) ∧
      Disjoint (W.map (S : Subgroup G).subtype)
        ((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom) ∧
      (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
        centralizer (W.map (S : Subgroup G).subtype : Set G) := by
  obtain ⟨g, hg, hne⟩ := exists_distinct_returning_conjugate_four
    hns S A hA hno hZ W hW z hzC hz hsep
  exact ⟨g, hg, disjoint_of_distinct_returning_conjugate_four
    S hno hZ W hW hunique z hzW hzC hz hsep hfactor g hg hne,
    returning_conjugate_le_centralizer S hno hZ W hW hunique hcontrol g hg⟩

end Stellmacher.Recognition.NormalEightSeparatedReturning
