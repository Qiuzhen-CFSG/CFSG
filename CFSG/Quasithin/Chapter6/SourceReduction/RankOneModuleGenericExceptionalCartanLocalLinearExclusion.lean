module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalLinearFour
public import Theory.GroupTheory.WreathedCyclicHall
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
/-!
# Excluding the original odd-prime linear ternary containers

The original residual recognition forces parameter five. In the literal
quotient Y/O₂(Y), intersect the full Cartan--Sylow join with its normal
containing component. This intersection is solvable, has wreathed Sylow
two-subgroups and a cyclic odd Hall subgroup. Its central two-core supplies
a characteristic line or four-group. The line fixes the residual involution.

If three divides the intersection order, the original cubic normalizes its
odd Hall subgroup and lies in it, since nine does not divide |SL₃(5)|.
The characteristic four then contradicts the proved original-cubic
calculation. If three does not divide the intersection order, wreathed fusion
supplies a cyclic normal odd complement and fixes the same involution.
This handles the whole actor, including any outer action, without assuming
that the original cubic normalizes the chosen Sylow subgroup.

The exact involution-centralizer preimage lifts normalization to the
original residual. Both PSL₃(p) and SL₃(p), for odd prime p, are excluded.
The sieve and Chapter12 application retain all original inputs; remaining
component rows and module alternatives are separate unfinished branches.

Source: Aschbacher--Smith 5.1.13, printed p.636, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels

private theorem linear_five_structure {K : Type*} [Group K] [Finite K]
    (hm : ClassicalGroup.IsPSL K 3 5 ∨ IsSL K 3 5) :
    (∀ S : Sylow 2 K, Nonempty (S ≃* WreathedThirtyTwo)) ∧ ¬ 9 ∣ Nat.card K := by
  have model : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 5 ∧ Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 3) F) := by
    rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | hm
    · let ep := Matrix.SL3.equivProjectiveOfCenterEqBot F
        ((Matrix.SL3.center_eq_bot_iff_card_mod_three F).mpr (by rw [hF]; decide))
      exact ⟨F,inferInstance,inferInstance,hF,⟨e.trans ep.symm⟩⟩
    · exact hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := model
  constructor
  · intro S
    let ep := Matrix.SL3.equivProjectiveOfCenterEqBot F
      ((Matrix.SL3.center_eq_bot_iff_card_mod_three F).mpr (by rw [hF]; decide))
    let eC := e.trans ep
    exact ⟨(eC.subgroupMap (S : Subgroup K)).trans
      (Theory.SpecificGroups.Classical.SylowMarkedSL2.psl3_five_sylow_wreath hF
        (S.mapSurjective eC.surjective)).some⟩
  · rw [Nat.card_congr e.toEquiv,
      Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF]
    norm_num

private theorem linear_cyclic_actor_centralizes
    {Y : Type*} [Group Y] [Finite Y]
    (K D B : Subgroup Y) [K.Normal] (hBK : B ≤ K)
    (P : Sylow 2 Y)
    (hW : ∀ S : Sylow 2 K, Nonempty (S ≃* WreathedThirtyTwo))
    (h9 : ¬ 9 ∣ Nat.card K)
    (hs : Group.IsSolvable (D ⊔ (P : Subgroup Y) : Subgroup Y))
    (hD : IsCyclic D) (ho : Odd (Nat.card D))
    (hperm : (D : Set Y) * (P : Set Y) = (P : Set Y) * (D : Set Y))
    (hB : Nat.card B = 3) (hBD : B ≤ normalizer (D : Set Y))
    (hno : ∀ E : Subgroup Y, E ≤ K ⊓ (P : Subgroup Y) →
      IsElementaryAbelian 2 E → Nat.card E = 4 → ¬ B ≤ normalizer (E : Set Y))
    (z : Y) (hzK : z ∈ K) (hzP : z ∈ P) (hz2 : orderOf z = 2)
    (hPz : (P : Subgroup Y) ≤ centralizer ({z} : Set Y)) :
    D ≤ centralizer ({z} : Set Y) := by
  let J := (D ⊔ (P : Subgroup Y)).subgroupOf K
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_normal K
  have hSJ : (S : Subgroup K) ≤ J := by rw [hS]; exact comap_mono le_sup_right
  let f : J →* (D ⊔ (P : Subgroup Y) : Subgroup Y) :=
    { toFun := fun x => ⟨x.val.val,x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hJs : Group.IsSolvable J := by
    let := hs
    apply Group.isSolvable_of_isSolvable_injective (f := f)
    intro x y hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (D ⊔ (P : Subgroup Y) : Subgroup Y) => (z : Y)) hh
  let DK := D.subgroupOf K
  have hDJ : DK ≤ J := comap_mono le_sup_left
  let E := DK.subgroupOf J
  let := hD
  let : IsCyclic DK := isCyclic_of_injective (K.subtype.subgroupComap D) (by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : D => (z : Y)) he)))
  let : IsCyclic E := isCyclic_of_injective
    (subgroupOfEquivOfLe hDJ).toMonoidHom (subgroupOfEquivOfLe hDJ).injective
  have hcop : Nat.Coprime (Nat.card D) (Nat.card P) := by
    obtain ⟨k,hk⟩ := P.isPGroup'.exists_card_eq
    rw [hk]
    exact ho.coprime_two_right.pow_right k
  have hEc : Nat.card E = Nat.card (D ⊓ K : Subgroup Y) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDJ).toEquiv]
    change Nat.card (D.subgroupOf K) = _
    rw [←inf_subgroupOf_right D K,Nat.card_congr
      (subgroupOfEquivOfLe (show D ⊓ K ≤ K from inf_le_right)).toEquiv]
  have hSc : Nat.card S = Nat.card ((P : Subgroup Y) ⊓ K : Subgroup Y) := by
    rw [hS,←inf_subgroupOf_right (P : Subgroup Y) K,Nat.card_congr
      (subgroupOfEquivOfLe (show (P : Subgroup Y) ⊓ K ≤ K from inf_le_right)).toEquiv]
  have hJc : Nat.card J = Nat.card E * Nat.card S := by
    rw [hEc,hSc]
    exact card_subgroupOf_sup_of_coprime_permutable D P K hcop hperm
  have hi : E.index = Nat.card S := by
    have hh := E.card_mul_index
    rw [hJc] at hh
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hh
  have hEodd : Odd (Nat.card E) := by
    rw [hEc]
    exact ho.of_dvd_nat (card_dvd_of_le (show D ⊓ K ≤ D from inf_le_left))
  have hHall : IsHallSubgroup OddHall.oddPrimes E := by
    refine ⟨?_,?_⟩
    · intro p hp he
      exact hEodd.not_two_dvd_nat (he ▸ hp)
    · intro p hp hp2
      rw [hi] at hp
      obtain ⟨k,hk⟩ := S.isPGroup'.exists_card_eq
      rw [hk] at hp
      exact hp2 (Nat.prime_eq_prime_of_dvd_pow p.property Nat.prime_two hp)
  have hBKD : B.subgroupOf K ≤ normalizer (E.map J.subtype : Set K) := by
    rw [map_subgroupOf_eq_of_le hDJ]
    intro b hb
    apply mem_normalizer_iff.mpr
    intro d
    exact mem_normalizer_iff.mp (hBD hb) d.val
  have hnoK : ∀ F : Subgroup K, F ≤ (S : Subgroup K) → IsElementaryAbelian 2 F →
      Nat.card F = 4 → ¬ B.subgroupOf K ≤ normalizer (F : Set K) := by
    intro F hFS hFA hF4 hn
    let := hFA
    apply hno (F.map K.subtype) ?_ IsElementaryAbelian.map_subtype
      (by rwa [card_map_of_injective K.subtype_injective])
    · have hh := (map_mono hn).trans (le_normalizer_map K.subtype)
      rwa [map_subgroupOf_eq_of_le hBK] at hh
    · rintro x ⟨y,hy,rfl⟩
      refine ⟨y.property,?_⟩
      have hh := hFS hy
      rw [hS] at hh
      exact hh
  let zK : K := ⟨z,hzK⟩
  have hzS : zK ∈ S := by change zK ∈ (S : Subgroup K); rw [hS]; exact hzP
  let zS : S := ⟨zK,hzS⟩
  have hzSc : zS ∈ center S := by
    apply mem_center_iff.mpr
    intro s
    apply Subtype.ext
    apply Subtype.ext
    have hh : s.val ∈ (S : Subgroup K) := s.property
    rw [hS] at hh
    exact mem_centralizer_singleton_iff.mp (hPz hh)
  intro d hdD
  let a : MulAut K := MulAut.conjNormal d
  have hJ : J.map a.toMonoidHom = J := by
    ext x
    rw [mem_map_equiv]
    change (a.symm x).val ∈ D ⊔ (P : Subgroup Y) ↔ x.val ∈ D ⊔ (P : Subgroup Y)
    rw [MulAut.conjNormal_symm_apply]
    exact ((mem_normalizer_iff''.mp
      ((D ⊔ (P : Subgroup Y)).le_normalizer (show d ∈ D ⊔ (P : Subgroup Y) from (show D ≤ D ⊔ (P : Subgroup Y) from le_sup_left) hdD))) x.val).symm
  have he := WreathedCyclicHall.automorphism_fix_of_cubic_normalizer h9 J hJs E hHall
    (B.subgroupOf K) ((Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv).trans hB)
    hBKD S (hW S).some hSJ hnoK zS
    ((orderOf_coe zS).symm.trans ((orderOf_coe zK).symm.trans hz2)) hzSc a hJ
  exact mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp (congrArg K.subtype he))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The entire original Cartan intersection normalizes the original residual
in both odd-prime linear containing rows, including the central cover. -/
theorem linear_ternary_cartan_normalizes_residual
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hCn : C.Normal)
    (hRC : residual H ≤ C.map Y.subtype)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨ IsSL (C ⧸ pCore 2 C) 3 p) :
    A ⊓ Y ≤ normalizer (residual H : Set G) := by
  have hternary : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
      ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
      IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p :=
    hm.elim Or.inl (fun hh => .inr (.inr (.inl hh)))
  obtain ⟨hp5,hfour,_⟩ := residual_section_of_odd_ternary h hH hgen hY.2 hR C hC hRC hp ho hternary
  subst p
  let q := QuotientGroup.mk' (pCore 2 Y)
  let Rbar := ((residual H).subgroupOf Y).map q
  let Cbar := C.map q
  let Dbar := (A.subgroupOf Y).map q
  let Bbar := (B.subgroupOf Y).map q
  have hTY := hH.1.1.2.trans hY.2
  let P := (T.subtype hTY).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  have hRC' : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  let : Cbar.Normal := Subgroup.Normal.map hCn q (QuotientGroup.mk'_surjective _)
  let e := (cComponentTwoCoreQuotientEquiv hC).symm
  have hmC : ClassicalGroup.IsPSL Cbar 3 5 ∨ IsSL Cbar 3 5 := by
    rcases hm with hm | ⟨F,_,_,hF,⟨a⟩⟩
    · exact .inl (hm.of_mulEquiv e)
    · exact .inr ⟨F,inferInstance,inferInstance,hF,⟨e.trans a⟩⟩
  obtain ⟨hW,h9⟩ := linear_five_structure hmC
  have hA5 : Nonempty ((residual H ⧸ pCore 2 (residual H)) ≃* alternatingGroup (Fin 5)) := by
    let e := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
    let eq := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hfour
    exact ⟨eq.symm.trans (a.trans
      (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)⟩
  have hBc := right_hall_card_three_of_residual_A5 h hH hgen c hA5
  have hBY := (c.right_le.trans inf_le_right).trans hY.2
  have hBbar : Nat.card Bbar = 3 := by
    have hd : Nat.card Bbar ∣ 3 := by
      have hd := card_map_dvd (B.subgroupOf Y) q
      rwa [Nat.card_congr (subgroupOfEquivOfLe hBY).toEquiv,hBc] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with hb | hb
    · have hz : Bbar = ⊥ := eq_bot_of_card_eq _ hb
      have hle : B.subgroupOf Y ≤ pCore 2 Y := by
        simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
      obtain ⟨k,hk⟩ := (pCore_isPGroup.to_le hle).exists_card_eq
      rw [Nat.card_congr (subgroupOfEquivOfLe hBY).toEquiv,hBc] at hk
      have hh : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow (by rw [←hk])
      norm_num at hh
    · exact hb
  have hBR : Bbar ≤ Rbar := map_mono (comap_mono (Global.right_cartan_le_residual c))
  have hBC : Bbar ≤ Cbar := by
    apply hBR.trans (map_mono ?_)
    have hh := comap_mono (f := Y.subtype) hRC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have hBD : Bbar ≤ normalizer (Dbar : Set (Y ⧸ pCore 2 Y)) := by
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    intro b hb
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (c.right_normalizes_left hb) (a : G)
  obtain ⟨z,hz,hz2,hu,hzT,hTC,_,_,hnormY⟩ :=
    residual_involution_of_odd_ternary h hH hgen hY.2 hR C hC hCn hRC hp ho hternary
  let : IsCyclic A := (c.left_cyclic_and_card h.sylow_normalizes h.linear).1
  let : IsCyclic (A.subgroupOf Y) := isCyclic_of_injective (Y.subtype.subgroupComap A) (by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : A => (z : G)) he)))
  have hcyc : IsCyclic Dbar := isCyclic_of_surjective
    (q.subgroupMap (A.subgroupOf Y)) (q.subgroupMap_surjective _)
  have hoA : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have hoD : Odd (Nat.card Dbar) := by
    apply Odd.of_dvd_nat _ (card_map_dvd _ q)
    rw [←inf_subgroupOf_right A Y,Nat.card_congr
      (subgroupOfEquivOfLe (show A ⊓ Y ≤ Y from inf_le_right)).toEquiv]
    exact hoA.of_dvd_nat (card_dvd_of_le (show A ⊓ Y ≤ A from inf_le_left))
  have hfix := linear_cyclic_actor_centralizes Cbar Dbar Bbar hBC P hW h9
    (h.cartan_sylow_action_isSolvable c hTY q) hcyc hoD
    (c.image_intersection_permutes_sylow h.sylow_normalizes hTY q) hBbar hBD
    (linear_ternary_right_hall_not_normalizes_sylow_four h hH hgen c hY hR C hC hCn hRC
      hp ho hm z hz hz2 hu hzT hTC)
    z (map_mono hRC' hz) hzT hz2 hTC
  intro a ha
  have hh : (⟨a,ha.2⟩ : Y) ∈ (centralizer ({z} : Set (Y ⧸ pCore 2 Y))).comap q :=
    hfix (mem_map_of_mem q (show (⟨a,ha.2⟩ : Y) ∈ A.subgroupOf Y from ha.1))
  rw [←hnormY] at hh
  exact hh
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
/-- The original sieve excludes every odd-prime ternary containing row,
retaining the same seed, normal component and all earlier restrictions. -/
theorem localCartan_escape_seed_no_odd_ternary
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        C.Normal ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
            ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
            IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p)) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,hU,hOdd⟩ :=
    localCartan_escape_seed_nonunitary_reduction h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,?_⟩
  intro p hp ho hm
  have hlin : ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨ IsSL (C ⧸ pCore 2 C) 3 p) := by
    intro hl
    have he := (hOdd p hp ho hl).1
    exact hescape (LocalSieve.linear_ternary_cartan_normalizes_residual h hH hgen c hY
      (he ▸ hKL) C hC hCn (he ▸ hKC) hp ho hl)
  rcases hm with hl | hu | hl | hu
  · exact hlin (.inl hl)
  · exact hU p hp ho (.inl hu)
  · exact hlin (.inr hl)
  · exact hU p hp ho (.inr hu)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
