module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalOddTernaryInvolution
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.CyclicHall
public import Theory.SpecificGroups.SU3.FiveSylow
public import Theory.GroupTheory.CoprimeProductIntersection

/-!
# Excluding both original odd-prime unitary Cartan containers

The checked odd-ternary recognition forces parameter five and identifies
the literal residual image in Y/O₂(Y) with SL₂(5). Intersect the full
original Cartan--Sylow join with its normal containing component. The
intersection is solvable, contains the complete semidihedral Sylow, and
has a cyclic odd Hall subgroup obtained from the original left Cartan.
Its central involution is therefore characteristic. Recovering the marked
SL₂(5) from that involution proves normalization by the whole Cartan actor.

Perfect normalizer lifting through the same O₂(Y) gives normalization of
the original residual, contradicting escape. The special unitary cover
retains its actual central kernel throughout. This closes both PSU₃(p)
and SU₃(p), for odd prime p, in the original sieve. The linear ternary,
remaining component and inverted-cubic cases are still open.

Source: Aschbacher--Smith A.3.21(a) and 5.1.13, printed pp.55,636,
`refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
private theorem generators_of_equiv {Y Z : Type*} [Group Y] [Group Z]
    (e : Y ≃* Z)
    (hg : ∃ a b : Z, orderOf a = 8 ∧ orderOf b = 2 ∧
      b*a*b⁻¹=a^3 ∧ closure ({a,b} : Set Z)=⊤) :
    ∃ a b : Y, orderOf a = 8 ∧ orderOf b = 2 ∧
      b*a*b⁻¹=a^3 ∧ closure ({a,b} : Set Y)=⊤ := by
  obtain ⟨a,b,ha,hb,hab,hgen⟩ := hg
  refine ⟨e.symm a,e.symm b,(e.symm.orderOf_eq a).trans ha,
    (e.symm.orderOf_eq b).trans hb,?_,?_⟩
  · simpa only [map_mul,map_inv,map_pow] using congrArg e.symm hab
  · have hh := congrArg (map e.symm.toMonoidHom) hgen
    rw [MonoidHom.map_closure,map_top_of_surjective _ e.symm.surjective] at hh
    simpa only [Set.image_insert_eq,Set.image_singleton,MulEquiv.coe_toMonoidHom] using hh

private theorem derived_bound_of_equiv {Y Z : Type*} [Group Y] [Group Z]
    (e : Y ≃* Z)
    (hb : ∀ z : Z, orderOf z = 2 →
      Nat.card (commutator (centralizer ({z} : Set Z))) ≤ 120) :
    ∀ z : Y, orderOf z = 2 →
      Nat.card (commutator (centralizer ({z} : Set Y))) ≤ 120 := by
  intro z hz
  have he : (centralizer ({z} : Set Y)).map e.toMonoidHom =
      centralizer ({e z} : Set Z) := by
    simpa only [Set.image_singleton] using map_centralizer_equiv ({z} : Set Y) e
  let a := (e.subgroupMap (centralizer ({z} : Set Y))).trans (MulEquiv.subgroupCongr he)
  have ha : (commutator (centralizer ({z} : Set Y))).map a.toMonoidHom =
      commutator (centralizer ({e z} : Set Z)) := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr a.surjective]
    rfl
  rw [Nat.card_congr ((a.subgroupMap (commutator (centralizer ({z} : Set Y)))).trans
    (MulEquiv.subgroupCongr ha)).toEquiv]
  exact hb (e z) ((e.orderOf_eq z).trans hz)

private theorem unitary_five_structure {Y : Type*} [Group Y] [Finite Y]
    (hm : ClassicalGroup.IsPSU Y 3 5 ∨ Chapter1.Section02.LocalModels.IsSU Y 3 5) :
    (∀ S : Sylow 2 Y, ∃ a b : S, orderOf a = 8 ∧ orderOf b = 2 ∧
      b*a*b⁻¹=a^3 ∧ closure ({a,b} : Set S)=⊤) ∧
    (∀ z : Y, orderOf z = 2 →
      Nat.card (commutator (centralizer ({z} : Set Y))) ≤ 120) := by
  rcases hm with ⟨F,_,_,J,hF,hc,⟨e⟩⟩ | ⟨F,_,_,J,hF,hc,⟨e⟩⟩
  · let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective e e.surjective
    refine ⟨?_,derived_bound_of_equiv e ?_⟩
    · intro S
      exact generators_of_equiv (e.subgroupMap (S : Subgroup Y))
        (BenderSuzuki.MatrixGroups.HermitianForm.FiveSylow.sylow_generators J hF hc
          (S.mapSurjective e.surjective))
    · exact Theory.SpecificGroups.Classical.SylowMarkedSL2.derived_centralizer_bound_of_central_cube_cover
        J.specialToProjective J.specialToProjective_surjective
        J.specialToProjective_ker_le_center
        (fun x hx => congrArg Subtype.val (J.specialToProjective_ker_cube ⟨x,hx⟩))
        (Theory.SpecificGroups.Classical.SylowMarkedSL2.unitary_derived_centralizer_card_le J hF hc)
  · refine ⟨?_,derived_bound_of_equiv e
      (Theory.SpecificGroups.Classical.SylowMarkedSL2.unitary_derived_centralizer_card_le J hF hc)⟩
    intro S
    let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
    let Q := P.mapSurjective J.specialToProjective_surjective
    let a := Sylow.equivOfSurjectiveCoprime J.specialToProjective
      J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left P Q
    exact generators_of_equiv ((e.subgroupMap (S : Subgroup Y)).trans a)
      (BenderSuzuki.MatrixGroups.HermitianForm.FiveSylow.sylow_generators J hF hc Q)

private theorem unitary_cyclic_actor_normalizes
    {Y : Type*} [Group Y] [Finite Y]
    (K R D : Subgroup Y) [K.Normal] (hRK : R ≤ K)
    (P : Sylow 2 Y) (hPR : (P : Subgroup Y) ≤ normalizer (R : Set Y))
    (hm : ClassicalGroup.IsPSU K 3 5 ∨ Chapter1.Section02.LocalModels.IsSU K 3 5)
    (hR : Chapter1.Section02.LocalModels.IsSL R 2 5)
    (hs : Group.IsSolvable (D ⊔ (P : Subgroup Y) : Subgroup Y))
    (hD : IsCyclic D) (ho : Odd (Nat.card D))
    (hperm : (D : Set Y) * (P : Set Y) = (P : Set Y) * (D : Set Y)) :
    D ≤ normalizer (R : Set Y) := by
  let J := (D ⊔ (P : Subgroup Y)).subgroupOf K
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_normal K
  have hSJ : (S : Subgroup K) ≤ J := by rw [hS]; exact comap_mono le_sup_right
  have hSR : (S : Subgroup K) ≤ normalizer (R.subgroupOf K : Set K) := by
    rw [hS,←subgroupOf_normalizer_eq hRK]
    exact comap_mono hPR
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
  obtain ⟨F,_,_,hF,⟨eR⟩⟩ := hR
  obtain ⟨hgens,hbound⟩ := unitary_five_structure hm
  intro d hdD
  let a : MulAut K := MulAut.conjNormal d
  have hJ : J.map a.toMonoidHom = J := by
    ext x
    rw [mem_map_equiv]
    change (a.symm x).val ∈ D ⊔ (P : Subgroup Y) ↔ x.val ∈ D ⊔ (P : Subgroup Y)
    rw [MulAut.conjNormal_symm_apply]
    exact ((mem_normalizer_iff''.mp
      ((D ⊔ (P : Subgroup Y)).le_normalizer (show d ∈ D ⊔ (P : Subgroup Y) from (show D ≤ D ⊔ (P : Subgroup Y) from le_sup_left) hdD))) x.val).symm
  have he := Theory.SpecificGroups.Classical.SylowMarkedSL2.automorphism_preserves_sl2_five_of_cyclic_odd_hall hgens hbound (R.subgroupOf K) J
    ((subgroupOfEquivOfLe hRK).trans eR) hF S hSR hSJ hJs E hHall a hJ
  rw [mem_normalizer_iff_map_conj_eq]
  have hh := congrArg (Subgroup.map K.subtype) he
  rw [map_map,map_subgroupOf_eq_of_le hRK] at hh
  have hf : K.subtype.comp a.toMonoidHom = (MulAut.conj d).toMonoidHom.comp K.subtype := by
    ext x; rfl
  rw [hf,←map_map,map_subgroupOf_eq_of_le hRK] at hh
  exact hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The entire original Cartan intersection normalizes the original residual
in both odd-prime unitary containing rows, including the central cover. -/
theorem odd_unitary_cartan_normalizes_residual
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hCn : C.Normal)
    (hRC : residual H ≤ C.map Y.subtype)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p) :
    A ⊓ Y ≤ normalizer (residual H : Set G) := by
  have hternary : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
      ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
      IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p := by
    rcases hm with hm | hm
    · exact .inr (.inl hm)
    · exact .inr (.inr (.inr hm))
  obtain ⟨hp5,_,hsl⟩ := residual_section_of_odd_ternary h hH hgen hY.2 hR C hC hRC hp ho hternary
  subst p
  let q := QuotientGroup.mk' (pCore 2 Y)
  let Rbar := ((residual H).subgroupOf Y).map q
  let Cbar := C.map q
  let Dbar := (A.subgroupOf Y).map q
  have hTY := hH.1.1.2.trans hY.2
  let P := (T.subtype hTY).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hRC' : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  let : Cbar.Normal := Subgroup.Normal.map hCn q (QuotientGroup.mk'_surjective _)
  let e := (cComponentTwoCoreQuotientEquiv hC).symm
  have hmC : ClassicalGroup.IsPSU Cbar 3 5 ∨ IsSU Cbar 3 5 := by
    rcases hm with hm | ⟨F,_,_,J,hF,hc,⟨a⟩⟩
    · exact .inl (hm.of_mulEquiv e)
    · exact .inr ⟨F,inferInstance,inferInstance,J,hF,hc,⟨e.trans a⟩⟩
  have hPR : (P : Subgroup (Y ⧸ pCore 2 Y)) ≤ normalizer (Rbar : Set (Y ⧸ pCore 2 Y)) := by
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq hRY]
    exact comap_mono (hH.1.1.2.trans (le_normalizer_residual H))
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
  have hnorm := unitary_cyclic_actor_normalizes Cbar Rbar Dbar (map_mono hRC') P hPR hmC hsl
    (h.cartan_sylow_action_isSolvable c hTY q) hcyc hoD
    (c.image_intersection_permutes_sylow h.sylow_normalizes hTY q)
  have hn := map_le_iff_le_comap.mp hnorm
  rw [residual_twoCore_normalizer h.qtke h.sylow_normalizes hH hgen hY.2] at hn
  exact fun a ha => hn (show (⟨a,ha.2⟩ : Y) ∈ A.subgroupOf Y from ha.1)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
/-- The original local-Cartan sieve excludes both odd-prime unitary rows,
retaining the linear rows and every earlier restriction at the same seed
and containing component. -/
theorem localCartan_escape_seed_nonunitary_reduction
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
          ¬ (ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p)) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨ IsSL (C ⧸ pCore 2 C) 3 p) →
          K = residual H ∧ p = 5 ∧
            ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
            IsSL (((residual H).subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))) 2 5 ∧
            Nat.card B = 3 ∧
            let q := QuotientGroup.mk' (pCore 2 Y)
            let Rbar := ((residual H).subgroupOf Y).map q
            let Cbar := C.map q
            let Tbar := ((T : Subgroup G).subgroupOf Y).map q
            ∃ z : Y ⧸ pCore 2 Y,
              z ∈ Rbar ∧ orderOf z = 2 ∧
              (∀ x : Y ⧸ pCore 2 Y, x ∈ Rbar → orderOf x = 2 → x = z) ∧
              z ∈ Tbar ∧
              Tbar ⊔ (B.subgroupOf Y).map q ≤ centralizer ({z} : Set (Y ⧸ pCore 2 Y)) ∧
              Rbar = ⁅Cbar ⊓ centralizer ({z} : Set (Y ⧸ pCore 2 Y)),
                Cbar ⊓ centralizer ({z} : Set (Y ⧸ pCore 2 Y))⁆ ∧
              (normalizer (residual H : Set G)).subgroupOf Y =
                (centralizer ({z} : Set (Y ⧸ pCore 2 Y))).comap q ∧
              ∃ a : (A ⊓ Y : Subgroup G), q ⟨a.val,a.property.2⟩ * z * (q ⟨a.val,a.property.2⟩)⁻¹ ≠ z) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,hOdd⟩ :=
    localCartan_escape_seed_oddTernary_involution_reduction h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,?_,?_⟩
  · intro p hp ho hm
    have hm' : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
        ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
        IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p := by
      rcases hm with hm | hm
      · exact .inr (.inl hm)
      · exact .inr (.inr (.inr hm))
    have he := (hOdd p hp ho hm').1
    exact hescape (LocalSieve.odd_unitary_cartan_normalizes_residual h hH hgen c hY
      (he ▸ hKL) C hC hCn (he ▸ hKC) hp ho hm)
  · intro p hp ho hm
    apply hOdd p hp ho
    exact hm.elim Or.inl (fun hm => .inr (.inr (.inl hm)))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
