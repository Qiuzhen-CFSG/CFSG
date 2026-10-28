module
public import Stellmacher.Recognition.Parrott.SecondCentralizerLocalOddObstruction
public import Theory.GroupTheory.SmallAbelianQuotientCentralizer
public import Theory.GroupTheory.CentralKernelPGroupCentralizer

/-!
# Centralizers in the actual second-transfer quotient

Embed the second-transfer group in C_G(v), with its Sylow image between F
and Ω₁(O₂(N)). The central four-group pulls back faithfully and remains of
order four after quotienting by v. Its nonidentity quotient involutions have
two-group centralizers, hence their centralizers equal the supplied Sylow.

For the remaining involutions, the source-specific small abelian Sylow
calculation is explicit. The transfer theorem and odd-subgroup obstruction
then identify the full quotient centralizer with that local Sylow. All kernel,
central-four cardinality, and odd-obstruction premises are discharged here.
No N₂ hypothesis or solvability of C_G(v) is assumed.

Source: Parrott (1972), printed p.683, the quotient-centralizer paragraph.
The remaining local abelian Sylow construction is developed separately.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottNormalizerFusionData
variable {G : Type*} [Group G] [Finite G] {z : G}
  {d : ParrottSecondElementaryData z} (n : ParrottNormalizerFusionData d)

public theorem second_transfer_odd_subgroup_eq_bot
    (h : ParrottCentralizerHypotheses z)
    {A : Type*} [Group A] [Finite A]
    (i : A →* G) (hi : Function.Injective i)
    (hic : i.range ≤ centralizer ({n.v} : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let Z := (center K).map (N.subtype.comp K.subtype)
    Z ≤ i.range →
    ∀ O : Subgroup A, Odd (Nat.card O) →
      Z.comap i ≤ normalizer (O : Set A) → O = ⊥ := by
  intro N K Z hZi O ho hZO
  have hh : O.map i = ⊥ := n.odd_subgroup_eq_bot h (O.map i)
    ((map_le_range i O).trans hic) (by rwa [card_map_of_injective hi]) (by
      change Z ≤ normalizer (O.map i : Set G)
      rw [← map_comap_eq_self hZi]
      exact (map_mono hZO).trans (O.le_normalizer_map i))
  exact map_injective hi (hh.trans (map_bot i).symm)

public theorem second_transfer_central_four_quotient_centralizer
    (h : ParrottCentralizerHypotheses z)
    {A B : Type*} [Group A] [Finite A] [Group B]
    (i : A →* G) (hi : Function.Injective i)
    (hic : i.range ≤ centralizer ({n.v} : Set G))
    (S : Sylow 2 A) (q : A →* B) (hq : Function.Surjective q)
    (hqk : q.ker ≤ center A) (hqp : IsPGroup 2 q.ker) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let Z := (center K).map (N.subtype.comp K.subtype)
    Z.comap i ≤ centralizer (S : Set A) →
    ∀ k ∈ (Z.comap i).map q, orderOf k = 2 →
      centralizer ({k} : Set B) ≤ (S : Subgroup A).map q := by
  intro N K Z hZS k hk hk2
  obtain ⟨a, ha, rfl⟩ := hk
  have ha1 : i a ≠ 1 := by
    intro he
    have ha1 : a = 1 := hi (he.trans i.map_one.symm)
    simp [ha1] at hk2
  have hp := n.core_center_double_centralizer_isTwoGroup h (i a) ha ha1
  let C := centralizer ({a} : Set A)
  let D := centralizer ({n.v} : Set G) ⊓ centralizer ({i a} : Set G)
  let j : C →* D := (i.comp C.subtype).codRestrict D (by
    intro x
    refine ⟨hic ⟨x, rfl⟩, ?_⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul, MonoidHom.comp_apply, coe_subtype] using congrArg i (mem_centralizer_singleton_iff.mp x.property))
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply hi
    exact congrArg D.subtype he
  have hC : IsPGroup 2 C := hp.of_injective j hj
  have hbar := q.isPGroup_centralizer_of_central_kernel hq hqk hqp a hC
  let Sbar := S.mapSurjective hq
  have hSC : (Sbar : Subgroup B) ≤ centralizer ({q a} : Set B) := by
    rintro _ ⟨s, hs, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg q (hZS ha s hs)
  exact (Sbar.is_maximal' hbar hSC).le

private theorem mem_zpowers_two {A : Type*} [Group A] [Finite A]
    {v x : A} (hv : orderOf v = 2) (hx : x ∈ zpowers v) : x = 1 ∨ x = v := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hv] at hx
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
  have hr2 : r < 2 := Finset.mem_range.mp hr
  interval_cases r <;> simp

omit [Finite G] in
public theorem second_transfer_quotient_core_center_geometry
    {A B : Type*} [Group A] [Finite A] [Group B]
    (i : A →* G) (hi : Function.Injective i)
    (hic : i.range ≤ centralizer ({n.v} : Set G))
    (S : Sylow 2 A) (hFS : d.F ≤ (S : Subgroup A).map i)
    (v : A) (hv : i v = n.v) (q : A →* B) (hqk : q.ker = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let Z := (center K).map (N.subtype.comp K.subtype)
    (S : Subgroup A).map i ≤ W →
    q.ker ≤ center A ∧ IsPGroup 2 q.ker ∧ Z ≤ i.range ∧
      Z.comap i ≤ centralizer (S : Set A) ∧ Nat.card ((Z.comap i).map q) = 4 := by
  intro N K W Z hSW
  have hv2 : orderOf v = 2 := by rw [← orderOf_injective i hi, hv]; exact n.v_order
  have hvc : v ∈ center A := by
    apply mem_center_iff.mpr
    intro a
    apply hi
    simp only [map_mul, hv]
    exact mem_centralizer_singleton_iff.mp (hic ⟨a, rfl⟩)
  have hker : q.ker ≤ center A := by rw [hqk]; exact zpowers_le.mpr hvc
  have hpker : IsPGroup 2 q.ker := by
    rw [hqk]
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])
  have hZF : Z ≤ d.F := n.core_center_le_omega_center.trans
    (n.omega_center_le_inf.trans inf_le_right)
  have hZi : Z ≤ i.range := hZF.trans (hFS.trans (map_le_range i _))
  let E := Z.comap i
  have hEmap : E.map i = Z := map_comap_eq_self hZi
  have hEcard : Nat.card E = 4 := by
    rw [← card_map_of_injective (K := E) hi, hEmap]
    exact n.ambient_core_center_card
  have hES : E ≤ centralizer (S : Set A) := by
    intro e he s hs
    apply hi
    simp only [map_mul]
    have hsK := n.omega_le_core (hSW (mem_map_of_mem i hs))
    obtain ⟨eK, heK, heq⟩ := he
    obtain ⟨sN, hsN, hsEq⟩ := hsK
    have hh := congrArg (N.subtype.comp K.subtype) (mem_center_iff.mp heK (⟨sN, hsN⟩ : K))
    change (sN : G) * (N.subtype.comp K.subtype) eK =
      (N.subtype.comp K.subtype) eK * (sN : G) at hh
    change (sN : G) = i s at hsEq
    rwa [heq, hsEq] at hh
  have hqinj : Function.Injective (q.comp E.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro e he
    have heker : (e : A) ∈ zpowers v := hqk ▸ (show (e : A) ∈ q.ker from he)
    rcases mem_zpowers_two hv2 heker with he1 | hev
    · exact Subtype.ext he1
    · have hvm : i v ∈ Z := hev ▸ e.property
      exact False.elim (n.v_not_mem_core_center (hv ▸ hvm))
  have heq : (⊤ : Subgroup E).map (q.comp E.subtype) = E.map q := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_comp, range_subtype]
  have hc : Nat.card (E.map q) = 4 := by
    rw [← heq, card_map_of_injective hqinj, Nat.card_congr (topEquiv (G := E)).toEquiv, hEcard]
  exact ⟨hker, hpker, hZi, hES, hc⟩


public theorem second_transfer_small_abelian_quotient_centralizer
    (h : ParrottCentralizerHypotheses z)
    {A B : Type*} [Group A] [Finite A] [Group B]
    (i : A →* G) (hi : Function.Injective i)
    (hic : i.range ≤ centralizer ({n.v} : Set G))
    (S : Sylow 2 A) (hFS : d.F ≤ (S : Subgroup A).map i)
    (v : A) (hv : i v = n.v) (q : A →* B) (hq : Function.Surjective q)
    (hqk : q.ker = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let Z := (center K).map (N.subtype.comp K.subtype)
    (S : Subgroup A).map i ≤ W →
    ∀ k : B, orderOf k = 2 → k ∉ (Z.comap i).map q →
    ∀ P : Sylow 2 (centralizer ({k} : Set B)), IsMulCommutative P → Nat.card P ≤ 16 →
    (P : Subgroup (centralizer ({k} : Set B))).map (centralizer ({k} : Set B)).subtype ≤
      (S : Subgroup A).map q →
    (Z.comap i).map q ≤ (P : Subgroup (centralizer ({k} : Set B))).map
      (centralizer ({k} : Set B)).subtype →
    normalizer (P : Set (centralizer ({k} : Set B))) ≤
      centralizer (((Z.comap i).map q).subgroupOf (centralizer ({k} : Set B)) : Set (centralizer ({k} : Set B))) →
    centralizer ({k} : Set B) ≤ (S : Subgroup A).map q := by
  intro N K W Z hSW k hk2 hkE P hPc hPcard hPS hEP hEN
  let : IsMulCommutative P := hPc
  let : Finite B := Finite.of_surjective q hq
  obtain ⟨hker, hkp, hZi, _hES, hEc⟩ :=
    n.second_transfer_quotient_core_center_geometry i hi hic S hFS v hv q hqk hSW
  let C := centralizer ({k} : Set B)
  let kC : C := ⟨k, mem_centralizer_singleton_iff.mpr rfl⟩
  have hkc : kC ∈ center C := mem_center_iff.mpr (fun c =>
    Subtype.ext (mem_centralizer_singleton_iff.mp c.property))
  have hkn : (zpowers kC).Normal := by
    constructor
    intro x hx g
    rw [mem_center_iff.mp ((zpowers_le.mpr hkc) hx) g, mul_inv_cancel_right]
    exact hx
  let := hkn
  have hkP : kC ∈ (P : Subgroup C) := by
    have hp : IsPGroup 2 (zpowers kC) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact (orderOf_coe kC).symm.trans hk2)
    exact hp.le_sylow_of_normal P (mem_zpowers kC)
  have heq := q.quotient_centralizer_eq_sylow_of_small_abelian hq hker hkp (Z.comap i)
    (n.second_transfer_odd_subgroup_eq_bot h i hi hic hZi) k hk2
    (hEP.trans (map_subtype_le _)) P hPcard hEP hEc hEN hkP hkE
  exact heq.le.trans hPS

end Stellmacher.Recognition.ParrottNormalizerFusionData
