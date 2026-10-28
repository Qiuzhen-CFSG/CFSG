module

public import Stellmacher.Recognition.Parrott.SecondElementary
public import Stellmacher.Recognition.Parrott.OuterOmegaSixteenUnconditional

/-!
# The second elementary subgroup from the derived-normalizer identity

The original normalizer identity N_G(J′)=C_G(z) supplies the fusion and
weak-closure steps of Parrott's Lemmas 2--3. The unrestricted order-sixteen
exclusion then forces an involution in J outside J′. Its actual fixed join
constructs the second elementary subgroup, with the compatible Sylow and
self-centralizer retained. No N₂ assumption is used.

The quasithin Tits source supplies the normalizer identity through solvability
of its actual Sylow overgroup.
Source: Parrott (1972), Lemmas 2--4, printed pp.673--675.
-/

open Subgroup
namespace Stellmacher.Recognition

/-- The original involution has an ambient conjugate in its centralizer outside the derived two-core. -/
public theorem parrott_fusion_outside_derived_of_normalizer
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (z : G) (h : ParrottCentralizerHypotheses z)
    (hnorm : normalizer (((commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype)) : Set G) =
      centralizer ({z} : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∃ t : G, orderOf t = 2 ∧ t ∈ H ∧ t ∉ E ∧ IsConj z t := by
  classical
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let E := D.map (H.subtype.comp J.subtype)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  change ∃ t : G, orderOf t = 2 ∧ t ∈ H ∧ t ∉ E ∧ IsConj z t
  have hclosure : ∀ t : H, (t : G) ∈ E → (t : G) ∉ zpowers z →
      (normalClosure ({t} : Set H)).map H.subtype = E := parrott_element_normalClosure z h
  by_contra hnone
  have horder (x : G) (hx : IsConj z x) : orderOf x = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hx
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq z).trans h.involution
  have hclosed (x : G) (hxH : x ∈ H) (hx : IsConj z x) : x ∈ E := by
    by_contra hxE
    exact hnone ⟨x, horder x hx, hxH, hxE, hx⟩
  obtain ⟨hZmap, _, _, _, _, hElem, _, hSylow⟩ := parrott_centralizer_structure z h
  change IsElementaryAbelian 2 D at hElem
  let : IsElementaryAbelian 2 D := hElem
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  have hzJ : z ∈ J.map H.subtype := by
    have hzZ : z ∈ (center J).map (H.subtype.comp J.subtype) := by
      rw [hZmap]
      exact mem_zpowers z
    obtain ⟨c, _, hcz⟩ := hzZ
    exact ⟨(c : H), c.property, hcz⟩
  let T : Sylow 2 H := default
  obtain ⟨S, hS⟩ := hSylow T
  have hJT : J ≤ (T : Subgroup H) := pCore_isPGroup.le_sylow_of_normal T
  have hSH : (S : Subgroup G) ≤ H := by
    rw [hS]
    exact map_subtype_le _
  have hzS : z ∈ (S : Subgroup G) := by
    rw [hS]
    exact map_mono hJT hzJ
  let zS : S := ⟨z, hzS⟩
  have hzSorder : orderOf zS = 2 := by
    exact (Subgroup.orderOf_coe zS).symm.trans h.involution
  obtain ⟨t, htneS, hzt⟩ := exists_distinct_isConj_in_sylow hns S zS hzSorder
  have htne : (t : G) ≠ z := fun heq => htneS (Subtype.ext heq)
  have htH : (t : G) ∈ H := hSH t.property
  have htE : (t : G) ∈ E := hclosed t htH hzt
  have ht2 : orderOf (t : G) = 2 := horder t hzt
  have htcyc : (t : G) ∉ zpowers z := by
    intro htcyc
    rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at htcyc
    obtain ⟨n, hn, hnt⟩ := Finset.mem_image.mp htcyc
    have hnlt : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · have ht1 : (t : G) = 1 := by simpa using hnt.symm
      simp [ht1] at ht2
    · exact htne (by simpa using hnt.symm)
  let C : Subgroup G := closure {x : G | x ∈ H ∧ IsConj z x}
  have hgen : E = C := by
    apply le_antisymm
    · let tH : H := ⟨t, htH⟩
      rw [← hclosure tH htE htcyc]
      apply map_le_iff_le_comap.mpr
      change closure (Group.conjugatesOfSet ({tH} : Set H)) ≤ C.comap H.subtype
      apply (Subgroup.closure_le _).mpr
      intro x hx
      obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      have hat : a = tH := Set.mem_singleton_iff.mp ha
      subst a
      apply Subgroup.subset_closure
      exact ⟨x.property, hzt.trans (H.subtype.map_isConj hax)⟩
    · exact (Subgroup.closure_le _).mpr (fun x hx => hclosed x hx.1 hx.2)
  have hnormLe : normalizer (E : Set G) ≤ H := hnorm.le
  exact htne (conjugate_eq_of_abelian_class_closure_normalizer z E hgen hnormLe t htH hzt)

/-- The core-involution negation forces z to be weakly closed in the actual derived image. -/
public theorem parrott_derived_weakClosure_of_core_involutions_of_normalizer
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z)
    (hnorm : normalizer (((commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype)) : Set G) =
      centralizer ({z} : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    (∀ t : G, t ∈ J.map H.subtype → orderOf t = 2 → t ∈ E) →
    ∀ t : G, t ∈ E → IsConj z t → t = z := by
  classical
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  change (∀ t : G, t ∈ J.map H.subtype → orderOf t = 2 → t ∈ E) →
    ∀ t : G, t ∈ E → IsConj z t → t = z
  intro hcore t ht hconj
  obtain ⟨_, _, _, _, _, hElem, hDcard, hSylow⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 (commutator J) := hElem
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  have hEcard : Nat.card E = 32 :=
    (card_map_of_injective (K := commutator J) (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)).trans hDcard
  let T : Sylow 2 H := Classical.choice inferInstance
  obtain ⟨S, hS⟩ := hSylow T
  have hSH : (S : Subgroup G) ≤ H := by
    rw [hS]
    exact map_subtype_le _
  exact conjugate_eq_of_unique_elementary_centralizer z E
    hnorm S hSH
    (fun A hAH hA hAcard => parrott_unique_elementary_of_core_involutions z h hcore
      A hAH hA (hAcard.trans hEcard)) t ht hconj

/-- The unrestricted fixed-join exclusion forces a core involution outside J′. -/
public theorem parrott_core_involution_of_derived_normalizer
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (z : G) (h : ParrottCentralizerHypotheses z)
    (hnorm : normalizer (((commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype)) : Set G) =
      centralizer ({z} : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∃ a : G, a ∈ J.map H.subtype ∧ orderOf a = 2 ∧ a ∉ E := by
  classical
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  change ∃ a : G, a ∈ J.map H.subtype ∧ orderOf a = 2 ∧ a ∉ E
  by_contra hnone
  have hcore (a : G) (ha : a ∈ J.map H.subtype) (ha2 : orderOf a = 2) : a ∈ E := by
    by_contra haE
    exact hnone ⟨a,ha,ha2,haE⟩
  obtain ⟨t,ht2,htH,htE,htconj⟩ :=
    parrott_fusion_outside_derived_of_normalizer hns z h hnorm
  let y : H := ⟨t,htH⟩
  have hy : orderOf y = 2 := (Subgroup.orderOf_coe y).symm.trans ht2
  have hyJ : y ∉ J := fun hyJ => htE (hcore t (mem_map_of_mem H.subtype hyJ) ht2)
  have hweak := parrott_derived_weakClosure_of_core_involutions_of_normalizer z h hnorm hcore
  have hle := parrott_outer_fixed_join_normalizer_le_centralizer_unconditional
    z h hweak y hy hyJ
  have hnot := parrott_omega_normalizer_not_le_centralizer z h hcore y hy hyJ htconj
  dsimp only at hnot
  rw [(parrott_outer_centralizer_omega z h hcore y hy hyJ).2.1] at hnot
  exact hnot hle

/-- The original second elementary subgroup, with no ambient N₂ premise. -/
public theorem parrott_second_elementary_of_derived_normalizer
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (z : G) (h : ParrottCentralizerHypotheses z)
    (hnorm : normalizer (((commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype)) : Set G) =
      centralizer ({z} : Set G)) : Nonempty (ParrottSecondElementaryData z) := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let DH := (commutator J).map J.subtype
  let E := (commutator J).map (H.subtype.comp J.subtype)
  obtain ⟨a,haJ,ha2,haE⟩ := parrott_core_involution_of_derived_normalizer hns z h hnorm
  obtain ⟨aH,haH,rfl⟩ := haJ
  have haD : aH ∉ DH := by
    intro haD
    have hmap : DH.map H.subtype = E := map_map _ _ _
    apply haE
    change (aH : G) ∈ E
    rw [← hmap]
    exact mem_map_of_mem H.subtype haD
  obtain ⟨d,_⟩ := parrott_second_elementary_of_core_involution z h aH haH
    ((Subgroup.orderOf_coe aH).symm.trans ha2) haD
  exact ⟨d⟩

end Stellmacher.Recognition
