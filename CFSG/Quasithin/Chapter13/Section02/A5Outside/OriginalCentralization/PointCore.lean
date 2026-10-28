module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.FiveNonblock
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.SpecificGroups.SymmetricFive.NormalTwoInTwelve

/-!
# The actual intermediate point core in 13.2.12

Write G₂=O²(C_L(v)) Baum(T), Q=O₂(LT), and Q₂=O₂(G₂), with all
cores embedded in the original ambient group. The source index three,
S₃ quotient and four-element Baumann image give [G₂:Q]=12 and
[Q₂:Q]=2. Normality then makes the actual image of Q₂ a transposition.
Consequently LQ₂=LT. If the two point cores coincide, the escaping first
point group rules out every nontrivial characteristic subgroup of Baum(Q₂)
normal in LT, using the already proved uniqueness over LT.

These are the literal intermediate-group and obstruction inputs to C.1.24.
OriginalCentralization/EqualCore applies its transposition branch to exclude
equal point cores; SourceAssembly/EqualCore supplies the result to the
universal terminal consumer.
Source: Aschbacher--Smith 13.2.12, printed p.882.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section06.CentralizerReduction Section06.CentralizerReduction.A5Module
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

theorem point_local_le :
    Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G) ≤
      L ⊔ (T : Subgroup G) :=
  sup_le ((map_subtype_le _).trans (inf_le_left.trans le_sup_left))
    (inf_le_left.trans le_sup_right)

theorem point_core_bounds
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    let P := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ P.pCoreIn 2 ∧
      P.pCoreIn 2 ≤ ChapterB.baumann (T : Subgroup G) := by
  let K := L ⊔ (T : Subgroup G)
  let B := ChapterB.baumann (T : Subgroup G)
  let P := Lv L (markedV d.flag.flag.module) ⊔ B
  have hQB : K.pCoreIn 2 ≤ B := sup_eq_right.mp
    (source_core_products_eq_baumann d hH hB hZ hs hz).1
  have hQP : K.pCoreIn 2 ≤ P := hQB.trans le_sup_right
  have hnormal : P ≤ normalizer (K.pCoreIn 2 : Set G) :=
    (point_local_le d).trans (K.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  have hi : (B.subgroupOf P).index = 3 := point_residual_baumann_index d hH hB hZ hs hz
  let R := ((T.isPGroup'.to_le (show B ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
    : IsPGroup 2 (B.subgroupOf P)).toSylow (show ¬ 2 ∣ (B.subgroupOf P).index by rw [hi]; decide)
  refine ⟨le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K) hQP hnormal,?_⟩
  exact (pCoreIn_le_sylow P R).trans_eq (map_subgroupOf_eq_of_le le_sup_right)

theorem point_baumann_image_card
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    Nat.card (((ChapterB.baumann (T : Subgroup G)).subgroupOf
      (L ⊔ (T : Subgroup G))).map d.localActor) = 4 := by
  obtain ⟨g,_,_,_,hBm⟩ := thompson_baumann_plane_marking_of_omega_movement d hH hZ
  have hb : ChapterB.baumann ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))) =
      (ChapterB.baumann (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G)) := by
    apply map_injective (L ⊔ (T : Subgroup G)).subtype_injective
    dsimp only [ChapterB.baumann, ChapterB.thompsonAlpha]
    rw [baumann_map_injective _ (L ⊔ (T : Subgroup G)).subtype_injective,
      map_subgroupOf_eq_of_le le_sup_right,
      map_subgroupOf_eq_of_le (inf_le_left.trans le_sup_right)]
  change (ChapterB.baumann ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)))).map d.localActor = _ at hBm
  rw [←hb,hBm,card_map_of_injective (MulAut.conj g).injective]
  exact BinaryPermutation.FivePairFixedSpaces.card_pairClosure

private theorem core_relIndex_eq_image_card (A : Subgroup G) (hA : A ≤ L ⊔ (T : Subgroup G)) :
    ((L ⊔ (T : Subgroup G)).pCoreIn 2).relIndex A =
      Nat.card ((A.subgroupOf (L ⊔ (T : Subgroup G))).map d.localActor) := by
  have hh := relIndex_map_map_of_injective (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
    (A.subgroupOf (L ⊔ (T : Subgroup G))) (L ⊔ (T : Subgroup G)).subtype_injective
  rw [map_subgroupOf_eq_of_le hA] at hh
  exact hh.trans (by
    rw [←d.localActor_kernel_eq_core d.normalizes_L]
    exact relIndex_ker _ _)

theorem point_core_indices
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    let K := L ⊔ (T : Subgroup G)
    let B := ChapterB.baumann (T : Subgroup G)
    let P := Lv L (markedV d.flag.flag.module) ⊔ B
    (K.pCoreIn 2).relIndex P = 12 ∧
      (P.pCoreIn 2).relIndex P = 6 ∧
      (K.pCoreIn 2).relIndex (P.pCoreIn 2) = 2 := by
  let K := L ⊔ (T : Subgroup G)
  let B := ChapterB.baumann (T : Subgroup G)
  let P := Lv L (markedV d.flag.flag.module) ⊔ B
  have hQB : K.pCoreIn 2 ≤ B := sup_eq_right.mp
    (source_core_products_eq_baumann d hH hB hZ hs hz).1
  have hQBcard : (K.pCoreIn 2).relIndex B = 4 :=
    (core_relIndex_eq_image_card d B (inf_le_left.trans le_sup_right)).trans
      (point_baumann_image_card d hH hZ)
  have hi := relIndex_mul_relIndex (K.pCoreIn 2) B P hQB le_sup_right
  rw [hQBcard,point_residual_baumann_index d hH hB hZ hs hz] at hi
  have hiP : (K.pCoreIn 2).relIndex P = 12 := hi.symm
  have hQ2 : (P.pCoreIn 2).relIndex P = 6 := by
    have hh := relIndex_map_map_of_injective (pCore 2 P) ⊤ P.subtype_injective
    rw [←MonoidHom.range_eq_map,range_subtype] at hh
    change (P.pCoreIn 2).relIndex P = _ at hh
    rw [relIndex_top_right] at hh
    obtain ⟨e⟩ := point_residual_baumann_core_quotient d hH hB hZ hs hz
    exact hh.trans (by
      rw [index_eq_card,Nat.card_congr e.toEquiv]
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial])
  refine ⟨hiP,hQ2,?_⟩
  have hj := relIndex_mul_relIndex (K.pCoreIn 2) (P.pCoreIn 2) P
    (point_core_bounds d hH hB hZ hs hz).1 (pCoreIn_le 2 P)
  rw [hiP,hQ2] at hj
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 6) hj

theorem point_core_image_cards
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    let K := L ⊔ (T : Subgroup G)
    let P := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    Nat.card ((P.subgroupOf K).map d.localActor) = 12 ∧
      Nat.card (((P.pCoreIn 2).subgroupOf K).map d.localActor) = 2 := by
  obtain ⟨hP,_,hQ⟩ := point_core_indices d hH hB hZ hs hz
  exact ⟨(core_relIndex_eq_image_card d _ (point_local_le d)).symm.trans hP,
    (core_relIndex_eq_image_card d _ ((pCoreIn_le 2 _).trans (point_local_le d))).symm.trans hQ⟩

theorem point_core_image_transposition
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    let K := L ⊔ (T : Subgroup G)
    let P := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    ∃ r : Equiv.Perm (Fin 5), r.IsSwap ∧
      ((P.pCoreIn 2).subgroupOf K).map d.localActor = zpowers r := by
  let K := L ⊔ (T : Subgroup G)
  let P := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
  have hn : P ≤ normalizer (P.pCoreIn 2 : Set G) := P.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hnk : P.subgroupOf K ≤ normalizer ((P.pCoreIn 2).subgroupOf K : Set K) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp (hn hx) (y : G)
  obtain ⟨hP,hQ⟩ := point_core_image_cards d hH hB hZ hs hz
  exact Theory.SpecificGroups.SymmetricFive.swap_of_normalized_two_in_twelve
    _ _ hP hQ ((map_mono hnk).trans (((P.pCoreIn 2).subgroupOf K).le_normalizer_map d.localActor))

theorem point_core_component_join
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    L ⊔ (Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)).pCoreIn 2 =
      L ⊔ (T : Subgroup G) := by
  let K := L ⊔ (T : Subgroup G)
  let P := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
  let Q := P.pCoreIn 2
  let X := (L ⊔ Q).subgroupOf K
  have hQK : Q ≤ K := (pCoreIn_le 2 P).trans (point_local_le d)
  obtain ⟨r,hr,hR⟩ := point_core_image_transposition d hH hB hZ hs hz
  have hXmap : X.map d.localActor = alternatingGroup (Fin 5) ⊔ zpowers r := by
    change ((L ⊔ Q).subgroupOf K).map d.localActor = _
    rw [subgroupOf_sup (show L ≤ K from le_sup_left) hQK,Subgroup.map_sup,
      d.localActor_component_image,hR]
  have hfull : X.map d.localActor = ⊤ := by
    have ha : alternatingGroup (Fin 5) ≤ X.map d.localActor := hXmap ▸ le_sup_left
    have hi : (X.map d.localActor).index ∣ 2 := by
      simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le ha
    rcases (Nat.dvd_prime Nat.prime_two).mp hi with hi | hi
    · exact index_eq_one.mp hi
    · have he := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi
      have hh : r ∈ X.map d.localActor := hXmap ▸ mem_sup_right (mem_zpowers r)
      rw [he,Equiv.Perm.mem_alternatingGroup,hr.sign_eq] at hh
      exact (by decide : (-1 : ℤˣ) ≠ 1) hh |>.elim
  have hker : d.localActor.ker ≤ X := by
    rw [d.localActor_kernel_eq_core d.normalizes_L]
    intro x hx
    exact mem_sup_right ((point_core_bounds d hH hB hZ hs hz).1
      (mem_map_of_mem K.subtype hx))
  have hX : X = ⊤ := by
    have hh := congrArg (comap d.localActor) hfull
    rwa [comap_map_eq,comap_top,sup_of_le_left hker] at hh
  exact le_antisymm (sup_le le_sup_left hQK) (subgroupOf_eq_top.mp hX)

theorem equal_point_cores_no_characteristic_baumann
    {P₁ : Subgroup G}
    (hout : ¬ P₁ ≤ normalizer (L : Set G))
    (heq : P₁.pCoreIn 2 =
      (Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)).pCoreIn 2) :
    let K := L ⊔ (T : Subgroup G)
    let P₂ := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    let R := (P₂.pCoreIn 2).subgroupOf K
    ∀ C : Subgroup (ChapterB.baumann R), C.Characteristic → C ≠ ⊥ →
      ¬ (C.map (ChapterB.baumann R).subtype).Normal := by
  intro K P₂ R C hC hne hnormal
  let := hC
  let B := ChapterB.baumann R
  let D := (C.map B.subtype).map K.subtype
  have hD : D ≠ ⊥ := by
    intro hb
    exact hne ((C.map_eq_bot_iff_of_injective B.subtype_injective).mp
      (((C.map B.subtype).map_eq_bot_iff_of_injective K.subtype_injective).mp hb))
  have hpR : IsPGroup 2 R := (isPGroup_pCoreIn 2 P₂).comap_subtype
  have hpD : IsPGroup 2 D := (((hpR.to_le inf_le_left).to_subgroup C).map B.subtype).map K.subtype
  have hKD : K ≤ normalizer (D : Set G) := by
    apply le_normalizer_iff.mpr
    intro k hk x hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact mem_map_of_mem K.subtype (hnormal.conj_mem y hy ⟨k,hk⟩)
  have hND : normalizer (D : Set G) ≤ normalizer (L : Set G) :=
    normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup hpD hD hKD
  have hP : P₁ ≤ normalizer (P₂.pCoreIn 2 : Set G) := by
    rw [←heq]
    exact P₁.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P₁ (pCore 2 P₁))
  have hRm : R.map K.subtype = P₂.pCoreIn 2 :=
    map_subgroupOf_eq_of_le ((pCoreIn_le 2 P₂).trans (point_local_le d))
  have hBm : B.map K.subtype = ChapterB.baumann (P₂.pCoreIn 2) := by
    dsimp only [B,ChapterB.baumann,ChapterB.thompsonAlpha]
    rw [baumann_map_injective K.subtype K.subtype_injective,hRm]
  have hRB : normalizer (P₂.pCoreIn 2 : Set G) ≤ normalizer (B.map K.subtype : Set G) := by
    rw [hBm]
    exact normalizer_le_normalizer_baumann _
  exact hout (hP.trans (hRB.trans ((normalizer_le_normalizer_characteristic_map
    K.subtype K.subtype_injective B C).trans hND)))

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
