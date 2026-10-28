module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerResidual
public import Theory.SpecificGroups.SymmetricSix.Parabolics.ThreeRank
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.PrimeSet

/-!
# The ordinary outside-normal-subgroup clause of 13.3.8

Under the original ordinary quotient and N_G(L)=LT, a two-perfect subgroup
Y of N_G(L) lies in L. If Y is normal in an outside overgroup H of T,
its join with the actual Sylow intersection in L is proper: otherwise
perfectness forces Y=L, and maximal two-local uniqueness puts H in N_G(L).
The image of that proper join in L/O₂(L)=A₆ has order dividing 24.
Its full kernel is a two-group, so Y is a {2,3}-group.

This proves the literal source implication with normality relative to H.
The normalizer supplement remains explicit. OrdinaryLocalAssembly applies
it at both the original ordinary core and the constructed reciprocal core,
removing the earlier universal 13.3.8 callback from that assembly.
Source: Aschbacher--Smith 13.3.8(2), printed pp.886--887.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V Y H : Subgroup G}

omit [Finite G] in
private theorem twoPerfect_le_component
    (D : ChosenModule T L V)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (hYM : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y) : Y ≤ L := by
  let M := normalizer (L : Set G)
  let A := L.subgroupOf M
  let : A.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hTM : (T : Subgroup G) ≤ M := D.sylow_normalizes_component
  have hs : A ⊔ (T : Subgroup G).subgroupOf M = ⊤ := by
    apply map_injective M.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le L.le_normalizer,
      map_subgroupOf_eq_of_le hTM,←MonoidHom.range_eq_map,range_subtype]
    exact hM.symm
  have hq : IsPGroup 2 (M ⧸ A) :=
    isPGroup_quotient_of_sup_eq_top A _ T.isPGroup'.comap_subtype hs
  have hp' : IsPPerfect 2 (Y.subgroupOf M) := hp.of_surjective
    (subgroupOfEquivOfLe hYM).symm.toMonoidHom (subgroupOfEquivOfLe hYM).symm.surjective
  have hi : Y.subgroupOf M ≤ A :=
    (le_pResidual_of_isPPerfect _ hp').trans (sInf_le ⟨inferInstance,hq⟩)
  intro y hy
  exact hi (show (⟨y,hYM hy⟩ : M) ∈ Y.subgroupOf M from hy)


/-- Every two-perfect normal subgroup of an outside overgroup lying in the ordinary normalizer is a {2,3}-group. -/
theorem ordinary_outside_twoThree
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G))
    (Y : Subgroup G) (hYH : Y ≤ H) (hnY : H ≤ normalizer (Y : Set G))
    (hp : IsPPerfect 2 Y) (hYM : Y ≤ normalizer (L : Set G)) :
    IsPiGroup twoThreePrimes Y := by
  have hYL := twoPerfect_le_component D hM hYM hp
  let M := normalizer (L : Set G)
  let A := L.subgroupOf M
  let : A.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨P,hP⟩ := (T.subtype D.sylow_normalizes_component).exists_subgroupOf_eq_of_normal A
  let e := subgroupOfEquivOfLe L.le_normalizer
  let S := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hST : ∀ s ∈ (S : Subgroup L), s.val ∈ (T : Subgroup G) := by
    rintro s ⟨a,ha,rfl⟩
    rw [hP] at ha
    exact ha
  let B := Y.subgroupOf L
  have hSB : (S : Subgroup L) ≤ normalizer (B : Set L) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro y
    exact mem_normalizer_iff.mp (hnY (hH.1.2 (hST s hs))) y.val
  let J := B ⊔ (S : Subgroup L)
  have hJne : J ≠ ⊤ := by
    intro hJ
    let : B.Normal := normalizer_eq_top_iff.mp (top_unique (hJ ▸
      sup_le B.le_normalizer hSB))
    have hq : IsPGroup 2 (L ⧸ B) := isPGroup_quotient_of_sup_eq_top B _ S.isPGroup' hJ
    let := hq.isNilpotent
    let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
    have hB : (⊤ : Subgroup L) ≤ B := le_of_isPerfect_of_solvable_quotient ⊤ B
    have hLH : L ≤ H := by
      intro l hl
      exact hYH (hB (show (⟨l,hl⟩ : L) ∈ (⊤ : Subgroup L) from trivial))
    have hu := (h.source_normalizer_maximal_unique structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2
    have hnQ : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
      H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
    exact hH.2 (hnQ.trans (normalizer_le_of_unique_maximalTwoLocal hu
      (isPGroup_pCoreIn 2 H) hH.1.1 ((sup_le hLH hH.1.2).trans hnQ)))
  let f : L →* alternatingGroup (Fin 6) := eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := eL.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ eL.injective,QuotientGroup.ker_mk']
  have hkerJ : f.ker ≤ J := hk ▸ (pCore_isPGroup.le_sylow_of_normal S).trans le_sup_right
  have himage : J.map f ≠ ⊤ := by
    intro he
    have hh := comap_map_eq_self hkerJ
    rw [he,comap_top] at hh
    exact hJne hh.symm
  have hcard : Nat.card (J.map f) ∣ 24 :=
    Theory.SpecificGroups.SymmetricSix.proper_sylow_overgroup_card_dvd_twenty_four
      (S.mapSurjective hf) (J.map f) (map_mono le_sup_right) himage
  have hBcard : Nat.card (B.map f) ∣ 24 := (card_dvd_of_le (map_mono le_sup_left)).trans hcard
  let g := f.comp B.subtype
  have hgr : g.range = B.map f := by rw [MonoidHom.range_comp,range_subtype]
  have hgker : IsPGroup 2 g.ker := by
    change IsPGroup 2 (f.comp B.subtype).ker
    rw [←MonoidHom.comap_ker,hk]
    exact pCore_isPGroup.comap_of_injective B.subtype B.subtype_injective
  obtain ⟨n,hn⟩ := hgker.exists_card_eq
  have hBpi : IsPiGroup twoThreePrimes B := by
    rw [IsPiGroup_iff]
    intro p hd
    change p.val = 2 ∨ p.val = 3
    have hc := g.ker.card_mul_index
    rw [index_ker,hgr,hn] at hc
    rw [←hc] at hd
    rcases p.property.dvd_mul.mp hd with hd | hd
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
        (p.property.dvd_of_dvd_pow hd) |>.resolve_left p.property.ne_one)
    · have hh : p.val ∣ 2^3 * 3 := hd.trans hBcard
      rcases p.property.dvd_mul.mp hh with hh | hh
      · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
          (p.property.dvd_of_dvd_pow hh) |>.resolve_left p.property.ne_one)
      · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp hh |>.resolve_left p.property.ne_one)
  exact hBpi.of_equiv (subgroupOfEquivOfLe hYL).symm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
