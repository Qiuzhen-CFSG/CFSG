module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Definitions
public import CFSG.Quasithin.Chapter10.SourceA5OvergroupReduction

/-!
# The half-Sylow reduction without an A₅ quotient

Assume the normalizer bound of 10.2.5 for the literal T₁ = N_T(L).
Its index two in T forces T₁ to be Sylow in every competing maximal
two-local above L₀T₁: a larger two-subgroup would be Sylow in M, and
source 1.2.7 would identify the overgroup with M. The original nonzero
module keeps both factors local at T₁. Source 1.2.4 then supplies normal
containing C-components, at least one of them strictly larger.

These steps do not require an A₅ marking. The normalizer bound and the
A.3.12/C.2.7 exclusion of the containing pair remain separate source
obligations. In particular, distinctness of the two containing components
is not assumed or asserted here.

Source: Aschbacher--Smith, 10.2.6, printed pp.748--749. The structural
proof adapts `SourceA5OvergroupReduction` to its exact normalizer premise.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D
private theorem source_uniqueness : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- A competing maximal two-local above L₀T₁ has the prescribed T₁ as Sylow. -/
theorem other_overgroup_sylow
    (hN : normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : IsMaximalTwoLocal H) (hne : H ≠ D.maximalLocal)
    (hLH : localOrbit T L ≤ H)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) H := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hRT : R ≤ (T : Subgroup G) := inf_le_left
  have hi : R.relIndex (T : Subgroup G) = 2 := by
    have he : R.subgroupOf (T : Subgroup G) =
        (normalizer (L : Set G)).subgroupOf (T : Subgroup G) := by
      ext x
      exact and_iff_right x.property
    change (R.subgroupOf (T : Subgroup G)).index = 2
    rw [he]
    exact source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  apply Chapter1.isSylowIn_iff.mpr
  refine ⟨T.isPGroup'.to_le hRT,hRH,?_⟩
  intro U hU hRU hUH
  by_contra hneU
  obtain ⟨Q,hUQ⟩ := hU.exists_le_sylow
  have hRQ : R ≤ (Q : Subgroup G) := hRU.trans hUQ
  have hindexQ : R.relIndex (Q : Subgroup G) = 2 := by
    have hcardQ := relIndex_mul_relIndex (⊥ : Subgroup G) R (Q : Subgroup G) bot_le hRQ
    have hcardT := relIndex_mul_relIndex (⊥ : Subgroup G) R (T : Subgroup G) bot_le hRT
    simp only [relIndex_bot_left] at hcardQ hcardT
    rw [hi] at hcardT
    have hQT : Nat.card Q = Nat.card T := Nat.card_congr (Q.equiv T).toEquiv
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := R))
      (hcardQ.trans (hQT.trans hcardT.symm))
  have hiU : R.relIndex U = 2 := by
    have hd : R.relIndex U ∣ 2 := hindexQ ▸
      dvd_of_mul_right_eq _ (relIndex_mul_relIndex R U (Q : Subgroup G) hRU hUQ)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact (hneU (le_antisymm (relIndex_eq_one.mp h) hRU)).elim
    · exact h
  have hUQeq : U = (Q : Subgroup G) := by
    have hh := relIndex_mul_relIndex R U (Q : Subgroup G) hRU hUQ
    rw [hiU,hindexQ] at hh
    exact le_antisymm hUQ (relIndex_eq_one.mp (by omega : U.relIndex (Q : Subgroup G) = 1))
  have hnormal : (R.subgroupOf U).Normal := normal_of_index_eq_two hiU
  have hUM : U ≤ D.maximalLocal :=
    ((normal_subgroupOf_iff_le_normalizer hRU).mp hnormal).trans
      hN
  exact hne (source_overgroup_eq_of_maximal_sylow D Q
    (hUQeq ▸ hUM) hH hLH (hUQeq ▸ hUH))

/-- The actual source component stays local at the half-Sylow in a competing overgroup. -/
theorem other_overgroup_local_component
    (hN : normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : IsMaximalTwoLocal H) (hne : H ≠ D.maximalLocal)
    (hLH : localOrbit T L ≤ H)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    {B : Subgroup G} (hB : B ∈ Chapter1.L G (T : Subgroup G))
    (hBL : B ≤ localOrbit T L) :
    B ∈ Chapter1.L G ((T : Subgroup G) ⊓ normalizer (L : Set G)) := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hBJ : B ⊔ R ≤ localJoin T L := sup_le (hBL.trans le_sup_left)
    (inf_le_left.trans le_sup_right)
  have hVR : D.moduleSubgroup ≤ R :=
    le_inf D.module_le_sylow (D.module_le_orbit.trans (source_nonnormal_orbit_le_normalizer D hn))
  have hcore : D.moduleSubgroup ≤ (B ⊔ R).pCoreIn 2 :=
    le_pCoreIn_of_normalizes D.module_elementary.isPGroup
      (hVR.trans le_sup_right) (hBJ.trans D.join_normalizes_module)
  refine ⟨hB.1.subgroupOf_of_le le_sup_left
    (sup_le le_sup_left (inf_le_left.trans le_sup_right)),?_,?_⟩
  · exact (other_overgroup_sylow D hN hn hH hne hLH hRH).restrict
      le_sup_right (sup_le (hBL.trans hLH) hRH)
  · intro he
    exact D.module_ne_bot (bot_unique (hcore.trans_eq he))

/-- The original normalized local component has a unique normal containing
component in a competing maximal two-local, with no embedding inspection assumed. -/
theorem other_overgroup_containing_component
    (hN : normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : IsMaximalTwoLocal H) (hne : H ≠ D.maximalLocal)
    (hLH : localOrbit T L ≤ H)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    {B : Subgroup G} (hB : B ∈ Chapter1.L G (T : Subgroup G))
    (hBL : B ≤ localOrbit T L)
    (hRB : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (B : Set G)) :
    ∃! K : Subgroup H, K.IsCComponent ∧ B.subgroupOf H ≤ K ∧ K.Normal := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  obtain ⟨P,hP⟩ := other_overgroup_sylow D hN hn hH hne hLH hRH
  have hP' : (P : Subgroup H) = R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hRH]
  have hlocal : B.subgroupOf H ∈ Chapter1.L H (P : Subgroup H) := by
    rw [hP']
    exact (Chapter1.mem_LIn_iff_subgroupOf hRH (hBL.trans hLH)).mp
      ⟨hBL.trans hLH,other_overgroup_local_component D hN hn hH hne hLH hRH hB hBL⟩
  have hPN : (P : Subgroup H) ≤ normalizer (B.subgroupOf H : Set H) := by
    rw [hP',←subgroupOf_normalizer_eq (hBL.trans hLH)]
    exact fun x hx => hRB hx
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    have hs := D.simpleQTKE.twoLocal_sqtk hH.1
    refine ⟨?_,hs.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hs.stronglyQuasithin p hp ho)
  exact Chapter1.Section02.lemma_1_2_4_containment_normality_source hQ P hlocal hPN

/-- A competing overgroup forces a proper enlargement of one of the two
literal original components. Distinctness of the containing components is
not asserted: that is a remaining source embedding inspection. -/
theorem other_overgroup_pair_enlargement
    (hN : normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : IsMaximalTwoLocal H) (hne : H ≠ D.maximalLocal)
    (hLH : localOrbit T L ≤ H)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H) :
    ∃ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) ∧
      localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom ∧
      ∃ K₁ K₂ : Subgroup H, K₁.IsCComponent ∧ K₁.Normal ∧
        K₂.IsCComponent ∧ K₂.Normal ∧ L.subgroupOf H ≤ K₁ ∧
        (L.map (MulAut.conj t).toMonoidHom).subgroupOf H ≤ K₂ ∧
        (L.subgroupOf H < K₁ ∨
          (L.map (MulAut.conj t).toMonoidHom).subgroupOf H < K₂) := by
  obtain ⟨t,ht,htn,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let B := L.map (MulAut.conj t).toMonoidHom
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hLorb : L ≤ localOrbit T L := le_componentOrbit L T
  have hBorb : B ≤ localOrbit T L := le_sup_right.trans hpair.ge
  have hlocalB : B ∈ Chapter1.L G (T : Subgroup G) := by
    have hh := (Chapter1.mem_L_map_iff (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).mpr D.maximal.1
    have he : (T : Subgroup G).map (MulAut.conj t).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)
    rwa [he] at hh
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) := by
    have he : R.subgroupOf (T : Subgroup G) =
        (normalizer (L : Set G)).subgroupOf (T : Subgroup G) := by
      ext x
      exact and_iff_right x.property
    have hnormal : (R.subgroupOf (T : Subgroup G)).Normal := by
      rw [he]
      exact normal_of_index_eq_two
        (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
    exact (normal_subgroupOf_iff_le_normalizer inf_le_left).mp hnormal
  have hRB : R ≤ normalizer (B : Set G) := by
    have he : R.map (MulAut.conj t).toMonoidHom = R :=
      mem_normalizer_iff_map_conj_eq.mp (hTR ht)
    rw [←he, show normalizer (B : Set G) =
      (normalizer (L : Set G)).map (MulAut.conj t).toMonoidHom from
      (map_normalizer_eq_of_bijective L (MulAut.conj t).bijective).symm]
    exact map_mono inf_le_right
  obtain ⟨K₁,⟨hK₁,hLK₁,hn₁⟩,_⟩ := other_overgroup_containing_component
    D hN hn hH hne hLH hRH D.maximal.1 hLorb inf_le_right
  obtain ⟨K₂,⟨hK₂,hBK₂,hn₂⟩,_⟩ := other_overgroup_containing_component
    D hN hn hH hne hLH hRH hlocalB hBorb hRB
  refine ⟨t,ht,htn,hpair,K₁,K₂,hK₁,hn₁,hK₂,hn₂,hLK₁,hBK₂,?_⟩
  by_contra hnot
  have hL : L.subgroupOf H = K₁ := by
    by_contra hh
    exact hnot (Or.inl (lt_of_le_of_ne hLK₁ hh))
  have hB : B.subgroupOf H = K₂ := by
    by_contra hh
    exact hnot (Or.inr (lt_of_le_of_ne hBK₂ hh))
  have hHN : H ≤ normalizer (localOrbit T L : Set G) := by
    rw [hpair]
    apply (le_inf ?_ ?_).trans (normalizer_inf_normalizer_le_normalizer_sup L B)
    · exact (normal_subgroupOf_iff_le_normalizer (hLorb.trans hLH)).mp (hL ▸ hn₁)
    · exact (normal_subgroupOf_iff_le_normalizer (hBorb.trans hLH)).mp (hB ▸ hn₂)
  exact hne (le_antisymm hHN (hH.2 (source_uniqueness D).normalizer_maximal.1 hHN))

/-- The exact containing-pair input to the remaining source inspection,
constructed from a competing maximal two-local and source 10.2.5. -/
theorem exists_containingPair
    (hN : normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : IsMaximalTwoLocal H) (hne : H ≠ D.maximalLocal)
    (hhalf : halfJoin T L ≤ H) :
    ∃ (t : G) (K₁ K₂ : Subgroup H), ContainingPair D H t K₁ K₂ := by
  have hLH : localOrbit T L ≤ H := le_sup_left.trans hhalf
  have hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H := le_sup_right.trans hhalf
  obtain ⟨t,ht,htn,hpair,K₁,K₂,hK₁,hn₁,hK₂,hn₂,hL,hB,hstrict⟩ :=
    other_overgroup_pair_enlargement D hN hn hH hne hLH hRH
  exact ⟨t,K₁,K₂,hH,hhalf,other_overgroup_sylow D hN hn hH hne hLH hRH,
    ht,htn,hpair,hK₁,hn₁,hK₂,hn₂,hL,hB,hstrict⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
