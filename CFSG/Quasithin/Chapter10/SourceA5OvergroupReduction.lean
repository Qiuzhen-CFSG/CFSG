module
public import CFSG.Quasithin.Chapter10.SourceA5NormalizerControl
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality

/-!
# Competing overgroups of the original nonnormal A₅ pair

Source uniqueness above L₀T transports to every Sylow subgroup of M.
The actual T₁=N_T(L) has index two in T and N_G(T₁)≤M. Any larger
two-subgroup containing T₁ would therefore be a full Sylow in M, forcing
a competing maximal two-local H back to M. Hence T₁ is Sylow in H.

The original nonzero FSU module keeps each factor local at T₁. The proved
source containment theorem supplies a unique normal containing component
for each of the two literal factors L and Lᵗ. At least one containment is
proper, since equality for both would make H normalize L₀ and lie in M.

This is the opening reduction of 10.2.6. It does not assert that the two
containing components are distinct, or exclude their proper enlargement:
those are the remaining A.3.12 and C.2.7 inspections. No new classification
or chosen-module premise is introduced.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 10.2.6, printed pp.748–749, using 1.2.4 and 1.2.7.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D
private theorem source_uniqueness : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- Source uniqueness applies to each literal Sylow subgroup of M. -/
theorem source_overgroup_eq_of_maximal_sylow
    (P : Sylow 2 G) (hPM : (P : Subgroup G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : IsMaximalTwoLocal H)
    (hLH : localOrbit T L ≤ H) (hPH : (P : Subgroup G) ≤ H) :
    H = D.maximalLocal := by
  let M := D.maximalLocal
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  obtain ⟨m,hm⟩ := MulAction.exists_smul_eq M (P.subtype hPM) (T.subtype hTM)
  have hm' : ((P : Subgroup G).subgroupOf M).map (MulAut.conj m).toMonoidHom =
      (T : Subgroup G).subgroupOf M := by
    exact congrArg (fun S : Sylow 2 M => (S : Subgroup M)) hm
  have hmapT : (P : Subgroup G).map (MulAut.conj (m : G)).toMonoidHom = T := by
    have hh := congrArg (map M.subtype) hm'
    rw [map_map, show M.subtype.comp (MulAut.conj m).toMonoidHom =
      (MulAut.conj (m : G)).toMonoidHom.comp M.subtype from rfl,
      ←map_map,map_subgroupOf_eq_of_le hPM,map_subgroupOf_eq_of_le hTM] at hh
    exact hh
  have hmapL : (localOrbit T L).map (MulAut.conj (m : G)).toMonoidHom = localOrbit T L :=
    mem_normalizer_iff_map_conj_eq.mp m.property
  have hmapM : M.map (MulAut.conj (m : G)).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer m.property)
  apply map_injective (f := (MulAut.conj (m : G)).toMonoidHom) (MulAut.conj (m : G)).injective
  rw [hmapM]
  apply (source_uniqueness D).normalizer_unique _ (isMaximalTwoLocal_map _ hH)
  apply sup_le
  · have hh : localOrbit T L ≤ H.map (MulAut.conj (m : G)).toMonoidHom := by
      rw [←hmapL]
      exact map_mono hLH
    exact (le_componentOrbit L T).trans hh
  · exact hmapT ▸ map_mono hPH

/-- A competing maximal two-local above L₀T₁ has the prescribed T₁ as Sylow. -/
theorem source_a5_other_overgroup_sylow
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
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
      (source_a5_sylow_stabilizer_normalizer_le D e hn)
  exact hne (source_overgroup_eq_of_maximal_sylow D Q
    (hUQeq ▸ hUM) hH hLH (hUQeq ▸ hUH))

/-- The actual source component stays local at the half-Sylow in a competing overgroup. -/
theorem source_a5_other_overgroup_local_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
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
  · exact (source_a5_other_overgroup_sylow D e hn hH hne hLH hRH).restrict
      le_sup_right (sup_le (hBL.trans hLH) hRH)
  · intro he
    exact D.module_ne_bot (bot_unique (hcore.trans_eq he))

/-- The original normalized local component has a unique normal containing
component in a competing maximal two-local, with no embedding inspection assumed. -/
theorem source_a5_other_overgroup_containing_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : IsMaximalTwoLocal H) (hne : H ≠ D.maximalLocal)
    (hLH : localOrbit T L ≤ H)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    {B : Subgroup G} (hB : B ∈ Chapter1.L G (T : Subgroup G))
    (hBL : B ≤ localOrbit T L)
    (hRB : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (B : Set G)) :
    ∃! K : Subgroup H, K.IsCComponent ∧ B.subgroupOf H ≤ K ∧ K.Normal := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  obtain ⟨P,hP⟩ := source_a5_other_overgroup_sylow D e hn hH hne hLH hRH
  have hP' : (P : Subgroup H) = R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hRH]
  have hlocal : B.subgroupOf H ∈ Chapter1.L H (P : Subgroup H) := by
    rw [hP']
    exact (Chapter1.mem_LIn_iff_subgroupOf hRH (hBL.trans hLH)).mp
      ⟨hBL.trans hLH,source_a5_other_overgroup_local_component D e hn hH hne hLH hRH hB hBL⟩
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
theorem source_a5_other_overgroup_pair_enlargement
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
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
  obtain ⟨K₁,⟨hK₁,hLK₁,hn₁⟩,_⟩ := source_a5_other_overgroup_containing_component
    D e hn hH hne hLH hRH D.maximal.1 hLorb inf_le_right
  obtain ⟨K₂,⟨hK₂,hBK₂,hn₂⟩,_⟩ := source_a5_other_overgroup_containing_component
    D e hn hH hne hLH hRH hlocalB hBorb hRB
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

end CFSG.Quasithin.Chapter10
