module
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.RankOneGeneration
public import Theory.GroupTheory.SubgroupCoverTransport

/-!
# The three rank-one parabolics in a maximal binary five-space parabolic

Relative to a fixed full flag, a rank-one parabolic deletes one cut and a
maximal parabolic retains one cut. Consequently exactly three rank-one
parabolics lie in a maximal parabolic. The actual correspondence through a
two-group kernel and the literal ambient inclusion preserve these covers.
Two distinct nodes in another Sylow overgroup leave a unique escaping node;
this is the lattice step that makes the source exchange fix P.

Source: Aschbacher--Smith, 10.2.9, printed p.753, combined manuscript
of 1 March 2004. The Chapter 10 consumer retains the source construction of
the two internal nodes and the terminal rank-five/rank-ten contradictions.
-/

open Subgroup BinaryLinear.OuterCyclic
@[expose] public noncomputable section
namespace BinaryLinear.FiveFlagGeometry
open MaximalOvergroups SylowOvergroups

abbrev RankOneBelow {H : Type*} [Group H] (S C : Subgroup H) :=
  {P : Subgroup H // S ⋖ P ∧ P ≤ C}

private theorem fullFlag_covBy_compl_singleton (b : FiveBasis) (i : Fin 4) :
    flagStabilizer b Set.univ ⋖ flagStabilizer b {i}ᶜ := by
  have hlt : flagStabilizer b Set.univ < flagStabilizer b {i}ᶜ := by
    refine lt_iff_le_not_ge.mpr ⟨(flag_le_iff b _ _).mpr (Set.subset_univ _),?_⟩
    intro h
    exact ((flag_le_iff b _ _).mp h (Set.mem_univ i)) (Set.mem_singleton i)
  refine covBy_of_eq_or_eq hlt ?_
  intro Q hBQ hQP
  obtain ⟨s,hs⟩ := overgroup_eq_flag b Q hBQ
  have hslo : {i}ᶜ ⊆ s := (flag_le_iff b _ _).mp (hs.symm.le.trans hQP)
  by_cases hi : i ∈ s
  · apply Or.inl
    have hall : s = Set.univ := by
      apply Set.eq_univ_of_forall
      intro j
      by_cases hj : j = i
      · exact hj ▸ hi
      · exact hslo hj
    exact hs.trans (congrArg (flagStabilizer b) hall)
  · apply Or.inr
    have he : s = {i}ᶜ := Set.Subset.antisymm (fun j hj hji => hi (hji ▸ hj)) hslo
    exact hs.trans (congrArg (flagStabilizer b) he)

/-- A cover of a full binary flag deletes exactly one of its four cuts. -/
theorem fullFlag_covBy_iff (b : FiveBasis) (P : Subgroup (LinearGroup 5)) :
    flagStabilizer b Set.univ ⋖ P ↔ ∃ i : Fin 4, P = flagStabilizer b {i}ᶜ := by
  constructor
  · intro hP
    obtain ⟨s,hs⟩ := overgroup_eq_flag b P hP.le
    have hproper : ¬ Set.univ ⊆ s := by
      intro h
      exact hP.ne (hs.trans (congrArg (flagStabilizer b)
        (Set.Subset.antisymm (Set.subset_univ _) h))).symm
    obtain ⟨i,_,hi⟩ := Set.not_subset.mp hproper
    have hnode : flagStabilizer b {i}ᶜ ≤ P := by
      rw [hs,flag_le_iff]
      exact fun j hj hji => hi (hji ▸ hj)
    have he := (covBy_iff_lt_and_eq_or_eq.mp hP).2 _
      (fullFlag_covBy_compl_singleton b i).le hnode
    exact ⟨i,(he.resolve_left (fullFlag_covBy_compl_singleton b i).ne.symm).symm⟩
  · rintro ⟨i,rfl⟩
    exact fullFlag_covBy_compl_singleton b i

/-- A maximal Sylow overgroup fixes exactly one cut of the same full flag. -/
theorem coatom_eq_singleton_flag (b : FiveBasis) (C : Subgroup (LinearGroup 5))
    (hSC : flagStabilizer b Set.univ ≤ C) (hC : IsCoatom C) :
    ∃ k : Fin 4, C = flagStabilizer b {k} := by
  obtain ⟨s,hs⟩ := overgroup_eq_flag b C hSC
  have hsne : s.Nonempty := by
    by_contra hn
    have he : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    exact hC.1 (by rw [hs,he,flagStabilizer_empty])
  obtain ⟨k,hk⟩ := hsne
  have hle : C ≤ flagStabilizer b {k} := by
    rw [hs,flag_le_iff,Set.singleton_subset_iff]
    exact hk
  refine ⟨k,?_⟩
  by_contra he
  exact (singleton_flag_isCoatom b k).1 (hC.2 _ (lt_of_le_of_ne hle he))

private theorem node_injective (b : FiveBasis) :
    Function.Injective (fun i : Fin 4 => flagStabilizer b {i}ᶜ) := by
  intro i j he
  by_contra hij
  have hsub := (flag_le_iff b _ _).mp he.le
  exact hsub hij (Set.mem_singleton i)

/-- The rank-one parabolics inside a maximal parabolic are the other three
nodes, with the common full flag kept fixed. -/
def rankOneBelowEquiv (b : FiveBasis) (k : Fin 4) :
    {i : Fin 4 // i ≠ k} ≃
      RankOneBelow (flagStabilizer b Set.univ) (flagStabilizer b {k}) :=
  Equiv.ofBijective (fun i => ⟨flagStabilizer b {i.val}ᶜ,
    by exact fullFlag_covBy_compl_singleton b i.val,
    (flag_le_iff b _ _).mpr (Set.singleton_subset_iff.mpr i.property.symm)⟩) (by
      constructor
      · intro i j he
        exact Subtype.ext (node_injective b (congrArg Subtype.val he))
      · intro P
        obtain ⟨i,hi⟩ := (fullFlag_covBy_iff b P.val).mp P.property.1
        have hki : k ≠ i := by
          have hh := (flag_le_iff b _ _).mp (hi ▸ P.property.2)
          exact hh (Set.mem_singleton k)
        exact ⟨⟨i,hki.symm⟩,Subtype.ext hi.symm⟩)

/-- A maximal parabolic of GL₅(2) contains exactly three covers of its
prescribed full Sylow subgroup. -/
theorem rankOneBelow_card (S : Sylow 2 (LinearGroup 5))
    (C : Subgroup (LinearGroup 5)) (hSC : (S : Subgroup _) ≤ C) (hC : IsCoatom C) :
    Nat.card (RankOneBelow (S : Subgroup _) C) = 3 := by
  obtain ⟨b,hb⟩ := sylow_eq_flagStabilizer S
  obtain ⟨k,hk⟩ := coatom_eq_singleton_flag b C (hb ▸ hSC) hC
  rw [hb,hk,←Nat.card_congr (rankOneBelowEquiv b k),Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun i : Fin 4 => i = k), Fintype.card_subtype_eq]
  rfl

/-- Covers and their containment in C are preserved through the actual
surjection when its kernel lies in the prescribed Sylow. -/
def rankOneBelowEquivOfTwoKernel {H : Type*} [Group H] [Finite H]
    (f : H →* LinearGroup 5) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (S : Sylow 2 H) (C : Subgroup H)
    (hSC : (S : Subgroup H) ≤ C) :
    RankOneBelow (S : Subgroup H) C ≃
      RankOneBelow ((S : Subgroup H).map f) (C.map f) := by
  have hker : f.ker ≤ (S : Subgroup H) := hk.le_sylow_of_normal S
  have hkerC : f.ker ≤ C := hker.trans hSC
  let forward : RankOneBelow (S : Subgroup H) C →
      RankOneBelow ((S : Subgroup H).map f) (C.map f) := fun P =>
    ⟨P.val.map f,by
      apply (comap_covBy_iff_of_surjective f hf _ _).mp
      rw [comap_map_eq_self hker,comap_map_eq_self (hker.trans P.property.1.le)]
      exact P.property.1,
      map_mono P.property.2⟩
  apply Equiv.ofBijective forward
  constructor
  · intro P Q he
    apply Subtype.ext
    exact map_injective_of_ker_le f (hker.trans P.property.1.le)
      (hker.trans Q.property.1.le) (congrArg Subtype.val he)
  · intro P
    have hcov : (S : Subgroup H) ⋖ P.val.comap f := by
      have hh := (comap_covBy_iff_of_surjective f hf _ _).mpr P.property.1
      rwa [comap_map_eq_self hker] at hh
    have hPC : P.val.comap f ≤ C := by
      have hh := comap_mono (f := f) P.property.2
      rwa [comap_map_eq_self hkerC] at hh
    refine ⟨⟨P.val.comap f,hcov,hPC⟩,?_⟩
    exact Subtype.ext (map_comap_eq_self_of_surjective hf P.val)

/-- The three rank-one overgroups survive a normal two-group kernel. -/
theorem rankOneBelow_card_of_two_kernel {H : Type*} [Group H] [Finite H]
    (f : H →* LinearGroup 5) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (S : Sylow 2 H) (C : Subgroup H)
    (hSC : (S : Subgroup H) ≤ C) (hC : IsCoatom C) :
    Nat.card (RankOneBelow (S : Subgroup H) C) = 3 := by
  rw [Nat.card_congr (rankOneBelowEquivOfTwoKernel f hf hk S C hSC)]
  exact rankOneBelow_card (S.mapSurjective hf) (C.map f) (map_mono hSC)
    (isCoatom_map_of_surjective_of_ker_le f hf C ((hk.le_sylow_of_normal S).trans hSC) hC)

/-- Rank-one overgroups in H are the same actual subgroups of the ambient
group, provided both endpoints lie in H. -/
def rankOneBelowEquivSubtype {K : Type*} [Group K] (H S C : Subgroup K)
    (hSC : S ≤ C) (hCH : C ≤ H) :
    RankOneBelow (S.subgroupOf H) (C.subgroupOf H) ≃ RankOneBelow S C := by
  have hSH : S ≤ H := hSC.trans hCH
  let forward : RankOneBelow (S.subgroupOf H) (C.subgroupOf H) → RankOneBelow S C := fun P =>
    ⟨P.val.map H.subtype,by
      have hh := (covBy_map_subtype_iff H _ _).mpr P.property.1
      rwa [map_subgroupOf_eq_of_le hSH] at hh,by
      have hh := map_mono (f := H.subtype) P.property.2
      rwa [map_subgroupOf_eq_of_le hCH] at hh⟩
  apply Equiv.ofBijective forward
  constructor
  · intro P Q he
    exact Subtype.ext (map_injective H.subtype_injective (congrArg Subtype.val he))
  · intro P
    have hPH : P.val ≤ H := P.property.2.trans hCH
    have hcov : S.subgroupOf H ⋖ P.val.subgroupOf H := by
      apply (covBy_map_subtype_iff H _ _).mp
      rw [map_subgroupOf_eq_of_le hSH,map_subgroupOf_eq_of_le hPH]
      exact P.property.1
    refine ⟨⟨P.val.subgroupOf H,hcov,comap_mono P.property.2⟩,?_⟩
    exact Subtype.ext (map_subgroupOf_eq_of_le hPH)

/-- With exactly three rank-one nodes below C, two distinct nodes in D
force the escaping node to be unique. -/
theorem existsUnique_rankOne_escaping_of_pair {H : Type*} [Group H]
    (S C D : Subgroup H) [Finite (RankOneBelow S C)]
    (hc : Nat.card (RankOneBelow S C) = 3)
    (A B : RankOneBelow S C) (hAB : A ≠ B) (hAD : A.val ≤ D) (hBD : B.val ≤ D)
    (hex : ∃ P : RankOneBelow S C, ¬ P.val ≤ D) :
    ∃! P : RankOneBelow S C, ¬ P.val ≤ D := by
  classical
  let X := RankOneBelow S C
  let : Fintype X := Fintype.ofFinite X
  obtain ⟨P,hP⟩ := hex
  have hAP : A ≠ P := by
    intro he
    exact hP (he ▸ hAD)
  have hBP : B ≠ P := by
    intro he
    exact hP (he ▸ hBD)
  have hcard : ({A,B,P} : Finset X).card = Fintype.card X := by
    rw [←Nat.card_eq_fintype_card,hc]
    simp [hAB,hAP,hBP]
  have hall := Finset.eq_univ_of_card ({A,B,P} : Finset X) hcard
  refine ⟨P,hP,?_⟩
  intro Q hQ
  have hmem : Q ∈ ({A,B,P} : Finset X) := by rw [hall]; exact Finset.mem_univ Q
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · exact (hQ (h ▸ hAD)).elim
  · exact (hQ (h ▸ hBD)).elim
  · exact h

end BinaryLinear.FiveFlagGeometry
