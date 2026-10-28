module
public import Theory.SpecificGroups.Alternating.SevenFivePlacement
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PResidual.NormalizedSupplement
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveSection

/-!
# The two-perfect part of a local A₅ normalizer in A₇

The full Sylow marks the two fixed letters of the actual A₅. A subgroup
normalizing it permutes these two letters. Its two-perfectness kills that
permutation action, placing it in their pointwise stabilizer, the same A₅.
This is the final intrinsic normalizer step in source 14.7.45(2).
-/

public noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt

/-- A two-perfect subgroup normalizing the original full-Sylow local A₅ in
A₇ lies in that same A₅; neither conjugate marking nor residual is supplied. -/
theorem twoPerfect_le_local_five
    (B : Subgroup (alternatingGroup (Fin 7)))
    (e : B ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 (alternatingGroup (Fin 7)))
    (hSB : (S : Subgroup (alternatingGroup (Fin 7))) ≤ normalizer (B : Set _))
    (A : Subgroup (alternatingGroup (Fin 7))) (hA : IsPPerfect 2 A)
    (hAB : A ≤ normalizer (B : Set _)) : A ≤ B := by
  classical
  let Z := fixedPoints B (Fin 7)
  have hpres (a : A) (i : Fin 7) (hi : i ∈ Z) : a.val • i ∈ Z := by
    intro b
    have hb := (mem_normalizer_iff''.mp (hAB a.property) b.val).mp b.property
    have hh := hi ⟨a.val⁻¹ * b.val * a.val,hb⟩
    change (a.val⁻¹ * b.val * a.val) • i = i at hh
    have hh' := congrArg (fun j : Fin 7 => a.val • j) hh
    change b.val • (a.val • i) = a.val • i
    simpa only [smul_smul,mul_inv_cancel_left,mul_assoc] using hh'
  let f : A →* Equiv.Perm Z := {
    toFun := fun a => (a.val.val : Equiv.Perm (Fin 7)).subtypeEquiv (fun i => by
      constructor
      · exact hpres a i
      · intro hi
        have hh := hpres a⁻¹ (a.val • i) hi
        simpa only [inv_smul_smul] using
          (show a.val⁻¹ • (a.val • i) ∈ Z from hh))
    map_one' := by ext i; rfl
    map_mul' := by intro a b; ext i; rfl }
  have hc : Nat.card Z = 2 := by
    rw [Nat.card_coe_set_eq]
    exact Theory.SpecificGroups.Alternating.SevenFivePlacement.fixed_card_two B e S hSB
  have hp : IsPGroup 2 (Equiv.Perm Z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,←Nat.card_eq_fintype_card,hc]
    decide)
  have hf := hA.hom_eq_one_of_isPGroup hp f
  have hfix (a : A) (i : Fin 7) (hi : i ∈ Z) : a.val • i = i := by
    exact congrArg (fun g : A →* Equiv.Perm Z => (g a ⟨i,hi⟩).val) hf
  obtain ⟨i,j,_,hB⟩ :=
    Theory.SpecificGroups.Alternating.SevenFivePlacement.exists_fixed_pair B e S hSB
  have hi : i ∈ Z := by
    intro b
    have hb : b.val ∈ fixingSubgroup (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7)) :=
      hB ▸ b.property
    exact hb ⟨i,by simp⟩
  have hj : j ∈ Z := by
    intro b
    have hb : b.val ∈ fixingSubgroup (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7)) :=
      hB ▸ b.property
    exact hb ⟨j,by simp⟩
  intro a ha
  rw [hB]
  rintro ⟨x,hx⟩
  rcases hx with rfl | ⟨rfl⟩
  · exact hfix ⟨a,ha⟩ _ hi
  · exact hfix ⟨a,ha⟩ _ hj

/-- Lift the marked normalizer calculation through its actual two-group
kernel. The original local A₅ and full Sylow subgroup are retained. -/
theorem twoPerfect_le_local_five_of_seven_quotient
    {G : Type*} [Group G] [Finite G]
    (f : G →* alternatingGroup (Fin 7)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (S : Sylow 2 G) (K : Subgroup G)
    (hK : K ∈ ChapterA.Section03.localCComponents S)
    (hSK : (S : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (A : Subgroup G) (hA : IsPPerfect 2 A)
    (hAK : A ≤ normalizer (K : Set G)) : A ≤ K := by
  have hkK : IsPGroup 2 (f.subgroupMap K).ker := by
    rw [Subgroup.ker_subgroupMap]
    exact hk.comap_subtype
  let e := alternatingGroup.SevenFiveSection.imageFiveEquiv f K hkK eK
  have hsol : Group.IsSolvable f.ker := by
    let := hk.isNilpotent
    infer_instance
  have hn := ChapterA.Section03.SourceEmbeddings.alternatingSeven_five_section_image_normalized
    f hf hsol S K hK hkK eK
  have hAf : IsPPerfect 2 (A.map f) := hA.of_surjective
    (f.subgroupMap A) (f.subgroupMap_surjective A)
  have ha := twoPerfect_le_local_five (K.map f) e (S.mapSurjective hf) hn
    (A.map f) hAf ((map_mono hAK).trans (le_normalizer_map f))
  have hsup : A ≤ K ⊔ f.ker := by
    rw [←comap_map_eq]
    intro a haA
    exact ha (mem_map_of_mem f haA)
  exact le_of_isPPerfect_of_le_sup_of_normalizes A K f.ker hA hk
    ((hk.le_sylow_of_normal S).trans hSK) hsup

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt
