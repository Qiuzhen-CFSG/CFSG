module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.FixerTransport
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement.PointImage.Models
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Larger fixers of a critical four-image

Inside a Sylow two-subgroup of S₆, two independent commuting involutions
have either no larger common centralizing displacement fixer, or that fixer
lies in the group of disjoint transpositions. Five pair vectors test the
literal natural quotient; the resulting small table is kernel checked.
Sylow conjugacy transports the conclusion to any central four-image.
The larger image consequently acts quadratically on the whole augmentation
cover, retaining its constant line. The original-replacement application is
in CriticalTwo. Source: MS93 (3.3)(ii)(1), (3.6), printed pp.866--871.
-/

public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
private def independentPair (a b : Six.Perm) : Prop :=
  a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a*b=b*a
private instance (a b : Six.Perm) : Decidable (independentPair a b) := by
  unfold independentPair; infer_instance
private def fixesPair (a b g : Six.Perm) : Prop :=
  fixesTest g a ∧ fixesTest g b ∧ g*a=a*g ∧ g*b=b*g
private instance (a b g : Six.Perm) : Decidable (fixesPair a b g) := by
  unfold fixesPair; infer_instance
private def inFour (a b g : Six.Perm) : Prop := g=1 ∨ g=a ∨ g=b ∨ g=a*b
private instance (a b g : Six.Perm) : Decidable (inFour a b g) := by
  unfold inFour; infer_instance
private def smallFixer (i j : Fin 16) : Prop := ∀ k : Fin 16,
  fixesPair (Six.sylowWords i) (Six.sylowWords j) (Six.sylowWords k) →
  inFour (Six.sylowWords i) (Six.sylowWords j) (Six.sylowWords k)
private instance (i j : Fin 16) : Decidable (smallFixer i j) := by
  unfold smallFixer; infer_instance
private def ordinaryFixer (i j : Fin 16) : Prop := ∀ k : Fin 16,
  fixesPair (Six.sylowWords i) (Six.sylowWords j) (Six.sylowWords k) →
  ∃ l : Fin 8, Six.dWords l = Six.sylowWords k
private instance (i j : Fin 16) : Decidable (ordinaryFixer i j) := by
  unfold ordinaryFixer; infer_instance
private theorem fixer_table : ∀ i j : Fin 16,
    independentPair (Six.sylowWords i) (Six.sylowWords j) →
    smallFixer i j ∨ ordinaryFixer i j := by decide +kernel
private theorem exists_independent_pair (A : Subgroup Six.Perm)
    [IsElementaryAbelian 2 A] (hc : Nat.card A = 4) :
    ∃ a ∈ A, ∃ b ∈ A, independentPair a b := by
  classical
  have hne : A ≠ ⊥ := by intro he;rw [he,card_bot] at hc;omega
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  have hb : ∃ b ∈ A, b ≠ 1 ∧ b ≠ a := by
    by_contra! hn
    have hsub : (A : Set Six.Perm) ⊆ {1,a} := by
      intro b hb
      by_cases h1 : b=1
      · exact Or.inl h1
      · exact Or.inr (hn b hb h1)
    have hh := Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
    rw [Nat.card_coe_set_eq ({1,a} : Set Six.Perm),Set.ncard_pair ha1.symm] at hh
    change Nat.card A ≤ 2 at hh
    omega
  obtain ⟨b,hb,hb1,hba⟩ := hb
  exact ⟨a,ha,b,hb,ha1,hb1,hba.symm,
    elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha,
    elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb,
    Subtype.ext_iff.mp (mul_comm (⟨a,ha⟩ : A) ⟨b,hb⟩)⟩

private theorem larger_fixer_le_ordinary (A B : Subgroup Six.Perm)
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 4) (hB : B ≤ Six.sylowCarrier)
    (hAB : A ≤ B) (hproper : ¬ B ≤ A)
    (hcentral : B ≤ centralizer (A : Set Six.Perm))
    (hfix : B ≤ subspaceKernel (naturalRepresentation (Fin 6))
      (subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ A) ⊤) : B ≤ D 6 := by
  obtain ⟨a,ha,b,hb,hind⟩ := exists_independent_pair A hA
  obtain ⟨i,rfl⟩ := (Six.mem_sylowCarrier_iff a).mp (hB (hAB ha))
  obtain ⟨j,rfl⟩ := (Six.mem_sylowCarrier_iff b).mp (hB (hAB hb))
  have hf {g : Six.Perm} (hg : g ∈ B) :
      fixesPair (Six.sylowWords i) (Six.sylowWords j) g :=
    ⟨fixesTest_of_fixes_moved A B hfix ha hg,
      fixesTest_of_fixes_moved A B hfix hb hg,
      (hcentral hg _ ha).symm,(hcentral hg _ hb).symm⟩
  rcases fixer_table i j hind with hs | hd
  · exfalso
    apply hproper
    intro g hg
    obtain ⟨k,rfl⟩ := (Six.mem_sylowCarrier_iff g).mp (hB hg)
    rcases hs k (hf hg) with he | he | he | he
    · rw [he];exact A.one_mem
    · rw [he];exact ha
    · rw [he];exact hb
    · rw [he];exact A.mul_mem ha hb
  · intro g hg
    obtain ⟨k,rfl⟩ := (Six.mem_sylowCarrier_iff g).mp (hB hg)
    obtain ⟨l,hl⟩ := hd k (hf hg)
    exact (Six.mem_disjointTranspositions_iff (3 : Fin 4) _).mpr ⟨l,hl⟩

/-- A strictly larger centralizing two-image fixing a four-group's natural
movement acts quadratically even on the entire augmentation cover. -/
theorem quadratic_core_of_four_image (A B : Subgroup Six.Perm)
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 4) (hp : IsPGroup 2 B)
    (hAB : A ≤ B) (hproper : ¬ B ≤ A)
    (hcentral : B ≤ centralizer (A : Set Six.Perm))
    (hfix : B ≤ subspaceKernel (naturalRepresentation (Fin 6))
      (subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ A) ⊤) :
    IsQuadratic (coreRepresentation (Fin 6)) B := by
  obtain ⟨P,hBP⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Six.Perm P Six.sylow
  let Ac := A.map (MulAut.conj g).toMonoidHom
  let Bc := B.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 Ac := IsElementaryAbelian.map _
  have hBc : Bc ≤ Six.sylowCarrier := by
    rintro _ ⟨b,hb,rfl⟩
    change (MulAut.conj g) b ∈ (Six.sylow : Subgroup Six.Perm)
    rw [←hg]
    exact mem_map_of_mem _ (hBP hb)
  have hAc : Nat.card Ac = 4 := (card_map_of_injective (MulAut.conj g).injective).trans hA
  have hproper' : ¬ Bc ≤ Ac := by
    intro hc
    exact hproper ((map_le_map_iff_of_injective (MulAut.conj g).injective).mp hc)
  have hcentral' : Bc ≤ centralizer (Ac : Set Six.Perm) := by
    rintro _ ⟨b,hb,rfl⟩ _ ⟨a,ha,rfl⟩
    exact (map_mul (MulAut.conj g) a b).symm.trans
      ((congrArg (MulAut.conj g) (hcentral hb a ha)).trans (map_mul (MulAut.conj g) b a))
  have hD := larger_fixer_le_ordinary Ac Bc hAc hBc (map_mono hAB)
    hproper' hcentral' (moved_fixer_conjugate A B g hfix)
  have hquad : IsQuadratic (coreRepresentation (Fin 6)) Bc :=
    fun a ha b hb v => PlaneMovement.ordinary_core_quadratic a (hD ha) b (hD hb) v
  have hh := PlaneMovement.quadratic_conjugate (coreRepresentation (Fin 6)) Bc hquad g⁻¹
  have he : Bc.map (MulAut.conj g⁻¹).toMonoidHom = B := by
    rw [map_map]
    have hi : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id _ := by ext x; simp [MulAut.conj_apply,mul_assoc]
    rw [hi,map_id]
  rwa [he] at hh

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
