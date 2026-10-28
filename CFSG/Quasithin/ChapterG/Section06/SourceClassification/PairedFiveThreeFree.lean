module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.ThreeFreeMaximal
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.PairedFiveWreathAction
public import Theory.SpecificGroups.SymmetricFive.WreathRank

/-!
# A three-free maximal subgroup excludes paired natural-five factors

The literal wreath identification puts every Sylow two-subgroup in a proper
subgroup with positive three-rank. Unique maximality puts its inverse image
in the prescribed minimal-parabolic maximal subgroup, contradicting its
three-free order. This eliminates the remaining five-letter row in the
positive-center argument, while retaining the original action and Sylow.

Source: Aschbacher–Smith, 10.2.1, printed p.743, using G.6.4.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06
variable {G : Type*} [Group G] [Finite G]

/-- The literal symmetric-five wreath actor cannot have a three-free unique
maximal subgroup above its Sylow two-subgroup. -/
theorem not_symmetricFive_wreath_of_three_free_maximal
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hthree : Nat.Coprime 3 (Nat.card (ChapterB.minimalParabolicMax T hP))) :
    ¬ Nonempty (G ≃* BinaryPermutation.FivePair.Wreath) := by
  rintro ⟨e⟩
  obtain ⟨B,hTB,hB,hBr⟩ :=
    Theory.SpecificGroups.SymmetricFive.WreathRank.exists_proper_sylow_overgroup_rank_two
      (T.mapSurjective (f := e.toMonoidHom) e.surjective)
  let K := B.comap e.toMonoidHom
  have hK : K ≠ ⊤ := by
    intro he
    have hh := congrArg (map e.toMonoidHom) he
    rw [map_comap_eq_self_of_surjective e.surjective,
      map_top_of_surjective e.toMonoidHom e.surjective] at hh
    exact hB hh
  have hTK : (T : Subgroup G) ≤ K := map_le_iff_le_comap.mp hTB
  have hKM : K ≤ ChapterB.minimalParabolicMax T hP := hP.1.le_maximal
    ⟨(ChapterB.minimalParabolicMax_spec T hP).2,
      (ChapterB.minimalParabolicMax_spec T hP).1.covBy_top⟩ hTK
    (lt_top_iff_ne_top.mpr hK)
  have hBc : 3 ∣ Nat.card B := by
    by_contra hn
    have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hn
    omega
  have hKc : Nat.card K = Nat.card B := by
    rw [←card_map_of_injective (f := e.toMonoidHom) e.injective,
      map_comap_eq_self_of_surjective e.surjective]
  have hd : 3 ∣ Nat.card (ChapterB.minimalParabolicMax T hP) :=
    (hKc ▸ hBc).trans (card_dvd_of_le hKM)
  have hh := hthree.coprime_dvd_right hd
  norm_num at hh

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {a : G}

/-- The paired-five alternative is excluded for the original faithful action. -/
theorem TwoFactors.not_paired_five_of_three_free_maximal
    (d : TwoFactors ρ a) (hf : Function.Injective ρ)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hthree : Nat.Coprime 3 (Nat.card (ChapterB.minimalParabolicMax T hP)))
    (h₁ : HasModelOn ρ d.first (subspaceCommutator ρ ⊤ d.first)
      (BinaryPermutation.naturalRepresentation (Fin 5)))
    (h₂ : HasModelOn ρ d.second (subspaceCommutator ρ ⊤ d.second)
      (BinaryPermutation.naturalRepresentation (Fin 5))) : False := by
  obtain ⟨_,_,e,_⟩ := d.exists_paired_five_wreath_action h₁ h₂ hf
  exact not_symmetricFive_wreath_of_three_free_maximal T hP hthree ⟨e⟩

end CFSG.Quasithin.ChapterG.Section06
