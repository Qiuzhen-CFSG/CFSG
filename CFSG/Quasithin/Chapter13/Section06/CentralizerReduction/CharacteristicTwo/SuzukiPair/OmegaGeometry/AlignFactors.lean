module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.OmegaGeometry.Factors

/-!
# Aligning a Suzuki pair without forgetting its factors

Align the two projections of the actual Sylow intersection by independent
inner automorphisms. Transport each factor marking separately, preserving
the moving element, both literal embeddings and the full factor permutation.
This refines the Borel choice in Alignment with the data needed by the
covered omega and action calculations.

Source: Aschbacher–Smith, proof of 13.6.6, p.927 / PDF p.944.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair

private theorem align (m : ℕ) (hm : 0 < m)
    (A : Subgroup (SuzukiMatrixGroup m)) (hA : IsPGroup 2 A) :
    ∃ g : SuzukiMatrixGroup m,
      A.map (MulAut.conj g).toMonoidHom ≤ SuzukiRootSubgroup m := by
  obtain ⟨P, hAP⟩ := hA.exists_le_sylow
  obtain ⟨R, hR⟩ := suzukiRootSubgroup_isSylow m hm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) P R
  have he := congrArg Sylow.toSubgroup hg
  change (P : Subgroup (SuzukiMatrixGroup m)).map (MulAut.conj g).toMonoidHom = _ at he
  rw [hR] at he
  exact ⟨g, (map_mono hAP).trans he.le⟩

variable {G : Type*} [Group G] [Finite G] {T K : Subgroup G} {v : G}

/-- Choose an aligned marking while preserving the actual pair and its permutation. -/
theorem PairFactors.exists_aligned {d : Marking T K v} (c : PairFactors d)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hKG : K ≤ Gv v) :
    ∃ (d' : Marking T K v) (c' : PairFactors d'),
      d'.parameter = d.parameter ∧ c'.moving = c.moving ∧
      ((Tv T v).subgroupOf (orbit T K v)).map d'.quotientMap ≤
        (SuzukiRootSubgroup d'.parameter).prod (SuzukiRootSubgroup d'.parameter) := by
  obtain ⟨S, hS⟩ := intersection_sylow T K v P hP hKG
  let f₁ := (MonoidHom.fst _ _).comp d.quotientMap
  let f₂ := (MonoidHom.snd _ _).comp d.quotientMap
  obtain ⟨g, hg⟩ := align d.parameter d.positive ((S : Subgroup _).map f₁)
    (S.isPGroup'.map f₁)
  obtain ⟨h, hh⟩ := align d.parameter d.positive ((S : Subgroup _).map f₂)
    (S.isPGroup'.map f₂)
  let e := MulEquiv.prodCongr (MulAut.conj g) (MulAut.conj h)
  let d' : Marking T K v := ⟨d.parameter, d.positive, d.equiv.trans e⟩
  let c' : PairFactors d' := {
    moving := c.moving
    moved := c.moved
    orbit_eq := c.orbit_eq
    permutation := c.permutation
    firstEquiv := c.firstEquiv.trans (MulAut.conj g)
    secondEquiv := c.secondEquiv.trans (MulAut.conj h)
    first_eq := by
      intro k
      change (MulAut.conj g (d.quotientMap (firstEmbedding T K v k)).1,
        MulAut.conj h (d.quotientMap (firstEmbedding T K v k)).2) = _
      rw [c.first_eq]
      exact Prod.ext rfl (map_one _)
    second_eq := by
      intro k
      change (MulAut.conj g (d.quotientMap (secondEmbedding T K v c.moving k)).1,
        MulAut.conj h (d.quotientMap (secondEmbedding T K v c.moving k)).2) = _
      rw [c.second_eq]
      exact Prod.ext (map_one _) rfl }
  refine ⟨d', c', rfl, rfl, ?_⟩
  rw [← hS]
  rintro y ⟨x, hx, rfl⟩
  exact ⟨hg (mem_map_of_mem _ (mem_map_of_mem f₁ hx)),
    hh (mem_map_of_mem _ (mem_map_of_mem f₂ hx))⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
