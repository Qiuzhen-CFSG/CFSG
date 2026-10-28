module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.Setup

/-!
# Choosing the paired Borel through the actual Sylow intersection

Project the image of T₀ to each concrete Suzuki factor. Each projection
is a two-subgroup, so Sylow conjugacy puts it in the standard root group.
Changing the two markings by these inner automorphisms then constructs a
lifted product Borel containing the original T₀. Only the marking changes;
the ambient component orbit and its full central kernel are preserved.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
open Subgroup BenderSuzuki.MatrixGroups

private theorem align_twoSubgroup (m : ℕ) (hm : 0 < m)
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

variable {G : Type*} [Group G]
variable {T K : Subgroup G} {v : G}

/-- Construct a marking whose standard product Borel contains T₀. The
two coordinate maps and the image of T₀ are kept explicit throughout. -/
theorem exists_aligned_marking (d : Marking T K v) (hT : IsPGroup 2 (Tv T v)) :
    ∃ d' : Marking T K v, d'.parameter = d.parameter ∧
      ((Tv T v).subgroupOf (orbit T K v)).map d'.quotientMap ≤
        (SuzukiRootSubgroup d'.parameter).prod (SuzukiRootSubgroup d'.parameter) := by
  let S := (Tv T v).subgroupOf (orbit T K v)
  have hS : IsPGroup 2 S := hT.of_injective
    (((orbit T K v).subtype.comp S.subtype).codRestrict (Tv T v) (fun x => x.property)) (by
      intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z : Tv T v => (z : G)) h)))
  let f := d.quotientMap
  let f₁ := (MonoidHom.fst _ _).comp f
  let f₂ := (MonoidHom.snd _ _).comp f
  obtain ⟨g, hg⟩ := align_twoSubgroup d.parameter d.positive (S.map f₁) (hS.map f₁)
  obtain ⟨h, hh⟩ := align_twoSubgroup d.parameter d.positive (S.map f₂) (hS.map f₂)
  let e := MulEquiv.prodCongr (MulAut.conj g) (MulAut.conj h)
  let d' : Marking T K v := ⟨d.parameter, d.positive, d.equiv.trans e⟩
  refine ⟨d', rfl, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact ⟨hg (mem_map_of_mem _ (mem_map_of_mem f₁ hx)),
    hh (mem_map_of_mem _ (mem_map_of_mem f₂ hx))⟩

/-- The Borel through the given T₀ is obtained from a genuine central
quotient marking, rather than supplied as a containment hypothesis. -/
theorem exists_borel_through_intersection (d : Marking T K v)
    (hT : IsPGroup 2 (Tv T v)) :
    ∃ d' : Marking T K v, d'.parameter = d.parameter ∧
      intersection T K v ≤ d'.borel := by
  obtain ⟨d', hm, ha⟩ := exists_aligned_marking d hT
  exact ⟨d', hm, d'.intersection_le_borel ha⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
