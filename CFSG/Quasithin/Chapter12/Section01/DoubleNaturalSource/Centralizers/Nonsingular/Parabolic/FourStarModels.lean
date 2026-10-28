module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.LinearThreeStarExclusion
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.BinaryThreeSection

/-!
# The degree-four star-component catalogue

A proper subgroup containing a full Sylow two-subgroup and a perfect
PSL3(2) two-core section excludes every rank-one and rank-two model in
the proved B.5 star catalogue. The linear-three argument retains its
central projective kernel; solvability places the restricted kernel
in the original section's two-core. The remaining models are A7,
SL4(2), and SL5(2), with actual group equivalences.

`FourStarSource` supplies these hypotheses from the original degree-four
nonsingular centralizer and applies the reduction to its source consumer.
Source: Aschbacher--Smith 12.1.1, printed pp.788--789; C.2.7 and B.5.1.
The imported native model proofs retain their source attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular
open ChapterC.C27Source

private theorem section_card_dvd {B A : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    [Group A] [Finite A] (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL)
    (f : B →* A) [Group.IsSolvable f.ker] : 168 ∣ Nat.card f.range := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e.isSimpleGroup
  have hk := PerfectCoreTwoExtension.solvable_ker_le_core f
  let q : (B ⧸ f.ker) →* (B ⧸ pCore 2 B) :=
    QuotientGroup.lift f.ker (QuotientGroup.mk' (pCore 2 B)) (by
      simpa only [QuotientGroup.ker_mk'] using hk)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) x
    exact ⟨QuotientGroup.mk' f.ker b,rfl⟩
  have hd := card_dvd_of_surjective q hq
  rwa [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
    Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_PSL] at hd

private theorem no_linearThree_section {B A : Type*} [Group B] [Finite B]
    [Group.IsPerfect B] [Group A] [Finite A] [Group.IsPerfect A]
    (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL)
    (f : B →* A) [Group.IsSolvable f.ker]
    (P : Sylow 2 A) (M : Subgroup A) (hPM : (P : Subgroup A) ≤ M)
    (hfM : f.range ≤ M) (hM : M ≠ ⊤)
    (F : ChapterB.QuasisimpleSource.BinaryField) (a : A ≃* SL(3,F.Carrier)) : False := by
  let q : A →* PSL(3,F.Carrier) :=
    (QuotientGroup.mk' (center SL(3,F.Carrier))).comp a.toMonoidHom
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp a.surjective
  have hqk : q.ker ≤ center A := by
    intro x hx
    have he : a x ∈ center SL(3,F.Carrier) := (QuotientGroup.eq_one_iff _).mp hx
    have hh := (centerCongr a.symm ⟨a x,he⟩).property
    change a.symm (a x) ∈ center A at hh
    simpa only [a.symm_apply_apply] using hh
  let : Group.IsSolvable q.ker := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective hqk)
  let j := q.comp f
  let : Group.IsSolvable j.ker := isSolvable_comap_of_solvable_ker f q.ker
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e.isSimpleGroup
  have hj : IsPGroup 2 j.ker := pCore_isPGroup.to_le
    (PerfectCoreTwoExtension.solvable_ker_le_core j)
  let π := (e.trans Matrix.PSL3Two.equiv.symm).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 B))
  have hπ : Function.Surjective π :=
    (e.trans Matrix.PSL3Two.equiv.symm).surjective.comp (QuotientGroup.mk'_surjective _)
  have ht := Matrix.PSL3.LinearThree.sylow_overgroup_eq_top_of_binary_three_quotient
    F.Carrier π hπ j hj F.degree_pos F.card_eq (P.mapSurjective hq) (M.map q)
    (map_mono hPM) (by rw [MonoidHom.range_comp]; exact map_mono hfM)
  have hs : Function.Surjective (q.comp M.subtype) := by
    rw [←MonoidHom.range_eq_top,MonoidHom.range_comp,range_subtype]
    exact ht
  have hsurj := PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    q M.subtype hs hqk
  exact hM ((MonoidHom.range_eq_top.mpr hsurj).symm.trans (range_subtype M)).symm

/-- A proper full-Sylow overgroup containing the original binary-three section
leaves only A7, A8 and SL5(2) in the actual B.5 star catalogue. -/
theorem four_star_models {B A : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    [Group A] [Finite A] [Group.IsPerfect A]
    (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL)
    (f : B →* A) [Group.IsSolvable f.ker]
    (P : Sylow 2 A) (M : Subgroup A) (hPM : (P : Subgroup A) ≤ M)
    (hfM : f.range ≤ M) (hM : M ≠ ⊤) (hm : StarModels.Model A) :
    Nonempty (A ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (A ≃* SL(4,ZMod 2)) ∨ Nonempty (A ≃* SL(5,ZMod 2)) := by
  have hd : 7 ∣ Nat.card A := (by decide : 7 ∣ 168).trans
    ((section_card_dvd e f).trans (card_subgroup_dvd_card _))
  have hmap (Q : Type) [Group Q] (a : A ≃* Q) : M.map a.toMonoidHom ≠ ⊤ := by
    intro ht
    exact hM (map_injective a.injective (ht.trans (map_top_of_surjective _ a.surjective).symm))
  cases hm with
  | linearTwo F a =>
    let j := a.toMonoidHom.comp f
    let : Group.IsSolvable j.ker := by
      rw [show j.ker = f.ker from MonoidHom.ker_comp_of_injective _ _ a.injective]
      infer_instance
    exact (Matrix.SpecialLinearGroup.no_binaryLinearTwo_of_solvable_kernel e j).elim
  | linearThree F a => exact (no_linearThree_section e f P M hPM hfM hM F a).elim
  | symplectic F large a =>
    let j := a.toMonoidHom.comp f
    let : Group.IsSolvable j.ker := by
      rw [show j.ker = f.ker from MonoidHom.ker_comp_of_injective _ _ a.injective]
      infer_instance
    have hF : 2 < Nat.card F.Carrier := by
      rw [F.card_eq]
      exact lt_of_lt_of_le (by decide : 2 < 2^2)
        (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) large)
    exact (hmap _ a (Theory.SpecificGroups.SymplecticFour.linearThree_section_sylow_overgroup_eq_top
      e hF (P.mapSurjective a.surjective) (M.map a.toMonoidHom) (map_mono hPM) j
      (by rw [MonoidHom.range_comp]; exact map_mono hfM))).elim
  | g2 F large a =>
    let j := a.toMonoidHom.comp f
    let : Group.IsSolvable j.ker := by
      rw [show j.ker = f.ker from MonoidHom.ker_comp_of_injective _ _ a.injective]
      infer_instance
    have hF : 2 < Nat.card F.Carrier := by
      rw [F.card_eq]
      exact lt_of_lt_of_le (by decide : 2 < 2^2)
        (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) large)
    exact (hmap _ a (Atlas.G2.linearThree_section_sylow_overgroup_eq_top
      e hF (P.mapSurjective a.surjective) (M.map a.toMonoidHom) (map_mono hPM) j
      (by rw [MonoidHom.range_comp]; exact map_mono hfM))).elim
  | g2DerivedTwo a =>
    have h7 : 7 ∣ Nat.card (M.map a.toMonoidHom) := by
      rw [card_map_of_injective a.injective]
      exact (by decide : 7 ∣ 168).trans ((section_card_dvd e f).trans (card_dvd_of_le hfM))
    exact (hmap _ a
      (Atlas.G2.BinaryParabolicPair.SevenSylowOvergroups.eq_top_of_sylow_of_seven_dvd
        (P.mapSurjective a.surjective) (M.map a.toMonoidHom) (map_mono hPM) h7)).elim
  | alternating n hn a =>
    rcases hn with rfl | rfl | rfl | rfl
    · rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at hd
      norm_num [Nat.factorial] at hd
    · rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at hd
      norm_num [Nat.factorial] at hd
    · exact .inl ⟨a⟩
    · exact .inr (.inl ⟨a.trans
        (Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans Atlas.Order20160A8.sl4TwoEquivPSL.symm)⟩)
  | linearFiveTwo a => exact .inr (.inr ⟨a⟩)
  | tripleSix c a =>
    have hc : Nat.card A = 1080 := by
      rw [←(center A).card_mul_index,index_eq_card,Nat.card_congr c.toEquiv,
        Nat.card_congr a.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      norm_num [Nat.factorial]
    rw [hc] at hd
    norm_num at hd
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular
