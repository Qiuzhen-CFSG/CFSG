module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.EvenModels.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.SimpleSection
public import Theory.SpecificGroups.PSL3Two.EmbeddingObstructions
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Coverage
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.GroupTheory.QuaternionSylowInvolution
public import BenderSuzuki.External.Huppert.II.theorem_8_27
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder

/-!
# Excluding the genuine Ree F₄ field components

An inner involution of an actual Ree carrier centralizes the marked
`PSL₃(2)` component.  The proved normalizer cover puts the resulting
two-subgroup in a conjugate full parabolic.  Its linear or Suzuki Levi
projection has a two-group kernel, so simplicity of the marked component makes
the projection faithful.  The second factor is killed by perfectness, leaving
an embedding into binary `PSL₂` or Suzuki.  The involution obstruction for the
former and the three-free order of the latter give the contradiction.

The proved large Ree automorphism theorem supplies innerness. Simplicity and
nonabelianness inherited from `SimpleInput` make the carrier centerless, so the
inner representative is itself an involution. Thus the final exclusion has
no additional model premise. The coefficient field is the actual Ree field,
of cardinal `2 ^ (2 * m + 1)`.

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1137; Theorem C and
Remark A.2.4, printed p.33; the Ree automorphism input in F.1.12, printed
pp.263--264 of `refs/quasithin.pdf`.
-/

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification

universe u

variable {S : Type u} [Group S] (s : SimpleInput S)

private abbrev markedComponentEmbedding : Matrix.PSL3Two.PSL →* S :=
  s.involution.fixedSubgroup.subtype.comp
    (s.component.subtype.comp s.equiv.symm.toMonoidHom)

private theorem projection_comp_injective
    {C P A B : Type*} [Group C] [Group P] [Group A] [Group B]
    [Finite C] [Finite P] [IsSimpleGroup C] [Group.IsPerfect C]
    (i : C →* P) (hi : Function.Injective i)
    (π : P →* A × B) (hπ : IsPGroup 2 π.ker) :
    Function.Injective (π.comp i) := by
  let f : C →* A × B := π.comp i
  have hf : Function.Injective f := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker f.normal_ker with hbot | htop
    · exact (MonoidHom.ker_eq_bot_iff f).mp hbot
    · let k : C →* π.ker := i.codRestrict _ (fun x => by
        apply MonoidHom.mem_ker.mpr
        have hx : x ∈ f.ker := htop.symm ▸ Subgroup.mem_top x
        exact MonoidHom.mem_ker.mp hx)
      have hk : Function.Injective k :=
        (MonoidHom.injective_codRestrict i π.ker _).2 hi
      let _ : Group.IsSolvable π.ker :=
        @IsNilpotent.to_isSolvable _ _ hπ.isNilpotent
      exact (Group.IsPerfect.not_isSolvable C
        (Group.isSolvable_of_isSolvable_injective hk)).elim
  exact hf

private theorem projection_first_injective
    {C A B : Type*} [Group C] [Group A] [Group B]
    [IsMulCommutative B] [Group.IsPerfect C]
    (f : C →* A × B) (hf : Function.Injective f) :
    Function.Injective ((MonoidHom.fst A B).comp f) := by
  let u : C →* B := (MonoidHom.snd A B).comp f
  have hu (x : C) : u x = 1 := by
    have hmap : (commutator C).map u = ⊥ := by
      change Subgroup.map u ⁅(⊤ : Subgroup C), ⊤⁆ = ⊥
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_self_eq_bot_iff.mpr inferInstance
    have hx : u x ∈ (commutator C).map u :=
      Subgroup.mem_map_of_mem u Group.IsPerfect.mem_commutator
    rw [hmap] at hx
    exact mem_bot.mp hx
  intro x y hxy
  apply hf
  apply Prod.ext hxy
  exact (hu x).trans (hu y).symm

private theorem centralizes_marked_component
    {m : ℕ} (e : S ≃* ReeF4.Model m)
    {g : ReeF4.Model m} (ha : MulAut.congr e s.involution = MulAut.conj g) :
    ∀ y : Matrix.PSL3Two.PSL,
      Commute g (e (markedComponentEmbedding s y)) := by
  intro y
  have hfix : (MulAut.congr e s.involution)
      (e (markedComponentEmbedding s y)) =
      e (markedComponentEmbedding s y) := by
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    apply congrArg e
    apply (MulAut.mem_fixedSubgroup _ _).mp
    exact (s.equiv.symm y).val.property
  rw [ha, MulAut.conj_apply] at hfix
  rw [commute_iff_eq]
  exact mul_inv_eq_iff_eq_mul.mp hfix

private theorem ree_component_in_parabolic
    {m : ℕ} (hm : 1 ≤ m) (e : S ≃* ReeF4.Model m)
    {g : ReeF4.Model m} (hg : IsInvolution g)
    (ha : MulAut.congr e s.involution = MulAut.conj g) :
    ∃ (_w : ReeF4.Model m) (side : ReeF4.LargeLocalSeeds.Side)
      (i : Matrix.PSL3Two.PSL →* ReeF4.ConverseParabolics.parabolic m side),
      Function.Injective i := by
  let R : Subgroup (ReeF4.Model m) := Subgroup.zpowers g
  have hR : R ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hg.1
  have hp : IsPGroup 2 R := BenderSuzuki.PFAppendixII.isPGroup_zpowers_of_involution hg
  obtain ⟨w, side, hcover⟩ := ReeF4.ConverseParabolics.normalizer_cover hm R hR hp
  have hyP (y : Matrix.PSL3Two.PSL) :
      (MulAut.conj w) (e (markedComponentEmbedding s y)) ∈
        ReeF4.ConverseParabolics.parabolic m side := by
    apply hcover
    apply Subgroup.mem_map_of_mem
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    have hc : (MulAut.conj (e (markedComponentEmbedding s y))) g = g := by
      rw [MulAut.conj_apply]
      exact mul_inv_eq_iff_eq_mul.mpr
        (centralizes_marked_component s e ha y).eq.symm
    change Subgroup.zpowers ((MulAut.conj (e (markedComponentEmbedding s y))) g) =
      Subgroup.zpowers g
    rw [hc]
  let j : Matrix.PSL3Two.PSL →* ReeF4.Model m :=
    (MulAut.conj w).toMonoidHom.comp
      (e.toMonoidHom.comp (markedComponentEmbedding s))
  let i : Matrix.PSL3Two.PSL →* ReeF4.ConverseParabolics.parabolic m side :=
    j.codRestrict _ hyP
  refine ⟨w, side, i, ?_⟩
  have hmark : Function.Injective (markedComponentEmbedding s) := by
    intro x y hxy
    apply s.equiv.symm.injective
    apply Subtype.ext
    apply Subtype.ext
    exact hxy
  exact (MonoidHom.injective_codRestrict j _ _).mpr
    ((MulAut.conj w).injective.comp (e.injective.comp hmark))

include s

/-- A genuine Ree `F₄` field model is excluded once its involutions are inner.
The innerness premise is the precise output required from the large
automorphism theorem used by the source assembly. -/
theorem SimpleInput.not_reeF4_of_inner {m : ℕ} (hm : 1 ≤ m)
    (hinner : ∀ a : MulAut (ReeF4.Model m), IsInvolution a →
      ∃ g : ReeF4.Model m, IsInvolution g ∧ MulAut.conj g = a) :
    ¬ Nonempty (S ≃* ReeF4.Model m) := by
  rintro ⟨e⟩
  let a : MulAut (ReeF4.Model m) := MulAut.congr e s.involution
  have ha_order : orderOf a = 2 := by
    exact (orderOf_injective (MulAut.congr e).toMonoidHom
      (MulAut.congr e).injective s.involution).trans s.involution_order
  have ha : IsInvolution a := by
    rcases (orderOf_eq_prime_iff).mp ha_order with ⟨hsq, hne⟩
    exact ⟨hne, hsq⟩
  obtain ⟨g, hg, hconj⟩ := hinner a ha
  obtain ⟨w, side, i, hi⟩ :=
    ree_component_in_parabolic s hm e hg hconj.symm
  cases side with
  | linear =>
      let π := ReeF4.ConverseParabolics.linearProjection hm
      let f := π.comp i
      let _ : IsSimpleGroup Matrix.PSL3Two.PSL :=
        Atlas.psl_simple_high_rank 3 (by decide)
      let _ : Group.IsPerfect Matrix.PSL3Two.PSL := Atlas.psl_perfect 3 (by decide)
      have hf : Function.Injective f :=
        projection_comp_injective i hi π
          (ReeF4.ConverseParabolics.linearProjection_ker_isPGroup hm)
      let q : Matrix.PSL3Two.PSL →*
          BenderSuzuki.MatrixGroups.PSL2MatrixGroup (ReeF4.CoefficientField m) :=
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL
          (F := ReeF4.CoefficientField m)).toMonoidHom.comp
          ((MonoidHom.fst _ _).comp f)
      have hq : Function.Injective q :=
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL
          (F := ReeF4.CoefficientField m)).injective.comp
          (projection_first_injective f hf)
      let P : Sylow 2 (BenderSuzuki.MatrixGroups.PSL2MatrixGroup
          (ReeF4.CoefficientField m)) := default
      obtain ⟨d⟩ :=
        BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive
          (ReeF4.field_card m) P
      exact Matrix.PSL3Two.not_injective_of_sylow_involutions_commute P
        (fun x y _ _ => d.symm.injective (by
          simp only [map_mul]
          exact mul_comm _ _)) q hq
  | suzuki =>
      let π := ReeF4.ConverseParabolics.suzukiProjection hm
      let f := π.comp i
      let _ : IsSimpleGroup Matrix.PSL3Two.PSL :=
        Atlas.psl_simple_high_rank 3 (by decide)
      let _ : Group.IsPerfect Matrix.PSL3Two.PSL := Atlas.psl_perfect 3 (by decide)
      have hf : Function.Injective f :=
        projection_comp_injective i hi π
          (ReeF4.ConverseParabolics.suzukiProjection_ker_isPGroup hm)
      have hq : Function.Injective ((MonoidHom.fst _ _).comp f) :=
        projection_first_injective f hf
      have hcard := Subgroup.card_dvd_of_injective ((MonoidHom.fst _ _).comp f) hq
      rw [Matrix.PSL3Two.card_PSL] at hcard
      have hthree : 3 ∣
          Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
        dvd_trans (by norm_num) hcard
      exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega) hthree

/-- The genuine Ree family cannot occur in the field-component sieve.
The source input supplies simplicity and nonabelianness; the large Ree
automorphism theorem discharges the innerness premise of the parabolic
obstruction, with no additional model hypotheses. -/
theorem SimpleInput.not_reeF4 {m : ℕ} (hm : 1 ≤ m) :
    ¬ Nonempty (S ≃* ReeF4.Model m) := by
  rintro ⟨e⟩
  let : IsSimpleGroup S := s.simple
  let : Group.IsPerfect S := ⟨(inferInstance : (commutator S).Normal).eq_bot_or_eq_top.resolve_left
    (fun h => s.nonabelian ((commutator_eq_bot_iff S).mp h))⟩
  let : IsSimpleGroup (ReeF4.Model m) := e.symm.isSimpleGroup
  let : Group.IsPerfect (ReeF4.Model m) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  apply s.not_reeF4_of_inner hm ?_ ⟨e⟩
  intro a ha
  obtain ⟨g, hg⟩ := ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.inner_of_sq_eq_one
    hm a ha.2
  refine ⟨g, ⟨?_, ?_⟩, hg⟩
  · intro he
    exact ha.1 (by rw [← hg, he, map_one])
  · apply MulAut.conj_injective_of_center_eq_bot center_eq_bot_of_simple_perfect
    rw [map_pow, hg, ha.2, map_one]

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
