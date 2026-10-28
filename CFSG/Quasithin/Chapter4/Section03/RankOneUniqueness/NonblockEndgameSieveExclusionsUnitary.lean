module
public import Theory.GroupTheory.PerfectTwoLocalNormalizer
public import Theory.SpecificGroups.SU3.EvenOuterTwoMovement
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.PerfectCore
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import BenderSuzuki.External.Huppert.II.theorem_10_13
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveGeometry

/-!
# Excluding both binary unitary rows of the literal nonblock sieve

The identity [R₂-star,Y-star] = R₂-star forces the radical image to consist
of inner automorphisms in a PSU₃ model. A nontrivial such two-subgroup has
a solvable normalizer, whereas its actual normalizer contains the nontrivial
perfect secondary image. Thus the literal radical image is trivial, contrary
to its prescribed nontrivial action.

For SU₃, automorphisms descend faithfully through the actual central cover
to PSU₃, preserving inner images, normalization and commutators. The proof
therefore treats both source models, including the possible order-three
center. It does not infer full-image centralization from centralization
modulo the secondary two-core.

Source: Aschbacher–Smith, original 4.3.14–16 and the ensuing elimination,
printed pp.617–618. This closes row (2); deriving the source alternatives
remains with `qt-d-1222-nonblock-endgame-sieve`.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve

/-- The projective unitary model excludes the actual moved radical arrangement. -/
theorem unitary_moved_twoGroup_eq_bot {U : Type*} [Group U] [Finite U]
    {n : ℕ} (hn : 1 < n) (hm : ClassicalGroup.IsPSU U 3 (2 ^ n))
    (X : Subgroup (MulAut U)) [Group.IsPerfect X] (hne : X ≠ ⊥)
    (hiX : X ≤ MulAut.innerSubgroup U)
    (R Y : Subgroup (MulAut U)) (hR : IsPGroup 2 R)
    (hXR : X ≤ normalizer (R : Set (MulAut U))) (hmove : ⁅R,Y⁆ = R) : R = ⊥ := by
  obtain ⟨F,_,_,J,hc,hconj,⟨e⟩⟩ := hm
  obtain ⟨C,hC⟩ := ChapterF.Source.Unitary.FormTransport.exists_standard_basis J n (by omega) hc hconj
  let J₀ := ChapterF.Source.Unitary.FormTransport.standardForm J
  let b := e.trans (ChapterF.Source.Unitary.FormTransport.projectiveEquiv J C hC)
  let A := MulAut.congr b
  let V := ProjectiveSpecialUnitaryMatrixGroup J₀
  let : Finite V := Finite.of_surjective b b.surjective
  have hf : Nat.card {x : F // J₀.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J₀.conj 2 n (by omega) hc hconj
  let : IsSimpleGroup V := BenderSuzuki.External.huppert_II_10_13 J₀ (2 ^ n)
    (lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) (by omega))) hc hf
  let X' := X.map A.toMonoidHom
  let R' := R.map A.toMonoidHom
  let Y' := Y.map A.toMonoidHom
  let : Group.IsPerfect X' := Group.IsPerfect.map _
  have hx : X' ≠ ⊥ := fun he => hne ((X.map_eq_bot_iff_of_injective A.injective).mp he)
  have hix : X' ≤ MulAut.innerSubgroup V := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨g,rfl⟩ := hiX hx
    exact ⟨b g,MulAut.congr_conj b g |>.symm⟩
  have hr : IsPGroup 2 R' := hR.map _
  have hn' : X' ≤ normalizer (R' : Set (MulAut V)) :=
    (map_mono hXR).trans (R.le_normalizer_map _)
  have hm' : ⁅R',Y'⁆ = R' := by
    change ⁅R.map A.toMonoidHom,Y.map A.toMonoidHom⁆ = R.map A.toMonoidHom
    rw [← map_commutator,hmove]
  have hir := HermitianForm.EvenSemilinear.moved_twoGroup_le_inner J₀ rfl
    (by omega : 2 ≤ n) hc hconj R' Y' hr hm'
  have hz := HermitianForm.EvenProjectiveComparison.center_eq_bot J₀ (by omega : 0 < n) hc hconj
  have he := inner_twoGroup_eq_bot_of_perfect_normalizer hz
    (ChapterF.Source.Unitary.two_normalizer_solvable (by omega : 0 < n)
      (show ClassicalGroup.IsPSU V 3 (2 ^ n) from ⟨F,inferInstance,inferInstance,J₀,hc,hconj,⟨MulEquiv.refl _⟩⟩))
    X' hx hix R' hr hir hn'
  exact (R.map_eq_bot_iff_of_injective A.injective).mp he

/-- Faithful descent of the special unitary cover preserves the same exclusion. -/
theorem special_unitary_moved_twoGroup_eq_bot {U : Type*} [Group U] [Finite U]
    [Group.IsPerfect U] {n : ℕ} (hn : 1 < n)
    (hm : Chapter1.Section02.LocalModels.IsSU U 3 (2 ^ n))
    (X : Subgroup (MulAut U)) [Group.IsPerfect X] (hne : X ≠ ⊥)
    (hiX : X ≤ MulAut.innerSubgroup U)
    (R Y : Subgroup (MulAut U)) (hR : IsPGroup 2 R)
    (hXR : X ≤ normalizer (R : Set (MulAut U))) (hmove : ⁅R,Y⁆ = R) : R = ⊥ := by
  obtain ⟨F,_,_,J,hc,hconj,⟨e⟩⟩ := hm
  let V := ProjectiveSpecialUnitaryMatrixGroup J
  let : Group.IsPerfect J.specialSubgroup := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : Finite V := Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let f : PerfectCentralCovering.Cover J.specialSubgroup V := {
    toMonoidHom := J.specialToProjective
    surjective := J.specialToProjective_surjective
    isPerfect := inferInstance
    ker_le_center := J.specialToProjective_ker_le_center }
  have hk : f.toMonoidHom.ker = center J.specialSubgroup :=
    J.specialToProjective_ker_eq_center
      (HermitianForm.EvenProjectiveComparison.center_eq_bot J (by omega) hc hconj)
  let A : MulAut U →* MulAut V := (f.autMap hk).comp (MulAut.congr e).toMonoidHom
  have hA : Function.Injective A := (f.autMap_injective hk).comp (MulAut.congr e).injective
  have hinner (g : U) : A (MulAut.conj g) = MulAut.conj (f.toMonoidHom (e g)) := by
    change f.autMap hk (MulAut.congr e (MulAut.conj g)) = _
    rw [MulAut.congr_conj]
    ext v
    obtain ⟨x,rfl⟩ := f.surjective v
    rw [f.autMap_apply]
    simp only [MulAut.conj_apply,map_mul,map_inv]
  let X' := X.map A
  let R' := R.map A
  let Y' := Y.map A
  let : Group.IsPerfect X' := Group.IsPerfect.map _
  have hx : X' ≠ ⊥ := fun he => hne ((X.map_eq_bot_iff_of_injective hA).mp he)
  have hix : X' ≤ MulAut.innerSubgroup V := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨g,rfl⟩ := hiX hx
    exact ⟨f.toMonoidHom (e g),(hinner g).symm⟩
  have hn' : X' ≤ normalizer (R' : Set (MulAut V)) :=
    (map_mono hXR).trans (R.le_normalizer_map _)
  have hm' : ⁅R',Y'⁆ = R' := by
    change ⁅R.map A,Y.map A⁆ = R.map A
    rw [← map_commutator,hmove]
  have he := unitary_moved_twoGroup_eq_bot hn
    (show ClassicalGroup.IsPSU V 3 (2 ^ n) from ⟨F,inferInstance,inferInstance,J,hc,hconj,⟨MulEquiv.refl _⟩⟩)
    X' hx hix R' Y' (hR.map _) hn' hm'
  exact (R.map_eq_bot_iff_of_injective hA).mp he

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The actual secondary inner image is nontrivial because its two-core quotient is PSL₂. -/
theorem SecondaryData.secondaryImage_ne_bot (s : SecondaryData c n) :
    SecondaryData.secondaryImage s ≠ ⊥ := by
  obtain ⟨F,_,_,_,⟨e⟩⟩ := SecondaryData.secondaryImage_model s
  let : Nontrivial (SecondaryData.secondaryImage s ⧸ pCore 2 (SecondaryData.secondaryImage s)) :=
    e.surjective.nontrivial
  let : Nontrivial (SecondaryData.secondaryImage s) :=
    (QuotientGroup.mk'_surjective (pCore 2 (SecondaryData.secondaryImage s))).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance

/-- Both SU₃ and PSU₃ are incompatible with the nontrivial literal radical action. -/
theorem SecondaryData.not_unitary_model (s : SecondaryData c n) (hn : 1 < n) :
    ¬ (Chapter1.Section02.LocalModels.IsSU (s.component ⧸ pCore 2 s.component) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 (2 ^ n)) := by
  let := SecondaryData.secondaryImage_perfect s
  let := s.quasisimple
  have hi : SecondaryData.secondaryImage s ≤ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) := by
    rw [show SecondaryData.secondaryImage s = (SecondaryData.secondaryProjection s).range.map MulAut.conj from
      SecondaryData.secondary_action_image s]
    exact map_le_range _ _
  intro hm
  apply (SecondaryData.radicalImage_two s).2
  rcases hm with hm | hm
  · exact special_unitary_moved_twoGroup_eq_bot hn hm _
      (SecondaryData.secondaryImage_ne_bot s) hi _ _ (SecondaryData.radicalImage_two s).1
      (SecondaryData.image_normalization s).1 (SecondaryData.radicalImage_moved s)
  · exact unitary_moved_twoGroup_eq_bot hn hm _
      (SecondaryData.secondaryImage_ne_bot s) hi _ _ (SecondaryData.radicalImage_two s).1
      (SecondaryData.image_normalization s).1 (SecondaryData.radicalImage_moved s)
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
