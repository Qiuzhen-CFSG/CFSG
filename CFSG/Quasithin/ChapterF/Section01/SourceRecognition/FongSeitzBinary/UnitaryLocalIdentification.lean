module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LocalFactorCenter
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Valence
public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison

/-!
# Original special and projective unitary local identification

The full original Borel-panel comparison and the actual unitary
Sylow-normalizer index give root order q cubed, including q = 2 and
arbitrary Hermitian forms. The injective canonical root projection is
therefore onto the original quotient Sylow. For a perfect original
factor, the canonical root-generated group is its SAME SU3 or PSU3
quotient, before (2B). Its panel kernel is exactly its center.

In the special-unitary case the actual scalar projection has exactly
that kernel. Once the explicit (2B) containment is supplied, it descends
to an isomorphism of the local permutation group with PSU3. The whole
original root cover remains SU3. All comparison formulas retain the
original factor lift, two-core quotient and scalar projection. The
projective-unitary branch is treated with the corresponding trivial
central kernel. Perfectness excludes degree nine and all solvable local
actions without assuming a field bound or (2B).

Source: Fong--Seitz I (2A)--(2B), (5C), pp.7--9,25--26;
Huppert II.10.12; Aschbacher--Smith F.1.1--3, pp.259--260.
Unitary (2B), nonperfect local recognition, rank-two model selection and
both marked endpoint lifts remain with the complete source assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
open HermitianForm

private instance {E : Type*} [Field E] [Finite E] : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

private theorem psu_sylow_card {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card T = (2^n)^3 := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  obtain ⟨a⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J (2^n) hcard hf
  let T' := T.mapSurjective (f := a.toMonoidHom) a.surjective
  let b : T ≃* T' := (T : Subgroup _).equivMapOfInjective a.toMonoidHom a.injective
  rw [Nat.card_congr b.toEquiv,
    Nat.card_congr (T'.equiv (EvenTwoRank.rootSylow
      (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J) rfl hn hcard hf)).toEquiv]
  change Nat.card (OddPrimeSylow.NormalizedOuter.Coverage.rootGroup
    (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J) rfl) = _
  exact OddPrimeSylow.NormalizedOuter.Coverage.rootGroup_card _ rfl _ hcard hf

private theorem su_sylow_card {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (T : Sylow 2 J.specialSubgroup) : Nat.card T = (2^n)^3 :=
  (Nat.card_congr (SylowOmega.specialSylowEquivProjective J T).toEquiv).trans
    (psu_sylow_card J hn hcard hconj _)

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)
  [Finite (L i)] (hp : Group.IsPerfect (L i))
  (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
  {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2^n)^2)
  (hconj : ∀ x, J.conj x = x^(2^n))
  (μ : ((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)

include e h hT hn hcard hconj μ in
theorem projectiveUnitary_simpleRoot_card_eq_quotientSylow :
    Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow T) := by
  let T' := (quotientSylow T).mapSurjective (f := μ.toMonoidHom) μ.surjective
  let a : quotientSylow T ≃* T' :=
    (quotientSylow T : Subgroup _).equivMapOfInjective μ.toMonoidHom μ.injective
  have he := Nat.card_congr ((localBorelPanel Q e h i).symm.trans
    (localBorelModelCosetEquiv (L i) S T hT μ))
  have hindex := singleton_parabolic_root_index Q split i
  change Nat.card (Panel Q i) = 1 + Nat.card (simpleRoot Q split i) at hindex
  have hm := psu_sylow_normalizer_index J n hn hcard hconj T'
  change Nat.card (ProjectiveSpecialUnitaryMatrixGroup J ⧸ sylowNormalizer T') = _ at hm
  have hc := psu_sylow_card J hn hcard hconj T'
  have hs := Nat.card_congr a.toEquiv
  have he' : 1 + Nat.card (simpleRoot Q split i) = (2^n)^3+1 := hindex.symm.trans (he.trans hm)
  omega

include e h hT hn hcard hconj μ in
theorem projectiveUnitary_simpleRoot_card :
    Nat.card (simpleRoot Q split i) = (2^n)^3 := by
  rw [projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split i T hT J hn hcard hconj μ]
  let T' := (quotientSylow T).mapSurjective (f := μ.toMonoidHom) μ.surjective
  let a : quotientSylow T ≃* T' :=
    (quotientSylow T : Subgroup _).equivMapOfInjective μ.toMonoidHom μ.injective
  exact (Nat.card_congr a.toEquiv).trans (psu_sylow_card J hn hcard hconj T')

include hn hcard hconj μ in
theorem projectiveUnitary_simpleRootSylowProjection_surjective :
    Function.Surjective (simpleRootSylowProjection Q e h split i hp T hT) :=
  ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨simpleRootSylowProjection_injective Q e h split i hp T hT,
      projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split i T hT J hn hcard hconj μ⟩).2

def projectiveUnitaryRankOneEquiv : rankOne Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  (rankOneQuotientEquiv Q e h split i hp T hT
    (projectiveUnitary_simpleRootSylowProjection_surjective Q e h split i hp T hT J hn hcard hconj μ)).trans μ

@[simp] theorem projectiveUnitaryRankOneEquiv_apply (r : rankOne Q split i) :
    projectiveUnitaryRankOneEquiv Q e h split i hp T hT J hn hcard hconj μ r =
      μ (QuotientGroup.mk' (pCore 2 (L i)) (rankOneLift Q e h split i hp r)) := by
  rw [projectiveUnitaryRankOneEquiv, MulEquiv.trans_apply, rankOneQuotientEquiv_apply]

include e h hp hT hn hcard hconj μ in
theorem projectiveUnitary_root_local_projection_injective :
    Function.Injective (RootLocalCover.projection Q split i) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro r hr
  let a := projectiveUnitaryRankOneEquiv Q e h split i hp T hT J hn hcard hconj μ
  have hz := MulEquivClass.apply_mem_center a (RootLocalCover.projection_ker_central Q split i hr)
  change a r ∈ center (ProjectiveSpecialUnitaryMatrixGroup J) at hz
  rw [EvenProjectiveComparison.center_eq_bot J hn hcard hconj, mem_bot] at hz
  exact a.injective (hz.trans a.map_one.symm)


section Special
variable (ν : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup)

include e h hT hn hcard hconj ν in
theorem specialUnitary_simpleRoot_card_eq_quotientSylow :
    Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow T) := by
  let T' := (quotientSylow T).mapSurjective (f := ν.toMonoidHom) ν.surjective
  let a : quotientSylow T ≃* T' :=
    (quotientSylow T : Subgroup _).equivMapOfInjective ν.toMonoidHom ν.injective
  have he := Nat.card_congr ((localBorelPanel Q e h i).symm.trans
    (localBorelModelCosetEquiv (L i) S T hT ν))
  have hindex := singleton_parabolic_root_index Q split i
  change Nat.card (Panel Q i) = 1 + Nat.card (simpleRoot Q split i) at hindex
  have hm := su_sylow_normalizer_index J n hn hcard hconj T'
  change Nat.card (J.specialSubgroup ⧸ sylowNormalizer T') = _ at hm
  have hc := su_sylow_card J hn hcard hconj T'
  have hs := Nat.card_congr a.toEquiv
  have he' : 1 + Nat.card (simpleRoot Q split i) = (2^n)^3+1 := hindex.symm.trans (he.trans hm)
  omega

include e h hT hn hcard hconj ν in
theorem specialUnitary_simpleRoot_card :
    Nat.card (simpleRoot Q split i) = (2^n)^3 := by
  rw [specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split i T hT J hn hcard hconj ν]
  let T' := (quotientSylow T).mapSurjective (f := ν.toMonoidHom) ν.surjective
  let a : quotientSylow T ≃* T' :=
    (quotientSylow T : Subgroup _).equivMapOfInjective ν.toMonoidHom ν.injective
  exact (Nat.card_congr a.toEquiv).trans (su_sylow_card J hn hcard hconj T')

include hn hcard hconj ν in
theorem specialUnitary_simpleRootSylowProjection_surjective :
    Function.Surjective (simpleRootSylowProjection Q e h split i hp T hT) :=
  ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨simpleRootSylowProjection_injective Q e h split i hp T hT,
      specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split i T hT J hn hcard hconj ν⟩).2

def specialUnitaryRankOneEquiv : rankOne Q split i ≃* J.specialSubgroup :=
  (rankOneQuotientEquiv Q e h split i hp T hT
    (specialUnitary_simpleRootSylowProjection_surjective Q e h split i hp T hT J hn hcard hconj ν)).trans ν

@[simp] theorem specialUnitaryRankOneEquiv_apply (r : rankOne Q split i) :
    specialUnitaryRankOneEquiv Q e h split i hp T hT J hn hcard hconj ν r =
      ν (QuotientGroup.mk' (pCore 2 (L i)) (rankOneLift Q e h split i hp r)) := by
  rw [specialUnitaryRankOneEquiv, MulEquiv.trans_apply, rankOneQuotientEquiv_apply]


end Special

include e h hp hT hn hcard hconj μ in
/-- The actual local action is not solvable, excluding the solvable type VI branch. -/
theorem projectiveUnitary_local_not_isSolvable :
    ¬ Group.IsSolvable (localGroup Q split i) :=
  localGroup_not_isSolvable_of_full_sylow Q e h split i hp T hT
    (projectiveUnitary_simpleRootSylowProjection_surjective Q e h split i hp T hT J hn hcard hconj μ)

omit [Finite (L i)] in
include hp hn hcard hconj μ in
/-- The projective model excludes the degree-nine exception on the perfect branch. -/
theorem projectiveUnitary_parameter_ge_two : 2 ≤ n := by
  let : Group.IsPerfect (L i) := hp
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Group.IsPerfect.ofSurjective (f := μ.toMonoidHom) μ.surjective
  exact Unitary.CartanPanel.parameter_ge_two J n hn hcard hconj

include e h hp split hT hn hcard hconj μ in
theorem projectiveUnitary_panel_card_ne_nine : Nat.card (Panel Q i) ≠ 9 := by
  have hc := singleton_parabolic_root_index Q split i
  change Nat.card (Panel Q i) = 1 + Nat.card (simpleRoot Q split i) at hc
  rw [projectiveUnitary_simpleRoot_card Q e h split i T hT J hn hcard hconj μ] at hc
  have hn2 := projectiveUnitary_parameter_ge_two i hp J hn hcard hconj μ
  have hq : 4 ≤ 2^n := (by decide : 4 = (2:ℕ)^2) ▸ Nat.pow_le_pow_right (by decide) hn2
  have hcube : 64 ≤ (2^n)^3 := (by decide : 64 = (4:ℕ)^3) ▸ Nat.pow_le_pow_left hq 3
  omega

def projectiveUnitaryLocalEquiv (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    localGroup Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  (MulEquiv.ofBijective (RootLocalCover.projection Q split i)
    ⟨projectiveUnitary_root_local_projection_injective Q e h split i hp T hT J hn hcard hconj μ,
      (RootLocalCover.central_odd_cover Q split i hV).1⟩).symm.trans
        (projectiveUnitaryRankOneEquiv Q e h split i hp T hT J hn hcard hconj μ)

@[simp] theorem projectiveUnitaryLocalEquiv_projection
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (r : rankOne Q split i) :
    projectiveUnitaryLocalEquiv Q e h split i hp T hT J hn hcard hconj μ hV
      (RootLocalCover.projection Q split i r) =
      μ (QuotientGroup.mk' (pCore 2 (L i)) (rankOneLift Q e h split i hp r)) := by
  let a := MulEquiv.ofBijective (RootLocalCover.projection Q split i)
    ⟨projectiveUnitary_root_local_projection_injective Q e h split i hp T hT J hn hcard hconj μ,
      (RootLocalCover.central_odd_cover Q split i hV).1⟩
  change projectiveUnitaryRankOneEquiv Q e h split i hp T hT J hn hcard hconj μ (a.symm (a r)) = _
  rw [MulEquiv.symm_apply_apply, projectiveUnitaryRankOneEquiv_apply]

def originalProjectiveUnitaryRankOneEquiv :
    originalRankOne Q e split i ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  (originalRankOneEquiv Q e split i).trans
    (projectiveUnitaryRankOneEquiv Q e h split i hp T hT J hn hcard hconj μ)

@[simp] theorem originalProjectiveUnitaryRankOneEquiv_projection
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (r : originalRankOne Q e split i) :
    originalProjectiveUnitaryRankOneEquiv Q e h split i hp T hT J hn hcard hconj μ r =
      projectiveUnitaryLocalEquiv Q e h split i hp T hT J hn hcard hconj μ hV
        (originalRootProjection Q e split i r) := by
  have hr : originalRootProjection Q e split i r =
      RootLocalCover.projection Q split i (originalRankOneEquiv Q e split i r) := by
    apply Subtype.ext
    rw [originalRootProjection_apply, RootLocalCover.projection_apply]
  rw [hr]
  change projectiveUnitaryRankOneEquiv Q e h split i hp T hT J hn hcard hconj μ
    (originalRankOneEquiv Q e split i r) = _
  rw [projectiveUnitaryLocalEquiv_projection, projectiveUnitaryRankOneEquiv_apply]

def originalProjectiveUnitaryCoverEquiv (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    letI := originalRadicalInClosure_normal Q e h split i
    (originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i) ≃* ProjectiveSpecialUnitaryMatrixGroup J := by
  letI := originalRadicalInClosure_normal Q e h split i
  exact (originalRootCoverEquiv Q e h split i hV).symm.trans
    (originalProjectiveUnitaryRankOneEquiv Q e h split i hp T hT J hn hcard hconj μ)

@[simp] theorem originalProjectiveUnitaryCoverEquiv_mk
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (r : originalRankOne Q e split i) :
    letI := originalRadicalInClosure_normal Q e h split i
    originalProjectiveUnitaryCoverEquiv Q e h split i hp T hT J hn hcard hconj μ hV
      (QuotientGroup.mk' (originalRadicalInClosure Q e split i)
        (inclusion (originalRankOne_le_localClosure Q e split i) r)) =
      μ (QuotientGroup.mk' (pCore 2 (L i))
        (rankOneLift Q e h split i hp (originalRankOneEquiv Q e split i r))) := by
  let := originalRadicalInClosure_normal Q e h split i
  rw [← originalRootCoverEquiv_apply Q e h split i hV r]
  change originalProjectiveUnitaryRankOneEquiv Q e h split i hp T hT J hn hcard hconj μ
    ((originalRootCoverEquiv Q e h split i hV).symm
      (originalRootCoverEquiv Q e h split i hV r)) = _
  rw [MulEquiv.symm_apply_apply]
  exact projectiveUnitaryRankOneEquiv_apply Q e h split i hp T hT J hn hcard hconj μ _


section Special
variable (ν : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup)

/-- The actual map to the projective model, retaining the scalar quotient. -/
def specialUnitaryProjectiveMap : rankOne Q split i →* ProjectiveSpecialUnitaryMatrixGroup J :=
  J.specialToProjective.comp
    (specialUnitaryRankOneEquiv Q e h split i hp T hT J hn hcard hconj ν).toMonoidHom

@[simp] theorem specialUnitaryProjectiveMap_apply (r : rankOne Q split i) :
    specialUnitaryProjectiveMap Q e h split i hp T hT J hn hcard hconj ν r =
      J.specialToProjective (ν (QuotientGroup.mk' (pCore 2 (L i))
        (rankOneLift Q e h split i hp r))) := by
  apply congrArg J.specialToProjective
  exact specialUnitaryRankOneEquiv_apply Q e h split i hp T hT J hn hcard hconj ν r

theorem specialUnitaryProjectiveMap_surjective :
    Function.Surjective (specialUnitaryProjectiveMap Q e h split i hp T hT J hn hcard hconj ν) :=
  J.specialToProjective_surjective.comp
    (specialUnitaryRankOneEquiv Q e h split i hp T hT J hn hcard hconj ν).surjective

/-- The projective scalar kernel is exactly the kernel of the source panel action. -/
theorem specialUnitaryProjectiveMap_ker :
    (specialUnitaryProjectiveMap Q e h split i hp T hT J hn hcard hconj ν).ker =
      (RootLocalCover.projection Q split i).ker := by
  rw [root_projection_ker_eq_center_of_full_sylow Q e h split i hp T hT
    (specialUnitary_simpleRootSylowProjection_surjective Q e h split i hp T hT J hn hcard hconj ν)]
  rw [specialUnitaryProjectiveMap, ← MonoidHom.comap_ker,
    J.specialToProjective_ker_eq_center (EvenProjectiveComparison.center_eq_bot J hn hcard hconj)]
  let a := specialUnitaryRankOneEquiv Q e h split i hp T hT J hn hcard hconj ν
  ext r
  change a r ∈ center J.specialSubgroup ↔ r ∈ center (rankOne Q split i)
  constructor
  · intro hr
    have hz := MulEquivClass.apply_mem_center a.symm hr
    change a.symm (a r) ∈ center (rankOne Q split i) at hz
    simpa only [MulEquiv.symm_apply_apply] using hz
  · exact MulEquivClass.apply_mem_center a

private def specialUnitaryLocalHom (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    localGroup Q split i →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (RootLocalCover.projection Q split i).liftOfSurjective
    (RootLocalCover.central_odd_cover Q split i hV).1
      ⟨specialUnitaryProjectiveMap Q e h split i hp T hT J hn hcard hconj ν,
        (specialUnitaryProjectiveMap_ker Q e h split i hp T hT J hn hcard hconj ν).ge⟩

private theorem specialUnitaryLocalHom_projection
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (r : rankOne Q split i) :
    specialUnitaryLocalHom Q e h split i hp T hT J hn hcard hconj ν hV
      (RootLocalCover.projection Q split i r) =
      specialUnitaryProjectiveMap Q e h split i hp T hT J hn hcard hconj ν r := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

private theorem specialUnitaryLocalHom_bijective
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    Function.Bijective (specialUnitaryLocalHom Q e h split i hp T hT J hn hcard hconj ν hV) := by
  let f := specialUnitaryLocalHom Q e h split i hp T hT J hn hcard hconj ν hV
  constructor
  · apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro x hx
    obtain ⟨r,rfl⟩ := (RootLocalCover.central_odd_cover Q split i hV).1 x
    have he : specialUnitaryProjectiveMap Q e h split i hp T hT J hn hcard hconj ν r = 1 := by
      rw [← specialUnitaryLocalHom_projection Q e h split i hp T hT J hn hcard hconj ν hV]
      exact hx
    have hk : r ∈ (RootLocalCover.projection Q split i).ker := by
      rw [← specialUnitaryProjectiveMap_ker Q e h split i hp T hT J hn hcard hconj ν]
      exact he
    exact hk
  · intro x
    obtain ⟨r,rfl⟩ := specialUnitaryProjectiveMap_surjective Q e h split i hp T hT J hn hcard hconj ν x
    exact ⟨RootLocalCover.projection Q split i r,
      specialUnitaryLocalHom_projection Q e h split i hp T hT J hn hcard hconj ν hV r⟩

/-- The special original quotient gives its faithful PROJECTIVE local group. -/
def specialUnitaryLocalEquiv (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    localGroup Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  MulEquiv.ofBijective (specialUnitaryLocalHom Q e h split i hp T hT J hn hcard hconj ν hV)
    (specialUnitaryLocalHom_bijective Q e h split i hp T hT J hn hcard hconj ν hV)

@[simp] theorem specialUnitaryLocalEquiv_projection
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (r : rankOne Q split i) :
    specialUnitaryLocalEquiv Q e h split i hp T hT J hn hcard hconj ν hV
      (RootLocalCover.projection Q split i r) =
      J.specialToProjective (ν (QuotientGroup.mk' (pCore 2 (L i))
        (rankOneLift Q e h split i hp r))) := by
  exact (specialUnitaryLocalHom_projection Q e h split i hp T hT J hn hcard hconj ν hV r).trans
    (specialUnitaryProjectiveMap_apply Q e h split i hp T hT J hn hcard hconj ν r)

def originalSpecialUnitaryRankOneEquiv : originalRankOne Q e split i ≃* J.specialSubgroup :=
  (originalRankOneEquiv Q e split i).trans
    (specialUnitaryRankOneEquiv Q e h split i hp T hT J hn hcard hconj ν)

@[simp] theorem originalSpecialUnitaryRankOneEquiv_projection
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (r : originalRankOne Q e split i) :
    J.specialToProjective (originalSpecialUnitaryRankOneEquiv Q e h split i hp T hT J hn hcard hconj ν r) =
      specialUnitaryLocalEquiv Q e h split i hp T hT J hn hcard hconj ν hV
        (originalRootProjection Q e split i r) := by
  have hr : originalRootProjection Q e split i r =
      RootLocalCover.projection Q split i (originalRankOneEquiv Q e split i r) := by
    apply Subtype.ext
    rw [originalRootProjection_apply, RootLocalCover.projection_apply]
  rw [hr]
  change J.specialToProjective (specialUnitaryRankOneEquiv Q e h split i hp T hT J hn hcard hconj ν
    (originalRankOneEquiv Q e split i r)) = _
  rw [specialUnitaryLocalEquiv_projection, specialUnitaryRankOneEquiv_apply]

def originalSpecialUnitaryCoverEquiv (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    letI := originalRadicalInClosure_normal Q e h split i
    (originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i) ≃* J.specialSubgroup := by
  letI := originalRadicalInClosure_normal Q e h split i
  exact (originalRootCoverEquiv Q e h split i hV).symm.trans
    (originalSpecialUnitaryRankOneEquiv Q e h split i hp T hT J hn hcard hconj ν)

@[simp] theorem originalSpecialUnitaryCoverEquiv_mk
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (r : originalRankOne Q e split i) :
    letI := originalRadicalInClosure_normal Q e h split i
    originalSpecialUnitaryCoverEquiv Q e h split i hp T hT J hn hcard hconj ν hV
      (QuotientGroup.mk' (originalRadicalInClosure Q e split i)
        (inclusion (originalRankOne_le_localClosure Q e split i) r)) =
      ν (QuotientGroup.mk' (pCore 2 (L i))
        (rankOneLift Q e h split i hp (originalRankOneEquiv Q e split i r))) := by
  let := originalRadicalInClosure_normal Q e h split i
  rw [← originalRootCoverEquiv_apply Q e h split i hV r]
  change originalSpecialUnitaryRankOneEquiv Q e h split i hp T hT J hn hcard hconj ν
    ((originalRootCoverEquiv Q e h split i hV).symm
      (originalRootCoverEquiv Q e h split i hV r)) = _
  rw [MulEquiv.symm_apply_apply]
  exact specialUnitaryRankOneEquiv_apply Q e h split i hp T hT J hn hcard hconj ν _

include e h hp hT hn hcard hconj ν in
/-- The actual local action is not solvable, excluding the solvable type VI branch. -/
theorem specialUnitary_local_not_isSolvable :
    ¬ Group.IsSolvable (localGroup Q split i) :=
  localGroup_not_isSolvable_of_full_sylow Q e h split i hp T hT
    (specialUnitary_simpleRootSylowProjection_surjective Q e h split i hp T hT J hn hcard hconj ν)

omit [Finite (L i)] in
include hp hn hcard hconj ν in
theorem specialUnitary_parameter_ge_two : 2 ≤ n := by
  let : Group.IsPerfect (L i) := hp
  let : Group.IsPerfect J.specialSubgroup :=
    Group.IsPerfect.ofSurjective (f := ν.toMonoidHom) ν.surjective
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Group.IsPerfect.ofSurjective (f := J.specialToProjective) J.specialToProjective_surjective
  exact Unitary.CartanPanel.parameter_ge_two J n hn hcard hconj

include e h hp split hT hn hcard hconj ν in
theorem specialUnitary_panel_card_ne_nine : Nat.card (Panel Q i) ≠ 9 := by
  have hc := singleton_parabolic_root_index Q split i
  change Nat.card (Panel Q i) = 1 + Nat.card (simpleRoot Q split i) at hc
  rw [specialUnitary_simpleRoot_card Q e h split i T hT J hn hcard hconj ν] at hc
  have hn2 := specialUnitary_parameter_ge_two i hp J hn hcard hconj ν
  have hq : 4 ≤ 2^n := (by decide : 4 = (2:ℕ)^2) ▸ Nat.pow_le_pow_right (by decide) hn2
  have hcube : 64 ≤ (2^n)^3 := (by decide : 64 = (4:ℕ)^3) ▸ Nat.pow_le_pow_left hq 3
  omega

end Special
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
