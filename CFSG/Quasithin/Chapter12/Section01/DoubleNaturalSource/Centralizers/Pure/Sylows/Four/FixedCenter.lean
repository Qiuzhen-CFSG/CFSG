module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.OmegaAction
public import Theory.GroupTheory.ConjugateOrbitIndexTwo
public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# The component-fixed omega subgroup at the original pure point

The point residual and T generate LT. Its T-conjugate span therefore equals
L: the quotient by that normal span is a two-group, while L is perfect.
The index-two point Sylow reduces this span to the two actual conjugates.
Their omega-center fixed subgroups each have index two, so their intersection
is nontrivial when the omega center has order greater than four.

This intersection is T-invariant and centralizes L. The two-group center
argument gives a nontrivial L-fixed subgroup of the central omega of T.
Local normalizer uniqueness also places the full normalizer of the original
intersection inside M, as required by the subsequent parabolic argument.

Every source application keeps the original point and chosen module. Only
the binary C.1.34 implication, owned by `qt-rank-two-ms93`, remains explicit.
The remaining Thompson/parabolic argument, component exclusions and final
fusion/closure assembly belong to `qt-d-double-natural-pure-fusion`; the
final centralizer parent is `qt-d-double-natural-centralizers`.
Source: Aschbacher--Smith, 12.1.4, printed p.790.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem orbit_eq_of_perfect (X L P : Subgroup G) [Group.IsPerfect L]
    (hP : IsPGroup 2 P) (hXL : X ≤ L) (hPL : P ≤ normalizer (L : Set G))
    (hgen : X ⊔ P = L ⊔ P) : componentOrbit X P = L := by
  apply le_antisymm
  · apply iSup_le
    intro p
    rintro _ ⟨x,hx,rfl⟩
    exact (hPL p.property x).mp (hXL hx)
  · let J := X ⊔ P
    have hLJ : L ≤ J := by dsimp [J]; rw [hgen]; exact le_sup_left
    let C := (componentOrbit X P).subgroupOf J
    let := componentOrbit_normal_subgroupOf_sup X P
    let e : L.subgroupOf J ≃* L := subgroupOfEquivOfLe hLJ
    let : Group.IsPerfect (L.subgroupOf J) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    let : Group.IsNilpotent (J ⧸ C) := (local_orbit_quotient_isPGroup X P hP).isNilpotent
    have hh := le_of_isPerfect_of_solvable_quotient (L.subgroupOf J) C
    intro x hx
    exact hh (show (⟨x,hLJ hx⟩ : J) ∈ L.subgroupOf J from hx)

variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal two conjugate point residuals generate L. -/
theorem doubleNatural_four_pure_residual_conjugate_generation_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ∀ t ∈ (T : Subgroup G), t ∉ B.pointSylow w →
        B.pointResidual w ⊔ (B.pointResidual w).map (MulAut.conj t).toMonoidHom = L := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix t ht htR
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  have he := S.marked_centralizer_eq D.sylow_normalizes_component w hw hp hfix
  change B.pointSylow w = _ at he
  have hi : (B.pointSylow w).relIndex (T : Subgroup G) = 2 := by
    rw [he]
    exact S.naturalSylowNormalizer_relIndex D.sylow_normalizes_component
  have hn := (D.doubleNatural_pure_local_family_of_many h hmany B S w hw hp hfix).2
  rw [←componentOrbit_eq_sup_of_index_two (B.pointResidual w) (T : Subgroup G)
    (B.pointSylow w) hi (inf_le_right.trans hn) ht htR]
  exact orbit_eq_of_perfect _ _ _ T.isPGroup' ((B.pointResidual_le w).trans inf_le_left)
    D.sylow_normalizes_component
    (S.four_pure_residual_sup_sylow D.sylow_normalizes_component w hw hp)

omit [Finite G] in
private theorem fixed_intersection_ne_bot (X L Z : Subgroup G) (t : G)
    (hZ : 4 < Nat.card Z) (htZ : t ∈ normalizer (Z : Set G))
    (hi : (centralizer (X : Set G)).relIndex Z = 2)
    (hgen : X ⊔ X.map (MulAut.conj t).toMonoidHom = L) :
    Z ⊓ centralizer (L : Set G) ≠ ⊥ := by
  let f := (MulAut.conj t).toMonoidHom
  let C := Z ⊓ centralizer (X : Set G)
  let D := C.map f
  have hZm : Z.map f = Z := mem_normalizer_iff_map_conj_eq.mp htZ
  have hCi : C.relIndex Z = 2 := (inf_relIndex_left _ _).trans hi
  have hDi : D.relIndex Z = 2 := by
    change (C.map f).relIndex Z = 2
    rw [←hZm,relIndex_map_map_of_injective _ _ (MulAut.conj t).injective]
    exact hCi
  have hne : C ⊓ D ≠ ⊥ := by
    intro hb
    have hh := relIndex_inf_le (H := C) (K := D) (L := Z)
    rw [hb,relIndex_bot_left,hCi,hDi] at hh
    omega
  apply ne_bot_of_le_ne_bot hne
  intro x hx
  refine ⟨hx.1.1,?_⟩
  apply le_centralizer_iff.mp ?_ (show x ∈ C ⊓ D from hx)
  rw [←hgen]
  apply sup_le
  · exact le_centralizer_iff.mpr (inf_le_left.trans inf_le_right)
  · intro y hy z hz
    obtain ⟨y,hy,rfl⟩ := hy
    obtain ⟨z,hzC,rfl⟩ := hz.2
    simpa only [map_mul] using (congrArg f (hzC.2 y hy)).symm

/-- The nontrivial component-fixed subgroup of Ω₁(Z(T₁)) forced by source 12.1.4. -/
theorem doubleNatural_four_pure_omega_fixed_ne_bot_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (classification : BinaryLinearThreeMSClassification KnownSimple.IsKnownSimple.{u}) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      Subgroup.omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥ := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  obtain ⟨hcard,hi⟩ := D.doubleNatural_four_pure_omega_index_of_many h hmany B classification S w hw hp hfix hf
  have he := S.marked_centralizer_eq D.sylow_normalizes_component w hw hp hfix
  change B.pointSylow w = _ at he
  have hidx : (B.pointSylow w).relIndex (T : Subgroup G) = 2 := by
    rw [he]
    exact S.naturalSylowNormalizer_relIndex D.sylow_normalizes_component
  have hnot : ¬ (T : Subgroup G) ≤ B.pointSylow w := by
    intro hh
    have h1 := relIndex_eq_one.mpr hh
    omega
  obtain ⟨t,ht,htR⟩ := SetLike.not_le_iff_exists.mp hnot
  let := normal_of_index_eq_two hidx
  have hn : (T : Subgroup G) ≤ normalizer (B.pointSylow w : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show B.pointSylow w ≤ (T : Subgroup G) from inf_le_left)).mp inferInstance
  exact fixed_intersection_ne_bot _ _ _ t hcard
    ((hn.trans (normalizer_le_normalizer_omegaCenterIn _)) ht) hi
    (D.doubleNatural_four_pure_residual_conjugate_generation_of_many h hmany B S w hw hp hfix t ht htR)


private theorem ambient_omega_fixed_ne_bot (T : Sylow 2 G) (R L : Subgroup G)
    (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : Subgroup.omegaCenterIn R ⊓ centralizer (L : Set G) ≠ ⊥) :
    Subgroup.omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G) ≠ ⊥ := by
  let A := Subgroup.omegaCenterIn R ⊓ centralizer (L : Set G)
  have hAT : A ≤ (T : Subgroup G) := inf_le_left.trans ((map_subtype_le _).trans hRT)
  have hn : (T : Subgroup G) ≤ normalizer (A : Set G) :=
    (le_inf (hTR.trans (normalizer_le_normalizer_omegaCenterIn R))
      (hTL.trans (normalizer_le_normalizer_centralizer L))).trans inf_normalizer_le_normalizer_inf
  let : (A.subgroupOf (T : Subgroup G)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hAT).mpr hn
  have hAn : A.subgroupOf (T : Subgroup G) ≠ ⊥ := by
    intro he
    apply hne
    change A = ⊥
    rw [←map_subgroupOf_eq_of_le hAT,he,Subgroup.map_bot]
  have hh := center_inf_ne_bot_of_normal T.isPGroup' (A.subgroupOf (T : Subgroup G)) hAn
  obtain ⟨x,hx,hx1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hh)
  have hx1 : x ≠ 1 := hx1
  intro he
  have hm : (x : G) ∈ Subgroup.omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G) := by
    refine ⟨(mem_omegaCenterIn_iff _ _).mpr ⟨x.property,?_,?_⟩,hx.2.2⟩
    · intro t ht
      exact congrArg Subtype.val (mem_center_iff.mp hx.1 ⟨t,ht⟩)
    · exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G) hx.2.1
  have hxG : (x : G) = 1 := by
    have hb : (x : G) ∈ (⊥ : Subgroup G) := he ▸ hm
    exact hb
  exact hx1 (Subtype.ext hxG)

/-- Failure of the marked ambient Sylow assertion forces a nontrivial
L-fixed subgroup in the central omega of the original full Sylow T. -/
theorem doubleNatural_four_full_omega_fixed_ne_bot_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (classification : BinaryLinearThreeMSClassification KnownSimple.IsKnownSimple.{u}) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      Subgroup.omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G) ≠ ⊥ := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  have he := S.marked_centralizer_eq D.sylow_normalizes_component w hw hp hfix
  change B.pointSylow w = _ at he
  have hi : (B.pointSylow w).relIndex (T : Subgroup G) = 2 := by
    rw [he]
    exact S.naturalSylowNormalizer_relIndex D.sylow_normalizes_component
  let := normal_of_index_eq_two hi
  exact ambient_omega_fixed_ne_bot T (B.pointSylow w) L inf_le_left
    ((normal_subgroupOf_iff_le_normalizer (show B.pointSylow w ≤ (T : Subgroup G) from inf_le_left)).mp inferInstance)
    D.sylow_normalizes_component
    (D.doubleNatural_four_pure_omega_fixed_ne_bot_of_many h hmany B classification S w hw hp hfix hf)


/-- The actual L-fixed omega subgroup has its full ambient normalizer in M,
as required by the later parabolic-normalizer argument in 12.1.4. -/
theorem doubleNatural_four_pure_omega_fixed_normalizer_le_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (classification : BinaryLinearThreeMSClassification KnownSimple.IsKnownSimple.{u}) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      normalizer (Subgroup.omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) : Set G) ≤
        normalizer (L : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  let R := B.pointSylow w
  let A := Subgroup.omegaCenterIn R ⊓ centralizer (L : Set G)
  have he := S.marked_centralizer_eq D.sylow_normalizes_component w hw hp hfix
  change R = _ at he
  have hi : R.relIndex (T : Subgroup G) = 2 := by
    rw [he]
    exact S.naturalSylowNormalizer_relIndex D.sylow_normalizes_component
  let := normal_of_index_eq_two hi
  have hnR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show R ≤ (T : Subgroup G) from inf_le_left)).mp inferInstance
  have hnA : (T : Subgroup G) ≤ normalizer (A : Set G) :=
    (le_inf (hnR.trans (normalizer_le_normalizer_omegaCenterIn R))
      (D.sylow_normalizes_component.trans (normalizer_le_normalizer_centralizer L))).trans
        inf_normalizer_le_normalizer_inf
  have hLA : L ≤ normalizer (A : Set G) :=
    (le_centralizer_iff.mp (show A ≤ centralizer (L : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  exact D.normal_subgroup_normalizer_le h.toHypothesis1221
    (show A ≤ L ⊔ (T : Subgroup G) from
      inf_le_left.trans ((map_subtype_le _).trans (inf_le_left.trans le_sup_right)))
    (D.doubleNatural_four_pure_omega_fixed_ne_bot_of_many h hmany B classification S w hw hp hfix hf)
    (sup_le hLA hnA)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
