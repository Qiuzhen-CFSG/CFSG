module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Kernel
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Embedding
public import Theory.GroupTheory.SylowSubgroupNormalizerImage
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The faithful section quotient in the pure-point Sylow argument

Keep the literal quotient H/C_H(Y/O₂(Y)). The proved kernel containment
lets the Sylow Frattini argument identify the image of N_H(T₁) with the
normalizer of the image of T₁. The kernel may have odd-order elements.

For the actual component orbit Y=⟨K^T⟩, the image of X is not normal:
normality would put the perfect image of Y inside the solvable image of X.
That perfect image is nontrivial, since otherwise [Y,Y]≤O₂(Y) would make
the nontrivial perfect group Y a two-group. This supplies the contradiction
target for the subsequent parabolic-normalizer argument on the same quotient.

The final application retains every original embedding row, including Held,
and the exact L-fixed omega-subgroup premise. The existing qt-rank-two-ms93
producer and qt-d-double-natural-pure-fusion retain that premise's discharge.
Maximality, component exclusions and the parabolic identification remain with
qt-d-double-natural-pure-fusion; qt-d-double-natural-centralizers supplies the
earlier chosen-module inputs. This does not assert the ambient Sylow theorem.
Source: Aschbacher--Smith 12.1.4, printed pp.790--791.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
open ChapterA.Section04
variable {G : Type*} [Group G]

/-- The source kernel C_H(Y/O₂(Y)), regarded inside H. -/
@[expose] def sectionKernel (H Y : Subgroup G) (_hn : H ≤ normalizer (Y : Set G)) : Subgroup H :=
  (twoSectionCentralizer Y H).subgroupOf H

/-- Only relative normality of Y in H is used. -/
instance sectionKernel_normal (H Y : Subgroup G) (hn : H ≤ normalizer (Y : Set G)) :
    (sectionKernel H Y hn).Normal :=
  normal_subgroupOf_of_le_normalizer (twoSectionCentralizer_normalized Y H hn)

/-- The literal source projection H → H/C_H(Y/O₂(Y)). -/
@[expose] def sectionProjection (H Y : Subgroup G) (hn : H ≤ normalizer (Y : Set G)) :
    H →* (H ⧸ sectionKernel H Y hn) :=
  QuotientGroup.mk' (sectionKernel H Y hn)

theorem sectionProjection_surjective (H Y : Subgroup G) (hn : H ≤ normalizer (Y : Set G)) :
    Function.Surjective (sectionProjection H Y hn) := by
  exact QuotientGroup.mk'_surjective _

theorem sectionProjection_ker (H Y : Subgroup G) (hn : H ≤ normalizer (Y : Set G)) :
    (sectionProjection H Y hn).ker = sectionKernel H Y hn := by
  exact QuotientGroup.ker_mk' _

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource ChapterA.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Frattini lifts the full normalizer on the original point-subgroup image. -/
theorem doubleNatural_four_pure_quotient_normalizer_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      ∀ H Y : Subgroup G, (T : Subgroup G) ≤ H →
        PureFourXi.residual T L ≤ Y → ∀ hn : H ≤ normalizer (Y : Set G),
        let q := PureFourXi.sectionProjection H Y hn
        (normalizer ((B.pointSylow w).subgroupOf H : Set H)).map q =
          normalizer (((B.pointSylow w).subgroupOf H).map q : Set (H ⧸ PureFourXi.sectionKernel H Y hn)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf H Y hTH hXY hn
  let q := PureFourXi.sectionProjection H Y hn
  apply (T.subtype hTH).normalizer_map_of_contains_kernel_intersection
    ((B.pointSylow w).subgroupOf H) (comap_mono inf_le_left) q
    (PureFourXi.sectionProjection_surjective H Y hn)
  intro t ht
  have htk : t ∈ PureFourXi.sectionKernel H Y hn := by
    rw [←PureFourXi.sectionProjection_ker H Y hn]
    exact ht.2
  exact D.doubleNatural_four_pure_sectionCentralizer_le_of_many h hmany B S w hw hp hfix hf
    Y hXY ⟨ht.1,htk.2⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

/-- A solvable seed cannot have normal image in the faithful section action
of its nontrivial perfect normal closure. -/
private theorem section_image_not_normal (H X Y : Subgroup G)
    (hn : H ≤ normalizer (Y : Set G)) (hXH : X ≤ H) (hYH : Y ≤ H)
    (he : conjugateSpanBy X H = Y) [Group.IsSolvable X] [Group.IsPerfect Y]
    (hne : Y ≠ ⊥) :
    ¬ ((X.subgroupOf H).map (sectionProjection H Y hn)).Normal := by
  let q := sectionProjection H Y hn
  let : Group.IsPerfect (Y.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hYH).symm.toMonoidHom)
      (subgroupOfEquivOfLe hYH).symm.surjective
  let : Group.IsSolvable (X.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hXH).toMonoidHom)
      (subgroupOfEquivOfLe hXH).injective
  let : Group.IsSolvable ((X.subgroupOf H).map q) :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective (X.subgroupOf H))
  have hker : ¬ Y.subgroupOf H ≤ q.ker := by
    intro hy
    have hc : ⁅Y,Y⁆ ≤ Y.pCoreIn 2 := by
      apply commutator_le.mpr
      intro y hyY z hzY
      have hk : (⟨y,hYH hyY⟩ : H) ∈ sectionKernel H Y hn := by
        rw [←sectionProjection_ker H Y hn]
        exact hy hyY
      exact hk.2.2 z hzY
    rw [Y.commutator_eq_self] at hc
    have hp : IsPGroup 2 Y := (isPGroup_pCoreIn 2 Y).to_le hc
    let := hp.isNilpotent
    let := (Subgroup.nontrivial_iff_ne_bot Y).mpr hne
    exact Group.IsPerfect.not_isSolvable Y inferInstance
  intro hnormal
  let := hnormal
  have hs : conjugateSpanBy (X.subgroupOf H) ⊤ = Y.subgroupOf H := by
    apply Subgroup.map_injective (f := H.subtype) H.subtype_injective
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hXH,
      ←MonoidHom.range_eq_map,range_subtype,map_subgroupOf_eq_of_le hYH,he]
  have hmap : (Y.subgroupOf H).map q ≤ (X.subgroupOf H).map q := by
    rw [←hs,map_conjugateSpanBy]
    exact conjugateSpanBy_le le_rfl le_normalizer_of_normal
  exact (map_not_le_of_isPerfect_of_isSolvable (Y.subgroupOf H) q hker
    ((X.subgroupOf H).map q)) hmap
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The constructed faithful component has the exact quotient normalizer equality
and a nonnormal residual image, retaining all corrected embedding alternatives. -/
theorem doubleNatural_four_pure_component_quotient_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥ →
      let X := PureFourXi.residual T L
      ∃ P : Sylow 2 G, B.pointSylow w < (P : Subgroup G) ∧
        (P : Subgroup G) ≤ B.pointCentralizer w ∧
        (P : Subgroup G) ⊓ normalizer (L : Set G) = B.pointSylow w ∧
        let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
        H ∈ HOver G ((X ⊔ (T : Subgroup G) : Subgroup G) : Set G) ∧
        H ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
        ¬ H ≤ normalizer (L : Set G) ∧
        ∃ A : Sylow 3 X, ∃ K : Subgroup G,
          K ∈ cComponentsIn H ∧ K ∈ Chapter1.L G (T : Subgroup G) ∧
          K ∈ MainForward.faithfulLocalComponents T ∧
          IsQuasisimple (XiQuotient K) ∧
          ((componentOrbit K (T : Subgroup G)).subgroupOf H).Normal ∧
          conjugateSpanBy X H = componentOrbit K (T : Subgroup G) ∧
          X < componentOrbit K (T : Subgroup G) ∧
          componentOrbit V (T : Subgroup G) ⊓
            centralizer (componentOrbit K (T : Subgroup G) : Set G) = ⊥ ∧
          (Alternatives 3 (T : Subgroup G) ((A : Subgroup X).map X.subtype) K ∨
            HeldAlternative 3 (T : Subgroup G) ((A : Subgroup X).map X.subtype) K) ∧
          ∃ hn : H ≤ normalizer (componentOrbit K (T : Subgroup G) : Set G),
            let q := PureFourXi.sectionProjection H (componentOrbit K (T : Subgroup G)) hn
            (normalizer ((B.pointSylow w).subgroupOf H : Set H)).map q =
              normalizer (((B.pointSylow w).subgroupOf H).map q :
                Set (H ⧸ PureFourXi.sectionKernel H (componentOrbit K (T : Subgroup G)) hn)) ∧
            ¬ ((X.subgroupOf H).map q).Normal := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf hne
  obtain ⟨P,hlt,hPC,hPM,hH,hHN,hout,A,K,hK,hKL,hfaith,hqK,hnK,he,hstrict,hfixK,halt⟩ :=
    D.doubleNatural_four_pure_component_embedding_of_many_of_omega_fixed h hmany B S w hw hp hfix hf hne
  let X := PureFourXi.residual T L
  let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
  have hKH : componentOrbit K (T : Subgroup G) ≤ H := by
    rw [←he]
    exact conjugateSpanBy_le (le_sup_left.trans le_sup_right) H.le_normalizer
  have hn : H ≤ normalizer (componentOrbit K (T : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hnK
  refine ⟨P,hlt,hPC,hPM,hH,hHN,hout,A,K,hK,hKL,hfaith,hqK,hnK,he,hstrict,hfixK,halt,hn,?_⟩
  constructor
  · exact D.doubleNatural_four_pure_quotient_normalizer_of_many h hmany B S w hw hp hfix hf
      H (componentOrbit K (T : Subgroup G)) (le_sup_right.trans le_sup_right) hstrict.le hn
  · let := Chapter1.mem_L_isPerfect hKL
    let : Group.IsPerfect (componentOrbit K (T : Subgroup G)) :=
      isPerfect_iSup_conjugates K (T : Subgroup G)
    let : Group.IsSolvable X :=
      (D.doubleNatural_four_pure_xi_of_many h hmany B S w hw hp hfix hf).1.isSolvable
    exact PureFourXi.section_image_not_normal H X (componentOrbit K (T : Subgroup G))
      hn (le_sup_left.trans le_sup_right) hKH he
      (ne_bot_of_gt (lt_of_le_of_lt bot_le hstrict))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
