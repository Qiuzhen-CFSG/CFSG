module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Parabolic
public import Theory.SpecificGroups.SymmetricEight.FourBlockQuotient
public import Theory.GroupTheory.ElementaryThompsonQuotientNormalizer
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.PGroup.NormalSupplementKernel

/-!
# The actual Thompson-normalizer quotient in LT

The two orbits of the marked elementary sixteen identify its full normalizer
with the unordered four-block stabilizer. Its two-core quotient is the
literal binary-plane wreath group SL2(2) wr C2, hence S3 wr C2.

The original LT action projection is surjective and has a two-group kernel
inside T. Thompson heredity therefore lifts its image normalizer exactly.
Removing this kernel preserves the two-core quotient, giving the required
wreath model of N_LT(J(T)) on the original source subgroups.

The final chosen-module application discharges movement from the contrary
ambient Sylow branch. It uses no MS classification. The full R2(LQ) splitting,
construction and escape of the source Xi member, and subsequent component
exclusions remain with qt-d-double-natural-pure-fusion; the parent
qt-d-double-natural-centralizers retains final source assembly.
Source: Aschbacher--Smith, 12.1.4, printed p.790; B.2.7 and B.4.9(2iii),
pp.76,92,94. The underlying eight-point comparison uses the attributed
ATLAS exceptional-isomorphism port already present in the imported model.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace BinaryNaturalDual.FourActors.PermutationCatalogue
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction

private theorem same_block_of_normalizes (g : Equiv.Perm (Fin 8))
    (hg : g ∈ normalizer (permutationA0 : Set (Equiv.Perm (Fin 8))))
    (i j : Fin 8) (hij : i.val / 4 = j.val / 4) : (g i).val / 4 = (g j).val / 4 := by
  have hmem : i ∈ MulAction.orbit (permutationActor 0) j :=
    (mem_permutationActor_orbit 0 j i).mpr (by simpa [blockLabel] using hij)
  obtain ⟨a,ha⟩ := MulAction.mem_orbit_iff.mp hmem
  change a.val j = i at ha
  have hc : g * a.val * g⁻¹ ∈ permutationA0 := (hg a.val).mp a.property
  have he : g i ∈ MulAction.orbit (permutationActor 0) (g j) := by
    refine MulAction.mem_orbit_iff.mpr ⟨⟨g * a.val * g⁻¹,hc⟩,?_⟩
    change (g * a.val * g⁻¹) (g j) = g i
    simpa only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using congrArg g ha
  exact (mem_permutationActor_orbit 0 (g j) (g i)).mp he

/-- The full normalizer of the marked elementary sixteen is the actual
unordered four-block stabilizer in S8. -/
theorem normalizer_permutationA0 : normalizer (permutationA0 : Set (Equiv.Perm (Fin 8))) =
    fourStabilizer := by
  apply le_antisymm
  · intro g hg
    rw [mem_fourStabilizer]
    intro i j
    constructor
    · intro he
      simpa using same_block_of_normalizes g⁻¹ ((normalizer _).inv_mem hg) (g i) (g j) he
    · exact same_block_of_normalizes g hg i j
  · rw [permutationA0_eq_kleinGroup,←fourStabilizer_pCoreIn]
    exact fourStabilizer.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image fourStabilizer (pCore 2 fourStabilizer))
end BinaryNaturalDual.FourActors.PermutationCatalogue

namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
open SourceFourActors
variable {M E : Type*} [Group M] [AddCommGroup E] [Module (ZMod 2) E]
  (S : SourceSetup 4 M E) (P : Sylow 2 M)

/-- The full normalizer preserves the two four-point blocks, in the same
Sylow-compatible source marking. -/
theorem four_A0_normalizer :
    (normalizer (A0 S P : Set M)).map (permutation S P).toMonoidHom =
      Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.fourStabilizer := by
  rw [Subgroup.map_equiv_normalizer_eq]
  have ha : (A0 S P).map (permutation S P).toMonoidHom =
      BinaryNaturalDual.FourActors.permutationA0 := by
    change (A0 S P).map (BinaryNaturalDual.FourActors.permutationEquiv.toMonoidHom.comp
      (group S P).toMonoidHom) = _
    rw [←map_map,actor_map]
    exact BinaryNaturalDual.FourActors.PermutationCatalogue.actor_map 0
  rw [ha]
  exact BinaryNaturalDual.FourActors.PermutationCatalogue.normalizer_permutationA0

/-- The actual two-core quotient of the full normalizer is SL2(2) wreath C2. -/
noncomputable def four_A0_normalizer_quotient :
    (normalizer (A0 S P : Set M) ⧸ pCore 2 (normalizer (A0 S P : Set M))) ≃*
      WreathTwoResidual.Actor := by
  let e := ((permutation S P).subgroupMap (normalizer (A0 S P : Set M))).trans
    (MulEquiv.subgroupCongr (S.four_A0_normalizer P))
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    Theory.SpecificGroups.SymmetricEight.FourBlockQuotient.fourStabilizerQuotientEquivActor
end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)

/-- Restrict the original normalizer action projection to LT. -/
@[expose] noncomputable def joinActionProjection
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (L ⊔ (T : Subgroup G) : Subgroup G) →* B.ActionQuotient :=
  B.actionProjection.comp (inclusion (sup_le L.le_normalizer hTM))
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
open Stellmacher ChapterH.NaturalDual.SourceFourActors
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {B : DoubledBranch T L V 4}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

include S in
/-- The LT projection is onto the original action group and has two-group
kernel contained in the original Sylow. -/
theorem four_join_action (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Function.Surjective (B.joinActionProjection hTM) ∧
      IsPGroup 2 (B.joinActionProjection hTM).ker ∧
      (B.joinActionProjection hTM).ker ≤ (T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)) := by
  let J := L ⊔ (T : Subgroup G)
  let f := B.joinActionProjection hTM
  let Lj := L.subgroupOf J
  let Tj := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let P := (T.subtype hTM).mapSurjective B.actionProjection_surjective
  have hT : (Tj : Subgroup J).map f = (P : Subgroup B.ActionQuotient) := by
    ext a
    constructor <;> rintro ⟨t,ht,rfl⟩
    · exact ⟨⟨t,(sup_le L.le_normalizer hTM) t.property⟩,ht,rfl⟩
    · exact ⟨⟨t,(show (T : Subgroup G) ≤ J from le_sup_right) ht⟩,ht,rfl⟩
  have hL : Lj.map f = componentLayer B.ActionQuotient := by
    rw [←S.component_layer]
    ext a
    constructor
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,hl⟩,rfl⟩
    · rintro ⟨l,rfl⟩
      exact ⟨⟨l,(show L ≤ J from le_sup_left) l.property⟩,l.property,rfl⟩
  have hsurj : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply index_eq_one.mp
    have hd : f.range.index ∣ 2 := by
      have hh := index_dvd_of_le (show componentLayer B.ActionQuotient ≤ f.range from
        hL ▸ map_le_range f Lj)
      rwa [BinaryNaturalDual.ModelOrbits.SourceComparison.componentLayer_index
        S.setup.degree S.setup.projective] at hh
    have hn : ¬ 2 ∣ f.range.index := fun hh => P.not_dvd_index
      (hh.trans (index_dvd_of_le (show (P : Subgroup B.ActionQuotient) ≤ f.range from
        hT ▸ map_le_range f Tj)))
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_right (fun hh => hn (by rw [hh]))
  let : Lj.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hTM)
  have hgen : Lj ⊔ (Tj : Subgroup J) = ⊤ := by
    change L.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  let e : Lj ≃* L := subgroupOfEquivOfLe le_sup_left
  have hk : IsPGroup 2 (f.comp Lj.subtype).ker := by
    have he : f.comp Lj.subtype = B.componentToActionQuotient.comp e.toMonoidHom := rfl
    rw [he,← MonoidHom.comap_ker,B.componentToActionQuotient_ker]
    exact pCore_isPGroup.comap_of_injective e.toMonoidHom e.injective
  have hfk := f.kernel_isPGroup_of_normal_supplement Lj Tj Tj.isPGroup' hgen hk
  exact ⟨hsurj,hfk,hfk.le_sylow_of_normal Tj⟩

include S in
/-- Normalizer transport for the original Thompson subgroup, using the
proved two-group kernel instead of assuming quotient functoriality of J. -/
theorem four_thompson_normalizer_quotient
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hm : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (componentOrbit V (T : Subgroup G) : Set G)) :
    let N := (normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)).subgroupOf
      (L ⊔ (T : Subgroup G));
    Nonempty ((N ⧸ pCore 2 N) ≃* WreathTwoResidual.Actor) := by
  let H := L ⊔ (T : Subgroup G)
  let R := (T : Subgroup G).subgroupOf H
  let f := B.joinActionProjection hTM
  let P := (T.subtype hTM).mapSurjective B.actionProjection_surjective
  obtain ⟨hf,hk,hkR⟩ := S.four_join_action hTM
  have hJR : (elementaryAbelianMaxJ R).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)]
  have hJH : elementaryAbelianMaxJ (T : Subgroup G) ≤ H :=
    (show elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) from
      sSup_le fun _ hA => hA.1).trans le_sup_right
  have hJR' : elementaryAbelianMaxJ R =
      (elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hJR,map_subgroupOf_eq_of_le hJH]
  have himage : (elementaryAbelianMaxJ R).map f = A0 S.setup P := by
    rw [hJR']
    have he : ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf H).map f =
        ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf (normalizer (L : Set G))).map
          B.actionProjection := by
      ext a
      constructor <;> rintro ⟨x,hx,rfl⟩
      · exact ⟨⟨x,(sup_le L.le_normalizer hTM) x.property⟩,hx,rfl⟩
      · exact ⟨⟨x,hJH hx⟩,hx,rfl⟩
    rw [he]
    exact S.four_thompson_image hTM hWT hm
  let N := normalizer (elementaryAbelianMaxJ R : Set H)
  have hN : N.map f = normalizer (A0 S.setup P : Set B.ActionQuotient) := by
    rw [normalizer_map_maxJ R f hf hkR,himage]
  let g := f.subgroupMap N
  have hg : Function.Surjective g := f.subgroupMap_surjective N
  have hkg : IsPGroup 2 g.ker := by
    apply hk.of_injective
      ((N.subtype.comp g.ker.subtype).codRestrict f.ker (fun x =>
        congrArg (fun a : N.map f => (a : B.ActionQuotient)) x.property))
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun a : f.ker => (a : H)) he))
  let eN := MulEquiv.subgroupCongr hN
  let e := (g.pCoreQuotientEquiv hg hkg).trans
    ((QuotientGroup.congr _ _ eN (pCore_map_iso 2 eN)).trans
      (S.setup.four_A0_normalizer_quotient P))
  have hn : N = (normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)).subgroupOf H := by
    change normalizer (elementaryAbelianMaxJ R : Set H) = _
    rw [hJR',subgroupOf_normalizer_eq hJH]
  exact ⟨(QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hn.symm)
    (pCore_map_iso 2 (MulEquiv.subgroupCongr hn.symm))).trans e⟩
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Stellmacher ChapterH.NaturalDual.SourceFourActors
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual normalizer in LT has the required binary-plane wreath quotient.
The original contrary ambient Sylow hypothesis discharges Thompson movement;
no normalizer model or quotient identification is an extra premise. -/
theorem doubleNatural_four_pure_thompson_normalizer_model_of_many
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
      let N := (normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)).subgroupOf
        (L ⊔ (T : Subgroup G));
      Nonempty ((N ⧸ pCore 2 N) ≃* WreathTwoResidual.Actor) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  exact S.four_thompson_normalizer_quotient D.sylow_normalizes_component
    (D.doubledOrbit_E322 h).le_sylow
    (D.doubleNatural_four_pure_thompson_moves_of_many h hmany B S w hw hp hfix hf).2
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
