module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianRadicalDisplacement
public import Theory.SpecificGroups.Janko4.Model.IrreducibleNineSectionRadical
public import Theory.SpecificGroups.Janko4.Model.NineSpaceThompson
public import Theory.GroupTheory.RadicalNormalizerIndexFour
import all CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.SmallRadicalNormalizer
import all CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.SmallRadical
import all CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.NativeNonFF

/-!
# Excluding the ordinary J₄ cover on the actual Hermitian nine-space

The native residual's full two-core quotient is PSL₃(4). Its perfect
nine-divisible section and irreducible central displacement force the
native radical U to be elementary. The native two-rank bound gives
|U| ≤ 2048 and index at most four over the original module image E.
Characteristic-two normalizer control identifies U as the full two-core
and its own centralizer. Three-freeness of C(E) removes the possible cubic
action on U/E, giving the full pointwise centralizer inside that normalizer.

The original non-FF hypothesis transports through the literal component
inclusion and central quotient, both bijective on the original module.
It makes U the Thompson subgroup of a full native Sylow. The native prime-23
normalizer then contradicts |E| = 512. This excludes the full ordinary
cover without placing the previously selected even-centralizer seed in C(A).
All covering centers, original residuals and original actions are retained.
The internal Mathieu imports reuse generic transport implementations while
preserving their existing public chapter boundaries.
Source: Aschbacher--Smith 4.2.13, 4.4.3 and Remark 4.4.2, printed
pp.611--612,619,623, as used in 8.2.7, p.718, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The original native radical is elementary, of order at most 2048,
with index at most four over the original nine-space. -/
theorem sourceOrbit_hermitian_ordinary_radical_elementary_of_card
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥) (hcardV : Nat.card V = 512)
    {k : Type*} [Field k] [Finite k]
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,k))
    (hfield : Nat.card k = 4)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let U := ((J.pCoreIn 2).comap j).map q
    let E := (V.comap j).map q
    IsElementaryAbelian 2 U ∧ Nat.card U ≤ 2048 ∧ E.relIndex U ≤ 4 := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let Fk := F.comap j
  let B := Fk.map q
  let U := ((J.pCoreIn 2).comap j).map q
  let E := (V.comap j).map q
  have hc := hw.2.2.2.2.2.2.1
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  let eb : Fk ≃* F := (subgroupOfEquivOfLe (hc.ordinary_component_contains_original K hK)).trans
    (subgroupOfEquivOfLe hFH)
  let : Group.IsPerfect F := Group.IsPerfect.map _
  let : Group.IsPerfect Fk := Group.IsPerfect.ofSurjective (f := eb.symm.toMonoidHom) eb.symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective Fk)
  have hn := D.sourceOrbit_pushingUp_native_radical hfix hw K hK e
  dsimp only at hn
  let : IsElementaryAbelian 2 E := hn.2.2.2.2.2.2.1
  have hE : Nat.card E = 512 := hn.2.2.2.2.2.2.2.1.trans hcardV
  obtain ⟨em⟩ := (D.sourceOrbit_hermitian_ordinary_center_kernel_of_card
    h hfix hcardV eQ hfield hw K hK e).2.2.2
  let b : B →* PSL(3,k) := em.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))
  have hb : Function.Surjective b := em.surjective.comp (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup PSL(3,k) := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect PSL(3,k) := Group.IsPerfect.ofSurjective hb
  have h9 : 9 ∣ Nat.card PSL(3,k) := by
    rw [Matrix.PSL3.LinearThree.card_projective,hfield]
    decide
  let hElem := Janko4.InvolutionCentralizers.nine_section_radical_elementary
    (Group.IsPerfect.not_isSolvable PSL(3,k)) h9 B U E b hb
    hn.2.1.isPGroup hn.2.2.2.1 hn.2.2.2.2.2.1 (by rw [hE]; decide)
    hn.2.2.2.2.1 (D.sourceOrbit_pushingUp_native_irreducible hfix hw K hK e)
    (D.sourceOrbit_hermitian_ordinary_radical_image_of_card
      h hfix hcardV eQ hfield hw K hK e).2.2.2.2.2.2.1
    (D.sourceOrbit_hermitian_ordinary_radical_displacement_of_card
      h hfix hcardV eQ hfield hw K hK e).le
  let := hElem
  have hupper : Nat.card U ≤ 2048 :=
    (primeRank_le_iff_elementary_card_le Janko4.Model).mp
      Janko4.TwoRank.model_twoRank_le_eleven U hElem
  have hcount := (E.subgroupOf U).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hn.2.2.2.2.2.1).toEquiv] at hcount
  change Nat.card E * E.relIndex U = Nat.card U at hcount
  rw [hE] at hcount
  exact ⟨hElem,hupper,by change E.relIndex U ≤ 4; omega⟩

/-- The same native radical is the entire residual-normalizer two-core
and is self-centralizing in the full J4 model. -/
theorem sourceOrbit_hermitian_ordinary_elementary_normalizer_of_card
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥) (hcardV : Nat.card V = 512)
    {k : Type*} [Field k] [Finite k]
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,k))
    (hfield : Nat.card k = 4)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let U := ((J.pCoreIn 2).comap j).map q
    let B := (F.comap j).map q
    (normalizer (B : Set Janko4.Model)).pCoreIn 2 = U ∧
      normalizer (U : Set Janko4.Model) = normalizer (B : Set Janko4.Model) ∧
      centralizer (U : Set Janko4.Model) = U := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let U := ((J.pCoreIn 2).comap j).map q
  let B := (F.comap j).map q
  let C := ((H ⊓ normalizer (L : Set G)).comap j).map q
  have hn := D.sourceOrbit_pushingUp_native_radical hfix hw K hK e
  dsimp only at hn
  let : IsElementaryAbelian 2 U := (D.sourceOrbit_hermitian_ordinary_radical_elementary_of_card
    h hfix hcardV eQ hfield hw K hK e).1
  have hc := sourceOrbit_pushingUp_native_normalizer hw K hK e
  change normalizer (B : Set Janko4.Model) = C ∧ _ at hc
  apply Subgroup.abelian_radical_in_constrained U (normalizer (B : Set Janko4.Model)) hn.2.1
    (U.le_normalizer.trans hn.2.2.1) hn.2.2.1
  rw [hc.1]
  exact hc.2

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource ChapterD.UniqueFactor
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- Transport the original non-FF action through the entire central cover. -/
theorem sourceOrbit_hermitian_ordinary_native_nonFF_of_card
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hcardV : Nat.card V = 512)
    {k : Type*} [Field k] [Finite k]
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,k))
    (hfield : Nat.card k = 4)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let E := (V.comap j).map q
    let B := (F.comap j).map q
    letI : IsElementaryAbelian 2 E :=
      (D.sourceOrbit_hermitian_ordinary_radical_image_of_card
        h hfix hcardV eQ hfield hw K hK e).2.1
    ¬ IsFFModule (imageRepresentation (normalizer (B : Set Janko4.Model)) E
      (D.sourceOrbit_hermitian_ordinary_normalizer_core_of_card h hfix hcardV eQ hfield hw K hK e).2.2.2) := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let M := H ⊓ normalizer (L : Set G)
  let Ek := V.comap j
  let Ck := M.comap j
  have hj : Function.Injective j := H.subtype_injective.comp K.subtype_injective
  have hjr : j.range = K.map H.subtype := by rw [MonoidHom.range_comp,range_subtype]
  have hEV : Ek.map j = V := map_comap_eq_self
    ((D.sourceOrbit_pushingUp_module_disjoint_central_factor hfix hw K hK).1.trans
      inf_le_right |>.trans_eq hjr.symm)
  let d : Ek ≃* V := (Ek.equivMapOfInjective j hj).trans (MulEquiv.subgroupCongr hEV)
  let := D.elementary
  let : IsElementaryAbelian 2 Ek := IsElementaryAbelian.of_injective d.toMonoidHom d.injective
  have hc := hw.2.2.2.2.2.2.1
  have hMF : M ≤ normalizer (F : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hc.component_le).mp hw.2.2.2.2.2.2.2.2.1
  have hn : Ck ≤ normalizer (Ek : Set K) :=
    ((comap_mono hMF).trans (F.le_normalizer_comap j)).trans
      (D.sourceOrbit_hermitian_ordinary_cover_module_normalizer_of_card h hfix hcardV eQ hfield hw K hK e)
  have hnoV : ¬ IsFFModule (ChapterE.automizerRepresentation V) := by
    intro hh
    exact D.sourceOrbit_automizer_nonFF h hnon ((automizer_ff_congr hV).mp hh)
  let : IsElementaryAbelian 2 (Ek.map j) := IsElementaryAbelian.map j
  let : IsElementaryAbelian 2 (Ek.map q) := IsElementaryAbelian.map q
  have n : Ck.map j ≤ normalizer (V : Set G) := by
    rw [←hEV]
    exact (map_mono hn).trans (Ek.le_normalizer_map j)
  have hnoj' : ¬ IsFFModule (imageRepresentation (Ck.map j) V n) := by
    intro hh
    apply hnoV
    let i : ChapterD.internalActionImage (Ck.map j) V n →* ChapterE.Automizer V :=
      inclusion (by
        rintro _ ⟨x,rfl⟩
        exact ⟨inclusion n x,rfl⟩)
    exact hh.map_equivariant _ _ i (inclusion_injective _)
      (LinearEquiv.refl _ _) (fun _ _ => rfl)
  have hnoj : ¬ IsFFModule (imageRepresentation (Ck.map j) (Ek.map j)
      ((map_mono hn).trans (Ek.le_normalizer_map j))) := fun hh =>
    hnoj' ((image_ff_congr rfl hEV _ n).mp hh)
  have hnj : ¬ IsFFModule (imageRepresentation Ck Ek hn) := by
    intro hh
    exact hnoj ((image_ff_map_iff j Ck Ek hn (by
      intro x y he
      apply Subtype.ext
      apply hj
      exact congrArg (fun z : Ek.map j => (z : G)) he)).mp hh)
  have hnat := D.sourceOrbit_pushingUp_native_radical hfix hw K hK e
  dsimp only at hnat
  have hiq : Function.Injective (q.subgroupMap Ek) :=
    ((q.subgroupMap_surjective Ek).bijective_of_nat_card_le
      ((Nat.card_congr d.toEquiv).le.trans hnat.2.2.2.2.2.2.2.1.symm.le)).1
  have hnoq : ¬ IsFFModule (imageRepresentation (Ck.map q) (Ek.map q)
      ((map_mono hn).trans (Ek.le_normalizer_map q))) := by
    intro hh
    exact hnj ((image_ff_map_iff q Ck Ek hn hiq).mpr hh)
  have hN := sourceOrbit_pushingUp_native_normalizer hw K hK e
  have heC : Ck.map q = normalizer ((F.comap j).map q : Set Janko4.Model) := hN.1.symm
  dsimp only
  intro hh
  exact hnoq ((image_ff_congr heC rfl _ _).mpr hh)


/-- Three-free native pointwise centralizers remove the cubic exception
at index four over the original nine-space. -/
theorem sourceOrbit_hermitian_ordinary_module_centralizer_of_card
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥) (hcardV : Nat.card V = 512)
    {k : Type*} [Field k] [Finite k]
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,k))
    (hfield : Nat.card k = 4)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let U := ((J.pCoreIn 2).comap j).map q
    let E := (V.comap j).map q
    let B := (F.comap j).map q
    normalizer (B : Set Janko4.Model) ⊓ centralizer (E : Set Janko4.Model) = U := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let U := ((J.pCoreIn 2).comap j).map q
  let E := (V.comap j).map q
  let B := (F.comap j).map q
  have hn := D.sourceOrbit_pushingUp_native_radical hfix hw K hK e
  dsimp only at hn
  have hs := D.sourceOrbit_hermitian_ordinary_radical_elementary_of_card
    h hfix hcardV eQ hfield hw K hK e
  let : IsElementaryAbelian 2 U := hs.1
  have hnorm := D.sourceOrbit_hermitian_ordinary_elementary_normalizer_of_card
    h hfix hcardV eQ hfield hw K hK e
  have hNE := (D.sourceOrbit_hermitian_ordinary_normalizer_core_of_card
    h hfix hcardV eQ hfield hw K hK e).2.2.2
  have h3 := (D.sourceOrbit_hermitian_ordinary_center_kernel_of_card
    h hfix hcardV eQ hfield hw K hK e).1
  refine le_antisymm (centralizer_le_core_of_fixed_index_le_four_three_free
    _ U E hnorm.1 hnorm.2.2.le hn.2.2.2.2.2.1 hs.2.2 hNE h3) ?_
  exact le_inf (U.le_normalizer.trans hn.2.2.1)
    (D.sourceOrbit_hermitian_ordinary_radical_image_of_card
      h hfix hcardV eQ hfield hw K hK e).2.2.2.2.2.2.1

/-- The actual nine-space and non-FF action exclude the full ordinary J4
cover, without centralizing an independently selected even-centralizer seed. -/
theorem sourceOrbit_hermitian_ordinary_false_of_card
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥) (hcardV : Nat.card V = 512)
    {k : Type*} [Field k] [Finite k]
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,k))
    (hfield : Nat.card k = 4)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) : False := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let U := ((J.pCoreIn 2).comap j).map q
  let E := (V.comap j).map q
  let B := (F.comap j).map q
  have hn := D.sourceOrbit_pushingUp_native_radical hfix hw K hK e
  dsimp only at hn
  have hs := D.sourceOrbit_hermitian_ordinary_radical_elementary_of_card
    h hfix hcardV eQ hfield hw K hK e
  let : IsElementaryAbelian 2 U := hs.1
  let : IsElementaryAbelian 2 E := hn.2.2.2.2.2.2.1
  have hnorm := D.sourceOrbit_hermitian_ordinary_elementary_normalizer_of_card
    h hfix hcardV eQ hfield hw K hK e
  have hcent := D.sourceOrbit_hermitian_ordinary_module_centralizer_of_card
    h hfix hcardV eQ hfield hw K hK e
  have hNE := (D.sourceOrbit_hermitian_ordinary_normalizer_core_of_card
    h hfix hcardV eQ hfield hw K hK e).2.2.2
  obtain ⟨P,hPC,hth⟩ := native_sylow_of_elementary_core_nonFF U E B
    hn.2.2.2.2.2.1 hnorm.1 hnorm.2.1 hcent hNE
    (D.sourceOrbit_hermitian_ordinary_native_nonFF_of_card
      h hV hfix hcardV eQ hfield hnon hw K hK e)
  apply Janko4.not_nineSpace_of_thompson_radical P U E hth hs.2.1 hn.2.1.isPGroup
    (hn.2.2.2.2.2.2.2.1.trans hcardV)
  · exact hnorm.2.1.le.trans hNE
  · exact (congrArg (fun X : Subgroup Janko4.Model => X ⊓ centralizer (E : Set Janko4.Model))
      hnorm.2.1).trans hcent

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
