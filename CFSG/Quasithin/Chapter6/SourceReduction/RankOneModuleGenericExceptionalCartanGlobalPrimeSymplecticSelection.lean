module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeDiagramSource
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.TwoCoreLocalPair
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.StarCoordinates
public import Theory.GroupTheory.CComponent.SolvableQuotient
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeConstruction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightGeometry
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.CComponents

/-!
# Canonical symplectic factors in the original Cartan argument

In the symplectic diagram source row, the intrinsic covering theorem
and the original center identity prove core_H(M) = O₂(H). We take the
solvable residuals of the literal preimages of the two model determinant
kernels. Their quotients are PSL₂ over the same marked field; the
perfect-lift argument proves the required relative C-component property.

The overlap two-core acts trivially on the Borel torus quotient and hence
preserves both local factors. The full Borel also normalizes them, so the
same holds for the original S and right Hall Cartan B. Each factor lies
outside M; the H-star property then gives generation with T. The source
Sylow intersection supplies a full Sylow in each selected factor.

The normalizer-index and Borel-product clauses of LocalData, the linear
diagram rows, and all remaining zero-core and changed-Sylow exclusions
stay with qt-d-1222-rankone-cartan-local-to-global. These results do not
assert the full conditional Cartan normalization theorem.
Source: Aschbacher–Smith E.2.2,5.1.11(3),5.2.1–2,
printed pp.215–216,635,646–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X] [Finite X]

private theorem symplectic_diagram_preimages_normalized
    (S : Sylow 2 X) {M C : Subgroup X} {f : ℕ}
    (hC : C.IsCComponent) (hc : SingleClauses M C S) (hf : 1 < f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage M C ≃* Sp4Derived F)
    (he : (componentOverlap M C).map e.toMonoidHom = sp4DerivedBorel F) :
    let q := QuotientGroup.mk' (sourceKernel M)
    let eF := e.trans (derivedEquivFull_of_card_gt_two (F := F) (by
      have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ f by omega)
      omega))
    let j := (sourceImage M C).subtype.comp eF.symm.toMonoidHom
    let P := (pointLocal.map j).comap q
    let Q := (planeLocal.map j).comap q
    M.pCoreIn 2 ≤ normalizer (P : Set X) ⊓ normalizer (Q : Set X) := by
  dsimp only
  let q := QuotientGroup.mk' (sourceKernel M)
  let N := sourceImage M C
  have hlarge : 2 < Nat.card F := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ f by omega)
    omega
  let ef := derivedEquivFull_of_card_gt_two (F := F) hlarge
  let eF := e.trans ef
  let j := N.subtype.comp eF.symm.toMonoidHom
  let : C.Normal := DiagramHall.single_component_normal S hC hc
  let : N.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hctop : commutator (Sp F) = ⊤ := by
    let := perfect_of_card_gt_two (F := F) hlarge
    exact Group.IsPerfect.commutator_eq_top
  have hefc : ef.toMonoidHom = (commutator (Sp F)).subtype := by
    apply MonoidHom.ext
    intro x
    exact derivedEquivFull_of_card_gt_two_apply _ x
  have hbf : (sp4DerivedBorel F).map ef.toMonoidHom = borel (F := F) := by
    rw [hefc]
    change ((borel (F := F)).subgroupOf (commutator (Sp F))).map
      (commutator (Sp F)).subtype = _
    simp only [subgroupOf_map_subtype,hctop,inf_top_eq]
  have hcoord : ((M.map q).subgroupOf N).map eF.toMonoidHom = borel (F := F) := by
    change ((sourceImage M M).subgroupOf (sourceImage M C)).map eF.toMonoidHom = _
    rw [← source_overlap_coordinate M C]
    change (componentOverlap M C).map (ef.toMonoidHom.comp e.toMonoidHom) = _
    rw [← map_map,he,hbf]
  have hM : (M.map q).comap j = borel (F := F) := by
    change (((M.map q).subgroupOf N).comap eF.symm.toMonoidHom) = _
    exact (comap_equiv_eq_map_symm eF.symm _).trans hcoord
  have hn := DiagramAutomorphisms.twoCore_normalizes_local_pair hF hf N (M.map q) eF.symm hM
  have hmap : (M.pCoreIn 2).map q ≤ (M.map q).pCoreIn 2 := by
    have hh : (pCore 2 M).map (q.subgroupMap M) ≤ pCore 2 (M.map q) :=
      le_sSup ⟨Normal.map inferInstance _ (q.subgroupMap_surjective M),pCore_isPGroup.map _⟩
    have hh' := map_mono (f := (M.map q).subtype) hh
    have heq : (M.map q).subtype.comp (q.subgroupMap M) = q.comp M.subtype := by
      apply MonoidHom.ext
      intro x
      rfl
    simpa only [pCoreIn,map_map,heq] using hh'
  have hp := (map_le_iff_le_comap.mp (hmap.trans (hn.trans inf_le_left))).trans
    (le_normalizer_comap q)
  have hq := (map_le_iff_le_comap.mp (hmap.trans (hn.trans inf_le_right))).trans
    (le_normalizer_comap q)
  exact le_inf hp hq

private theorem perfect_twoPerfect (R : Type*) [Group R] [Finite R] [Group.IsPerfect R] :
    IsPPerfect 2 R := by
  intro J hJ hp
  let := hJ
  have hs : Subsingleton (R ⧸ J) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (R ⧸ J) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

private theorem perfect_preimage_spec
    {Y : Type*} [Group Y] [Finite Y]
    (q : X →* Y) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (A : Subgroup Y) [Group.IsPerfect A] [IsQuasisimple (A ⧸ pCore 2 A)] :
    let P := A.comap q
    let R := (solvableResidual P).map P.subtype
    R.map q = A ∧ R ≤ pResidual 2 X ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* (A ⧸ pCore 2 A)) ∧
      (R.subgroupOf (normalizer (R : Set X))).IsCComponent := by
  let P := A.comap q
  let R := (solvableResidual P).map P.subtype
  have him : R.map q = A := by
    simpa only [solvableResidual_eq_top,← MonoidHom.range_eq_map,range_subtype]
      using map_solvableResidual_comap q hq A
  let := (inferInstance : Group.IsPerfect (solvableResidual P))
  let : Group.IsPerfect R := Group.IsPerfect.map P.subtype
  have hp : IsPPerfect 2 R := perfect_twoPerfect R
  let r := q.subgroupMap R
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let ea := MulEquiv.subgroupCongr him
  let eqr := (r.quotientPCoreEquivOfSurjective (q.subgroupMap_surjective R) hr).trans
    (QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea))
  let : IsQuasisimple (R ⧸ pCore 2 R) := IsQuasisimple.of_mulEquiv eqr.symm
  let eN := subgroupOfEquivOfLe R.le_normalizer
  let eqN := QuotientGroup.congr _ _ eN (pCore_map_iso 2 eN)
  let : IsQuasisimple ((R.subgroupOf (normalizer (R : Set X))) ⧸
      pCore 2 (R.subgroupOf (normalizer (R : Set X)))) :=
    IsQuasisimple.of_mulEquiv eqN.symm
  have hn : (R.subgroupOf (normalizer (R : Set X))).Normal :=
    normal_subgroupOf_of_le_normalizer le_rfl
  exact ⟨him,le_pResidual_of_isPPerfect R hp,⟨eqr⟩,
    isCComponent_of_isPPerfect_of_quasisimple_core_quotient hn.isSubnormal
      (hp.of_surjective eN.symm.toMonoidHom eN.symm.surjective)⟩

/-- The symplectic source has no surviving central scalar kernel. -/
theorem symplectic_sourceKernel_eq_twoCore
    (S : Sylow 2 X) {M C : Subgroup X} {f : ℕ}
    (hSM : (S : Subgroup X) ≤ M) (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses M C S) (hf : 1 < f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage M C ≃* Sp4Derived F) : sourceKernel M = pCore 2 X := by
  have hO : pCore 2 X ≤ sourceKernel M := normal_le_normalCore.mpr
    ((pCore_isPGroup.le_sylow_of_normal S).trans hSM)
  obtain ⟨E,_,_,hE,⟨eR⟩⟩ := symplectic_diagram_component_quotient hC hqs hO hf hF e
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hE)
  let ea : actorImage C ≃* Sp E := (cComponentTwoCoreQuotientEquiv hC).symm.trans
    (eR.trans EvenProjective.equiv.symm)
  have hz : center (actorImage C) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr ea ⟨x,hx⟩).property
    change ea x ∈ center (Sp E) at hh
    rw [EvenProjective.center_eq_bot,mem_bot] at hh
    exact ea.map_eq_one_iff.mp hh
  apply le_antisymm _ hO
  have he := hc.kernel_center
  rw [hz,Subgroup.map_bot] at he
  simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he


/-- The two determinant kernels in the common symplectic flag. -/
@[expose] def symplecticModelLocal (F : Type) [Field F] (i : Bool) : Subgroup (Sp F) :=
  if i then pointLocal else planeLocal

/-- The canonical perfect lift of a model local through the actual source quotient. -/
@[expose] def symplecticSourceFactor
    {F : Type} [Field F] (M C : Subgroup X)
    (e : sourceImage M C ≃* Sp F) (i : Bool) : Subgroup X :=
  let j := (sourceImage M C).subtype.comp e.symm.toMonoidHom
  let P := ((symplecticModelLocal F i).map j).comap (QuotientGroup.mk' (sourceKernel M))
  (solvableResidual P).map P.subtype

private theorem symplectic_source_factor_spec
    {M C : Subgroup X} {f : ℕ} (hf : 1 < f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage M C ≃* Sp F)
    (he : (componentOverlap M C).map e.toMonoidHom = borel (F := F))
    (hk : sourceKernel M = pCore 2 X) (i : Bool) :
    let R := symplecticSourceFactor M C e i
    R ≤ pResidual 2 X ∧ ¬ R ≤ M ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) ∧
      (R.subgroupOf (normalizer (R : Set X))).IsCComponent := by
  let q := QuotientGroup.mk' (sourceKernel M)
  let A := symplecticModelLocal F i
  let j := (sourceImage M C).subtype.comp e.symm.toMonoidHom
  let P := (A.map j).comap q
  let R := symplecticSourceFactor M C e i
  have hj : Function.Injective j := (sourceImage M C).subtype_injective.comp e.symm.injective
  have hlarge : 2 < Nat.card F := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ f by omega)
    omega
  let : Group.IsPerfect A := by
    cases i
    · exact planeLocal_perfect hF hf
    · exact pointLocal_perfect hF hf
  let : IsQuasisimple (A ⧸ pCore 2 A) := by
    cases i
    · exact (planeNaturalExtension hF hf).quotient_quasisimple hlarge
    · exact (pointNaturalExtension hF hf).quotient_quasisimple hlarge
  let ea := A.equivMapOfInjective j hj
  let eqA := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let : Group.IsPerfect (A.map j) := Group.IsPerfect.map j
  let : IsQuasisimple ((A.map j) ⧸ pCore 2 (A.map j)) := IsQuasisimple.of_mulEquiv eqA
  have hqk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk',hk]; exact pCore_isPGroup
  obtain ⟨him,hle,⟨er⟩,hcomp⟩ := perfect_preimage_spec q (QuotientGroup.mk'_surjective _) hqk (A.map j)
  let eSL : (A ⧸ pCore 2 A) ≃* Matrix.SpecialLinearGroup (Fin 2) F := by
    cases i
    · exact planeLocalCoreQuotientEquiv hF hf
    · exact pointLocalCoreQuotientEquiv hF hf
  refine ⟨hle,?_,⟨F,inferInstance,inferInstance,hF,
    ⟨er.trans (eqA.symm.trans (eSL.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F))))⟩⟩,hcomp⟩
  intro hRM
  have hcoord : (M.map q).comap j = borel (F := F) := by
    have hh := he
    rw [source_overlap_coordinate] at hh
    exact (comap_equiv_eq_map_symm e.symm _).trans hh
  have hAB : A ≤ borel (F := F) := by
    rw [←hcoord]
    apply map_le_iff_le_comap.mp
    rw [←him]
    exact map_mono hRM
  let : Group.IsSolvable (borel (F := F)) := isSolvable_borel hF
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective (inclusion_injective hAB)
  let r := eSL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  let : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Group.isSolvable_of_surjective (f := r) (eSL.surjective.comp (QuotientGroup.mk'_surjective _))
  let := NaturalExtension.model_perfect hlarge
  let := NaturalExtension.model_simple hlarge
  exact Group.IsPerfect.not_isSolvable (Matrix.SpecialLinearGroup (Fin 2) F) inferInstance

/-- Both canonical diagram factors have their genuine rank-one quotient and
are normalized by the original overlap two-core, including at field four. -/
theorem symplectic_diagram_factors
    (S : Sylow 2 X) {M C : Subgroup X} {f : ℕ}
    (hSM : (S : Subgroup X) ≤ M) (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses M C S) (hf : 1 < f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage M C ≃* Sp4Derived F)
    (he : (componentOverlap M C).map e.toMonoidHom = sp4DerivedBorel F) :
    ∃ eF : sourceImage M C ≃* Sp F,
      (componentOverlap M C).map eF.toMonoidHom = borel (F := F) ∧
      ∀ i : Bool, let R := symplecticSourceFactor M C eF i
        R ≤ pResidual 2 X ∧ ¬ R ≤ M ∧
        ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) ∧
        (R.subgroupOf (normalizer (R : Set X))).IsCComponent ∧
        M.pCoreIn 2 ≤ normalizer (R : Set X) := by
  have hlarge : 2 < Nat.card F := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ f by omega)
    omega
  let ef := derivedEquivFull_of_card_gt_two (F := F) hlarge
  let eF := e.trans ef
  have hctop : commutator (Sp F) = ⊤ := by
    let := perfect_of_card_gt_two (F := F) hlarge
    exact Group.IsPerfect.commutator_eq_top
  have hefc : ef.toMonoidHom = (commutator (Sp F)).subtype := by
    apply MonoidHom.ext
    intro x
    exact derivedEquivFull_of_card_gt_two_apply _ x
  have hbf : (sp4DerivedBorel F).map ef.toMonoidHom = borel (F := F) := by
    rw [hefc]
    change ((borel (F := F)).subgroupOf (commutator (Sp F))).map
      (commutator (Sp F)).subtype = _
    simp only [subgroupOf_map_subtype,hctop,inf_top_eq]
  have hmark : (componentOverlap M C).map eF.toMonoidHom = borel (F := F) := by
    change (componentOverlap M C).map (ef.toMonoidHom.comp e.toMonoidHom) = _
    rw [←map_map,he,hbf]
  have hker := symplectic_sourceKernel_eq_twoCore S hSM hC hqs hc hf hF e
  have hnorm := symplectic_diagram_preimages_normalized S hC hc hf hF e he
  refine ⟨eF,hmark,?_⟩
  intro i
  obtain ⟨hle,hnot,hquot,hcomp⟩ := symplectic_source_factor_spec hf hF eF hmark hker i
  refine ⟨hle,hnot,hquot,hcomp,?_⟩
  let j := (sourceImage M C).subtype.comp eF.symm.toMonoidHom
  let P := ((symplecticModelLocal F i).map j).comap (QuotientGroup.mk' (sourceKernel M))
  apply le_trans _ (normalizer_le_normalizer_characteristic_image P (solvableResidual P))
  cases i
  · exact hnorm.trans inf_le_right
  · exact hnorm.trans inf_le_left

omit [Finite X] in
/-- The full source Borel normalizes each canonical lifted local factor. -/
theorem symplecticSourceFactor.overlap_normalizes
    {M C : Subgroup X}
    {F : Type} [Field F]
    (e : sourceImage M C ≃* Sp F)
    (he : (componentOverlap M C).map e.toMonoidHom = borel (F := F)) (i : Bool) :
    M ⊓ C ≤ normalizer (symplecticSourceFactor M C e i : Set X) := by
  let q := QuotientGroup.mk' (sourceKernel M)
  let A := symplecticModelLocal F i
  let j := (sourceImage M C).subtype.comp e.symm.toMonoidHom
  let P := (A.map j).comap q
  have hAB : borel (F := F) ≤ normalizer (A : Set (Sp F)) := by
    cases i <;> dsimp [A,symplecticModelLocal]
    · exact inf_le_right.trans (le_normalizer_of_normal_subgroupOf planeLocal_le)
    · exact inf_le_left.trans (le_normalizer_of_normal_subgroupOf pointLocal_le)
  have hcoord : ((borel (F := F)).map j) = (M ⊓ C).map q := by
    rw [←he]
    change ((componentOverlap M C).map e.toMonoidHom).map
      ((sourceImage M C).subtype.comp e.symm.toMonoidHom) = _
    rw [map_map]
    have hj : ((sourceImage M C).subtype.comp e.symm.toMonoidHom).comp e.toMonoidHom =
        (sourceImage M C).subtype := by
      apply MonoidHom.ext
      intro x
      simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply]
    rw [hj]
    change ((sourceImage M (M ⊓ C)).subgroupOf (sourceImage M C)).map
      (sourceImage M C).subtype = _
    exact map_subgroupOf_eq_of_le (map_mono (f := q) inf_le_right)
  have hpre : M ⊓ C ≤ (normalizer (A.map j : Set _)).comap q := by
    apply map_le_iff_le_comap.mp
    rw [←hcoord]
    exact (map_mono hAB).trans (le_normalizer_map j)
  exact (hpre.trans (le_normalizer_comap q)).trans
    (normalizer_le_normalizer_characteristic_image P (solvableResidual P))

private theorem sylow_in_normalized_subfactor
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) {K R : Subgroup G} (hRK : R ≤ K)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTR : (T : Subgroup G) ⊓ K ≤ normalizer (R : Set G)) :
    ∃ P : Sylow 2 R, (P : Subgroup R).map R.subtype = (T : Subgroup G) ⊓ R := by
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  have hn : (S : Subgroup K) ≤ normalizer (R.subgroupOf K : Set K) := by
    rw [hS]
    apply le_trans _ (le_normalizer_comap K.subtype)
    intro x hx
    exact hTR ⟨hx,x.property⟩
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow S (R.subgroupOf K) hn
  let e := subgroupOfEquivOfLe hRK
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((P : Subgroup (R.subgroupOf K)).map e.toMonoidHom).map R.subtype = _
  rw [hP,hS]
  ext x
  constructor
  · rintro ⟨r,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨hy,y.property⟩
  · rintro ⟨ht,hr⟩
    exact ⟨⟨x,hr⟩,⟨⟨⟨x,hRK hr⟩,hr⟩,ht,rfl⟩,rfl⟩

/-- The symplectic diagram source constructs actual rank-one factors in H,
with the original S and B normalizing them and with the required generation. -/
theorem symplectic_source_original_factors_marked
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L H A B : Subgroup G} {f : ℕ}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* Sp4Derived F)
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = sp4DerivedBorel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e
      ((pointParabolic (F := F)).subgroupOf (Sp4Derived F))
      ((planeParabolic (F := F)).subgroupOf (Sp4Derived F))) :
    ∃ eF : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* Sp F,
      (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
        eF.toMonoidHom = borel (F := F) ∧
      ∀ i, let R := fun j => (symplecticSourceFactor
        ((normalizer (L : Set G)).subgroupOf H) C eF j).map H.subtype
      R i ≤ residual H ∧ ¬ R i ≤ normalizer (L : Set G) ∧
      R i ⊔ (T : Subgroup G) = H ∧
      ClassicalGroup.IsPSL (R i ⧸ pCore 2 (R i)) 2 (2 ^ f) ∧
      ((R i).subgroupOf (R i ⊔ normalizingSylow T (R i))).IsCComponent ∧
      Global.sourceS L H ≤ normalizer (R i : Set G) ∧
      B ≤ normalizer (R i : Set G) ∧
      ∃ P : Sylow 2 (R i), (P : Subgroup (R i)).map (R i).subtype =
        Global.sourceS L H ⊓ R i := by
  let S := T.subtype hH.1.1.2
  let M := (normalizer (L : Set G)).subgroupOf H
  obtain ⟨eF,hmark,hr⟩ := symplectic_diagram_factors S (comap_mono hTL) hC hqs hc hf hF e he
  have hSK := diagram_sourceS_intersection_residual hTL hH hpar hC hc hf
    (Or.inr ⟨F,inferInstance,inferInstance,inferInstance,by omega,hF,e,he,hmove⟩)
  let R0 := symplecticSourceFactor M C eF
  let R (i : Bool) := (R0 i).map H.subtype
  refine ⟨eF,hmark,?_⟩
  intro i
  obtain ⟨hle,hnot,hquot,hcomp,hS⟩ := hr i
  have hRH : R i ≤ H := map_subtype_le _
  have hout : ¬ R i ≤ normalizer (L : Set G) :=
    fun hh => hnot (map_le_iff_le_comap.mp hh)
  let er := (R0 i).equivMapOfInjective H.subtype H.subtype_injective
  let eqr := QuotientGroup.congr _ _ er (pCore_map_iso 2 er)
  have hq : ClassicalGroup.IsPSL (R i ⧸ pCore 2 (R i)) 2 (2 ^ f) := hquot.of_mulEquiv eqr.symm
  have hp : Group.IsPerfect (R0 i) := by
    let : Group.IsPerfect ((R0 i).subgroupOf (normalizer (R0 i : Set H))) := hcomp.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (R0 i).le_normalizer).toMonoidHom)
      (subgroupOfEquivOfLe (R0 i).le_normalizer).surjective
  let := hp
  let : Group.IsPerfect (R i) := Group.IsPerfect.map H.subtype
  have hq0 := hq
  obtain ⟨E,_,_,hE,⟨eR⟩⟩ := hq0
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hE)
  have hlarge : 2 < Nat.card E := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ f by omega)
    omega
  let aSL := eR.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := E)).symm
  let : IsQuasisimple ((pointLocal (F := E)) ⧸ pCore 2 (pointLocal (F := E))) :=
    (pointNaturalExtension hE hf).quotient_quasisimple hlarge
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) E) :=
    IsQuasisimple.of_mulEquiv (pointLocalCoreQuotientEquiv hE hf)
  let : IsQuasisimple (R i ⧸ pCore 2 (R i)) := IsQuasisimple.of_mulEquiv aSL.symm
  let J := R i ⊔ normalizingSylow T (R i)
  have hNJ : J ≤ normalizer (R i : Set G) := sup_le (R i).le_normalizer inf_le_right
  let ej := subgroupOfEquivOfLe (show R i ≤ J from le_sup_left)
  let eqj := QuotientGroup.congr _ _ ej (pCore_map_iso 2 ej)
  let : IsQuasisimple (((R i).subgroupOf J) ⧸ pCore 2 ((R i).subgroupOf J)) :=
    IsQuasisimple.of_mulEquiv eqj.symm
  have hn : ((R i).subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hNJ
  have hjc : ((R i).subgroupOf J).IsCComponent :=
    isCComponent_of_isPPerfect_of_quasisimple_core_quotient hn.isSubnormal
      ((perfect_twoPerfect (R i)).of_surjective ej.symm.toMonoidHom ej.symm.surjective)
  have hSm : (M.pCoreIn 2).map H.subtype = Global.sourceS L H := by
    rw [map_pCoreIn_of_injective 2 M H.subtype H.subtype_injective,subgroupOf_map_subtype]
    rfl
  have hSn : Global.sourceS L H ≤ normalizer (R i : Set G) := by
    rw [←hSm]
    exact (map_mono hS).trans (le_normalizer_map H.subtype)
  have hBn : B ≤ normalizer (R i : Set G) := by
    have hbc : B.subgroupOf H ≤ M ⊓ C := by
      refine le_inf (comap_mono (c.right_le.trans inf_le_left)) ?_
      have heC := (DiagramHall.single_component_eq_twoResidual S hC hc).symm
      rw [heC]
      have hh := comap_mono (f := H.subtype) (Global.right_cartan_le_residual c)
      simpa only [residual,Subgroup.subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using hh
    have hn0 := hbc.trans (symplecticSourceFactor.overlap_normalizes eF hmark i)
    have hh := (map_mono (f := H.subtype) hn0).trans (le_normalizer_map H.subtype)
    change (B.subgroupOf H).map H.subtype ≤ normalizer (R i : Set G) at hh
    rwa [map_subgroupOf_eq_of_le (c.right_le.trans inf_le_right)] at hh
  have hRK : R i ≤ residual H := map_mono hle
  have hTR : (T : Subgroup G) ⊓ residual H ≤ normalizer (R i : Set G) :=
    (hSK.ge.trans inf_le_left).trans hSn
  obtain ⟨P,hP⟩ := sylow_in_normalized_subfactor T hRK
    (hH.1.1.2.trans (le_normalizer_residual H)) hTR
  have hSR : Global.sourceS L H ⊓ R i = (T : Subgroup G) ⊓ R i := by
    calc
      _ = (Global.sourceS L H ⊓ residual H) ⊓ R i := by rw [inf_assoc,inf_eq_right.mpr hRK]
      _ = ((T : Subgroup G) ⊓ residual H) ⊓ R i := by rw [hSK]
      _ = _ := by rw [inf_assoc,inf_eq_right.mpr hRK]
  refine ⟨hRK,hout,?_,hq,hjc,hSn,hBn,P,hP.trans hSR.symm⟩
  apply le_antisymm (sup_le hRH hH.1.1.2)
  by_contra hh
  have hlt : R i ⊔ (T : Subgroup G) < H :=
    lt_of_le_of_ne (sup_le hRH hH.1.1.2) (fun he => hh he.ge)
  exact hout (le_sup_left.trans (Chapter3.HStar.proper_overgroup_le T hH le_sup_right hlt))

/-- The symplectic diagram source constructs actual rank-one factors in H,
with the original S and B normalizing them and with the required generation. -/
theorem symplectic_source_original_factors
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L H A B : Subgroup G} {f : ℕ}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* Sp4Derived F)
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = sp4DerivedBorel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e
      ((pointParabolic (F := F)).subgroupOf (Sp4Derived F))
      ((planeParabolic (F := F)).subgroupOf (Sp4Derived F))) :
    ∃ R : Bool → Subgroup G, ∀ i,
      R i ≤ residual H ∧ ¬ R i ≤ normalizer (L : Set G) ∧
      R i ⊔ (T : Subgroup G) = H ∧
      ClassicalGroup.IsPSL (R i ⧸ pCore 2 (R i)) 2 (2 ^ f) ∧
      ((R i).subgroupOf (R i ⊔ normalizingSylow T (R i))).IsCComponent ∧
      Global.sourceS L H ≤ normalizer (R i : Set G) ∧
      B ≤ normalizer (R i : Set G) ∧
      ∃ P : Sylow 2 (R i), (P : Subgroup (R i)).map (R i).subtype =
        Global.sourceS L H ⊓ R i := by
  obtain ⟨eF,_,hr⟩ := symplectic_source_original_factors_marked
    hTL hH hpar c hC hqs hc hf hF e he hmove
  exact ⟨fun i => (symplecticSourceFactor
    ((normalizer (L : Set G)).subgroupOf H) C eF i).map H.subtype,hr⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
