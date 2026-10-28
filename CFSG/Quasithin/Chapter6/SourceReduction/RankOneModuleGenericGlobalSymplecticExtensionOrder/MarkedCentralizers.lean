module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.FixedQuotient
public import CFSG.Quasithin.Chapter5.Section03SymplecticSource.MarkedCentralizers

/-!
# Three full centralizer comparisons for the prepared symplectic row

The original root-centralizer bounds and the proved S=T square-centralizer
bound combine with the extension bounds to identify the full centralizers.
The isomorphisms are restrictions of the same coherent full-normalizer
marking, retaining its pure endpoints and whole middle in either orientation.
Thus the distinguished elements and all outer actors retain their literal
images. The later order argument must still prove the three-class catalogue
and preservation of the selected class predicates inside these centralizers.

Source: Aschbacher--Smith 5.3.2--3 and F.4.39,42--43, printed pp.658--659
and 294--296 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
open SourceFusionOrder
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem endpoint_center_image {F : Type*} [Field F]
    {K P : Subgroup G} {R Q : Subgroup (Sp F)} (_hKP : K≤P) (e : P≃*Q)
    (hR : (K.subgroupOf P).map (Q.subtype.comp e.toMonoidHom)=R)
    (z : P) (hz : z.val∈(center K).map K.subtype) :
    (e z).val∈(center R).map R.subtype := by
  let φ := Q.subtype.comp e.toMonoidHom
  obtain ⟨k,hk,hkz⟩ := hz
  have hxK : z.val∈K := hkz ▸ k.property
  refine ⟨⟨φ z,hR ▸ mem_map_of_mem φ hxK⟩,mem_center_iff.mpr ?_,rfl⟩
  intro r
  obtain ⟨x,hx,hxr⟩ := (show r.val∈(K.subgroupOf P).map φ from hR.symm ▸ r.property)
  apply Subtype.ext
  change r.val*φ z=φ z*r.val
  rw [←hxr,←map_mul,←map_mul]
  apply congrArg φ
  apply Subtype.ext
  have hh := congrArg (fun v : K => v.val) ((mem_center_iff.mp hk) ⟨x.val,hx⟩)
  change x.val*k.val=k.val*x.val at hh
  change k.val=z.val at hkz
  change x.val*z.val=z.val*x.val
  rwa [hkz] at hh

omit [Finite G] in
private theorem root_centralizer_comparison {F : Type*} [Field F] [CharP F 2]
    {K P M : Subgroup G} (hKP : K≤P) (hPM : P≤M)
    {Q R : Subgroup (Sp F)} (e : P≃*Q)
    (hR : (K.subgroupOf P).map (Q.subtype.comp e.toMonoidHom)=R)
    (E : SourceExtension F) (N : Subgroup (MulAut (Sp F))) (hN : N≤E.carrier)
    (f : M≃*N) (hmark : ∀ x, (f (inclusion hPM x)).val=MulAut.conj (e x).val)
    (hc : ∀ z∈(center R).map R.subtype, z≠1 →
      centralizer ({E.innerMap z} : Set E.carrier)≤N.subgroupOf E.carrier)
    (ha : ∀ z∈(center K).map K.subtype, orderOf z=2 → centralizer ({z} : Set G)≤M)
    (z : M) (hz : z.val∈(center K).map K.subtype) (hz2 : orderOf z.val=2) :
    MarkedCentralizerComparison M ((inclusion hN).comp f.toMonoidHom) z := by
  let zP : P := ⟨z.val,hKP (map_subtype_le _ hz)⟩
  have hzr := endpoint_center_image hKP e hR zP hz
  have hzne : (e zP).val≠1 := by
    intro he
    have he' : z.val=1 := congrArg P.subtype (e.map_eq_one_iff.mp (Subtype.ext he))
    simp [he'] at hz2
  let φ : M→*E.carrier := (inclusion hN).comp f.toMonoidHom
  have hφ : Function.Injective φ := (inclusion_injective hN).comp f.injective
  have hm : φ z=E.innerMap (e zP).val := Subtype.ext (hmark zP)
  apply marked_centralizer_comparison M φ hφ z (ha z.val hz hz2)
  intro x hx
  have hxN : x.val∈N := hc _ hzr hzne (hm ▸ hx)
  refine ⟨f.symm ⟨x.val,hxN⟩,?_⟩
  apply Subtype.ext
  change (f (f.symm ⟨x.val,hxN⟩)).val=x.val
  exact congrArg (fun v : N => v.val) (f.apply_symm_apply ⟨x.val,hxN⟩)

private theorem marked_sylow_equiv {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0<m) (hF : Nat.card F=2^m)
    {S C : Subgroup G} (hSC : S≤C) (hs : Chapter1.IsSylowIn 2 S C)
    (e : C ≃* borel (F := F)) :
    ∃ eS : S ≃* unipotent (F := F),
      ∀ s : S, (e (inclusion hSC s)).val=(eS s).val := by
  obtain ⟨R,hR⟩ := hs
  have hRS : (R : Subgroup C)=S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [hR,map_subgroupOf_eq_of_le hSC]
  let U := (unipotentSylow hF hm).subtype unipotent_le_borel
  let : (U : Subgroup (borel (F := F))).Normal := unipotent_normal_in_borel
  let := Sylow.unique_of_normal U (inferInstance : U.Normal)
  have hSU : (S.subgroupOf C).map e.toMonoidHom=unipotent.subgroupOf borel := by
    rw [←hRS]
    exact congrArg Sylow.toSubgroup (Subsingleton.elim
      (R.mapSurjective (f := e.toMonoidHom) e.surjective) U)
  let eS : S ≃* unipotent (F := F) := (subgroupOfEquivOfLe hSC).symm.trans
    ((e.subgroupMap (S.subgroupOf C)).trans
      ((MulEquiv.subgroupCongr hSU).trans (subgroupOfEquivOfLe unipotent_le_borel)))
  exact ⟨eS,fun _ => rfl⟩

private theorem square_centralizer_comparison {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0<m) (hF : Nat.card F=2^m) (hm' : 1<m)
    {S C D : Subgroup G} (hSC : S≤C) (hCD : C≤D) (hs : Chapter1.IsSylowIn 2 S C)
    (e : C≃*borel (F := F)) (E : SourceExtension F)
    (f : D≃*E.middle) (hmark : ∀ x, (f (inclusion hCD x)).val=MulAut.conj (e x).val)
    (z : S) (hne : z≠1) (hsq : ∃ y : S, y^2=z)
    (hc : centralizer ({z.val} : Set G)≤D) :
    MarkedCentralizerComparison D
      ((inclusion (inf_le_left.trans E.left_le)).comp f.toMonoidHom)
      (inclusion (hSC.trans hCD) z) := by
  obtain ⟨a,ha⟩ := marked_sylow_equiv hm hF hSC hs e
  let φ : D→*E.carrier := (inclusion (inf_le_left.trans E.left_le)).comp f.toMonoidHom
  have hφ : Function.Injective φ := (inclusion_injective (inf_le_left.trans E.left_le)).comp f.injective
  have hmark' : φ (inclusion (hSC.trans hCD) z)=E.innerMap (a z).val := by
    apply Subtype.ext
    exact (hmark (inclusion hSC z)).trans (congrArg MulAut.conj (ha z))
  apply marked_centralizer_comparison D φ hφ _ hc
  intro x hx
  have hsq' : ∃ y : unipotent (F := F), y^2=a z := by
    obtain ⟨y,hy⟩ := hsq
    exact ⟨a y,by rw [←map_pow,hy]⟩
  have hxM : x.val∈E.middle :=
    Chapter5.Section03SymplecticSource.extension_square_centralizer hF hm' E (a z)
      (a.map_ne_one_iff.mpr hne) hsq' (hmark' ▸ hx)
  refine ⟨f.symm ⟨x.val,hxM⟩,?_⟩
  apply Subtype.ext
  change (f (f.symm ⟨x.val,hxM⟩)).val=x.val
  exact congrArg (fun v : E.middle => v.val) (f.apply_symm_apply ⟨x.val,hxM⟩)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
open SourceFusionOrder
variable {G : Type*} [Group G] [Finite G]

/-- The root-centralizer comparisons for one prescribed endpoint marking. -/
@[expose] def SymplecticRootComparisons {J : Type*} [Group J]
    (K M : Subgroup G) (φ : M→*J) : Prop :=
  ∀ z : M, z.val∈(center K).map K.subtype → orderOf z.val=2 →
    MarkedCentralizerComparison M φ z

/-- The square-centralizer comparisons for the prescribed whole-middle marking. -/
@[expose] def SymplecticSquareComparisons {J : Type*} [Group J]
    (S D : Subgroup G) (φ : D→*J) (hSD : S≤D) : Prop :=
  ∀ z : S, orderOf z=2 → (∃ y : S, y^2=z) →
    MarkedCentralizerComparison D φ (inclusion hSD z)

/-- Full centralizer comparisons retaining the same pure pair, full endpoints,
and whole middle, in either orientation. -/
@[expose] def SymplecticMarkedCentralizers {L K S : Subgroup G}
    {F : Type*} [Field F] (a : SymplecticNormalizerMarking L K S F) : Prop :=
    let M₁ := normalizer (L : Set G)
    let M₂ := normalizer (K : Set G)
    let hSD : S≤M₁⊓M₂ :=
      le_inf ((le_sup_right.trans le_sup_left).trans a.left_le)
        ((le_sup_right.trans le_sup_left).trans a.right_le)
    (∃ e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] (S))
        (SourceNormalizerExtension.diagram F),
      ∃ f : RankTwoAmalgam.Iso (SymplecticCompletion.diagram L (K)) a.extension.amalgam,
      (∀ x, (f.left (inclusion a.left_le x)).val=MulAut.conj (e.left x).val) ∧
      (∀ x, (f.right (inclusion a.right_le x)).val=MulAut.conj (e.right x).val) ∧
      (∀ x, (f.middle (inclusion (le_inf (inf_le_left.trans a.left_le)
        (inf_le_right.trans a.right_le)) x)).val=MulAut.conj (e.middle x).val) ∧
      SymplecticRootComparisons L M₁ ((inclusion a.extension.left_le).comp f.left.toMonoidHom) ∧
      SymplecticRootComparisons (K) M₂ ((inclusion a.extension.right_le).comp f.right.toMonoidHom) ∧
      SymplecticSquareComparisons (S) (M₁⊓M₂)
        ((inclusion (inf_le_left.trans a.extension.left_le)).comp f.middle.toMonoidHom) hSD) ∨
    (∃ e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] (S))
        (SourceNormalizerExtension.diagram F).reverse,
      ∃ f : RankTwoAmalgam.Iso (SymplecticCompletion.diagram L (K)) a.extension.amalgam.reverse,
      (∀ x, (f.left (inclusion a.left_le x)).val=MulAut.conj (e.left x).val) ∧
      (∀ x, (f.right (inclusion a.right_le x)).val=MulAut.conj (e.right x).val) ∧
      (∀ x, (f.middle (inclusion (le_inf (inf_le_left.trans a.left_le)
        (inf_le_right.trans a.right_le)) x)).val=MulAut.conj (e.middle x).val) ∧
      SymplecticRootComparisons L M₁ ((inclusion a.extension.right_le).comp f.left.toMonoidHom) ∧
      SymplecticRootComparisons (K) M₂ ((inclusion a.extension.left_le).comp f.right.toMonoidHom) ∧
      SymplecticSquareComparisons (S) (M₁⊓M₂)
        ((inclusion (inf_le_left.trans a.extension.left_le)).comp f.middle.toMonoidHom) hSD)

variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
include d h hH hp hm hF he

/-- Both root classes and the nonroot square class have full ambient
centralizers identified by the same full-normalizer marking. The pointwise
map equations include the distinguished involutions and all outer actors. -/
theorem Preparation.symplectic_marked_centralizers
    (a : SymplecticNormalizerMarking L (residual H) (sourceS L H) F) :
    SymplecticMarkedCentralizers a := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let C := P 0⊓P 1
  let D := normalizer (L : Set G)⊓normalizer (residual H : Set G)
  have hSC : sourceS L H≤C :=
    le_inf (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_left)
  have hCD : C≤D := le_inf (inf_le_left.trans a.left_le) (inf_le_right.trans a.right_le)
  have hf := d.hypothesisF11 h hH.1.1.2
  have hs : Chapter1.IsSylowIn 2 (sourceS L H) C := by
    change Chapter1.IsSylowIn 2 (sourceS L H) (P 0⊓P 1)
    rw [show P 0⊓P 1=ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) from
      ChapterF.Source.lemma_F_1_3_6 hf]
    exact hf.sylow_commonBorel
  have hm' : 1<m := (d.symplectic_amalgam_blocks h hH.1.1.2 hp F hm hF he).1.symm ▸ h.exponent
  have hres (i : Fin 2) : (![L,residual H] i).subgroupOf (P i)=solvableResidual (P i) := by
    rw [←d.parabolic_residuals h hH.1.1.2 hp i]
    exact comap_map_eq_self_of_injective (P i).subtype_injective _
  have hpoint (i : Fin 2) (e : P i≃*pointParabolic (F := F)) :
      ((![L,residual H] i).subgroupOf (P i)).map
        (pointParabolic.subtype.comp e.toMonoidHom)=pointLocal := by
    rw [hres,←map_map,map_solvableResidual_eq e.toMonoidHom e.surjective]
    exact pointParabolic_solvableResidual_eq hF hm'
  have hplane (i : Fin 2) (e : P i≃*planeParabolic (F := F)) :
      ((![L,residual H] i).subgroupOf (P i)).map
        (planeParabolic.subtype.comp e.toMonoidHom)=planeLocal := by
    rw [hres,←map_map,map_solvableResidual_eq e.toMonoidHom e.surjective]
    exact planeParabolic_solvableResidual_eq hF hm'
  have hc := d.symplectic_central_involution_centralizers h hH hp F hm hF he
  have hsq (e : C≃*borel (F := F)) (f : D≃*a.extension.middle)
      (hf : ∀ x, (f (inclusion hCD x)).val=MulAut.conj (e x).val) :
      SymplecticSquareComparisons (sourceS L H) D
        ((inclusion (inf_le_left.trans a.extension.left_le)).comp f.toMonoidHom) (hSC.trans hCD) := by
    intro z hz hzs
    exact square_centralizer_comparison hm hF hm' hSC hCD hs e a.extension f hf z
      (by intro hh; simp [hh] at hz) hzs
      (d.symplectic_square_centralizer_le_middle h hH hp F hm hF he z hz hzs)
  rcases a.comparison with ⟨e,f,hl,hr,hd⟩ | ⟨e,f,hl,hr,hd⟩
  · left
    refine ⟨e,f,hl,hr,hd,?_,?_,hsq e.middle f.middle hd⟩
    · exact root_centralizer_comparison (le_sup_left.trans le_sup_left) a.left_le e.left
        (hpoint 0 e.left) a.extension a.extension.left a.extension.left_le f.left hl
        (Chapter5.Section03SymplecticSource.extension_point_centralizer hF hm' a.extension) (hc 0)
    · exact root_centralizer_comparison (le_sup_left.trans le_sup_left) a.right_le e.right
        (hplane 1 e.right) a.extension a.extension.right a.extension.right_le f.right hr
        (Chapter5.Section03SymplecticSource.extension_plane_centralizer hF hm' a.extension) (hc 1)
  · right
    refine ⟨e,f,hl,hr,hd,?_,?_,hsq e.middle f.middle hd⟩
    · exact root_centralizer_comparison (le_sup_left.trans le_sup_left) a.left_le e.left
        (hplane 0 e.left) a.extension a.extension.right a.extension.right_le f.left hl
        (Chapter5.Section03SymplecticSource.extension_plane_centralizer hF hm' a.extension) (hc 0)
    · exact root_centralizer_comparison (le_sup_left.trans le_sup_left) a.right_le e.right
        (hpoint 1 e.right) a.extension a.extension.left a.extension.left_le f.right hr
        (Chapter5.Section03SymplecticSource.extension_point_centralizer hF hm' a.extension) (hc 1)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
