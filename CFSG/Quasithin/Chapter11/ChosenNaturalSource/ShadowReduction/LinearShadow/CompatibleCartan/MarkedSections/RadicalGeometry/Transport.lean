module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.MarkedSections.RadicalGeometry.Model
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.MarkedSections.Source
public import Theory.GroupTheory.PCoreImageRestriction
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The literal source radical intersection

The same aligned quotient and vector coordinates identify the actual
Rᵢ = O₂(LᵢT) with the preimage of the corresponding model radical.
For every v outside V₂, membership of p in P intersect R₁ is equivalent
to [v,p] lying in V₁. The highest root image has order q and the literal
kernel V₂ has order q², giving |P intersect R₁| = q³.

Source: Aschbacher--Smith, 11.3.8 and its following complement paragraph,
printed pp.774–775. In particular R₁ is not replaced by O₂(L₁).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Matrix
open scoped MatrixGroups IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterB.QuasisimpleSource

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.MarkedSections.RadicalGeometry
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
open Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m))

/-- The same aligned quotient sends the original Sylow into both flag locals. -/
theorem sylow_image_le_local (i : Fin 2) :
    ((T : Subgroup G).subgroupOf L).map (SL3.PlaneAction.alignedQuotient D S m) ≤
      SL3.PlaneAction.localGroup (F := S.field.Carrier) i := by
  rintro _ ⟨t,ht,rfl⟩
  have ht' : (SL3.coordinates D S m).quotientMap t ∈
      (SL3.innerSylow D S m : Subgroup SL(3,S.field.Carrier)) := by
    rw [SL3.innerSylow_eq]
    exact mem_map_of_mem _ ht
  rw [← SL3.alignment_sylow] at ht'
  obtain ⟨u,hu,he⟩ := ht'
  have hq : SL3.PlaneAction.alignedQuotient D S m t = u := by
    change (MulAut.conj (SL3.alignment D S m)⁻¹)
      ((SL3.coordinates D S m).quotientMap t) = u
    rw [← he]
    simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv]
    group
  rw [hq]
  fin_cases i
  · exact hu.1
  · exact hu.2

/-- The quotient of the actual local join, before taking its two-core. -/
theorem local_join_image (hTL : (T : Subgroup G) ≤ L) (i : Fin 2) :
    ((f.Li i ⊔ (T : Subgroup G)).subgroupOf L).map
      (SL3.PlaneAction.alignedQuotient D S m) =
      SL3.PlaneAction.localGroup (F := S.field.Carrier) i := by
  rw [flag_eq D S m f]
  have hle : (SL3.flag D S m).Li i ≤ L := (localResidual_le _).trans inf_le_left
  rw [subgroupOf_sup hle hTL, Subgroup.map_sup,
    SL3.PlaneAction.local_image]
  exact sup_eq_left.mpr (sylow_image_le_local D S m i)

/-- The literal Rᵢ is the preimage of the model local radical, in L. -/
theorem radical_preimage (hTL : (T : Subgroup G) ≤ L) (i : Fin 2) :
    (f.Ri i).subgroupOf L =
      ((SL3.PlaneAction.localGroup (F := S.field.Carrier) i).pCoreIn 2).comap
        (SL3.PlaneAction.alignedQuotient D S m) := by
  let q := SL3.PlaneAction.alignedQuotient D S m
  let A := (f.Li i ⊔ (T : Subgroup G)).subgroupOf L
  have hA : f.Li i ⊔ (T : Subgroup G) ≤ L :=
    sup_le ((localResidual_le _).trans inf_le_left) hTL
  have hk : IsPGroup 2 q.ker := by
    rw [SL3.PlaneAction.alignedQuotient_ker]
    exact pCore_isPGroup
  have hker : q.ker ≤ A := by
    intro x hx
    have hp : (x : G) ∈ L.pCoreIn 2 :=
      mem_map_of_mem L.subtype ((SL3.PlaneAction.alignedQuotient_ker D S m) ▸ hx)
    have hh := (pCoreIn_le_sylow L (T.subtype hTL)) hp
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTL] at hh
    exact mem_sup_right hh
  have him : A.map q = SL3.PlaneAction.localGroup (F := S.field.Carrier) i :=
    local_join_image D S m f hTL i
  have hc := inf_comap_pCoreIn_eq_of_ker_isPGroup 2 q A hk
  have hle : ((A.map q).pCoreIn 2).comap q ≤ A := by
    apply (comap_mono (pCoreIn_le 2 (A.map q))).trans
    exact (comap_map_eq_self hker).le
  rw [inf_eq_right.mpr hle, him] at hc
  change ((f.Li i ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf L = _
  rw [← pCoreIn_subgroupOf 2 _ L hA]
  exact hc.symm

/-- The literal common core has exactly the line-radical image. -/
theorem common_core_image (P : Subgroup G) (hP : P = (f.Li 1).pCoreIn 2) :
    (P.subgroupOf L).map (SL3.PlaneAction.alignedQuotient D S m) =
      (lineLocalSL S.field.Carrier).pCoreIn 2 := by
  subst P
  rw [flag_eq D S m f]
  have hle : (SL3.flag D S m).Li 1 ≤ L := (localResidual_le _).trans inf_le_left
  rw [← pCoreIn_subgroupOf 2 _ L hle, map_pCoreIn_of_ker_isPGroup]
  · rw [SL3.PlaneAction.local_image]
    rfl
  · rw [SL3.PlaneAction.alignedQuotient_ker]
    exact pCore_isPGroup
/-- Radical membership for a given element of the original L. -/
theorem mem_radical_iff (hTL : (T : Subgroup G) ≤ L) (i : Fin 2) (l : L) :
    (l : G) ∈ f.Ri i ↔ SL3.PlaneAction.alignedQuotient D S m l ∈
      (SL3.PlaneAction.localGroup (F := S.field.Carrier) i).pCoreIn 2 := by
  change l ∈ (f.Ri i).subgroupOf L ↔ _
  rw [radical_preimage D S m f hTL i]
  rfl

/-- The kernel remains the original V, not merely an isomorphic two-group. -/
theorem quotient_eq_one_iff (hcore : L.pCoreIn 2 = V) (l : L) :
    SL3.PlaneAction.alignedQuotient D S m l = 1 ↔ (l : G) ∈ V := by
  change l ∈ (SL3.PlaneAction.alignedQuotient D S m).ker ↔ _
  rw [SL3.PlaneAction.alignedQuotient_ker, ← hcore]
  exact (mem_map_iff_mem L.subtype_injective).symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.MarkedSections.RadicalGeometry

open Subgroup Theory.GroupTheory Representation Matrix
open scoped MatrixGroups IsMulCommutative commutatorElement
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.MarkedSections.RadicalGeometry
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- Natural coordinates with exactly the same alignment as the local quotient. -/
def alignedVectors : Additive V ≃+ (Fin 3 → S.field.Carrier) :=
  (SL3.naturalEquiv D S m).toAdditiveLeft.trans
    ((Coordinates.sl3 m).modelLinearEquiv (SL3.alignment D S m)⁻¹).toAddEquiv

theorem alignedVectors_apply (v : Additive V) :
    alignedVectors D S m v = specialLinearNatural 3 (SL3.alignment D S m)⁻¹
      ((Coordinates.sl3 m).projection v.toMul).toAdd := rfl

/-- The vector alignment and the quotient alignment intertwine exactly. -/
theorem alignedVectors_conjugation (l : L) (v : V) :
    alignedVectors D S m (Additive.ofMul
      (V.normalizerMonoidHom (inclusion D.normalizes l) v)) =
      (SL3.PlaneAction.alignedQuotient D S m l).val.mulVec
        (alignedVectors D S m (Additive.ofMul v)) := by
  change specialLinearNatural 3 (SL3.alignment D S m)⁻¹
    (SL3.naturalEquiv D S m (V.normalizerMonoidHom (inclusion D.normalizes l) v)).toAdd = _
  rw [SL3.naturalEquiv_conjugation]
  change specialLinearNatural 3 (SL3.alignment D S m)⁻¹
    (specialLinearNatural 3 ((Coordinates.sl3 m).quotientMap l)
      (SL3.naturalEquiv D S m v).toAdd) =
    specialLinearNatural 3 (SL3.PlaneAction.alignedQuotient D S m l)
      (specialLinearNatural 3 (SL3.alignment D S m)⁻¹ (SL3.naturalEquiv D S m v).toAdd)
  simp [SL3.PlaneAction.alignedQuotient, map_mul, map_inv]
  rfl

/-- Membership in each original flag subgroup in the single aligned basis. -/
theorem mem_flag_aligned (f : InvariantFlag (.sl3 m)) (i : Fin 3) (v : V) :
    (v : G) ∈ f.Vi i ↔ alignedVectors D S m (Additive.ofMul v) ∈ SL3.Model.flag i := by
  rw [flag_eq D S m f]
  change (v : G) ∈ (Coordinates.sl3 m).preimage (SL3.Model.flagFor (SL3.alignment D S m) i) ↔ _
  rw [Coordinates.mem_preimage, SL3.PlaneAction.mem_flagFor_iff]
  rfl

/-- The literal group commutator has the expected displacement coordinates. -/
theorem alignedVectors_commutator (l : L) (v : V) :
    ∃ w : V, (w : G) = ⁅(v : G),(l : G)⁆ ∧
      alignedVectors D S m (Additive.ofMul w) =
        alignedVectors D S m (Additive.ofMul v) -
          (SL3.PlaneAction.alignedQuotient D S m l).val.mulVec
            (alignedVectors D S m (Additive.ofMul v)) := by
  let v' := V.normalizerMonoidHom (inclusion D.normalizes l) v
  refine ⟨v * v'⁻¹, ?_, ?_⟩
  · change (v : G) * ((l : G) * (v : G) * (l : G)⁻¹)⁻¹ = _
    simp only [commutatorElement_def]
    group
  · rw [sub_eq_add_neg]
    change alignedVectors D S m (Additive.ofMul v + -Additive.ofMul v') = _
    rw [map_add, map_neg, alignedVectors_conjugation]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.MarkedSections.RadicalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.MarkedSections.RadicalGeometry
open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
open Matrix.PSL3.LinearThree
open scoped MatrixGroups IsMulCommutative commutatorElement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m)) (P : Subgroup G)
    (hP : P = (f.Li 1).pCoreIn 2) (hTL : (T : Subgroup G) ≤ L)

include hP hTL

/-- Every vector outside V₂ detects the literal radical intersection. -/
theorem radical_incidence (v : V) (hv : (v : G) ∉ f.Vi 1) (p : P) :
    (p : G) ∈ f.Ri 0 ↔ ⁅(v : G),(p : G)⁆ ∈ f.Vi 0 := by
  have hPL : P ≤ L := hP ▸ (pCoreIn_le 2 (f.Li 1)).trans
    ((localResidual_le _).trans inf_le_left)
  let l : L := inclusion hPL p
  have hp : SL3.PlaneAction.alignedQuotient D S m l ∈ (lineLocalSL S.field.Carrier).pCoreIn 2 := by
    rw [← common_core_image D S m f P hP]
    exact mem_map_of_mem _ p.property
  have hv' : alignedVectors D S m (Additive.ofMul v) 2 ≠ 0 := by
    intro hz
    apply hv
    exact (mem_flag_aligned D S m f 1 v).mpr hz
  obtain ⟨w,hw,he⟩ := alignedVectors_commutator D S m l v
  change (l : G) ∈ f.Ri 0 ↔ ⁅(v : G),(l : G)⁆ ∈ f.Vi 0
  rw [← hw,mem_flag_aligned D S m f 0 w,he]
  exact (mem_radical_iff D S m f hTL 0 l).trans
    (line_core_displacement _ hp _ hv').symm

/-- A source vector for the radical hyperplane exists in the original V. -/
theorem exists_radical_incidence :
    ∃ v : V, (v : G) ∉ f.Vi 1 ∧
      ∀ p : P, (p : G) ∈ f.Ri 0 ↔ ⁅(v : G),(p : G)⁆ ∈ f.Vi 0 := by
  let v := (alignedVectors D S m).symm ![0,0,1]
  have hv : (v.toMul : G) ∉ f.Vi 1 := by
    intro hh
    have he := (mem_flag_aligned D S m f 1 v.toMul).mp hh
    change alignedVectors D S m v 2 = 0 at he
    rw [show alignedVectors D S m v = ![0,0,1] from
      (alignedVectors D S m).apply_symm_apply _] at he
    exact one_ne_zero he
  exact ⟨v.toMul,hv,radical_incidence D S m f P hP hTL v.toMul hv⟩

/-- The order of the literal radical intersection is q³. -/
theorem radical_intersection_card (hcore : L.pCoreIn 2 = V)
    (hPV : P ⊓ V = f.Vi 1) :
    Nat.card (P ⊓ f.Ri 0 : Subgroup G) = (2 ^ S.field.degree) ^ 3 := by
  let A := P ⊓ f.Ri 0
  have hPL : P ≤ L := hP ▸ (pCoreIn_le 2 (f.Li 1)).trans
    ((localResidual_le _).trans inf_le_left)
  let q := SL3.PlaneAction.alignedQuotient D S m
  let r : A →* SL(3,S.field.Carrier) := q.comp (inclusion (inf_le_left.trans hPL))
  have hr : r.range = (lineLocalSL S.field.Carrier).pCoreIn 2 ⊓
      (pointLocalSL S.field.Carrier).pCoreIn 2 := by
    apply le_antisymm
    · rintro g ⟨a,rfl⟩
      refine ⟨?_,?_⟩
      · rw [← common_core_image D S m f P hP]
        exact mem_map_of_mem q a.property.1
      · exact (mem_radical_iff D S m f hTL 0
          (inclusion (inf_le_left.trans hPL) a)).mp a.property.2
    · rintro g ⟨hg,hpt⟩
      rw [← common_core_image D S m f P hP] at hg
      obtain ⟨p,hp,he⟩ := hg
      have hpR : (p : G) ∈ f.Ri 0 :=
        (mem_radical_iff D S m f hTL 0 p).mpr (he ▸ hpt)
      exact ⟨⟨p,hp,hpR⟩,he⟩
  let ek : r.ker ≃ f.Vi 1 := {
    toFun := fun z => ⟨z.val,hPV ▸ ⟨z.val.property.1,
      (quotient_eq_one_iff D S m hcore (inclusion (inf_le_left.trans hPL) z.val)).mp z.property⟩⟩
    invFun := fun z => by
      have hz : (z : G) ∈ P ⊓ V := hPV.symm ▸ z.property
      let a : A := ⟨z,hz.1,f.seed_le_Ri S 0 hz.2⟩
      exact ⟨a,(quotient_eq_one_iff D S m hcore
        (inclusion (inf_le_left.trans hPL) a)).mpr hz.2⟩
    left_inv := by intro z; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro z; apply Subtype.ext; rfl }
  have hk : Nat.card r.ker = (2 ^ S.field.degree)^2 := by
    rw [Nat.card_congr ek,← hPV]
    exact (Nat.card_congr (planeCoordinates D S m f P hPV).toEquiv).trans
      (by simp only [Nat.card_fun,Nat.card_fin,S.field.card_eq])
  have hc := r.ker.card_mul_index
  rw [index_ker,hr,card_radical_intersection,S.field.card_eq,hk] at hc
  change Nat.card A = _
  rw [←hc]
  ring
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.MarkedSections.RadicalGeometry
