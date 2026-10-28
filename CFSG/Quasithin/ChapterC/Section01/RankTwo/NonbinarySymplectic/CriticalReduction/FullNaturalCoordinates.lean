module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallMovers
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedIndex
public import Theory.Representation.BinaryOffender.EmbeddedFixedIndex
public import Theory.Representation.SymplecticFourOrthogonalCover.QuadraticLifting

/-!
# Full natural coordinates for the replacement edge

One marking of the entire vertex quotient gives exact fixed indices and
lifts quadratic action to the full U-layer, including its central kernel.
Conjugating a containing Sylow keeps these two properties in the same
coordinates. This is the shared action input to the root-product argument
and the maximizing parabolic choice of MS93 (5.0)--(5.1), pp.912--913.
The construction is extracted unchanged from RootProductQuadratic.
-/

public noncomputable section
open Subgroup Matrix Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation.SymplecticFourOrthogonalCover
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A single marking of the whole vertex quotient computes every exact
centralizer index on the original U, including its entire fixed kernel. -/
private theorem inner_indices_quadratic
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp E.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)) (A.map f)) ∧
        ∀ A : Subgroup (stabilizer d.radical a),
          IsQuadratic (restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)) (A.map f) →
          ⁅⁅(U d.radical a).subgroupOf (stabilizer d.radical a),A⁆,A⁆ = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d ha
  have hCtop : C = ⊤ := by
    have hpre : C.comap q = ⊤ := by
      rw [show C = (K.subgroupOf d.overgroup).map q from rfl,
        comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hpre]
    rw [←MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hlarge : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let ed : L (K := E.Carrier) ≃* Sp E.Carrier :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hlarge)).trans Subgroup.topEquiv
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let fD := e.groupEquiv.toMonoidHom.comp κC
  let f := ed.toMonoidHom.comp fD
  have hκC : Function.Surjective κC := by
    intro x
    obtain ⟨g,hg⟩ := hκ x
    exact ⟨g,Subtype.ext hg⟩
  have hf : Function.Surjective f := ed.surjective.comp (e.groupEquiv.surjective.comp hκC)
  have hfker : f.ker = κ.ker := by
    ext x
    change ed (e.groupEquiv (κC x)) = 1 ↔ κ x = 1
    rw [ed.map_eq_one_iff,e.groupEquiv.map_eq_one_iff]
    exact Subtype.ext_iff
  let S := stabilizer d.radical a
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  let U₀ := (U d.radical a).subgroupOf S
  let jS := j.codRestrict S (fun w => hUS (hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)))
  have hjS : Function.Injective jS := fun v w he => hj (congrArg Subtype.val he)
  have hjSr : jS.range = U₀ := by
    ext x
    constructor
    · rintro ⟨w,rfl⟩
      change j w ∈ U d.radical a
      exact hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)
    · intro hx
      obtain ⟨w,hw⟩ := (show x.val ∈ j.range from hjr.symm ▸ hx)
      exact ⟨w,Subtype.ext hw⟩
  let σ := MovedSection.coverAction s e
  have haction (x : S) (w : s.space.toSubmodule) :
      jS (Multiplicative.ofAdd (σ (fD x) w)) =
        x * jS (Multiplicative.ofAdd w) * x⁻¹ := by
    apply Subtype.ext
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  refine ⟨E,hE,f,hf,by rw [hfker]; exact hκQ,?_,?_⟩
  · intro A
    have hi := embedded_centralizer_index σ U₀ A jS hjS hjSr (fD.comp A.subtype)
      (fun x w => haction x.val w)
    rw [fixedCodim_of_binaryCover (MovedSection.coverProjection s e) he] at hi
    rw [MonoidHom.range_comp,range_subtype] at hi
    rw [hi]
    congr 1
    let τ := restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)
    have hσ : binaryNatural (K := E.Carrier) = τ.comp ed.toMonoidHom := rfl
    rw [hσ,fixedCodim,fixedSpace_comp_map,Subgroup.map_map]
    rfl
  · intro A hquad
    refine embedded_quadratic_of_natural_quadratic U₀ A jS hjSr
      (fD.comp A.subtype) σ (fun x w => haction x.val w)
      (MovedSection.coverProjection s e) he ?_
    intro x y v
    exact hquad (f x.val) (mem_map_of_mem f x.property)
      (f y.val) (mem_map_of_mem f y.property) v

omit h d in
private theorem quadratic_conjugate {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    {A : Subgroup G} (hA : IsQuadratic ρ A) (g : G) :
    IsQuadratic ρ (A.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
  change ρ (g*a*g⁻¹) (ρ (g*b*g⁻¹) v-v) = ρ (g*b*g⁻¹) v-v
  have hh := congrArg (ρ g) (hA a ha b hb (ρ g⁻¹ v))
  simpa only [map_mul,Module.End.mul_apply,map_sub,ρ.inv_self_apply,ρ.self_inv_apply] using hh

/-- Compatible whole-vertex indices, Sylow placement, and quadratic lifting
on the entire original U-layer. -/
theorem Input.replacement_small_mover_quadratic_coordinates
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp E.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
              2 ^ fixedCodim (restrictScalars (k := ZMod 2)
                (symplecticNatural (k := E.Carrier) 2)) (A.map f)) ∧
        (∀ A : Subgroup (stabilizer d.radical a), A ≤ (Q d.radical t).subgroupOf (stabilizer d.radical a) →
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            movingIndex ((A.map f).subgroupOf unipotent)) ∧
        ∀ A : Subgroup (stabilizer d.radical a),
          IsQuadratic (restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)) (A.map f) →
          ⁅⁅(U d.radical a).subgroupOf (stabilizer d.radical a),A⁆,A⁆ = ⊥ := by
  obtain ⟨E,hE,f,hf,hfQ,hidx,hquad⟩ := inner_indices_quadratic h d geometry hb ha
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hpT : IsPGroup 2 (Q d.radical t) := hjR ▸ (h.replacement_two_group d).map j
  let T := (Q d.radical t).subgroupOf (stabilizer d.radical a)
  obtain ⟨S,hS⟩ := (hpT.comap_subtype.map f).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp E.Carrier) S
    (unipotentSylow (by rw [E.card_eq]) (by rw [hE]; exact h.nonbinary.le))
  have hSm : (S : Subgroup (Sp E.Carrier)).map (MulAut.conj g).toMonoidHom = unipotent :=
    congrArg (fun S : Sylow 2 (Sp E.Carrier) => (S : Subgroup (Sp E.Carrier))) hg
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hTf : T.map f' ≤ unipotent := by
    rw [←Subgroup.map_map]
    exact (map_mono hS).trans_eq hSm
  have hker : f'.ker = f.ker := by
    ext x
    change (MulAut.conj g) (f x) = 1 ↔ f x = 1
    exact (MulAut.conj g).map_eq_one_iff
  refine ⟨E,hE,f',(MulAut.conj g).surjective.comp hf,by rw [hker]; exact hfQ,hTf,?_,?_,?_⟩
  · intro A
    rw [←Subgroup.map_map,fixedCodim_map_conj]
    exact hidx A
  · intro A hAT
    have hAf : A.map f' ≤ unipotent := (map_mono hAT).trans hTf
    let τ := restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)
    have hi : (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) = 2 ^ fixedCodim τ (A.map f') := by
      rw [←Subgroup.map_map, fixedCodim_map_conj]
      exact hidx A
    rw [hi,←binary_movingIndex]
    congr 1
    have hcomp : restrictScalars (k := ZMod 2) (natural (F := E.Carrier)) =
        τ.comp (unipotent (F := E.Carrier)).subtype := rfl
    rw [hcomp]
    rw [fixedCodim,fixedCodim,fixedSpace_comp_map,map_subgroupOf_eq_of_le hAf]
  · intro A hq
    apply hquad A
    have hh := quadratic_conjugate _ hq g⁻¹
    have hm : (A.map f').map (MulAut.conj g⁻¹).toMonoidHom = A.map f := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [f',MulAut.conj_apply,mul_assoc]
    rwa [hm] at hh

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
