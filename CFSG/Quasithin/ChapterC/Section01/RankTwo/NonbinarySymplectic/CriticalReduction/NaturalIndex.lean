module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.InnerAction
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedIndex
public import Theory.Representation.BinaryOffender.EmbeddedFixedIndex

/-!
# Exact natural indices on the replacement's full moving layer

Outer removal identifies the entire vertex quotient with the symplectic
component. The original central cover, rather than a split quotient,
computes the centralizer index of every subgroup on U. The full central
kernel and the original field degree are retained.

This supplies the literal small-mover inequality in MS93 (5.0)--(5.4),
printed pp.912--915, for the replacement used in Section 7.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation.SymplecticFourOrthogonalCover
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A single marking of the whole vertex quotient computes every exact
centralizer index on the original U, including its entire fixed kernel. -/
theorem Input.replacement_inner_natural_indices
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp E.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)) (A.map f) := by
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
  refine ⟨E,hE,f,hf,by rw [hfker]; exact hκQ,?_⟩
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
  intro A
  let σ := MovedSection.coverAction s e
  have hi := embedded_centralizer_index σ U₀ A jS hjS hjSr (fD.comp A.subtype) (by
    intro x w
    apply Subtype.ext
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x.val))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x.val w)
  rw [fixedCodim_of_binaryCover (MovedSection.coverProjection s e) he] at hi
  rw [MonoidHom.range_comp,range_subtype] at hi
  rw [hi]
  congr 1
  let τ := restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)
  have hσ : binaryNatural (K := E.Carrier) = τ.comp ed.toMonoidHom := rfl
  rw [hσ,fixedCodim,fixedSpace_comp_map,Subgroup.map_map]
  rfl

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
