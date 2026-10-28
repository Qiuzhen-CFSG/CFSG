module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SecondStar

/-!
# The literal inner vertex action on the minimum replacement

The two star bounds imply that the component fills the whole ambient core
quotient whenever the critical distance is at least four. Composing that
quotient map with the natural-cover marking gives a surjection from each
original-group vertex stabilizer to Sp₄ at the original field degree.
Its kernel is exactly Q, and its action on the actual U-layer agrees with
the natural action modulo the full residual-centralizer kernel.

This supplies the whole vertex action required by MS93 (5.0), printed p.912,
after the characteristic reduction of Section 7, printed pp.932--933.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation.SymplecticFourOrthogonalCover
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The whole stabilizer has the inner symplectic quotient and the literal natural
cover, including its full fixed kernel, at the original nonbinary degree. -/
theorem Input.replacement_inner_natural_action
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp E.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
      ∃ π : U d.radical a →* Multiplicative (Vector E.Carrier), Function.Surjective π ∧
        (∀ u : U d.radical a, π u = 1 ↔
          (u : FreeAmalgam d.radical) ∈ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) ∧
        (∀ (v : stabilizer d.radical a) (u : U d.radical a),
          π ⟨v.val*u.val*v.val⁻¹,
            (mem_normalizer_iff.mp (U_normalized a v.property) u.val).mp u.property⟩ =
            Multiplicative.ofAdd (f v • (π u).toAdd)) := by
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
  have hElarge : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let derivedEquiv : L (K := E.Carrier) ≃* Sp E.Carrier :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hElarge)).trans
      Subgroup.topEquiv
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let f := derivedEquiv.toMonoidHom.comp (e.groupEquiv.toMonoidHom.comp κC)
  have hκC : Function.Surjective κC := by
    intro x
    obtain ⟨g,hg⟩ := hκ x
    exact ⟨g,Subtype.ext hg⟩
  have hf : Function.Surjective f :=
    derivedEquiv.surjective.comp (e.groupEquiv.surjective.comp hκC)
  have hfker : f.ker = κ.ker := by
    ext x
    change derivedEquiv (e.groupEquiv (κC x))=1 ↔ κ x=1
    rw [derivedEquiv.map_eq_one_iff,e.groupEquiv.map_eq_one_iff]
    exact Subtype.ext_iff
  obtain ⟨π,hπ,hπj,hπact⟩ := exists_equivariant_embedded_projection
    (U d.radical a) (stabilizer d.radical a) (U_normalized a)
    s.space.toRepresentation (MovedSection.ambientAction s e) j hj hjr
    (MovedSection.coverProjection s e).toLinearMap he.1
    (MovedSection.coverProjection_ambient s e) κ hconj
  refine ⟨E,hE,f,hf,by rw [hfker]; exact hκQ,π,hπ,?_,?_⟩
  · intro u
    obtain ⟨w,hw⟩ := (show u.val ∈ j.range from hjr.symm ▸ u.property)
    have hu : (⟨j (Multiplicative.ofAdd w.toAdd),by rw [←hjr]; exact ⟨_,rfl⟩⟩ : U d.radical a) = u :=
      Subtype.ext hw
    have hh := hπj w.toAdd
    rw [hu] at hh
    rw [hh]
    change MovedSection.coverProjection s e w.toAdd = 0 ↔ _
    rw [hker]
    exact hw ▸ Iff.rfl
  · intro v u
    rw [hπact]
    exact congrArg Multiplicative.ofAdd (MovedSection.ambientAction_component s e (κC v) (π u).toAdd)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
