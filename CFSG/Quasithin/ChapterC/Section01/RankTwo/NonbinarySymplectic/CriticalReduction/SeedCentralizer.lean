module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.VertexAction
public import Theory.Representation.SymplecticNaturalNormalizer.FixedSeedInner

/-!
# The fixed seed centralizer lies over the symplectic component

The full vertex action is used here, including possible field automorphisms.
A two-subgroup of the component fixes a natural field line. Fixed lifting
through the actual cover and literal conjugation show that centralizing its
fixed seed fixes that line pointwise. The faithful ambient action then puts
the centralizer in the component preimage. No central complement is chosen.

This proves the inner-containment input to the star argument on the minimum
replacement. The star subgroup and its core cut still have to be constructed.
Source: MS93 (3.4) and Section 7, printed pp.868 and 933.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
private theorem seed_centralizer_from_ambient_cover
    {J : Type*} [Group J] [Finite J] (A T : Subgroup J) {n : ℕ}
    (hC : (A.map (QuotientGroup.mk' (pCore 2 J))).Normal)
    (hk : centralizer (omegaCenterIn (pCore 2 J) : Set J) = pCore 2 J)
    (hcent : centralizer (A.map (QuotientGroup.mk' (pCore 2 J)) : Set (J ⧸ pCore 2 J)) = ⊥)
    (hn : 1 < n) {a : Vertex T}
    (hambient :
    let C := A.map (QuotientGroup.mk' (pCore 2 J))
    letI : C.Normal := hC
    let ρ := NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 J)) (QuotientGroup.mk' (pCore 2 J))
      (QuotientGroup.mk'_surjective _)
      ((QuotientGroup.ker_mk' _).trans hk.symm)
    let s := MovedSection.ofNormal ρ C
    ∃ E : BinaryField, E.degree = n ∧
      ∃ e : ActionEquiv (s.action.comp C.subtype) (binaryNatural (K := E.Carrier)),
        IsCover (MovedSection.coverProjection s e) ∧
      ∃ j : Multiplicative s.space.toSubmodule →* FreeAmalgam T,
        Function.Injective j ∧ j.range = U T a ∧
      ∃ κ : stabilizer T a →* (J ⧸ pCore 2 J), Function.Surjective κ ∧
        κ.ker.map (stabilizer T a).subtype = Q T a ∧
        κ.ker.map (stabilizer T a).subtype = BinaryMS.MS93.C T a ∧
        ((Ltilde T a).subgroupOf (stabilizer T a)).map κ = C ∧
        Function.Injective (MovedSection.ambientAction s e) ∧
        (∀ g : J ⧸ pCore 2 J, ∃ σ : E.Carrier ≃+* E.Carrier, ∀ c v,
          MovedSection.ambientAction s e g (c • v) =
            σ c • MovedSection.ambientAction s e g v) ∧
        (∀ (g : stabilizer T a) (v : s.space.toSubmodule),
          j (Multiplicative.ofAdd (s.space.toRepresentation (κ g) v)) =
            (g : FreeAmalgam T) * j (Multiplicative.ofAdd v) * (g : FreeAmalgam T)⁻¹) ∧
        (∀ (g : stabilizer T a) (v : s.space.toSubmodule),
          MovedSection.coverProjection s e (s.space.toRepresentation (κ g) v) =
            MovedSection.ambientAction s e (κ g) (MovedSection.coverProjection s e v)) ∧
        (∀ v : s.space.toSubmodule, MovedSection.coverProjection s e v = 0 ↔
          j (Multiplicative.ofAdd v) ∈ centralizer (Ltilde T a : Set (FreeAmalgam T))))
    (P : Sylow 2 (Ltilde T a)) :
    stabilizer T a ⊓ centralizer
      (U T a ⊓ centralizer
        (((P : Subgroup (Ltilde T a)).map (Ltilde T a).subtype) :
          Set (FreeAmalgam T)) : Set (FreeAmalgam T)) ≤
      Ltilde T a ⊔ Q T a := by
  obtain ⟨E,hE,e,he,j,hj,hjU,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    hambient
  let C := A.map (QuotientGroup.mk' (pCore 2 J))
  let : C.Normal := hC
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 J)) (QuotientGroup.mk' (pCore 2 J))
    (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans hk.symm)) C
  let f₀ : Ltilde T a →* (J ⧸ pCore 2 J) :=
    κ.comp (inclusion (Ltilde_le_stabilizer a))
  have hf₀ : f₀.range = C := by
    rw [MonoidHom.range_comp,inclusion_range]
    exact hκL
  let f := e.groupEquiv.toMonoidHom.comp
    (f₀.codRestrict C (fun x => hf₀ ▸ ⟨x,rfl⟩))
  have hfmark (x : Ltilde T a) :
      (e.groupEquiv.symm (f x) : J ⧸ pCore 2 J) = f₀ x := by
    change (e.groupEquiv.symm (e.groupEquiv ⟨f₀ x,_⟩) : J ⧸ pCore 2 J) = f₀ x
    rw [e.groupEquiv.symm_apply_apply]
  let π := f.comp (P : Subgroup (Ltilde T a)).subtype
  have hcard : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact lt_of_lt_of_le (by decide : 2 < 2^2)
      (Nat.pow_le_pow_right (by decide) hn)
  let derivedEquiv : L (K := E.Carrier) ≃* Matrix.symplecticGroup (Fin 2) E.Carrier :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hcard)).trans
      Subgroup.topEquiv
  intro x hx
  let x' : stabilizer T a := ⟨x,hx.1⟩
  have hxC : κ x' ∈ C := by
    apply SymplecticNaturalNormalizer.mem_component_of_fixes_cover_seed C
      (hcent ▸ bot_le)
      hcard (e.groupEquiv.trans derivedEquiv) (MovedSection.ambientAction s e)
      (fun b w => MovedSection.ambientAction_component s e b w)
      (MovedSection.coverProjection s e) he π.range
      (P.isPGroup'.of_surjective π.rangeRestrict π.rangeRestrict_surjective)
      (κ x') (s.space.toRepresentation (κ x'))
      (fun w => MovedSection.coverProjection_ambient s e (κ x') w)
    intro w hw
    have hseed : j (Multiplicative.ofAdd w) ∈ U T a ⊓ centralizer
        (((P : Subgroup (Ltilde T a)).map (Ltilde T a).subtype) :
          Set (FreeAmalgam T)) := by
      refine ⟨hjU ▸ ⟨Multiplicative.ofAdd w,rfl⟩,?_⟩
      intro t ht
      obtain ⟨k,hk,rfl⟩ := ht
      have hfix := hw ⟨π ⟨k,hk⟩,⟨⟨k,hk⟩,rfl⟩⟩
      have hfix' : s.space.toRepresentation (f₀ k) w = w := by
        change s.space.toRepresentation (e.groupEquiv.symm (f k)) w = w at hfix
        rwa [hfmark] at hfix
      have heq := hconj (inclusion (Ltilde_le_stabilizer a) k) w
      change j (Multiplicative.ofAdd (s.space.toRepresentation (f₀ k) w)) =
        (k : FreeAmalgam T) * j (Multiplicative.ofAdd w) *
          (k : FreeAmalgam T)⁻¹ at heq
      rw [hfix'] at heq
      exact mul_inv_eq_iff_eq_mul.mp heq.symm
    apply Multiplicative.ofAdd.injective
    apply hj
    rw [hconj]
    change x * j (Multiplicative.ofAdd w) * x⁻¹ = _
    rw [← hx.2 _ hseed,mul_inv_cancel_right]
  have hpre : x' ∈ C.comap κ := hxC
  have hmap : (C.comap κ).map (stabilizer T a).subtype = Ltilde T a ⊔ Q T a := by
    dsimp only [C]
    rw [←hκL,comap_map_eq,Subgroup.map_sup,
      map_subgroupOf_eq_of_le (Ltilde_le_stabilizer a),hκQ]
  exact hmap ▸ mem_map_of_mem (stabilizer T a).subtype hpre

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

include h

/-- The centralizer of the actual component Sylow seed lies over the
component, even when the entire vertex quotient has outer automorphisms. -/
theorem Input.replacement_componentSylowSeed_centralizer_le
    {a : Vertex d.radical} (ha : color d.radical a = false)
    (P : Sylow 2 (Ltilde d.radical a)) :
    stabilizer d.radical a ⊓ centralizer
      (U d.radical a ⊓ centralizer
        (((P : Subgroup (Ltilde d.radical a)).map (Ltilde d.radical a).subtype) :
          Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤
      Ltilde d.radical a ⊔ Q d.radical a := by
  exact seed_centralizer_from_ambient_cover (K.subgroupOf d.overgroup) d.radical
    (h.replacement_component_image_structure d).2.1
    (h.replacement_centralOmega_centralizer d)
    (h.replacement_component_image_structure d).2.2.2.2 h.nonbinary
    (h.replacement_ambient_initial_cover_at_vertex d ha) P

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
