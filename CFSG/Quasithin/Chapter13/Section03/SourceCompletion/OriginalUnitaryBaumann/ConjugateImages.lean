module
public import CFSG.Quasithin.ChapterB.Section02.Baumann.AutomorphicOffender
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.AutomizerImages
public import CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry.OffenderIntersections

/-!
# Root-eight images of moving Baumann-normalizer conjugates

Restrict the original natural action to the actual Baumann subgroup. A
normalizer conjugation is an automorphism of this subgroup, so the symmetric
no-strong-offender argument makes its moving module image an offender.
The unique point-radical offender theorem identifies that image with the
marked root eight. The existing single-displacement theorem then identifies
[V,V^x], V intersect V^x, and C_V(V^x) with the original three-space.
The literal Baumann centralizer has index eight in the same action marking.

The original contrary-case application is ConjugateGeometry. Source:
Aschbacher--Smith 13.3.10(2), printed p.888, using B.4.6(13) and B.1.4(6).
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag ChapterB.BaumannArgument
variable {G : Type*} [Group G] [Finite G]

private theorem unitary_automorphic_image
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ g v, E (Additive.ofMul (MulAut.conjNormal g v)) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (q g) (E (Additive.ofMul v)))
    (hp : q.range ≤ Atlas.G2.LieParabolicSetup.radical₂)
    (a : MulAut G) (hne : ¬ V.map a.toMonoidHom ≤ centralizer (V : Set G)) :
    (V.map a.toMonoidHom).map q = Atlas.G2.BinaryCore.elementary := by
  have hk := unitary_coordinate_kernel V q E he
  let qr := q.rangeRestrict
  have hkr := q.ker_rangeRestrict.trans hk
  let τ := NormalElementaryQuotient.representation V qr q.rangeRestrict_surjective hkr
  have hno := (unitary_no_strong_and_le_baumann V q E hk he ⊤ le_top).1
  have ho := automorphic_image_isOffender V hno qr q.rangeRestrict_surjective hkr a hne
  have he' (g : q.range) (v : Additive V) :
      E (τ g v) = Atlas.G2.Restricted.NaturalCoordinates.action F g.val (E v) := by
    obtain ⟨g,rfl⟩ := q.rangeRestrict_surjective g
    have hr := NormalElementaryQuotient.representation_apply V qr
      q.rangeRestrict_surjective hkr g v
    have hh : (τ (qr g) v).toMul = MulAut.conjNormal g v.toMul := Subtype.ext hr
    exact (congrArg (fun w : V => E (Additive.ofMul w)) hh).trans (he g v.toMul)
  have hm := ho.map_equivariant τ (Atlas.G2.Restricted.NaturalCoordinates.action F)
    q.range.subtype q.range.subtype_injective E he'
  rw [Subgroup.map_map] at hm
  exact Atlas.G2.Natural.BinaryPointOffenders.offender_eq_elementary _ hm
    ((map_le_range _ _).trans hp)

/-- Every moving conjugate under the normalizer of the original Baumann group
has exactly the root-eight image; no maximal-elementary or rank premise remains. -/
theorem unitary_baumann_moving_conjugate_image
    (V B : Subgroup G) [IsElementaryAbelian 2 V]
    (rho : Automizer V →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ a v, E (automizerRepresentation V a v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hVB : V ≤ B) (hBN : B ≤ normalizer (V : Set G))
    (hp : (inducedAutomizer V B).map rho ≤ Atlas.G2.LieParabolicSetup.radical₂)
    (x : G) (hx : x ∈ normalizer (B : Set G))
    (hne : ¬ V.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (V : Set G)) :
    (inducedAutomizer V (V.map (MulAut.conj x⁻¹).toMonoidHom)).map rho =
      Atlas.G2.BinaryCore.elementary := by
  let U := V.subgroupOf B
  let N := normalizer (V : Set G)
  let A := V.map (MulAut.conj x⁻¹).toMonoidHom
  let : U.Normal := normal_subgroupOf_of_le_normalizer hBN
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVB (p := 2)
  let EUa : Additive U ≃+ Additive V := (subgroupOfEquivOfLe hVB).toAdditive
  let EU : Additive U ≃ₗ[F] Additive V := { EUa with map_smul' := ZMod.map_smul EUa }
  let E' := EU.trans E
  let q : B →* Atlas.G2.Model F :=
    (rho.comp V.normalizerMonoidHom.rangeRestrict).comp (inclusion hBN)
  let a : MulAut B := B.normalizerMonoidHom ⟨x⁻¹,(normalizer (B : Set G)).inv_mem hx⟩
  have he' (b : B) (v : U) :
      E' (Additive.ofMul (MulAut.conjNormal b v)) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (q b) (E' (Additive.ofMul v)) :=
    he (V.normalizerMonoidHom.rangeRestrict (inclusion hBN b)) (EU (Additive.ofMul v))
  have hp' : q.range ≤ Atlas.G2.LieParabolicSetup.radical₂ := by
    rintro g ⟨b,rfl⟩
    apply hp
    exact ⟨_,⟨⟨b.val,hBN b.property⟩,b.property,rfl⟩,rfl⟩
  have hmap : (U.map a.toMonoidHom).map B.subtype = A := by
    have ha : B.subtype.comp a.toMonoidHom =
        (MulAut.conj x⁻¹).toMonoidHom.comp B.subtype := by
      ext b
      rfl
    rw [map_map,ha,←map_map,map_subgroupOf_eq_of_le hVB]
  have hne' : ¬ U.map a.toMonoidHom ≤ centralizer (U : Set B) := by
    intro hc
    have hm := map_mono (f := B.subtype) hc
    rw [hmap,map_centralizer_subtype,map_subgroupOf_eq_of_le hVB] at hm
    exact hne (hm.trans inf_le_right)
  have hi := unitary_automorphic_image U q E' he' hp' a hne'
  have hAB : A ≤ B := by
    rw [←hmap]
    exact map_subtype_le _
  have hm : (U.map a.toMonoidHom).map (inclusion hBN) = A.subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [map_map]
    change (U.map a.toMonoidHom).map B.subtype = _
    rw [hmap,map_subgroupOf_eq_of_le (hAB.trans hBN)]
  simpa only [q,←Subgroup.map_map,hm,inducedAutomizer] using hi
/-- The moving conjugate meets V in precisely its fixed three-space, which
is also the whole commutator. The original seed marking is retained. -/
theorem unitary_baumann_moving_conjugate_intersection
    (V B U : Subgroup G) [IsElementaryAbelian 2 V]
    (rho : Automizer V →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ a v, E (automizerRepresentation V a v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hVB : V ≤ B) (hBN : B ≤ normalizer (V : Set G))
    (hp : (inducedAutomizer V B).map rho ≤ Atlas.G2.LieParabolicSetup.radical₂)
    (hUV : U ≤ V) (hU : pointCoordinateSubspace E U = seed)
    (x : G) (hx : x ∈ normalizer (B : Set G))
    (hne : ¬ V.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (V : Set G)) :
    let A := V.map (MulAut.conj x⁻¹).toMonoidHom
    (inducedAutomizer V A).map rho = Atlas.G2.BinaryCore.elementary ∧
      V ⊓ centralizer (A : Set G) = U ∧ ⁅V,A⁆ = U ∧ V ⊓ A = U := by
  intro A
  let a := (MulAut.conj x⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map a
  have hBa : B.map a = B :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (B : Set G)).inv_mem hx)
  have hAB : A ≤ B := (map_mono hVB).trans_eq hBa
  have hAN := hAB.trans hBN
  have hBNA : B ≤ normalizer (A : Set G) := by
    have hm := (map_mono (f := a) hBN).trans (V.le_normalizer_map a)
    rwa [hBa] at hm
  have hcomm : ⁅V,A⁆ ≤ V ⊓ A := le_inf
    (le_normalizer_iff_commutator_le_left.mp hAN)
    (le_normalizer_iff_commutator_le_right.mp (hVB.trans hBNA))
  have hi := unitary_baumann_moving_conjugate_image V B rho E he hVB hBN hp x hx hne
  have hfix := unitary_centralizer_eq_marked_seed rho E he A U hAN hUV hU hi
  have ho : IsOffender (Atlas.G2.Restricted.NaturalCoordinates.action F)
      ((inducedAutomizer V A).map rho) := by
    rw [hi]
    refine ⟨⟨?_,inferInstance⟩,?_⟩
    · intro hz
      have hc := Atlas.G2.BinaryCore.card_elementary
      rw [hz,card_bot] at hc
      contradiction
    · rw [Atlas.G2.Natural.BinaryModelOffenders.elementary_eq]
      have hd : BinaryOffender.fixedCodim (Atlas.G2.Restricted.NaturalCoordinates.action F)
          (Atlas.G2.EvenTwoRank.elementary F) = 3 :=
        Atlas.G2.NaturalOffenders.fixedCodim_elementary (F := ZMod 2) (n := 1) (by norm_num)
      have hr : rank (Atlas.G2.EvenTwoRank.elementary F) = 3 :=
        Atlas.G2.NaturalOffenders.elementary_rank (F := ZMod 2) (n := 1) (by norm_num)
      exact hd.le.trans hr.ge
  have hm := UnitaryGeometry.commutator_eq_fixed_of_offender E rho he ho hcomm
  have hj := UnitaryGeometry.intersection_eq_commutator_of_offender E rho he ho hcomm
  exact ⟨hi,hfix,hm.trans hfix,hj.trans (hm.trans hfix)⟩
omit [Finite G] in
/-- The literal centralizer in the marked root-eight preimage has index eight. -/
theorem unitary_root_eight_centralizer_index
    (V B : Subgroup G) [IsElementaryAbelian 2 V]
    (rho : Automizer V →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ a v, E (automizerRepresentation V a v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hBN : B ≤ normalizer (V : Set G))
    (himage : (inducedAutomizer V B).map rho = Atlas.G2.BinaryCore.elementary) :
    (B ⊓ centralizer (V : Set G)).relIndex B = 8 := by
  have hf : Function.Injective rho := by
    intro a b hab
    apply automizerRepresentation_injective V
    apply LinearMap.ext
    intro v
    apply E.injective
    rw [he,he,hab]
  have hi : (centralizer (V : Set G)).relIndex B = Nat.card (inducedAutomizer V B) := by
    rw [inducedAutomizer,←relIndex_ker,MonoidHom.ker_rangeRestrict,
      normalizerMonoidHom_ker,relIndex_subgroupOf hBN]
  rw [inf_relIndex_left,hi,←card_map_of_injective hf,himage,
    Atlas.G2.BinaryCore.card_elementary]
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
