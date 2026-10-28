module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NaturalLayer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.AmbientLayer

/-!
# Full vertex action on the characteristic replacement graph

The replacement's natural cover is realized on the literal moving subgroup U
at every original-group vertex of its own holomorph graph. The whole vertex
group acts with kernel Q = C(Z), and its faithful natural quotient action is
semilinear over a field of the original degree. Both the fixed central kernel
and the exact equivariance of the cover projection are retained.

The transport uses the replacement's proved two-group, core containment,
residual and omega-orbit faithfulness. It requires no replacement odd-index
witness or field-four restriction.
Source: MS93 (3.2)(vi), pp.863--866, applied after Section 7, pp.932--933.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open SymplecticConjugatePair.Ambient
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
private theorem initial_cover_from_layer
    {J : Type*} [Group J] [Finite J] (A T : Subgroup J) {n : ℕ}
    (hC : (A.map (QuotientGroup.mk' (pCore 2 J))).Normal)
    (hk : centralizer (omegaCenterIn (pCore 2 J) : Set J) = pCore 2 J)
    (hres : pResidual 2 J = A)
    (hinit : ⁅omegaOrbit T,A⁆ = ⁅omegaCenterIn (pCore 2 J),A⁆)
    (hcover :
      let C := A.map (QuotientGroup.mk' (pCore 2 J))
      letI : C.Normal := hC
      let ρ := NormalElementaryQuotient.representation
        (omegaCenterIn (pCore 2 J)) (QuotientGroup.mk' (pCore 2 J))
        (QuotientGroup.mk'_surjective _)
        ((QuotientGroup.ker_mk' _).trans hk.symm)
      let s := MovedSection.ofNormal ρ C
      ∃ E : BinaryField, E.degree = n ∧
        ∃ e : ActionEquiv (s.action.comp C.subtype) (binaryNatural (K := E.Carrier)),
          IsCover (MovedSection.coverProjection s e))
    {a : Vertex T} (ha : color T a = false) :
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
          ∃ f : Ltilde T a →* commutator (Matrix.symplecticGroup (Fin 2) E.Carrier),
            Function.Surjective f ∧
            (∀ (k : Ltilde T a) (v : s.space.toSubmodule),
              j (Multiplicative.ofAdd (MovedSection.coverAction s e (f k) v)) =
                (k:FreeAmalgam T) * j (Multiplicative.ofAdd v) * (k:FreeAmalgam T)⁻¹) ∧
            (∀ v : s.space.toSubmodule, MovedSection.coverProjection s e v = 0 ↔
              j (Multiplicative.ofAdd v) ∈ centralizer (Ltilde T a : Set (FreeAmalgam T))) := by
  dsimp only
  let C := A.map (QuotientGroup.mk' (pCore 2 J))
  let : C.Normal := hC
  let q := QuotientGroup.mk' (pCore 2 J)
  let hq := QuotientGroup.mk'_surjective (pCore 2 J)
  let hk := (QuotientGroup.ker_mk' _).trans hk.symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 J)) q hq hk) C
  obtain ⟨E,hE,e,he⟩ := hcover
  obtain ⟨i,hi,_,hiL,hiU⟩ := Sp4Four.LocalPackage.vertex_coordinates T ha
  rw [hres] at hiL
  have hU : (⁅omegaOrbit T,A⁆).map i = U T a := by
    simpa only [Sp4Four.LocalPackage.initialLayer,hres] using hiU
  let j := i.comp (ElementaryMovedCover.embedding (omegaCenterIn (pCore 2 J)) A q hq hk)
  refine ⟨E,hE,e,he,j,hi.comp (ElementaryMovedCover.embedding_injective _ _ _ _ _),?_,?_⟩
  · dsimp only [j]
    rw [MonoidHom.range_comp,ElementaryMovedCover.embedding_range,←hinit]
    exact hU
  · exact ElementaryMovedCover.exists_conjugationActor (omegaCenterIn (pCore 2 J))
      A q hq hk i hi (Ltilde T a) hiL e

private theorem ambient_cover_from_layer
    {J : Type*} [Group J] [Finite J] (A T : Subgroup J) {n : ℕ}
    (hC : (A.map (QuotientGroup.mk' (pCore 2 J))).Normal)
    (hk : centralizer (omegaCenterIn (pCore 2 J) : Set J) = pCore 2 J)
    (hres : pResidual 2 J = A)
    (hinit : ⁅omegaOrbit T,A⁆ = ⁅omegaCenterIn (pCore 2 J),A⁆)
    (hp : IsPGroup 2 T) (hQR : pCore 2 J ≤ T)
    (hfaith : centralizer (omegaOrbit T : Set J) = pCore 2 J)
    (hcent : centralizer (A.map (QuotientGroup.mk' (pCore 2 J)) : Set (J ⧸ pCore 2 J)) = ⊥)
    (hn : 1 < n)
    (hcover :
      let C := A.map (QuotientGroup.mk' (pCore 2 J))
      letI : C.Normal := hC
      let ρ := NormalElementaryQuotient.representation
        (omegaCenterIn (pCore 2 J)) (QuotientGroup.mk' (pCore 2 J))
        (QuotientGroup.mk'_surjective _)
        ((QuotientGroup.ker_mk' _).trans hk.symm)
      let s := MovedSection.ofNormal ρ C
      ∃ E : BinaryField, E.degree = n ∧
        ∃ e : ActionEquiv (s.action.comp C.subtype) (binaryNatural (K := E.Carrier)),
          IsCover (MovedSection.coverProjection s e))
    {a : Vertex T} (ha : color T a = false) :
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
          j (Multiplicative.ofAdd v) ∈ centralizer (Ltilde T a : Set (FreeAmalgam T))) := by
  dsimp only
  let C := A.map (QuotientGroup.mk' (pCore 2 J))
  let : C.Normal := hC
  let q := QuotientGroup.mk' (pCore 2 J)
  let hq := QuotientGroup.mk'_surjective (pCore 2 J)
  let hk := (QuotientGroup.ker_mk' _).trans hk.symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 J)) q hq hk) C
  obtain ⟨E,hE,e,he⟩ := hcover
  obtain ⟨i,hi,hir,hiK,hiU,hiQ⟩ :=
    Sp4Four.SourceComparison.vertex_coordinates_with_kernel T
      hp hQR ha
  rw [hres] at hiK
  have hU : (⁅omegaOrbit T,A⁆).map i = U T a := by
    simpa only [Sp4Four.LocalPackage.initialLayer,hres] using hiU
  let j := i.comp (ElementaryMovedCover.embedding (omegaCenterIn (pCore 2 J)) A q hq hk)
  let κ := ElementaryMovedCover.embeddedQuotient q i hi (stabilizer T a) hir
  have hkQ : κ.ker.map (stabilizer T a).subtype = Q T a := by
    rw [ElementaryMovedCover.embeddedQuotient_kernel,QuotientGroup.ker_mk']
    exact hiQ
  refine ⟨E,hE,e,he,j,hi.comp (ElementaryMovedCover.embedding_injective _ _ _ _ _),?_,
    κ,ElementaryMovedCover.embeddedQuotient_surjective q i hi _ hir hq,hkQ,?_,?_,
    MovedSection.ambientAction_faithful s e binaryNatural_injective
      hcent,?_,?_,?_,?_⟩
  · dsimp only [j]
    rw [MonoidHom.range_comp,ElementaryMovedCover.embedding_range,←hinit]
    exact hU
  · exact hkQ.trans (MSCentralOrbit.C_eq_Q T hp
      hQR hfaith a ha).symm
  · rw [←hiK]
    exact ElementaryMovedCover.embeddedQuotient_subgroup q i hi _ hir A
  · have hcard : 2 < Nat.card E.Carrier := by
      rw [E.card_eq,hE]
      exact lt_of_lt_of_le (by decide : 2 < 2^2)
        (Nat.pow_le_pow_right (by decide) hn)
    let derivedEquiv : commutator (Matrix.symplecticGroup (Fin 2) E.Carrier) ≃*
        Matrix.symplecticGroup (Fin 2) E.Carrier :=
      (MulEquiv.subgroupCongr
        (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hcard)).trans
        Subgroup.topEquiv
    intro g
    exact SymplecticNaturalNormalizer.exists_field_twist
      ⟨linearAction (MovedSection.ambientAction s e) g,
        SymplecticNaturalNormalizer.operator_mem_naturalNormalizer C hcard
          (e.groupEquiv.trans derivedEquiv) (MovedSection.ambientAction s e)
          (fun b v => MovedSection.ambientAction_component s e b v) g⟩
  · exact ElementaryMovedCover.embedded_ambient_conjugate _ _ _ _ _ i hi _ hir
  · intro g v
    exact MovedSection.coverProjection_ambient s e (κ g) v
  · obtain ⟨f,hf,hact,hker⟩ := ElementaryMovedCover.exists_conjugationActor
      (omegaCenterIn (pCore 2 J)) A q hq hk i hi (Ltilde T a) hiK e
    exact hker

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

include h

theorem Input.replacement_initial_cover_at_vertex
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    let C := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
    letI : C.Normal := (h.replacement_component_image_structure d).2.1
    let ρ := NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 d.overgroup)) (QuotientGroup.mk' (pCore 2 d.overgroup))
      (QuotientGroup.mk'_surjective _)
      ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)
    let s := MovedSection.ofNormal ρ C
    ∃ E : BinaryField, E.degree = n ∧
      ∃ e : ActionEquiv (s.action.comp C.subtype) (binaryNatural (K := E.Carrier)),
        IsCover (MovedSection.coverProjection s e) ∧
        ∃ j : Multiplicative s.space.toSubmodule →* FreeAmalgam d.radical,
          Function.Injective j ∧ j.range = U d.radical a ∧
          ∃ f : Ltilde d.radical a →* commutator (Matrix.symplecticGroup (Fin 2) E.Carrier),
            Function.Surjective f ∧
            (∀ (k : Ltilde d.radical a) (v : s.space.toSubmodule),
              j (Multiplicative.ofAdd (MovedSection.coverAction s e (f k) v)) =
                (k:FreeAmalgam d.radical) * j (Multiplicative.ofAdd v) * (k:FreeAmalgam d.radical)⁻¹) ∧
            (∀ v : s.space.toSubmodule, MovedSection.coverProjection s e v = 0 ↔
              j (Multiplicative.ofAdd v) ∈ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) := by
  exact initial_cover_from_layer (K.subgroupOf d.overgroup) d.radical
    (h.replacement_component_image_structure d).2.1
    (h.replacement_centralOmega_centralizer d) (h.replacement_residual d)
    (h.replacement_initialCore_eq d) (h.replacement_centralOmega_initial_cover d) ha

theorem Input.replacement_ambient_initial_cover_at_vertex
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    let C := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
    letI : C.Normal := (h.replacement_component_image_structure d).2.1
    let ρ := NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 d.overgroup)) (QuotientGroup.mk' (pCore 2 d.overgroup))
      (QuotientGroup.mk'_surjective _)
      ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)
    let s := MovedSection.ofNormal ρ C
    ∃ E : BinaryField, E.degree = n ∧
      ∃ e : ActionEquiv (s.action.comp C.subtype) (binaryNatural (K := E.Carrier)),
        IsCover (MovedSection.coverProjection s e) ∧
      ∃ j : Multiplicative s.space.toSubmodule →* FreeAmalgam d.radical,
        Function.Injective j ∧ j.range = U d.radical a ∧
      ∃ κ : stabilizer d.radical a →* (d.overgroup ⧸ pCore 2 d.overgroup), Function.Surjective κ ∧
        κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        κ.ker.map (stabilizer d.radical a).subtype = BinaryMS.MS93.C d.radical a ∧
        ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ = C ∧
        Function.Injective (MovedSection.ambientAction s e) ∧
        (∀ g : d.overgroup ⧸ pCore 2 d.overgroup, ∃ σ : E.Carrier ≃+* E.Carrier, ∀ c v,
          MovedSection.ambientAction s e g (c • v) =
            σ c • MovedSection.ambientAction s e g v) ∧
        (∀ (g : stabilizer d.radical a) (v : s.space.toSubmodule),
          j (Multiplicative.ofAdd (s.space.toRepresentation (κ g) v)) =
            (g : FreeAmalgam d.radical) * j (Multiplicative.ofAdd v) * (g : FreeAmalgam d.radical)⁻¹) ∧
        (∀ (g : stabilizer d.radical a) (v : s.space.toSubmodule),
          MovedSection.coverProjection s e (s.space.toRepresentation (κ g) v) =
            MovedSection.ambientAction s e (κ g) (MovedSection.coverProjection s e v)) ∧
        (∀ v : s.space.toSubmodule, MovedSection.coverProjection s e v = 0 ↔
          j (Multiplicative.ofAdd v) ∈ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) := by
  exact ambient_cover_from_layer (K.subgroupOf d.overgroup) d.radical
    (h.replacement_component_image_structure d).2.1
    (h.replacement_centralOmega_centralizer d) (h.replacement_residual d)
    (h.replacement_initialCore_eq d) (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
    (h.replacement_component_image_structure d).2.2.2.2 h.nonbinary
    (h.replacement_centralOmega_initial_cover d) ha

/-- The literal moving subgroup is elementary; this is derived from the
positive critical geometry of the input rather than supplied to its cover. -/
theorem Input.replacement_vertex_moving_elementary {a : Vertex d.radical} (ha : color d.radical a = false) :
    IsElementaryAbelian 2 (U d.radical a) := by
  obtain ⟨g,hpos,_⟩ := (h.replacement_positive_even_geometry d)
  let : IsElementaryAbelian 2 (X d.radical a) := omegaCenter_elementary (Q d.radical a)
  let : IsElementaryAbelian 2 (Z d.radical a) := IsElementaryAbelian.of_le
    (g.omega_bound a ha (by rwa [g.distance_constant a ha]))
  exact IsElementaryAbelian.of_le (DistanceEight.U_le_Z d.radical a)

/-- The initial cover realized on the literal moving subgroup, with its
actual residual actor and fixed kernel, for every nonbinary degree. -/
theorem Input.replacement_initial_subgroup_cover_at_vertex
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    letI := (h.replacement_vertex_moving_elementary d) ha
    ∃ E : BinaryField, E.degree = n ∧
      ∃ σ : Representation (ZMod 2)
          (commutator (Matrix.symplecticGroup (Fin 2) E.Carrier)) (Additive (U d.radical a)),
      ∃ p : σ.IntertwiningMap (binaryNatural (K := E.Carrier)), IsCover p ∧
      ∃ f : Ltilde d.radical a →* commutator (Matrix.symplecticGroup (Fin 2) E.Carrier),
        Function.Surjective f ∧
        (∀ (k : Ltilde d.radical a) (u : U d.radical a),
          ((σ (f k) (Additive.ofMul u)).toMul : FreeAmalgam d.radical) =
            (k : FreeAmalgam d.radical) * u * (k : FreeAmalgam d.radical)⁻¹) ∧
        p.toLinearMap.ker.toAddSubgroup.toSubgroup'.map (U d.radical a).subtype =
          U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
  let := (h.replacement_vertex_moving_elementary d) ha
  obtain ⟨E,hE,e,he,j,hj,hjU,f,hf,hact,hker⟩ := (h.replacement_initial_cover_at_vertex d) ha
  obtain ⟨σ,p,hp,hact',hker'⟩ := exists_subgroup_cover _ _ _ he
    (U d.radical a) (Ltilde d.radical a) j hj hjU f hact hker
  exact ⟨E,hE,σ,p,hp,f,hf,hact',hker'⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
