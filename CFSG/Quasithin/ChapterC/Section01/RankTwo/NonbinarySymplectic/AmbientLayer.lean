module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.GraphLayer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.AmbientAction
public import Theory.Representation.CentralCoverCoordinates
public import Theory.Representation.SymplecticNaturalNormalizer.FixedLineInner

/-!
# The full vertex action for a nonbinary symplectic MS-pair

The initial natural quotient carries the faithful action of the whole
ambient quotient, not just its component. Transport through the original
vertex coordinates retains the exact two-core kernel, the component image,
and both conjugation and projection formulas. A second transport puts the
cover on the additive group of the literal graph subgroup U.
The full ambient action is semilinear over the natural coefficient field.

All fields retain the degree of the original input. The central kernel of
the cover is retained; no splitting or field-four restriction is used.
Source: MS93 (3.2)(vi), pp.863--866, and the setup for (3.3), p.867.
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
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)

include h

/-- The natural quotient and its original projection are equivariant for
the entire vertex group. Its action is faithful modulo the actual Q = C(Z). -/
theorem Input.ambient_initial_cover_at_vertex
    {a : Vertex R} (ha : color R a = false) :
    let C := K.map (QuotientGroup.mk' (pCore 2 H))
    letI : C.Normal := h.component_image_structure.2.1
    let ρ := NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 H)) (QuotientGroup.mk' (pCore 2 H))
      (QuotientGroup.mk'_surjective _)
      ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)
    let s := MovedSection.ofNormal ρ C
    ∃ E : BinaryField, E.degree = n ∧
      ∃ e : ActionEquiv (s.action.comp C.subtype) (binaryNatural (K := E.Carrier)),
        IsCover (MovedSection.coverProjection s e) ∧
      ∃ j : Multiplicative s.space.toSubmodule →* FreeAmalgam R,
        Function.Injective j ∧ j.range = U R a ∧
      ∃ κ : stabilizer R a →* (H ⧸ pCore 2 H), Function.Surjective κ ∧
        κ.ker.map (stabilizer R a).subtype = Q R a ∧
        κ.ker.map (stabilizer R a).subtype = BinaryMS.MS93.C R a ∧
        ((Ltilde R a).subgroupOf (stabilizer R a)).map κ = C ∧
        Function.Injective (MovedSection.ambientAction s e) ∧
        (∀ g : H ⧸ pCore 2 H, ∃ σ : E.Carrier ≃+* E.Carrier, ∀ c v,
          MovedSection.ambientAction s e g (c • v) =
            σ c • MovedSection.ambientAction s e g v) ∧
        (∀ (g : stabilizer R a) (v : s.space.toSubmodule),
          j (Multiplicative.ofAdd (s.space.toRepresentation (κ g) v)) =
            (g : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (g : FreeAmalgam R)⁻¹) ∧
        (∀ (g : stabilizer R a) (v : s.space.toSubmodule),
          MovedSection.coverProjection s e (s.space.toRepresentation (κ g) v) =
            MovedSection.ambientAction s e (κ g) (MovedSection.coverProjection s e v)) ∧
        (∀ v : s.space.toSubmodule, MovedSection.coverProjection s e v = 0 ↔
          j (Multiplicative.ofAdd v) ∈ centralizer (Ltilde R a : Set (FreeAmalgam R))) := by
  dsimp only
  let C := K.map (QuotientGroup.mk' (pCore 2 H))
  let : C.Normal := h.component_image_structure.2.1
  let q := QuotientGroup.mk' (pCore 2 H)
  let hq := QuotientGroup.mk'_surjective (pCore 2 H)
  let hk := (QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) C
  obtain ⟨E,hE,e,he⟩ := h.centralOmega_initial_cover
  obtain ⟨i,hi,hir,hiK,hiU,hiQ⟩ :=
    Sp4Four.SourceComparison.vertex_coordinates_with_kernel R
      h.radical.isPGroup h.radical.twoCore_le ha
  rw [h.residual_eq] at hiK
  have hU : (⁅omegaOrbit R,K⁆).map i = U R a := by
    simpa only [Sp4Four.LocalPackage.initialLayer,h.residual_eq] using hiU
  let j := i.comp (ElementaryMovedCover.embedding (omegaCenterIn (pCore 2 H)) K q hq hk)
  let κ := ElementaryMovedCover.embeddedQuotient q i hi (stabilizer R a) hir
  have hkQ : κ.ker.map (stabilizer R a).subtype = Q R a := by
    rw [ElementaryMovedCover.embeddedQuotient_kernel,QuotientGroup.ker_mk']
    exact hiQ
  refine ⟨E,hE,e,he,j,hi.comp (ElementaryMovedCover.embedding_injective _ _ _ _ _),?_,
    κ,ElementaryMovedCover.embeddedQuotient_surjective q i hi _ hir hq,hkQ,?_,?_,
    MovedSection.ambientAction_faithful s e binaryNatural_injective
      h.component_image_structure.2.2.2.2,?_,?_,?_,?_⟩
  · dsimp only [j]
    rw [MonoidHom.range_comp,ElementaryMovedCover.embedding_range,←h.initialCore_eq]
    exact hU
  · exact hkQ.trans (MSCentralOrbit.C_eq_Q R h.radical.isPGroup
      h.radical.twoCore_le h.omegaOrbit_centralizer a ha).symm
  · rw [←hiK]
    exact ElementaryMovedCover.embeddedQuotient_subgroup q i hi _ hir K
  · have hcard : 2 < Nat.card E.Carrier := by
      rw [E.card_eq,hE]
      exact lt_of_lt_of_le (by decide : 2 < 2^2)
        (Nat.pow_le_pow_right (by decide) h.nonbinary)
    let d : commutator (Matrix.symplecticGroup (Fin 2) E.Carrier) ≃*
        Matrix.symplecticGroup (Fin 2) E.Carrier :=
      (MulEquiv.subgroupCongr
        (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hcard)).trans
        Subgroup.topEquiv
    intro g
    exact SymplecticNaturalNormalizer.exists_field_twist
      ⟨linearAction (MovedSection.ambientAction s e) g,
        SymplecticNaturalNormalizer.operator_mem_naturalNormalizer C hcard
          (e.groupEquiv.trans d) (MovedSection.ambientAction s e)
          (fun b v => MovedSection.ambientAction_component s e b v) g⟩
  · exact ElementaryMovedCover.embedded_ambient_conjugate _ _ _ _ _ i hi _ hir
  · intro g v
    exact MovedSection.coverProjection_ambient s e (κ g) v
  · obtain ⟨f,hf,hact,hker⟩ := ElementaryMovedCover.exists_conjugationActor
      (omegaCenterIn (pCore 2 H)) K q hq hk i hi (Ltilde R a) hiK e
    exact hker

/-- The literal moving subgroup is elementary; this is derived from the
positive critical geometry of the input rather than supplied to its cover. -/
theorem Input.vertex_moving_elementary {a : Vertex R} (ha : color R a = false) :
    IsElementaryAbelian 2 (U R a) := by
  obtain ⟨g,hpos,_⟩ := h.positive_even_geometry
  let : IsElementaryAbelian 2 (X R a) := omegaCenter_elementary (Q R a)
  let : IsElementaryAbelian 2 (Z R a) := IsElementaryAbelian.of_le
    (g.omega_bound a ha (by rwa [g.distance_constant a ha]))
  exact IsElementaryAbelian.of_le (DistanceEight.U_le_Z R a)

/-- The initial cover realized on the literal moving subgroup, with its
actual residual actor and fixed kernel, for every nonbinary degree. -/
theorem Input.initial_subgroup_cover_at_vertex
    {a : Vertex R} (ha : color R a = false) :
    letI := h.vertex_moving_elementary ha
    ∃ E : BinaryField, E.degree = n ∧
      ∃ σ : Representation (ZMod 2)
          (commutator (Matrix.symplecticGroup (Fin 2) E.Carrier)) (Additive (U R a)),
      ∃ p : σ.IntertwiningMap (binaryNatural (K := E.Carrier)), IsCover p ∧
      ∃ f : Ltilde R a →* commutator (Matrix.symplecticGroup (Fin 2) E.Carrier),
        Function.Surjective f ∧
        (∀ (k : Ltilde R a) (u : U R a),
          ((σ (f k) (Additive.ofMul u)).toMul : FreeAmalgam R) =
            (k : FreeAmalgam R) * u * (k : FreeAmalgam R)⁻¹) ∧
        p.toLinearMap.ker.toAddSubgroup.toSubgroup'.map (U R a).subtype =
          U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) := by
  let := h.vertex_moving_elementary ha
  obtain ⟨E,hE,e,he,j,hj,hjU,f,hf,hact,hker⟩ := h.initial_cover_at_vertex ha
  obtain ⟨σ,p,hp,hact',hker'⟩ := exists_subgroup_cover _ _ _ he
    (U R a) (Ltilde R a) j hj hjU f hact hker
  exact ⟨E,hE,σ,p,hp,f,hf,hact',hker'⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
