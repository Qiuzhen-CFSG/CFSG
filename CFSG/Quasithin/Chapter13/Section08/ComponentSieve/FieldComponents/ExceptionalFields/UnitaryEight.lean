module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.UnitaryEight.Borel
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.RepresentationTheory.Basic
/-!
# Excluding the two unitary-eight cases in 13.8.20

The source seed is the image of V₃ in the literal quotient U_H/V₁, where
U_H is its H-conjugate span. `SeedSetup` keeps the actual conjugation action,
the Borel image in K*, B = O²(B₀), the binary rank-two and B-invariance
conditions, and Ṽ₃ = [Ṽ₃,L₁]. The earlier containment deduction supplies
L₁ ≤ K, H = KT and U_H = [U_H,K]. Normality is relative to H or U_H.

The precise combined F.9.18(7)/B.4.5 input identifies this representation
with the restriction to F₂ of the natural SU₃(8) matrix module over F₆₄.
The module has dimension six over the Hermitian fixed field F₈ and eighteen
over F₂, as proved in `BinarySeed`. The coordinates intertwine the actual
K* action, so the F₈ scalar structure also transports to the source module.
A dimension equality alone is never used to identify representations.

The seed maps to a four-element subset of the natural module. Images of
finite-group two-residuals are two-residuals; hence that subset is invariant
under the residual of an actual SU₃ Sylow normalizer. Its conjugate torus
of order nine gives the intrinsic contradiction. The proof works for every
binary plane, so the retained seed commutator identity is not needed after
the natural-module identification.

The initial PSU₃ alternative remains a genuine projective matrix-group
isomorphism. The earlier classification must produce the SU₃ actor and
intertwining coordinates even in that branch. We never make the cover's
natural action descend to PSU₃.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.20,
printed p.955 (PDF p.972), paragraph beginning “We next observe”. This is a
conditional exceptional-case deduction, not a proof of F.9.18 or B.4.5.
-/

@[expose] public section
open Matrix BenderSuzuki.MatrixGroups Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.UnitaryEight
variable {G : Type*} [Group G]

/-- The actual map K → K* inside H/O₂(H). -/
def componentProjection (H K : Subgroup G) (hKH : K ≤ H) : K →* Source.starImage H K where
  toFun k := ⟨QuotientGroup.mk' (pCore 2 H) ⟨k.val, hKH k.property⟩,
    ⟨⟨k.val, hKH k.property⟩, k.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul (QuotientGroup.mk' (pCore 2 H))
    (⟨a.val, hKH a.property⟩ : H) (⟨b.val, hKH b.property⟩ : H))

variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The additive form of the actual source quotient. -/
abbrev SourceSpace := Additive (Source.Utilde H V₃ V₁)

/-- The literal image of V₃ in U_H/V₁ as a binary subspace. -/
def seedSpace : Submodule (ZMod 2) (SourceSpace H V₃ V₁) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup
    ((V₃.subgroupOf (Source.UH H V₃)).map
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)))))

/-- Conjugation on the actual H-conjugate span of V₃. -/
def conjugateSource (h : H) (u : Source.UH H V₃) : Source.UH H V₃ :=
  ⟨h.val * u.val * h.val⁻¹,
    le_normalizer_iff.mp (le_normalizer_conjugateSpanBy V₃ H) h.val h.property
      u.val u.property⟩

/-- The standing source data at the unitary exclusion, after L₁ ≤ K.
The Borel is specified by its exact image as a Sylow normalizer in K*. -/
structure SeedSetup (K L₁ T B₀ B : Subgroup G) where
  component_le : K ≤ H
  component_normal : (K.subgroupOf H).Normal
  generated : H = K ⊔ T
  line_le : V₁ ≤ Source.UH H V₃
  seed_le : V₃ ≤ H
  L₁_le : L₁ ≤ K
  U_commutator : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆
  borel_le : B₀ ≤ K
  residual_eq : B = (pResidual 2 B₀).map B₀.subtype
  sylow : Sylow 2 (Source.starImage H K)
  borel_image : ((componentProjection H K component_le).comp (inclusion borel_le)).range =
    normalizer (sylow : Set (Source.starImage H K))
  representation : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁)
  conjugation : ∀ (h : H) (u : Source.UH H V₃),
    representation (QuotientGroup.mk' (pCore 2 H) h)
      (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)) =
    Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
      (conjugateSource H V₃ h u))
  invariant : ∀ b ∈ Source.starImage H B, ∀ v ∈ seedSpace H V₃ V₁,
    representation b v ∈ seedSpace H V₃ V₁
  seed_commutator : seedSpace H V₃ V₁ = Submodule.span (ZMod 2)
    {v | ∃ l ∈ Source.starImage H L₁, ∃ w ∈ seedSpace H V₃ V₁,
      v = representation l w - w}
  seed_rank : Module.finrank (ZMod 2) (seedSpace H V₃ V₁) = 2

variable {E : Type*} [Field E] [Algebra (ZMod 2) E]

/-- An actual group isomorphism and equivariant linear coordinates with
the binary restriction of the natural special unitary module. -/
structure NaturalIdentification (K : Subgroup G) (J : HermitianForm 3 E)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁)) where
  actor : Source.starImage H K ≃* J.specialSubgroup
  coordinates : SourceSpace H V₃ V₁ ≃ₗ[ZMod 2] (Fin 3 → E)
  equivariant : ∀ k : Source.starImage H K, ∀ v,
    coordinates (ρ k.val v) = (actor k).val.val *ᵥ coordinates v

private theorem map_residual_range {A C : Type*} [Group A] [Group C] [Finite A]
    (f : A →* C) : (pResidual 2 A).map f =
      (pResidual 2 f.range).map f.range.subtype := by
  have hf : f = f.range.subtype.comp f.rangeRestrict := rfl
  conv_lhs => rw [hf]
  rw [← Subgroup.map_map, map_pResidual_of_surjective 2 _ f.rangeRestrict_surjective]

variable [Finite G] [Finite E]

/-- The actual rank-two source seed contradicts the natural SU₃(8) module
identification. All Borel coordinates and residual transport are proved. -/
theorem natural_seed_contradiction (K L₁ T B₀ B : Subgroup G)
    (d : SeedSetup H V₃ V₁ K L₁ T B₀ B)
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1; 0,1,0; 1,0,0])
    (hcard : Nat.card E = 64) (hfixed : Nat.card {x : E // J.conj x = x} = 8)
    (n : NaturalIdentification H V₃ V₁ K J d.representation) : False := by
  let f₀ := (componentProjection H K d.component_le).comp (inclusion d.borel_le)
  let f := n.actor.toMonoidHom.comp f₀
  let P := d.sylow.mapSurjective (f := n.actor.toMonoidHom) n.actor.surjective
  have hrange : f.range = normalizer (P : Set J.specialSubgroup) := by
    rw [MonoidHom.range_comp, d.borel_image]
    exact map_equiv_normalizer_eq (d.sylow : Subgroup (Source.starImage H K)) n.actor
  have hr : (pResidual 2 B₀).map f =
      (pResidual 2 (normalizer (P : Set J.specialSubgroup))).map
        (normalizer (P : Set J.specialSubgroup)).subtype := by
    rw [map_residual_range, hrange]
  let W := (seedSpace H V₃ V₁).map n.coordinates.toLinearMap
  have hwcard : Nat.card W = 4 := by
    rw [← Nat.card_congr (Submodule.equivMapOfInjective n.coordinates.toLinearMap
      n.coordinates.injective (seedSpace H V₃ V₁)).toEquiv,
      Module.natCard_eq_pow_finrank (K := ZMod 2), d.seed_rank, Nat.card_zmod]
    norm_num
  apply no_four_set_sylow_borel J hJ hcard hfixed P (W : Set (Fin 3 → E)) hwcard
  intro r v hv
  obtain ⟨b, hb, hbr⟩ := show r.val ∈ (pResidual 2 B₀).map f by
    rw [hr]
    exact r.property
  obtain ⟨w, hw, rfl⟩ := hv
  have hbB : b.val ∈ B := by
    rw [d.residual_eq]
    exact ⟨b, hb, rfl⟩
  have hqB : (f₀ b).val ∈ Source.starImage H B := by
    exact ⟨⟨b.val, d.component_le (d.borel_le b.property)⟩, hbB, rfl⟩
  refine ⟨d.representation (f₀ b).val w, d.invariant _ hqB w hw, ?_⟩
  change n.coordinates (d.representation (f₀ b).val w) = r.val.val.val *ᵥ n.coordinates w
  rw [n.equivariant]
  exact congrArg (fun a : J.specialSubgroup => a.val.val *ᵥ n.coordinates w) hbr
/-- The combined earlier F.9.18(7)/B.4.5 input identifies the actual
representation with the natural SU₃(8) representation. Its premise records
both genuine matrix-group alternatives; its conclusion has an actual SU
actor isomorphism and intertwining coordinates. -/
def EarlierUnitaryClassification (K L₁ T B₀ B : Subgroup G)
    (d : SeedSetup H V₃ V₁ K L₁ T B₀ B) (J : HermitianForm 3 E) : Prop :=
  (Nonempty (Source.starImage H K ≃* J.specialSubgroup) ∨
    Nonempty (Source.starImage H K ≃* ProjectiveSpecialUnitaryMatrixGroup J)) →
      Nonempty (NaturalIdentification H V₃ V₁ K J d.representation)

/-- Both unitary-eight alternatives are impossible under the precise earlier
representation classification. In the projective branch the SU identification
comes from that classification; no natural action of PSU₃(8) is postulated. -/
theorem unitary_cases_excluded (K L₁ T B₀ B : Subgroup G)
    (d : SeedSetup H V₃ V₁ K L₁ T B₀ B)
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1; 0,1,0; 1,0,0])
    (hcard : Nat.card E = 64) (hfixed : Nat.card {x : E // J.conj x = x} = 8)
    (classification : EarlierUnitaryClassification H V₃ V₁ K L₁ T B₀ B d J) :
    (¬ Nonempty (Source.starImage H K ≃* J.specialSubgroup)) ∧
    (¬ Nonempty (Source.starImage H K ≃* ProjectiveSpecialUnitaryMatrixGroup J)) := by
  have exclude (h : Nonempty (Source.starImage H K ≃* J.specialSubgroup) ∨
      Nonempty (Source.starImage H K ≃* ProjectiveSpecialUnitaryMatrixGroup J)) : False := by
    obtain ⟨n⟩ := classification h
    exact natural_seed_contradiction H V₃ V₁ K L₁ T B₀ B d J hJ hcard hfixed n
  exact ⟨fun h => exclude (Or.inl h), fun h => exclude (Or.inr h)⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.UnitaryEight
