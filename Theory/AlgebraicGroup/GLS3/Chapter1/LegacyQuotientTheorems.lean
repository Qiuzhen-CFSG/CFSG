module

import Theory.AlgebraicGroup.QuotientData
public import Theory.AlgebraicGroup.Basic
public import Theory.AlgebraicGroup.Variety.Defs
public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Solvable
public import Theory.AlgebraicGroup.Connected
public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Theory.AlgebraicGroup.Tori.Basic
public import Theory.AlgebraicGroup.Unipotent.Basic
public import Theory.AlgebraicGroup.Unipotent.Radical
public import Theory.AlgebraicGroup.Radical.Defs
public import Theory.AlgebraicGroup.Reductive.Defs
public import Theory.AlgebraicGroup.Semisimple.Defs
public import Theory.AlgebraicGroup.Isomorphism
public import Theory.AlgebraicGroup.Morphism.ClosedImage

universe u

namespace Theory.AlgebraicGroup.LegacyQuotient

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public structure QuotientData
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) where
  quotient : Variety k
  quotientAlgebraicGroup : AlgebraicGroup quotient
  projection : @Morphism k _ G quotient
    (inferInstance : AlgebraicGroup G) quotientAlgebraicGroup
  surjective : Function.Surjective projection.onPoints
  kernel_eq : projection.kernel = H.toSubgroup
  factor : ∀ {I : Variety k} (_ : AlgebraicGroup I)
    (φ : AlgebraicGroup.Morphism G I), H.toSubgroup ≤ φ.kernel →
      ∃! ψ : AlgebraicGroup.Morphism quotient I, ψ.comp projection = φ

public theorem source_theorem_1_5_1_e
    {K : Variety k} [AlgebraicGroup K] (hK : Variety.IsConnected K)
    (hSolv : Group.IsSolvable (Variety.Point K)) :
    ∃ U : ClosedSubgroup K, IsUnipotentRadicalSubgroup U ∧
      ∀ T : ClosedSubgroup K, IsMaximalTorus T →
        ∃ q : Theory.AlgebraicGroup.LegacyQuotient.QuotientData U,
          letI : AlgebraicGroup q.quotient := q.quotientAlgebraicGroup
          ∃ e : @AlgebraicGroup.Iso k _ q.quotient T.carrierVariety
              q.quotientAlgebraicGroup T.carrierAlgebraicGroup,
            ∀ t : Variety.Point T.carrierVariety,
              e.hom.onPoints (q.projection.onPoints
                (T.inclusion.onPoints t)) = t := by
  obtain ⟨U, hU, hT⟩ := Theory.AlgebraicGroup.theorem_1_5_1_e hK hSolv
  refine ⟨U, hU, ?_⟩
  intro T hTmax
  obtain ⟨Q, hQ, π, hsurj, hker, hfactor, e, he⟩ := hT T hTmax
  let q : Theory.AlgebraicGroup.LegacyQuotient.QuotientData U :=
    { quotient := Q
      quotientAlgebraicGroup := hQ
      projection := π
      surjective := hsurj
      kernel_eq := hker
      factor := hfactor }
  refine ⟨q, ?_⟩
  exact ⟨e, he⟩

public theorem source_theorem_1_7_2_g
    {G : Variety k} [AlgebraicGroup G] (hG : Variety.IsConnected G) :
    ∃ Ru R : ClosedSubgroup G,
      IsRadicalSubgroup R ∧ IsUnipotentRadicalOf R Ru ∧
      ∃ qᵤ : Theory.AlgebraicGroup.LegacyQuotient.QuotientData Ru,
        ∃ qᵣ : Theory.AlgebraicGroup.LegacyQuotient.QuotientData R,
        @IsReductiveAlgebraicGroup k _ qᵤ.quotient qᵤ.quotientAlgebraicGroup ∧
        @IsSemisimpleAlgebraicGroup k _ qᵣ.quotient qᵣ.quotientAlgebraicGroup := by
  obtain ⟨Ru, R, hR, hRu, hU, hR'⟩ :=
    Theory.AlgebraicGroup.theorem_1_7_2_g hG
  obtain ⟨Qu, hQu, πu, hsurju, hkeru, hfactoru, hredu⟩ := hU
  obtain ⟨Qr, hQr, πr, hsurjr, hkerr, hfactorr, hsemir⟩ := hR'
  let qu : Theory.AlgebraicGroup.LegacyQuotient.QuotientData Ru :=
    { quotient := Qu
      quotientAlgebraicGroup := hQu
      projection := πu
      surjective := hsurju
      kernel_eq := hkeru
      factor := hfactoru }
  let qr : Theory.AlgebraicGroup.LegacyQuotient.QuotientData R :=
    { quotient := Qr
      quotientAlgebraicGroup := hQr
      projection := πr
      surjective := hsurjr
      kernel_eq := hkerr
      factor := hfactorr }
  exact ⟨Ru, R, hR, hRu, qu, qr, hredu, hsemir⟩

end Theory.AlgebraicGroup.LegacyQuotient
