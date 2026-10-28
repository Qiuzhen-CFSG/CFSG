module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.MarkedLine.ScalarClosure
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Source

/-!
# The original doubled-case line and its vector commutator

This assembly keeps the original flag preimage and the selected conjugate
A=V^g. Sylow conjugacy supplies compatible coordinates, the Cartan scalar
span supplies field closure, and the original flag cardinality supplies
dimension one. The vector-commutator theorem then constructs u in V_H
outside C_{V_H}(A) with [A,⟨u⟩]=V₁.

The scalar-span input for the literal D₀ remains explicit. In particular,
this conditional assembly does not discharge source 11.3.7(4); the Hall
spectrum and finite-field spanning arguments must supply that input.
Source: Aschbacher--Smith, 11.3.7(4), doubled case, printed p.773.
-/

@[expose] public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {H L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The original line in a supplied compatible marking; the only new
mathematical premise is additive spanning by the actual Cartan scalars. -/
theorem source_marked_line_of_cartan_span
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (hline : U₁ = c.binarySubspace (f.space 0))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G)
    (cK : NaturalQuotientMarking T H S.field) (b : SL(2,S.field.Carrier))
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom)
      S.field cK.multiplicity)
    (he : ∀ (v : omegaClosure T H) (i : Fin cK.multiplicity),
      (n.coordinates v).toAdd i = ((cK.changeBasis b).coordinates v).toAdd i)
    (D_H : Subgroup G)
    (hcontain : D.centralQuotientPreimage U₁ ≤
      omegaClosure T H ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hcomm : D.centralQuotientPreimage U₁ = ⁅D.centralQuotientPreimage U₁,oddCartanPart D_H⁆)
    (hspan : AddSubgroup.closure (cartanScalarSet cK b (oddCartanPart D_H)) = ⊤) :
    ∃ E : Submodule S.field.Carrier (Fin cK.multiplicity → Fin 2 → S.field.Carrier),
      Module.finrank S.field.Carrier E = 1 ∧ E ≤ n.fixedSpace ∧
      n.liftSpace E = D.centralQuotientPreimage U₁ ∧
      ∃ u : omegaClosure T H,
        (u : G) ∉ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) ∧
        ⁅V.map (MulAut.conj g).toMonoidHom,zpowers (u : G)⁆ = D.centralQuotientPreimage U₁ := by
  obtain ⟨E,hE,hfix,hEU⟩ := cK.fieldLine_of_cartan_span b n he
    (D.centralQuotientPreimage U₁) (oddCartanPart D_H) hcontain hcomm
    (source_flag_line_card c f hline hfixed) hspan
  obtain ⟨u,hu,huE⟩ := n.exists_vector_commutator E hE hfix
  exact ⟨E,hE,hfix,hEU,u,hu,huE.trans hEU⟩

omit [Finite G] in
private theorem reindex_line {A : Subgroup G} {F : BinaryField} {m r : ℕ}
    (hm : m = r) (n : NaturalSylowCoordinates T H A F m)
    (E : Submodule F.Carrier (Fin m → Fin 2 → F.Carrier))
    (hE : Module.finrank F.Carrier E = 1) (hfix : E ≤ n.fixedSpace)
    (U : Subgroup G) (hEU : n.liftSpace E = U)
    (ρ : outsideResidual H → SL(2,F.Carrier))
    (he : ∀ (k : outsideResidual H) (v : omegaClosure T H) (i : Fin m),
      (n.coordinates (residualAction T H k v)).toAdd i =
        (ρ k).val *ᵥ (n.coordinates v).toAdd i) :
    ∃ (n' : NaturalSylowCoordinates T H A F r)
      (E' : Submodule F.Carrier (Fin r → Fin 2 → F.Carrier)),
      Module.finrank F.Carrier E' = 1 ∧ E' ≤ n'.fixedSpace ∧ n'.liftSpace E' = U ∧
      ∀ (k : outsideResidual H) (v : omegaClosure T H) (i : Fin r),
        (n'.coordinates (residualAction T H k v)).toAdd i =
          (ρ k).val *ᵥ (n'.coordinates v).toAdd i := by
  subst r
  exact ⟨n,E,hE,hfix,hEU,he⟩

/-- Construct both the marking and the original field line in the doubled
source configuration, conditionally on the actual Hall scalar-span input.
The result retains the full K-intertwiner after the simultaneous basis change. -/
theorem source_doubled_marked_line_of_torus_spectrum
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (_hSL : ∃ e, c = Coordinates.sl3 e)
    (hline : U₁ = c.binarySubspace (f.space 0))
    (s : Hypothesis1131At D S U₁ H) (_hcounter : ¬ Proposition1132At D S U₁ H)
    (g : G) (cK : NaturalQuotientMarking T H S.field) (hm : cK.multiplicity = 2)
    (hfixedL : V ⊓ centralizer (L : Set G) = ⊥)
    (hfixedK : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    [IsSimpleGroup (outsideResidual H ⧸ pCore 2 (outsideResidual H))]
    (hAH : V.map (MulAut.conj g).toMonoidHom ≤ H)
    (P : Sylow 2 (residualStar T H))
    (hP : (P : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H))
    (D_H X : Subgroup G)
    (_hDH : D_H ≤ H ⊓ normalizer (L : Set G))
    (_hHall : IsHallSubgroup OddHall.oddPrimes
      (D_H.subgroupOf (H ⊓ normalizer (L : Set G))))
    (_hDKL : oddCartanPart D_H ≤ outsideResidual H ⊓ L)
    (_hX : IsCartan T L X) (_hDX : oddCartanPart D_H ≤ X)
    (hcontain : D.centralQuotientPreimage U₁ ≤
      omegaClosure T H ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hcomm : D.centralQuotientPreimage U₁ = ⁅D.centralQuotientPreimage U₁,oddCartanPart D_H⁆)
    (hfield : AddSubgroup.closure (torusScalarSet S.field) = ⊤)
    (hspectrum : ∀ b : SL(2,S.field.Carrier),
      (∀ k : outsideResidual H, (k : G) ∈ oddCartanPart D_H →
        (b * cK.quotientEquiv (QuotientGroup.mk' _ k) * b⁻¹).val 1 0 = 0) →
      torusScalarSet S.field ⊆ cartanScalarSet cK b (oddCartanPart D_H)) :
    ∃ (b : SL(2,S.field.Carrier))
      (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field 2)
      (E : Submodule S.field.Carrier (Fin 2 → Fin 2 → S.field.Carrier)),
      Module.finrank S.field.Carrier E = 1 ∧ E ≤ n.fixedSpace ∧
      n.liftSpace E = D.centralQuotientPreimage U₁ ∧
      (∀ (k : outsideResidual H) (v : omegaClosure T H) (i : Fin 2),
        (n.coordinates (residualAction T H k v)).toAdd i =
          (b * cK.quotientEquiv (QuotientGroup.mk' _ k) * b⁻¹).val *ᵥ
            (n.coordinates v).toAdd i) ∧
      ∃ u : omegaClosure T H,
        (u : G) ∉ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) ∧
        ⁅V.map (MulAut.conj g).toMonoidHom,zpowers (u : G)⁆ = D.centralQuotientPreimage U₁ := by
  obtain ⟨b,n,he⟩ := cK.compatibleSylowCoordinates hfixedK s.outside.1.1.2
    s.moves_omega_center hAH P hP
  have hne : D.centralQuotientPreimage U₁ ≠ ⊥ := by
    intro hz
    have hc := source_flag_line_card c f hline hfixedL
    rw [hz,Subgroup.card_bot] at hc
    have := Finite.one_lt_card (α := S.field.Carrier)
    omega
  have htri := cK.cartan_lowerLeft_eq_zero b n he (D.centralQuotientPreimage U₁)
    (oddCartanPart D_H) hcontain hne hcomm
  have hspan : AddSubgroup.closure (cartanScalarSet cK b (oddCartanPart D_H)) = ⊤ := by
    apply top_unique
    rw [← hfield]
    exact AddSubgroup.closure_mono (hspectrum b htri)
  obtain ⟨E,hE,hfix,hEU,u,hu,huU⟩ := source_marked_line_of_cartan_span c f hline
    hfixedL g cK b n he D_H hcontain hcomm hspan
  obtain ⟨n',E',hE',hfix',hEU',he'⟩ := reindex_line hm n E hE hfix
    (D.centralQuotientPreimage U₁) hEU
    (fun k => b * cK.quotientEquiv (QuotientGroup.mk' _ k) * b⁻¹)
    (cK.compatibleSylow_intertwines b n he)
  exact ⟨b,n',E',hE',hfix',hEU',he',u,hu,huU⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
