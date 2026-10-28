module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Commutators
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.GeometryReductions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.Cardinalities
/-!
# Original-line and starred-Sylow assembly

The original flag preimage has order q when C_V(L)=1. In the one-copy
case it therefore equals the entire V_H fixed space. In arbitrary multiplicity,
a field-line identification and reciprocal transvection orbit geometry combine
with the explicit vector-commutator calculation to construct the adjusted line
transporter. The existing counterexample line-normalizer theorem gives A=V,
and the actual starred Sylow image is transported using that equality.

The reciprocal transvection geometry, and in the doubled case the source
field-line identification, are explicit unproved premises. Thus these exports
are conditional assembly, not completed source 11.3.7(4).

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.3.7(4), printed p.773. Conjugation is left conjugation, hence x*g.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] {T : Sylow 2 G} {H : Subgroup G}
variable [Finite G] {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

open LocalGeometry

/-- The original quotient-line preimage has order q once its fixed kernel
vanishes. This is independent of the natural coordinates selected for V_H. -/
theorem source_flag_line_card
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (hline : U₁ = c.binarySubspace (f.space 0))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    Nat.card (D.centralQuotientPreimage U₁) = Nat.card S.field.Carrier := by
  have he : D.centralQuotientPreimage U₁ = c.preimage (f.space 0) := by
    rw [hline]; rfl
  rw [he,Closure.Nonabelian.card_preimage c hfixed,f.dimension]
  simp only [Fin.val_zero,zero_add,pow_one,S.field.card_eq]

/-- The original source line is the entire fixed space in the one-copy case.
This discharges field-line identification in that branch. -/
theorem source_one_copy_line
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (hline : U₁ = c.binarySubspace (f.space 0))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G)
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field 1)
    (hcontain : D.centralQuotientPreimage U₁ ≤
      omegaClosure T H ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    n.liftSpace n.fixedSpace = D.centralQuotientPreimage U₁ := by
  rw [← n.fixed_eq_liftSpace,← n.commutator_eq_fixed]
  exact (n.one_copy_line_eq_commutator hcontain
    (source_flag_line_card c f hline hfixed)).symm

/-- Assembly after the two remaining geometric calculations: the original line
is a field line in the fixed space, and reciprocal transvections identify every
nonzero vector displacement with an L₂-conjugate of the selected source line.
Neither of these premises is asserted to follow here from the source. -/
theorem source_seed_eq_of_commutator_line_geometry
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hcounter : ¬ Proposition1132At D S U₁ H)
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (g : G) {m : ℕ}
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field m)
    (U : Submodule S.field.Carrier (Fin m → Fin 2 → S.field.Carrier))
    (hU : Module.finrank S.field.Carrier U = 1) (hfix : U ≤ n.fixedSpace)
    (hline : n.liftSpace U = D.centralQuotientPreimage U₁)
    (hgeometry : ∀ w : omegaClosure T H,
      (w : G) ∉ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) →
      ∃ x ∈ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G),
        ⁅V.map (MulAut.conj g).toMonoidHom,zpowers (w : G)⁆ =
          (D.centralQuotientPreimage U₁).map (MulAut.conj (x * g)).toMonoidHom) :
    (∃ x ∈ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G),
      (D.centralQuotientPreimage U₁).map (MulAut.conj (x * g)).toMonoidHom =
        D.centralQuotientPreimage U₁) ∧ V.map (MulAut.conj g).toMonoidHom = V := by
  obtain ⟨w,hw,he⟩ := n.exists_vector_commutator U hU hfix
  obtain ⟨x,hx,hxline⟩ := hgeometry w hw
  have htransport := hxline.symm.trans (he.trans hline)
  exact ⟨⟨x,hx,htransport⟩,source_seed_eq_of_line_transporter s p hcounter halt
    g x hx htransport⟩

/-- The Sylow subgroup is the original starred image, transported only after
identifying the selected conjugate with V. -/
theorem source_seed_star_sylow_of_commutator_line_geometry
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hcounter : ¬ Proposition1132At D S U₁ H)
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (g : G) {m : ℕ}
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field m)
    (U : Submodule S.field.Carrier (Fin m → Fin 2 → S.field.Carrier))
    (hU : Module.finrank S.field.Carrier U = 1) (hfix : U ≤ n.fixedSpace)
    (hline : n.liftSpace U = D.centralQuotientPreimage U₁)
    (hgeometry : ∀ w : omegaClosure T H,
      (w : G) ∉ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) →
      ∃ x ∈ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G),
        ⁅V.map (MulAut.conj g).toMonoidHom,zpowers (w : G)⁆ =
          (D.centralQuotientPreimage U₁).map (MulAut.conj (x * g)).toMonoidHom)
    (P : Sylow 2 (residualStar T H))
    (hP : (P : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H)) :
    V.map (MulAut.conj g).toMonoidHom = V ∧
      (P : Subgroup (residualStar T H)).map (residualStar T H).subtype =
        (V.subgroupOf H).map (starProjection T H) := by
  have he := (source_seed_eq_of_commutator_line_geometry s p hcounter halt
    g n U hU hfix hline hgeometry).2
  exact ⟨he,by simpa only [he] using hP⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
