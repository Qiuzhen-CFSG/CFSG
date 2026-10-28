module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalCoordinates
public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore

/-!
# Fixed-space and conjugate-identification reductions in 11.3.7

Once the Cartan computation gives C_Z(L) = C_Z(K), that common subgroup
centralizes both LT and H. Nonsolvable uniqueness makes it trivial. Every
nontrivial T-invariant two-subgroup meets Ω₁Z(T), so C_V(L) and C_{V_H}(K)
then vanish as well. The original H outside N_G(L) is retained.

The second reduction identifies V with its actual selected conjugate when
the transvection calculation supplies a transporter of the original line,
possibly adjusted inside the conjugate's normalizer. The product x*g is
forced by the convention v ↦ g*v*g⁻¹.

The natural-summand marking, torus lift and comparison, and adjusted line
transporter are explicit remaining mathematical premises. This module does
not assert that 11.3.7 has been completed.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.3.7(3--4), printed p.773.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Matrix
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)

omit [Finite G] in
theorem omegaCenter_eq : omegaCenter T = omegaCenterIn (T : Subgroup G) :=
  (omegaCenterIn_eq_omegaOneAmbient _).symm

omit [Finite G] in
theorem omegaCenter_elementary : IsElementaryAbelian 2 (omegaCenter T) := by
  rw [omegaCenter_eq]
  infer_instance

theorem subgroup_eq_bot_of_central_omega_disjoint (Q : Subgroup G)
    (hQT : Q ≤ (T : Subgroup G)) (hn : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hd : Q ⊓ omegaCenter T = ⊥) : Q = ⊥ := by
  by_contra hQ
  apply inf_omegaCenterIn_ne_bot_of_normalized_twoGroup Q (T : Subgroup G)
    hQT T.isPGroup' hn hQ
  rwa [← omegaCenter_eq]

include D S in
theorem omega_fixed_eq_bot_of_common_fixed
    (hTH : (T : Subgroup G) ≤ H) (hout : ¬ H ≤ normalizer (L : Set G))
    (hcommon : omegaCenter T ⊓ centralizer (L : Set G) =
      omegaCenter T ⊓ centralizer (outsideResidual H : Set G)) :
    omegaCenter T ⊓ centralizer (L : Set G) = ⊥ := by
  let E := omegaCenter T ⊓ centralizer (L : Set G)
  by_contra hE
  let := omegaCenter_elementary (T := T)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le (show E ≤ omegaCenter T from inf_le_left)
  have hEC : E ≤ centralizer ((L ⊔ (T : Subgroup G) : Subgroup G) : Set G) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      (le_centralizer_iff.mp (inf_le_left.trans (omegaCenter_le_sylow_centralizer T)))
  have hLT : L ⊔ (T : Subgroup G) ≤ normalizer (E : Set G) :=
    (le_centralizer_iff.mp hEC).trans (Subgroup.centralizer_le_normalizer _)
  have hEH : E ≤ centralizer (H : Set G) := by
    apply le_centralizer_iff.mpr
    rw [← outsideResidual_sup_sylow T H hTH]
    apply sup_le
    · apply le_centralizer_iff.mp
      change omegaCenter T ⊓ centralizer (L : Set G) ≤ _
      rw [hcommon]
      exact inf_le_right
    · exact (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right).trans
        (le_centralizer_iff.mp hEC)
  have hlocal : IsTwoLocal (normalizer (E : Set G)) :=
    ⟨E,hE,IsElementaryAbelian.isPGroup 2 E,rfl⟩
  obtain ⟨M,hNM,hM⟩ := Finite.exists_le_maximal hlocal
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    S.source.simpleQTKE T S.source.maximal_faithful.1
  have hML : M = normalizer (L : Set G) := by
    simpa only [D.localOrbit_eq] using hu.normalizer_unique M hM (hLT.trans hNM)
  apply hout
  exact (le_centralizer_iff.mp hEH).trans
    ((Subgroup.centralizer_le_normalizer _).trans (hML ▸ hNM))

include D S in
theorem seed_fixed_eq_bot_of_omega_fixed
    (hz : omegaCenter T ⊓ centralizer (L : Set G) = ⊥) :
    V ⊓ centralizer (L : Set G) = ⊥ := by
  apply subgroup_eq_bot_of_central_omega_disjoint (T := T) (V ⊓ centralizer (L : Set G))
    (inf_le_left.trans D.le_sylow)
  · exact (le_inf S.sylow_normalizes
      (D.sylow_normalizes_component.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  · apply bot_unique
    apply le_trans _ hz.le
    exact le_inf inf_le_right (inf_le_left.trans inf_le_right)

theorem closure_fixed_eq_bot_of_omega_fixed
    (hWT : omegaClosure T H ≤ (T : Subgroup G))
    (hTH : (T : Subgroup G) ≤ H)
    (hz : omegaCenter T ⊓ centralizer (outsideResidual H : Set G) = ⊥) :
    omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥ := by
  apply subgroup_eq_bot_of_central_omega_disjoint (T := T)
    (omegaClosure T H ⊓ centralizer (outsideResidual H : Set G))
    (inf_le_left.trans hWT)
  · apply (le_inf (hTH.trans (omegaClosure_normalized T H))
      ((hTH.trans (outsideResidual_normalized H)).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  · apply bot_unique
    exact (le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans hz.le

variable {D S} {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

theorem source_fixed_spaces_of_common_omega
    (s : Hypothesis1131At D S U₁ H)
    (hWT : omegaClosure T H ≤ (T : Subgroup G))
    (hcommon : omegaCenter T ⊓ centralizer (L : Set G) =
      omegaCenter T ⊓ centralizer (outsideResidual H : Set G)) :
    omegaCenter T ⊓ centralizer (L : Set G) = ⊥ ∧
      V ⊓ centralizer (L : Set G) = ⊥ ∧
      omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥ := by
  have hz := omega_fixed_eq_bot_of_common_fixed D S s.outside.1.1.2 s.outside.1.2 hcommon
  exact ⟨hz,seed_fixed_eq_bot_of_omega_fixed D S hz,
    closure_fixed_eq_bot_of_omega_fixed hWT s.outside.1.1.2 (hcommon.symm.trans hz)⟩


omit [Finite G] in
/-- The line normalizer identifies the actual conjugate, even after an adjustment
inside its own normalizer. Conjugation here is x ↦ g*x*g⁻¹. -/
theorem conjugate_eq_of_adjusted_line (U V : Subgroup G)
    (hn : normalizer (U : Set G) ≤ normalizer (V : Set G)) (g x : G)
    (hx : x ∈ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hu : U.map (MulAut.conj (x * g)).toMonoidHom = U) :
    V.map (MulAut.conj g).toMonoidHom = V := by
  have hxg : V.map (MulAut.conj (x * g)).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (hn (mem_normalizer_iff_map_conj_eq.mpr hu))
  have hcomp : (MulAut.conj x).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (x * g)).toMonoidHom := by
    ext v
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      _root_.mul_inv_rev]
    group
  have he : (V.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      V.map (MulAut.conj g).toMonoidHom := mem_normalizer_iff_map_conj_eq.mp hx
  rw [Subgroup.map_map, hcomp, hxg] at he
  exact he.symm

/-- The endpoint of both transvection cases on the original source line.
The transvection analysis must construct the displayed adjusted transporter. -/
theorem source_seed_eq_of_line_transporter
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hcounter : ¬ Proposition1132At D S U₁ H)
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (g x : G)
    (hx : x ∈ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hline : (D.centralQuotientPreimage U₁).map (MulAut.conj (x * g)).toMonoidHom =
      D.centralQuotientPreimage U₁) :
    V.map (MulAut.conj g).toMonoidHom = V :=
  conjugate_eq_of_adjusted_line _ _
    (line_normalizer_le_of_counterexample s p hcounter halt) g x hx hline


/-- The original fixed-space conclusion from the marked torus calculation and
its remaining comparison on the L-side. Both inputs have concrete source
producers; this theorem is not the completed 11.3.7(3). -/
theorem source_fixed_spaces_of_diagonal
    (s : Hypothesis1131At D S U₁ H)
    (hWT : omegaClosure T H ≤ (T : Subgroup G))
    (c : NaturalQuotientMarking T H S.field) (D_H : Subgroup G)
    (hDH : D_H ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (D_H.subgroupOf (H ⊓ normalizer (L : Set G))))
    (d : outsideResidual H) (hd : (d : G) ∈ oddCartanPart D_H)
    (a : S.field.Carrier) (ha : a ≠ 1)
    (hdiag : (c.quotientEquiv (QuotientGroup.mk' _ d)).val = !![a,0;0,a⁻¹])
    (hcompare : omegaCenter T ⊓ centralizer (oddCartanPart D_H : Set G) =
      omegaCenter T ⊓ centralizer (L : Set G)) :
    omegaCenter T ⊓ centralizer (L : Set G) = ⊥ ∧
      V ⊓ centralizer (L : Set G) = ⊥ ∧
      omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥ :=
  source_fixed_spaces_of_common_omega s hWT
    (hcompare.symm.trans (source_oddCartan_omega_fixed c D_H
      (oddCartanPart_le_residual_of_hall _ D_H hDH hHall) d hd a ha hdiag))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
