module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.SourceGeneration.ModuleAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.Preparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ChiefObstruction.PointCommutator
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.Centralization
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.Commutator.ConjugateGeneration
/-!
# Central generation in the proof of 14.7.72

The two applications of 14.7.13 use its actual commutator spans. The
intersection with U then follows from irreducibility of U/(VU₀) and the
nonabelianness forced by V ≤ S' = R. The proved centralizer step of 14.7.71
and p-perfect commutator idempotence give [R,L₁]=V. Normal generation by
L₁ propagates the commutator bound to L.

The earlier 14.7.13 implications and natural-section irreducibility
remain explicit. Point-residual normal generation is proved using 12.8.5(2). No intermediate
conclusion of 14.7.72 is included among these source inputs.
Source: Aschbacher–Smith, 14.7.13 and 14.7.72, printed pp.1046,1075–1076.
-/
public section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.SourceGeneration
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- Exact earlier 14.7.13(3),(4), with the original two commutator spans.
Its producer must supply the ambient hypotheses of that earlier lemma;
this interface is not asserted for arbitrary invariant flags. -/
structure EarlierThirteen (c : CriticalPath (L := L) F) : Prop where
  central : c.b = 3 → ⁅⁅F.U, Q T L⁆, c.Uα⁆ = ⊥ →
    conjugateSpanBy ⁅F.U, Q T L⁆ L ≤ (center (S F L)).map (S F L).subtype
  frattini_derived : c.b = 3 →
    (frattini (S F L)).map (S F L).subtype = conjugateSpanBy ⁅F.U, c.Uα⁆ L ∧
      ⁅S F L, S F L⁆ = conjugateSpanBy ⁅F.U, c.Uα⁆ L

omit [Finite G] in
private theorem center_image_le_centralizer (A : Subgroup G) :
    (center A).map A.subtype ≤ centralizer (A : Set G) := by
  rintro _ ⟨z, hz, rfl⟩ a ha
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨a, ha⟩)

/-- Both spans in 14.7.13 equal the original R. In the second equality,
the point containment from the proof of 14.7.70 supplies all of V. -/
theorem central_and_derived (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c)
    (h13 : EarlierThirteen c) (hE : ⁅F.U, Q T L⁆ = V ⊔ d.U₀)
    (hpoint : F.Vi 1 ≤ ⁅F.U, c.Uα⁆) :
    R d ≤ (center (S F L)).map (S F L).subtype ∧
      (frattini (S F L)).map (S F L).subtype = R d ∧ ⁅S F L, S F L⁆ = R d := by
  have hER : conjugateSpanBy ⁅F.U, Q T L⁆ L = R d := by
    rw [hE]
    exact le_antisymm
      (conjugateSpanBy_le (sup_le (V_le_R d) (U₀_le_R d)) (L_normalizes_R d))
      (conjugateSpanBy_mono le_sup_right le_rfl)
  have hEα : ⁅F.U, Q T L⁆ ≤ c.Uα := by
    rw [hE, sup_comm, ← e.intersection]
    exact inf_le_right
  have hUU : ⁅F.U, F.U⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff_isMulCommutative.mpr d.abelian)
  have hαα : ⁅c.Uα, c.Uα⁆ = ⊥ := by
    change ⁅F.U.map (MulAut.conj c.conjugator⁻¹).toMonoidHom,
      F.U.map (MulAut.conj c.conjugator⁻¹).toMonoidHom⁆ = ⊥
    rw [← map_commutator, hUU, Subgroup.map_bot]
  have hEcomm : ⁅⁅F.U, Q T L⁆, c.Uα⁆ = ⊥ :=
    bot_unique ((commutator_mono hEα le_rfl).trans hαα.le)
  have hcentral := h13.central e.distance hEcomm
  rw [hER] at hcentral
  let B := conjugateSpanBy ⁅F.U, c.Uα⁆ L
  have hVB : V ≤ B := (point_span d).symm.le.trans (conjugateSpanBy_mono hpoint le_rfl)
  have hAB : ⁅F.U, c.Uα⁆ ≤ B := le_conjugateSpanBy _ _
  have hEB : d.U₀ ⊔ V ≤ B := by
    rw [← e.intersection, e.commutator_seed]
    exact sup_le hAB hVB
  have hAR : ⁅F.U, c.Uα⁆ ≤ R d :=
    (le_sup_left.trans e.commutator_seed.symm.le).trans
      (e.intersection.le.trans (sup_le (U₀_le_R d) (V_le_R d)))
  have hBR : B = R d := le_antisymm (conjugateSpanBy_le hAR (L_normalizes_R d))
    (conjugateSpanBy_le (le_sup_left.trans hEB) (le_normalizer_conjugateSpanBy _ _))
  have hh := h13.frattini_derived e.distance
  exact ⟨hcentral, hh.1.trans hBR, hh.2.trans hBR⟩

/-- 14.7.13(1), specialized to the original U, Q and U₀-span. -/
theorem commutator_S_Q (hSQ : S F L ≤ Q T L) (hE : ⁅F.U, Q T L⁆ = V ⊔ d.U₀) :
    ⁅S F L, Q T L⁆ = R d := by
  have hLQ : L ≤ normalizer (Q T L : Set G) :=
    le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have he := commutator_iSup_conjugates F.U L (Q T L) (U_le_S.trans hSQ) hLQ
  rw [← conjugateSpanBy_eq_iSup_conj, ← conjugateSpanBy_eq_iSup_conj] at he
  change ⁅S F L, Q T L⁆ = conjugateSpanBy ⁅F.U, Q T L⁆ L at he
  rw [he, hE]
  exact le_antisymm
    (conjugateSpanBy_le (sup_le (V_le_R d) (U₀_le_R d)) (L_normalizes_R d))
    (conjugateSpanBy_mono le_sup_right le_rfl)

/-- Irreducibility is stated on the literal invariant subgroup interval
[VU₀,U], hence concerns the original section U/(VU₀). -/
@[expose] def SectionIrreducible : Prop := ∀ A : Subgroup G,
  V ⊔ d.U₀ ≤ A → A ≤ F.U → F.Li L 1 ≤ normalizer (A : Set G) →
    A = V ⊔ d.U₀ ∨ A = F.U

/-- The case U ≤ R would make S abelian, contradicting its derived
subgroup containing the nontrivial original natural seed. -/
theorem fixed_span_intersection (hcentral : R d ≤ (center (S F L)).map (S F L).subtype)
    (hderived : ⁅S F L, S F L⁆ = R d) (hirr : SectionIrreducible d) :
    R d ⊓ F.U = V ⊔ d.U₀ := by
  have hn : ¬ F.U ≤ R d := by
    intro hUR
    have hSR : S F L ≤ R d := conjugateSpanBy_le hUR (L_normalizes_R d)
    have hbot : ⁅S F L, S F L⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr
        ((hSR.trans hcentral).trans (center_image_le_centralizer _))
    exact d.natural.chosen.ne_bot (bot_unique ((V_le_R d).trans (hderived.symm.trans hbot).le))
  have hL₁U : F.Li L 1 ≤ normalizer (F.U : Set G) :=
    ((F.Li_le L 1).trans inf_le_right).trans d.conjugationSection.normalized
  have hL₁R : F.Li L 1 ≤ normalizer (R d : Set G) :=
    ((F.Li_le L 1).trans inf_le_left).trans (L_normalizes_R d)
  have hnorm : F.Li L 1 ≤ normalizer (R d ⊓ F.U : Subgroup G) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_inf _ _ _ (MulAut.conj x).injective,
      mem_normalizer_iff_map_conj_eq.mp (hL₁R hx),
      mem_normalizer_iff_map_conj_eq.mp (hL₁U hx)]
  rcases hirr (R d ⊓ F.U)
    (le_inf (sup_le (V_le_R d) (U₀_le_R d)) (sup_le (Data.V_le_U F) d.U₀_le_U))
    inf_le_right hnorm with he | he
  · exact he
  · exact (hn (he.symm.le.trans inf_le_left)).elim

/-- The original point residual acts onto V and centralizes U₀. -/
theorem join_commutator_point : ⁅V ⊔ d.U₀, F.Li L 1⁆ = V := by
  have hfix : ⁅d.U₀, F.Li L 1⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (ChiefFactors.L₁_le_K.trans d.K_centralizes_U₀))
  have hUV : F.U ≤ normalizer (V : Set G) :=
    ((le_centralizer_iff_isMulCommutative.mpr d.abelian).trans
      (centralizer_le (Data.V_le_U F))).trans (Subgroup.centralizer_le_normalizer _)
  have hpre : V ⊔ d.U₀ ≤ commutatorPreimage F.U (F.Li L 1) V :=
    sup_le (le_commutatorPreimage (Data.V_le_U F) d.seed_eq_commutator_point_residual.symm.le)
      (le_commutatorPreimage d.U₀_le_U (hfix.le.trans bot_le))
  exact le_antisymm
    ((commutator_mono hpre le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hUV))
    (d.seed_eq_commutator_point_residual.le.trans (commutator_mono le_sup_left le_rfl))

set_option backward.isDefEq.respectTransparency false in
/-- Apply the genuine 14.7.71 centralizer theorem, followed by
commutator idempotence for the literal L₁=O²(L∩H). -/
theorem fixed_span_commutator_point (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c)
    (hSQ : S F L ≤ Q T L)
    (hcentral : R d ≤ (center (S F L)).map (S F L).subtype)
    (hinter : R d ⊓ F.U = V ⊔ d.U₀) : ⁅R d, F.Li L 1⁆ = V := by
  have hRC : R d ≤ ChiefFactors.C F :=
    le_inf ((R_le_S d).trans (hSQ.trans (Q_le_H F)))
      ((hcentral.trans (center_image_le_centralizer _)).trans (centralizer_le U_le_S))
  have hcomm : ⁅R d, F.Li L 1⁆ ≤ V ⊔ d.U₀ :=
    (ChiefFactors.fixed_span_commutator d c e hRC).trans hinter.le
  have hperfect : IsPPerfect 2 (F.Li L 1) := by
    change IsPPerfect 2 ((pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)).map (L ⊓ F.Gi 1).subtype)
    exact isPPerfect_embedded_pResidual 2 (L ⊓ F.Gi 1)
  have hidem := commutator_isPPerfect_idempotent (F.Li L 1) (R d) hperfect
    ((isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).to_le ((R_le_S d).trans hSQ))
    (((F.Li_le L 1).trans inf_le_left).trans (L_normalizes_R d))
  exact le_antisymm
    (hidem.symm.le.trans ((commutator_mono hcomm le_rfl).trans (join_commutator_point d).le))
    (d.seed_eq_commutator_point_residual.le.trans (commutator_mono (V_le_R d) le_rfl))

include d in
/-- The earlier point-residual generation on the actual natural flag
already implies normal generation in L. No normality of L₁ in H is used. -/
theorem point_residual_normal_span : conjugateSpanBy (F.Li L 1) L = L := by
  let := d.natural.chosen.elementary
  have h := NormalGeometry.flag_generation_of_linear F
    d.natural.naturalMarking.geometryAction d.natural.residual 2
    (NormalGeometry.flag_linear_generation F (by decide) 2 (by decide) (by decide))
  apply le_antisymm (conjugateSpanBy_le_self ((F.Li_le L 1).trans inf_le_left))
  exact h.symm.le.trans (conjugateSpanBy_mono le_rfl inf_le_left)

/-- Point-residual normal generation propagates the bound to the full
actor, with all generation and normalization premises discharged. -/
theorem fixed_span_commutator_L
    (hcomm : ⁅R d, F.Li L 1⁆ = V) : ⁅R d, L⁆ ≤ V := by
  let C := commutatorPreimage L (R d) V
  have hLC : L ≤ normalizer (C : Set G) :=
    commutatorPreimage_normalized L (R d) V L d.natural.chosen.normalizes
      L.le_normalizer (L_normalizes_R d) d.natural.chosen.normalizes
  have hL₁C : F.Li L 1 ≤ C :=
    le_commutatorPreimage ((F.Li_le L 1).trans inf_le_left)
      ((commutator_comm _ _).trans hcomm).le
  have hle : L ≤ C := (point_residual_normal_span d).symm.le.trans
    (conjugateSpanBy_le hL₁C hLC)
  rw [commutator_comm]
  exact (commutator_mono hle le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ d.natural.chosen.normalizes)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.SourceGeneration
