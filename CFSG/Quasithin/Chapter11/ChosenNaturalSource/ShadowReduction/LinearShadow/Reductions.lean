module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.SourceClauses
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import Theory.GroupTheory.TINormalizerControl
/-!
# Counterexample reductions for the linear shadow

The kernel of the original chosen central quotient is C_V(L). It is normalized
by LT, so nonsolvable uniqueness forces its normalizer into M = N_G(L) whenever
it is nontrivial. Consequently an escaping centralizer of any quotient preimage
makes that kernel trivial. This verifies the kernel/uniqueness route saved in
`Scratch/ChosenNaturalShadow/FixedSpace.lean` by the shadow-reduction owner.

`Preceding1133` retains only the conclusions of 11.0.3(4), 11.2.2(5),
11.2.3 and 11.2.5, together with the nonzero source line. These are inputs from
the preceding local-geometry owner, not conclusions of Proposition 11.3.2.
The 11.2.5 input is its application after Hypothesis 11.3.1 supplies the extra
SL3 centralizer bound, using V1 ≤ V2. In particular the normalizer decomposition
is conditional on fixed-space vanishing; it is used only after that has been
proved. E.3.15 is applied with the actual relative Sylow subgroup in H and the
actual O2(H), and excludes the G2 marking in the weak-closure-in-core branch.

This proves 11.3.3, including all four clauses of 11.3.2 in its positive branch.
The last theorem gives 11.3.4(4) conditional on the SL3/Sp4 alternative in
11.3.4(2). Constructing that alternative, proving k = n, identifying the common
two-core and constructing compatible fields remain separate obligations.
No theorem here claims the full Proposition 11.3.2.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.3.3--4, printed p.771; the uniqueness input is 1.2.7.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V)
omit [Finite G] in
theorem fixed_le_centralQuotientPreimage (U : Submodule (ZMod 2) D.chosenCentralQuotient) :
    V ⊓ centralizer (L : Set G) ≤ D.centralQuotientPreimage U := by
  rw [← LocalGeometry.centralQuotientPreimage_bot D]
  exact map_mono (comap_mono (show (⊥ : Subgroup (Multiplicative D.chosenCentralQuotient)) ≤
    U.toAddSubgroup.toSubgroup from bot_le))

theorem fixed_trivial_of_quotient_preimage_centralizer_outside
    (S : D.NonbinaryNaturalInput) (U : Submodule (ZMod 2) D.chosenCentralQuotient)
    (hout : ¬ centralizer (D.centralQuotientPreimage U : Set G) ≤ normalizer (L : Set G)) :
    V ⊓ centralizer (L : Set G) = ⊥ := by
  by_contra hne
  let C := V ⊓ centralizer (L : Set G)
  let := D.elementary
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le (show C ≤ V from inf_le_left)
  have hnormC : L ⊔ (T : Subgroup G) ≤ normalizer (C : Set G) := by
    apply le_trans _ Subgroup.inf_normalizer_le_normalizer_inf
    refine le_inf (sup_le D.normalizes S.sylow_normalizes) ?_
    exact (sup_le L.le_normalizer D.sylow_normalizes_component).trans
      (le_normalizer_of_normal_subgroupOf (Subgroup.centralizer_le_normalizer _))
  have hlocal : IsTwoLocal (normalizer (C : Set G)) :=
    ⟨C, hne, IsElementaryAbelian.isPGroup 2 C, rfl⟩
  obtain ⟨M, hNM, hM⟩ := Finite.exists_le_maximal hlocal
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    S.source.simpleQTKE T S.source.maximal_faithful.1
  have hML : M = normalizer (L : Set G) := by
    have he : componentOrbit L (T : Subgroup G) = L := D.localOrbit_eq
    simpa only [he] using hu.normalizer_unique M hM (hnormC.trans hNM)
  apply hout
  apply (centralizer_le (fixed_le_centralQuotientPreimage D U)).trans
  exact (Subgroup.centralizer_le_normalizer (C : Set G)).trans (hML ▸ hNM)

open Representation CFSG.Quasithin.ChapterB.QuasisimpleSource

/-- Only preceding-source conclusions used in 11.3.3. The field is the original
marked field, and the normalizers concern the actual quotient-line preimage. -/
structure Preceding1133 (S : D.NonbinaryNaturalInput)
    (U₁ : Submodule (ZMod 2) D.chosenCentralQuotient) (H : Subgroup G) : Prop where
  line_nonzero : U₁ ≠ ⊥
  ti : ∀ g ∈ normalizer (L : Set G),
    V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V
  normalizer_control :
    centralizer (D.centralQuotientPreimage U₁ : Set G) ≤ normalizer (L : Set G) →
      normalizer (D.centralQuotientPreimage U₁ : Set G) ≤ normalizer (L : Set G)
  normalizer_split : V ⊓ centralizer (L : Set G) = ⊥ →
    normalizer (D.centralQuotientPreimage U₁ : Set G) =
      centralizer (D.centralQuotientPreimage U₁ : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (D.centralQuotientPreimage U₁ : Set G))
  weak_obstruction : Source.WeakClosureObstruction (T : Subgroup G) V
    (D.centralQuotientPreimage U₁) H
  g2_weak_normalizer :
    Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) →
    normalizer (Source.weakClosureZero (T : Subgroup G) V : Set G) ≤
      normalizer (L : Set G)

variable {D} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H : Subgroup G}

/-- The source TI assertion controls the relative line normalizer. -/
theorem Preceding1133.relative_normalizer_le_seed_normalizer
    (p : Preceding1133 D S U₁ H) :
    normalizer (L : Set G) ⊓ normalizer (D.centralQuotientPreimage U₁ : Set G) ≤
      normalizer (V : Set G) :=
  inf_normalizer_le_of_trivial_intersections p.ti
    (D.centralQuotientPreimage_ne_bot U₁ p.line_nonzero) (D.centralQuotientPreimage_le U₁)

/-- E.3.15 applies to the literal two-core of the selected outside local group. -/
theorem Hypothesis1131At.normalizes_weakClosure_of_le_core
    (h : Hypothesis1131At D S U₁ H)
    (hcore : Source.weakClosureZero (T : Subgroup G) V ≤ H.pCoreIn 2) :
    H ≤ normalizer (Source.weakClosureZero (T : Subgroup G) V : Set G) := by
  have hTH : (T : Subgroup G) ≤ H := h.outside.1.1.2
  have hW : ChapterE.indexedWeakClosure V
      (((T.subtype hTH : Sylow 2 H) : Subgroup H).map H.subtype) 0 ≤ H.pCoreIn 2 := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH,
      ← weakClosureZero_eq_indexed] using hcore
  have hnorm := ChapterE.normalizer_le_weakClosure_normalizer_of_two_overgroup
    V H (T.subtype hTH) (H.pCoreIn 2) 0
    (isPGroup_pCoreIn 2 H) (pCoreIn_le 2 H) hW
  have hHN : H ≤ normalizer (H.pCoreIn 2 : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH,
    ← weakClosureZero_eq_indexed] using hHN.trans hnorm

/-- The nonabelian normalizer closure forces the centralizer outside M. -/
theorem Preceding1133.centralizer_outside_of_weakClosure_le_core
    (p : Preceding1133 D S U₁ H)
    (hcore : Source.weakClosureZero (T : Subgroup G) V ≤ H.pCoreIn 2) :
    ¬ centralizer (D.centralQuotientPreimage U₁ : Set G) ≤ normalizer (L : Set G) := by
  intro hc
  have hNV : normalizer (D.centralQuotientPreimage U₁ : Set G) ≤
      normalizer (V : Set G) :=
    (le_inf (p.normalizer_control hc) le_rfl).trans
      p.relative_normalizer_le_seed_normalizer
  have hspan : Source.conjugateSpan (normalizer (D.centralQuotientPreimage U₁ : Set G)) V ≤ V := by
    apply iSup_le
    intro g
    exact (mem_normalizer_iff_map_conj_eq.mp (hNV g.property)).le
  have hnon := p.weak_obstruction.resolve_left (not_not.mpr hcore)
  let := D.elementary
  apply hnon
  apply le_centralizer_iff_isMulCommutative.mp
  exact hspan.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
    (centralizer_le hspan))

/-- Source 11.3.3's positive branch proves all four clauses, from §§11.0--11.2.
No shadow conclusion is an input of this theorem. -/
theorem proposition1132_of_weakClosure_le_core
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hcore : Source.weakClosureZero (T : Subgroup G) V ≤ H.pCoreIn 2) :
    Proposition1132At D S U₁ H := by
  have hout := p.centralizer_outside_of_weakClosure_le_core hcore
  have hfixed := fixed_trivial_of_quotient_preimage_centralizer_outside D S U₁ hout
  refine ⟨?_, hout, hfixed, ?_⟩
  · cases S.natural with
    | sl3 m =>
      exact (hout (h.linear_centralizer
        ⟨S.field.Carrier, inferInstance, inferInstance, S.field.card_eq, ⟨m.some.groupEquiv⟩⟩)).elim
    | sp4 m =>
      exact ⟨S.field.Carrier, inferInstance, inferInstance, S.field.card_eq, ⟨m.some.groupEquiv⟩⟩
    | g2 m =>
      exact (h.outside.1.2 ((h.normalizes_weakClosure_of_le_core hcore).trans
        (p.g2_weak_normalizer m))).elim
  · intro hcore'
    exact nonabelian_centralizer_span_of_weakClosure D U₁ H p.weak_obstruction hcore'
      (p.normalizer_split hfixed) p.relative_normalizer_le_seed_normalizer

/-- In a counterexample to 11.3.2, W₀(T,V) escapes O₂(H), as in 11.3.3. -/
theorem weakClosure_not_le_core_of_counterexample
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hcounter : ¬ Proposition1132At D S U₁ H) :
    ¬ Source.weakClosureZero (T : Subgroup G) V ≤ H.pCoreIn 2 :=
  fun hcore => hcounter (proposition1132_of_weakClosure_le_core h p hcore)

/-- With the genuine 11.3.4(2) alternative, a counterexample has N_G(V₁) ≤ N_G(V).
The classification alternative is left to the numerical/local-group reduction. -/
theorem line_normalizer_le_of_counterexample
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hcounter : ¬ Proposition1132At D S U₁ H)
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree)) :
    normalizer (D.centralQuotientPreimage U₁ : Set G) ≤ normalizer (V : Set G) := by
  have hc : centralizer (D.centralQuotientPreimage U₁ : Set G) ≤ normalizer (L : Set G) := by
    by_contra hout
    apply hcounter
    have hfixed := fixed_trivial_of_quotient_preimage_centralizer_outside D S U₁ hout
    refine ⟨halt.resolve_left (fun hsl => hout (h.linear_centralizer hsl)), hout, hfixed, ?_⟩
    intro hcore
    exact (weakClosure_not_le_core_of_counterexample h p hcounter hcore).elim
  exact (le_inf (p.normalizer_control hc) le_rfl).trans
    p.relative_normalizer_le_seed_normalizer
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
