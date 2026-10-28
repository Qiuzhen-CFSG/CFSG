module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.SourceSetup
public import CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry

/-!
# The L₃(2) source setup for the final Theorem D branch

The chosen L₃(2) quotient already supplies case (1) of Hypothesis 14.3.1.
The genuine earlier 13.3.2 implication supplies maximal faithful membership
and the natural marking of the original chosen module. All other fields of
Hypothesis 12.8.1(1) follow from the original global exclusions. The existing
Chapter 12 constructions then provide the actual invariant flag, parabolic
conjugator, action kernels, normalizer control and escape.

The natural actor in source 13.3.2(3) is L/C_L(V). In this specialization
L/O₂(L) is simple and the chosen Irr⁺ module is noncentral, while O₂(L)
centralizes it. Thus C_L(V)=O₂(L), giving exactly the literal quotient map
used below. The earlier implication is still explicit; it is owned by
qt-13-03-preliminaries. It supplies no Chapter 14 flag or local conclusion.
The three other universal predecessors are the existing 12.2.2 structural
implication, 1.2.7 and 12.2.13, owned by the Chapter 12 and Section 1.2 owners.

Source: Aschbacher--Smith, 13.3.2(2--4), pp.884--885; Hypothesis 12.8.1(1)
and Notation 12.8.2, pp.849--850; 14.3.1(1), 14.3.3 and 14.3.7, pp.990--992.
The L₂(2) alternative and its elimination are separate preserved source work.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.Chapter14.Section03.CaseOneSource
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u

/-- The universal L₃(2) specialization of the earlier 13.3.2(2--4).
The coordinates intertwine conjugation on the original chosen subgroup V
with the original projection L → L/O₂(L). -/
def Earlier1332CaseOne : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L : Subgroup G),
    Counterexample T L → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 →
      FaithfulMaximalLocal T L ∧ IsQuasisimple (L ⧸ pCore 2 L) ∧
      ∀ (V : Subgroup G) (chosen : ChosenModule T L V),
        letI := chosen.elementary
        Nonempty (AmbientNaturalMarking L chosen.normalizes 3)

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G}

omit [Finite G] in
/-- The full rank-two catalogue at exponent greater than one is included
in the original larger-even-field exclusion, including general Ree groups. -/
theorem largerEvenFieldModel_of_rankTwo {f : ℕ} (hf : 1 < f)
    (h : ClassificationModels.IsRankTwoModel G f) : LargerEvenFieldModel G := by
  refine ⟨f, hf, ?_⟩
  cases h with
  | linear _ iso => exact .inl ⟨3, .inl iso⟩
  | unitary_four _ iso => exact .inl ⟨4, .inr (.inl iso)⟩
  | unitary_five _ iso => exact .inl ⟨5, .inr (.inl iso)⟩
  | symplectic _ iso => exact .inl ⟨2, .inr (.inr (.inl iso))⟩
  | g2 _ iso => exact .inr (.inl iso)
  | triality _ iso => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl iso)))))))
  | ree_f4 m _ he iso =>
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨m, he, .inr iso⟩)))))))
  | symplectic_derived he _ => omega
  | g2_derived he _ => omega
  | tits he _ => omega

/-- Construct Hypothesis 12.2.3 from the actual Chapter 13 configuration;
only the earlier maximality and quasisimple-quotient facts are used here. -/
theorem hypothesis1223 (d : Counterexample T L)
    (hmax : FaithfulMaximalLocal T L) (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    Hypothesis1223 KnownSimple.IsKnownSimple.{u} T L where
  simpleQTKE := d.qtke
  maximal_faithful := hmax
  quasisimple := hq
  no_rankTwo := fun f hf h => d.no_larger_field (largerEvenFieldModel_of_rankTwo hf h)
  no_M22 := d.no_sporadic .m22 (by simp)
  no_M23 := d.no_sporadic .m23 (by simp)
  no_J4 := d.no_sporadic .j4 (by simp)

/-- The genuine higher-rank alternative 12.8.1(1), constructed at n=3.
No flag, escape, full-action or normalizer conclusion is an input. -/
noncomputable def higherRankHypothesis (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (chosen : ChosenModule T L V) :
    HigherRankHypothesis KnownSimple.IsKnownSimple.{u} T L V 3 := by
  obtain ⟨hmax, hqs, hnat⟩ := earlier G T L d hq
  letI := chosen.elementary
  let A := Classical.choice (hnat V chosen)
  exact {
    source := hypothesis1223 d hmax hqs
    chosen := chosen
    rank := by decide
    quotient_model := hq
    natural := ⟨A.quotientEquiv, A.coordinates, A.equivariant⟩
    no_nextLinear := d.no_linear 4 (Or.inl rfl)
    no_A9 := d.no_alternating_nine
    no_M24 := d.no_sporadic .m24 (by simp) }

/-- The original Irr⁺ member can be selected using the universal structural
predecessor. Its natural coordinates come from the earlier 13.3.2 theorem. -/
theorem exists_higherRankHypothesis (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) :
    ∃ V : Subgroup G, Nonempty (HigherRankHypothesis KnownSimple.IsKnownSimple.{u} T L V 3) := by
  have hs := earlier G T L d hq
  obtain ⟨V, ⟨chosen⟩⟩ := (structural G T L (hypothesis1223 d hs.1 hs.2.1)).2.1
  exact ⟨V, ⟨higherRankHypothesis d earlier hq chosen⟩⟩

variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
  (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
include d earlier hq chosen

/-- The actual 14.3.3 normalizer/TI conclusions used by the later L₃(2)
geometry, obtained from the original source input and universal predecessors. -/
theorem source_normalizers (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u}) :
    (L.subgroupOf (normalizer (L : Set G))).Normal ∧
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
    IsMaximalTwoLocal (normalizer (L : Set G)) ∧
    {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} =
      {normalizer (L : Set G)} ∧
    (∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V) ∧
    normalizer (V : Set G) ≤ normalizer (L : Set G) ∧
    seedNormalizer (normalizer (L : Set G)) V = normalizer (V : Set G) := by
  let h := higherRankHypothesis d earlier hq chosen
  have hm := h.maximal_unique previous.structural previous.uniqueness
  exact ⟨(normal_subgroupOf_iff_le_normalizer L.le_normalizer).mpr le_rfl,
    h.sylow_normalizes previous.structural, hm.1, hm.2,
    h.seed_TI previous.structural,
    h.seed_normalizer_le previous.structural previous.uniqueness,
    h.seedNormalizer_eq previous.structural previous.uniqueness⟩

/-- Source 14.3.3(6), with its arbitrary normalized nonzero subspace retained. -/
theorem intersection_normalizer (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (A J : Subgroup G) (hA : A ≠ ⊥) (hAV : A ≤ V)
    (hJ : J ≤ normalizer (A : Set G)) :
    J ⊓ normalizer (L : Set G) = J ⊓ normalizer (V : Set G) := by
  let h := higherRankHypothesis d earlier hq chosen
  exact inf_eq_inf_normalizer_of_trivial_intersections
    (h.seed_TI previous.structural)
    (h.seed_normalizer_le previous.structural previous.uniqueness) hA hAV hJ

/-- The actual L and LT conjugation kernels and full L action needed by
the Chapter 14 local analysis. No quotient action is replaced by an isomorphism tag. -/
theorem source_actions (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    L ⊓ centralizer (V : Set G) = L.pCoreIn 2 ∧
    (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
    ∀ a : MulAut V, ∃ l ∈ L, ∀ v : V, l * (v : G) * l⁻¹ = (a v : G) := by
  let h := higherRankHypothesis d earlier hq chosen
  exact ⟨h.centralizer_L, h.centralizer_LT structural, h.full_L_action⟩

/-- Construct the original flag, point and omitted-point conjugator, and
discharge escape and H_z membership for that same point normalizer. -/
theorem source_flag (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u}) :
    primeRank 2 V = 3 ∧ ∃ (F : InvariantFlag T V 3) (z g : G),
      z ≠ 1 ∧ F.Vi 1 = zpowers z ∧ g ∈ F.P L ∧ g ∉ F.H ∧
      (∀ i, i ≤ 3 → ∀ A : Subgroup G, A ≤ V → Nat.card A = 2 ^ i →
        (T : Subgroup G) ≤ normalizer (A : Set G) → A = F.Vi i) ∧
      F.H = centralizer ({z} : Set G) ∧
      ¬ F.H ≤ normalizer (L : Set G) ∧
      F.H ∈ F.Hz L (normalizer (L : Set G)) := by
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨hrank, F, huniq, z, hz, he, g, hgP, hgH⟩ := h.exists_flag_geometry previous.structural
  exact ⟨hrank, F, z, g, hz, he, hgP, hgH, huniq, F.H_eq_centralizer (by decide) z he,
    h.flag_escape F previous.alternatives, h.point_mem_Hz F previous.alternatives⟩

/-- The original natural marking supplies both the center intersection and
the plane generation used in 14.3.11 and in the later nonabelian analysis. -/
theorem source_seed_geometry (F : InvariantFlag T V 3) :
    conjugateSpanBy (F.Vi 2) (F.Li L 1) = V ∧
    F.U = conjugateSpanBy (F.Vi 2) F.H ∧
    (¬ IsMulCommutative F.U → V ⊓ F.ZU = F.Vi 1) := by
  let h := higherRankHypothesis d earlier hq chosen
  let := chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  have hirr := F.invariant_subgroup_of_ambient_natural h.naturalMarking (by decide)
  exact ⟨F.seed_eq_plane_span L (by decide) chosen.normalizes hirr,
    F.U_eq_plane_span L (by decide) chosen.normalizes hirr,
    F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking (by decide)⟩

/-- Source 14.3.7: the full natural L-action factors every actual element
of M_V through L and the literal centralizer C_M(V). -/
theorem seed_normalizer_factorization :
    (seedNormalizer (normalizer (L : Set G)) V : Set G) =
      (L : Set G) * (normalizer (L : Set G) ⊓ centralizer (V : Set G) : Subgroup G) := by
  let h := higherRankHypothesis d earlier hq chosen
  ext m
  constructor
  · intro hm
    let a := V.normalizerMonoidHom ⟨m, hm.2⟩
    obtain ⟨l, hl, he⟩ := h.full_L_action a
    let c := l⁻¹ * m
    have hc : c ∈ centralizer (V : Set G) := by
      intro v hv
      have hv' := he ⟨v, hv⟩
      change l * v * l⁻¹ = m * v * m⁻¹ at hv'
      have hh := congrArg (fun y : G => l⁻¹ * y * m) hv'
      simpa [c, mul_assoc] using hh
    refine ⟨l, hl, c, ⟨?_, hc⟩, ?_⟩
    · exact (normalizer (L : Set G)).mul_mem
        ((normalizer (L : Set G)).inv_mem (L.le_normalizer hl)) hm.1
    · simp [c]
  · rintro ⟨l, hl, c, hc, rfl⟩
    exact ⟨(normalizer (L : Set G)).mul_mem (L.le_normalizer hl) hc.1,
      (normalizer (V : Set G)).mul_mem (chosen.normalizes hl)
        (Subgroup.centralizer_le_normalizer _ hc.2)⟩

/-- The second factorization in 14.3.7, for the same original flag:
M_V = L(M ∩ G₁). -/
theorem point_normalizer_factorization
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) :
    (seedNormalizer (normalizer (L : Set G)) V : Set G) =
      (L : Set G) * (normalizer (L : Set G) ⊓ F.H : Subgroup G) := by
  let h := higherRankHypothesis d earlier hq chosen
  apply Set.Subset.antisymm
  · intro m hm
    obtain ⟨l, hl, c, hc, rfl⟩ :=
      (seed_normalizer_factorization d earlier hq chosen).le hm
    exact Set.mul_mem_mul hl ⟨hc.1,
      (centralizer_le (F.le_seed 1)).trans (Subgroup.centralizer_le_normalizer _) hc.2⟩
  · rintro _ ⟨l, hl, c, hc, rfl⟩
    exact (seedNormalizer (normalizer (L : Set G)) V).mul_mem
      ⟨L.le_normalizer hl, chosen.normalizes hl⟩
      (h.flag_normalizer_le structural F (by decide) (by decide) hc)

/-- The final conditional clause of 14.3.7, with V-normality expressed
as its literal normalizer containment. -/
theorem normalizer_eq_join_of_point_intersection
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3)
    (hV : normalizer (L : Set G) ≤ normalizer (V : Set G))
    (hinter : normalizer (L : Set G) ⊓ F.H = F.Li L 1 ⊔ (T : Subgroup G)) :
    normalizer (L : Set G) = L ⊔ (T : Subgroup G) := by
  let h := higherRankHypothesis d earlier hq chosen
  apply le_antisymm
  · intro m hm
    obtain ⟨l, hl, c, hc, rfl⟩ :=
      (point_normalizer_factorization d earlier hq chosen structural F).le ⟨hm, hV hm⟩
    have hc' : c ∈ L ⊔ (T : Subgroup G) := by
      rw [hinter] at hc
      exact (sup_le_sup_right ((F.Li_le L 1).trans inf_le_left) _) hc
    exact (L ⊔ (T : Subgroup G)).mul_mem (mem_sup_left hl) hc'
  · exact sup_le L.le_normalizer (h.sylow_normalizes structural)

/-- A literal later consumer: all source premises of the checked local
center-product theorem are supplied, retaining its original antecedents. -/
theorem source_localKernel (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    conjugate F.ZU g ≤ F.U →
      (F.ZU = Chapter12.Section08.centerIn (F.I₂ L) ⊔ F.Vi 1 ∧
        Disjoint (Chapter12.Section08.centerIn (F.I₂ L)) (F.Vi 1) ∧
        ∃ e : Chapter12.Section08.centerIn (F.I₂ L) × F.Vi 1 ≃* F.ZU,
          ∀ a b, (e (a, b) : G) = (a : G) * (b : G)) ∧
      ⁅L, Chapter12.Section08.centerIn (F.I₂ L)⁆ = ⊥ :=
  (higherRankHypothesis d earlier hq chosen).localKernel_center_product previous F hne g hgP hgH

end CFSG.Quasithin.Chapter14.Section03.CaseOneSource
