module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.DualExtensions.Reduction
public import Theory.Representation.FirstCohomologyG2Natural.NonbinaryBound
public import Theory.Representation.FirstCohomologyG2Natural.BinaryBound
public import Theory.Representation.FirstCohomologyG2Natural.BinaryGeneration

/-!
# Octonion cocycles and the two G2 consumers

The proved cocycle bounds over binary and larger fields make every natural
G2-derived cocycle an octonion displacement. Fixed-point freeness on the
derived group then proves the corresponding assertion for the full G2 group,
including the distinct binary endpoint. Scalar restriction identifies binary
cocycles with these same cocycles over the defining field.

Consequently the exact remaining model calculation is `G2TraceDetection`:
an offender of rank 3n cannot fix a nonzero-trace octonion modulo
the scalar identity line. Its implication to cocycle detection is proved,
and both literal B.4.2 G2 rows are connected to the original moved-section
consumer. The final two supplement theorems here are conditional on this
explicit model geometry. Neither the geometry nor the G2 exclusions are
claimed as proved in this module.

The model geometry has independent binary and nonbinary branches. It must be
proved before the B.5.1 assembly can discharge the trace parameter. In
particular it cannot be supplied by a cohomology dimension alone, a fixed-space
assumption on the original V, or identification of G2(2) with G2(2)'.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.1.5–7,
printed pp.408–409; B.4.6 and B.5.1(5), printed pp.88–90 and 102–103.
The octonion coordinates and actions are the existing attributed ATLAS ports.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.DualExtensions
open Atlas.SplitOctonion Atlas.G2.Natural

private theorem derived_fixed_eq_bot (K : Type*) [Field K] [CharP K 2] :
    OneCohomology.fixed (derivedAction K) = ⊥ := by
  apply bot_unique
  intro v hv
  obtain ⟨x, rfl⟩ := mk_surjective K v
  apply (mk_eq_zero_iff K x).mpr
  apply (ambientCocycle_eq_zero_iff K x.val).mp
  rw [ambientCocycle_traceZero]
  ext g
  exact sub_eq_zero.mpr (hv g)

private theorem cocycle_eq_of_restrict_eq
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    {ρ : Representation k G V} (N : Subgroup G) [N.Normal]
    (hN : OneCohomology.fixed (ρ.comp N.subtype) = ⊥)
    (f t : cocycles ρ) (hft : ∀ n : N, f.val n = t.val n) : f = t := by
  let d := f - t
  have hd (n : N) : d.val n = 0 := sub_eq_zero.mpr (hft n)
  apply sub_eq_zero.mp
  apply Subtype.ext
  funext g
  have hm : d.val g ∈ OneCohomology.fixed (ρ.comp N.subtype) := by
    intro n
    let m : N := ⟨g⁻¹ * n * g, by simpa using (inferInstance : N.Normal).conj_mem n n.property g⁻¹⟩
    have he : (n : G) * g = g * m := by simp [m, mul_assoc]
    have h := d.property n g
    rw [he, d.property g m, hd n, hd m, map_zero, zero_add, add_zero] at h
    exact h.symm
  rwa [hN] at hm

/-- The full G2 cocycle obtained by octonion displacement modulo the scalar
line. This keeps the full actor distinct from its derived subgroup. -/
def fullOctonionCocycle (K : Type*) [Field K] [CharP K 2] :
    Carrier K →ₗ[K] cocycles (action K) where
  toFun x := ⟨fun g => mk K (displacement K g x), by
    intro g h
    change mk K (displacement K (g * h) x) =
      action K g (mk K (displacement K h x)) + mk K (displacement K g x)
    rw [action_mk, ← map_add]
    congr 1
    apply Subtype.ext
    change ambient K (g * h) x - x =
      ambient K g (ambient K h x - x) + (ambient K g x - x)
    rw [map_mul, Module.End.mul_apply, map_sub]
    abel⟩
  map_add' x y := by ext g; exact map_add ((mk K).comp (displacement K g)) x y
  map_smul' a x := by ext g; exact map_smul ((mk K).comp (displacement K g)) a x

/-- The already proved binary and nonbinary cocycle calculations exhaust
full-group cocycles as well: equality on the derived group detects equality,
since the natural derived action has no fixed vectors. -/
theorem fullOctonionCocycle_surjective (K : Type*) [Field K] [CharP K 2] [Finite K] :
    Function.Surjective (fullOctonionCocycle K) := by
  have hs : Function.Surjective (ambientCocycle K) := by
    by_cases hK : Nat.card K = 2
    · exact ambientCocycle_surjective_of_binary_generation K (binary_pair_generates K hK)
    · have hlt : 2 < Nat.card K := by
        let := Fintype.ofFinite K
        have : 1 < Fintype.card K := Fintype.one_lt_card
        rw [Nat.card_eq_fintype_card] at hK ⊢
        omega
      exact ambientCocycle_surjective_of_finrank_cocycles_le K
        (finrank_cocycles_le_seven_nonbinary K hlt)
  intro f
  let f' : cocycles (derivedAction K) := ⟨fun g => f.val g, fun g h => f.property g h⟩
  obtain ⟨x, hx⟩ := hs f'
  refine ⟨x, cocycle_eq_of_restrict_eq (commutator (Atlas.G2.Model K)) (derived_fixed_eq_bot K)
    (fullOctonionCocycle K x) f ?_⟩
  intro n
  exact congrArg (fun c : cocycles (derivedAction K) => c.val n) hx

/-- The remaining concrete geometry says that an octonion fixed modulo
scalars by A has trace zero. Surjectivity of the actual displacement map
turns that geometry into the needed binary cocycle detection. -/
theorem g2_cocycleDetection_of_trace (F : BinaryField)
    (A : Subgroup (Atlas.G2.Model F.Carrier))
    (htrace : ∀ x : Carrier F.Carrier,
      (∀ a ∈ A, mk F.Carrier (displacement F.Carrier a x) = 0) → trace x = 0) :
    CocycleDetection (binaryG2 F) A := by
  intro f hf
  let f' := cocyclesRestrictEquiv (k := ZMod 2) (action F.Carrier) f
  obtain ⟨x, hx⟩ := fullOctonionCocycle_surjective F.Carrier f'
  have htx : trace x = 0 := htrace x (by
    intro a ha
    exact (congrArg (fun c : cocycles (action F.Carrier) => c.val a) hx).trans (hf a ha))
  refine ⟨mk F.Carrier ⟨x, htx⟩, ?_⟩
  apply Subtype.ext
  funext g
  change action F.Carrier g (mk F.Carrier ⟨x, htx⟩) - mk F.Carrier ⟨x, htx⟩ = f.val g
  rw [action_mk, ← map_sub]
  exact congrArg (fun c : cocycles (action F.Carrier) => c.val g) hx

/-- The precise remaining octonion calculation. This is an explicit geometric
premise for conditional consumers, not a source theorem or a splitting claim.
The full G2 group acts on the eight coordinates and fixes the scalar identity. -/
def G2TraceDetection (F : BinaryField) : Prop :=
  ∀ A : Subgroup (Atlas.G2.Model F.Carrier), IsOffender (binaryG2 F) A → rank A = 3 * F.degree →
    ∀ x : Carrier F.Carrier,
      (∀ a ∈ A, ∃ c : F.Carrier, c • unit = a.val x - x) → trace x = 0

theorem g2_cocycleDetection (F : BinaryField) (htrace : G2TraceDetection F)
    (A : Subgroup (Atlas.G2.Model F.Carrier)) (hA : IsOffender (binaryG2 F) A)
    (hr : rank A = 3 * F.degree) : CocycleDetection (binaryG2 F) A := by
  apply g2_cocycleDetection_of_trace F A
  intro x hx
  apply htrace A hA hr x
  intro a ha
  exact (mk_eq_zero_iff F.Carrier _).mp (hx a ha)

universe u v w z
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

private noncomputable def fullRestriction {H : Type w} [Group H]
    {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) H W} {L : Subgroup G} (hL : L = ⊤)
    (e : ActionEquiv (ρ.comp L.subtype) σ) : ActionEquiv ρ σ := by
  subst L
  exact ⟨Subgroup.topEquiv.symm.trans e.groupEquiv, e.linearEquiv,
    fun g v => e.intertwines ⟨g, mem_top g⟩ v⟩

private theorem supplement_of_g2_equiv [Finite G] {K : CFSG.Quasithin.GroupClass.{u}}
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (F : BinaryField) (e : ActionEquiv s.action (binaryG2 F)) (htrace : G2TraceDetection F)
    (hoff : ∀ A, IsBestOffender s.action A → rank A = 3 * F.degree)
    (hq : quadraticRatio s.action = 1) : s.space.toSubmodule ⊔ ρ.invariants = ⊤ := by
  let := h.finite_module
  let := h.quasisimple
  let := component_normal_of_fitting_eq_sup_center L h.fitting
  obtain ⟨A, hA⟩ := source_isFF h
  have hb := (offender_equality s hq hA).1
  have ha := (hb.isOffender _).map_equivariant _ _ e.groupEquiv.toMonoidHom
    e.groupEquiv.injective e.linearEquiv e.intertwines
  have hr : rank (A.map e.groupEquiv.toMonoidHom) = 3 * F.degree := by
    rw [rank_map_injective _ e.groupEquiv.injective, hoff A hb]
  exact supplement_of_cocycleDetection h s hq hA
    (CocycleDetection.of_equiv e A (g2_cocycleDetection F htrace _ ha hr))

/-- Full-field G2 consumer of the geometric prerequisite. Ratio one transfers
the offender generators and proves G=L; the given natural marking then becomes
an equivalence of the full actor. The trace premise remains to be proved. -/
theorem g2_supplement_of_trace [Finite G] {K : CFSG.Quasithin.GroupClass.{u}}
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (F : BinaryField) (hg : offenderSubgroup s.action = L)
    (e : ActionEquiv (s.action.comp L.subtype) (binaryG2 F))
    (hoff : ∀ A, IsBestOffender s.action A → rank A = 3 * F.degree)
    (hq : quadraticRatio s.action = 1) (htrace : G2TraceDetection F) :
    s.space.toSubmodule ⊔ ρ.invariants = ⊤ := by
  let := h.finite_module
  let := h.quasisimple
  let := component_normal_of_fitting_eq_sup_center L h.fitting
  have hL : L = ⊤ := hg.symm.trans (section_generated s hq h.generated)
  exact supplement_of_g2_equiv h s F (fullRestriction hL e) htrace hoff hq

/-- Binary G2 consumer retaining the actual derived-subgroup marking of L.
The offender-generated actor is the full G2(2), and is never identified with
G2(2)'. The trace premise is the separate binary geometric calculation. -/
theorem g2Two_supplement_of_trace [Finite G] {K : CFSG.Quasithin.GroupClass.{u}}
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (e : MarkedActionEquiv s.action (offenderSubgroup s.action) L (g2Natural (ZMod 2))
      (commutator (Atlas.G2.Model (ZMod 2))))
    (hoff : ∀ A, IsBestOffender s.action A → rank A = 3)
    (hq : quadraticRatio s.action = 1) (htrace : G2TraceDetection BinaryField.two) :
    s.space.toSubmodule ⊔ ρ.invariants = ⊤ := by
  let := h.finite_module
  let := h.quasisimple
  let := component_normal_of_fitting_eq_sup_center L h.fitting
  have hJ := section_generated s hq h.generated
  let E := fullRestriction hJ e.action
  apply supplement_of_g2_equiv h s BinaryField.two E htrace (fun A hA => ?_) hq
  simpa only [BinaryField.two, mul_one] using hoff A hA

end CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.DualExtensions
