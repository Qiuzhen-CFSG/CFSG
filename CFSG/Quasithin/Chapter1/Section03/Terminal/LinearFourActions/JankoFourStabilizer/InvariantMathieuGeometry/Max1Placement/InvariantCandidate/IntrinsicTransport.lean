module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.CoreRecovery

/-!
# Reducing intrinsic core recovery to the literal max1 subgroup

The intrinsic geometry can be proved entirely inside the certified max1
subgroup. An actual candidate isomorphism transports the local C-component,
its Sylow subgroup, and its L₄(2) section to that carrier. The embedded center
of the two-core commutes with injective maps, so the centralizer condition
and uniqueness of elementary subgroups transport back into the ambient J₄.

`LiteralIntrinsicCoreRecovery` is the remaining local geometry, not an
assertion that it has been proved. This reduction supplies no ambient
centralizer or normalizer bound; those belong to `AmbientCoreRecovery`.

Source: Aschbacher–Smith A.3.12(17), printed pp.47–48, and the proof of
1.3.9, p.514; GLS3 Table 5.3i. The actual max1 model and quotient comparison
are certified in `Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu`.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
open Section02.LocalModels
universe u v
variable {G : Type u} [Group G] {G' : Type v} [Group G']

/-- The embedded center of the two-core commutes with every faithful embedding. -/
theorem map_coreCenter_of_injective (A : Subgroup G) (f : G →* G')
    (hf : Function.Injective f) :
    (coreCenter A).map f = coreCenter (A.map f) := by
  have hcore := map_pCoreIn_of_injective 2 A f hf
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨hcore ▸ mem_map_of_mem f ha.1, ?_⟩
    intro y hy
    rw [← hcore] at hy
    obtain ⟨b, hb, rfl⟩ := hy
    simpa only [map_mul] using congrArg f (ha.2 b hb)
  · intro hx
    have hxcore := hx.1
    rw [← hcore] at hxcore
    obtain ⟨a, ha, rfl⟩ := hxcore
    refine ⟨a, ⟨ha, ?_⟩, rfl⟩
    intro b hb
    apply hf
    simpa only [map_mul] using hx.2 (f b) (hcore ▸ mem_map_of_mem f hb)

/-- Intrinsic recovery inside a given ambient group: its two-core centralizes
Z(O₂(B)) and is the unique elementary subgroup of order 2048 doing so. -/
@[expose] def CoreRecoveryInside (B : Subgroup G) : Prop :=
  pCore 2 G ≤ centralizer (coreCenter B : Set G) ∧
    ∀ E ∈ centralElementary B, E = pCore 2 G

/-- Pull intrinsic recovery back through an actual ambient isomorphism. -/
theorem coreRecoveryInside_of_equiv {B : Subgroup G} (e : G ≃* G')
    (h : CoreRecoveryInside (B.map e.toMonoidHom)) : CoreRecoveryInside B := by
  constructor
  · intro x hx z hz
    apply e.injective
    have hx' : e x ∈ pCore 2 G' :=
      pCore_map_iso 2 e ▸ mem_map_of_mem e.toMonoidHom hx
    have hz' : e z ∈ coreCenter (B.map e.toMonoidHom) :=
      map_coreCenter B e ▸ mem_map_of_mem e.toMonoidHom hz
    simpa only [map_mul] using h.1 hx' (e z) hz'
  · intro E hE
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [pCore_map_iso]
    exact h.2 _ (map_mem_centralElementary hE e)

/-- The local geometric obligation on the literal certified carrier.
The source Sylow-local condition and the actual section are retained. -/
@[expose] def LiteralIntrinsicCoreRecovery : Prop :=
  ∀ (B : Subgroup certifiedMathieuSubgroup) (T : Sylow 2 certifiedMathieuSubgroup),
    ClassicalGroup.IsPSL (XiQuotient B) 4 2 →
    B ∈ ChapterA.Section03.localCComponents T → CoreRecoveryInside B

-- Transport uses the group interface, not the underlying 112-dimensional matrices.
attribute [local irreducible] Janko4.modelGroup certifiedMathieuSubgroup

/-- A proof on the literal max1 carrier supplies intrinsic recovery for every
candidate, using its actual isomorphism and its own Sylow-local witness. -/
theorem intrinsicCoreRecovery_of_literal
    (hliteral : LiteralIntrinsicCoreRecovery) : IntrinsicCoreRecovery := by
  intro A H hA hH
  obtain ⟨hAH, ⟨e⟩, T, hT⟩ := hH
  let B : Subgroup certifiedMathieuSubgroup := (A.subgroupOf H).map e.toMonoidHom
  let f : A ≃* B := (subgroupOfEquivOfLe hAH).symm.trans
    (e.subgroupMap (A.subgroupOf H))
  have hB : ClassicalGroup.IsPSL (XiQuotient B) 4 2 :=
    hA.of_mulEquiv (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).symm
  have hBT : B ∈ ChapterA.Section03.localCComponents
      (T.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup certifiedMathieuSubgroup) := by
    let : Group.IsSolvable e.toMonoidHom.ker := by
      rw [e.toMonoidHom.ker_eq_bot e.injective]
      infer_instance
    exact Section02.localCComponents_map_of_solvable_ker hT e.toMonoidHom
  have hinside : CoreRecoveryInside (A.subgroupOf H) :=
    coreRecoveryInside_of_equiv e (hliteral B _ hB hBT)
  have hcenter : (coreCenter (A.subgroupOf H)).map H.subtype = coreCenter A := by
    rw [map_coreCenter_of_injective _ _ H.subtype_injective, map_subgroupOf_eq_of_le hAH]
  constructor
  · rintro x ⟨y, hy, rfl⟩ z hz
    rw [← hcenter] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact congrArg Subtype.val (hinside.1 hy w hw)
  · intro E hE hEH
    have hE' : E.subgroupOf H ∈ centralElementary (A.subgroupOf H) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x hx z hz
        exact Subtype.ext (hE.1 hx z (hcenter ▸ mem_map_of_mem H.subtype hz))
      · let := hE.2.1
        exact IsElementaryAbelian.subgroupOf hEH
      · exact (Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv).trans hE.2.2
    have heq := congrArg (Subgroup.map H.subtype) (hinside.2 _ hE')
    rwa [map_subgroupOf_eq_of_le hEH] at heq

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
