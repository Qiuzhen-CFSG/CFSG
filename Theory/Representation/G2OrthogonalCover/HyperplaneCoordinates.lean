module

public import Theory.Representation.G2OrthogonalCover

/-!
# Off-scalar hyperplanes in the binary orthogonal cover

The norm polar pairing identifies functionals on the trace-zero seven-space
with ambient octonions modulo the scalar identity. A hyperplane avoiding the
identity has a unique representing octonion of trace one and fifth coordinate
zero. Its six remaining coordinates give the affine 64-point hyperplane model.

This is the literal cover geometry used in Aschbacher--Smith, Lemma 12.4.8,
printed p.815. The split-octonion conventions and attribution are retained
from the imported ATLAS port; see LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section

open Atlas.SplitOctonion Module
namespace Atlas.G2.Natural.OrthogonalCover.Hyperplanes

local notation "F" => ZMod 2
local notation "E" => TraceZero F

/-- Six affine coordinates for an off-scalar hyperplane. -/
abbrev Parameters := Fin 6 → F

/-- The canonical trace-one octonion representing a hyperplane functional. -/
def representative (a : Parameters) : Carrier F :=
  ![a 0, a 1, a 2, 1, 0, a 3, a 4, a 5]

/-- Remove the two diagonal coordinates of an octonion. -/
def coordinates (x : Carrier F) : Parameters :=
  ![x 0, x 1, x 2, x 5, x 6, x 7]

@[simp] theorem coordinates_representative (a : Parameters) :
    coordinates (representative a) = a := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem trace_representative (a : Parameters) :
    trace (representative a) = 1 := by
  simp [representative, trace]

theorem representative_coordinates {x : Carrier F} (hx : trace x = 1) :
    representative (coordinates x) = x + x 4 • unit := by
  have hd : x 3 + x 4 = 1 := hx
  funext i
  fin_cases i <;> simp [representative, coordinates, unit, hd, CharTwo.add_self_eq_zero]

/-- The normalized functional corresponding to the six coordinates. -/
def functional (a : Parameters) : E →ₗ[F] F :=
  (normPolar (representative a)).comp (TraceZero F).subtype

@[simp] theorem functional_identity (a : Parameters) :
    functional a (identity F) = 1 := by
  change normPolar (representative a) unit = 1
  rw [normPolar_symm, polar_unit, trace_representative]

/-- The literal kernel in the original seven-dimensional space. -/
def hyperplane (a : Parameters) : Submodule F E := (functional a).ker

theorem identity_not_mem (a : Parameters) : identity F ∉ hyperplane a := by
  change functional a (identity F) ≠ 0
  rw [functional_identity]
  exact one_ne_zero

theorem finrank_hyperplane (a : Parameters) : finrank F (hyperplane a) = 6 := by
  have hn : functional a ≠ 0 := by
    intro he
    have hh := LinearMap.congr_fun he (identity F)
    simp at hh
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  rw [finrank_traceZero] at hd
  change finrank F (hyperplane a) + 1 = 7 at hd
  omega

private theorem ambientPairing_surjective :
    Function.Surjective (normPolar : Carrier F →ₗ[F] Carrier F →ₗ[F] F) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := F) (V := Carrier F)).symm).mp
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  exact normPolar_nondegenerate (fun y => LinearMap.congr_fun hx y)

private theorem functional_coordinates {x : Carrier F} (hx : trace x = 1) :
    functional (coordinates x) = (normPolar x).comp (TraceZero F).subtype := by
  ext y
  change normPolar (representative (coordinates x)) y.val = normPolar x y.val
  rw [representative_coordinates hx, map_add, LinearMap.add_apply,
    map_smul, LinearMap.smul_apply, polar_unit]
  rw [show trace y.val = 0 from y.property, smul_zero, add_zero]

/-- Every off-scalar hyperplane is the kernel of one of the affine coordinates. -/
theorem exists_hyperplane (U : Submodule F E)
    (hU : finrank F U = 6) (hi : identity F ∉ U) :
    ∃ a : Parameters, hyperplane a = U := by
  obtain ⟨f, hf, hUf⟩ := U.exists_le_ker_of_notMem hi
  have hf1 : f (identity F) = 1 :=
    (by decide +kernel : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hf
  obtain ⟨l, hl⟩ := LinearMap.dualMap_surjective_of_injective
    (TraceZero F).injective_subtype f
  obtain ⟨x, rfl⟩ := ambientPairing_surjective l
  have hx : trace x = 1 := by
    have hh := LinearMap.congr_fun hl (identity F)
    change normPolar x unit = f (identity F) at hh
    rw [normPolar_symm, polar_unit] at hh
    exact hh.trans hf1
  refine ⟨coordinates x, ?_⟩
  have he : functional (coordinates x) = f := (functional_coordinates hx).trans hl
  change (functional (coordinates x)).ker = U
  rw [he]
  apply (Submodule.eq_of_le_of_finrank_eq hUf ?_).symm
  have hn : f ≠ 0 := by
    intro heq
    have hh := LinearMap.congr_fun heq (identity F)
    exact hf hh
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  rw [hU]
  rw [finrank_traceZero] at hd
  omega

theorem functional_injective : Function.Injective functional := by
  intro a b he
  have hp : ∀ y : E, normPolar (representative a - representative b) y.val = 0 := by
    intro y
    rw [map_sub, LinearMap.sub_apply]
    exact sub_eq_zero.mpr (LinearMap.congr_fun he y)
  obtain ⟨c, hc⟩ := (orthogonal_traceZero_iff F _).mp hp
  have hc0 : c = 0 := by
    have hh := congrFun hc 4
    simpa [representative, unit] using hh
  have hr : representative a = representative b := by
    apply sub_eq_zero.mp
    simpa [hc0] using hc.symm
  exact (coordinates_representative a).symm.trans
    ((congrArg coordinates hr).trans (coordinates_representative b))

/-- Canonical affine parameters determine distinct literal cover hyperplanes. -/
theorem hyperplane_injective : Function.Injective hyperplane := by
  intro a b he
  apply functional_injective
  ext v
  have hv : v - functional a v • identity F ∈ hyperplane a := by
    change functional a (v - functional a v • identity F) = 0
    simp
  rw [he] at hv
  change functional b (v - functional a v • identity F) = 0 at hv
  simpa using (sub_eq_zero.mp (by simpa using hv)).symm

/-- There are exactly 64 off-scalar hyperplanes in the seven-space. -/
theorem card_hyperplanes :
    Nat.card {U : Submodule F E // finrank F U = 6 ∧ identity F ∉ U} = 64 := by
  let e : Parameters ≃ {U : Submodule F E // finrank F U = 6 ∧ identity F ∉ U} :=
    Equiv.ofBijective (fun a => ⟨hyperplane a, finrank_hyperplane a, identity_not_mem a⟩)
      ⟨fun a b he => hyperplane_injective (congrArg Subtype.val he), by
        rintro ⟨U, hU, hi⟩
        obtain ⟨a, ha⟩ := exists_hyperplane U hU hi
        exact ⟨a, Subtype.ext ha⟩⟩
  rw [← Nat.card_congr e]
  simp [Parameters]

/-- The affine coordinate norm distinguishes the two source orbit candidates. -/
def normClass (a : Parameters) : F := SplitOctonion.norm (representative a)

theorem normClass_coordinates (a : Parameters) :
    normClass a = a 0 * a 5 + a 1 * a 4 + a 2 * a 3 := by
  simp [normClass, representative, SplitOctonion.norm]

theorem coordinates_add_scalar (x : Carrier F) (c : F) :
    coordinates (x + c • unit) = coordinates x := by
  funext i
  fin_cases i <;> simp [coordinates, unit]

/-- The action induced by the actual full octonion automorphism group. -/
def act (g : Model F) (a : Parameters) : Parameters :=
  coordinates (g.val (representative a))

theorem act_one (a : Parameters) : act 1 a = a := coordinates_representative a

theorem act_mul (g h : Model F) (a : Parameters) :
    act (g * h) a = act g (act h a) := by
  have ht : trace (h.val (representative a)) = 1 :=
    (automorphism_trace h _).trans (trace_representative a)
  change coordinates (g.val (h.val (representative a))) =
    coordinates (g.val (representative (coordinates (h.val (representative a)))))
  rw [representative_coordinates ht, map_add, map_smul, automorphism_unit,
    coordinates_add_scalar]

instance : MulAction (Model F) Parameters where
  smul := act
  one_smul := act_one
  mul_smul := act_mul

theorem functional_act (g : Model F) (a : Parameters) (v : E) :
    functional (act g a) (traceZeroAction F g v) = functional a v := by
  have ht : trace (g.val (representative a)) = 1 :=
    (automorphism_trace g _).trans (trace_representative a)
  change functional (coordinates (g.val (representative a))) _ = _
  rw [functional_coordinates ht]
  change normPolar (g.val (representative a)) (g.val v.val) =
    normPolar (representative a) v.val
  exact automorphism_normPolar g _ _

/-- Affine coordinates intertwine the literal image of a cover hyperplane. -/
theorem map_hyperplane (g : Model F) (a : Parameters) :
    (hyperplane a).map (traceZeroAction F g) = hyperplane (act g a) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    change functional (act g a) (traceZeroAction F g w) = 0
    exact (functional_act g a w).trans hw
  · intro hv
    refine ⟨traceZeroAction F g⁻¹ v, ?_, ?_⟩
    · have hh := functional_act g a (traceZeroAction F g⁻¹ v)
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
        map_one, Module.End.one_apply] at hh
      exact hh.symm.trans hv
    · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
        map_one, Module.End.one_apply]

private theorem norm_add_scalar_of_trace_one {x : Carrier F}
    (hx : trace x = 1) (c : F) :
    SplitOctonion.norm (x + c • unit) = SplitOctonion.norm x := by
  have hn : SplitOctonion.norm (c • unit : Carrier F) = c * c := by
    simp [SplitOctonion.norm, unit]
  have hp : normPolar x (c • unit) = c := by
    rw [normPolar_symm, map_smul, LinearMap.smul_apply, polar_unit, hx]
    simp
  rw [norm_add, hn, hp]
  have hc : c * c + c = 0 :=
    (by decide +kernel : ∀ t : ZMod 2, t * t + t = 0) c
  linear_combination hc

/-- The two affine norm classes are invariant under the full intended actor. -/
theorem normClass_act (g : Model F) (a : Parameters) :
    normClass (act g a) = normClass a := by
  have ht : trace (g.val (representative a)) = 1 :=
    (automorphism_trace g _).trans (trace_representative a)
  change SplitOctonion.norm
    (representative (coordinates (g.val (representative a)))) = _
  rw [representative_coordinates ht, norm_add_scalar_of_trace_one ht]
  exact automorphism_norm g _

end Atlas.G2.Natural.OrthogonalCover.Hyperplanes
