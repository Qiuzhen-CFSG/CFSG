module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.EffectiveSections
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorLevi
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.CoreCommutators
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.PanelKernel
public import Theory.GroupTheory.PCoreFrattiniAction

/-!
# Effective radical modules on the same marked quotient

The complementary intersection V = U ∩ U^s is the actual endpoint two-core
once the earlier panel-kernel containment holds. Local characteristic two
and the Burnside Frattini-kernel theorem show that the whole endpoint action
on V/Φ(V) has kernel exactly V. Its restriction to the root-generated
rank-one group is faithful: the opposite Levi intersects U in the simple
root, and that root meets V trivially.

This supplies the actual effective radical action used in Fong--Seitz I
(5F)(a), pp.27--28, and the first module in the proof of (6H), p.52.
The original F.1.1 consumer supplies local characteristic two; no simplicity,
perfectness, field synchronization, or module recognition is assumed. The
same argument includes the binary endpoints. Effectivity on the derived
radical and the later centralizer estimates remain separate proof steps.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)

private theorem core_le_unipotent : (Endpoint Q i).pCoreIn 2 ≤ split.U := by
  rintro x ⟨y,hy,rfl⟩
  exact pCore_isPGroup.le_sylow_of_normal
    (split.sylow.subtype (split.U_le.trans (Q.tits.B_le_standardParabolic _))) hy

include hV in
theorem remainder_eq_endpoint_core :
    simpleRemainder Q split i = (Endpoint Q i).pCoreIn 2 :=
  QuadrangleStructure.remainder_eq_parabolic_core Q split i hV (core_le_unipotent Q split i)

def endpointRadicalAction : Endpoint Q i →* MulAut (simpleRemainder Q split i) :=
  (simpleRemainder Q split i).normalizerMonoidHom.comp
    (inclusion (remainder_parabolic_normalizes Q split i hV))

@[simp] theorem endpointRadicalAction_apply (g : Endpoint Q i) (v : simpleRemainder Q split i) :
    (endpointRadicalAction Q split i hV g v : X ⧸ Q.D) = (g : X ⧸ Q.D)*v*(g : X ⧸ Q.D)⁻¹ := rfl

def endpointFrattiniAction : Endpoint Q i →*
    MulAut ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i)) :=
  (quotientAut (frattini (simpleRemainder Q split i))).comp
    (endpointRadicalAction Q split i hV)

@[simp] theorem endpointFrattiniAction_mk (g : Endpoint Q i) (v : simpleRemainder Q split i) :
    endpointFrattiniAction Q split i hV g (QuotientGroup.mk v) =
      QuotientGroup.mk (endpointRadicalAction Q split i hV g v) :=
  quotientAut_apply_mk _ _ _

variable (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤
  pCore 2 (Endpoint Q i))

include hc in
/-- The full endpoint acts with precisely its actual two-core as kernel. -/
theorem endpointFrattiniAction_ker :
    (endpointFrattiniAction Q split i hV).ker =
      (simpleRemainder Q split i).subgroupOf (Endpoint Q i) := by
  let V := simpleRemainder Q split i
  let A := Endpoint Q i
  let a := endpointRadicalAction Q split i hV
  let f := endpointFrattiniAction Q split i hV
  have hVtwo : IsPGroup 2 V := split.isTwo.to_le inf_le_left
  have hCV : a.ker ≤ pCore 2 A := by
    intro g hg
    apply hc
    rw [mem_centralizer_iff]
    intro u hu
    have huV : (u : X ⧸ Q.D) ∈ V := by
      rw [show V = A.pCoreIn 2 from remainder_eq_endpoint_core Q split i hV]
      exact mem_map_of_mem A.subtype hu
    have he := congrArg (fun t : MulAut V => (t ⟨u,huV⟩ : X ⧸ Q.D)) hg
    change (g : X ⧸ Q.D)*u*(g : X ⧸ Q.D)⁻¹ = u at he
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp he).symm
  have hker : IsPGroup 2 f.ker :=
    (isPGroup_quotientAut_frattini_kernel hVtwo).comap_of_ker_isPGroup a
      (pCore_isPGroup.to_le hCV)
  have hle : f.ker ≤ pCore 2 A := le_sSup ⟨inferInstance,hker⟩
  apply le_antisymm
  · intro g hg
    change (g : X ⧸ Q.D) ∈ V
    rw [show V = A.pCoreIn 2 from remainder_eq_endpoint_core Q split i hV]
    exact mem_map_of_mem A.subtype (hle hg)
  · intro g hg
    let : Fact (IsPGroup 2 V) := ⟨hVtwo⟩
    let : IsElementaryAbelian 2 (V ⧸ frattini V) := isElementaryAbelian_quotient_frattini
    apply MulEquiv.ext
    intro v
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (frattini V) v
    change quotientAut (frattini V) (a g) (QuotientGroup.mk' (frattini V) x) = _
    rw [quotientAut_apply_mk]
    change QuotientGroup.mk' (frattini V)
      ((⟨g,hg⟩ : V)*x*(⟨g,hg⟩ : V)⁻¹) = QuotientGroup.mk' (frattini V) x
    rw [map_mul,map_mul,map_inv,mul_comm (QuotientGroup.mk' (frattini V) (⟨g,hg⟩ : V)),
      mul_inv_cancel_right]

include hc in
/-- The source R_i acts faithfully on the literal effective radical section. -/
theorem radical_effectiveAction_injective :
    Function.Injective (radicalSection Q split i hV).effectiveAction := by
  let d := radicalSection Q split i hV
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro r hr
  let g : Endpoint Q i := inclusion (rankOne_le_parabolic Q split i) r
  have hg : g ∈ (endpointFrattiniAction Q split i hV).ker := by
    apply MulEquiv.ext
    intro z
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (frattini d.numerator) z
    change quotientAut (frattini d.numerator) (d.numeratorAction r)
      (QuotientGroup.mk' (frattini d.numerator) x) = _
    rw [quotientAut_apply_mk]
    change QuotientGroup.mk' (frattini d.numerator) (d.numeratorAction r x) =
      QuotientGroup.mk' (frattini d.numerator) x
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hx : d.numeratorAction r x / x ∈ d.effectiveDenominator := by
      apply QuotientGroup.eq_iff_div_mem.mp
      exact (d.effectiveAction_mk r x).symm.trans
        (congrArg (fun t : MulAut d.EffectiveCarrier => t (QuotientGroup.mk x)) hr)
    have hd : d.effectiveDenominator = frattini d.numerator := by
      rw [d.effectiveDenominator_eq]
      exact sup_bot_eq _
    rw [hd] at hx
    exact hx
  rw [endpointFrattiniAction_ker Q split i hV hc] at hg
  have hrV : (r : X ⧸ Q.D) ∈ simpleRemainder Q split i := hg
  have hrU : (r : X ⧸ Q.D) ∈ simpleRoot Q split i := by
    rw [← UnitarySource.rootActor_inf_unipotent Q split i]
    exact ⟨r.property,hrV.1⟩
  exact Subtype.ext (disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) hrU hrV)

include hc in
/-- The faithful action is the existing binary representation of that section. -/
theorem radical_effectiveRepresentation_injective :
    Function.Injective (radicalSection Q split i hV).effectiveRepresentation :=
  (radicalSection Q split i hV).effectiveRepresentation_injective
    (radical_effectiveAction_injective Q split i hV hc)

include hc in
theorem radical_isEffective : (radicalSection Q split i hV).IsEffective := by
  unfold RootSection.IsEffective
  rw [(MonoidHom.ker_eq_bot_iff _).mpr (radical_effectiveAction_injective Q split i hV hc)]
  exact bot_le

include hc in
/-- Faithfulness also holds on the actual radical abelianization used on p.52. -/
theorem radical_abelianizationAction_injective :
    Function.Injective (radicalQuotientAction Q split i hV) := by
  intro r t he
  let d := radicalSection Q split i hV
  apply radical_effectiveAction_injective Q split i hV hc
  ext z
  induction z using QuotientGroup.induction_on with
  | H x =>
    rw [d.effectiveAction_mk, d.effectiveAction_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hh : Abelianization.of (radicalAction Q split i hV r x) =
        Abelianization.of (radicalAction Q split i hV t x) :=
      (radicalQuotientAction_of Q split i hV r x).symm.trans
        ((congrArg (fun f : MulAut (RadicalQuotient Q split i) =>
          f (Abelianization.of (x : simpleRemainder Q split i))) he).trans
            (radicalQuotientAction_of Q split i hV t x))
    have hd : radicalAction Q split i hV r x / radicalAction Q split i hV t x ∈
        commutator (simpleRemainder Q split i) := QuotientGroup.eq_iff_div_mem.mp hh
    let : Fact (IsPGroup 2 d.numerator) := ⟨d.isTwo⟩
    apply (show frattini d.numerator ≤ d.effectiveDenominator from by
      rw [d.effectiveDenominator_eq]; exact le_sup_left)
    change (radicalSection Q split i hV).numeratorAction r x /
      (radicalSection Q split i hV).numeratorAction t x ∈ frattini d.numerator
    rw [radicalSection_numeratorAction_apply Q split i hV r x,
      radicalSection_numeratorAction_apply Q split i hV t x]
    exact commutator_le_frattini_of_isPGroup (p := 2) hd


end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
