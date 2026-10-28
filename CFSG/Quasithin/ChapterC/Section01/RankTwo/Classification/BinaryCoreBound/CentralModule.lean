module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Head
public import Stellmacher.OmegaOneCenterMap
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction

/-!
# The central elementary module in a binary MS group

Characteristic two puts the center of the radical inside the two-core. Thus
its nontrivial omega center lies in the omega center of the core. If the
component fixed that entire module, the product decomposition would make the
radical's omega center central in J, contradicting (MS3).

Source: Aschbacher–Smith, C.1.31–32, printed pp.135–136. This proves actual
noncentrality. Faithfulness modulo the two-core and the construction of an
FF-offender are further steps, and no conclusion about the center of the
commutator core is inferred merely from this module.
-/

public section
namespace CFSG.Quasithin.ChapterC.BinaryMS
open Subgroup Stellmacher
universe u
variable (J : Type u) [Group J]

/-- Ω₁Z(O₂(J)), with both intrinsic subtype maps into J explicit. -/
@[expose] noncomputable def centralModule : Subgroup J := omegaOneCenterAmbient (pCore 2 J)

/-- The central module is elementary abelian. -/
theorem centralModule_elementary : IsElementaryAbelian 2 (centralModule J) :=
  omegaOneCenterAmbient_elementaryAbelian _

/-- The central module is normal in its actual ambient group. -/
theorem centralModule_normal : (centralModule J).Normal := by
  let : (omega₁ (center (pCore 2 J)) (p := 2)).Characteristic := omega₁_characteristic _
  change (((omega₁ (center (pCore 2 J)) (p := 2)).map
    (center (pCore 2 J)).subtype).map (pCore 2 J).subtype).Normal
  infer_instance

/-- Membership has the literal central involution interpretation. -/
theorem mem_centralModule (x : J) : x ∈ centralModule J ↔
    x ∈ pCore 2 J ∧ x ^ 2 = 1 ∧ ∀ n ∈ pCore 2 J, n * x = x * n :=
  mem_omegaOneCenterAmbient_iff _ _

variable {J} [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R)
include h

/-- The radical omega center embeds into the actual core's omega center. -/
theorem Input.radicalOmega_le_centralModule : omegaOneCenterAmbient R ≤ centralModule J := by
  intro x hx
  obtain ⟨_, hx2, hxc⟩ := (mem_omegaOneCenterAmbient_iff R x).mp hx
  have hc : x ∈ centralizer (pCore 2 J : Set J) :=
    fun n hn => hxc n (h.radical.twoCore_le hn)
  exact (mem_centralModule J x).mpr ⟨h.core_selfCentralizing hc, hx2, hc⟩

/-- (MS3) forces a genuinely nontrivial component action on Ω₁Z(O₂(J)). -/
theorem Input.component_not_centralizes : ¬ L ≤ centralizer (centralModule J : Set J) := by
  intro hc
  let C : Subgroup R := (omega₁ (center R) (p := 2)).map (center R).subtype
  let : (omega₁ (center R) (p := 2)).Characteristic := omega₁_characteristic _
  let : C.Characteristic := inferInstance
  let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr h.radical_ne_bot
  have hCne : C ≠ ⊥ := omega_center_ne_bot h.radical.isPGroup
  have hCcentral : C.map R.subtype ≤ center J := by
    intro x hx
    have hxR : x ∈ omegaOneCenterAmbient R := hx
    have hxV : x ∈ centralModule J := h.radicalOmega_le_centralModule hxR
    have hxcent := (mem_omegaOneCenterAmbient_iff R x).mp hxR |>.2.2
    apply mem_center_iff.mpr
    intro j
    obtain ⟨l, hl, r, hr, rfl⟩ := h.product j
    calc
      l * r * x = l * (r * x) := mul_assoc _ _ _
      _ = l * (x * r) := by rw [hxcent r hr]
      _ = (l * x) * r := (mul_assoc _ _ _).symm
      _ = (x * l) * r := by rw [hc hl x hxV]
      _ = x * (l * r) := mul_assoc _ _ _
  apply h.characteristic C inferInstance hCne
  constructor
  intro x hx j
  rw [mem_center_iff.mp (hCcentral hx) j, mul_inv_cancel_right]
  exact hx

/-- In particular this actual central module is nontrivial. -/
theorem Input.centralModule_ne_bot : centralModule J ≠ ⊥ := by
  intro hv
  apply h.component_not_centralizes
  intro l _ x hx
  have hx1 : x = 1 := by
    have hx' : x ∈ (⊥ : Subgroup J) := by rw [← hv]; exact hx
    exact hx'
  simp only [hx1, one_mul, mul_one]

end CFSG.Quasithin.ChapterC.BinaryMS
