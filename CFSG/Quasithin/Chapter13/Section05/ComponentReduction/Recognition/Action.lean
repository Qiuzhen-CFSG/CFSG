module

public import CFSG.Quasithin.ChapterF.Section09.Basic
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupTheory.CommutatorPreimageFrattini
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# The faithful binary action on the original U_H/V₁

F.9.1 supplies relative normality of V₁ in U_H and the two-group property
of U_H. The proved Frattini bound Φ(U_H) ≤ V₁ therefore makes U_H/V₁
an elementary abelian two-group, even when U_H is nonabelian.

Conjugation on representatives constructs the H-action. Its kernel is
exactly the F.9 commutator kernel and hence O₂(H), giving a faithful
representation of the literal H/O₂(H). We identify U_H/V₁ with its actual
image in N_G(V₁)/V₁ and retain the quotient formula for that identification.
The image of V₃ = Vplus generates this module, by the original definition
U_H = ⟨V₃^H⟩. The final existence theorem discharges the quotient instances
from F.9.1; it does not assume commutativity of U_H.

The representative calculations follow the quotient-action pattern in
Chapter13/Section06/TerminalContradiction/Ratio/QuotientAction.lean, while
the new Frattini argument supplies the nonabelian source application.
No irreducibility, natural-module recognition or splitting is asserted.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
F.9.1–2, printed pp.317–318, Notation 13.5.8, printed p.918, and
Lemma 13.5.21, printed pp.923–924 (PDF pp.940–941).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Action
open Section08.Source
variable {G : Type*} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)

include h

theorem point_normal : (D.V₁.subgroupOf D.UH).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((h.UH_le_H.trans h.H_centralizes).trans (Subgroup.centralizer_le_normalizer _))

variable [(D.V₁.subgroupOf D.UH).Normal]

omit h in
local instance : (D.V₁.subgroupOf D.g2.G₁).Normal := D.g2.point_normal

abbrev ModuleGroup := D.UH ⧸ D.V₁.subgroupOf D.UH
abbrev Space := Additive (ModuleGroup D)

theorem quotient_elementary : IsElementaryAbelian 2 (ModuleGroup D) := by
  have hp : IsPGroup 2 D.UH := h.g2_hypothesis.U_isPGroup
  exact elementary_quotient_of_frattini_le hp (D.V₁.subgroupOf D.UH)
    (fun x hx => h.frattini_UH_le_point (mem_map_of_mem D.UH.subtype hx))

omit [(D.V₁.subgroupOf D.UH).Normal] in
theorem UH_le_ambient : D.UH ≤ D.g2.G₁ :=
  (h.UH_le_H.trans h.H_centralizes).trans (Subgroup.centralizer_le_normalizer _)

/-- The natural inclusion in the book's ambient quotient N_G(V₁)/V₁. -/
def tildeMap : ModuleGroup D →* D.Tilde :=
  QuotientGroup.map (D.V₁.subgroupOf D.UH) (D.V₁.subgroupOf D.g2.G₁)
    (inclusion (UH_le_ambient D h)) (fun _ hu => hu)

theorem tildeMap_injective : Function.Injective (tildeMap D h) := by
  apply (tildeMap D h).ker_eq_bot_iff.mp
  ext q
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (D.V₁.subgroupOf D.UH) q
  change QuotientGroup.mk' (D.V₁.subgroupOf D.g2.G₁)
    (inclusion (UH_le_ambient D h) u) = 1 ↔
      QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u = 1
  constructor
  · intro hu
    have hm := (QuotientGroup.eq_one_iff (N := D.V₁.subgroupOf D.g2.G₁)
      (inclusion (UH_le_ambient D h) u)).mp hu
    exact (QuotientGroup.eq_one_iff u).mpr hm
  · intro hu
    exact (QuotientGroup.eq_one_iff _).mpr ((QuotientGroup.eq_one_iff u).mp hu)

theorem tildeMap_mem (u : ModuleGroup D) : tildeMap D h u ∈ D.tilde D.UH := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (D.V₁.subgroupOf D.UH) u
  exact mem_map.mpr ⟨inclusion (UH_le_ambient D h) u,
    u.property, rfl⟩

/-- Identify U_H/V₁ with its literal image, retaining the original quotient map. -/
noncomputable def tildeEquiv : ModuleGroup D ≃* D.tilde D.UH :=
  MulEquiv.ofBijective ((tildeMap D h).codRestrict _ (tildeMap_mem D h))
    ⟨fun _ _ he => tildeMap_injective D h (congrArg Subtype.val he), by
      rintro ⟨x, y, hy, rfl⟩
      refine ⟨QuotientGroup.mk' (D.V₁.subgroupOf D.UH) ⟨y, hy⟩, ?_⟩
      apply Subtype.ext
      rfl⟩

theorem tildeEquiv_mk (u : D.UH) :
    (tildeEquiv D h (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u) : D.Tilde) =
      QuotientGroup.mk' (D.V₁.subgroupOf D.g2.G₁)
        (inclusion (UH_le_ambient D h) u) := rfl

noncomputable def quotientAction : D.H →* MulAut (ModuleGroup D) :=
  (exists_quotient_conjugation_action D.H D.UH D.V₁
    (le_normalizer_conjugateSpanBy D.Vplus D.H)
    (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    (point_normal D h)).choose

theorem quotientAction_apply (x : D.H) (u : D.UH) :
    quotientAction D h x (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u) =
      QuotientGroup.mk' (D.V₁.subgroupOf D.UH)
        ⟨x.val * u.val * x.val⁻¹,
          le_normalizer_iff.mp (le_normalizer_conjugateSpanBy D.Vplus D.H)
            x.val x.property u.val u.property⟩ :=
  (exists_quotient_conjugation_action D.H D.UH D.V₁
    (le_normalizer_conjugateSpanBy D.Vplus D.H)
    (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    (point_normal D h)).choose_spec x u

variable [IsElementaryAbelian 2 (ModuleGroup D)]

noncomputable def representation : Representation (ZMod 2) D.H (Space D) where
  toFun x := (quotientAction D h x).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext u
    change Additive.ofMul (quotientAction D h 1 u.toMul) = u
    rw [map_one]
    rfl
  map_mul' x y := by
    ext u
    change Additive.ofMul (quotientAction D h (x * y) u.toMul) = _
    rw [map_mul]
    rfl

theorem representation_apply (x : D.H) (u : D.UH) :
    representation D h x
      (Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u)) =
    Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH)
      ⟨x.val * u.val * x.val⁻¹,
        le_normalizer_iff.mp (le_normalizer_conjugateSpanBy D.Vplus D.H)
          x.val x.property u.val u.property⟩) :=
  congrArg Additive.ofMul (quotientAction_apply D h x u)

theorem mem_ker_iff (x : D.H) :
    x ∈ (representation D h).ker ↔ ∀ u ∈ D.UH, ⁅(x : G), u⁆ ∈ D.V₁ := by
  constructor
  · intro hx u hu
    have he := congrArg (fun f => f (Additive.ofMul
      (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) ⟨u, hu⟩))) hx
    rw [representation_apply] at he
    have hm := QuotientGroup.eq_iff_div_mem.mp (Additive.ofMul.injective he)
    simpa only [mem_subgroupOf, coe_div, coe_mul, coe_inv, div_eq_mul_inv,
      commutatorElement_def] using hm
  · intro hx
    apply LinearMap.ext
    intro w
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (D.V₁.subgroupOf D.UH) w.toMul
    have he : Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u) = w :=
      congrArg Additive.ofMul hu
    rw [← he, representation_apply]
    apply congrArg Additive.ofMul
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa only [mem_subgroupOf, coe_div, coe_mul, coe_inv, div_eq_mul_inv,
      commutatorElement_def] using hx u u.property

theorem kernel_eq_twoCore : (representation D h).ker = pCore 2 D.H := by
  have he : (representation D h).ker.map D.H.subtype = h.kernel D.UH := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      apply (h.mem_kernel_iff h.UH_le_H).mpr
      refine ⟨y.property, fun u hu => ?_⟩
      simpa only [Subgroup.subtype_apply, commutatorElement_inv] using
        D.V₁.inv_mem ((mem_ker_iff D h y).mp hy u hu)
    · intro x hx
      obtain ⟨hxH, hx⟩ := (h.mem_kernel_iff h.UH_le_H).mp hx
      refine ⟨⟨x, hxH⟩, (mem_ker_iff D h _).mpr ?_, rfl⟩
      intro u hu
      simpa only [commutatorElement_inv] using D.V₁.inv_mem (hx u hu)
  exact map_injective D.H.subtype_injective (he.trans h.kernel_UH_eq_QH)

noncomputable def starRepresentation :
    Representation (ZMod 2) (Hstar D.H) (Space D) :=
  QuotientGroup.lift (pCore 2 D.H) (representation D h) (kernel_eq_twoCore D h).ge

theorem starRepresentation_mk (x : D.H) :
    starRepresentation D h (QuotientGroup.mk' (pCore 2 D.H) x) =
      representation D h x := QuotientGroup.lift_mk _ _ x

theorem starRepresentation_injective : Function.Injective (starRepresentation D h) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (kernel_eq_twoCore D h).symm

theorem starRepresentation_apply (x : D.H) (u : D.UH) :
    starRepresentation D h (QuotientGroup.mk' (pCore 2 D.H) x)
      (Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u)) =
    Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH)
      ⟨x.val * u.val * x.val⁻¹,
        le_normalizer_iff.mp (le_normalizer_conjugateSpanBy D.Vplus D.H)
          x.val x.property u.val u.property⟩) := by
  rw [starRepresentation_mk, representation_apply]

noncomputable def seedSpace : Submodule (ZMod 2) (Space D) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup
    ((D.Vplus.subgroupOf D.UH).map (QuotientGroup.mk' (D.V₁.subgroupOf D.UH))))

theorem seedSpace_generates (W : Subrepresentation (starRepresentation D h))
    (hseed : seedSpace D ≤ W.toSubmodule) : W = ⊤ := by
  let π := QuotientGroup.mk' (D.V₁.subgroupOf D.UH)
  let J : Subgroup D.UH :=
    (Subgroup.toAddSubgroup.symm W.toSubmodule.toAddSubgroup).comap π
  let B := J.map D.UH.subtype
  have hVB : D.Vplus ≤ B := by
    intro v hv
    let u : D.UH := ⟨v, le_conjugateSpanBy D.Vplus D.H hv⟩
    refine ⟨u, ?_, rfl⟩
    apply hseed
    exact ⟨u, hv, rfl⟩
  have hHB : D.H ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    rintro x hx b ⟨u, hu, rfl⟩
    let v : D.UH := ⟨x * u.val * x⁻¹,
      le_normalizer_iff.mp (le_normalizer_conjugateSpanBy D.Vplus D.H)
        x hx u.val u.property⟩
    refine ⟨v, ?_, rfl⟩
    change Additive.ofMul (π v) ∈ W
    rw [← starRepresentation_apply D h ⟨x, hx⟩ u]
    exact W.apply_mem_toSubmodule _ hu
  have hUB : D.UH ≤ B := conjugateSpanBy_le hVB hHB
  apply top_unique
  intro v _
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (D.V₁.subgroupOf D.UH) v.toMul
  obtain ⟨w, hw, hwu⟩ := hUB u.property
  have hwue : w = u := Subtype.ext hwu
  subst w
  change Additive.ofMul (π u) ∈ W at hw
  simpa [π, hu] using hw

omit [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (ModuleGroup D)] in
/-- The F.9.1 application supplies all quotient instances and a faithful
action with its actual generating seed. No commutativity of U_H is assumed. -/
theorem exists_source_action :
    letI := point_normal D h
    letI := quotient_elementary D h
    ∃ ρ : Representation (ZMod 2) (Hstar D.H) (Space D),
      Function.Injective ρ ∧
      (∀ (x : D.H) (u : D.UH),
        ρ (QuotientGroup.mk' (pCore 2 D.H) x)
          (Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u)) =
        Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH)
          ⟨x.val * u.val * x.val⁻¹,
            le_normalizer_iff.mp (le_normalizer_conjugateSpanBy D.Vplus D.H)
              x.val x.property u.val u.property⟩)) ∧
      ∀ W : Subrepresentation ρ, seedSpace D ≤ W.toSubmodule → W = ⊤ := by
  let := point_normal D h
  let := quotient_elementary D h
  exact ⟨starRepresentation D h, starRepresentation_injective D h,
    starRepresentation_apply D h, seedSpace_generates D h⟩

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Action

end
