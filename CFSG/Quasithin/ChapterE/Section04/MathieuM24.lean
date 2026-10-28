module

public import CFSG.Quasithin.ChapterE.Section04.MathieuM24.GeneratingFamily
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.Mathieu.M24.Properties.OuterRestriction
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.Mathieu.M24.ValueBoundParabolics.Transport
public import Theory.Mathieu.M24.ValueBoundParabolics.Construction
public import Theory.Mathieu.M24.ValueBoundParabolics.CentralCover

/-!
# The M₂₄ generating family in E.4.3

Every automorphism of the concrete M₂₄ is inner. Perfectness detects innerness
through the central quotient of the quasisimple generalized Fitting subgroup
L. Hence G = L C_G(L), and self-centralization of F*(G) gives G = L. In
particular the Sylow-generation hypothesis of E.4.2 holds without first
identifying the central cover with M₂₄.

The ambient two-core hypothesis passes to L. The central-cover theorem then
eliminates its center, giving an actual isomorphism G ≃ M₂₄. Sylow conjugacy
transports the certified native generating triple of order-3072 overgroups
to overgroups of the specified T. Their intrinsic two-core quotients are S₃,
and their finite family satisfies the local condition with budget at most
three. This completes the M₂₄ group-theoretic input to E.4.2; the resulting
representation bound is assembled separately by the section owner.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.4.3(2),
printed pp. 241–242 (PDF pp. 252–253).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValueBound
variable {G : Type*} [Group G] [Finite G]

/-- Innerness on the actual M₂₄ central quotient forces the generalized
Fitting subgroup to be the whole ambient group. -/
theorem m24_generalizedFitting_eq_top (hL : IsQuasisimple (generalizedFitting G))
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* Sporadic.Mathieu.M24) :
    generalizedFitting G = ⊤ := by
  let L := generalizedFitting G
  let : IsQuasisimple L := hL
  apply top_unique
  intro g _
  obtain ⟨a, ha⟩ := Sporadic.Mathieu.M24OuterRestriction.conj_surjective
    (MulAut.centralQuotientAction e (MulAut.conjNormal g : MulAut L))
  obtain ⟨l, hl⟩ := (MulAut.centralQuotientAction_inner_iff e
    (MulAut.conjNormal g : MulAut L)).mp ⟨a, ha.symm⟩
  have hc : (l : G)⁻¹ * g ∈ centralizer (L : Set G) := by
    intro x hx
    have he := congrArg Subtype.val (DFunLike.congr_fun hl ⟨x, hx⟩)
    change g * x * g⁻¹ = (l : G) * x * (l : G)⁻¹ at he
    have he' : g * x = (l : G) * x * (l : G)⁻¹ * g := by
      calc
        g * x = (g * x * g⁻¹) * g := by group
        _ = _ := by rw [he]
    calc
      x * ((l : G)⁻¹ * g) = (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹ * g) := by group
      _ = (l : G)⁻¹ * (g * x) := by rw [he']
      _ = ((l : G)⁻¹ * g) * x := by group
  have hmem := ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le hc
  simpa only [mul_inv_cancel_left] using L.mul_mem l.property hmem

/-- The M₂₄ case satisfies the ambient generation hypothesis of E.4.2. -/
theorem m24_component_sup_sylow (hL : IsQuasisimple (generalizedFitting G))
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* Sporadic.Mathieu.M24)
    (T : Sylow 2 G) : generalizedFitting G ⊔ (T : Subgroup G) = ⊤ := by
  rw [m24_generalizedFitting_eq_top hL e, top_sup_eq]

/-- Once the cover kernel is eliminated, the ambient group is actually
isomorphic to the fixed Witt-design M₂₄. -/
theorem m24_ambient_equiv_of_center_eq_bot (hL : IsQuasisimple (generalizedFitting G))
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* Sporadic.Mathieu.M24)
    (hc : center (generalizedFitting G) = ⊥) : Nonempty (G ≃* Sporadic.Mathieu.M24) := by
  let d : generalizedFitting G ≃* G :=
    (MulEquiv.subgroupCongr (m24_generalizedFitting_eq_top hL e)).trans Subgroup.topEquiv
  exact ⟨d.symm.trans ((QuotientGroup.quotientBot (G := generalizedFitting G)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hc.symm).trans e))⟩

/-- Assembly for a specified native triple and trivial central-cover kernel.
The unconditional construction below supplies both inputs. -/
theorem m24_generating_family_of_center_eq_bot_and_native_triple
    (hL : IsQuasisimple (generalizedFitting G))
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* Sporadic.Mathieu.M24)
    (hc : center (generalizedFitting G) = ⊥) (T : Sylow 2 G)
    (P : Fin 3 → Subgroup Sporadic.Mathieu.M24)
    (hle : ∀ i, Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.candidate ≤ P i)
    (hcard : ∀ i, Nat.card (P i) = 3072) (hgen : ⨆ i, P i = ⊤) :
    ∃ Δ : Finset (Subgroup G), IsGeneratingFamily T Δ ∧ localRankBudget Δ ≤ 3 ∧
      ∀ H ∈ Δ, H < ⊤ := by
  obtain ⟨d⟩ := m24_ambient_equiv_of_center_eq_bot hL e hc
  obtain ⟨R, hT, hR, hproper, hquot⟩ :=
    Sporadic.Mathieu.M24ValueBoundParabolics.transport_native_triple d T P hle hcard hgen
  exact generating_family_of_three_symmetric_quotients T R hT hR hquot hproper

/-- Under the standing trivial-two-core hypothesis, the M₂₄ central quotient
identifies the actual ambient group with M₂₄. -/
theorem m24_ambient_equiv (hcore : pCore 2 G = ⊥)
    (hL : IsQuasisimple (generalizedFitting G))
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* Sporadic.Mathieu.M24) :
    Nonempty (G ≃* Sporadic.Mathieu.M24) := by
  let : IsQuasisimple (generalizedFitting G) := hL
  apply m24_ambient_equiv_of_center_eq_bot hL e
  apply Sporadic.Mathieu.M24ValueBoundParabolics.center_eq_bot_of_twoCore_eq_bot ?_ e
  apply (map_eq_bot_iff_of_injective _ (generalizedFitting G).subtype_injective).mp
  apply le_bot_iff.mp
  rw [← hcore]
  exact le_sSup ⟨inferInstance, pCore_isPGroup.map (generalizedFitting G).subtype⟩

/-- Three actual proper overgroups of the prescribed Sylow subgroup generate
G, with each quotient by its intrinsic two-core isomorphic to S₃. -/
theorem m24_sylow_overgroups (hcore : pCore 2 G = ⊥)
    (hL : IsQuasisimple (generalizedFitting G))
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* Sporadic.Mathieu.M24)
    (T : Sylow 2 G) :
    ∃ P : Fin 3 → Subgroup G, (∀ i, (T : Subgroup G) ≤ P i) ∧
      (⨆ i, P i) = ⊤ ∧ (∀ i, P i < ⊤) ∧
      (∀ i, Nonempty ((P i ⧸ pCore 2 (P i)) ≃* Equiv.Perm (Fin 3))) := by
  obtain ⟨d⟩ := m24_ambient_equiv hcore hL e
  obtain ⟨P, hle, hcard, hgen⟩ :=
    Sporadic.Mathieu.M24ValueBoundParabolics.exists_native_triple
  exact Sporadic.Mathieu.M24ValueBoundParabolics.transport_native_triple
    d T P hle hcard hgen

/-- The M₂₄ generating-family conclusion used in E.4.3(2), with every
central-cover and native-generation premise discharged. -/
theorem m24_generating_family (hcore : pCore 2 G = ⊥)
    (hL : IsQuasisimple (generalizedFitting G))
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* Sporadic.Mathieu.M24)
    (T : Sylow 2 G) :
    ∃ Δ : Finset (Subgroup G), IsGeneratingFamily T Δ ∧ localRankBudget Δ ≤ 3 ∧
      ∀ H ∈ Δ, H < ⊤ := by
  obtain ⟨P, hT, hgen, hproper, hquot⟩ := m24_sylow_overgroups hcore hL e T
  exact generating_family_of_three_symmetric_quotients T P hT hgen hquot hproper

end CFSG.Quasithin.ChapterE.ValueBound
