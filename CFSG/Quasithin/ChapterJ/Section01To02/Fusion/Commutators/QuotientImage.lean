module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Statements
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Commutators.QuotientMaps
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Commutators.QuotientImage.Invariance
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Commutators.QuotientImage.Nontriviality
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Commutators.QuotientImage.CubicAction
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.FixedPlane

/-!
# The conditional quotient-image argument in J.2.4(1)

The central product writes h = bu with b in C_Q(B), u in U, and b outside
U. The quotient commutator row is unchanged by u. Cubic irreducibility on
R₁/S and J.2.3(8) force C_R₁(b) ≤ S. The index-four obstruction then makes
the row nontrivial, and its K-invariance and the inherited natural action
force its range to be the full literal image of U in H/Z.

The marked point-parabolic construction supplies CubicQuotientData, including
the actual index |Q : Q ∩ S| = 4. The final theorem also discharges R₁ = QS
and Q ≤ K using J.2.2(1), and [HC,K] ≤ U using the fixed-plane proof of
J.2.2(3). It retains only CentralProductData and the exact fixed-subgroup
implication C_{S/V}(R₁) ≤ U/V from J.2.3(8). Their producers are the
central-decomposition branch and `qt-j12-special-core`, respectively.
The final J.2.4 assembly belongs to `qt-j12-fusion-commutators`, whose
`Fusion.sourceJ24_of_centralProduct_of_modZ` consumes this literal image
equality. Thus no cubic action, index, invariance or nontriviality premise
remains in `modZ_commutator_eq_of_centralProduct`.

Source: Aschbacher–Smith, Lemma J.2.4(1), printed p.434 (PDF p.445),
with the earlier J.2.1–3 structure on printed pp.432–434.
-/

public section
noncomputable section
open Subgroup
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.ChapterJ.Fusion
variable {G : Type*} [Group G] [Finite G]

/-- The J.2.4(1) deduction with the marked cubic action and earlier-source
conclusions explicit. The theorem below supplies that action and the J.2.2
conclusions from the actual local setup. -/
theorem modZ_commutator_eq_of_cubic (d : LocalSetup G)
    (B : Sylow 3 d.toTypeRuSetup.L₁) (cp : CentralProductData d.toTypeRuSetup B)
    (cubic : CubicQuotientData d B)
    (hR : d.toTypeRuSetup.R₁ = d.toTypeRuSetup.Q ⊔ d.toTypeRuSetup.S)
    (hQK : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.K)
    (hCK : ⁅d.toTypeRuSetup.HC,d.toTypeRuSetup.K⁆ ≤ d.toTypeRuSetup.U)
    (hfixed : ∀ s ∈ d.toTypeRuSetup.S,
      (∀ r ∈ d.toTypeRuSetup.R₁, ⁅r,s⁆ ∈ d.V) → s ∈ d.toTypeRuSetup.U) :
    ∀ h : G, ∀ hh : h ∈ d.toTypeRuSetup.HC, h ∉ d.toTypeRuSetup.U →
      ⁅zpowers (centerQuotientMap d.toTypeRuSetup ⟨h,hh.1⟩),
        modZ d.toTypeRuSetup d.toTypeRuSetup.Q⁆ =
        modZ d.toTypeRuSetup d.toTypeRuSetup.U := by
  let D := d.toTypeRuSetup
  let : IsElementaryAbelian 2 D.U := d.elementary_U
  have hCQ : ⁅D.HC,D.Q⁆ ≤ D.U := (commutator_mono le_rfl hQK).trans hCK
  have hUQ : ⁅D.U,D.Q⁆ ≤ D.Z := by
    rw [commutator_comm]
    exact D.commutator_Q_U_le_Z
  have hBHC : HB D B ≤ D.HC := by rw [cp.product_eq]; exact le_sup_left
  have hBU : HB D B ≤ centralizer (D.U : Set G) := hBHC.trans inf_le_right
  intro h hh hn
  have hp : h ∈ (↑(HB D B) : Set G) * (↑D.U : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right (HB D B) D.U
      (hBU.trans (Subgroup.centralizer_le_normalizer _)), ← cp.product_eq]
    exact hh
  obtain ⟨b,hb,u,hu,he⟩ := hp
  have hbnot : b ∉ D.U := by
    intro hbU
    exact hn (he ▸ D.U.mul_mem hbU hu)
  have hbC := hBHC hb
  have hcR := centralizer_R₁_le_S_of_cubic d B cubic hR hfixed b hb hbC hbnot
  have hQR : D.Q ≤ D.R₁ := by rw [hR]; exact le_sup_left
  have hcQ : D.Q ⊓ centralizer ({b} : Set G) ≤ D.S :=
    (inf_le_inf_right _ hQR).trans hcR
  have hbfull := modZ_commutator_eq_of_ne_bot D hQK hCK ⟨b,hbC⟩
    (modZ_commutator_ne_bot_of_index D d.card_Z cubic.index ⟨b,hbC⟩ hcQ)
  have hrow : commutatorRow D d.U_le_HC hCQ hUQ ⟨h,hh⟩ =
      commutatorRow D d.U_le_HC hCQ hUQ ⟨b,hbC⟩ := by
    have he' : (⟨h,hh⟩ : D.HC) =
        ⟨b * u,D.HC.mul_mem hbC (d.U_le_HC hu)⟩ := Subtype.ext he.symm
    rw [he']
    exact commutatorRow_mul_U D d.U_le_HC hCQ hUQ ⟨b,hbC⟩ ⟨u,hu⟩
  rw [← commutatorRow_range D d.U_le_HC hCQ hUQ ⟨h,hh⟩,
    hrow, commutatorRow_range D d.U_le_HC hCQ hUQ ⟨b,hbC⟩]
  exact hbfull

/-- J.2.4(1) from the central decomposition and the literal J.2.3(8)
fixed-subgroup conclusion. The marked cubic action, index four and all
J.2.2 inputs are derived from the actual local setup. -/
theorem modZ_commutator_eq_of_centralProduct (d : LocalSetup G)
    (B : Sylow 3 d.toTypeRuSetup.L₁) (cp : CentralProductData d.toTypeRuSetup B)
    (hfixed : ∀ s ∈ d.toTypeRuSetup.S,
      (∀ r ∈ d.toTypeRuSetup.R₁, ⁅r,s⁆ ∈ d.V) → s ∈ d.toTypeRuSetup.U) :
    ∀ h : G, ∀ hh : h ∈ d.toTypeRuSetup.HC, h ∉ d.toTypeRuSetup.U →
      ⁅zpowers (centerQuotientMap d.toTypeRuSetup ⟨h,hh.1⟩),
        modZ d.toTypeRuSetup d.toTypeRuSetup.Q⁆ =
        modZ d.toTypeRuSetup d.toTypeRuSetup.U := by
  apply modZ_commutator_eq_of_cubic d B cp (cubicQuotientData d B)
    (d.parabolic_core_eq_R₁.symm.trans d.Q_sup_S_eq_parabolic_core.symm)
    d.Q_le_K _ hfixed
  rw [commutator_comm]
  exact commutator_le.mpr fun k hk c hc => d.HC_commutator_K_mem_U ⟨c,hc⟩ ⟨k,hk⟩

end CFSG.Quasithin.ChapterJ.Fusion
