module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Statements
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Elementary
public import Theory.GroupTheory.QuaternionElementaryProduct

/-!
# The omega, Frattini and elementary-fusion clause of J.2.6

The quaternion decomposition HC = C_Q(B)U identifies every involution of HC
with an element of U. Its Frattini subgroup is the common subgroup Z. The
earlier natural-action fusion proof sends all nonidentity elements of U to z.

The decomposition remains an explicit premise, to be constructed by the
J.2.4 branch from J.2.1–3. It is not an additional type-Ru hypothesis and
this conditional theorem does not assert completion of J.2.6.

Source: Aschbacher–Smith, J.2.6(4), printed p.434 (PDF p.445).
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Fusion
variable {G : Type*} [Group G] [Finite G]

/-- J.2.6(4) from the quaternion decomposition and the earlier center facts. -/
theorem elementaryFusion_of_centralProduct (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (cp : CentralProductData d B)
    (hZ : Nat.card d.Z = 2) (hZV : d.Z ≤ d.V)
    {z : G} (hz : z ∈ d.Z) (hz1 : z ≠ 1) : ElementaryFusion d z := by
  let := d.elementary_U_of_card_Z hZ
  have hBHC : HB d B ≤ d.HC := by rw [cp.product_eq]; exact le_sup_left
  have hcomm : HB d B ≤ centralizer (d.U : Set G) := hBHC.trans inf_le_right
  have hinter : Nat.card (HB d B ⊓ d.U : Subgroup G) = 2 := by
    rw [cp.intersection_eq, hZ]
  refine ⟨?_, ?_, fun u hu hu1 => d.fusion_U hZ hZV hz hz1 hu hu1⟩
  · rw [cp.product_eq]
    exact omegaOne_eq_of_quaternion_elementary_product _ _ cp.quaternion hinter hcomm
  · rw [cp.product_eq]
    exact (frattini_eq_of_quaternion_elementary_product _ _ cp.quaternion hinter hcomm).trans
      cp.intersection_eq

end CFSG.Quasithin.ChapterJ.Fusion
