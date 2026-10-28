module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.Quotients
public import Theory.PPrimeCore

/-!
# Source-local objects for the five-centralizer argument

The subgroup P in J.2.7 is initially the odd core, with its literal image
in G. It is not identified with the five-core until after the order-45
alternative has been excluded. The two witness types below state the
local quaternion and inverter calculations still needed from Ru2 and
J.2.1–6. Neither type assumes the centralizer's odd-complement product,
its order, its five-core, or the nonconjugacy conclusion.

Source: Aschbacher–Smith, J.2.7(5–6), printed pp.435–436 (PDF pp.446–447).
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}

/-- The actual ambient image of O(C_G(B₅)), before the five-group argument. -/
abbrev fiveOddPart (B5 : Sylow 5 d.toTypeRuSetup.H) : Subgroup G :=
  (pPrimeCore 2 (G5 B5)).map (G5 B5).subtype

/-- The local calculation preceding Brauer–Suzuki on printed p.435.
Construction from Ru2 and the earlier source clauses remains a separate obligation. -/
structure FiveQuaternionData (B5 : Sylow 5 d.toTypeRuSetup.H) where
  twoSylow : Sylow 2 (G5 B5)
  twoSylow_image : (twoSylow : Subgroup (G5 B5)).map (G5 B5).subtype = CQ B5
  quaternion : Nonempty (CQ B5 ≃* QuaternionGroup 2)
  local_product : d.toTypeRuSetup.H ⊓ G5 B5 = B5Image B5 ⊔ CQ B5
  local_card : Nat.card (d.toTypeRuSetup.H ⊓ G5 B5 : Subgroup G) = 40
  le_HC : CQ B5 ≤ d.toTypeRuSetup.HC
  inf_U : CQ B5 ⊓ d.toTypeRuSetup.U = d.toTypeRuSetup.Z

/-- The z-class inverter and its quaternion fusion on printed p.436.
The conjugating element remains in the literal quaternion subgroup. -/
structure FiveInverterData (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H) where
  i : G
  mem_H : i ∈ d.toTypeRuSetup.H
  square : i ^ 2 = 1
  z_class : IsConj i c.z
  inverts : ∀ x ∈ B5Image B5, i * x * i⁻¹ = x⁻¹
  noncentral : i ∉ centralizer (CQ B5 : Set G)
  fused : ∃ t : CQ B5, (t : G) * i * (t : G)⁻¹ = c.z * i

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
