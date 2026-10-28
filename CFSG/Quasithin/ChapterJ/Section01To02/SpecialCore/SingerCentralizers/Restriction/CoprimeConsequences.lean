module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers.Restriction
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers.Coprime

/-!
# Applying the Singer fixed-plane calculation to the source centralizer

The concrete restriction calculation makes S₀ an abelian four-group and
proves S₀ ∩ V = 1. These discharge the two fixed-subgroup premises in the
existing coprime centralizer splitting. The order and exact exponent still
use the independent full-commutator theorem J.2.3(6), stated explicitly.

Source: Aschbacher–Smith, Lemma J.2.3(1),(3), printed pp.433–434
(PDF pp.444–445 of the combined manuscript of 1 March 2004).
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.SpecialCore
variable {G : Type*} [Group G] [Finite G]

/-- The fixed and moving factors generate the actual element centralizer. -/
theorem SingerChoice.coreCentralizer_eq_sup_from_restriction
    (d : TypeRuSetup G) (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (s : G) (hs : s ∈ fixedCore d c.B7) :
    d.S ⊓ centralizer ({s} : Set G) = fixedCore d c.B7 ⊔ movingCore d c.B7 s :=
  c.coreCentralizer_eq_sup d B (c.fixedCore_commutative d B) s hs

/-- The entire natural kernel lies in the moving factor. -/
theorem SingerChoice.V_le_movingCore_from_restriction
    (d : TypeRuSetup G) (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (s : G) (hs : s ∈ d.S) : d.V ≤ movingCore d c.B7 s :=
  c.V_le_movingCore d B (c.fixedCore_disjoint_V d B) s hs

/-- The independent full-commutator theorem gives order 256 and exponent four. -/
theorem SingerChoice.coreCentralizer_order_exponent_from_restriction
    (d : TypeRuSetup G) (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (hfull : ∀ t : d.S, (t : G) ∉ d.V → ⁅zpowers (t : G), d.S⁆ = d.V)
    (s : G) (hs : s ∈ fixedCore d c.B7) (hs1 : s ≠ 1) :
    Nat.card (d.S ⊓ centralizer ({s} : Set G) : Subgroup G) = 256 ∧
      Monoid.exponent (d.S ⊓ centralizer ({s} : Set G) : Subgroup G) = 4 :=
  c.coreCentralizer_order_exponent d B hfull (c.fixedCore_disjoint_V d B) s hs hs1
end CFSG.Quasithin.ChapterJ.SpecialCore
