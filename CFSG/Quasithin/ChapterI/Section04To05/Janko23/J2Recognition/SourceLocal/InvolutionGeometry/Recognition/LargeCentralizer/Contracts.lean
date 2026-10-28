module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.Basic

/-!
# Inputs to the large-centralizer argument

The central quotient is literally C_G(t)/⟨t⟩, with its subgroup normality
proved inside C_G(t). `LocalFrame` specifies the earlier w = 2 geometry:
the two four-groups E and U, their elementary Sylow join, and the cubic
actions X₁ and X₃. It does not identify U with the intrinsic two-core.

`QuotientGeometry` retains the images of that Sylow subgroup and E under
the actual quotient map. Its kernel-local hypothesis asks for both a
single involution class and a four-group centralizer. None of these records
asserts an existence theorem. Their constructors remain source obligations.

Source: Aschbacher, *Sporadic Groups* (1994), 46.3, 46.14 and 47.1(1),
printed pp.251,257–260.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer

variable {G : Type*} [Group G]

def centralInvolution (t : G) : involutionCentralizer t :=
  ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩

def quotientKernel (t : G) : Subgroup (involutionCentralizer t) :=
  zpowers (centralInvolution t)

theorem quotientKernel_le_center (t : G) :
    quotientKernel t ≤ center (involutionCentralizer t) := by
  apply zpowers_le.mpr
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)

instance quotientKernel_normal (t : G) : (quotientKernel t).Normal where
  conj_mem x hx g := by
    have he := mem_center_iff.mp (quotientKernel_le_center t hx) g
    simpa only [he, mul_inv_cancel_right] using hx

abbrev CentralQuotient (t : G) := involutionCentralizer t ⧸ quotientKernel t

def quotientMap (t : G) : involutionCentralizer t →* CentralQuotient t :=
  QuotientGroup.mk' (quotientKernel t)

structure TransferData (t : G) where
  S : Sylow 2 (CentralQuotient t)
  elementary : IsElementaryAbelian 2 S
  E : Subgroup S
  index : E.index = 2
  closed : ∀ x y : S, orderOf x = 2 →
    IsConj (x : CentralQuotient t) (y : CentralQuotient t) → (x ∈ E ↔ y ∈ E)

structure TransferKernel {t : G} (F : TransferData t) where
  M : Subgroup (CentralQuotient t)
  normal : M.Normal
  index : M.index = 2
  intersection : M.subgroupOf (F.S : Subgroup (CentralQuotient t)) = F.E

variable [Finite G]

/-- The part of the w = 2 geometry used before recognizing the second
centralizer. `U` is the chosen four-group, not an assumed intrinsic core. -/
structure LocalFrame (D : Seed G) (t : G) where
  R : Subgroup G
  E : Subgroup G
  U : Subgroup G
  X1 : Subgroup G
  X3 : Subgroup G
  R_card : Nat.card R = 64
  E_center : (center R).map R.subtype = E
  E_card : Nat.card E = 4
  U_card : Nat.card U = 4
  disjoint : Disjoint E U
  elementary : IsElementaryAbelian 2 (E ⊔ U : Subgroup G)
  join_le_R : E ⊔ U ≤ R
  U_eq : R ⊓ centralizer (X1 : Set G) = U
  z_mem : D.z ∈ E
  t_mem : t ∈ U
  A : Sylow 2 (involutionCentralizer t)
  A_eq : (A : Subgroup (involutionCentralizer t)).map
    (involutionCentralizer t).subtype = E ⊔ U
  core_intersection : (E ⊔ U) ⊓ ambientCore D.z = E
  double_centralizer : involutionCentralizer t ⊓ involutionCentralizer D.z = E ⊔ U
  X1_card : Nat.card X1 = 3
  X1_le : X1 ≤ involutionCentralizer t
  X1_normalizes : X1 ≤ normalizer (E : Set G)
  X1_transitive : ∀ e ∈ E, e ≠ 1 → ∀ f ∈ E, f ≠ 1 →
    ∃ x : X1, (x : G) * e * (x : G)⁻¹ = f
  X3_card : Nat.card X3 = 3
  X3_normalizes : X3 ≤ normalizer (U : Set G)
  X3_centralizes : X3 ≤ centralizer (E ⊔ X1 : Set G)
  X3_transitive : ∀ u ∈ U, u ≠ 1 → ∀ v ∈ U, v ≠ 1 →
    ∃ x : X3, (x : G) * u * (x : G)⁻¹ = v
  normalizer_intersection_card :
    Nat.card ↥(involutionCentralizer t ⊓ normalizer (R : Set G)) = 48

namespace LocalFrame
variable {D : Seed G} {t : G}

/-- An ambient subgroup's image in the literal central quotient. -/
def quotientImage (B : Subgroup G) : Subgroup (CentralQuotient t) :=
  (B.subgroupOf (involutionCentralizer t)).map (quotientMap t)

end LocalFrame

/-- The quotient fusion and centralizer facts, before transfer and A₅
recognition. The local theorem includes a single involution class as well as
the four-group centralizer; the latter alone would be insufficient. -/
structure QuotientGeometry {D : Seed G} {t : G} (F : LocalFrame D t) where
  transfer : TransferData t
  sylow_eq : (transfer.S : Subgroup (CentralQuotient t)) =
    LocalFrame.quotientImage (F.E ⊔ F.U)
  closed_eq : transfer.E.map (transfer.S : Subgroup (CentralQuotient t)).subtype =
    LocalFrame.quotientImage F.E
  kernel_local : ∀ K : TransferKernel transfer,
    Nonempty (DihedralInvolutionCentralizerHypotheses K.M 2)

/-- The actual A₅ in K/⟨t⟩, together with the Sylow-intersection marking
needed to lift it. It is not a model for K or its normalizer. -/
structure RecognizedQuotient {D : Seed G} {t : G} (F : LocalFrame D t) where
  geometry : QuotientGeometry F
  kernel : TransferKernel geometry.transfer
  equiv : kernel.M ≃* A5

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
