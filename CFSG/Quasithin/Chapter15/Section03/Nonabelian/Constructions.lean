module

public import CFSG.Quasithin.Chapter15.Section03.Constructions
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# The centralizer and conjugate closure in 15.3.50–61

In the contrary case the source takes `H = C_G(Z)` and `U = ⟨Z_S^H⟩`.
The action below is conjugation on the literal quotient `U/(Z ∩ U)`;
the source input `Z ≤ Z_S` identifies its denominator with `Z`.
Normality is proved inside `U`, without imposing ambient normality on `Z`.
The actor quotient `H* = H/O₂(H)` is distinct from this vector quotient.

The remaining definitions fix the groups in 15.3.54 and 15.3.56. Right
conjugation agrees with the book; the action homomorphism uses left
conjugation. The subgroup `K` in 15.3.59 is the two-residual `O²(H)`.
Joins denote generated subgroups, with product descriptions left to proofs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.1145–1151.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian

open Subgroup
variable {G : Type*} [Group G]

/-- The maximal centralizer chosen in the contrary case. -/
abbrev centralizerH (Z : Subgroup G) : Subgroup G := centralizer (Z : Set G)

/-- The source's `U = ⟨Z_S^{C_G(Z)}⟩`. -/
abbrev closureU (Z ZS : Subgroup G) : Subgroup G := localSpan ZS (centralizerH Z)

/-- The two-core `Q_H`, formed inside `H` and embedded back into `G`. -/
noncomputable abbrev coreQ (Z : Subgroup G) : Subgroup G :=
  Stellmacher.twoCoreAmbient (centralizerH Z)

/-- The two-residual `K = O²(H)`, not the two-core. -/
noncomputable abbrev residualK (Z : Subgroup G) : Subgroup G :=
  Stellmacher.twoResidualAmbient (centralizerH Z)

/-- The actual intersection `T_K = T ∩ O²(H)`. -/
noncomputable def residualSylow (T Z : Subgroup G) : Subgroup G := T ⊓ residualK Z

/-- The book's right conjugate `A^g`. -/
def rightConjugate (A : Subgroup G) (g : G) : Subgroup G :=
  A.map (MulAut.conj g⁻¹).toMonoidHom

/-- `I = ⟨U,U^g⟩` in 15.3.54. -/
def pairI (Z ZS : Subgroup G) (g : G) : Subgroup G :=
  closureU Z ZS ⊔ rightConjugate (closureU Z ZS) g

/-- `P = O₂(I)` in 15.3.54. -/
noncomputable def pairP (Z ZS : Subgroup G) (g : G) : Subgroup G :=
  Stellmacher.twoCoreAmbient (pairI Z ZS g)

/-- `W = U ∩ P` in 15.3.54. -/
noncomputable def pairW (Z ZS : Subgroup G) (g : G) : Subgroup G :=
  closureU Z ZS ⊓ pairP Z ZS g

/-- `V₀ = ⟨Z^{Y₁}⟩` in 15.3.56. -/
abbrev lineV₀ (Z Y₁ : Subgroup G) : Subgroup G := localSpan Z Y₁

/-- `F = U ∩ H^y` in 15.3.56. -/
def intersectionF (Z ZS : Subgroup G) (y : G) : Subgroup G :=
  closureU Z ZS ⊓ rightConjugate (centralizerH Z) y

/-- `X = F^y` in 15.3.56. -/
def partnerX (Z ZS : Subgroup G) (y : G) : Subgroup G :=
  rightConjugate (intersectionF Z ZS y) y

/-- `E = F ∩ X` in 15.3.56. -/
def intersectionE (Z ZS : Subgroup G) (y : G) : Subgroup G :=
  intersectionF Z ZS y ⊓ partnerX Z ZS y

theorem ZS_le_closureU (Z ZS : Subgroup G) : ZS ≤ closureU Z ZS :=
  le_conjugateSpanBy _ _

theorem closureU_le_H {Z ZS : Subgroup G} (hZS : ZS ≤ centralizerH Z) :
    closureU Z ZS ≤ centralizerH Z := conjugateSpanBy_le_self hZS

theorem H_normalizes_closureU (Z ZS : Subgroup G) :
    centralizerH Z ≤ normalizer (closureU Z ZS : Set G) :=
  le_normalizer_conjugateSpanBy _ _

/-- Only relative normality is needed to form `U/Z`. -/
theorem denominator_normal {Z ZS : Subgroup G} (hZS : ZS ≤ centralizerH Z) :
    (Z.subgroupOf (closureU Z ZS)).Normal := by
  constructor
  intro z hz u
  change (z : G) ∈ Z at hz
  change (u : G) * (z : G) * (u : G)⁻¹ ∈ Z
  have hc := mem_centralizer_iff.mp (closureU_le_H hZS u.property) z hz
  simpa only [← hc, mul_inv_cancel_right] using hz

/-- The actual vector quotient, distinct from `H/O₂(H)`. -/
abbrev VectorQuotient (Z ZS : Subgroup G) :=
  closureU Z ZS ⧸ Z.subgroupOf (closureU Z ZS)

/-- The source actor quotient `H* = H/O₂(H)`, using the internal two-core. -/
abbrev ActorQuotient (Z : Subgroup G) := centralizerH Z ⧸ pCore 2 (centralizerH Z)

variable (Z ZS : Subgroup G) [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- The distinguished line is the image of `Z_S` in the literal `U/Z`. -/
def distinguishedLine : Subgroup (VectorQuotient Z ZS) :=
  (ZS.subgroupOf (closureU Z ZS)).map (QuotientGroup.mk' _)

/-- The genuine conjugation action on `U/Z`, constructed rather than postulated. -/
noncomputable def quotientAction : centralizerH Z →* MulAut (VectorQuotient Z ZS) :=
  Classical.choose (exists_quotient_conjugation_action (centralizerH Z)
    (closureU Z ZS) Z (H_normalizes_closureU Z ZS)
    (Subgroup.centralizer_le_normalizer _) inferInstance)

/-- Compatibility with the quotient projection fixes the action completely. -/
theorem quotientAction_mk (h : centralizerH Z) (u : closureU Z ZS) :
    quotientAction Z ZS h (QuotientGroup.mk' _ u) =
      QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS))
        ⟨(h : G) * (u : G) * (h : G)⁻¹,
          (mem_normalizer_iff.mp (H_normalizes_closureU Z ZS h.property) u).mp
            u.property⟩ :=
  Classical.choose_spec (exists_quotient_conjugation_action (centralizerH Z)
    (closureU Z ZS) Z (H_normalizes_closureU Z ZS)
    (Subgroup.centralizer_le_normalizer _) inferInstance) h u

/-- The kernel identification of 15.3.48(3) identifies the literal `H*`
with its faithful action image; this is an actual multiplicative equivalence. -/
noncomputable def actorQuotientEquivRange
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) :
    ActorQuotient Z ≃* (quotientAction Z ZS).range :=
  (QuotientGroup.quotientMulEquivOfEq hkernel.symm).trans
    (QuotientGroup.quotientKerEquivRange (quotientAction Z ZS))

/-- The actor equivalence sends each coset to its actual conjugation automorphism. -/
theorem actorQuotientEquivRange_mk
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (h : centralizerH Z) :
    (actorQuotientEquivRange Z ZS hkernel (QuotientGroup.mk' _ h) :
      MulAut (VectorQuotient Z ZS)) = quotientAction Z ZS h := rfl

end CFSG.Quasithin.Chapter15.Section03.Nonabelian
