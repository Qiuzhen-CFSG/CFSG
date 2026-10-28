module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.SectionBound
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.FrobeniusDegree

/-!
# The dimension obstruction in Lemma 8.2.7

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma 8.2.7, printed pp.717–718 (PDF pp.734–735).

The proved reduction combines the upper bound ten on the literal section
of O₂(X)U/U with the lower bound 24 from a free order-24 normalizer of an
odd abelian subgroup in that section's action image. Both bounds are proved;
neither is a premise. The conjugation formula fixes the quotient action.

This is not yet the source assertion that K_U/O₂(K_U) is quasisimple.
Its assembly still needs the A.3.12 radical selection, a compatible offender
reselection in H = XT, the extraspecial exclusion, and an elementary section
admitting the containing component's action and the required odd extension.
In particular an H-chief factor need not admit the larger component action.
The extension's free normalizer must also be constructed from its genuine
model and action, without identifying q with p in the SL₂(5) branch.

The final source assembly remains in this module. Its incoming L_U must be
Normalizer.localResidual L U, N must be N_G(U), and normality of K_U is
relative to N; the parent supplies complete conclusions 8.2.2–6.
-/

public section
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The contradiction for a marked section with the actual larger action.
The rank-five premise is the earlier table's B/U entry. The odd abelian
kernel and its free normalizer are literal subgroups of the quotient action
image; their existence is not assumed to follow from a family name. -/
theorem section_obstruction (X U V T J E D : Subgroup G)
    [(D.subgroupOf E).Normal]
    [IsElementaryAbelian 2 (V ⊓ X.pCoreIn 2 : Subgroup G)]
    [IsElementaryAbelian 2 (E ⧸ D.subgroupOf E)]
    [MulDistribMulAction J (E ⧸ D.subgroupOf E)]
    (hTX : T ≤ normalizer (X : Set G))
    (hQT : X.pCoreIn 2 ≤ T) (hTV : T ≤ normalizer (V : Set G))
    (hVT : V ≤ T) (hUT : U ≤ T) (hUC : U ≤ centralizer (V : Set G))
    (hER : E ≤ X.pCoreIn 2 ⊔ U) (hUD : U ≤ D)
    (hJE : J ≤ normalizer (E : Set G))
    (hact : ∀ j : J, ∀ e : E,
      j • (QuotientGroup.mk' (D.subgroupOf E) e) =
        QuotientGroup.mk' (D.subgroupOf E)
          ⟨(j : G) * (e : G) * (j : G)⁻¹,
            (mem_normalizer_iff.mp (hJE j.property) e).mp e.property⟩)
    (Y : Subgroup (MulAut (E ⧸ D.subgroupOf E))) (hodd : Odd (Nat.card Y))
    (t : J)
    (ht : IsInvolution (MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E) t))
    (htV : (t : G) ∈ V)
    (hinv : ∀ y ∈ Y,
      MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E) t * y *
        (MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E) t)⁻¹ = y⁻¹)
    (hfull : commutatorAction Y (E ⧸ D.subgroupOf E) = ⊤)
    (hrow : Module.finrank (ZMod 2)
      (Additive ((V ⊓ X.pCoreIn 2 : Subgroup G) ⧸ U.subgroupOf (V ⊓ X.pCoreIn 2))) ≤ 5)
    (N C : Subgroup (MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E)).range)
    [Nontrivial N] [IsMulCommutative N]
    (hNodd : Odd (Nat.card N)) (hCcard : Nat.card C = 24)
    (hCN : C ≤ normalizer (N : Set (MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E)).range))
    (hfree : ∀ c : C, c ≠ 1 → ∀ n : N,
      (c : (MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E)).range) * n *
        (c : (MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E)).range)⁻¹ = n → n = 1) :
    False := by
  have hsmall := section_finrank_le_ten X U V T J E D hTX hQT hTV hVT hUT hUC
    hER hUD hJE hact Y hodd t ht htV hinv hfull hrow
  have hlarge := actionImage_finrank_ge_twentyFour
    (MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E)).range N C hNodd hCcard hCN hfree
  omega

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion
