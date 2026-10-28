module
public import Theory.GroupTheory.RankOneInvariantKernelCounting
public import Theory.Representation.SL2.FullFixedIndex

/-!
# The original-degree SL2 invariant-kernel orbit formula

The faithful elementary action of H/O2(H)=SL2(2^n) gives a full fixed index
at least q squared on the core omega. Any supplement L has the same fixed
subgroup there. The sharp maximum-abelian upper bound on the larger
invariant-kernel omega therefore discharges the orbit-counting theorem.
The quotient, both omegas and every central attachment are literal.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 7.6,
printed pp.61-62. RootProductNilesQuotient supplies the actual selected L.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace NilesRankOneKernel
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]

theorem sl2_invariantKernel_orbit
    (S : Sylow 2 H) (α : MulAut S)
    (e : (H ⧸ pCore 2 H) ≃* SL(2,F))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (hV : omegaCenterIn (pCore 2 H) ≤
      (invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype)
    (hC : centralizer (omegaCenterIn (pCore 2 H) : Set H) = pCore 2 H)
    (L : Subgroup H) (hgen : L ⊔ pCore 2 H = ⊤)
    (hupp : (centralizer (L : Set H)).relIndex
      (omegaCenterIn ((invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype)) ≤
        Nat.card F ^ 2) :
    invariantNormalKernel (S : Subgroup H) α =
      ⨅ m : ℤ, ((pCore 2 H).subgroupOf (S : Subgroup H)).map ((α ^ m).toMonoidHom) := by
  let V := omegaCenterIn (pCore 2 H)
  let : V.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp (by
    simpa only [normalizer_eq_top] using normalizer_le_normalizer_omegaCenterIn (pCore 2 H)))
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    change e.toMonoidHom.ker.comap (QuotientGroup.mk' (pCore 2 H)) = _
    rw [e.toMonoidHom.ker_eq_bot e.injective,MonoidHom.comap_bot,QuotientGroup.ker_mk']
  have hkc : q.ker = centralizer (V : Set H) := hk.trans hC.symm
  have hred : IsPReduced 2 V := by
    refine ⟨inferInstance,inferInstance,?_⟩
    let eq := (QuotientGroup.quotientMulEquivOfEq hC).trans e
    apply (map_eq_bot_iff_of_injective _ (f := eq.toMonoidHom) eq.injective).mp
    rw [pCore_map_iso 2 eq,Matrix.SL2.twoCore_eq_bot]
  have hl := Representation.SL2.normal_fixed_index_lower V q hq hkc hn hF
  have hfixed := SmallMover.fixed_inf_sup V (pCore 2 H) L
    (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
  rw [sup_comm,hgen] at hfixed
  rw [←inf_relIndex_left V (centralizer ((⊤ : Subgroup H) : Set H)),hfixed,
    inf_relIndex_left] at hl
  exact invariantKernel_eq_orbit_inf_of_fixed_indices S α hV hC hred L hgen
    (Nat.card F^2) hl hupp
end NilesRankOneKernel
