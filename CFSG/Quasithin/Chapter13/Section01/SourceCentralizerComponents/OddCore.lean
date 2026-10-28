module
public import Theory.GroupTheory.Fitting.TwoCorePreimage
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Ambient

/-!
# The odd core in the original centralizer argument

The original 1.1.5 hypotheses make the marked involution invert O(H),
so O(H) is abelian. Its image in H/O₂(H) lies in the Fitting subgroup.
Consequently O(H) lies in the source-controlled Fitting preimage and hence
in M, while 1.1.5 makes O(H) meet M trivially. This proves O(H)=1 without
assuming that arbitrary odd-order groups are solvable.

Source: Aschbacher–Smith, proof of 13.1.12(3), printed p.874, and 1.1.5(2).
The actual centralizer consumer is SourceCentralizerStructure.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents
open Chapter1
variable {G : Type*} [Group G] [Finite G]

/-- Fitting-preimage control eliminates the literal odd core under 1.1.5. -/
theorem oddCore_eq_bot_of_twoFitting_le
    {H M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : Lemma115Hypotheses H S M z)
    (hfit : (twoFittingCore H).map H.subtype ≤ M) : pPrimeCore 2 H = ⊥ := by
  let R := pPrimeCore 2 H
  let zH : H := ⟨z,h.mem_intersection.1⟩
  let φ : MulAut R := MulAut.conjNormal zH
  have hinv (r : R) : φ r = r⁻¹ := by
    apply Subtype.ext
    apply Subtype.ext
    exact h.inverts_oddCore r r.property
  let : CommGroup R := { (inferInstance : Group R) with
    mul_comm := fun a b => by
      have he := φ.map_mul a⁻¹ b⁻¹
      simpa only [hinv,mul_inv_rev,inv_inv] using he.symm }
  let q := QuotientGroup.mk' (pCore 2 H)
  let : (R.map q).Normal := (inferInstance : R.Normal).map q (QuotientGroup.mk'_surjective _)
  let : Group.IsNilpotent (R.map q) := Group.nilpotent_of_surjective
    (q.subgroupMap R) (q.subgroupMap_surjective R)
  have hRF : R.map q ≤ fittingSubgroup (H ⧸ pCore 2 H) := le_sSup ⟨inferInstance,inferInstance⟩
  apply bot_unique
  intro r hr
  have hrF : r ∈ twoFittingCore H := hRF (mem_map_of_mem q hr)
  have hrM : (r:G) ∈ M := hfit (mem_map_of_mem H.subtype hrF)
  have hm : (⟨r,hrM⟩ : M.subgroupOf H) ∈ R.subgroupOf (M.subgroupOf H) := hr
  rw [h.oddCore_intersection_eq_bot] at hm
  exact congrArg Subtype.val (mem_bot.mp hm)

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents
