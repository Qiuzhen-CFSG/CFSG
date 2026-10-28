module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryGeneration.Generation

/-!
# The marked S₃ quotient of I₂

Restrict the actual P-action on V₂ to I₂. The core cover shows this
restriction is still onto; its two-group kernel is the literal plane
centralizer and hence the two-core of I₂. The first isomorphism theorem
constructs the quotient equivalence, with its action on every quotient
representative recorded explicitly.

Source: Aschbacher–Smith, Lemma 12.8.9(1–2), printed p.853.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- Restricting the literal plane action gives the marked S₃ quotient of I₂. -/
theorem binary_I₂_quotient (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]
    (hn : 2 ≤ n) (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (F.binarySeedAction L hL))
    (hcore : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hfactor : F.P L = (F.P L).pCoreIn 2 ⊔ F.I₂ L) :
    F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2 ∧
      ∃ e : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* Equiv.Perm (Fin 3),
        ∀ (x : F.I₂ L) (v : F.Vi 2),
          ((F.binaryPlaneLabel hn).symm (e (QuotientGroup.mk x)) v : G) =
            (x : G) * (v : G) * (x : G)⁻¹ := by
  let P := F.P L
  let I := F.I₂ L
  have hIP : I ≤ P := le_sup_right.trans hfactor.ge
  let f := F.binaryPermutationAction hn L hL
  let j := inclusion hIP
  let r := f.comp j
  have hk : f.ker = pCore 2 P := (F.binaryPermutationAction_ker hn L hL).trans
    (F.binaryPlaneAction_ker_eq_twoCore hn L hL hfull hcore)
  have hcover : pCore 2 P ⊔ I.subgroupOf P = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hIP, ← MonoidHom.range_eq_map, range_subtype]
    exact hfactor.symm
  have hsurj : Function.Surjective r := by
    have hm := congrArg (fun A : Subgroup P => A.map f) hcover
    rw [← hk, Subgroup.map_sup, Subgroup.map_ker_self, bot_sup_eq,
      map_top_of_surjective f (F.binaryPermutationAction_surjective hn L hL hfull)] at hm
    apply MonoidHom.range_eq_top.mp
    change (f.comp j).range = ⊤
    rw [MonoidHom.range_comp, inclusion_range]
    exact hm
  have hkr : IsPGroup 2 r.ker := by
    change IsPGroup 2 (f.comp j).ker
    rw [← MonoidHom.comap_ker]
    have hfker : IsPGroup 2 f.ker := hk.symm ▸ (show IsPGroup 2 (pCore 2 P) from pCore_isPGroup)
    exact hfker.comap_of_injective j (inclusion_injective _)
  have hrCore : r.ker = pCore 2 I := ker_eq_twoCore_of_surjective_perm_three r hsurj hkr
  have hrC : r.ker = (centralizer (F.Vi 2 : Set G)).subgroupOf I := by
    ext x
    change f (j x) = 1 ↔ (x : G) ∈ centralizer (F.Vi 2 : Set G)
    rw [← MonoidHom.mem_ker, F.binaryPermutationAction_ker hn L hL,
      F.binaryPlaneAction_ker hn L hL]
    rfl
  have hC := congrArg (fun A : Subgroup I => A.map I.subtype) (hrC.symm.trans hrCore)
  rw [subgroupOf_map_subtype, inf_comm] at hC
  refine ⟨hC, ?_⟩
  let e : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.quotientMulEquivOfEq hrCore.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective r hsurj)
  refine ⟨e, fun x v => ?_⟩
  have he : e (QuotientGroup.mk x) = r x := rfl
  rw [he]
  change ((F.binaryPlaneLabel hn).symm
    (F.binaryPlaneLabel hn (F.binaryPlaneAction hn L hL (j x))) v : G) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
