module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Actions
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.QuotientActions

/-!
# Constructing the faithful section action from the earlier centralizer identity

The actual action by conjugation on U/Z is linearized over F_2. Its kernel
is the relative quotient centralizer C_H(U/Z), so the source identity
C_H(U/Z) = O_2(H) produces a faithful representation of H/O_2(H) and the
required formula on representatives. No ambient normality of Z is imposed.

Elementary abelianness passes to smaller conjugate spans. For the replacement
K this gives both U_K = <Z_S^K> and V_K = <V^K> from 15.3.49(d).
Faithfulness is reconstructed from the earlier centralizer identity at K;
it is not assumed to follow by restricting the faithful action at H.
The source assembly must obtain that identity from 15.3.48 for K.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.48(3)
and the replacement in 15.3.49, printed pp.1142–1144.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction

variable {G : Type*} [Group G]

/-- Elementary abelianness descends with both the seed and the local actor. -/
theorem localSpan_elementary_of_le
    (V A H K : Subgroup G) [IsElementaryAbelian 2 (localSpan V H)]
    (hAV : A ≤ V) (hKH : K ≤ H) : IsElementaryAbelian 2 (localSpan A K) := by
  have hi : localSpan A K ≤ localSpan V H := conjugateSpanBy_mono hAV hKH
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · intro a b
    apply Subtype.ext
    exact congrArg (fun x : localSpan V H => (x : G))
      (mul_comm (⟨a, hi a.property⟩ : localSpan V H) ⟨b, hi b.property⟩)
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro a
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (a : G) (hi a.property)

/-- Construct the specified faithful section action from its genuine kernel computation. -/
noncomputable def sectionActionOfCentralizer
    (H U Z : Subgroup G) [IsElementaryAbelian 2 U] [(Z.subgroupOf H).Normal]
    (hZU : Z ≤ U) (hUH : U ≤ H)
    (hHU : H ≤ normalizer (U : Set G)) (hHZ : H ≤ normalizer (Z : Set G))
    (hkernel : CosetSetup.quotientCentralizer H U Z = pCore 2 H) : SectionAction H U Z := by
  let f := CosetSetup.quotientAction H U Z hHU hHZ
  let ρ : Representation (ZMod 2) H (Additive (U ⧸ Z.subgroupOf U)) :=
    { toFun h := (f h).toMonoidHom.toAdditive.toZModLinearMap 2
      map_one' := by
        ext v
        change Additive.ofMul (f 1 v.toMul) = v
        rw [map_one]
        rfl
      map_mul' := by
        intro a b
        ext v
        change Additive.ofMul (f (a * b) v.toMul) =
          Additive.ofMul (f a (f b v.toMul))
        rw [map_mul]
        rfl }
  have hker : ρ.ker = f.ker := by
    ext h
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hh
      apply MulEquiv.ext
      intro v
      exact congrArg Additive.toMul
        (congrArg (fun e : Module.End (ZMod 2) (Additive (U ⧸ Z.subgroupOf U)) =>
          e (Additive.ofMul v)) hh)
    · intro hh
      ext v
      change Additive.ofMul (f h v.toMul) = v
      rw [hh]
      rfl
  have hker' : ρ.ker = pCore 2 H :=
    hker.trans ((CosetSetup.quotientAction_ker H U Z hHU hHZ hUH).trans hkernel)
  refine
    { layer_le := hZU
      normalizes := hHU
      normalizes_layer := hHZ
      representation := QuotientGroup.lift (pCore 2 H) ρ hker'.ge
      on_representatives := ?_
      faithful := (QuotientGroup.injective_lift_iff (pCore 2 H) ρ hker'.ge).mpr hker'.symm }
  intro h u
  change Additive.ofMul (f h (QuotientGroup.mk' (Z.subgroupOf U) u)) = _
  exact congrArg Additive.ofMul (CosetSetup.quotientAction_apply H U Z hHU hHZ h u)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
