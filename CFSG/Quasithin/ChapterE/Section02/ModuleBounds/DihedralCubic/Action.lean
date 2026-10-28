module

public import Theory.Representation.NormalElementaryQuotient

/-!
# Conjugation on the original elementary subgroup

This is the relative-normalizer version of `NormalElementaryQuotient`:
U normalizes V, but V need not be normal in the ambient group. The actual
normalizer homomorphism descends through a surjection with kernel C_U(V).
Its binary representation on the original V is faithful, with the exact
conjugation formula on representatives.

The parent uses this construction for Aut_X(V) and for the original
M₀/C_M₀(V) action in Aschbacher–Smith E.2.13 and 15.4.2(4), combined
manuscript (1 March 2004), printed pp.224–225 and 1156.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.DihedralCubic
variable {G D : Type*} [Group G] [Group D]
  (U V : Subgroup G) (hn : U ≤ normalizer (V : Set G))

/-- Conjugation on the original subgroup, with only relative normalization. -/
def conjugation : U →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion hn)

lemma conjugation_ker : (conjugation U V hn).ker = (centralizer (V : Set G)).subgroupOf U := by
  ext u
  change V.normalizerMonoidHom (inclusion hn u) = 1 ↔ _
  change inclusion hn u ∈ V.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

include hn in
lemma centralizer_normal : ((centralizer (V : Set G)).subgroupOf U).Normal := by
  rw [← conjugation_ker U V hn]
  infer_instance

variable [IsElementaryAbelian 2 V]
  (q : U →* D) (hq : Function.Surjective q)
  (hk : q.ker = (centralizer (V : Set G)).subgroupOf U)

noncomputable def conjugationAut : D →* MulAut V :=
  q.liftOfSurjective hq ⟨conjugation U V hn, by rw [hk, conjugation_ker]⟩

omit [IsElementaryAbelian 2 V] in
lemma conjugationAut_apply (u : U) (v : V) :
    (conjugationAut U V hn q hq hk (q u) v : G) = u * v * (u : G)⁻¹ := by
  unfold conjugationAut
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

/-- The canonical faithful binary action on V, retaining the given quotient map. -/
noncomputable def representation : Representation (ZMod 2) D (Additive V) where
  toFun d := (conjugationAut U V hn q hq hk d).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change conjugationAut U V hn q hq hk 1 v.toMul = v.toMul
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    change conjugationAut U V hn q hq hk (a * b) v.toMul =
      conjugationAut U V hn q hq hk a (conjugationAut U V hn q hq hk b v.toMul)
    rw [map_mul]
    rfl

lemma representation_apply (u : U) (v : Additive V) :
    ((representation U V hn q hq hk (q u) v).toMul : G) =
      u * v.toMul * (u : G)⁻¹ :=
  conjugationAut_apply U V hn q hq hk u v.toMul

lemma representation_injective : Function.Injective (representation U V hn q hq hk) := by
  apply (representation U V hn q hq hk).ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro d hd
  obtain ⟨u, rfl⟩ := hq d
  have hu : u ∈ q.ker := by
    rw [hk]
    intro v hv
    have he := congrArg (fun k : Module.End (ZMod 2) (Additive V) =>
      ((k (Additive.ofMul ⟨v, hv⟩)).toMul : G)) hd
    change ((representation U V hn q hq hk (q u) (Additive.ofMul ⟨v, hv⟩)).toMul : G) = v at he
    rw [representation_apply] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  exact hu
end CFSG.Quasithin.ChapterE.DihedralCubic
