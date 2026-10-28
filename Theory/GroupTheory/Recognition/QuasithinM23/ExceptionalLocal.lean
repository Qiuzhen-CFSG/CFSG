module
public import Theory.Representation.BinaryAlternatingSevenControl.Normalizer
public import Theory.Representation.NormalElementaryQuotient
public import Theory.PGroupCore
public import Mathlib.GroupTheory.IsSubnormal

/-!
# Subnormal exceptional local groups on an elementary sixteen-group

A faithful A₇ image on a binary four-space is self-normalizing. A subnormal
such image must therefore be the entire acting group: otherwise the first
strict step in a subnormal chain would lie in its normalizer. Passing to the
centralizer quotient proves that a subnormal subgroup with quotient A₇ and
the same self-centralizing elementary core of order sixteen is the whole group.

The source application is the actual exceptional overcomponent in
Aschbacher–Smith 5.2.11(4), printed pp.653–654 (`refs/quasithin.pdf`).
No ambient normality or splitting is assumed.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.QuasithinM23

private theorem subnormal_actor_eq_top
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 4)
    (N : Subgroup G) (hn : N.IsSubnormal) (e : N ≃* alternatingGroup (Fin 7)) :
    N = ⊤ := by
  let σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V :=
    ρ.comp (N.subtype.comp e.symm.toMonoidHom)
  have hσ : Function.Injective σ := hf.comp (Subtype.val_injective.comp e.symm.injective)
  have hr : Representation.BinaryOffender.actionImage σ = N.map ρ.asGroupHom := by
    have he : σ.asGroupHom = ρ.asGroupHom.comp (N.subtype.comp e.symm.toMonoidHom) := by
      apply MonoidHom.ext
      intro g
      apply Units.ext
      rfl
    rw [Representation.BinaryOffender.actionImage, he]
    rw [MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr e.symm.surjective, ← MonoidHom.range_eq_map, range_subtype]
  have hs := Representation.BinaryAlternatingSevenControl.actionImage_self_normalizing σ hσ hd
  rw [hr] at hs
  have hnormalizer : normalizer (N : Set G) ≤ N := by
    intro x hx
    have hx' := N.le_normalizer_map ρ.asGroupHom (mem_map_of_mem ρ.asGroupHom hx)
    rw [hs] at hx'
    obtain ⟨y, hy, he⟩ := hx'
    exact hf (congrArg Units.val he) ▸ hy
  rcases IsSubnormal.iff_eq_top_or_exists.mp hn with ht | ⟨K, hK, _, hNK⟩
  · exact ht
  · exact (not_le_of_gt hK
      (((normal_subgroupOf_iff_le_normalizer hK.le).mp hNK).trans hnormalizer)).elim

/-- A subnormal A₇ quotient on the whole self-centralizing elementary core
of order sixteen leaves no larger ambient group. -/
theorem eq_top_of_subnormal_alternatingSeven
    {G : Type*} [Group G] [Finite G]
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 16) (hC : centralizer (U : Set G) ≤ U)
    (J : Subgroup G) (hJ : J.IsSubnormal)
    (hc : (pCore 2 J).map J.subtype = U)
    (e : J ⧸ pCore 2 J ≃* alternatingGroup (Fin 7)) : J = ⊤ := by
  have hCU : centralizer (U : Set G) = U := le_antisymm hC
    (fun x hx => mem_centralizer_iff.mpr (fun y hy => setLike_mul_comm hy hx))
  let q := QuotientGroup.mk' U
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective U
  have hk : q.ker = centralizer (U : Set G) := (QuotientGroup.ker_mk' U).trans hCU.symm
  let ρ := Representation.NormalElementaryQuotient.representation U q hq hk
  have hf : Function.Injective ρ :=
    Representation.NormalElementaryQuotient.representation_injective U q hq hk
  have hd : Module.finrank (ZMod 2) (Additive U) = 4 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    calc
      2 ^ Module.finrank (ZMod 2) (Additive U) = Nat.card (Additive U) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
      _ = 2 ^ 4 := (Nat.card_congr Additive.toMul).trans hU
  let f : J →* G ⧸ U := q.comp J.subtype
  have hfk : f.ker = pCore 2 J := by
    ext x
    change q x.val = 1 ↔ x ∈ pCore 2 J
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', ← hc]
    exact mem_map_iff_mem J.subtype_injective
  have hfr : f.range = J.map q := by rw [MonoidHom.range_comp, range_subtype]
  let eN : J.map q ≃* alternatingGroup (Fin 7) :=
    (MulEquiv.subgroupCongr hfr.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hfk).trans e))
  have htop := subnormal_actor_eq_top ρ hf hd (J.map q) (hJ.map hq) eN
  have hUJ : U ≤ J := hc ▸ map_subtype_le (pCore 2 J)
  have heq := congrArg (Subgroup.comap q) htop
  rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hUJ, comap_top] at heq
  exact heq

end Theory.GroupTheory.QuasithinM23
