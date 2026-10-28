module
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.SpecialLinearNatural
public import Theory.SpecificGroups.SL2.NaturalStabilizer
/-!
# Centralizers in a binary natural plane

Let a finite group act on a normal elementary abelian subgroup as the
full natural SL₂(2) module, with the literal centralizer as kernel.
Every nonzero subgroup of the module centralized by a Sylow 2-subgroup
has centralizer equal to the product of that Sylow subgroup and the
kernel. A nonzero vector has a 2-group stabilizer; Sylow maximality and
the first isomorphism theorem then give the claimed equality.

This is the rank-two centralizer calculation used in Aschbacher–Smith
14.1.11 (printed p.978), stated independently of the ambient classification.
-/

public section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
namespace Theory.GroupAction.BinaryNaturalPlaneSeed
variable {G : Type*} [Group G] [Finite G]

theorem centralizer_eq_sylow_sup
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (S : Sylow 2 G) (A : Subgroup G) (hAV : A ≤ V) (hne : A ≠ ⊥)
    (hSA : (S : Subgroup G) ≤ centralizer (A : Set G))
    (c : Additive V ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (e : (G ⧸ centralizer (V : Set G)) ≃* SL(2,ZMod 2))
    (hc : ∀ g v, c (NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set G)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) g v) =
      Representation.specialLinearNatural 2 (e g) (c v)) :
    centralizer (A : Set G) = (S : Subgroup G) ⊔ centralizer (V : Set G) := by
  let K := centralizer (V : Set G)
  let N := centralizer (A : Set G)
  let q := QuotientGroup.mk' K
  let f := e.toMonoidHom.comp q
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = K := by
    ext g
    change e (q g) = 1 ↔ g ∈ K
    rw [← e.map_one,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff g
  let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hne
  obtain ⟨z,hz⟩ := exists_ne (1 : A)
  let v : V := ⟨z,hAV z.property⟩
  let w := c (Additive.ofMul v)
  have hw : w ≠ 0 := by
    intro he
    have hv : Additive.ofMul v = 0 := c.injective (he.trans c.map_zero.symm)
    exact hz (Subtype.ext (congrArg (fun a : Additive V => (a.toMul : G)) hv))
  have hNS : N.map f ≤ MulAction.stabilizer SL(2,ZMod 2) w := by
    rintro _ ⟨g,hg,rfl⟩
    change Representation.specialLinearNatural 2 (e (q g)) w = w
    rw [←hc]
    congr 1
    apply congrArg Additive.ofMul
    apply Subtype.ext
    change ((NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set G)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      (q g) (Additive.ofMul v)).toMul : G) = (v : G)
    rw [NormalElementaryQuotient.representation_apply]
    exact mul_inv_eq_iff_eq_mul.mpr ((hg (z : G) z.property).symm)
  have hp : IsPGroup 2 (N.map f) := (Matrix.SL2.stabilizer_nonzero_isPGroup w hw).to_le hNS
  let P := S.mapSurjective hf
  have he : N.map f = (P : Subgroup SL(2,ZMod 2)) :=
    P.is_maximal' hp (map_mono hSA)
  have hh := congrArg (comap f) he
  change (N.map f).comap f = ((S : Subgroup G).map f).comap f at hh
  rw [comap_map_eq,comap_map_eq,hker,sup_eq_left.mpr (centralizer_le hAV)] at hh
  exact hh
end Theory.GroupAction.BinaryNaturalPlaneSeed
