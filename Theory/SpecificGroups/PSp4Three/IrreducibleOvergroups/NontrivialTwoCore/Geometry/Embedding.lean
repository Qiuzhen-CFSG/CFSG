module

public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.NontrivialTwoCore.Geometry.CommutantPlane
public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.NontrivialTwoCore.Representation
public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.NontrivialTwoCore.CoreLift
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter

/-!
# The actual plane action of an extraspecial core's centralizer

The embedded center of a normal extraspecial two-core has order two and
is central in the full preimage. Faithful irreducibility makes its
nonidentity element act as minus identity. A noncommuting pair in the
core therefore acts by anticommuting operators with scalar squares.
Their commutant acts faithfully on a ternary plane, by the explicit
sign-space construction of `CommutantPlane`.

The representation here is the actual symplectic matrix action and the
centralizer is taken inside the full preimage. Source application:
Aschbacher–Smith, Theorem 0.1.2(4), condition K, printed pp.4 and 482 of
`refs/quasithin.pdf`.
-/

namespace Matrix.PSp4Three.NontrivialTwoCore.Geometry
open Subgroup LinearInvolution
open scoped commutatorElement

private theorem central_involution_eq_neg_one
    {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (rho : Representation F G V) [Representation.IsIrreducible rho]
    (hrho : Function.Injective rho) (h2 : (2 : F) ≠ 0)
    (z : G) (hz : z ∈ center G) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) :
    rho z = -1 := by
  let W : Subrepresentation rho := {
    toSubmodule := plus (rho z)
    apply_mem_toSubmodule := fun g x hx => by
      rw [mem_plus] at hx ⊢
      have hzg : z * g = g * z := (mem_center_iff.mp hz g).symm
      change (rho z * rho g) x = rho g x
      rw [← map_mul, hzg, map_mul]
      change rho g (rho z x) = rho g x
      rw [hx] }
  have hW : W = ⊥ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top W with hb | ht
    · exact hb
    · exfalso
      apply hz1
      apply hrho
      rw [map_one]
      ext x
      exact (mem_plus (rho z) x).mp (show x ∈ W by rw [ht]; trivial)
  have hplus : plus (rho z) = ⊥ := congrArg Subrepresentation.toSubmodule hW
  have hi : Function.Involutive (rho z) := by
    intro x
    change (rho z * rho z) x = x
    rw [← map_mul, ← pow_two, hz2, map_one]
    rfl
  ext x
  obtain ⟨⟨p,m⟩,rfl⟩ := (decomposition (rho z) hi h2).surjective x
  have hp : p.val = 0 := by simpa [hplus] using p.prop
  change rho z (p.val + m.val) = -(p.val + m.val)
  rw [hp, zero_add, (mem_minus (rho z) m.val).mp m.prop]

/-- The commutant of an extraspecial lifted two-core has a faithful ternary
plane representation. Only irreducibility of the full preimage is needed. -/
public theorem fullPreimage_twoCore_centralizer_gl_two_embedding
    (M : Subgroup (PSp 2 (ZMod 3))) (hred : ¬ HasInvariantSubspace M)
    (hspecial : IsExtraspecial 2 (pCore 2 (fullPreimage M))) :
    ∃ f : centralizer (pCore 2 (fullPreimage M) : Set (fullPreimage M)) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 3), Function.Injective f := by
  classical
  let L := fullPreimage M
  let P := pCore 2 L
  let := hspecial
  have hquot := IsExtraspecial.quotient_elementary_abelian 2 P
  obtain ⟨a, b, hab⟩ : ∃ a b : P, a * b ≠ b * a := by
    by_contra! h
    have hc : center P = ⊤ := top_unique (fun x _ => mem_center_iff.mpr (fun y => h y x))
    let : Nontrivial (P ⧸ center P) := IsExtraspecial.quotient_nontrivial 2 P
    exact QuotientGroup.nontrivial_iff.mp inferInstance hc
  let z : P := ⁅a, b⁆
  have hz1 : z ≠ 1 := by
    exact fun h => hab (commutatorElement_eq_one_iff_mul_comm.mp h)
  have hz : z ∈ center P := hquot.commutator_le_center_of_central_quotient
    (commutator_mem_commutator (mem_top a) (mem_top b))
  have hZcard : Nat.card (center P) = 2 := IsExtraspecial.center_order_p 2 P
  have hZL : (center P).map P.subtype ≤ center L :=
    central_of_normal_card_two _ (by rw [card_map_of_injective P.subtype_injective, hZcard])
  have hzL : z.val ∈ center L := hZL ⟨z, hz, rfl⟩
  have hz2 : z ^ 2 = 1 := by
    have he := pow_card_eq_one' (x := (⟨z, hz⟩ : center P))
    rw [hZcard] at he
    exact congrArg Subtype.val he
  have hcases (x : P) (hx : x ∈ center P) : x = 1 ∨ x = z := by
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : center P)).mp hZcard
    exact Or.inr (congrArg Subtype.val
      ((hw ⟨x, hx⟩ (fun h => hx1 (congrArg Subtype.val h))).trans
        (hw ⟨z, hz⟩ (fun h => hz1 (congrArg Subtype.val h))).symm))
  let R := fullPreimageRepresentation M
  let : Representation.IsIrreducible R :=
    (fullPreimageRepresentation_irreducible_iff M).mpr hred
  have hRz : R z.val = -1 := central_involution_eq_neg_one R
    (fullPreimageRepresentation_injective M) (by decide) z.val hzL
    (congrArg Subtype.val hz2) (fun h => hz1 (Subtype.ext h))
  let sigma : Representation (ZMod 3) P (Vector 2 (ZMod 3)) := R.comp P.subtype
  have hsigmaz : sigma z = -1 := hRz
  have hsquare (x : P) : sigma x * sigma x = 1 ∨ sigma x * sigma x = -1 := by
    rcases hcases (x ^ 2) (hquot.sq_mem_center_of_central_quotient x) with h | h
    · left; rw [← map_mul, ← pow_two, h, map_one]
    · right; rw [← map_mul, ← pow_two, h, hsigmaz]
  have hab' : sigma a * sigma b = -(sigma b * sigma a) := by
    have he : a * b = z * (b * a) := by dsimp [z]; group
    rw [← map_mul, he, map_mul, map_mul, hsigmaz]
    ext v
    rfl
  let C := centralizer (P : Set L)
  let rho : C →* (Vector 2 (ZMod 3) ≃ₗ[ZMod 3] Vector 2 (ZMod 3)) :=
    toLinear.comp (L.subtype.comp C.subtype)
  have hrho : Function.Injective rho := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply ext_action
    intro v
    exact LinearEquiv.congr_fun h v
  have hcomm (x : P) (c : C) (v : Vector 2 (ZMod 3)) :
      toLinear x.val.val (rho c v) = rho c (toLinear x.val.val v) := by
    have he : x.val * c.val = c.val * x.val := mem_centralizer_iff.mp c.prop x.val x.prop
    change x.val.val • (c.val.val • v) = c.val.val • (x.val.val • v)
    rw [← mul_smul, ← mul_smul, ← Subgroup.coe_mul, he]
    rfl
  exact exists_gl_two_embedding_of_anticommuting_pair rho hrho
    (toLinear a.val.val) (toLinear b.val.val)
    (hsquare a) (hsquare b) hab' (hcomm a) (hcomm b) (by simp [Vector, Index])

end Matrix.PSp4Three.NontrivialTwoCore.Geometry
