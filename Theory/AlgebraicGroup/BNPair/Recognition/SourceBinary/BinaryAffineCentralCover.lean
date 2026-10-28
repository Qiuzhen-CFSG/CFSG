module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.BinaryAffineModel
public import Theory.GroupTheory.CentralStemAbelianSylow
public import Theory.GroupTheory.CentralExtensionPartialInversion
public import Theory.SpecificGroups.GL2.ThreePartialInversion

/-!
# Triviality of odd stem covers of the degree-nine affine group

For a faithful solvable doubly transitive action of degree nine and order
144, affine coordinates identify a Sylow-three subgroup with the ternary
plane. A Sylow-two point stabilizer contains a partial inverter of a basis.
The central commutator calculation makes the full Sylow-three preimage
abelian. Central Sylow transfer then kills every prime divisor of an odd
stem kernel, and the covering homomorphism is injective.

This proves the degree-nine instance of Fong--Seitz I (4A)(c), printed p.19,
used in the exceptional local-cover branch of (5B)--(5C), pp.25--26.
-/

public noncomputable section
open Subgroup MulAction Matrix
open Matrix.GeneralLinearGroup.PrimeThreeFiveResidual
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.BinaryPanel
variable {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω]
  [FaithfulSMul G Ω] [Finite Ω]

theorem injective_odd_stem_nine_action
    (ht : IsMultiplyPretransitive G Ω 2) [Group.IsSolvable G]
    (hc : Nat.card Ω = 9) (hg : Nat.card G = 144) (o : Ω)
    {E : Type*} [Group E] [Finite E]
    (f : E →* G) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (ho : Nat.Coprime 2 (Nat.card f.ker))
    (hd : f.ker ≤ commutator E) : Function.Injective f := by
  obtain ⟨S,e,c,_⟩ := exists_affine_sylow_comparison ht hc hg o
  let k : Nine →* G := e.toMonoidHom.comp SemidirectProduct.inl
  have hki : Function.Injective k := e.injective.comp SemidirectProduct.inl_injective
  have hcard : Nat.card k.range = 9 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hki).toEquiv]
    simp [Nine,Nat.card_eq_fintype_card]
  have hkp : IsPGroup 3 k.range := IsPGroup.of_card (n := 2) hcard
  have hidx : k.range.index = 16 := by
    have hh := k.range.index_mul_card
    rw [hcard,hg] at hh
    omega
  let T : Sylow 3 G := hkp.toSylow (by rw [hidx]; decide)
  obtain ⟨x,y,r,hgen,hx,hrx,hry⟩ := three_sylow_partial_inversion S
  let t : G := e (SemidirectProduct.inr r)
  have hconj (v : Nine) : t*k v*t⁻¹ = k (planeAction 3 (r : PlaneGL) v) := by
    change e (SemidirectProduct.inr r) * e (SemidirectProduct.inl v) *
      (e (SemidirectProduct.inr r))⁻¹ = e (SemidirectProduct.inl _)
    rw [←map_inv,←map_mul,←map_mul]
    apply congrArg e
    have hh := (SemidirectProduct.inl_aut (φ := sylowPlaneAction S) r v).symm
    rw [map_inv] at hh
    change _ = SemidirectProduct.inl (sylowPlaneAction S r v)
    exact hh
  have hx' : (k x)^3=1 := by rw [←map_pow,hx,map_one]
  have hxy : Commute (k x) (k y) := by
    change k x*k y=k y*k x
    rw [←map_mul,←map_mul,mul_comm]
  have htx : t*k x*t⁻¹=(k x)⁻¹ := by rw [hconj,hrx,map_inv]
  have hty : Commute t (k y) :=
    mul_inv_eq_iff_eq_mul.mp ((hconj y).trans (congrArg k hry))
  obtain ⟨a,ha⟩ := hf (k x)
  obtain ⟨b,hb⟩ := hf (k y)
  have hab := CentralExtension.commute_lifts_of_partial_inversion f hf hk
    (k x) (k y) t (by decide : Nat.Coprime 3 2) hx' hxy htx hty a b ha hb
  have hT : closure ({f a,f b} : Set G) = (T : Subgroup G) := by
    rw [ha,hb]
    change closure ({k x,k y} : Set G) = k.range
    rw [←Set.image_singleton,←Set.image_insert_eq,←MonoidHom.map_closure,hgen]
    exact (MonoidHom.range_eq_map k).symm
  exact CentralExtension.injective_of_odd_stem_of_order_144_of_abelian_three_preimage
    f hf hk hd ho hg T
    (CentralExtension.isMulCommutative_comap_of_pair_lifts f hk T a b hab hT)
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.BinaryPanel
