module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.CubicNatural
public import Theory.GroupTheory.PrimeRankNormalIntersection
public import Theory.GroupAction.ComponentRankAction.PrimeClosure

/-!
# Cubic containment through the original natural action image

The kernel meets the marked SL₃ subgroup in a prime-to-three group. An
ambient kernel divisible by three would meet an elementary plane in that
subgroup, by the rank-two normal-intersection argument, a contradiction.
The actual image therefore inherits the rank bound. Its faithful natural
SL₃ marking gives cubic containment, which lifts across the original kernel.
No splitting or centrality of that kernel is required.

Source: Aschbacher--Smith A.3.19, printed pp.54--55, for the application in
11.0.4, printed p.760. CubicSeed applies this to the literal chosen seed.
The final preliminary owner retains invariant-constituent selection.
-/

public noncomputable section
open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.CubicNatural
variable {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    [Group H] [Finite H]

/-- The ambient action kernel is prime to three if it is prime to three on
a full-rank normal subgroup. No centrality of the original kernel is assumed. -/
theorem kernel_coprime_of_rank_two {A : Type*} [Group A]
    (f : H →* A) (L : Subgroup H)
    (hker : Nat.Coprime 3 (Nat.card (f.comp L.subtype).ker))
    (hrL : 2 ≤ primeRank 3 L) (hr : primeRank 3 H ≤ 2) :
    Nat.Coprime 3 (Nat.card f.ker) := by
  classical
  have heq : primeRank 3 L = 2 := le_antisymm
    ((Theory.GroupTheory.primeRank_le_of_injective 3 L.subtype L.subtype_injective).trans hr) hrL
  obtain ⟨B,hB,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := L) (p := 3)
  let := hB
  let E := B.map L.subtype
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.map L.subtype
  have hc : Nat.card E = 3 ^ 2 := by
    rw [card_map_of_injective L.subtype_injective,hcard,heq]
  have hi := injective_comp_subtype_of_coprime_ker (f.comp L.subtype) hker B
    (IsElementaryAbelian.isPGroup 3 B)
  have hinf : E ⊓ f.ker = ⊥ := by
    apply eq_bot_iff.mpr
    rintro y ⟨⟨b,hb,rfl⟩,hy⟩
    have he : (⟨b,hb⟩ : B) = 1 := hi (by
      change f b = f 1
      rw [map_one]
      exact hy)
    exact congrArg (fun z : B => (z.val : H)) he
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro hd
  exact E.inf_ne_bot_of_elementary_plane f.ker
    (by rw [normalizer_eq_top]; exact le_top) hd hc hr hinf

/-- Cubic containment through the actual, possibly nonfaithful natural action.
Only its restriction to L has a prime-to-three kernel; the ambient kernel bound
is deduced from the ambient three-rank. -/
theorem cubic_mem_of_natural_quotient
    (L : Subgroup H) [L.Normal] (η : L →* SL(3,F))
    (hη : Function.Surjective η) (hηker : Nat.Coprime 3 (Nat.card η.ker))
    (ρ : Representation (ZMod 2) H (Fin 3 → F))
    (hnat : ∀ (g : L) (v : Fin 3 → F), ρ (g : H) v = (η g).val.mulVec v)
    (hd : 3 ∣ Nat.card F - 1) (hr : primeRank 3 H ≤ 2)
    (x : H) (hx : x ^ 3 = 1) : x ∈ L := by
  classical
  let A := ρ.asGroupHom.range
  let f : H →* A := ρ.asGroupHom.rangeRestrict
  let σ : Representation (ZMod 2) A (Fin 3 → F) := (Units.coeHom _).comp A.subtype
  have hσ : Function.Injective σ := by
    intro a b hab
    exact Subtype.ext (Units.ext hab)
  have hrep (h : H) : σ (f h) = ρ h := rfl
  have hf : Function.Surjective f := ρ.asGroupHom.rangeRestrict_surjective
  let : Finite A := Finite.of_surjective f hf
  let K := L.map f
  let j := f.subgroupMap L
  have hj : Function.Surjective j := f.subgroupMap_surjective L
  have hjker : j.ker = η.ker := by
    ext l
    constructor
    · intro hl
      apply Subtype.ext
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      have hh := congrArg (fun a : K => σ a.val v) hl
      change ρ (l : H) v = v at hh
      change (η l).val.mulVec v = (1 : SL(3,F)).val.mulVec v
      exact (hnat l v).symm.trans (hh.trans (Matrix.one_mulVec v).symm)
    · intro hl
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      apply LinearMap.ext
      intro v
      change ρ (l : H) v = v
      rw [hnat,hl]
      exact Matrix.one_mulVec v
  let q : SL(3,F) →* K := η.liftOfSurjective hη ⟨j,hjker.ge⟩
  have hq (l : L) : q (η l) = j l :=
    η.liftOfRightInverse_comp_apply (Function.surjInv hη)
      (Function.rightInverse_surjInv hη) ⟨j,hjker.ge⟩ l
  have hqn (a : SL(3,F)) (v : Fin 3 → F) : σ (q a).val v = a.val.mulVec v := by
    obtain ⟨l,rfl⟩ := hη a
    rw [hq]
    exact hnat l v
  have hqi : Function.Injective q := by
    intro a b hab
    apply Subtype.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    change a.val.mulVec v = b.val.mulVec v
    rw [← hqn a v,← hqn b v,hab]
  have hqs : Function.Surjective q := by
    intro k
    obtain ⟨l,rfl⟩ := hj k
    exact ⟨η l,hq l⟩
  let e : K ≃* SL(3,F) := (MulEquiv.ofBijective q ⟨hqi,hqs⟩).symm
  have hen (k : K) (v : Fin 3 → F) : σ (k : A) v = (e k).val.mulVec v := by
    have he : q (e k) = k := (MulEquiv.ofBijective q ⟨hqi,hqs⟩).apply_symm_apply k
    rw [← hqn,he]
  have hkL : Nat.Coprime 3 (Nat.card (f.comp L.subtype).ker) := by
    have he : (f.comp L.subtype).ker = j.ker := by
      ext l
      change f (l : H) = 1 ↔ j l = 1
      constructor
      · exact fun h => Subtype.ext h
      · exact fun h => congrArg Subtype.val h
    rwa [he,hjker]
  have hrL : 2 ≤ primeRank 3 L := by
    rw [primeRank_eq_of_surjective_of_coprime 3 η hη hηker]
    exact Matrix.PSL3.SplitPrimeRank.special_rank F hd
  have hk := kernel_coprime_of_rank_two f L hkL hrL hr
  have hrA : primeRank 3 A ≤ 2 :=
    (primeRank_le_of_surjective_of_coprime 3 f hf hk).trans hr
  let : K.Normal := Subgroup.Normal.map inferInstance f hf
  have himage : f x ∈ K := cubic_mem_of_natural K e σ hσ hen hd hrA (f x)
    (by rw [← map_pow,hx,map_one])
  by_cases hxe : x = 1
  · exact hxe ▸ L.one_mem
  exact Theory.GroupAction.ComponentRankAction.prime_element_mem_of_image_mem f hk L x
    (orderOf_eq_prime hx hxe) himage

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.CubicNatural
