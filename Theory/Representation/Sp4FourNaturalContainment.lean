module
public import Theory.Representation.SymplecticConjugatePair.Ambient.Normalizer
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.TwoSylowSource
public import Theory.SpecificGroups.SymplecticFour.OddFieldActors.Torus
public import Theory.GroupAction.ComponentRankAction
public import Theory.GroupTheory.PResidual.Quotient

/-!
# Rank-two ambient actions containing the natural Sp₄(4) layer

The natural symplectic commutant consists of field scalars. Its elements
have cube one over the field of four elements. The full cubic rank of Sp₄(4)
and the ambient rank bound force its centralizer to have order prime to three,
so faithfulness makes this centralizer trivial. Ambient conjugation is
therefore injective. The actual outer automorphism group has order four,
which places the ambient two-residual in the specified symplectic layer.

This is the marked natural-module specialization of the rank argument in
Aschbacher--Smith A.3.18, printed pp.51--53, used in13.7.6, printed p.940.
No later point-residual containment or carrier-only section is assumed.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer
namespace Representation.Sp4FourNaturalContainment
variable {F H : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group H] [Finite H]

/-- The ambient centralizer of the marked natural symplectic layer is trivial. -/
theorem centralizer_eq_bot_of_natural (hF : Nat.card F = 4)
    (L : Subgroup H) (e : L ≃* Sp F)
    (ρ : Representation (ZMod 2) H (Vector F)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Vector F), ρ (g : H) v = symplecticNatural 2 (e g) v)
    (hr : primeRank 3 H ≤ 2) : centralizer (L : Set H) = ⊥ := by
  have hz : center L = ⊥ := by
    apply bot_unique
    intro x hx
    have he : e x ∈ center (Sp F) := ((centerCongr e) ⟨x,hx⟩).property
    rw [EvenProjective.center_eq_bot, mem_bot] at he
    exact e.injective (he.trans (map_one e).symm)
  have hrL : 2 ≤ primeRank 3 L := by
    rw [primeRank_congr 3 e]
    exact OddFieldActors.split_prime_rank (by simp [hF])
  have hcop := Theory.GroupAction.ComponentRankAction.centralizer_coprime L
    (p := 3) (by rw [hz]; simp) hrL hr
  apply bot_unique
  intro x hx
  obtain ⟨c, hc⟩ := natural_commutant_of_pair centralizer_block_scalars (ρ x) (by
    intro y v
    let l := e.symm y.val
    have hl (w : Vector F) : ρ (l : H) w = naturalDerivedAction y w := by
      rw [hnat, e.apply_symm_apply]
      rfl
    rw [← hl, ← hl]
    have hcomm : x * (l : H) = (l : H) * x :=
      (mem_centralizer_iff.mp hx l l.property).symm
    have hh := LinearMap.congr_fun (congrArg ρ hcomm) v
    simpa only [map_mul, Module.End.mul_apply] using hh)
  have hc0 : c ≠ 0 := by
    intro hc0
    have he : ρ x (Pi.single (Sum.inl 0) 1) = ρ x 0 := by rw [hc, hc0]; simp
    have hh := (ρ.apply_bijective x).1 he
    have hv := congrFun hh (Sum.inl 0)
    simp at hv
  have hc3 : c ^ 3 = 1 := by
    have hh := pow_card_eq_one' (x := Units.mk0 c hc0)
    have hu : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
    rw [hu] at hh
    exact congrArg Units.val hh
  have hx3 : x ^ 3 = 1 := by
    apply hfaith
    apply LinearMap.ext
    intro v
    rw [map_pow, map_one]
    change (ρ x * (ρ x * (ρ x * 1))) v = v
    simp only [Module.End.mul_apply, Module.End.one_apply, hc, smul_smul]
    rw [← mul_assoc, ← pow_two, ← pow_succ, hc3, one_smul]
  let y : centralizer (L : Set H) := ⟨x,hx⟩
  have hy3 : y ^ 3 = 1 := Subtype.ext hx3
  have ho : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hy3) (orderOf_dvd_natCard y)
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp ho)

/-- The actual ambient two-residual lies in its marked natural Sp₄(4) layer. -/
theorem pResidual_le_of_natural (hF : Nat.card F = 4)
    (L : Subgroup H) [L.Normal] (e : L ≃* Sp F)
    (ρ : Representation (ZMod 2) H (Vector F)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Vector F), ρ (g : H) v = symplecticNatural 2 (e g) v)
    (hr : primeRank 3 H ≤ 2) : pResidual 2 H ≤ L := by
  let f : H →* MulAut (Sp F) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := L))
  have hinj : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro x hx
    have he : MulAut.conjNormal (H := L) x = 1 :=
      (MulAut.congr e).injective (hx.trans (map_one (MulAut.congr e)).symm)
    have hc : x ∈ centralizer (L : Set H) := by
      apply mem_centralizer_iff.mpr
      intro l hl
      have hh := congrArg Subtype.val (DFunLike.congr_fun he ⟨l,hl⟩)
      change x * l * x⁻¹ = l at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    simpa only [centralizer_eq_bot_of_natural hF L e ρ hfaith hnat hr, mem_bot] using hc
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))
  have houter : IsPGroup 2 (MulAut.Outer (Sp F)) := IsPGroup.of_card (n := 2)
    (DiagramAutomorphisms.card_outer_eq_two_mul (m := 2) (by simpa using hF) (by decide))
  have hres := pResidual_le_ker_of_isPGroup 2 (q.comp f) houter
  intro x hx
  have hi : f x ∈ MulAut.innerSubgroup (Sp F) :=
    (QuotientGroup.eq_one_iff (f x)).mp (hres hx)
  obtain ⟨g, hg⟩ := hi
  have he : f (e.symm g : L) = MulAut.conj g := by
    change MulAut.congr e (MulAut.conjNormal (e.symm g : H)) = _
    rw [MulAut.conjNormal_val]
    apply MulEquiv.ext
    intro y
    change e (e.symm g * e.symm y * (e.symm g)⁻¹) = g * y * g⁻¹
    simp
  have heq : x = (e.symm g : L) := hinj (hg.symm.trans he.symm)
  rw [heq]
  exact (e.symm g).property

end Representation.Sp4FourNaturalContainment
