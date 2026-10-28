module
public import Theory.Representation.SemilinearFixedIndex
public import Theory.Representation.SymplecticNaturalNormalizer.FixedLineInner

/-!
# Small offenders have no field twist

In a faithful semilinear action on F4^4, an offender with fixed quotient of
order at most sixteen is field-linear. A nontrivial twist would make its
fixed space a binary four-space whose two scalar translates span the entire
module. Its pointwise fixer then has at most four elements, contradicting
the offender inequality. For a centric symplectic component this also places
the offender inside the actual component.

Source application: MS93 (5.0)--(5.7), pp.912--919. The original tensor
consumer is Sp4Four.SourceComparison.OriginalSmallMovers.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
namespace Representation
variable {G F : Type*} [Group G] [Field F] [Finite F] [Algebra (ZMod 2) F]

theorem linear_on_small_offender
    (hF : Nat.card F = 4) (ρ : Representation (ZMod 2) G (Vector F))
    (hfaith : Function.Injective ρ)
    (hsemi : ∀ a : G, ∃ σ : F ≃+* F, ∀ c v, ρ a (c • v) = σ c • ρ a v)
    (A : Subgroup G) [Finite A]
    (hsmall : Nat.card (Vector F ⧸ fixedSpace ρ A) ≤ 16)
    (hoff : Nat.card (Vector F ⧸ fixedSpace ρ A) ≤ Nat.card A) :
    ∀ a ∈ A, ∀ (c : F) v, ρ a (c • v) = c • ρ a v := by
  classical
  by_contra! hn
  obtain ⟨a,ha,c,v,hcv⟩ := hn
  obtain ⟨σ,hσ⟩ := hsemi a
  have hne : σ ≠ RingEquiv.refl F := by
    intro he
    apply hcv
    rw [hσ,he]
    rfl
  have hquot : Nat.card (Vector F ⧸ fixedSpace ρ A) = 16 :=
    le_antisymm hsmall (sixteen_le_fixed_quotient_card_of_twist hF ρ A ha hne hσ)
  have hV : Nat.card (Vector F) = 256 := by
    rw [Module.natCard_eq_pow_finrank (K := F)]
    simp [Theory.SpecificGroups.SymplecticFour.Vector,hF]
  have hmul : Nat.card (fixedSpace ρ A) * Nat.card (Vector F ⧸ fixedSpace ρ A) = 256 := by
    rw [←hV, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Vector F ⧸ fixedSpace ρ A),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Vector F),←pow_add,add_comm,
      (fixedSpace ρ A).finrank_quotient_add_finrank]
  have hfix : Nat.card (fixedSpace ρ A) = 16 := by rw [hquot] at hmul; omega
  obtain ⟨d,hd⟩ : ∃ d : F, σ d ≠ d := by
    by_contra! h
    exact hne (RingEquiv.ext h)
  let f : fixedSpace ρ A × fixedSpace ρ A → Vector F := fun p => p.1.val+d•p.2.val
  have hf : Function.Injective f := by
    rintro ⟨w,z⟩ ⟨w',z'⟩ he
    change w.val+d•z.val=w'.val+d•z'.val at he
    have hh : d•(z.val-z'.val)=w'.val-w.val := by
      rw [smul_sub]
      exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa only [add_comm] using he)
    have hh' := congrArg (ρ a) hh
    have hw : ρ a w.val = w.val := w.property ⟨a,ha⟩
    have hw' : ρ a w'.val = w'.val := w'.property ⟨a,ha⟩
    have hz : ρ a z.val = z.val := z.property ⟨a,ha⟩
    have hz' : ρ a z'.val = z'.val := z'.property ⟨a,ha⟩
    rw [hσ,map_sub,map_sub,hw,hw',hz,hz',←hh] at hh'
    have hzero : (σ d-d) • (z.val-z'.val)=0 := by rw [sub_smul,hh',sub_self]
    have hez : z=z' := Subtype.ext (sub_eq_zero.mp
      ((smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hd)))
    have hew : w=w' := by
      rw [hez] at he
      exact Subtype.ext (add_right_cancel he)
    exact Prod.ext hew hez
  have hfs : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,by simp [Nat.card_prod,hfix,hV]⟩).2
  choose τ hτ using hsemi
  have hτinj : Function.Injective (fun x : A => τ x.val d) := by
    intro x y hxy
    change τ x.val d = τ y.val d at hxy
    apply Subtype.ext
    apply hfaith
    apply LinearMap.ext
    intro v
    obtain ⟨⟨w,z⟩,rfl⟩ := hfs v
    change ρ x.val (w.val+d•z.val) = ρ y.val (w.val+d•z.val)
    have hfixed (u : fixedSpace ρ A) (g : A) : ρ g.val u.val = u.val := u.property g
    rw [map_add,map_add,hτ,hτ,hfixed w x,hfixed w y,hfixed z x,hfixed z y,hxy]
  have hc : Nat.card A ≤ 4 := (Nat.card_le_card_of_injective _ hτinj).trans_eq hF
  rw [hquot] at hoff
  omega

/-- Small offenders in a faithful ambient natural action lie in its actual
centric symplectic component. -/
theorem small_offender_le_symplectic_component [CharP F 2]
    (hF : Nat.card F = 4) (B : Subgroup G) [B.Normal]
    (hcent : centralizer (B : Set G) ≤ B) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) G (Vector F)) (hfaith : Function.Injective ρ)
    (hB : ∀ b : B, ∀ v, ρ (b:G) v = symplecticNatural 2 (e b) v)
    (A : Subgroup G) [Finite A]
    (hsmall : Nat.card (Vector F ⧸ fixedSpace ρ A) ≤ 16)
    (hoff : Nat.card (Vector F ⧸ fixedSpace ρ A) ≤ Nat.card A) : A ≤ B := by
  have hsemi (a : G) : ∃ σ : F ≃+* F, ∀ c v, ρ a (c • v) = σ c • ρ a v :=
    SymplecticNaturalNormalizer.exists_field_twist
      ⟨SymplecticConjugatePair.Ambient.linearAction ρ a,
        SymplecticNaturalNormalizer.operator_mem_naturalNormalizer B (by omega) e ρ hB a⟩
  have hlin := linear_on_small_offender hF ρ hfaith hsemi A hsmall hoff
  have hmul : Nat.card (fixedSpace ρ A) * Nat.card (Vector F ⧸ fixedSpace ρ A) = 256 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Vector F ⧸ fixedSpace ρ A),
      ←pow_add,add_comm,(fixedSpace ρ A).finrank_quotient_add_finrank,
      ←Module.natCard_eq_pow_finrank (K := ZMod 2)]
    rw [Module.natCard_eq_pow_finrank (K := F)]
    simp [Theory.SpecificGroups.SymplecticFour.Vector,hF]
  have hfix : 1 < Nat.card (fixedSpace ρ A) := by nlinarith
  let := Fintype.ofFinite (fixedSpace ρ A)
  let : Nontrivial (fixedSpace ρ A) := Fintype.one_lt_card_iff_nontrivial.mp (by simpa only [Nat.card_eq_fintype_card] using hfix)
  obtain ⟨v,hv⟩ := exists_ne (0 : fixedSpace ρ A)
  have hv0 : v.val ≠ 0 := fun h => hv (Subtype.ext h)
  intro a ha
  apply SymplecticNaturalNormalizer.mem_component_of_fixes_field_line
    B hcent (by omega) e ρ hB a v.val hv0
  intro c
  rw [hlin a ha]
  exact congrArg (c • ·) (show ρ a v.val = v.val from v.property ⟨a,ha⟩)
end Representation
