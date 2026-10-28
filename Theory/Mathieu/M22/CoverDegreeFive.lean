module
public import Theory.Representation.AbelianFrobeniusDegree
public import Theory.Mathieu.M22.Properties.ElevenFiveFrobenius
public import Theory.Mathieu.M22.UniversalMultiplier.PrimaryBounds
public import Theory.GroupTheory.CentralCoprimePrimeLift
public import Theory.GroupTheory.CentralExtensionSections

/-!
# A degree bound for full Mathieu twenty-two covers

The certified eleven-by-five Frobenius subgroup of M₂₂ lifts through every
perfect central cover: central Sylow transfer excludes five and eleven from
the covering kernel. Its faithful weight orbit forces degree at least five
in characteristic different from eleven. Taking the derived group of a
central preimage extends the bound to Mathieu covers embedded in central
images, with the full covering center retained.

Source: Aschbacher--Smith H.12.1, printed p.394, and the weight-orbit argument
of G.7.2(2), pp.347--348. The application excludes the four-dimensional
classical models in the component comparison of 4.2.13, p.612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M22CentralCover

/-- Every faithful representation of a full perfect M₂₂ cover has degree at least five
away from characteristic eleven. -/
theorem faithful_degree_ge_five
    {F E V : Type*} [Field F] [Group E] [Finite E]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (f : PerfectCentralCovering.Cover E M22)
    (ρ : Representation F E V) (hρ : Function.Injective ρ)
    (h11 : (11 : F) ≠ 0) : 5 ≤ Module.finrank F V := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨v,hv⟩ := exists_prime_orderOf_dvd_card' (G := M22) 5 (by rw [m22_order]; decide)
  obtain ⟨K,hK,hn,hfree⟩ := m22_exists_eleven_five v hv
  have h5cop : Nat.Coprime 5 (Nat.card f.toMonoidHom.ker) :=
    (Nat.prime_five.coprime_iff_not_dvd).mpr
      (M22UniversalMultiplier.not_dvd_kernel_of_ne_two_three f (by decide) (by decide) (by decide))
  have h11cop : Nat.Coprime 11 (Nat.card f.toMonoidHom.ker) :=
    (Nat.prime_eleven.coprime_iff_not_dvd).mpr
      (M22UniversalMultiplier.not_dvd_kernel_of_ne_two_three f (by decide) (by decide) (by decide))
  obtain ⟨C,hC,hCm,_,_,hiC⟩ := exists_prime_lift_of_central_coprime
    f.toMonoidHom f.surjective f.ker_le_center h5cop (zpowers v)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,hv,pow_one]))
  obtain ⟨P,hP,hPm,hN,_,hiP⟩ := exists_prime_lift_of_central_coprime
    f.toMonoidHom f.surjective f.ker_le_center h11cop K
    (IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hK))
  have hCc : Nat.card C = 5 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hiC).toEquiv]
    rw [MonoidHom.range_comp,range_subtype]
    rw [hCm,Nat.card_zpowers,hv]
  have hPc : Nat.card P = 11 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hiP).toEquiv]
    rw [MonoidHom.range_comp,range_subtype]
    rw [hPm,hK]
  let : IsCyclic P := isCyclic_of_prime_card hPc
  let : Nontrivial P := (Finite.one_lt_card_iff_nontrivial (α := P)).mp (by rw [hPc]; decide)
  have hCP : C ≤ normalizer (P : Set E) := by
    rw [←hN,←map_le_iff_le_comap,hCm]
    exact hn
  have hfreeP (c : C) (hc : c ≠ 1) (k : P)
      (hck : (c : E) * (k : E) * (c : E)⁻¹ = k) : k = 1 := by
    apply hiP
    change f.toMonoidHom (k : E) = f.toMonoidHom 1
    rw [map_one]
    apply hfree (f.toMonoidHom c) (hCm ▸ mem_map_of_mem _ c.property)
    · intro he
      exact hc (hiC (he.trans (map_one f.toMonoidHom).symm))
    · exact hPm ▸ mem_map_of_mem _ k.property
    · simpa only [map_mul,map_inv] using congrArg f.toMonoidHom hck
  simpa only [hCc] using
    Representation.card_le_finrank_of_fixedPointFree_normalizer_of_field ρ P C hρ
      (by simpa only [hPc,Nat.cast_ofNat] using h11) hCP hfreeP

/-- The same bound holds when the full Mathieu cover lies in a central image
of the faithfully represented group. -/
theorem faithful_degree_ge_five_of_central_image
    {F E Q V : Type*} [Field F] [Group E] [Finite E] [Group Q]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : E →* Q) (hq : Function.Surjective q) (hk : q.ker ≤ center E)
    (B : Subgroup Q) [IsQuasisimple B] (e : (B ⧸ center B) ≃* M22)
    (ρ : Representation F E V) (hρ : Function.Injective ρ)
    (h11 : (11 : F) ≠ 0) : 5 ≤ Module.finrank F V := by
  let U := B.comap q
  let r : U →* B := q.subgroupComap B
  have hr : Function.Surjective r := q.subgroupComap_surjective_of_surjective B hq
  have hrk : r.ker ≤ center U := by
    intro x hx
    exact mem_center_iff.mpr fun y => Subtype.ext
      (mem_center_iff.mp (hk (congrArg Subtype.val hx)) y)
  let d := CentralExtension.derivedCover r hr hrk
  let := d.isPerfect
  let a := d.quotientCenterEquiv.trans e
  let f : PerfectCentralCovering.Cover (commutator U) M22 := {
    toMonoidHom := a.toMonoidHom.comp (QuotientGroup.mk' (center (commutator U)))
    surjective := a.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := inferInstance
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ a.injective,QuotientGroup.ker_mk'] }
  let i := U.subtype.comp (commutator U).subtype
  exact faithful_degree_ge_five f (ρ.comp i)
    (hρ.comp (U.subtype_injective.comp (commutator U).subtype_injective)) h11

end Sporadic.Mathieu.M22CentralCover
