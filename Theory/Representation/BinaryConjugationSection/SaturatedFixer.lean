module
public import Theory.Representation.BinaryConjugationSection.CentralImage
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.PrimeRankOrderBound
/-!
# Centralizing actors when a reduced section fills the automorphism rank

The coordinate map of a reduced binary section factors through its inner
conjugation image. If the image is no larger than the coordinate module,
the two kernels coincide. When the module fills an upper bound on the
elementary two-rank of Aut(I), adjoining any commuting involution cannot
enlarge that image. Such an involution is therefore inner by a vector fixed
by the original actor, and equality of kernels makes it trivial.

The source application is the natural-plus-dual comparison in
Aschbacher--Smith 10.2.9, printed pp.750--751. Fixed vectors are retained in
the coordinate kernel; no splitting or irreducibility is required.
-/

public section
open Subgroup Theory.GroupTheory
namespace Representation.BinaryConjugationSection
variable {G K : Type*} [Group G] [Group K] [Finite G]
  {H A B : Subgroup G} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} (d : BinaryConjugationSection H A B ρ)
/-- A coordinate quotient of maximal possible size has exactly the image kernel. -/
theorem ker_eq_of_card_range_le (f : A →* K) (hk : f.ker ≤ d.coordinates.ker)
    (hc : Nat.card f.range ≤ Nat.card W) : f.ker = d.coordinates.ker := by
  let g := QuotientGroup.lift f.ker d.coordinates (fun a ha => MonoidHom.mem_ker.mp (hk ha))
  have hg : Function.Surjective g := by
    intro w
    obtain ⟨a,ha⟩ := d.onto w
    exact ⟨QuotientGroup.mk' f.ker a,ha⟩
  have hi : Function.Injective g := (hg.bijective_of_nat_card_le (by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact hc)).injective
  apply le_antisymm hk
  intro a ha
  apply (QuotientGroup.eq_one_iff a).mp
  apply hi
  exact (MonoidHom.mem_ker.mp ha).trans (map_one g).symm
end Representation.BinaryConjugationSection

namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] [Finite G]
  {L A I U : Subgroup G} [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 U]

/-- An elementary actor centralizing the original group also centralizes the
containing group when the literal reduced section fills its automorphism rank. -/
theorem centralizes_of_saturated_automorphism_rank
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) L W}
    (d : BinaryConjugationSection L A (A ⊓ centralizer (L : Set G)) ρ)
    (hLI : L ≤ I) (hUN : U ≤ normalizer (I : Set G))
    (hUL : U ≤ centralizer (L : Set G))
    {m : ℕ} (hc : 2^m ≤ Nat.card W) (hr : primeRank 2 (MulAut I) ≤ m) :
    U ≤ centralizer (I : Set G) := by
  have hAI : A ≤ I := d.section_le.trans hLI
  let f : A →* MulAut I := (MulAut.conj : I →* MulAut I).comp (inclusion hAI)
  let E := f.range
  let : IsElementaryAbelian 2 E := by
    change IsElementaryAbelian 2 f.range
    rw [MonoidHom.range_eq_map]
    let : IsElementaryAbelian 2 (⊤ : Subgroup A) :=
      { toIsMulCommutative := inferInstance
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
          (fun a => Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 A) a.val)) }
    exact IsElementaryAbelian.map f
  have hk : f.ker ≤ d.coordinates.ker := by
    intro a ha
    apply (d.coordinates_eq_one_iff a).mpr
    refine ⟨a.property,?_⟩
    intro l hl
    have hh := congrArg (fun b : MulAut I => (b ⟨l,hLI hl⟩ : G)) ha
    change a.val * l * a.val⁻¹ = l at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hu := (primeRank_le_iff_elementary_card_le (MulAut I)).mp hr E inferInstance
  have heker := d.ker_eq_of_card_range_le f hk (hu.trans hc)
  have hbig : 2^m ≤ Nat.card E := hc.trans (d.card_le_range f hk)
  intro u huU
  let b : MulAut I := I.normalizerMonoidHom ⟨u,hUN huU⟩
  have hbfix (l : L) : b (inclusion hLI l) = inclusion hLI l := by
    apply Subtype.ext
    change u * l.val * u⁻¹ = l.val
    exact mul_inv_eq_iff_eq_mul.mpr (hUL huU l.val l.property).symm
  have hb2 : b^2 = 1 := by
    have hu2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) u huU
    change (I.normalizerMonoidHom ⟨u,hUN huU⟩)^2=1
    rw [←map_pow]
    have he : (⟨u,hUN huU⟩ : normalizer (I : Set G))^2=1 :=
      Subtype.ext hu2
    rw [he,map_one]
  have hbC : b ∈ centralizer (E : Set (MulAut I)) := by
    rintro _ ⟨a,rfl⟩
    have hbA : b (inclusion hAI a) = inclusion hAI a :=
      hbfix ⟨a,d.section_le a.property⟩
    apply MulEquiv.ext
    intro x
    change (inclusion hAI a) * b x * (inclusion hAI a)⁻¹ =
      b ((inclusion hAI a) * x * (inclusion hAI a)⁻¹)
    simp only [map_mul,map_inv,hbA]
  let : IsElementaryAbelian 2 (zpowers b) := IsElementaryAbelian.zpowers_of_pow_eq_one hb2
  let : IsElementaryAbelian 2 (E ⊔ zpowers b : Subgroup (MulAut I)) :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hbC)
  have hbound := (primeRank_le_iff_elementary_card_le (MulAut I)).mp hr
    (E ⊔ zpowers b) inferInstance
  have he : E = E ⊔ zpowers b := eq_of_le_of_card_ge le_sup_left (hbound.trans hbig)
  have hbE : b ∈ E := by
    rw [he]
    exact (show zpowers b ≤ E ⊔ zpowers b from le_sup_right) (mem_zpowers b)
  obtain ⟨a,ha⟩ := hbE
  have hac : (a : G) ∈ centralizer (L : Set G) := by
    intro l hl
    have hh := congrArg (fun x : I => (x : G)) (hbfix ⟨l,hl⟩)
    rw [←ha] at hh
    change a.val * l * a.val⁻¹ = l at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have had : a ∈ d.coordinates.ker := (d.coordinates_eq_one_iff a).mpr ⟨a.property,hac⟩
  have haf : a ∈ f.ker := heker.symm ▸ had
  have hb : b = 1 := ha.symm.trans (MonoidHom.mem_ker.mp haf)
  intro i hi
  have hh := congrArg (fun a : MulAut I => (a ⟨i,hi⟩ : G)) hb
  change u*i*u⁻¹=i at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm
end Representation.BinaryConjugationSection
