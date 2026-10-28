module

public import Theory.Mathieu.M22.UniversalMultiplier.Basic
public import Theory.Mathieu.M22.UniversalMultiplier.PrimaryBounds

/-!
# Assembly of the cyclic-twelve multiplier calculation for M₂₂

The genuine triple cover supplies a quotient of order three. A genuine
cyclic-four cover would supply a cyclic quotient of order four. If eight
does not divide the universal kernel order, the proved odd-primary bounds
force the whole kernel to have order twelve. Its map onto the cyclic-four
kernel then has kernel of order three. Centrality and coprimality imply
cyclicity, giving the required group isomorphism, not just its order.

Source: Aschbacher–Smith I.1.3(4), printed p.407; I.1.1 specifies the
universal-kernel convention. The cyclic-four cover and the exclusion of
eight remain explicit inputs. Thus this module is a conditional assembly,
not yet an unconditional proof of I.1.3(4).
-/

namespace Sporadic.Mathieu.M22UniversalMultiplier
open Theory.GroupTheory

universe u
variable {L : Type u} [Group L] [Finite L] [IsQuasisimple L]

/-- A genuine cyclic-four cover and an upper bound of twelve force the actual
universal kernel to be cyclic of order twelve. -/
public theorem kernel_equiv_twelve_of_bound_and_cyclic_four_cover
    (f : Covering L M22) (hf : Covering.IsUniversal.{0, u, 0} f)
    (hbound : Nat.card f.toMonoidHom.ker ≤ 12)
    {E : Type} [Group E] [Finite E] [IsQuasisimple E]
    (g : Covering E M22)
    (heg : Nonempty (g.toMonoidHom.ker ≃* Multiplicative (ZMod 4))) :
    Nonempty (f.toMonoidHom.ker ≃* Multiplicative (ZMod 12)) := by
  obtain ⟨eg⟩ := heg
  have hgcard : Nat.card g.toMonoidHom.ker = 4 :=
    (Nat.card_congr eg.toEquiv).trans (Nat.card_zmod 4)
  let a := hf.lift g
  have ha (x : L) : g (a x) = f x :=
    congrArg (fun q : Covering L M22 => q x) (hf.lift_fac g)
  have h4 : 4 ∣ Nat.card f.toMonoidHom.ker := by
    rw [← hgcard]
    exact kernel_card_dvd_of_surjective_factor f.toMonoidHom g.toMonoidHom
      a.toMonoidHom a.surjective (congrArg Covering.toMonoidHom (hf.lift_fac g))
  have h12 : 12 ∣ Nat.card f.toMonoidHom.ker :=
    (show Nat.Coprime 3 4 by decide).mul_dvd_of_dvd_of_dvd (three_dvd_kernel f hf) h4
  have hcard : Nat.card f.toMonoidHom.ker = 12 :=
    le_antisymm hbound (Nat.le_of_dvd Nat.card_pos h12)
  let q : f.toMonoidHom.ker →* g.toMonoidHom.ker :=
    (a.toMonoidHom.comp f.toMonoidHom.ker.subtype).codRestrict _ (fun x => by
      change g (a x) = 1
      rw [ha]
      exact x.property)
  have hqs : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := a.surjective y
    change a x = (y : E) at hx
    have hxf : x ∈ f.toMonoidHom.ker := by
      change f x = 1
      rw [← ha, hx]
      exact y.property
    exact ⟨⟨x, hxf⟩, Subtype.ext hx⟩
  have hqcard : Nat.card q.ker = 3 := by
    have hc := q.ker.card_mul_index
    rw [Subgroup.index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hqs).toEquiv,
      hgcard, hcard] at hc
    omega
  let : IsCyclic q.ker := isCyclic_of_prime_card hqcard
  let : IsCyclic g.toMonoidHom.ker := eg.isCyclic.mpr inferInstance
  let : CommGroup f.toMonoidHom.ker :=
    { (inferInstance : Group f.toMonoidHom.ker) with
      mul_comm := fun x y => Subtype.ext
        (Subgroup.mem_center_iff.mp (f.ker_le_center y.property) x) }
  let : IsCyclic f.toMonoidHom.ker := Group.isCyclic_of_coprime_card_ker q
    (by rw [hqcard, hgcard]; decide) hqs
  exact ⟨mulEquivOfCyclicCardEq (hcard.trans (Nat.card_zmod 12).symm)⟩

/-- The exact cubic part of any chosen universal covering kernel. -/
public theorem sylow_three_kernel_card (f : Covering L M22)
    (hf : Covering.IsUniversal.{0, u, 0} f) (P : Sylow 3 f.toMonoidHom.ker) :
    Nat.card P = 3 := by
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hn0 : n ≠ 0 := by
    intro h0
    have hd := P.dvd_card_of_dvd_card (three_dvd_kernel f hf)
    rw [hn, h0, pow_zero] at hd
    exact (by decide : ¬ 3 ∣ 1) hd
  have hn2 : n < 2 := by
    by_contra! h2
    exact not_nine_dvd_kernel (PerfectCentralCovering.ofCovering f)
      ((pow_dvd_pow 3 h2).trans (hn ▸ (P : Subgroup f.toMonoidHom.ker).card_subgroup_dvd_card))
  have hn1 : n = 1 := by omega
  simpa [hn1] using hn

/-- Source assembly from precisely the missing two-primary bound and the
independent cyclic-four covering construction. Both premises must still be proved. -/
public theorem kernel_equiv_twelve_of_not_eight_and_cyclic_four_cover
    (f : Covering L M22) (hf : Covering.IsUniversal.{0, u, 0} f)
    (h8 : ¬ 8 ∣ Nat.card f.toMonoidHom.ker)
    {E : Type} [Group E] [Finite E] [IsQuasisimple E]
    (g : Covering E M22)
    (heg : Nonempty (g.toMonoidHom.ker ≃* Multiplicative (ZMod 4))) :
    Nonempty (f.toMonoidHom.ker ≃* Multiplicative (ZMod 12)) :=
  kernel_equiv_twelve_of_bound_and_cyclic_four_cover f hf
    (Nat.le_of_dvd (by decide)
      (kernel_card_dvd_twelve_of_not_eight (PerfectCentralCovering.ofCovering f) h8)) g heg

end Sporadic.Mathieu.M22UniversalMultiplier
