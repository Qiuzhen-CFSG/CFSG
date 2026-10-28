module

public import Theory.Mathieu.M22.UniversalMultiplier.TwoPrimary.Reduction
public import Theory.Mathieu.M22.UniversalMultiplier.TwoPrimary.HexadLifting
public import Theory.Mathieu.M22.UniversalMultiplier.TwoPrimary.LocalTransfer
public import Theory.Mathieu.M22.UniversalMultiplier.TwoRankSource.FourthPowers
public import Theory.Mathieu.M22.UniversalMultiplier.Basic

/-!
# The two-primary upper bound for perfect central covers of M₂₂

Global involution fusion and the genuine A₆ module-cover theorem make every
central two-kernel cyclic. The fourth-power homomorphism on the native split
hexad preimage, together with odd-index transfer, bounds its exponent by four.
Removing cubic torsion then excludes eight from every finite perfect central
kernel over the actual M₂₂. The odd-primary bounds give divisibility by twelve,
including for the literal canonical universal projection.

The conditional `HexadLiftBound` route is retained as reusable mathematics.
The unconditional bounds use the proved native `TwoRankSource` family and
require no standalone relative hexad bound or cyclic-four covering construction.

Source: Aschbacher–Smith I.1.3(4), printed p.407, with the native local geometry
of I.2.2(6), printed p.412. The final cyclic-twelve assembly is retained in
`UniversalMultiplier`; its independent cyclic-four lower construction is still
needed for the exact multiplier formula.
-/

public section
namespace Sporadic.Mathieu.M22UniversalMultiplier
open PerfectCentralCovering Subgroup
universe u

/-- Every finite perfect central cover of M₂₂ with two-group kernel has cyclic kernel. -/
theorem twoPrimary_kernel_isCyclic
    {E : Type*} [Group E] [Finite E] (f : Cover E M22)
    (hp : IsPGroup 2 f.toMonoidHom.ker) : IsCyclic f.toMonoidHom.ker :=
  TwoRankSource.twoPrimary_kernel_isCyclic f hp

/-- Every element of a two-group kernel over M₂₂ has fourth power one. -/
theorem twoPrimary_kernel_fourth_eq_one
    {E : Type*} [Group E] [Finite E] (f : Cover E M22)
    (hp : IsPGroup 2 f.toMonoidHom.ker) (c : f.toMonoidHom.ker) : c ^ 4 = 1 :=
  TwoRankSource.twoPrimary_kernel_fourth_eq_one f hp c

/-- The order of any two-group perfect central kernel over M₂₂ divides four. -/
theorem twoPrimary_kernel_card_dvd_four
    {E : Type*} [Group E] [Finite E] (f : Cover E M22)
    (hp : IsPGroup 2 f.toMonoidHom.ker) : Nat.card f.toMonoidHom.ker ∣ 4 :=
  TwoRankSource.twoPrimary_kernel_card_dvd_four f hp

/-- The numerical two-primary upper bound, with no additional local hypothesis. -/
theorem twoPrimary_kernel_card_le_four
    {E : Type*} [Group E] [Finite E] (f : Cover E M22)
    (hp : IsPGroup 2 f.toMonoidHom.ker) : Nat.card f.toMonoidHom.ker ≤ 4 :=
  Nat.le_of_dvd (by decide) (twoPrimary_kernel_card_dvd_four f hp)

/-- Eight does not divide the kernel order of any finite perfect central cover of M₂₂. -/
theorem not_eight_dvd_kernel
    {E : Type*} [Group E] [Finite E] (f : Cover E M22) :
    ¬ 8 ∣ Nat.card f.toMonoidHom.ker :=
  TwoRankSource.not_eight_dvd_kernel f

/-- The two-primary and odd-primary bounds apply to the same original covering map. -/
theorem kernel_card_dvd_twelve
    {E : Type*} [Group E] [Finite E] (f : Cover E M22) :
    Nat.card f.toMonoidHom.ker ∣ 12 :=
  kernel_card_dvd_twelve_of_not_eight f (not_eight_dvd_kernel f)

/-- The two-primary upper bound for the actual canonical universal projection. -/
theorem not_eight_dvd_universal_kernel :
    ¬ 8 ∣ Nat.card (universalProjection M22).ker :=
  not_eight_dvd_kernel (universalCover M22)

/-- The full upper bound for the kernel of the actual canonical universal projection. -/
theorem universal_kernel_card_dvd_twelve :
    Nat.card (universalProjection M22).ker ∣ 12 :=
  kernel_card_dvd_twelve (universalCover M22)

/-- The native square identity and transfer consume precisely the local
relative kernel bound, for the literal hexad preimage. -/
theorem twoPrimary_kernel_card_le_four_of_hexad_bound
    (hlocal : HexadLiftBound.{u})
    {E : Type u} [Group E] [Finite E] (f : Cover E M22)
    (hp : IsPGroup 2 f.toMonoidHom.ker) : Nat.card f.toMonoidHom.ker ≤ 4 := by
  let P := m22HexadStabilizer.comap f.toMonoidHom
  let q : P →* m22HexadStabilizer := f.toMonoidHom.subgroupComap m22HexadStabilizer
  have hq : Function.Surjective q :=
    f.toMonoidHom.subgroupComap_surjective_of_surjective m22HexadStabilizer f.surjective
  have hqk {x : P} (hx : x ∈ q.ker) : (x : E) ∈ f.toMonoidHom.ker :=
    congrArg Subtype.val hx
  have hqc : q.ker ≤ center P := fun x hx => mem_center_iff.mpr fun y =>
    Subtype.ext (mem_center_iff.mp (f.ker_le_center (hqk hx)) y)
  let k : q.ker →* f.toMonoidHom.ker :=
    (P.subtype.comp q.ker.subtype).codRestrict _ (fun x => hqk x.property)
  have hki : Function.Injective k := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : f.toMonoidHom.ker => (z : E)) h))
  have hqp : IsPGroup 2 q.ker := hp.of_injective k hki
  obtain ⟨s, hs⟩ := exists_hexadSection_lift f.toMonoidHom f.surjective
    f.ker_le_center hp m22Hexad123_mem
  let t : alternatingGroup (Fin 6) →* P := s.codRestrict P (fun a => by
    change f.toMonoidHom (s a) ∈ m22HexadStabilizer
    have hsa : f.toMonoidHom (s a) = (m22HexadSection m22Hexad123_mem a : M22) :=
      DFunLike.congr_fun hs a
    rw [hsa]
    exact (m22HexadSection m22Hexad123_mem a).property)
  have ht : q.comp t = m22HexadSection m22Hexad123_mem := by
    ext a : 1
    exact Subtype.ext (DFunLike.congr_fun hs a)
  exact (kernel_card_le_hexad_derived_kernel f hp).trans
    (hlocal P q hq hqc hqp ⟨t, ht⟩)

/-- The remaining relative hexad calculation suffices for every finite perfect
central cover of the native M₂₂, including kernels with odd torsion. -/
theorem not_eight_dvd_kernel_of_hexad_bound
    (hlocal : HexadLiftBound.{u})
    {E : Type u} [Group E] [Finite E] (f : Cover E M22) :
    ¬ 8 ∣ Nat.card f.toMonoidHom.ker :=
  not_eight_dvd_kernel_of_twoPrimary_bound
    (fun _ _ _ g hp => twoPrimary_kernel_card_le_four_of_hexad_bound hlocal g hp) f

/-- Application to the existing odd-primary calculation. The only additional
premise is the relative local kernel bound. -/
theorem kernel_card_dvd_twelve_of_hexad_bound
    (hlocal : HexadLiftBound.{u})
    {E : Type u} [Group E] [Finite E] (f : Cover E M22) :
    Nat.card f.toMonoidHom.ker ∣ 12 :=
  kernel_card_dvd_twelve_of_not_eight f (not_eight_dvd_kernel_of_hexad_bound hlocal f)
end Sporadic.Mathieu.M22UniversalMultiplier
