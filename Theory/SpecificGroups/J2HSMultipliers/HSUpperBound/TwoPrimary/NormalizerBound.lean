module

public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.Reduction
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.NormalizerBound.Prelude
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.NormalizerBound.Quotient
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.NormalizerBound.IntegralCore
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.LocalReduction

/-!
# The HS normalizer kernel bound with a core section and involution lift

For an arbitrary finite perfect central two-cover g:D→N of the actual HS
normalizer, put A=g⁻¹(O₂(N)) and R=[A,D]. The quotient D/R maps onto
N/O₂(N)=SL₃(2), with central two-kernel equal to the image of ker(g).
The specified lift of s₀ remains a nonidentity involution downstairs.
The dihedral Sylow and involution-fusion result in `Quotient` therefore
kills that quotient kernel, proving ker(g)≤R.

The core-section hypothesis makes A abelian. The integral crossed-homomorphism
calculation in `IntegralCore`, applied to the literal conjugation action on
O₂(N), proves |R∩ker(g)|≤2. Together these results bound the entire kernel
by two, for arbitrary finite perfect central two-covers with the specified
section and involution lift. The actual HS restriction application discharges
the local-kernel premise of `not_four_dvd_of_core_section_of_local_bound`;
only the separately supplied core section remains in that application.

Source: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407, and the normalizer
argument for HS in I.2.2(5), printed p.412. The quotient step here handles
arbitrary kernels and uses the literal normalizer quotient and s₀ lift.
-/

public section

namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound
open Subgroup
open Sporadic.LeechRelated.HS BlockNormalizer

variable {D : Type*} [Group D] [Finite D] [Group.IsPerfect D]

/-- The specified noncore involution lift forces the full central kernel into
the core displacement subgroup. The core section is not needed for this step. -/
theorem kernel_le_coreDisplacements
    (g : D →* baseNormalizer) (hg : Function.Surjective g)
    (hk : g.ker ≤ center D) (hp : IsPGroup 2 g.ker)
    (hlift : ∃ x : D, g x = normalizerInvolution ∧ x ^ 2 = 1) :
    g.ker ≤ coreDisplacements g := by
  let R := coreDisplacements g
  let p := QuotientGroup.mk' R
  have hRQ : R ≤ (pCore 2 baseNormalizer).comap g := coreDisplacements_le g
  let q : (D ⧸ R) →* (baseNormalizer ⧸ pCore 2 baseNormalizer) :=
    QuotientGroup.map R (pCore 2 baseNormalizer) g hRQ
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 baseNormalizer) y
    obtain ⟨y, rfl⟩ := hg y
    exact ⟨p y, rfl⟩
  have hker : q.ker = g.ker.map p := by
    dsimp only [q]
    rw [QuotientGroup.ker_map]
    change (corePreimage g).map p = g.ker.map p
    rw [corePreimage_eq g hg, Subgroup.map_sup]
    have hR : R.map p = ⊥ := by
      apply le_bot_iff.mp
      rintro _ ⟨a, ha, rfl⟩
      exact (QuotientGroup.eq_one_iff a).mpr ha
    change R.map p ⊔ g.ker.map p = g.ker.map p
    rw [hR, bot_sup_eq]
  have hqc : q.ker ≤ center (D ⧸ R) := by
    rw [hker]
    rintro _ ⟨z, hz, rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective R y
    simpa only [map_mul] using congrArg p (mem_center_iff.mp (hk hz) y)
  have hqp : IsPGroup 2 q.ker := by rw [hker]; exact hp.map p
  obtain ⟨e₀⟩ := baseNormalizer_quotient_of_surjective baseNormalizer_action_surjective
  let e := e₀.trans Matrix.PSL3Two.equiv
  let f := e.toMonoidHom.comp q
  have hfker : f.ker = q.ker :=
    MonoidHom.ker_comp_of_injective q e.toMonoidHom e.injective
  have htriv : f.ker = ⊥ := by
    apply quotient_kernel_trivial f (e.surjective.comp hq) (by rwa [hfker]) (by rwa [hfker])
    obtain ⟨x, hx, hx2⟩ := hlift
    refine ⟨p x, ?_, by rw [← map_pow, hx2, map_one]⟩
    intro hx1
    have hq1 : q (p x) = 1 := e.injective (hx1.trans e.map_one.symm)
    have hmem : g x ∈ pCore 2 baseNormalizer := (QuotientGroup.eq_one_iff (g x)).mp hq1
    rw [hx] at hmem
    exact normalizerInvolution_not_mem_core hmem
  intro z hz
  have hpz : p z ∈ q.ker := hker ▸ mem_map.mpr ⟨z, hz, rfl⟩
  rw [← hfker, htriv, mem_bot] at hpz
  exact (QuotientGroup.eq_one_iff z).mp hpz

/-- The split-involution cover has no central kernel left after quotienting
by core displacements. Thus it suffices to bound the central module kernel. -/
theorem card_kernel_le_of_displacement_bound
    (g : D →* baseNormalizer) (hg : Function.Surjective g)
    (hk : g.ker ≤ center D) (hp : IsPGroup 2 g.ker)
    (hlift : ∃ x : D, g x = normalizerInvolution ∧ x ^ 2 = 1)
    (hbound : Nat.card (coreDisplacements g ⊓ g.ker : Subgroup D) ≤ 2) :
    Nat.card g.ker ≤ 2 := by
  rwa [inf_eq_right.mpr (kernel_le_coreDisplacements g hg hk hp hlift)] at hbound

/-- A finite perfect central two-cover of the literal HS normalizer has kernel
of order at most two if its two-core has a section and the specified noncore
involution lifts to an involution. This discharges the complete local-bound
premise of `not_four_dvd_of_core_section_of_local_bound`. -/
theorem card_kernel_le_two
    (g : D →* baseNormalizer) (hg : Function.Surjective g)
    (hk : g.ker ≤ center D) (hp : IsPGroup 2 g.ker)
    (hcore : ∃ s : pCore 2 baseNormalizer →* D,
      g.comp s = (pCore 2 baseNormalizer).subtype)
    (hlift : ∃ x : D, g x = normalizerInvolution ∧ x ^ 2 = 1) :
    Nat.card g.ker ≤ 2 := by
  obtain ⟨s, hs⟩ := hcore
  exact card_kernel_le_of_displacement_bound g hg hk hp hlift
    (card_coreDisplacements_inf_ker_le g hg hk s hs)

end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound

namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound
open Subgroup
open Sporadic.LeechRelated.HS BlockNormalizer

/-- Application to the literal HS restriction: only its central displacement
bound remains beyond the separately supplied core section. -/
theorem not_four_dvd_of_core_section_of_displacement_bound
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Carrier) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (hp : IsPGroup 2 f.ker)
    (hcore : ∃ s : pCore 2 baseNormalizer →* baseNormalizer.comap f,
      (f.subgroupComap baseNormalizer).comp s = (pCore 2 baseNormalizer).subtype)
    (hbound : Nat.card (coreDisplacements (f.subgroupComap baseNormalizer) ⊓
      (f.subgroupComap baseNormalizer).ker : Subgroup (baseNormalizer.comap f)) ≤ 2) :
    ¬ 4 ∣ Nat.card f.ker := by
  let g := f.subgroupComap baseNormalizer
  let : Group.IsPerfect (baseNormalizer.comap f) := restriction_isPerfect f hf hk hp
  have hg := f.subgroupComap_surjective_of_surjective baseNormalizer hf
  have hgp : IsPGroup 2 g.ker := hp.of_equiv (restrictionKernelEquiv f).symm
  obtain ⟨s, hs⟩ := hcore
  have hle := card_kernel_le_of_displacement_bound g hg (restriction_ker_le_center f hk)
    hgp (exists_involution_lift_of_e0_lift f hf (exists_e0_lift_of_core_section f s hs)) hbound
  have hc : Nat.card g.ker = Nat.card f.ker :=
    Nat.card_congr (restrictionKernelEquiv f).toEquiv
  rw [hc] at hle
  intro hfour
  have hge := Nat.le_of_dvd (Nat.card_pos (α := f.ker)) hfour
  omega

/-- On the literal HS restriction, the core section supplies the specified
involution lift through HS fusion. The local kernel bound has no remaining
premise; construction of the core section belongs to the HS assembly. -/
theorem not_four_dvd_of_core_section
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Carrier) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (hp : IsPGroup 2 f.ker)
    (hcore : ∃ s : pCore 2 baseNormalizer →* baseNormalizer.comap f,
      (f.subgroupComap baseNormalizer).comp s = (pCore 2 baseNormalizer).subtype) :
    ¬ 4 ∣ Nat.card f.ker := by
  apply not_four_dvd_of_core_section_of_local_bound f hf hk hp hcore
  intro D _ _ _ g hg hkg hpg hsection hlift
  exact card_kernel_le_two g hg hkg hpg hsection hlift

end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound
