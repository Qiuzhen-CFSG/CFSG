module

public import Theory.Frattini.PGroup
public import Theory.GroupTheory.Commutator.CentralSylowTransfer
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect central covers

This module records finite perfect central extensions and the transfer argument
that controls their kernels. The universal-cover existence construction belongs
in a separate extension of this interface.

The kernel calculation is the finite-group input in Aschbacher--Smith I.1.2:
over a group with cyclic Sylow `p`-subgroups, a finite perfect central
extension has kernel of order prime to `p`.

The transfer/Frattini proofs are adapted from the general central-extension
lemmas in `Theory.Alternating.theorem_5_2_1_2`, here with only group-theory
dependencies. No quasisimplicity assumption is used.
-/

namespace PerfectCentralCovering

public section

open scoped IsMulCommutative

/-- A surjective homomorphism from a perfect group with central kernel. -/
structure Cover (L G : Type*) [Group L] [Group G] extends L →* G where
  surjective : Function.Surjective toMonoidHom
  isPerfect : Group.IsPerfect L
  ker_le_center : toMonoidHom.ker ≤ Subgroup.center L

attribute [coe] Cover.toMonoidHom

variable {L G M : Type*} [Group L] [Group G] [Group M]

/-- The kernel of a perfect central cover, called the multiplier when the cover
is universal. -/
abbrev multiplier (f : Cover L G) : Subgroup L := f.toMonoidHom.ker

/-- A finite perfect central cover lifts uniquely through every finite perfect
central cover with the same base. -/
@[expose] def IsUniversal [Finite G] (f : Cover L G) : Prop :=
  ∀ (M : Type*) [Group M] [Finite M] (g : Cover M G),
    ∃! h : L →* M, g.toMonoidHom.comp h = f.toMonoidHom

/-- The displayed triangle for a morphism of covers commutes. -/
@[expose] def Compatible (f : Cover L G) (g : Cover M G) (h : L →* M) : Prop :=
  g.toMonoidHom.comp h = f.toMonoidHom

theorem compatible_iff {f : Cover L G} {g : Cover M G} {h : L →* M} :
    Compatible f g h ↔ g.toMonoidHom.comp h = f.toMonoidHom := Iff.rfl

universe u v

/-- Universal perfect central covers of the same base are uniquely isomorphic
by an isomorphism commuting with the projection. -/
theorem IsUniversal.existsUnique_mulEquiv
    {L M : Type u} {G : Type v} [Group L] [Group M] [Group G]
    [Finite L] [Finite M] [Finite G]
    (f : Cover L G) (g : Cover M G)
    (hf : IsUniversal.{u, v, u} f) (hg : IsUniversal.{u, v, u} g) :
    ∃! e : L ≃* M, g.toMonoidHom.comp e.toMonoidHom = f.toMonoidHom := by
  obtain ⟨h, hh, huniq⟩ := hf M g
  obtain ⟨k, hk, _⟩ := hg L f
  have hkh : k.comp h = MonoidHom.id L := by
    apply (hf L f).unique
    · rw [← MonoidHom.comp_assoc, hk, hh]
    · exact MonoidHom.comp_id _
  have hhk : h.comp k = MonoidHom.id M := by
    apply (hg M g).unique
    · rw [← MonoidHom.comp_assoc, hh, hk]
    · exact MonoidHom.comp_id _
  let e : L ≃* M :=
    { h with
      invFun := k
      left_inv := fun x => DFunLike.congr_fun hkh x
      right_inv := fun x => DFunLike.congr_fun hhk x }
  refine ⟨e, hh, ?_⟩
  intro e' he'
  apply MulEquiv.toMonoidHom_injective
  exact huniq e'.toMonoidHom he'

/-- The central part of a Sylow subgroup of a finite perfect group lies in its
Frattini subgroup. -/
theorem central_subgroup_le_frattini_sylow
    {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime] (P : Sylow p H)
    (X : Subgroup P)
    (hXcentral : X.map (P : Subgroup H).subtype ≤ Subgroup.center H) :
    X ≤ frattini P := by
  let C := commutator P
  let qC := QuotientGroup.mk' C
  let : IsMulCommutative (P ⧸ C) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (by
      dsimp [C]
      exact le_rfl)
  let tau : H →* P ⧸ C := MonoidHom.transfer qC
  have htau_one (g : H) : tau g = 1 := by
    apply MonoidHom.mem_ker.mp
    exact Abelianization.commutator_subset_ker tau
      (Group.IsPerfect.mem_commutator (g := g))
  have hcomm_frattini : C ≤ frattini P := by
    dsimp [C]
    let : Fact (IsPGroup p P) := ⟨P.isPGroup'⟩
    exact commutator_le_frattini_of_isPGroup (p := p)
  intro x hx
  let xH : H := (P : Subgroup H).subtype x
  have hxcenter : xH ∈ Subgroup.center H :=
    hXcentral (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hkey : ∀ (k : Nat) (g0 : H),
      g0⁻¹ * xH ^ k * g0 ∈ (P : Subgroup H) →
        g0⁻¹ * xH ^ k * g0 = xH ^ k := by
    intro k g0 _
    have hxpow : xH ^ k ∈ Subgroup.center H :=
      (Subgroup.center H).pow_mem hxcenter k
    have hc := Subgroup.mem_center_iff.mp hxpow g0
    rw [mul_assoc, hc.symm]
    simp
  have hqCpow : qC (x ^ P.index) = 1 := by
    have hformula := MonoidHom.transfer_eq_pow qC xH hkey
    have harg :
        (⟨xH ^ P.index,
            MonoidHom.transfer_eq_pow_aux xH hkey⟩ : P) = x ^ P.index := by
      apply Subtype.ext
      rfl
    rw [harg] at hformula
    exact hformula.symm.trans (htau_one xH)
  have hxpowC : x ^ P.index ∈ C := by
    exact (QuotientGroup.eq_one_iff (x ^ P.index)).mp hqCpow
  have hxpowF : x ^ P.index ∈ frattini P := hcomm_frattini hxpowC
  let qF := QuotientGroup.mk' (frattini P)
  let hPF : IsPGroup p (P ⧸ frattini P) :=
    P.isPGroup'.to_quotient (frattini P)
  have hqFpow : qF x ^ P.index = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (x ^ P.index)).mpr hxpowF
  have hqFx : qF x = 1 := by
    apply (hPF.powEquiv' P.not_dvd_index).injective
    simpa using hqFpow
  exact (QuotientGroup.eq_one_iff x).mp hqFx

/-- The part of a central kernel lying in a Sylow subgroup belongs to that
Sylow subgroup's Frattini subgroup. -/
theorem ker_comap_le_frattini_sylow
    {H K : Type*} [Group H] [Finite H] [Group.IsPerfect H] [Group K]
    {p : Nat} [Fact p.Prime] (P : Sylow p H) (f : H →* K)
    (hker : f.ker ≤ Subgroup.center H) :
    f.ker.comap (P : Subgroup H).subtype ≤ frattini P := by
  apply central_subgroup_le_frattini_sylow P
  rintro x ⟨y, hy, rfl⟩
  exact hker hy

/-- A cyclic Sylow subgroup downstairs lifts to a cyclic Sylow subgroup in a
finite perfect central extension. -/
theorem isCyclic_sylow_of_isCyclic_mapSurjective
    {H K : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    [Group K] [Finite K]
    {p : Nat} [Fact p.Prime]
    (P : Sylow p H) (f : H →* K) (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hcyclic : IsCyclic (P.mapSurjective hsurj)) :
    IsCyclic P := by
  let Q : Sylow p K := P.mapSurjective hsurj
  let : IsCyclic Q := hcyclic
  obtain ⟨q, hqgen⟩ := IsCyclic.exists_generator (α := Q)
  have hqmap : (q : K) ∈ (P : Subgroup H).map f := by
    change (q : K) ∈ (Q : Subgroup K)
    exact q.2
  obtain ⟨xH, hxP, hfx⟩ := Subgroup.mem_map.mp hqmap
  let x : P := ⟨xH, hxP⟩
  have hfxq : f x = q := hfx
  let Kx : Subgroup P := Subgroup.zpowers x
  have hKx_sup : Kx ⊔ frattini P = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hyQ : f y ∈ (Q : Subgroup K) := by
      change f (y : H) ∈ (P : Subgroup H).map f
      exact Subgroup.mem_map.mpr ⟨y, y.2, rfl⟩
    let yQ : Q := ⟨f y, hyQ⟩
    obtain ⟨n, hn⟩ := hqgen yQ
    have hfy : f (y * x ^ (-n)) = 1 := by
      rw [map_mul, map_zpow, hfxq]
      change (yQ : K) * (q : K) ^ (-n) = 1
      rw [← hn]
      simp
    have hdiff : y * x ^ (-n) ∈ frattini P := by
      apply ker_comap_le_frattini_sylow P f hker
      exact hfy
    have hxpow : x ^ n ∈ Kx := ⟨n, rfl⟩
    have hdecomp : y = (y * x ^ (-n)) * x ^ n := by simp
    rw [hdecomp]
    exact (Kx ⊔ frattini P).mul_mem
      (show y * x ^ (-n) ∈ Kx ⊔ frattini P from
        (le_sup_right : frattini P ≤ Kx ⊔ frattini P) hdiff)
      (show x ^ n ∈ Kx ⊔ frattini P from
        (le_sup_left : Kx ≤ Kx ⊔ frattini P) hxpow)
  have hKx_top : Kx = ⊤ := frattini_nongenerating hKx_sup
  exact ⟨x, fun y => by
    show y ∈ Kx
    rw [hKx_top]
    exact Subgroup.mem_top y⟩

/-- A central subgroup contained in a cyclic Sylow subgroup of a finite
perfect group is trivial. -/
theorem central_subgroup_eq_bot_of_isCyclic_sylow
    {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime]
    (P : Sylow p H) (hPcyclic : IsCyclic P)
    (X : Subgroup P)
    (hXcentral : X.map (P : Subgroup H).subtype ≤ Subgroup.center H) :
    X = ⊥ := by
  let : IsCyclic P := hPcyclic
  let tau : H →* P := MonoidHom.transfer (MonoidHom.id P)
  have htau_one (g : H) : tau g = 1 := by
    apply MonoidHom.mem_ker.mp
    exact Abelianization.commutator_subset_ker tau
      (Group.IsPerfect.mem_commutator (g := g))
  apply le_antisymm
  · intro x hx
    let xH : H := (P : Subgroup H).subtype x
    have hxcenter : xH ∈ Subgroup.center H :=
      hXcentral (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    have hkey : ∀ (k : Nat) (g0 : H),
        g0⁻¹ * xH ^ k * g0 ∈ (P : Subgroup H) →
          g0⁻¹ * xH ^ k * g0 = xH ^ k := by
      intro k g0 _
      have hxpow : xH ^ k ∈ Subgroup.center H :=
        (Subgroup.center H).pow_mem hxcenter k
      have hc := Subgroup.mem_center_iff.mp hxpow g0
      rw [mul_assoc, hc.symm]
      simp
    have hxpow : x ^ P.index = 1 := by
      have hformula := MonoidHom.transfer_eq_pow (MonoidHom.id P) xH hkey
      have harg :
          (⟨xH ^ P.index,
              MonoidHom.transfer_eq_pow_aux xH hkey⟩ : P) = x ^ P.index := by
        apply Subtype.ext
        rfl
      rw [harg] at hformula
      exact hformula.symm.trans (htau_one xH)
    have hxone : x = 1 := by
      apply (P.isPGroup'.powEquiv' P.not_dvd_index).injective
      simpa using hxpow
    exact Subgroup.mem_bot.mpr hxone
  · exact bot_le

/-- If all Sylow `p`-subgroups of the quotient are cyclic, then `p` does not
divide the kernel of any finite perfect central extension. -/
theorem not_dvd_card_kernel_of_isCyclic_sylow
    {H K : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    [Group K] [Finite K]
    {p : Nat} [Fact p.Prime]
    (f : H →* K) (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hcyclic : ∀ Q : Sylow p K, IsCyclic Q) :
    ¬ p ∣ Nat.card f.ker := by
  intro hpker
  obtain ⟨z, hzorder⟩ := exists_prime_orderOf_dvd_card' p hpker
  have hzorderH : orderOf (z : H) = p :=
    (Subgroup.orderOf_coe z).trans hzorder
  let Z : Subgroup H := Subgroup.zpowers (z : H)
  have hZcard : Nat.card Z = p := by
    dsimp [Z]
    rw [Nat.card_zpowers, hzorderH]
  have hZp : IsPGroup p Z := by
    apply IsPGroup.of_card (n := 1)
    simpa using hZcard
  obtain ⟨P, hZP⟩ := hZp.exists_le_sylow
  have hPcyclic : IsCyclic P :=
    isCyclic_sylow_of_isCyclic_mapSurjective
      P f hsurj hker (hcyclic (P.mapSurjective hsurj))
  let X : Subgroup P := f.ker.comap (P : Subgroup H).subtype
  have hXcentral : X.map (P : Subgroup H).subtype ≤ Subgroup.center H := by
    rintro x ⟨y, hy, rfl⟩
    exact hker hy
  have hXbot : X = ⊥ :=
    central_subgroup_eq_bot_of_isCyclic_sylow P hPcyclic X hXcentral
  have hzZ : (z : H) ∈ Z := Subgroup.mem_zpowers (z : H)
  let zP : P := ⟨z, hZP hzZ⟩
  have hzX : zP ∈ X := z.2
  rw [hXbot] at hzX
  have hzPone : zP = 1 := Subgroup.mem_bot.mp hzX
  have hzHone : (z : H) = 1 := congrArg Subtype.val hzPone
  have hzorderOne : orderOf (z : H) = 1 := orderOf_eq_one_iff.mpr hzHone
  exact (Fact.out : Nat.Prime p).ne_one (hzorderH.symm.trans hzorderOne)

theorem Cover.not_dvd_card_multiplier_of_isCyclic_sylow
    {H K : Type*} [Group H] [Finite H] [Group K] [Finite K]
    {p : Nat} [Fact p.Prime] (f : Cover H K)
    (hcyclic : ∀ Q : Sylow p K, IsCyclic Q) :
    ¬ p ∣ Nat.card (multiplier f) := by
  let := f.isPerfect
  exact not_dvd_card_kernel_of_isCyclic_sylow
    f.toMonoidHom f.surjective f.ker_le_center hcyclic

end

end PerfectCentralCovering
