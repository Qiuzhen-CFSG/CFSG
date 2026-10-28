module

public import Theory.GroupTheory.PerfectCentralCoverLocalBound
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary.PrimaryReduction

/-!
# Two-primary transfer through an odd local quotient

A central two-extension of an odd-order quotient is pulled back to the
original group. The projection of the pullback onto the extension is
surjective, hence maps its derived subgroup onto the original derived
subgroup. Raising to the odd kernel order puts a derived lift into the
other projection kernel; injectivity there forces the original two-element
to be trivial.

If this local derived-kernel vanishing holds on an odd-index subgroup,
central transfer excludes every two-group perfect kernel. The existing
Schur--Zassenhaus primary reduction then excludes two from an arbitrary
finite perfect central kernel, retaining the original map and all other
primary parts. No reduction to double covers is assumed.

The consumer in `TwoPrimary` uses the actual GU₂ map onto an odd-index
subgroup of PSU₃. The local GU₂ calculation and the matrix geometry remain
separate inputs. Source: the transfer argument underlying GLS3 §6.1 and
Aschbacher--Smith I.1.1--4, printed pp.407--408 (PDF pp.418--419).
-/

public section
open Subgroup
namespace PerfectCentralCovering
universe u v w

/-- Every finite central two-group extension of the given group has kernel
disjoint from its derived subgroup. This is a local input, not a multiplier
assertion for a projective unitary group. -/
@[expose] def TwoKernelDerivedTrivial (B : Type v) [Group B] : Prop :=
  ∀ {D : Type u} [Group D] [Finite D] (g : D →* B),
    Function.Surjective g → g.ker ≤ center D → IsPGroup 2 g.ker →
      g.ker ⊓ _root_.commutator D = ⊥

/-- Local derived-kernel vanishing descends through an actual surjection
whose kernel has odd order. No centrality of that odd kernel is needed. -/
theorem twoKernelDerivedTrivial_of_odd_surjection
    {B : Type v} {C : Type w} [Group B] [Finite B] [Group C]
    (j : B →* C) (hj : Function.Surjective j) (ho : Odd (Nat.card j.ker))
    (hlocal : TwoKernelDerivedTrivial.{max u v, v} B) :
    TwoKernelDerivedTrivial.{u, w} C := by
  intro E _ _ f hf hc hk
  let R : Subgroup (E × B) := {
    carrier := {x | f x.1 = j x.2}
    one_mem' := by simp
    mul_mem' := by
      intro x y hx hy
      change f (x.1 * y.1) = j (x.2 * y.2)
      rw [map_mul, map_mul, hx, hy]
    inv_mem' := by
      intro x hx
      change f x.1⁻¹ = j x.2⁻¹
      rw [map_inv, map_inv, hx] }
  let a : R →* E := (MonoidHom.fst E B).comp R.subtype
  let b : R →* B := (MonoidHom.snd E B).comp R.subtype
  have hab (x : R) : f (a x) = j (b x) := x.property
  have ha : Function.Surjective a := by
    intro x
    obtain ⟨y, hy⟩ := hj (f x)
    exact ⟨⟨(x, y), hy.symm⟩, rfl⟩
  have hb : Function.Surjective b := by
    intro y
    obtain ⟨x, hx⟩ := hf (j y)
    exact ⟨⟨(x, y), hx⟩, rfl⟩
  have hka {x : R} (hx : x ∈ b.ker) : a x ∈ f.ker := by
    rw [MonoidHom.mem_ker, hab, MonoidHom.mem_ker.mp hx, map_one]
  have hbc : b.ker ≤ center R := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Prod.ext
    · exact mem_center_iff.mp (hc (hka hx)) (a y)
    · change b y * b x = b x * b y
      rw [MonoidHom.mem_ker.mp hx, mul_one, one_mul]
  let k : b.ker →* f.ker := (a.comp b.ker.subtype).codRestrict f.ker
    (fun x => hka x.property)
  have hki : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val h
    · exact (MonoidHom.mem_ker.mp x.property).trans (MonoidHom.mem_ker.mp y.property).symm
  have hd := hlocal b hb hbc (hk.of_injective k hki)
  apply (f.ker ⊓ _root_.commutator E).eq_bot_iff_forall.mpr
  intro x hx
  have hmap : (_root_.commutator R).map a = _root_.commutator E := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr ha]
    rfl
  obtain ⟨y, hy, hyx⟩ := show x ∈ (_root_.commutator R).map a by rw [hmap]; exact hx.2
  have hyk : b y ∈ j.ker := by
    rw [MonoidHom.mem_ker, ← hab, hyx]
    exact hx.1
  have hypow : b (y ^ Nat.card j.ker) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨b y, hyk⟩ : j.ker)))
  have hyone : y ^ Nat.card j.ker = 1 := by
    apply mem_bot.mp
    rw [← hd]
    exact ⟨hypow, pow_mem hy _⟩
  have hxpow : (⟨x, hx.1⟩ : f.ker) ^ Nat.card j.ker = 1 := by
    apply Subtype.ext
    change x ^ Nat.card j.ker = 1
    rw [← hyx, ← map_pow, hyone, map_one]
  have he : (⟨x, hx.1⟩ : f.ker) = 1 := by
    apply (hk.powEquiv (Nat.coprime_two_left.mpr ho)).injective
    simpa only [IsPGroup.powEquiv_apply, one_pow] using hxpow
  exact congrArg Subtype.val he

/-- A local derived-kernel calculation at odd index excludes two from the
original arbitrary perfect central kernel. -/
theorem Cover.not_two_dvd_kernel_of_local_derived
    {E : Type u} {G : Type v} [Group E] [Finite E] [Group G]
    (f : Cover E G) (H : Subgroup G) (hindex : Odd H.index)
    (hlocal : TwoKernelDerivedTrivial.{u, v} H) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker := by
  apply Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary.not_two_dvd_kernel_of_twoGroup_case
    (G := G) (E := E) ?_ f
  intro D _ _ g hg
  let : Group.IsPerfect D := g.isPerfect
  let M := H.comap g.toMonoidHom
  let q : M →* H := g.toMonoidHom.subgroupComap H
  have hq : Function.Surjective q :=
    g.toMonoidHom.subgroupComap_surjective_of_surjective H g.surjective
  have hker {x : M} (hx : x ∈ q.ker) : (x : D) ∈ g.toMonoidHom.ker :=
    congrArg Subtype.val hx
  have hqc : q.ker ≤ center M := by
    intro x hx
    exact mem_center_iff.mpr fun y =>
      Subtype.ext (mem_center_iff.mp (g.ker_le_center (hker hx)) y)
  let k : q.ker →* g.toMonoidHom.ker :=
    (M.subtype.comp q.ker.subtype).codRestrict g.toMonoidHom.ker (fun x => hker x.property)
  have hki : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : g.toMonoidHom.ker => (z : D)) h
  have hdisj := hlocal q hq hqc (hg.of_injective k hki)
  have hKM : g.toMonoidHom.ker ≤ M := by
    intro x hx
    change g.toMonoidHom x ∈ H
    rw [MonoidHom.mem_ker.mp hx]
    exact H.one_mem
  have hder : g.toMonoidHom.ker ≤ ⁅M, M⁆ :=
    central_pSubgroup_le_commutator M g.toMonoidHom.ker hKM g.ker_le_center hg
      (by simpa only [M, Subgroup.index_comap_of_surjective _ g.surjective] using hindex.not_two_dvd_nat)
  have hbot : g.toMonoidHom.ker = ⊥ := by
    apply g.toMonoidHom.ker.eq_bot_iff_forall.mpr
    intro x hx
    have hxd := hder hx
    rw [← map_subtype_commutator] at hxd
    obtain ⟨y, hy, hyx⟩ := hxd
    change (y : D) = x at hyx
    have hyk : y ∈ q.ker := by
      apply Subtype.ext
      change g.toMonoidHom (y : D) = 1
      rw [hyx]
      exact hx
    have hyone : y = 1 := mem_bot.mp (hdisj ▸ (show y ∈ q.ker ⊓ _root_.commutator M from ⟨hyk, hy⟩))
    rw [← hyx, hyone]
    rfl
  rw [hbot, Subgroup.card_bot]
  decide

end PerfectCentralCovering
