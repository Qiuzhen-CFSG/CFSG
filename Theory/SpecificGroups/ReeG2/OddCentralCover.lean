module

public import Theory.SpecificGroups.ReeG2.InvolutionProjectiveProduct
public import Theory.GroupTheory.OddCentralInvolutionLifting.Centralizers
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.CoveringKernelCard
public import GorensteinWalter.PSL2SchurMultiplier

/-!
# Large Ree groups in odd central extensions

The actual Ree torus involution lifts uniquely through an odd central
kernel. The derived preimage of its marked PSL₂ subgroup is perfect.
The proved universal SL₂ cover forces this derived preimage's kernel to
divide two; its oddness makes the kernel trivial. The resulting PSL₂
embedding centralizes the lifted involution and retains the original
projection triangle. Its defining rank is 2m+1.

The final source application takes the literal map G → G/Z(G) → Ree(F,m).
It contradicts quasithinness of G for m≥1 without any assertion that
quasithinness descends to arbitrary central quotients, and without a Ree
multiplier calculation. The m=0 derived exception remains separate.

Source: Aschbacher–Smith A.2.13 and A.2.17, printed pp.37–39;
the PSL₂ finite universal-cover input is I.1.3–I.1.4, printed pp.407–408.
The concrete Ree matrices are the attributed ATLAS construction imported
by InvolutionProjectiveProduct; see LICENSES/ATLAS.txt.
-/

public section

open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups

namespace Atlas.ReeG2.OddCentralCover

universe u v

private theorem exists_psl2_section
    {F : Type u} [Field F] [Finite F] [Fact (3 < Nat.card F)]
    (hodd : Odd (Nat.card F)) (h9 : Nat.card F ≠ 9)
    {E : Type v} [Group E] [Finite E]
    (f : E →* PSL(2, F)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (ho : Odd (Nat.card f.ker)) :
    ∃ s : PSL(2, F) →* E, f.comp s = MonoidHom.id _ := by
  let D := commutator E
  let g : D →* PSL(2, F) := f.comp D.subtype
  have hD : D.map f = ⊤ := by
    change (commutator E).map f = ⊤
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    exact Group.IsPerfect.commutator_eq_top
  have hg : Function.Surjective g := by
    intro b
    have hb : b ∈ D.map f := by rw [hD]; trivial
    obtain ⟨d, hd, hdb⟩ := hb
    exact ⟨⟨d, hd⟩, hdb⟩
  let : Group.IsPerfect D :=
    commutator_isPerfect_of_surjective_of_ker_le_center f hf hc
  have hgc : g.ker ≤ center D := by
    intro d hd
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_center_iff.mp (hc hd) x)
  let k : g.ker →* f.ker :=
    (D.subtype.comp g.ker.subtype).codRestrict f.ker (fun x => x.property)
  have hki : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.ker => (z : E)) h
  have hgo : Odd (Nat.card g.ker) :=
    Odd.of_dvd_nat ho (Subgroup.card_dvd_of_injective k hki)
  let c : Cover D PSL(2, F) := {
    toMonoidHom := g
    surjective := hg
    isPerfect := inferInstance
    ker_le_center := hgc }
  let : IsQuasisimple D := c.isQuasisimple
  let d : Covering D PSL(2, F) := c.toCovering
  have hu : Covering.IsUniversal.{u, u, v} (GorensteinWalter.PSL2Cover.cover F) :=
    GorensteinWalter.PSL2Cover.isUniversal_of_odd F hodd h9
  have hfac : g.comp (hu.lift d).toMonoidHom =
      (GorensteinWalter.PSL2Cover.cover F).toMonoidHom :=
    congrArg Covering.toMonoidHom (hu.lift_fac d)
  have hdvd : Nat.card g.ker ∣ 2 := by
    have h := kernel_card_dvd_of_surjective_factor
      (GorensteinWalter.PSL2Cover.cover F).toMonoidHom g
      (hu.lift d).toMonoidHom (hu.lift d).surjective hfac
    have htwo : Nat.card (GorensteinWalter.PSL2Cover.cover F).toMonoidHom.ker = 2 :=
      GorensteinWalter.sl2ProjectiveProjection_ker_card F hodd
    simpa only [htwo] using h
  have hgker : g.ker = ⊥ := Subgroup.card_eq_one.mp
    (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_right.mpr hgo) dvd_rfl hdvd)
  let e : D ≃* PSL(2, F) :=
    MulEquiv.ofBijective g ⟨g.ker_eq_bot_iff.mp hgker, hg⟩
  refine ⟨D.subtype.comp e.symm.toMonoidHom, ?_⟩
  ext b
  exact e.apply_symm_apply b

variable {F : Type u} [Field F] [Finite F] [CharP F 3]
    {E : Type v} [Group E] [Finite E]

/-- The marked PSL₂ factor lifts into the centralizer of the actual lifted
Ree torus involution, with its original projection triangle. -/
theorem exists_marked_psl2_lift
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card F = 3 ^ (2 * m + 1))
    (f : E →* Model F m) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (ho : Odd (Nat.card f.ker)) :
    ∃ (t : E) (s : PSL(2, F) →* E),
      t ≠ 1 ∧ t ^ 2 = 1 ∧ f t = torusInvolution m ∧
      Function.Injective s ∧ f.comp s = InvolutionProduct.projectiveHom m ∧
      ∀ x, Commute t (s x) := by
  have hlarge : 9 < Nat.card F := by
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 3) (by omega : 3 ≤ 2 * m + 1)
    rw [hcard]
    norm_num at hpow ⊢
    omega
  let : Fact (3 < Nat.card F) := ⟨by omega⟩
  have hFodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (by decide : Odd 3).pow
  let i : PSL(2, F) →* Model F m := InvolutionProduct.projectiveHom m
  have hi : Function.Injective i := InvolutionProduct.projectiveHom_injective m
  let H : Subgroup E := i.range.comap f
  let e : PSL(2, F) ≃* i.range := MonoidHom.ofInjective hi
  let g : H →* PSL(2, F) := e.symm.toMonoidHom.comp (f.subgroupComap i.range)
  have hg : Function.Surjective g :=
    e.symm.surjective.comp (f.subgroupComap_surjective_of_surjective i.range hf)
  have hfg (x : H) : f (x : E) = i (g x) := by
    exact (MonoidHom.apply_ofInjective_symm hi (f.subgroupComap i.range x)).symm
  have hker (x : H) (hx : x ∈ g.ker) : (x : E) ∈ f.ker := by
    change f (x : E) = 1
    rw [hfg, show g x = 1 from hx, map_one]
  have hgc : g.ker ≤ center H := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (hc (hker x hx)) (y : E))
  let k : g.ker →* f.ker :=
    (H.subtype.comp g.ker.subtype).codRestrict f.ker (fun x => hker x x.property)
  have hki : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.ker => (z : E)) h
  have hgo : Odd (Nat.card g.ker) :=
    Odd.of_dvd_nat ho (Subgroup.card_dvd_of_injective k hki)
  obtain ⟨sH, hsH⟩ := exists_psl2_section hFodd (by omega) g hg hgc hgo
  have hsHinj : Function.Injective sH := by
    intro x y h
    calc
      x = g (sH x) := (DFunLike.congr_fun hsH x).symm
      _ = g (sH y) := congrArg g h
      _ = y := DFunLike.congr_fun hsH y
  let s : PSL(2, F) →* E := H.subtype.comp sH
  have hs : f.comp s = i := by
    apply MonoidHom.ext
    intro x
    change f (sH x : E) = i x
    rw [hfg]
    exact congrArg i (DFunLike.congr_fun hsH x)
  obtain ⟨t, htf, ht2⟩ := OddCentralLifting.exists_involution_lift
    f ho hf (torusInvolution m) (torusInvolution_sq m)
  have ht : t ≠ 1 := by
    intro h
    apply torusInvolution_ne_one (F := F) m
    rw [← htf, h, map_one]
  refine ⟨t, s, ht, ht2, htf, H.subtype_injective.comp hsHinj, hs, ?_⟩
  intro x
  apply Commute.symm
  apply OddCentralLifting.centralizes_of_image f ho hc ht2
  rw [htf, show f (s x) = i x from DFunLike.congr_fun hs x]
  exact (InvolutionProduct.projectiveHom_commute m x).eq.symm

/-- The local rank witness remains in the original covering group and
its involution has the prescribed image h(−1) in the Ree model. -/
theorem exists_marked_involution_primeRank_ge
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card F = 3 ^ (2 * m + 1))
    (f : E →* Model F m) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (ho : Odd (Nat.card f.ker)) :
    ∃ t : E, t ≠ 1 ∧ t ^ 2 = 1 ∧ f t = torusInvolution m ∧
      2 * m + 1 ≤ primeRank 3 (centralizer ({t} : Set E)) := by
  obtain ⟨t, s, ht, ht2, htf, hsi, _hs, hcomm⟩ :=
    exists_marked_psl2_lift m hm hcard f hf hc ho
  refine ⟨t, ht, ht2, htf, ?_⟩
  let j : PSL(2, F) →* centralizer ({t} : Set E) :=
    s.codRestrict _ (fun x => mem_centralizer_singleton_iff.mpr (hcomm x).eq.symm)
  apply Matrix.SpecialLinearGroup.fieldExponent_le_primeRank_of_projective_injective hcard j
  intro x y h
  exact hsi (congrArg Subtype.val h)

end Atlas.ReeG2.OddCentralCover
