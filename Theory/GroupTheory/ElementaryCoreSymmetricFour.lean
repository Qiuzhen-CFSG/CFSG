module

public import Theory.GroupTheory.CentralS3InvolutionComplement
public import Theory.GroupTheory.SelfCentralizingFourSymmetricFour
public import Theory.GroupTheory.ElementaryCentralFactorTransfer
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# An elementary local core gives S4 or C2 times S4

Let Q be a self-centralizing normal elementary two-subgroup of a finite
G. Suppose Q is the direct product of a normal subgroup U of order four
and the ambient center, whose order is at most two, and G/Q is S3.
If G contains an involution outside Q, then G is S4 or C2 times S4.
The outside-involution hypothesis must not be omitted: the weaker central
extension data do not alone guarantee a split extension.

Pass first to G/U. The image of the ambient center is the central kernel
of its surjection onto S3. The given involution survives outside that
kernel, so the central-extension complement theorem applies. Pulling its
complement back to G yields a subgroup L genuinely complementary to the
ambient center. Counting Q as U times the center gives |L|=24.
The elementary central-factor transfer makes U self-centralizing in L;
the four-Sylow-subgroup action theorem identifies L with S4. Finally,
multiplication identifies G with the center times L, and the center has
order one or two.

This isolates the terminal group identification in Stellmacher (8.2),
journal p.38, from its graph-theoretic hypotheses; see
`refs/latex/stellmacher-n-group.tex`. In the intended application U is
[Z_d,E_d], while the critical opposite elementary center supplies the
involution outside Q. All of those inputs remain explicit here.
-/

open scoped Pointwise IsMulCommutative

public theorem elementary_core_symmetric_four_or_c2_product
    {G : Type*} [Group G] [Finite G]
    (Q U : Subgroup G) [Q.Normal] [U.Normal] [IsElementaryAbelian 2 Q]
    (hcent : Subgroup.centralizer (Q : Set G) ≤ Q)
    (hQ : Q = U ⊔ Subgroup.center G)
    (hUZ : U ⊓ Subgroup.center G = ⊥)
    (hUcard : Nat.card U = 4) (hZcard : Nat.card (Subgroup.center G) ≤ 2)
    (hquot : Nonempty (G ⧸ Q ≃* Equiv.Perm (Fin 3)))
    (hout : ∃ t : G, t ∉ Q ∧ t ^ 2 = 1) :
    Nonempty (G ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (G ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) := by
  classical
  let Z := Subgroup.center G
  change Nat.card Z ≤ 2 at hZcard
  let π := QuotientGroup.mk' U
  let Zbar := Z.map π
  obtain ⟨e⟩ := hquot
  let f : G →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective Q)
  have hfker : f.ker = Q := by
    ext g
    change e (QuotientGroup.mk' Q g) = 1 ↔ g ∈ Q
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff g
  have hUQ : U ≤ Q := hQ.symm ▸ le_sup_left
  have hUker : U ≤ f.ker := hfker.symm ▸ hUQ
  let fbar := QuotientGroup.lift U f hUker
  have hfbar : Function.Surjective fbar := QuotientGroup.lift_surjective_of_surjective U f hf hUker
  have hfbarker : fbar.ker = Zbar := by
    dsimp only [fbar, Zbar, π]
    rw [QuotientGroup.ker_lift, hfker, hQ, Subgroup.map_sup, QuotientGroup.map_mk'_self,
      bot_sup_eq]
  have hZbarcent : Zbar ≤ Subgroup.center (G ⧸ U) := by
    rintro z ⟨z₀, hz₀, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro gbar
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective U gbar
    change π g * π z₀ = π z₀ * π g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz₀ g]
  have hZbarcard : Nat.card Zbar ≤ 2 :=
    (Nat.le_of_dvd (Nat.card_pos (α := Z)) (Z.card_map_dvd π)).trans hZcard
  let : Zbar.Normal := hfbarker ▸ fbar.normal_ker
  obtain ⟨t, htQ, ht2⟩ := hout
  have htbar : π t ∉ Zbar := by
    intro ht
    have htker : fbar (π t) = 1 := MonoidHom.mem_ker.mp (hfbarker.symm ▸ ht)
    have hft : f t = 1 := htker
    exact htQ (hfker ▸ MonoidHom.mem_ker.mpr hft)
  obtain ⟨B, hB⟩ := exists_complement_of_central_s3_quotient_involution
    Zbar hZbarcent hZbarcard fbar hfbar hfbarker (π t) htbar
    (by rw [← map_pow, ht2, map_one])
  let L := B.comap π
  have hUL : U ≤ L := by
    intro u hu
    change π u ∈ B
    have huπ : π u = 1 := (QuotientGroup.eq_one_iff u).mpr hu
    rw [huπ]
    exact B.one_mem
  have hZL : Disjoint Z L := by
    apply disjoint_iff_inf_le.mpr
    rintro x ⟨hxZ, hxL⟩
    have hxπ : π x = 1 := hB.disjoint.le_bot
      ⟨Subgroup.mem_map.mpr ⟨x, hxZ, rfl⟩, hxL⟩
    have hxU : x ∈ U := (QuotientGroup.eq_one_iff x).mp hxπ
    exact hUZ.le ⟨hxU, hxZ⟩
  have hZLcomp : Z.IsComplement' L := by
    refine ⟨Subgroup.mul_injective_of_disjoint hZL, ?_⟩
    intro g
    obtain ⟨⟨zbar, b⟩, hzb⟩ := hB.2 (π g)
    obtain ⟨z, hz, hzbar⟩ := zbar.property
    have hzπ : π z = zbar := hzbar
    have hl : z⁻¹ * g ∈ L := by
      change π (z⁻¹ * g) ∈ B
      rw [map_mul, map_inv, hzπ, ← hzb, inv_mul_cancel_left]
      exact b.property
    exact ⟨(⟨z, hz⟩, ⟨z⁻¹ * g, hl⟩), mul_inv_cancel_left z g⟩
  have hQcard : Nat.card Q = 4 * Nat.card Z := by
    let m : U × Z → Q := fun x => ⟨x.1 * x.2,
      hQ.symm ▸ (U ⊔ Z).mul_mem ((show U ≤ U ⊔ Z from le_sup_left) x.1.property)
        ((show Z ≤ U ⊔ Z from le_sup_right) x.2.property)⟩
    have hm : Function.Bijective m := by
      constructor
      · intro x y hxy
        exact Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hUZ)
          (congrArg Subtype.val hxy)
      · intro q
        have hq : (q : G) ∈ U ⊔ Z := hQ ▸ q.property
        obtain ⟨u, hu, z, hz, huz⟩ := Subgroup.mem_sup_of_normal_left.mp hq
        exact ⟨(⟨u, hu⟩, ⟨z, hz⟩), Subtype.ext huz⟩
    rw [← Nat.card_congr (Equiv.ofBijective m hm), Nat.card_prod, hUcard]
  have hGcard : Nat.card G = 24 * Nat.card Z := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Q, Nat.card_congr e.toEquiv, hQcard]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
    omega
  have hLcard : Nat.card L = 24 := by
    have hc := hZLcomp.card_mul_card
    rw [hGcard] at hc
    have hzpos : 0 < Nat.card Z := Nat.card_pos
    nlinarith
  have htransfer : IsElementaryAbelian 2 (U.subgroupOf L) ∧
      Subgroup.centralizer (U.subgroupOf L : Set L) ≤ U.subgroupOf L := by
    exact elementary_central_factor_selfCentralizing_subgroupOf Q U L hQ hcent hUL hZL.symm
  let : IsElementaryAbelian 2 (U.subgroupOf L) := htransfer.1
  have hULcard : Nat.card (U.subgroupOf L) = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUL).toEquiv).trans hUcard
  obtain ⟨eL⟩ := mulEquiv_perm_four_of_selfCentralizing_four_card_twentyfour
    (U.subgroupOf L) hULcard htransfer.2 hLcard
  have hpoint (z : Z) (l : L) : Commute (Z.subtype z) (L.subtype l) :=
    (Subgroup.mem_center_iff.mp z.property l).symm
  let m : Z × L →* G := Z.subtype.noncommCoprod L.subtype hpoint
  have hm : Function.Bijective m := hZLcomp
  let eG : G ≃* Z × L := (MulEquiv.ofBijective m hm).symm
  have hzpos : 0 < Nat.card Z := Nat.card_pos
  rcases (show Nat.card Z = 1 ∨ Nat.card Z = 2 by omega) with hz | hz
  · left
    have hZbot : Z = ⊥ := Subgroup.card_eq_one.mp hz
    have hLtop : L = ⊤ := by simpa [hZbot] using hZLcomp.sup_eq_top
    exact ⟨((MulEquiv.subgroupCongr hLtop).trans Subgroup.topEquiv).symm.trans eL⟩
  · right
    let eZ : Z ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hz (by
      simp [Nat.card_eq_fintype_card])
    exact ⟨eG.trans (MulEquiv.prodCongr eZ eL)⟩
