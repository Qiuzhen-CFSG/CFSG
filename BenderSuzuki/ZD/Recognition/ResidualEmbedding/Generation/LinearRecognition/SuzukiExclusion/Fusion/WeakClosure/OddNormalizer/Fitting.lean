module

public import Theory.GroupTheory.Fitting.Core
public import Theory.GroupTheory.SolvableMinimalNormal
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.ActionContract
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.ActionConsequences
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.FrobeniusExclusion
public import FeitThompson.FinalTheorem

/-!
# The Fitting argument for the odd Suzuki quotient normalizer

Let H = N_M(S)/S, F = F(H), and K be the actual torus image. If F ∩ K
were trivial, the element-centralizer bound and C_H(K) = K would make
C_F(k) trivial for every nonidentity k in K. The Odd Order Theorem makes
H solvable, so F is nontrivial. An abelian minimal normal prime-power
subgroup of F then supplies exactly the excluded Frobenius kernel.

For the nontrivial intersection, normality of F and Z(F), together with
the same centralizer bounds, gives Z(F) ∩ K ≠ 1. A nonidentity element
there has fixed subgroup U-bar of order two. Every element of F preserves
this subgroup and therefore fixes it pointwise. Hence U-bar = C_S-bar(F),
and normality of F proves invariance under H. This justifies the source's
fixed-subgroup step without assuming normality of an intersection.

The final applications use the literal quotient normalizer and Burnside
fusion interfaces. Construction of ActionData belongs to the parent assembly.
Source: GLS4, Chapter 2, Lemma 14.9, `refs/KGroup/GLS4/Chapter2.tex`,
lines 2600–2620.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace BenderSuzuki.ZD.SuzukiExclusion.OddNormalizer.Fitting
variable {H : Type*} [Group H]

private theorem centralizer_inf_eq_bot (F K : Subgroup H) [F.Normal]
    (hdis : F ⊓ K = ⊥) (hK : centralizer (K : Set H) = K)
    {x : H} (hc : centralizer ({x} : Set H) ≤ normalizer (K : Set H)) :
    F ⊓ centralizer ({x} : Set H) = ⊥ := by
  let C := F ⊓ centralizer ({x} : Set H)
  have hcomm : ⁅C, K⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← hdis]
    exact le_inf ((commutator_mono inf_le_left le_rfl).trans (commutator_le_left F K))
      (le_normalizer_iff_commutator_le_right.mp (inf_le_right.trans hc))
  have hCK : C ≤ K := by
    rw [← hK]
    exact commutator_eq_bot_iff_le_centralizer.mp hcomm
  exact le_bot_iff.mp (le_inf inf_le_left hCK |>.trans hdis.le)

private theorem center_inf_ne_bot (F K : Subgroup H) [F.Normal] [Group.IsNilpotent F]
    (hne : F ⊓ K ≠ ⊥)
    (hc : ∀ x ∈ K, x ≠ 1 → centralizer ({x} : Set H) ≤ normalizer (K : Set H))
    (hK : centralizer (K : Set H) = K) :
    (center F).map F.subtype ⊓ K ≠ ⊥ := by
  obtain ⟨x, hx, hx1⟩ := (F ⊓ K).bot_or_exists_ne_one.resolve_left hne
  have hFne : F ≠ ⊥ := fun he => hx1 (show x = 1 from mem_bot.mp (he ▸ hx.1))
  let : Nontrivial F := (nontrivial_iff_ne_bot F).mpr hFne
  let A := (center F).map F.subtype
  have hAne : A ≠ ⊥ := fun he => Group.IsNilpotent.center_ne_bot F
    (((center F).map_eq_bot_iff_of_injective F.subtype_injective).mp he)
  have hAnorm : A ≤ normalizer (K : Set H) := by
    apply le_trans ?_ (hc x hx.2 hx1)
    rintro _ ⟨c, hc, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val ((mem_center_iff.mp hc) ⟨x, hx.1⟩)).symm
  intro he
  have hcomm : ⁅A, K⁆ = ⊥ := le_bot_iff.mp
    ((le_inf (commutator_le_left A K)
      (le_normalizer_iff_commutator_le_right.mp hAnorm)).trans he.le)
  have hAK : A ≤ K := hK ▸ commutator_eq_bot_iff_le_centralizer.mp hcomm
  exact hAne (le_bot_iff.mp ((le_inf le_rfl hAK).trans he.le))

variable {V : Type*} [Group V]

private theorem fixes_of_preserves_two (U : Subgroup V) (hU : Nat.card U = 2)
    (b : MulAut V) (hb : ∀ v ∈ U, b v ∈ U) {v : V} (hv : v ∈ U) : b v = v := by
  obtain ⟨u, _, hu⟩ := (Nat.card_eq_two_iff' (1 : U)).mp hU
  by_cases hv1 : v = 1
  · simp [hv1]
  have hb1 : b v ≠ 1 := fun he => hv1 (b.injective (he.trans b.map_one.symm))
  exact congrArg Subtype.val ((hu ⟨b v, hb v hv⟩ (fun he => hb1 (congrArg Subtype.val he))).trans
    (hu ⟨v, hv⟩ (fun he => hv1 (congrArg Subtype.val he))).symm)

private theorem preserves_of_fitting_intersection (F K : Subgroup H)
    [F.Normal] [Group.IsNilpotent F]
    (hne : F ⊓ K ≠ ⊥)
    (hc : ∀ x ∈ K, x ≠ 1 → centralizer ({x} : Set H) ≤ normalizer (K : Set H))
    (hK : centralizer (K : Set H) = K)
    (a : H →* MulAut V) (U : Subgroup V) (hU : Nat.card U = 2)
    (hfix : ∀ k ∈ K, k ≠ 1 → ∀ v : V, a k v = v ↔ v ∈ U) :
    ∀ n : H, ∀ v ∈ U, a n v ∈ U := by
  obtain ⟨z, hz, hz1⟩ := ((center F).map F.subtype ⊓ K).bot_or_exists_ne_one.resolve_left
    (center_inf_ne_bot F K hne hc hK)
  obtain ⟨zF, hzF, rfl⟩ := hz.1
  have hFfix : ∀ f ∈ F, ∀ v ∈ U, a f v = v := by
    intro f hf v hv
    apply fixes_of_preserves_two U hU (a f) ?_ hv
    intro w hw
    apply (hfix zF hz.2 hz1 (a f w)).mp
    have hcomm : (zF : H) * f = f * zF :=
      (congrArg Subtype.val ((mem_center_iff.mp hzF) ⟨f, hf⟩)).symm
    calc
      a zF (a f w) = a ((zF : H) * f) w := by rw [map_mul]; rfl
      _ = a (f * zF) w := by rw [hcomm]
      _ = a f (a zF w) := by rw [map_mul]; rfl
      _ = a f w := by rw [(hfix zF hz.2 hz1 w).mpr hw]
  intro n v hv
  apply (hfix zF hz.2 hz1 (a n v)).mp
  have hconj : n⁻¹ * (zF : H) * n ∈ F := by
    simpa only [inv_inv] using (inferInstance : F.Normal).conj_mem zF zF.property n⁻¹
  calc
    a zF (a n v) = a ((zF : H) * n) v := by rw [map_mul]; rfl
    _ = a (n * (n⁻¹ * (zF : H) * n)) v := by congr 2; group
    _ = a n (a (n⁻¹ * (zF : H) * n) v) := by rw [map_mul]; rfl
    _ = a n v := by rw [hFfix _ hconj v hv]

end BenderSuzuki.ZD.SuzukiExclusion.OddNormalizer.Fitting

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion.OddNormalizer
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- The trivial Fitting–torus intersection would give the excluded abelian
odd-prime-power Frobenius kernel in the literal normalizer quotient. -/
public theorem ActionData.fitting_torus_intersection_ne_bot
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (hU : Nat.card g.U = 2) (he : ElementaryQuotient d g)
    (hD8 : m = 1 → Nat.card (residualPairStabilizer M t) ∣ 294)
    (a : ActionData d g) :
    fittingSubgroup (quotient g) ⊓ torusImage g ≠ ⊥ := by
  let H := quotient g
  let F := fittingSubgroup H
  let K := torusImage g
  let : Group.IsSolvable H := odd_order_theorem H a.odd
  have hKcard : 1 < Nat.card K := by
    rw [a.torus_card]
    have hp : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by decide) (by
      have := d.parameter_pos
      omega)
    norm_num at hp
    omega
  have hFne : F ≠ ⊥ := by
    intro hF
    have hHcard := (fitting_eq_bot_iff_card_eq_one_of_solvable H).mp hF
    have hle := K.card_le_card_group
    rw [hHcard] at hle
    omega
  intro hdis
  obtain ⟨R, p, hRn, hRne, hRF, hp, hRcomm, hRp, _⟩ :=
    exists_minimal_normal_abelian_pGroup F hFne
  let : R.Normal := hRn
  let : IsMulCommutative R := hRcomm
  let : Fact p.Prime := ⟨hp⟩
  let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hRne
  have hp2 : p ≠ 2 := by
    intro htwo
    obtain ⟨r, hr⟩ := exists_ne (1 : R)
    have hd : p ∣ Nat.card R := (hRp.dvd_orderOf hr).trans (orderOf_dvd_natCard r)
    have hodd : Odd (Nat.card R) := a.odd.of_dvd_nat R.card_subgroup_dvd_card
    rw [htwo] at hd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd)
  apply d.no_quotient_frobenius_kernel g s hU he hD8 a R hp hp2 hRp hRne
    (le_normalizer_of_normal)
  intro k hk r hkr
  apply Subtype.ext
  have hk1 : (k : H) ≠ 1 := fun heq => hk (Subtype.ext heq)
  have hc := Fitting.centralizer_inf_eq_bot F K hdis a.torus_centralizer
    (a.element_centralizers k k.property hk1)
  apply mem_bot.mp
  rw [← hc]
  exact ⟨hRF r.property, mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp hkr).symm⟩

/-- The Fitting argument of Lemma 14.9 preserves the actual image of U.
Only the independently constructed action remains an explicit intermediate input. -/
public theorem ActionData.preserves_involutionImage
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (hsemi : TorusSemiregular M t) (s : SylowGeometry g)
    (hU : Nat.card g.U = 2) (he : ElementaryQuotient d g)
    (hD8 : m = 1 → Nat.card (residualPairStabilizer M t) ∣ 294)
    (a : ActionData d g) :
    ∀ x : quotient g, ∀ v : sylowImage d g,
      (v : pointQuotient d) ∈ involutionImage d g →
      (a.action x v : pointQuotient d) ∈ involutionImage d g := by
  let U := (involutionImage d g).subgroupOf (sylowImage d g)
  have hcard : Nat.card U = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe (involutionImage_le d g)).toEquiv).trans
      ((involutionImage_card d g).trans hU)
  exact Fitting.preserves_of_fitting_intersection
    (fittingSubgroup (quotient g)) (torusImage g)
    (a.fitting_torus_intersection_ne_bot d g s hU he hD8)
    a.element_centralizers a.torus_centralizer a.action U hcard
    (fun k hk hk1 v => a.torus_fixed_iff d g hsemi hk hk1 v)

/-- Apply Fitting preservation to the full normalizer in M/M°. -/
public theorem ActionData.normalizerInvariant_of_fitting
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (hsemi : TorusSemiregular M t) (s : SylowGeometry g)
    (hU : Nat.card g.U = 2) (he : ElementaryQuotient d g)
    (hD8 : m = 1 → Nat.card (residualPairStabilizer M t) ∣ 294)
    (a : ActionData d g) : QuotientNormalizerInvariant d g :=
  a.normalizerInvariant d g (a.preserves_involutionImage d g hsemi s hU he hD8)

/-- Burnside fusion with the Fitting normalizer-invariance premise discharged. -/
public theorem ActionData.quotientFusion_of_fitting
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (hsemi : TorusSemiregular M t) (s : SylowGeometry g)
    (hU : Nat.card g.U = 2) (he : ElementaryQuotient d g)
    (hD8 : m = 1 → Nat.card (residualPairStabilizer M t) ∣ 294)
    (a : ActionData d g) : QuotientFusion d g :=
  a.quotientFusion d g s he (a.preserves_involutionImage d g hsemi s hU he hD8)

end BenderSuzuki.ZD.SuzukiExclusion.OddNormalizer
