module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.Algebra
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.CoprimeGeneration
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.Selection
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.Conjugation
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Source.Basic

/-!
# Constructing the actual Section 17 local configuration

The selected commuting involutions from Section 16 determine the literal
subgroup `D₀ = D ∩ C_G(tu)°`. Fusion `u ~ tu` transfers involution saturation
of the centralizer circle, so D₀ has odd order. Four-centralizer generation
on `⟨u,t⟩`, followed by coprime commutator idempotence, proves that D₀ does
not centralize t: otherwise `[O₂′(D),t]` centralizes u, contradicting the
original residual-generation theorem. Thus the noncentrality required by
`TwoCoreLocalData` is a conclusion, not a new source premise.

Source: GLS, Volume 4, Chapter 2, (17B–C) and Lemma 17.2(c,d),
`refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD.Section17.NativeSource
open Subgroup PFAppendixIII Theory.GroupTheory PFchapter1section1
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
public theorem circle_normalizer (h : IsProductDisconnected Z M) (v : G) :
    centralizer ({v} : Set G) ≤ normalizer (centralizerClosure Z v : Set G) := by
  apply le_normalizer_closure_iff.mpr
  intro g hg x hx
  exact subset_closure ⟨h.invariant g x hx.1,
    (centralizer ({v} : Set G)).mul_mem
      ((centralizer ({v} : Set G)).mul_mem hg hx.2)
      ((centralizer ({v} : Set G)).inv_mem hg)⟩

private theorem involution_zpowers_cases {t x : G} (ht : PFAppendixIII.IsInvolution t)
    (hx : x ∈ zpowers t) : x = 1 ∨ x = t := by
  classical
  have ho : orderOf t = 2 := orderOf_eq_prime ht.sq_eq_one ht.ne_one
  rw [mem_zpowers_iff_mem_range_orderOf, ho] at hx
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hx
  have hi2 := Finset.mem_range.mp hi
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · exact Or.inl (by simpa using he.symm)
  · exact Or.inr (by simpa using he.symm)

/-- The precise source (17C), retaining the original t and u. -/
public theorem residualCommutator_two_centralizers
    (h : IsProductDisconnected Z M) {t u : G}
    (ht : t ∈ Z) (htM : t ∉ M)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (htu : Commute t u) :
    residualCommutator M t =
      ⁅residualCommutator M t ⊓ centralizer ({u} : Set G), zpowers t⁆ ⊔
      ⁅residualCommutator M t ⊓ centralizer ({t * u} : Set G), zpowers t⁆ := by
  have hti := h.involutions t ht
  let W := zpowers u ⊔ zpowers t
  have hut : zpowers u ≤ centralizer ({t} : Set G) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr htu.symm.eq)
  let : IsElementaryAbelian 2 (zpowers u) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hu.sq_eq_one
  let : IsElementaryAbelian 2 W := residualFourActor_elementary hti (zpowers u) hut
  have htuNorm : t ∈ normalizer (zpowers u : Set G) :=
    Subgroup.centralizer_le_normalizer _ (by
      intro x hx
      exact mem_centralizer_singleton_iff.mp (hut hx))
  have hWcard : Nat.card W = 4 := by
    rw [card_sup_zpowers_of_normalizing_involution (zpowers u) t hti.sq_eq_one
      (fun hh => htM ((zpowers_le.mpr huD.1) hh)) htuNorm,
      Nat.card_zpowers, orderOf_eq_prime hu.sq_eq_one hu.ne_one]
  have hWK : W ≤ normalizer (residualCommutator M t : Set G) :=
    sup_le ((zpowers_le.mpr huD).trans (residualPair_le_normalizer_residualCommutator h ht htM))
      zpowers_le_normalizer_residualCommutator
  have hWt : W ≤ centralizer ({t} : Set G) :=
    sup_le hut (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
  have hgen := residualCommutator_four_generation hti W hWcard hWK hWt
  apply le_antisymm
  · apply hgen.le.trans
    apply iSup_le
    intro w
    apply iSup_le
    intro hw
    have hcases : (w : G) = 1 ∨ (w : G) = t ∨ (w : G) = u ∨ (w : G) = t * u := by
      have hwprod : (w : G) ∈ (zpowers u : Set G) * (zpowers t : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left _ _ (zpowers_le.mpr htuNorm)]
        exact w.property
      obtain ⟨a, ha, b, hb, he⟩ := hwprod
      rcases involution_zpowers_cases hu ha with rfl | rfl <;>
        rcases involution_zpowers_cases hti hb with rfl | rfl
      · exact Or.inl (by simpa using he.symm)
      · exact Or.inr (Or.inl (by simpa using he.symm))
      · exact Or.inr (Or.inr (Or.inl (by simpa using he.symm)))
      · exact Or.inr (Or.inr (Or.inr (he.symm.trans htu.symm.eq)))
    rcases hcases with hw1 | hwt | hwu | hwtu
    · exact (hw hw1).elim
    · rw [hwt]
      have hz : ⁅residualCommutator M t ⊓ centralizer ({t} : Set G), zpowers t⁆ = ⊥ := by
        apply commutator_eq_bot_iff_le_centralizer.mpr
        simpa only [zpowers_eq_closure, centralizer_closure] using (inf_le_right :
          residualCommutator M t ⊓ centralizer ({t} : Set G) ≤ centralizer ({t} : Set G))
      rw [hz]
      exact bot_le
    · rw [hwu]
      exact le_sup_left
    · rw [hwtu]
      exact le_sup_right
  · apply sup_le <;>
      exact (commutator_mono inf_le_left le_rfl).trans (residualCommutator_idempotent hti).le

/-- Lemma 17.2(c): the actual twisted intersection cannot centralize t. -/
public theorem twisted_pair_noncentral
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hg : ResidualGeneration Z M) {t u z : G}
    (ht : t ∈ Z) (htM : t ∉ M)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (htu : Commute t u) (hz : z ∈ Z) (hzM : z ∈ M) (hzu : Commute z u) :
    ¬ (residualPairStabilizer M t ⊓ centralizerClosure Z (t * u) : Subgroup G) ≤
      centralizer ({t} : Set G) := by
  intro hcent
  let K := residualCommutator M t
  let L := centralizerClosure Z (t * u)
  let H := K ⊓ centralizer ({t * u} : Set G)
  have htL : zpowers t ≤ L := zpowers_le.mpr
    (mem_centralizerClosure ht ((Commute.refl t).mul_right htu))
  have hHL : H ≤ normalizer (L : Set G) := inf_le_right.trans (circle_normalizer h _)
  have hCL : ⁅H, zpowers t⁆ ≤ L := by
    exact (commutator_mono hHL htL).trans
      (le_normalizer_iff_commutator_le_right.mp (le_refl (normalizer (L : Set G))))
  have hCD : ⁅H, zpowers t⁆ ≤ residualPairStabilizer M t :=
    ((commutator_mono inf_le_left le_rfl).trans
      (residualCommutator_idempotent (h.involutions t ht)).le).trans
        ((residualCommutator_le_oddCore (h.involutions t ht)).trans residualOddCore_le_pair)
  have hzero : ⁅H, zpowers t⁆ = ⊥ := by
    have hz : ⁅⁅H, zpowers t⁆, zpowers t⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      simpa only [zpowers_eq_closure, centralizer_closure] using (le_inf hCD hCL).trans hcent
    rwa [residualFixedCommutator_idempotent (h.involutions t ht)
      ((Commute.refl t).mul_right htu).symm] at hz
  have hK : K ≤ centralizer ({u} : Set G) := by
    apply (residualCommutator_two_centralizers h ht htM huD hu htu).le.trans
    apply sup_le
    · exact (Subgroup.commutator_le_sup
        (H₁ := residualCommutator M t ⊓ centralizer ({u} : Set G)) (H₂ := zpowers t)).trans
        (sup_le inf_le_right (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr htu.eq)))
    · exact hzero.le.trans bot_le
  exact residualCommutator_not_le_involution_centralizer h r hg hz hzM ht htM hu hzu htu hK

/-- Lemma 17.2(d): fusion from Section 16 makes the actual twisted
intersection odd. No oddness of the full two-point stabilizer is asserted. -/
public theorem twisted_pair_odd
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M) {t u : G}
    (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (htu : Commute t u)
    {z : G} (hz : z ∈ Z) (hzM : z ∈ M) (hzu : Commute z u)
    (hfusion : IsConj u (t * u)) :
    Odd (Nat.card (residualPairStabilizer M t ⊓ centralizerClosure Z (t * u) : Subgroup G)) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 heven.two_dvd
  have hxi : PFAppendixIII.IsInvolution (x : G) := by
    have ho : orderOf (x : G) = 2 := by simpa only [Subgroup.orderOf_coe] using hx
    exact ⟨(orderOf_eq_prime_iff.mp ho).2, (orderOf_eq_prime_iff.mp ho).1⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp hfusion
  have hback : MulAut.conj g⁻¹ (t * u) = u := by
    rw [← hg]
    simp only [MulAut.conj_apply, inv_inv]
    group
  have hxL := centralizerClosure_conj_mem h g⁻¹ (t * u) x.property.2
  rw [hback] at hxL
  have hxZback : MulAut.conj g⁻¹ (x : G) ∈ Z := by
    rw [centralizerClosure_eq_map] at hxL
    obtain ⟨y0, hy0, hyx⟩ := hxL
    let y : localCircle Z (centralizer ({u} : Set G)) := ⟨y0, hy0⟩
    have he : localCircleHom Z (centralizer ({u} : Set G)) y =
        MulAut.conj g⁻¹ (x : G) := hyx
    rw [← he]
    apply localCircle_involution_mem h r _ (r.involution_centralizer_ne_top h hu)
      (fun hle => htM (hle (mem_centralizer_singleton_iff.mpr htu.eq)))
      ⟨z, hz, mem_centralizer_singleton_iff.mpr hzu.eq, hzM⟩
    have hi := BenderSuzuki.IsInvolution.map_of_injective hxi (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective
    refine ⟨?_, ?_⟩
    · intro hy
      apply hi.ne_one
      have hh := he
      rw [hy, map_one] at hh
      exact hh.symm
    · apply localCircleHom_injective Z (centralizer ({u} : Set G))
      rw [map_pow, he, map_one]
      exact hi.sq_eq_one
  have hxZ := h.invariant g _ hxZback
  have hc : MulAut.conj g (MulAut.conj g⁻¹ (x : G)) = (x : G) := by
    simp only [MulAut.conj_apply, inv_inv]
    group
  rw [hc] at hxZ
  exact not_mem_Z_of_mem_residualPairStabilizer h htM x.property.1 hxZ

/-- The actual local data from the original selected involutions and the
earlier Section 16 fusion. The oddness, normalization and noncentrality
fields are all proved by this construction. -/
@[expose] public def localDataOfSelected
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hg : ResidualGeneration Z M) (t : G) (ht : t ∈ Z) (htM : t ∉ M)
    (u : residualPairIn M t) (hu : orderOf u = 2)
    (htu : Commute t ((u : M) : G)) (z : M) (hz : (z : G) ∈ Z)
    (hzu : Commute (z : G) ((u : M) : G))
    (hfusion : IsConj ((u : M) : G) (t * ((u : M) : G))) : TwoCoreLocalData Z M := by
  have huD : ((u : M) : G) ∈ residualPairStabilizer M t := u.property
  have hui : PFAppendixIII.IsInvolution ((u : M) : G) := by
    have ho : orderOf ((u : M) : G) = 2 := by simpa only [Subgroup.orderOf_coe] using hu
    exact ⟨(orderOf_eq_prime_iff.mp ho).2, (orderOf_eq_prime_iff.mp ho).1⟩
  refine {
    t := t, t_mem := ht, t_not_mem := htM, u := u, u_order := hu,
    commutes_t := htu.symm, z := z, z_mem := hz, commutes_z := hzu.symm,
    odd_twisted_pair := twisted_pair_odd h r htM hui htu hz z.property hzu hfusion,
    normalizes_twisted_pair := ?_,
    noncentral_twisted_pair := twisted_pair_noncentral h r hg ht htM huD hui htu hz z.property hzu }
  exact inf_normalizer_le_normalizer_inf
    ⟨involution_mem_normalizer_residualPairStabilizer (h.involutions t ht),
      (circle_normalizer h _) (mem_centralizer_singleton_iff.mpr
        ((Commute.refl t).mul_right htu).eq)⟩

end BenderSuzuki.ZD.Section17.NativeSource
