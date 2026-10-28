module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.Kernel
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Excluding the Tits component in the binary inspection

The source central involution acts on the centerless component as conjugation
by a nonidentity involution in its Sylow center. A genuine Parrott--Atlas
isomorphism and Sylow conjugacy identify that involution with `r5`.
Its centralizer contains the first marked parabolic, so the source centralizer
bound puts this parabolic in the actual component local subgroup. Exhaustive
Sylow-overgroup coverage, and the intersection of the first parabolic with the
second normalizer, force that local subgroup to equal the first parabolic.

Every nontrivial subgroup normal in the marked Sylow subgroup contains `r5`,
its unique nonidentity central element. Applied to the original normal
four-group, this gives a nonidentity element fixed by the actor, contradicting
its already proved fixed-point-free action. All transport uses actual
multiplicative equivalences. No parabolic classification or two-core shape is
assumed; in particular the disputed printed first-core invariant is unused.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the n = 1
paragraph of 15.3.43, printed p.1140, with A.2.3--4, p.33, and the source
involution of 1.1.5(3). The intrinsic local facts use Parrott (1972), p.683.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.ExceptionalInspection

private theorem r5_mem_of_normalized (W : Subgroup Tits.Atlas1600Group)
    (hle : W ≤ Tits.atlas1600SylowTwoSubgroup) (hne : W ≠ ⊥)
    (hn : Tits.atlas1600SylowTwoSubgroup ≤ normalizer (W : Set Tits.Atlas1600Group)) :
    Tits.atlas1600R5 ∈ W := by
  let T := Tits.atlas1600SylowTwoSubgroup
  let N := W.subgroupOf T
  have hWT : W ≤ T := hle
  have hN : N ≠ ⊥ := by
    intro h
    apply hne
    have hm := congrArg (fun A : Subgroup T => A.map T.subtype) h
    simpa only [N, map_subgroupOf_eq_of_le hWT, Subgroup.map_bot] using hm
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  let : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact (IsPGroup 2 T) := ⟨IsPGroup.of_card (n := 11)
    (by norm_num [T, Tits.atlas1600SylowTwoSubgroup_card])⟩
  obtain ⟨w, hw, hwc⟩ := exists_nontrivial_center_mem_normal (p := 2) N
  rcases (Tits.atlas1600SylowTwo_mem_center_iff w.val).mp hwc with he | he
  · exact (hw (Subtype.ext (Subtype.ext he))).elim
  · exact he ▸ w.property

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

omit [Finite G] in
private theorem inner_involution
    (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {z : G} (hz : SourceInvolution S M z) (hi : ActsInner L z)
    (hZ : center L = ⊥) (P : Sylow 2 L)
    (hP : (P : Subgroup L) = S.subgroupOf L) :
    ∃ t : L, t ≠ 1 ∧ t ∈ (P : Subgroup L) ∧
      t ∈ centralizer (P : Set L) ∧
      (∀ x : L, z * (x : G) * z⁻¹ = (t : G) * (x : G) * (t : G)⁻¹) := by
  obtain ⟨t, ht⟩ := hi
  have htne : t ≠ 1 := by
    intro he
    apply c.component_outside
    intro x hx
    apply hz.centralizer_le
    apply mem_centralizer_singleton_iff.mpr
    have heq := ht ⟨x, hx⟩
    rw [he] at heq
    simp only [coe_one, one_mul, inv_one, mul_one] at heq
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  let ρ : I →* MulAut L := L.normalizerMonoidHom.comp (inclusion c.normalizes)
  let zi : I := ⟨z, (sylow_le_local c hz.mem).2⟩
  have hconj : ρ zi = MulAut.conj t := by
    apply MulEquiv.ext
    intro x
    exact Subtype.ext (ht x)
  have hzi : zi ^ 2 = 1 := Subtype.ext (hz.order ▸ pow_orderOf_eq_one z)
  have ht2 : t ^ 2 = 1 := by
    apply MulAut.conj_injective_of_center_eq_bot hZ
    rw [map_pow, ← hconj, ← map_pow, hzi, map_one, map_one]
  have htc : t ∈ centralizer (P : Set L) := by
    intro x hx
    apply Subtype.ext
    have hxS : (x : G) ∈ S := by
      change x ∈ S.subgroupOf L
      rwa [← hP]
    have heq : (t : G) * (x : G) * (t : G)⁻¹ = (x : G) := by
      rw [← ht, ← hz.central x hxS, mul_inv_cancel_right]
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  have htP : t ∈ (P : Subgroup L) := by
    have hp : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers]
      change orderOf t = 2
      exact orderOf_eq_prime ht2 htne)
    have hm : t ∈ zpowers t ⊓ normalizer (P : Set L) :=
      ⟨mem_zpowers t, Subgroup.centralizer_le_normalizer _ htc⟩
    rw [hp.inf_normalizer_sylow P] at hm
    exact hm.2
  exact ⟨t, htne, htP, htc, ht⟩

/-- The Tits alternative cannot occur in the reduced binary configuration. -/
public theorem not_tits (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {z : G} (hz : SourceInvolution S M z) (hs : IsSimpleGroup L)
    (hi : ActsInner L z) (iso : Nonempty (L ≃* Tits.ParrottGroup)) : False := by
  let hm : Model L z 1 := .simple hs (.rankTwo (.tits rfl iso)) hi
  have hZ := binary_center_eq_bot c hm
  obtain ⟨P, hP⟩ := component_sylow c
  have hPL : (P : Subgroup L) = S.subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [hP, subgroupOf_map_subtype]
  obtain ⟨t, htne, htP, htc, ht⟩ := inner_involution c hz hi hZ P hPL
  obtain ⟨e⟩ := iso
  obtain ⟨f, hf⟩ := Tits.RelativeSylowMarking.exists_sylow_marking
    (e.trans Tits.parrottFiniteImageEquiv) P
  have hft : f t = Tits.atlas1600R5 :=
    Tits.RelativeSylowMarking.image_eq_r5_of_sylow_center f P hf htP htc htne
  let H := (M.subgroupOf L).map f.toMonoidHom
  have hHproper : H ≠ ⊤ := by
    intro he
    have hM : M.subgroupOf L = ⊤ := Subgroup.map_injective f.injective
      (he.trans (map_top_of_surjective f.toMonoidHom f.surjective).symm)
    exact c.component_outside (subgroupOf_eq_top.mp hM)
  have hSH : Tits.atlas1600SylowTwoSubgroup ≤ H := by
    rw [← hf, hPL]
    exact map_mono (fun x hx => c.sylow_le_M hx)
  have hfirst : Tits.ExceptionalParabolics.first ≤ H := by
    intro x hx
    let a := f.symm x
    have hac : a * t = t * a := by
      apply f.injective
      simpa only [map_mul, a, MulEquiv.apply_symm_apply, hft] using
        mem_centralizer_singleton_iff.mp (Tits.ExceptionalParabolics.first_le_centralizer hx)
    have ham : (a : G) ∈ M := by
      apply hz.centralizer_le
      apply mem_centralizer_singleton_iff.mpr
      have heq : z * (a : G) * z⁻¹ = a := by
        rw [ht]
        have hh := congrArg Subtype.val hac.symm
        change (t : G) * (a : G) = (a : G) * (t : G) at hh
        rw [hh, mul_inv_cancel_right]
      exact (mul_inv_eq_iff_eq_mul.mp heq).symm
    exact mem_map.mpr ⟨a, ham, f.apply_symm_apply x⟩
  have hHfirst : H = Tits.ExceptionalParabolics.first := by
    rcases Tits.ConverseLocalCoverage.le_first_or_second H hHproper hSH with h | h
    · exact le_antisymm h hfirst
    · have hfirstS : Tits.ExceptionalParabolics.first ≤ Tits.atlas1600SylowTwoSubgroup := by
        intro x hx
        exact Tits.RelativeParabolicNormalizers.first_inf_normalizer_secondCenter.le
          ⟨hx, Tits.RelativeParabolicNormalizers.second_le_normalizer_secondCenter (h (hfirst hx))⟩
      have hcard := Nat.card_le_card_of_injective
        (inclusion hfirstS) (inclusion_injective hfirstS)
      rw [Tits.ReeLocalBlockOrders.first_card, Tits.atlas1600SylowTwoSubgroup_card] at hcard
      omega
  let W := (V₂.subgroupOf L).map f.toMonoidHom
  have hWS : W ≤ Tits.atlas1600SylowTwoSubgroup := by
    rw [← hf, hPL]
    exact map_mono (fun x hx => c.plane_two_le hx)
  have hWne : W ≠ ⊥ := by
    intro he
    have hV : V₂.subgroupOf L = ⊥ :=
      Subgroup.map_injective f.injective (he.trans (Subgroup.map_bot f.toMonoidHom).symm)
    have hVbot : V₂ = ⊥ := by
      have hm := congrArg (fun A : Subgroup L => A.map L.subtype) hV
      simpa only [map_subgroupOf_eq_of_le (plane_le_component c), Subgroup.map_bot] using hm
    have hcard : Nat.card V₂ = 1 := Subgroup.card_eq_one.mpr hVbot
    rw [c.plane_two_card] at hcard
    omega
  have hWnorm : Tits.atlas1600SylowTwoSubgroup ≤ normalizer (W : Set Tits.Atlas1600Group) := by
    rw [← hf, hPL, ← map_equiv_normalizer_eq]
    apply map_mono
    rw [← subgroupOf_normalizer_eq (plane_le_component c)]
    exact fun x hx => c.plane_two_normalized (sylow_le_local c hx)
  have htV : (t : G) ∈ V₂ := by
    have hh := r5_mem_of_normalized W hWS hWne hWnorm
    rw [← hft] at hh
    obtain ⟨v, hv, he⟩ := hh
    exact f.injective he ▸ hv
  have htY : (t : G) ∈ centralizer (Yplus : Set G) := by
    intro y hy
    let yl : L := ⟨y, c.y_le_component hy⟩
    have hyH : f yl ∈ H := mem_map_of_mem f.toMonoidHom (actor_le_local c hy).1
    rw [hHfirst] at hyH
    have hcomm := mem_centralizer_singleton_iff.mp
      (Tits.ExceptionalParabolics.first_le_centralizer hyH)
    rw [← hft, ← map_mul, ← map_mul] at hcomm
    exact congrArg Subtype.val (f.injective hcomm)
  let : IsKleinFour V₂ := plane_isKleinFour c
  have hgen : theta Yplus = Yplus := by rw [← c.theta_eq, theta_idempotent]
  have hzero := fourGroup_centralizer_eq_bot hgen
    ((actor_le_local c).trans c.plane_two_normalized) c.plane_two_commutator
  exact htne (Subtype.ext (hzero.le ⟨htV, htY⟩))

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.ExceptionalInspection
