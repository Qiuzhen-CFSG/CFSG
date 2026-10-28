module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Centralizer
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenContradiction
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.SylowNormalizerFrattini
public import Theory.GroupTheory.ElementaryThompsonRelative
public import CFSG.Quasithin.ChapterB.Section02.UniqueOffender

/-!
# The literal plane centralizer and its ambient normalizer

The source seed is nontrivial and lies in the distinguished four-group.
If it has order four, the plane is the seed and is centralized by T.
If it has order two, the T-action on the plane is nontrivial and fixes
that seed, so its image has order two. These alternatives identify the
plane with the embedded Ω₁Z(S), where S = C_T([V,B]).

Baumann containment gives J(S) = J(T). The original characteristic-normalizer
control puts N_G(S) in M, while the omega-center identity puts it in Mc.
The actual S is Sylow in the plane centralizer, which has characteristic
two, and Frattini gives the literal plane-normalizer factorization.
In the equality row, N_G(S) therefore has order prime to three.
The final theorem applies the retained geometry directly to the existing
source terminal contradiction, leaving only its later critical-pair premises.

No residual-index identity or Held exclusion is assumed. Both remain with
qt-e-152-residual-geometry; qt-e-152-plane-geometry owns the earlier inputs
and the final discharge of the terminal critical-pair premises.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.2.12--14 and the terminal argument, printed pp.1111--1112,1119--1120.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterD ChapterD.UniqueFactor Chapter1 ChapterE ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}

/-- The two seed and Sylow-centralizer alternatives, without a residual-index premise. -/
theorem ResidualInput.plane_alternatives
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    (planeCentralizer T ⁅V,B⁆ = (T : Subgroup G) ∧ centralInvolutions T = ⁅V,B⁆) ∨
      (Nat.card (centralInvolutions T) = 2 ∧
        (planeCentralizer T ⁅V,B⁆).relIndex (T : Subgroup G) = 2) := by
  let := h.prepared.elementary
  let E := ⁅V,B⁆
  have hEV : E ≤ V := d.plane_le
  have hET : E ≤ (T : Subgroup G) := hEV.trans h.le_sylow
  have hTN : (T : Subgroup G) ≤ normalizer (E : Set G) :=
    d.outside.1.1.2.trans d.plane_normalized
  have hZc : Nat.card (centralInvolutions T) = 2 ∨ Nat.card (centralInvolutions T) = 4 := by
    have hd : Nat.card (centralInvolutions T) ∣ 2 ^ 2 := by
      change Nat.card (centralInvolutions T) ∣ 4
      rw [←d.plane_card]
      exact card_dvd_of_le d.seed_le_plane
    have hgt := (one_lt_card_iff_ne_bot (H := centralInvolutions T)).mpr
      (centralInvolutions_ne_bot_of_maximal_local T h.maximal.1)
    obtain ⟨n,hn,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    interval_cases n
    · norm_num only [pow_zero] at he
      exact (Nat.ne_of_gt hgt he).elim
    · exact Or.inl he
    · exact Or.inr he
  rcases hZc with hZ | hZ
  · refine Or.inr ⟨hZ,?_⟩
    obtain ⟨z,hz,hzne⟩ := (centralInvolutions T).bot_or_exists_ne_one.resolve_left
      (centralInvolutions_ne_bot_of_maximal_local T h.maximal.1)
    let f := actionHom (T : Subgroup G) E hTN
    have hfix : ∀ a ∈ f.range, a (⟨z,d.seed_le_plane hz⟩ : E) = ⟨z,d.seed_le_plane hz⟩ := by
      rintro a ⟨t,rfl⟩
      apply Subtype.ext
      change (t : G) * z * (t : G)⁻¹ = z
      rw [(centralInvolutions_le_centralizer_sylow T hz) t t.property,mul_inv_cancel_right]
    have hbound := card_mulAut_subgroup_le_two_of_fixed_point d.plane_card
      (⟨z,d.seed_le_plane hz⟩ : E) (fun he => hzne (congrArg Subtype.val he)) f.range hfix
    have hne : f.range ≠ ⊥ := by
      intro he
      have hEZ : E ≤ centralInvolutions T := by
        intro v hv
        apply (mem_omegaOneCenterAmbient_iff _ v).mpr
        refine ⟨hET hv,elemPow_eq_one_of_isElementaryAbelian (p := 2) v (hEV hv),?_⟩
        intro t ht
        have ht1 : f ⟨t,ht⟩ = 1 := (show f ⟨t,ht⟩ ∈ (⊥ : Subgroup (MulAut E)) from
          he ▸ (show f ⟨t,ht⟩ ∈ f.range from ⟨⟨t,ht⟩,rfl⟩))
        have hh := congrArg (fun a : MulAut E => (a ⟨v,hv⟩ : G)) ht1
        change t * v * t⁻¹ = v at hh
        exact mul_inv_eq_iff_eq_mul.mp hh
      have hh := card_le_of_le hEZ
      change Nat.card E ≤ Nat.card (centralInvolutions T) at hh
      rw [show Nat.card E = 4 from d.plane_card,hZ] at hh
      omega
    have hc : Nat.card f.range = 2 := by
      have hgt := (one_lt_card_iff_ne_bot (H := f.range)).mpr hne
      exact Nat.le_antisymm hbound (by omega)
    have hk : f.ker = (planeCentralizer T E).subgroupOf (T : Subgroup G) := by
      rw [show f = actionHom (T : Subgroup G) E hTN from rfl,actionHom_ker]
      ext t
      exact ⟨fun ht => ⟨t.property,ht⟩,fun ht => ht.2⟩
    change ((planeCentralizer T E).subgroupOf (T : Subgroup G)).index = 2
    rw [←hk,index_ker,hc]
  · have he : centralInvolutions T = E :=
      eq_of_le_of_card_ge d.seed_le_plane (by rw [hZ]; exact d.plane_card.le)
    refine Or.inl ⟨?_,he⟩
    change (T : Subgroup G) ⊓ centralizer (E : Set G) = (T : Subgroup G)
    rw [←he]
    exact inf_eq_left.mpr (le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T))

/-- The actual distinguished plane is the omega-center of its Sylow centralizer. -/
theorem ResidualInput.plane_eq_omegaCenter
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    ⁅V,B⁆ = omegaOneCenterAmbient (planeCentralizer T ⁅V,B⁆) :=
  d.geometry.omegaCenter d.plane_alternatives

/-- Baumann containment preserves the literal elementary Thompson subgroup. -/
theorem ResidualInput.planeCentralizer_thompson
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    elementaryAbelianMaxJ (planeCentralizer T ⁅V,B⁆) = elementaryAbelianMaxJ (T : Subgroup G) :=
  elementaryAbelianMaxJ_eq_of_intermediate _ _
    ((ChapterB.elementaryAbelianMaxJ_le_baumann _).trans d.geometry.baumann_le) inf_le_left

/-- The full ambient normalizer of S lies in the original intersection. -/
theorem ResidualInput.planeCentralizer_normalizer_le_intersection
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    normalizer (planeCentralizer T ⁅V,B⁆ : Set G) ≤ M ⊓ Mc := by
  have hNM : normalizer (planeCentralizer T ⁅V,B⁆ : Set G) ≤ M := by
    have hN := normalizer_le_normalizer_elementaryAbelianMaxJ (planeCentralizer T ⁅V,B⁆)
    rw [d.planeCentralizer_thompson] at hN
    exact hN.trans (source_centralizing_baumann_control h.ambient T h.maximal
      h.centralizing).2.2.2.2.2.1
  have hNMc : normalizer (planeCentralizer T ⁅V,B⁆ : Set G) ≤ Mc := by
    apply le_trans (normalizer_le_normalizer_omegaCenter _) ?_
    rw [←d.plane_eq_omegaCenter]
    exact d.plane_normalizer
  exact le_inf hNM hNMc

/-- The original S is Sylow in the actual plane centralizer. -/
theorem ResidualInput.planeCentralizer_sylow
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    IsSylowIn 2 (planeCentralizer T ⁅V,B⁆) (centralizer ((⁅V,B⁆ : Subgroup G) : Set G)) := by
  have hn := (d.outside.1.1.2.trans d.plane_normalized).trans
    (normalizer_le_normalizer_centralizer _)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T
    (centralizer ((⁅V,B⁆ : Subgroup G) : Set G)) hn
  refine ⟨P,?_⟩
  rw [hP,subgroupOf_map_subtype]
  rfl

/-- The plane normalizer is generated by its centralizer and the full normalizer of S. -/
theorem ResidualInput.plane_normalizer_factor
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    normalizer ((⁅V,B⁆ : Subgroup G) : Set G) =
      normalizer (planeCentralizer T ⁅V,B⁆ : Set G) ⊔ centralizer ((⁅V,B⁆ : Subgroup G) : Set G) := by
  obtain ⟨P,hP⟩ := d.planeCentralizer_sylow
  have hn : normalizer ((⁅V,B⁆ : Subgroup G) : Set G) ≤
      normalizer (centralizer ((⁅V,B⁆ : Subgroup G) : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer (⁅V,B⁆ : Subgroup G)
  have hf := le_normalizer_sylow_sup (centralizer ((⁅V,B⁆ : Subgroup G) : Set G))
    (normalizer ((⁅V,B⁆ : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _) hn P
  rw [hP] at hf
  apply le_antisymm hf
  apply sup_le ?_ (Subgroup.centralizer_le_normalizer _)
  have he := normalizer_le_normalizer_omegaCenter (planeCentralizer T ⁅V,B⁆)
  rwa [←d.plane_eq_omegaCenter] at he

/-- The actual plane centralizer inherits characteristic two from its normalizer. -/
theorem ResidualInput.plane_centralizer_characteristic_two
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    centralizer (pCore 2 (centralizer ((⁅V,B⁆ : Subgroup G) : Set G)) :
      Set (centralizer ((⁅V,B⁆ : Subgroup G) : Set G))) ≤
        pCore 2 (centralizer ((⁅V,B⁆ : Subgroup G) : Set G)) := by
  let E := ⁅V,B⁆
  let := h.prepared.elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective
    (inclusion d.plane_le) (inclusion_injective d.plane_le)
  have hEne : E ≠ ⊥ := by
    intro he
    have hc := d.plane_card
    change Nat.card E = 4 at hc
    rw [he,card_bot] at hc
    contradiction
  have hlocal : IsTwoLocal (normalizer (E : Set G)) :=
    ⟨E,hEne,IsElementaryAbelian.isPGroup 2 E,rfl⟩
  have hN : normalizer (E : Set G) ∈ He G :=
    lemma_1_1_4_6 T (h.ambient.evenCharacteristic T)
      ⟨mem_H_of_isTwoLocal hlocal,d.outside.1.1.2.trans d.plane_normalized⟩
  have hCne : centralizer (E : Set G) ≠ ⊥ := by
    intro he
    exact hEne (bot_unique (E.le_centralizer.trans he.le))
  exact mem_He_iff.mp (lemma_1_1_3_1 hN hCne (Subgroup.centralizer_le_normalizer _)
    (normal_subgroupOf_centralizer_normalizer (E : Set G)).isSubnormal)

/-- Actual equality-row consumer: the full normalizer of S has order prime to three. -/
theorem ResidualInput.planeCentralizer_normalizer_three_free_of_eq
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (he : partnerSpan H Mc = residual H) :
    Nat.Coprime 3 (Nat.card (normalizer (planeCentralizer T ⁅V,B⁆ : Set G))) :=
  (d.intersection_three_free_of_eq he).of_dvd_right
    (card_dvd_of_le d.planeCentralizer_normalizer_le_intersection)

/-- The literal terminal consumer uses the proved geometry with no index or Held-exclusion premise. -/
theorem ResidualInput.contradiction_of_critical_pair
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (hTS : ∀ x ∈ (T : Subgroup G), x ^ 2 = 1 → x ∈ planeCentralizer T ⁅V,B⁆)
    (hcomm : ⁅V,planeCentralizer T ⁅V,B⁆⁆ ≤ ⁅V,B⁆)
    (hs : letI := h.prepared.elementary; 1 < globalS V)
    (hoverlap : ∀ g : G, ⁅V,B⁆ ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (g : G)
    (hfirst : subgroupCorank V (V ⊓ (twoCoreIn H).map (MulAut.conj g).toMonoidHom) ≤ 1)
    (hsecond : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ twoCoreIn H) ≤ 1)
    (hmove : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) : False :=
  source_chosen_contradiction_of_critical_pair T h H ⁅V,B⁆ d.geometry
    hTS hcomm hs hoverlap g hfirst hsecond hmove

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
