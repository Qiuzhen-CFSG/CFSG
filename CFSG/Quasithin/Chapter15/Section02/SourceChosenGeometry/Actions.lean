module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry
public import CFSG.Quasithin.Chapter15.Section01.OrderingSource.Assembly
public import CFSG.Quasithin.Chapter15.Section01.ChosenCentralizerPlacement
public import Theory.GroupTheory.PResidual.PrimeTo
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Theory.SpecificGroups.OrthogonalFourBinary.OmegaResidualGeometry

/-!
# Ambient action and centralizer geometry for the source planes

Full support identifies C_M(Z) with C_M(V)T by the preceding seed-residual
bound. Every T-normal plane meets Z. The literal O^{3′}(Mc) bound therefore
makes each three-subgroup of its normalizer fix a nonidentity point of the
plane, forcing trivial action on that four-element group.

The centralizer identities follow either from maximality of the Sylow action
image or from a three-group two-residual in the action image. The natural
Omega coordinates discharge the latter premise. The former still needs the
small-model calculation. These results do not yet prove the restricted
alternatives, the unique involution image, or the numerical plane alternatives.

Source: Aschbacher--Smith, 15.2.13--14, printed pp.1111--1112,
combined manuscript of 1 March 2004, refs/quasithin.pdf.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06 ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

/-- Full support and the preceding seed-residual theorem give the second equality
of 15.2.14(5), before restricting the small action or identifying Mc. -/
theorem ChosenSmallSource.seed_centralizer_eq {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hfull : V = localModule T M) :
    M ⊓ centralizer (centralInvolutions T : Set G) =
      (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) := by
  let C := M ⊓ centralizer (centralInvolutions T : Set G)
  have hTC : (T : Subgroup G) ≤ C := le_inf h.maximal.1.2
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T))
  have hgen := congrArg (Subgroup.map C.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTC))
  rw [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTC,
    ← MonoidHom.range_eq_map, range_subtype] at hgen
  apply le_antisymm
  · change C ≤ _
    rw [← hgen]
    exact sup_le_sup_right (le_inf ((map_subtype_le _).trans inf_le_left)
      h.prepared.seed_residual) _
  · apply sup_le
    · exact inf_le_inf_left M (centralizer_le (by rw [hfull]; exact le_conjugateSpanBy _ _))
    · exact hTC

end CFSG.Quasithin.Chapter15.Section02

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The two residual conventions used by the plane construction and uniqueness
consumer agree: both mean O^{3′}, with a quotient of order prime to three. -/
theorem piResidual_threeComplement_eq_primeToResidual : piResidual {p : Nat.Primes | p.val ≠ 3} G = primeToResidual 3 G := by
  unfold piResidual primeToResidual
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN, hpi⟩
    let := hN
    refine ⟨hN, Nat.prime_three.coprime_iff_not_dvd.mpr ?_⟩
    intro hd
    exact (IsPiGroup_iff _ _).mp hpi ⟨3, Nat.prime_three⟩ hd rfl
  · rintro ⟨hN, hcop⟩
    refine ⟨hN, (IsPiGroup_iff _ _).mpr ?_⟩
    intro p hp he
    exact Nat.prime_three.coprime_iff_not_dvd.mp hcop (he ▸ hp)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry

namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06 ChosenGeometry
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The normal elementary chosen module lies in the fixed ambient Sylow group. -/
theorem ChosenSmallSource.le_sylow {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) : V ≤ (T : Subgroup G) := by
  let := h.prepared.elementary
  let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.prepared.normalized
  have hp : IsPGroup 2 (V.subgroupOf M) :=
    (IsElementaryAbelian.isPGroup 2 V).comap_subtype
  have hv := hp.le_sylow_of_normal (T.subtype h.maximal.1.2)
  intro v hvV
  exact hv (show (⟨v, h.prepared.le_selected hvV⟩ : M) ∈ V.subgroupOf M from hvV)

/-- Every nontrivial T-invariant subgroup of the chosen module meets Ω₁Z(T).
This supplies the fixed nonidentity point used in the cubic exclusion. -/
theorem ChosenSmallSource.seed_meets_normal_submodule {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) {E : Subgroup G}
    (hEV : E ≤ V) (hE : E ≠ ⊥) (hn : (T : Subgroup G) ≤ normalizer (E : Set G)) :
    centralInvolutions T ⊓ E ≠ ⊥ := by
  let := h.prepared.elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective
    (inclusion hEV) (inclusion_injective hEV)
  have hET := hEV.trans (ChosenSmallSource.le_sylow h)
  let N := E.subgroupOf (T : Subgroup G)
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  have hN : N ≠ ⊥ := by
    intro he
    have hm := map_subgroupOf_eq_of_le hET
    change N.map (T : Subgroup G).subtype = E at hm
    rw [he, Subgroup.map_bot] at hm
    exact hE hm.symm
  obtain ⟨z, hz, hzne⟩ := (center (T : Subgroup G) ⊓ N).bot_or_exists_ne_one.resolve_left
    (center_inf_ne_bot_of_normal T.isPGroup' N hN)
  have hex : ∃ z : G, z ∈ centralInvolutions T ⊓ E ∧ z ≠ 1 := by
    refine ⟨z, ⟨?_, hz.2⟩, fun he => hzne (Subtype.ext he)⟩
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨z.property, ?_, ?_⟩
    · exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) hz.2
    · intro t ht
      exact congrArg Subtype.val ((mem_center_iff.mp hz.1) ⟨t, ht⟩)
  intro he
  obtain ⟨z, hz, hzne⟩ := hex
  exact hzne (by simpa only [he, mem_bot] using hz)

/-- Every three-subgroup of Mc lies in its literal O^{3′} residual. -/
theorem threeSubgroup_le_threePrimeResidual {X Mc : Subgroup G} (hp : IsPGroup 3 X) (hle : X ≤ Mc) :
    X ≤ threePrimeResidual Mc := by
  intro x hx
  obtain ⟨n, hn⟩ := hp ⟨x, hx⟩
  rw [threePrimeResidual, piResidual_threeComplement_eq_primeToResidual]
  refine mem_map.mpr ⟨⟨x, hle hx⟩, ?_, rfl⟩
  exact mem_primeToResidual_of_pow (n := n) (Subtype.ext (congrArg (fun a : X => (a : G)) hn))

/-- The ambient obstruction in 15.2.13: a three-subgroup normalizing an
allowed plane fixes the plane pointwise. Its residual containment fixes a
nonidentity Sylow-central point; that point's automorphism stabilizer has
order at most two. No small-action classification is assumed. -/
theorem ChosenSmallSource.threeSubgroup_plane_normalizer_centralizes {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) {E X : Subgroup G}
    (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hn : (T : Subgroup G) ≤ normalizer (E : Set G))
    (hbound : normalizer (E : Set G) ≤ Mc)
    (hres : threePrimeResidual Mc ≤ centralizer (centralInvolutions T : Set G))
    (hX : IsPGroup 3 X) (hXn : X ≤ normalizer (E : Set G)) :
    X ≤ centralizer (E : Set G) := by
  have hE : E ≠ ⊥ := by
    intro he
    have hc : Nat.card E = 1 := he ▸ card_bot
    omega
  obtain ⟨z, hz, hzne⟩ := (centralInvolutions T ⊓ E).bot_or_exists_ne_one.resolve_left
    (ChosenSmallSource.seed_meets_normal_submodule h hEV hE hn)
  have hXZ : X ≤ centralizer (centralInvolutions T : Set G) :=
    (threeSubgroup_le_threePrimeResidual hX (hXn.trans hbound)).trans hres
  let f := actionHom X E hXn
  have hfix : ∀ a ∈ f.range, a (⟨z, hz.2⟩ : E) = ⟨z, hz.2⟩ := by
    rintro a ⟨x, rfl⟩
    apply Subtype.ext
    change (x : G) * z * (x : G)⁻¹ = z
    rw [← hXZ x.property z hz.1, mul_inv_cancel_right]
  have hc := card_mulAut_subgroup_le_two_of_fixed_point hcard
    (⟨z, hz.2⟩ : E) (fun he => hzne (congrArg Subtype.val he)) f.range hfix
  have hp : IsPGroup 3 f.range := hX.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hbot : f.range = ⊥ := by
    apply eq_bot_of_card_eq
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn] at hc ⊢
    cases n with
    | zero => rfl
    | succ n =>
      have hh : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by decide)
      simp only [pow_succ] at hc
      omega
  intro x hx
  have hk : (⟨x, hx⟩ : X) ∈ f.ker := by
    apply MonoidHom.mem_ker.mpr
    have hm : f ⟨x, hx⟩ ∈ f.range := ⟨⟨x, hx⟩, rfl⟩
    rwa [hbot, mem_bot] at hm
  rw [show f = actionHom X E hXn from rfl, actionHom_ker] at hk
  exact hk
end CFSG.Quasithin.Chapter15.Section02
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06 ChosenGeometry
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem partner_eq_of_intersection_centralizes {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V)
    (hi : M ⊓ Mc ≤ centralizer (centralInvolutions T : Set G)) :
    Mc = centralizer (centralInvolutions T : Set G) := by
  have hC := centralizer_le_partner T h.partner
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    h.partner ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc :=
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T)).trans hC
  have ho := source_ordering_of_centralizing_orderingMaximal h.ambient T h.empty
    h.maximal h.centralizing Mc ⟨hMc.1, hTMc⟩
  apply le_antisymm ?_ hC
  intro x hx
  obtain ⟨a, ha, c, hc, rfl⟩ := ho x hx
  exact mul_mem (hi ⟨ha.2, ha.1⟩) (centralizer_le (le_conjugateSpanBy _ _) hc.2)

/-- The centralizer conclusions 15.2.14(1),(5) in the maximal-Sylow-image rows.
The image-maximality premise is a separate model calculation for S₃, D₁₀,
and Sz(2); it is not supplied by this theorem. -/
theorem ChosenSmallSource.centralizers_of_sylow_image_coatom {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hfull : V = localModule T M)
    (hmax : IsCoatom (((T : Subgroup G).subgroupOf M).map
      (actionHom M V h.prepared.normalized).rangeRestrict)) :
    Mc = centralizer (centralInvolutions T : Set G) ∧
      M ⊓ Mc = M ⊓ centralizer (centralInvolutions T : Set G) ∧
      M ⊓ centralizer (centralInvolutions T : Set G) =
        (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) := by
  let f := (actionHom M V h.prepared.normalized).rangeRestrict
  let S := ((T : Subgroup G).subgroupOf M).map f
  let I := (M ⊓ Mc).subgroupOf M
  have hC := centralizer_le_partner T h.partner
  have hTMc : (T : Subgroup G) ≤ Mc :=
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T)).trans hC
  have hSI : S ≤ I.map f := map_mono (comap_mono (le_inf h.maximal.1.2 hTMc))
  have hIs : I.map f = S := by
    rcases hmax.le_iff.mp hSI with htop | heq
    · have hMMc : M ≤ Mc := by
        intro x hx
        have him : f ⟨x, hx⟩ ∈ I.map f := htop ▸ mem_top _
        obtain ⟨y, hy, he⟩ := him
        have hk : y⁻¹ * (⟨x, hx⟩ : M) ∈ f.ker := by
          change f (y⁻¹ * ⟨x, hx⟩) = 1
          rw [map_mul, map_inv, he, inv_mul_cancel]
        rw [show f = (actionHom M V h.prepared.normalized).rangeRestrict from rfl,
          MonoidHom.ker_rangeRestrict, actionHom_ker] at hk
        have hh := Mc.mul_mem hy.2 (h.prepared.centralizer_le_partner T h.partner hk)
        change (y : G) * ((y : G)⁻¹ * x) ∈ Mc at hh
        simpa only [mul_inv_cancel_left] using hh
      have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
        h.partner ▸ Set.mem_singleton Mc
      exact (h.different (le_antisymm hMMc (h.maximal.1.1.2 hMc.1.1 hMMc))).elim
    · exact heq
  have hIle : M ⊓ Mc ≤ (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) := by
    intro x hx
    have him : f ⟨x, hx.1⟩ ∈ S := hIs ▸ mem_map_of_mem f hx
    obtain ⟨t, ht, he⟩ := him
    have hk : t⁻¹ * (⟨x, hx.1⟩ : M) ∈ f.ker := by
      change f (t⁻¹ * ⟨x, hx.1⟩) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    rw [show f = (actionHom M V h.prepared.normalized).rangeRestrict from rfl,
      MonoidHom.ker_rangeRestrict, actionHom_ker] at hk
    have hh : (t : G) * ((t : G)⁻¹ * x) ∈
        (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) :=
      mul_mem (mem_sup_right ht)
      (mem_sup_left (show (t : G)⁻¹ * x ∈ M ⊓ centralizer (V : Set G) from
        ⟨M.mul_mem (M.inv_mem t.property) hx.1, hk⟩))
    simpa only [mul_inv_cancel_left] using hh
  have he : Mc = centralizer (centralInvolutions T : Set G) :=
    partner_eq_of_intersection_centralizes h (hIle.trans ((ChosenSmallSource.seed_centralizer_eq h hfull).ge.trans inf_le_right))
  exact ⟨he, by rw [he], h.seed_centralizer_eq hfull⟩
end CFSG.Quasithin.Chapter15.Section02
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06 ChosenGeometry
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem cover_of_threeResidual_and_sylow {N D : Type*} [Group N] [Finite N] [Group D] [Finite D]
    (P : Sylow 2 N) (f : N →* D) (h3 : IsPGroup 3 (pResidual 2 D))
    (C : Subgroup N) (hk : f.ker ≤ C)
    (hR : piResidual {p : Nat.Primes | p.val ≠ 3} N ≤ C)
    (hP : (P : Subgroup N) ≤ C) : C = ⊤ := by
  let r := f.rangeRestrict
  let S := P.mapSurjective f.rangeRestrict_surjective
  have hr3 : IsPGroup 3 (pResidual 2 f.range) :=
    (h3.comap_subtype (K := f.range)).to_le
      (map_le_iff_le_comap.mp (map_pResidual_le 2 f.range.subtype))
  have hr : pResidual 2 f.range ≤ piResidual {p : Nat.Primes | p.val ≠ 3} f.range := by
    rw [piResidual_threeComplement_eq_primeToResidual]
    intro x hx
    obtain ⟨n, hn⟩ := hr3 ⟨x, hx⟩
    exact mem_primeToResidual_of_pow (n := n)
      (congrArg (fun y : pResidual 2 f.range => (y : f.range)) hn)
  have hRc : piResidual {p : Nat.Primes | p.val ≠ 3} f.range ≤ C.map r := by
    rw [← map_piResidual_of_surjective _ r f.rangeRestrict_surjective]
    exact map_mono hR
  have hmap : C.map r = ⊤ := by
    apply top_unique
    rw [← pResidual_sup_sylow_eq_top S]
    exact sup_le (hr.trans hRc) (map_mono hP)
  apply top_unique
  intro x hx
  have hm : r x ∈ C.map r := hmap ▸ mem_top _
  obtain ⟨y, hy, he⟩ := hm
  have hkx : y⁻¹ * x ∈ f.ker := by
    change f (y⁻¹ * x) = 1
    have he' : f y = f x := congrArg Subtype.val he
    rw [map_mul, map_inv, he', inv_mul_cancel]
  simpa only [mul_inv_cancel_left] using C.mul_mem hy (hk hkx)

/-- The residual route to 15.2.14(1),(5). A three-group two-residual in the
actual action image is covered by O^{3′}; the supplied residual centralization
and the earlier ordering factorization then identify the whole partner. -/
theorem ChosenSmallSource.centralizers_of_threeGroup_twoResidual {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hfull : V = localModule T M)
    (h3 : IsPGroup 3 (pResidual 2 (internalActionImage M V h.prepared.normalized)))
    (hres : threePrimeResidual Mc ≤ centralizer (centralInvolutions T : Set G)) :
    Mc = centralizer (centralInvolutions T : Set G) ∧
      M ⊓ Mc = M ⊓ centralizer (centralInvolutions T : Set G) ∧
      M ⊓ centralizer (centralInvolutions T : Set G) =
        (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) := by
  let L := M ⊓ Mc
  let f := (actionHom M V h.prepared.normalized).rangeRestrict
  let q := f.comp (inclusion (show L ≤ M from inf_le_left))
  let C := (centralizer (centralInvolutions T : Set G)).subgroupOf L
  have hTZ : (T : Subgroup G) ≤ centralizer (centralInvolutions T : Set G) :=
    le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T)
  have hTL : (T : Subgroup G) ≤ L :=
    le_inf h.maximal.1.2 (hTZ.trans (centralizer_le_partner T h.partner))
  have hk : q.ker ≤ C := by
    intro x hx
    have hx' : inclusion (show L ≤ M from inf_le_left) x ∈ f.ker := hx
    rw [show f = (actionHom M V h.prepared.normalized).rangeRestrict from rfl,
      MonoidHom.ker_rangeRestrict, actionHom_ker] at hx'
    exact centralizer_le (show centralInvolutions T ≤ V by
      rw [hfull]; exact le_conjugateSpanBy _ _) hx'
  have hR : piResidual {p : Nat.Primes | p.val ≠ 3} L ≤ C := by
    intro x hx
    exact ((threePrimeResidual_mono (show L ≤ Mc from inf_le_right)).trans hres)
      (mem_map_of_mem L.subtype hx)
  have he : C = ⊤ := cover_of_threeResidual_and_sylow (T.subtype hTL) q h3 C hk hR (fun x hx => hTZ hx)
  have hi : L ≤ centralizer (centralInvolutions T : Set G) := by
    intro x hx
    exact (show (⟨x, hx⟩ : L) ∈ C from he ▸ mem_top _)
  have hc := partner_eq_of_intersection_centralizes h hi
  exact ⟨hc, by rw [hc], h.seed_centralizer_eq hfull⟩

/-- Original 15.2.14(1),(5) for the natural Omega row. The actual coordinate
isomorphism supplies the needed three-group residual; the only additional
source inputs are full support and the residual bound of 15.2.12. -/
theorem ChosenSmallSource.centralizers_of_omega {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hfull : V = localModule T M)
    (ho : letI := h.prepared.elementary;
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hres : threePrimeResidual Mc ≤ centralizer (centralInvolutions T : Set G)) :
    Mc = centralizer (centralInvolutions T : Set G) ∧
      M ⊓ Mc = M ⊓ centralizer (centralInvolutions T : Set G) ∧
      M ⊓ centralizer (centralInvolutions T : Set G) =
        (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) := by
  let := h.prepared.elementary
  obtain ⟨x, e, hx⟩ := ho.2.2.2.2
  have h3 : IsPGroup 3 (pResidual 2 (internalActionImage M V h.prepared.normalized)) := by
    let f := (e.toMonoidHom.comp (pResidual 2 _).subtype).codRestrict
      (pResidual 2 OrthogonalFourBinary.omega)
      (fun y => map_pResidual_le 2 e.toMonoidHom (mem_map_of_mem _ y.property))
    exact OrthogonalFourBinary.omega_twoResidual_elementary.isPGroup.of_injective f
      (fun a b hab => Subtype.ext (e.injective (congrArg Subtype.val hab)))
  exact ChosenSmallSource.centralizers_of_threeGroup_twoResidual h hfull h3 hres
end CFSG.Quasithin.Chapter15.Section02
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The distinguished-plane consumer of the cubic obstruction, retaining the
literal Kc and its source residual identity. -/
theorem ChosenPlaneGeometry.threeSubgroup_normalizer_centralizes {T : Sylow 2 G} {M Mc V H E : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (hg : ChosenPlaneGeometry h H E)
    (hresidual : partnerSpan H Mc = threePrimeResidual Mc)
    (hcentral : partnerSpan H Mc ≤ centralizer (centralInvolutions T : Set G))
    {X : Subgroup G} (hX : IsPGroup 3 X) (hXE : X ≤ normalizer (E : Set G)) :
    X ≤ centralizer (E : Set G) :=
  ChosenSmallSource.threeSubgroup_plane_normalizer_centralizes h hg.plane_le hg.plane_card (hg.outside.1.1.2.trans hg.normalized)
    hg.plane_normalizer (hresidual ▸ hcentral) hX hXE

/-- The obstruction applies uniformly to the actual commutator planes in Σ⁰(V).
The explicit inputs are 15.2.5, 15.2.8, the plane clauses of 15.2.11, and
15.2.12(4),(5). This is the ambient input to the remaining small-model exclusions. -/
theorem source_chosen_uniform_cubic_plane_centralization {T : Sylow 2 G} {M Mc V H : Subgroup G}
    (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M, Mc})
    (hquotient : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hfull : V = localModule T M)
    (hresidual : partnerSpan H Mc = threePrimeResidual Mc)
    (hcentral : partnerSpan H Mc ≤ centralizer (centralInvolutions T : Set G))
    (hplanes : ∀ B ∈ sigmaOutside (T : Subgroup G) H,
      ⁅V, B⁆ ≤ V ∧ Nat.card (⁅V, B⁆ : Subgroup G) = 4 ∧ H ≤ normalizer ((⁅V, B⁆ : Subgroup G) : Set G)) :
    ∀ B ∈ sigmaOutside (T : Subgroup G) H, ∀ X : Subgroup G,
      IsPGroup 3 X → X ≤ normalizer ((⁅V, B⁆ : Subgroup G) : Set G) → X ≤ centralizer ((⁅V, B⁆ : Subgroup G) : Set G) := by
  intro B hB X hX hXB
  obtain ⟨hBV, hcard, hnormal⟩ := hplanes B hB
  have hg := source_chosen_geometry_of_plane h hH htwo hquotient hfull hBV hcard hnormal
  exact ChosenPlaneGeometry.threeSubgroup_normalizer_centralizes hg hresidual hcentral hX hXB
end CFSG.Quasithin.Chapter15.Section02
