module
public import Stellmacher.SectionNine.DistanceOneInitialEightFixedPlane
public import Theory.GroupTheory.ElementarySixteenInvolutionNormalizer
public import Theory.GroupTheory.WreathTwoInvolutionCentralizer

/-!
# The selected eight's initial S4 normalizer quotient

In the actual distance-one local context, the explicit subgroup-selection
properties imply that the initial vertex normalizer of U modulo U is S4.
The initial faithful/local conclusions, exact Vstar containment, initial-center
invariance, moved terminal core, and intrinsic self-centralization are explicit;
no quotient-image noncentrality or normalizer model is assumed.

Restrict U to the initial stabilizer and use its actual wreath quotient map.
The kernel is the elementary order16 initial center. Comparing its quotient
with the faithful centralizer quotient, both having the same wreath image,
makes this kernel self-centralizing. The fixed-plane producer gives the
intersection of U with this kernel order4 and the exact kernel fixed subgroup.
Thus the image of U has order2 and lies in the image of the actual edge Sylow.

If this involution image were central in that Sylow, the elementary-kernel
normalizer-preimage theorem would force every terminal-core element to
normalize U. This contradicts the selected moved-core property. The native
wreath involution-centralizer theorem now supplies its S3 quotient, and the
generic faithful-elementary16 lift gives the native S4 normalizer quotient.
An explicit equivalence between native and ambient normalizers transports
the surjection and its exact kernel to the requested subgroup intersection.

Source: Stellmacher (9.1), Journal of Algebra190 (1997), p.48, the initial local
normalizer in the final elementary-eight construction.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven

/-- The actual selected elementary eight has initial normalizer quotient S4. -/
public theorem distance_one_initial_eight_normalizer
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx)
    (hlocal : DistanceOneLocalConclusion ctx)
    (U : Subgroup G) (hElem : IsElementaryAbelian 2 U) (hUcard : Nat.card U = 8)
    (hUV : U ≤ conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a'))
    (hZaN : ZAt ctx.Γ ctx.criticalPath.a ≤ Subgroup.normalizer (U : Set G))
    (hQnot : ¬ QAt ctx.Γ ctx.criticalPath.a' ≤ Subgroup.normalizer (U : Set G))
    (hself : conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a') ⊓ Subgroup.centralizer (U : Set G) = U) :
    QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.normalizer (U : Set G)) U
      (Equiv.Perm (Fin 4)) := by
  classical
  let := hElem
  let first := GAt ctx.Γ ctx.criticalPath.a
  let Za := ZAt ctx.Γ ctx.criticalPath.a
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  have hcont := distance_one_vstar_containments ctx hlength
  have hUT : U ≤ T := hUV.trans hcont.2.2.1
  obtain ⟨hTfirst, sylow, hTsylow⟩ :=
    (SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  change T ≤ first at hTfirst
  have hUfirst : U ≤ first := hUT.trans hTfirst
  have hZafirst : Za ≤ first := by
    change ZAt ctx.Γ ctx.criticalPath.a ≤ first
    rw [← hlocal.2.2.2.1]
    change ctx.Γ.twoCoreAt ctx.criticalPath.a ≤ first
    rw [ctx.Γ.twoCoreAt_def]
    exact SevenSix.twoCoreIn_le first
  have hneighbor : ctx.criticalPath.a' ∈ CosetGraphContext.neighborhood ctx.Γ ctx.criticalPath.a := by
    rw [CosetGraphContext.neighborhood, ctx.Γ.neighbors_def]
    exact (ctx.Γ.distance_symm _ _).trans (ctx.criticalPath.endpoint_distance.trans hlength)
  let : IsElementaryAbelian 2 Za := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hneighbor
  obtain ⟨f, hf, hfker⟩ := hlocal.1
  change first →* SL2TwoWreathC2 at f
  change Function.Surjective f at hf
  have hker : f.ker = Za.subgroupOf first := by rw [hfker, hlocal.2.2.2.1]
  have hAelem : IsElementaryAbelian 2 f.ker := by
    rw [hker]
    exact IsElementaryAbelian.subgroupOf hZafirst
  have hAcard : Nat.card f.ker = 16 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZafirst).toEquiv]
    exact hfaithful.1
  obtain ⟨faith, hfaith, hfaithker⟩ := hfaithful.2
  change first →* SL2TwoWreathC2 at faith
  change Function.Surjective faith at hfaith
  change faith.ker = (first ⊓ Subgroup.centralizer (Za : Set G)).subgroupOf first at hfaithker
  have hkle : f.ker ≤ faith.ker := by
    rw [hker, hfaithker]
    intro a ha
    refine ⟨a.property, ?_⟩
    intro z hz
    exact setLike_mul_comm (s := Za) hz ha
  have hkcard : Nat.card f.ker = Nat.card faith.ker := by
    have hhf := f.ker.card_mul_index
    have hhh := faith.ker.card_mul_index
    rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf, Subgroup.card_top] at hhf
    rw [Subgroup.index_ker, faith.range_eq_top_of_surjective hfaith, Subgroup.card_top] at hhh
    have hp : 0 < Nat.card SL2TwoWreathC2 := Nat.card_pos
    nlinarith
  have hkeq : f.ker = faith.ker := Subgroup.eq_of_le_of_card_ge hkle hkcard.symm.le
  have hAself : Subgroup.centralizer (f.ker : Set first) ≤ f.ker := by
    intro x hx
    rw [hkeq, hfaithker]
    refine ⟨x.property, ?_⟩
    intro z hz
    have hzker : (⟨z, hZafirst hz⟩ : first) ∈ f.ker := by rw [hker]; exact hz
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx (⟨z, hZafirst hz⟩ : first) hzker)
  let Un := U.subgroupOf first
  have hUncard : Nat.card Un = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUfirst).toEquiv).trans hUcard
  have hUnElem : IsElementaryAbelian 2 Un := IsElementaryAbelian.subgroupOf hUfirst
  have hAnorm : f.ker ≤ Subgroup.normalizer (Un : Set first) := by
    rw [hker, ← Subgroup.subgroupOf_normalizer_eq hUfirst]
    exact Subgroup.subgroupOf_mono first hZaN
  obtain ⟨hIcard, hIfix⟩ := distance_one_initial_eight_fixed_plane ctx hlength hfaithful hlocal
    U hElem hUcard hUV hZaN hQnot hself
  have hIncard : Nat.card (f.ker ⊓ Un : Subgroup first) = 4 := by
    rw [hker]
    change Nat.card ((Za ⊓ U).subgroupOf first) = 4
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hUfirst)).toEquiv]
    exact hIcard
  have hInfix : f.ker ⊓ Subgroup.centralizer (Un : Set first) = f.ker ⊓ Un := by
    rw [hker]
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      apply (hIfix.le ?_).2
      refine ⟨hx.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro u hu
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx.2 (⟨u, hUfirst hu⟩ : first) hu)
    · intro hx
      refine ⟨hx.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro u hu
      exact Subtype.ext (setLike_mul_comm (s := U) (show (u : G) ∈ U from hu) hx.2)
  have himagecard : Nat.card (Un.map f) = 2 := by
    have hh := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup first) (f.ker ⊓ Un) Un bot_le inf_le_right
    simp only [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right, Subgroup.relIndex_ker] at hh
    rw [hIncard, hUncard] at hh
    omega
  obtain ⟨z0, hz0ne, _⟩ := (Nat.card_eq_two_iff' (1 : Un.map f)).mp himagecard
  let z : SL2TwoWreathC2 := z0
  have hzne : z ≠ 1 := fun hh => hz0ne (Subtype.ext hh)
  have hz2 : z ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := z0)
    rw [himagecard] at hh
    exact congrArg Subtype.val hh
  have hzorder : orderOf z = 2 := orderOf_eq_prime hz2 hzne
  have himage : Un.map f = Subgroup.zpowers z := by
    apply (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr z0.property) ?_).symm
    rw [himagecard, Nat.card_zpowers, hzorder]
  let P := sylow.mapSurjective hf
  have hUnS : Un ≤ (sylow : Subgroup first) := by
    intro x hx
    have hTx : (x : G) ∈ T := hUT hx
    rw [← hTsylow] at hTx
    obtain ⟨y, hy, hxy⟩ := hTx
    exact (show y = x from Subtype.ext hxy) ▸ hy
  have hzP : z ∈ (P : Subgroup SL2TwoWreathC2) := Subgroup.map_mono hUnS z0.property
  have hpre := Subgroup.normalizer_eq_comap_centralizer_of_elementary_kernel
    f Un hAelem hUnElem hInfix z hzorder himage
  have hQT : Q ≤ T := by
    have hend : ctx.criticalPath.a' = ctx.criticalPath.firstStep := by
      rw [← ctx.criticalPath.path_end, ← ctx.criticalPath.path_first]
      congr 1
      exact Fin.ext hlength
    change QAt ctx.Γ ctx.criticalPath.a' ≤ T
    rw [hend]
    exact (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).2
  have hznc : z ∉ (Subgroup.center P).map (P : Subgroup SL2TwoWreathC2).subtype := by
    intro hzc
    obtain ⟨zz, hzz, heqz⟩ := hzc
    apply hQnot
    intro t ht
    have htfirst : t ∈ first := hTfirst (hQT ht)
    let tn : first := ⟨t, htfirst⟩
    have htnS : tn ∈ (sylow : Subgroup first) := by
      have hTx := hQT ht
      rw [← hTsylow] at hTx
      obtain ⟨y, hy, hyt⟩ := hTx
      exact (show y = tn from Subtype.ext hyt) ▸ hy
    have hfP : f tn ∈ (P : Subgroup _) := Subgroup.mem_map_of_mem _ htnS
    have hcomm : Commute (f tn) z := by
      rw [← heqz]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzz (⟨f tn, hfP⟩ : P))
    have htnN : tn ∈ Subgroup.normalizer (Un : Set first) := by
      rw [hpre]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    rw [← Subgroup.subgroupOf_normalizer_eq hUfirst] at htnN
    exact htnN
  obtain ⟨_, ψ, hψ, hψker⟩ := wreath_two_noncentral_involution_centralizer P z hzP hz2 hznc
  obtain ⟨_, F, hFsur, hFker⟩ := exists_symmetric_four_normalizer_of_faithful_elementary_sixteen
    f hf Un hAelem hAcard hAself hUnElem hUncard hAnorm hIncard hInfix z hzorder himage ψ hψ hψker
  let N := first ⊓ Subgroup.normalizer (U : Set G)
  let native := Subgroup.normalizer (Un : Set first)
  let eN : N ≃* native := {
    toFun := fun x => ⟨⟨x, x.property.1⟩, (Subgroup.subgroupOf_normalizer_eq hUfirst).le x.property.2⟩
    invFun := fun x => ⟨x, x.val.property, (Subgroup.subgroupOf_normalizer_eq hUfirst).ge x.property⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
    map_mul' := by intro x y; rfl }
  refine ⟨F.comp eN.toMonoidHom, hFsur.comp eN.surjective, ?_⟩
  ext x
  change F (eN x) = 1 ↔ x ∈ U.subgroupOf N
  rw [← MonoidHom.mem_ker, hFker]
  rfl

end Stellmacher.SectionNine
