module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.ShortCounting

/-!
# Full ambient short-centralizer containment, including the cubic endpoint

Endpoint automorphisms preserve the central two-core's center, so the
original nonsplitting four-plane is normal in the enlarged short centralizer.
Its nonidentity elements still form one local orbit. Consequently the enlarged
two-core centralizes the plane, while normality of the old centralizer puts
the plane in its derived subgroup. The cubic index preserves five-freeness.
The proved unique-coset count and the binary Bender/A5 nonsplitting argument
then exclude a proper ambient short centralizer.

This completes the short-centralizer containment step of Aschbacher--Smith
F.4.42 for the original endpoints in 14.2.18 and 14.3.15, printed
pp.295,987,994 (`refs/quasithin.pdf`). The genuine earlier marked realization
remains explicit. The component consumer is EightBorelShortExtension.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
local notation "P" => binaryParameters 1 Nat.zero_lt_one
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}

omit [Finite G] in
private theorem plane_image_mem (r : MarkedTriality T M Mc H) (a : ExtensionField P)
    (ha : a ≠ 0)
    (x : centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H))) :
    x ∈ markedShortPlane r a ha ↔ (r.right x.val).val ∈ ShortRootCentralizer.plane P := by
  change (markedShortCentralizerEquiv r a ha x).val ∈ ShortRootCentralizer.plane P ↔ _
  rw [markedShortCentralizerEquiv_val]

variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
include hG hempty hM hu hmany hcard e hH

/-- The old long-root four-plane remains normal in the full short centralizer. -/
theorem source_short_plane_full_normal (r : MarkedTriality T M Mc H)
    (a : ExtensionField P) (ha : a ≠ 0) :
    let C := centralizer ({(markedShortRoot r a : G)} : Set G)
    let X := M.subgroupOf C
    ((shortPlaneInAmbient r a ha).subgroupOf X).Normal := by
  let L := secondParabolic T M Mc H
  let C := centralizer ({(markedShortRoot r a : G)} : Set G)
  let X := M.subgroupOf C
  let V := shortPlaneInAmbient r a ha
  have hn := source_second_normalized hG hempty hM hu hmany hcard e hH r
  apply normal_subgroupOf_of_le_normalizer
  intro n hnX
  apply mem_normalizer_fintype
  intro v hv
  obtain ⟨y,hy,hyv⟩ := hv
  let b := L.normalizerMonoidHom ⟨n.val,hn hnX⟩
  let f := (r.right.symm.trans b).trans r.right
  have hmem : (r.right (b y.val)).val ∈ ShortRootCentralizer.plane P := by
    have hh := ShortRootCentralizer.BinaryOrbit.parabolic_automorphism_preserves_plane
      f (r.right y.val) ((plane_image_mem r a ha y).mp hy)
    simpa only [f,MulEquiv.trans_apply,MulEquiv.symm_apply_apply] using hh
  have he : (b y.val : G) = (n*v*n⁻¹ : C).val := by
    change n.val * (y.val : G) * n.val⁻¹ = _
    rw [←hyv]
    rfl
  have hyc : b y.val ∈ centralizer ({markedShortRoot r a} : Set L) := by
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    change (b y.val : G) * (markedShortRoot r a : G) =
      (markedShortRoot r a : G) * (b y.val : G)
    rw [he]
    exact mem_centralizer_singleton_iff.mp (n*v*n⁻¹ : C).property
  refine ⟨⟨b y.val,hyc⟩,(plane_image_mem r a ha _).mpr hmem,?_⟩
  exact Subtype.ext he

/-- Every nonidentity element of the original plane has unique fixed cosets
for the full endpoint centralizer. -/
theorem source_short_plane_full_unique_fixed (r : MarkedTriality T M Mc H)
    (a : ExtensionField P) (ha : a ≠ 0) :
    let C := centralizer ({(markedShortRoot r a : G)} : Set G)
    ∀ x : C, x ∈ shortPlaneInAmbient r a ha → x ≠ 1 →
      ∃! q : C ⧸ M.subgroupOf C, x • q = q := by
  dsimp only
  obtain ⟨z,hzne,_⟩ := (Nat.card_eq_two_iff' (1 : centralInvolutions T)).mp
    (plane_centralInvolutions_card T M hM.1.2 hcard e)
  have hz1 : (z : G) ≠ 1 := fun hh => hzne (Subtype.ext hh)
  have hzQ : (z : G) ∈ firstCoreCenter H := by
    rw [source_firstCore_center hG hempty hM hu hmany hcard e hH r]
    exact z.property
  intro x hx hx1
  obtain ⟨y,hy,hye⟩ := hx
  have hy1 : (y.val : G) ≠ 1 := by
    intro hh
    apply hx1
    rw [←hye]
    exact Subtype.ext hh
  obtain ⟨c,hc⟩ := marked_short_plane_orbit r hH.1.1.2 a ha hzQ hz1 y hy hy1
  apply source_short_unique_fixed hG hempty hM hu hmany hcard e hH r a ha z.property hz1 x
  exact isConj_iff.mpr ⟨(c.val : G),hc.trans (congrArg Subtype.val hye)⟩

/-- The full local short centralizer is five-free, including its cubic extension. -/
theorem source_short_full_five_free (r : MarkedTriality T M Mc H)
    (a : ExtensionField P) (ha : a ≠ 0) :
    ¬ 5 ∣ Nat.card (M.subgroupOf (centralizer ({(markedShortRoot r a : G)} : Set G))) := by
  let L := secondParabolic T M Mc H
  let C := centralizer ({(markedShortRoot r a : G)} : Set G)
  let X := M.subgroupOf C
  let X₀ := L.subgroupOf C
  have hzero : ¬ 5 ∣ Nat.card X₀ := by
    rw [←Nat.card_congr (shortLocalEquiv r a).toEquiv]
    exact marked_short_five_free r a ha
  by_cases hp : Mc = H
  · have he := source_second_eq_of_partner_eq hG hempty hM hu hmany hcard e hH r hp
    simpa only [X₀,L,he] using hzero
  · have hLM := (source_parabolics hG T hempty hM hu hmany hcard e H hH
      (firstResidualQuotientEquiv r)).2.2.2.2
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (L ⊓ C) (M ⊓ C) bot_le (inf_le_inf_right C hLM)
    simp only [relIndex_bot_left] at hc
    rw [source_short_centralizer_index_three hG hempty hM hu hmany hcard e hH r hp a ha] at hc
    have hi (A : Subgroup G) : Nat.card (A.subgroupOf C) = Nat.card (A ⊓ C : Subgroup G) :=
      card_map_of_injective (K := A.subgroupOf C) (f := C.subtype) C.subtype_injective |>.symm.trans
        (congrArg (fun B : Subgroup G => Nat.card B) (subgroupOf_map_subtype A C))
    rw [←hi L,←hi M] at hc
    intro hdvd
    rw [←hc] at hdvd
    rcases (show Nat.Prime 5 by decide).dvd_mul.mp hdvd with hh | hh
    · exact hzero hh
    · norm_num at hh

/-- The full ambient short-root centralizer lies in the original full endpoint,
including the cubic case. -/
theorem source_short_centralizer_le (r : MarkedTriality T M Mc H)
    (a : ExtensionField P) (ha : a ≠ 0) :
    centralizer ({(markedShortRoot r a : G)} : Set G) ≤ M := by
  by_contra hproper
  let L := secondParabolic T M Mc H
  let C := centralizer ({(markedShortRoot r a : G)} : Set G)
  let X := M.subgroupOf C
  let X₀ := L.subgroupOf C
  let D := centralizer ({markedShortRoot r a} : Set L)
  let V := shortPlaneInAmbient r a ha
  have hLM := (source_parabolics hG T hempty hM hu hmany hcard e H hH
    (firstResidualQuotientEquiv r)).2.2.2.2
  have hXX : X₀ ≤ X := fun _ hx => hLM hx
  obtain ⟨hVX₀,_,hVe,hVc,hVd⟩ := shortPlaneInAmbient_structure r a ha
  have hVX : V ≤ X := hVX₀.trans hXX
  let : (V.subgroupOf X).Normal := source_short_plane_full_normal
    hG hempty hM hu hmany hcard e hH r a ha
  let : IsElementaryAbelian 2 V := hVe
  have hXne : X ≠ ⊤ := by
    intro he
    apply hproper
    intro x hx
    exact show (⟨x,hx⟩ : C) ∈ X from he ▸ mem_top _
  have hnorm : X ≤ normalizer (X₀ : Set C) := by
    intro n hn
    apply mem_normalizer_fintype
    intro x hx
    exact (mem_normalizer_iff.mp
      (source_second_normalized hG hempty hM hu hmany hcard e hH r hn) x.val).mp hx
  have hcore : X₀.pCoreIn 2 ≤ X.pCoreIn 2 := pCoreIn_mono_of_normalizes hXX hnorm
  have hderived : V ≤ ⁅X.pCoreIn 2,X.pCoreIn 2⁆ :=
    hVd.trans (commutator_mono hcore hcore)
  obtain ⟨⟨eA⟩,S,hSV⟩ := CFSG.Quasithin.BinaryShortModels.unique_fixed_four_five_free_normalClosure
    V X hVX hVc (source_short_full_five_free hG hempty hM hu hmany hcard e hH r a ha) hXne
    (source_short_plane_full_unique_fixed hG hempty hM hu hmany hcard e hH r a ha)
  have hcardV : Nat.card (V.subgroupOf X) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVX).toEquiv).trans hVc
  have hcX : pCore 2 X ≤ centralizer (V.subgroupOf X : Set X) := by
    apply normal_pGroup_centralizes_of_transitive_nonidentity (pCore 2 X) (V.subgroupOf X)
      pCore_isPGroup (by rw [hcardV]; decide)
    obtain ⟨z,hzne,_⟩ := (Nat.card_eq_two_iff' (1 : centralInvolutions T)).mp
      (plane_centralInvolutions_card T M hM.1.2 hcard e)
    have hz1 : (z : G) ≠ 1 := fun hh => hzne (Subtype.ext hh)
    have hzQ : (z : G) ∈ firstCoreCenter H := by
      rw [source_firstCore_center hG hempty hM hu hmany hcard e hH r]
      exact z.property
    intro x hx hx1 y hy hy1
    obtain ⟨dx,hdx,hdxe⟩ := hx
    obtain ⟨dy,hdy,hdye⟩ := hy
    have hdx1 : (dx.val : G) ≠ 1 := fun hh =>
      hx1 (Subtype.ext (hdxe.symm.trans (Subtype.ext hh)))
    have hdy1 : (dy.val : G) ≠ 1 := fun hh =>
      hy1 (Subtype.ext (hdye.symm.trans (Subtype.ext hh)))
    obtain ⟨c,hc⟩ := marked_short_plane_orbit r hH.1.1.2 a ha hzQ hz1 dx hdx hdx1
    obtain ⟨d,hd⟩ := marked_short_plane_orbit r hH.1.1.2 a ha hzQ hz1 dy hdy hdy1
    let f : D →* X := (inclusion hXX).comp (shortLocalEquiv r a).toMonoidHom
    refine ⟨f (d*c⁻¹),Subtype.ext (Subtype.ext ?_)⟩
    have hxc : x.val.val = (c.val : G) * z * (c.val : G)⁻¹ :=
      (congrArg Subtype.val hdxe).symm.trans hc.symm
    have hyc : y.val.val = (d.val : G) * z * (d.val : G)⁻¹ :=
      (congrArg Subtype.val hdye).symm.trans hd.symm
    change ((d.val:G)*(c.val:G)⁻¹)*x.val.val*((d.val:G)*(c.val:G)⁻¹)⁻¹=y.val.val
    rw [hxc,hyc]
    group
  have hcentral : X.pCoreIn 2 ≤ centralizer (V : Set C) := by
    rintro _ ⟨q,hq,rfl⟩ v hv
    exact congrArg Subtype.val (hcX hq ⟨v,hVX hv⟩ hv)
  have hbot := alternating_five_sylow_not_le_commutator_centralizer
    (normalClosure (V : Set C)) V (X.pCoreIn 2) eA S hSV hcentral hderived
  change Nat.card V = 4 at hVc
  rw [hbot,card_bot] at hVc
  omega

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
