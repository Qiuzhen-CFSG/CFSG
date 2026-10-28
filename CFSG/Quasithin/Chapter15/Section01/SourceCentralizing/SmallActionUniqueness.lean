module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OrbitUniqueness
public import CFSG.Quasithin.Chapter15.Section01.ChosenCentralizerPlacement
public import Theory.GroupTheory.SixActionSylowOvergroup
public import Theory.GroupTheory.SylowIndexThreeProduct
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# Original maximal overgroups in the small-action Case II rows

The original ordering implies that a third maximal two-local subgroup has
intersection with M escaping the distinguished partner Mc. For a chosen
action of order six, that intersection must induce the full action: an image
which is a two-group would lie in the original Sylow image and lift into Mc.
Full action gives the central-seed span, whose proved uniqueness is a
contradiction.

The second route uses the literal normalizer of Z cap V. Its full ambient
normalizer lies in Mc by the singleton centralizer hypothesis. If its index
in M is three, the escaping intersection supplements it, again giving the
same seed span. All groups, maps, and chosen V remain the source objects.
These prove the corresponding15.2.5 rows, not the later CaseII contradiction.

Source: Aschbacher--Smith15.2.2 and15.2.5, printed pp.1104,1107.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- Original15.2.5 for the order-six chosen action, without later source premises. -/
theorem PreparedChosenModule.maximal_overgroups_of_action_card_six
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (hc : Nat.card (internalActionImage M V hV.normalized) = 6) :
    maximalTwoLocalOvergroups (T : Subgroup G) = {M, Mc} := by
  classical
  let := hV.elementary
  let D := internalActionImage M V hV.normalized
  let f : M →* D := (actionHom M V hV.normalized).rangeRestrict
  have hf : Function.Surjective f := (actionHom M V hV.normalized).rangeRestrict_surjective
  let P := (T.subtype hM.1.2).mapSurjective hf
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  ext N
  constructor
  · intro hN
    by_cases hNM : N = M
    · simp [hNM]
    have ho := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN
    let H := M ⊓ N
    have hTH : (T : Subgroup G) ≤ H := le_inf hM.1.2 hN.2
    have hHout (hNMc : N ≠ Mc) : ¬ H ≤ Mc := by
      intro hH
      have hle : N ≤ Mc := by
        intro x hx
        obtain ⟨a, ha, b, hb, rfl⟩ := ho x hx
        exact Mc.mul_mem (hH ⟨ha.2,ha.1⟩)
          (localModule_centralizer_le_partner T N hu hb.2)
      exact hNMc (le_antisymm hle (hN.1.2 hMc.1.1 hle))
    by_cases hNMc : N = Mc
    · simp [hNMc]
    let A := (H.subgroupOf M).map f
    have hPA : (P : Subgroup D) ≤ A := map_mono (show (T : Subgroup G).subgroupOf M ≤
        H.subgroupOf M from comap_mono hTH)
    have hAnot : ¬ IsPGroup 2 A := by
      intro hA
      have hAP : A ≤ (P : Subgroup D) := (P.is_maximal' hA hPA).le
      apply hHout hNMc
      intro x hx
      have hxA : f ⟨x,hx.1⟩ ∈ A := mem_map_of_mem f hx
      obtain ⟨t, ht, he⟩ := hAP hxA
      have hk : t⁻¹ * (⟨x,hx.1⟩ : M) ∈ f.ker := by
        change f (t⁻¹ * ⟨x,hx.1⟩) = 1
        rw [map_mul,map_inv,he,inv_mul_cancel]
      have hk' : t⁻¹ * (⟨x,hx.1⟩ : M) ∈ (actionHom M V hV.normalized).ker := by
        exact congrArg (fun d : D => (d : MulAut V)) hk
      rw [actionHom_ker] at hk'
      have hxc : (t : G)⁻¹ * x ∈ Mc := hV.centralizer_le_partner T hu hk'
      have hh : (t : G) * ((t : G)⁻¹ * x) ∈ Mc := Mc.mul_mem (hTMc ht) hxc
      simpa only [mul_inv_cancel_left] using hh
    have hAtop : A = ⊤ := eq_top_of_sylow_le_of_six_action P A hPA hAnot
      (MonoidHom.id D) (by rw [MonoidHom.ker_id]; exact IsPGroup.of_bot) hc
    have himage : (actionHom M V hV.normalized).range ≤
        (H.subgroupOf M).map (actionHom M V hV.normalized) := by
      rintro x ⟨m,rfl⟩
      have hm : f m ∈ A := hAtop ▸ mem_top _
      obtain ⟨y,hy,he⟩ := hm
      exact ⟨y,hy,congrArg (fun d : D => (d : MulAut V)) he⟩
    have huniq := Section02.source_unique_overgroup_of_full_action hG T hempty hM hJ
      hV hTH inf_le_left himage
    exact (hNM (Set.mem_singleton_iff.mp (huniq ▸
      (show N ∈ maximalTwoLocalOvergroups H from ⟨hN.1,inf_le_right⟩)))).elim
  · intro hN
    rcases Set.mem_insert_iff.mp hN with rfl | hN
    · exact hM.1
    · obtain rfl := Set.mem_singleton_iff.mp hN
      exact ⟨hMc.1,hTMc⟩


/-- The actual central seed has its full normalizer inside the distinguished partner. -/
theorem PreparedChosenModule.central_seed_normalizer_le_partner
    (T : Sylow 2 G) {M Mc V : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V) :
    normalizer (centralInvolutions T ⊓ V : Set G) ≤ Mc := by
  have hseed : centralInvolutions T ⊓ V ≠ ⊥ := by
    intro he
    apply hV.nontrivial
    rw [hV.seed_span,he]
    exact bot_unique (conjugateSpanBy_le bot_le (by
      change M ≤ normalizer (⊥ : Subgroup G)
      rw [normalizer_eq_top]
      exact le_top))
  apply normalizer_le_of_unique_maximalTwoLocal
    (fun L hL hCL => Set.mem_singleton_iff.mp (hu ▸
      (show L ∈ maximalTwoLocalOvergroups
        (centralizer (centralInvolutions T : Set G)) from ⟨hL,hCL⟩)))
    (T.isPGroup'.to_le (inf_le_left.trans (by
      intro z hz
      exact ((mem_omegaOneCenterAmbient_iff _ z).mp hz).1))) hseed
  exact (centralizer_le (show centralInvolutions T ⊓ V ≤ centralInvolutions T from
    inf_le_left)).trans (Subgroup.centralizer_le_normalizer _)

/-- The index-three seed-normalizer row of original15.2.5. -/
theorem PreparedChosenModule.maximal_overgroups_of_seed_index_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (hi : (M ⊓ normalizer (centralInvolutions T ⊓ V : Set G)).relIndex M = 3) :
    maximalTwoLocalOvergroups (T : Subgroup G) = {M, Mc} := by
  classical
  let := hV.elementary
  let ZV := centralInvolutions T ⊓ V
  let B := M ⊓ normalizer (ZV : Set G)
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hTB : (T : Subgroup G) ≤ B := by
    refine le_inf hM.1.2 ?_
    exact (le_inf
      ((le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)).trans
        (Subgroup.centralizer_le_normalizer _))
      (hM.1.2.trans hV.normalized)).trans inf_normalizer_le_normalizer_inf
  have hBMc : B ≤ Mc := inf_le_right.trans (hV.central_seed_normalizer_le_partner T hu)
  ext N
  constructor
  · intro hN
    by_cases hNM : N = M
    · simp [hNM]
    by_cases hNMc : N = Mc
    · simp [hNMc]
    let H := M ⊓ N
    have hTH : (T : Subgroup G) ≤ H := le_inf hM.1.2 hN.2
    have hHout : ¬ H ≤ B := by
      intro hHB
      have ho := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN
      have hle : N ≤ Mc := by
        intro x hx
        obtain ⟨a,ha,b,hb,rfl⟩ := ho x hx
        exact Mc.mul_mem (hBMc (hHB ⟨ha.2,ha.1⟩))
          (localModule_centralizer_le_partner T N hu hb.2)
      exact hNMc (le_antisymm hle (hN.1.2 hMc.1.1 hle))
    have hp : (H : Set G) * (B : Set G) = (M : Set G) :=
      coe_mul_eq_of_index_three_sylow T hTH hTB inf_le_left inf_le_left hi hHout
    have hspan := Section02.source_seed_span_of_product T (M := M) (M₀ := M)
      (X := H) inf_le_left hV.normalized hV.seed_span (Or.inr hp.ge)
    have huniq := Section02.source_unique_overgroup_of_seed_span hG T hempty hM hJ
      hTH inf_le_left hV.nontrivial hV.normalized hspan
    exact (hNM (Set.mem_singleton_iff.mp (huniq ▸
      (show N ∈ maximalTwoLocalOvergroups H from ⟨hN.1,inf_le_right⟩)))).elim
  · intro hN
    rcases Set.mem_insert_iff.mp hN with rfl | hN
    · exact hM.1
    · obtain rfl := Set.mem_singleton_iff.mp hN
      exact ⟨hMc.1,hTMc⟩

/-- The actual symmetric-three source action discharges the order-six premise. -/
theorem PreparedChosenModule.maximal_overgroups_of_symmetric_three_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (e : internalActionImage M V hV.normalized ≃* Equiv.Perm (Fin 3)) :
    maximalTwoLocalOvergroups (T : Subgroup G) = {M, Mc} := by
  apply hV.maximal_overgroups_of_action_card_six hG T hempty hM hJ hu
  exact (Nat.card_congr e.toEquiv).trans (by rw [Nat.card_eq_fintype_card]; decide)

end CFSG.Quasithin.Chapter15.Section01
