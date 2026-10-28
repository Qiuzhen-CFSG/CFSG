module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.FullCentralizer
public import Theory.Representation.BinaryOffender.FixedKernelResidual
public import Theory.Representation.BinaryOffender.CentralSectionAction
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# Exact supports of the full decomposable centralizer residual

The kernel on the first Thompson four-group normalizes its order-two
intersection with the first dihedral factor, hence centralizes that
involution. The four-group is exactly the involution's fixed space on
its sixteen-element support. The binary involution-kernel theorem then
forces the full two-residual to fix this support.

The opposite original odd kernel is contained in the full residual and
is normalized by the marked centralizer. Its coprime fixed/moved splitting
therefore identifies both full residual supports exactly. Transport uses
the original action map with kernel C_M(V). Both orders remain sixteen,
and the common prime remains three or five.

The actual eight-dimensional prepared-action application is in the parent
Decomposable module. Exact residual order, generation, and the identification
of the Sylow marked centralizer with the support stabilizer remain separate
source obligations; these identities alone do not construct the marker.

Source: Aschbacher--Smith 15.1.16(a)--18, printed pp.1092--1093.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

private theorem sylow_card_two {D : Type*} [Group D] [Finite D]
    (S : Sylow 2 D) {p : ℕ} (hp : Odd p) (hc : Nat.card D = 2*p) : Nat.card S = 2 := by
  have hd : 2 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 1) (by simp [hc])
  obtain ⟨k,hk⟩ := S.isPGroup'.exists_card_eq
  have hcop : Nat.Coprime (Nat.card S) p := by
    rw [hk]
    exact hp.coprime_two_left.pow_left k
  have hb : Nat.card S ∣ 2 := hcop.dvd_of_dvd_mul_right (hc ▸ card_subgroup_dvd_card _)
  exact Nat.dvd_antisymm hb hd

private theorem fixedSpace_sup_eq {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (A B : Subgroup D) :
    fixedSpace ρ (A ⊔ B) = fixedSpace ρ A ⊓ fixedSpace ρ B := by
  apply le_antisymm (le_inf (fixedSpace_antitone ρ le_sup_left)
    (fixedSpace_antitone ρ le_sup_right))
  have ha : A ≤ subspaceKernel ρ (fixedSpace ρ A ⊓ fixedSpace ρ B) ⊤ :=
    fun a ha => ⟨mem_top _,fun v hv => hv.1 ⟨a,ha⟩⟩
  have hb : B ≤ subspaceKernel ρ (fixedSpace ρ A ⊓ fixedSpace ρ B) ⊤ :=
    fun b hb => ⟨mem_top _,fun v hv => hv.2 ⟨b,hb⟩⟩
  exact fun v hv a => ((sup_le ha hb) a.property).2 v hv

private theorem first_sylow_fixed {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hTM : (T : Subgroup G) ≤ M)
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn)) :
    let ρ := imageRepresentation M V hn
    let S : Subgroup (internalActionImage M V hn) := ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict
    let F := c.ambientFactor d s.first
    let B := S ⊓ F.actor
    let W := F.space ⊓ fixedSpace ρ
      (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict)
    Nat.card B = 2 ∧ subspaceKernel ρ W F.actor = B ∧
      W = F.space ⊓ fixedSpace ρ B := by
  intro ρ S F B W
  let H := c.ambientFactor d s.second
  let Q : Sylow 2 (internalActionImage M V hn) :=
    (T.subtype hTM).mapSurjective (actionHom M V hn).rangeRestrict_surjective
  have hgen : F.actor ⊔ H.actor = Jhat ρ := by
    rw [←c.ambient_actors_generate d]
    apply le_antisymm
    · exact sup_le (le_iSup (fun k => (c.ambientFactor d k).actor) s.first)
        (le_iSup (fun k => (c.ambientFactor d k).actor) s.second)
    · exact iSup_le fun k => by
        rcases s.covers k with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
  have hcom : ∀ f ∈ F.actor, ∀ g ∈ H.actor, Commute f g := by
    intro f hf g hg
    simp only [F,H,FactorData.ambientFactor,Factor.map_actor,FactorData.embedding] at hf hg
    obtain ⟨f,hf,rfl⟩ := hf
    obtain ⟨g,hg,rfl⟩ := hg
    exact congrArg (Jhat ρ).subtype (d.actors_commute c.faithful s.distinct hf hg).eq
  have hHF : H.actor ≤ normalizer (F.actor : Set _) := by
    apply le_normalizer_iff.mpr
    intro g hg f hf
    rw [(hcom f hf g hg).symm.eq,mul_inv_cancel_right]
    exact hf
  have hFn : (F.actor.subgroupOf (Jhat ρ)).Normal :=
    normal_subgroupOf_of_le_normalizer (hgen ▸ sup_le F.actor.le_normalizer hHF)
  have hsub : F.actor.IsSubnormal := Subgroup.IsSubnormal.trans
    (hgen ▸ le_sup_left) hFn.isSubnormal (Jhat_normal ρ).isSubnormal
  obtain ⟨QF,hQF⟩ := Q.exists_subgroupOf_eq_of_subnormal F.actor hsub
  have hodd : Odd s.prime := by rcases s.prime_cases with h | h <;> rw [h] <;> decide
  have hFc : Nat.card F.actor = 2*s.prime :=
    (Nat.card_range_of_injective F.embedding.group_injective).trans
      ((Nat.card_congr (s.dihedral s.first).dihedral.some.toEquiv).trans DihedralGroup.nat_card)
  have hBc : Nat.card B = 2 := by
    have hh := sylow_card_two QF hodd hFc
    rw [hQF] at hh
    calc
      Nat.card B = Nat.card (B.subgroupOf F.actor) :=
        (Nat.card_congr (subgroupOfEquivOfLe (show B ≤ F.actor from inf_le_right)).toEquiv).symm
      _ = 2 := by
        have hSQ : (Q : Subgroup (internalActionImage M V hn)) = S := rfl
        rw [hSQ] at hh
        simpa only [B,inf_subgroupOf_right] using hh
  have he : subspaceKernel ρ W (Jhat ρ) = B ⊔ H.actor :=
    (s.core_centralizer hTM hn c d hJ).1
  have hFH : Disjoint F.actor H.actor := by
    simpa only [F,H,FactorData.ambientFactor,Factor.map_actor,FactorData.embedding] using
      Subgroup.disjoint_map (Jhat ρ).subtype_injective (d.actors_independent.pairwiseDisjoint s.distinct)
  have hHB : H.actor ≤ normalizer (B : Set (internalActionImage M V hn)) := by
    apply le_normalizer_iff.mpr
    intro g hg b hb
    rw [(hcom b hb.2 g hg).symm.eq,mul_inv_cancel_right]
    exact hb
  have hK : subspaceKernel ρ W F.actor = B := by
    apply le_antisymm
    · intro x hx
      have hxC : x ∈ subspaceKernel ρ W (Jhat ρ) := ⟨(hgen ▸ le_sup_left) hx.1,hx.2⟩
      rw [he] at hxC
      have hm : x ∈ (B : Set (internalActionImage M V hn)) * (H.actor : Set _) := by
        rw [←coe_mul_of_right_le_normalizer_left B H.actor hHB]
        exact hxC
      obtain ⟨b,hb,a,ha,rfl⟩ := hm
      have haF : a ∈ F.actor := by
        have hh := F.actor.mul_mem (F.actor.inv_mem hb.2) hx.1
        simpa only [inv_mul_cancel_left] using hh
      have ha1 : a = 1 := disjoint_def.mp hFH haF ha
      rw [ha1]
      exact (mul_one b).symm ▸ hb
    · intro b hb
      have hbC : b ∈ subspaceKernel ρ W (Jhat ρ) := he ▸ mem_sup_left hb
      exact ⟨hb.2,hbC.2⟩
  have hJ' : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict = S ⊓ Jhat ρ := hJ
  have hSJ : S ⊓ Jhat ρ ≤ B ⊔ H.actor := by
    rw [←he]
    intro g hg
    refine ⟨hg.2,?_⟩
    intro v hv
    have hv' : v ∈ fixedSpace ρ (S ⊓ Jhat ρ) := hJ' ▸ hv.2
    exact hv' ⟨g,hg⟩
  refine ⟨hBc,hK,le_antisymm ?_ ?_⟩
  · apply le_inf inf_le_left
    intro v hv b
    have hbK : (b : internalActionImage M V hn) ∈ subspaceKernel ρ W F.actor := by
      rw [hK]
      exact b.property
    exact hbK.2 v hv
  · intro v hv
    refine ⟨hv.1,?_⟩
    have hfix : v ∈ fixedSpace ρ (S ⊓ Jhat ρ) := by
      apply fixedSpace_antitone ρ hSJ
      rw [fixedSpace_sup_eq]
      exact ⟨hv.2,c.ambient_cross d s.distinct hv.1⟩
    exact hJ'.symm ▸ hfix


/-- The full marked-centralizer residual fixes the entire original first
support, for either of the original primes three and five. -/
theorem ThompsonPair.full_residual_fixes_first {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hTM : (T : Subgroup G) ≤ M)
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn)) :
    let ρ := imageRepresentation M V hn
    let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
      (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict)
    let K := subspaceKernel ρ W ⊤
    (c.ambientFactor d s.first).space ≤ fixedSpace ρ ((pResidual 2 K).map K.subtype) := by
  intro ρ W K
  let S : Subgroup (internalActionImage M V hn) := ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict
  let F := c.ambientFactor d s.first
  let B := S ⊓ F.actor
  let P := (s.marking s.second).kernel.map (c.ambientFactor d s.second).embedding.groupMap
  obtain ⟨hBc,hB,hW⟩ := first_sylow_fixed hTM hn c d s hJ
  change Nat.card B = 2 at hBc
  change subspaceKernel ρ W F.actor = B at hB
  change W = F.space ⊓ fixedSpace ρ B at hW
  have hKP : K ≤ normalizer (P : Set _) := (s.full_image_residual hTM hn c d hJ).2.1
  have hKU : K ≤ subspaceStabilizer ρ F.space := by
    rw [←s.kernel_fixed s.second s.first s.distinct.symm]
    exact fixedSpace_stable_of_normalizes ρ hKP
  have hKF : K ≤ normalizer (F.actor : Set _) :=
    hKU.trans (c.support_stabilizer_normalizes_actor d π hp hs s.first)
  have hKB : K ≤ normalizer (B : Set (internalActionImage M V hn)) := by
    rw [←hB]
    exact pointwiseKernel_normalizes ρ W F.actor K hKF le_rfl
  have hCB : K ≤ centralizer (B : Set (internalActionImage M V hn)) := hKB.trans (normalizer_le_centralizer_of_card_two B hBc)
  let : IsCyclic B := isCyclic_of_prime_card hBc
  obtain ⟨t,ht⟩ := B.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hto : orderOf t = 2 := by rw [←Nat.card_zpowers,ht,hBc]
  have htB : t ∈ B := ht ▸ mem_zpowers t
  have htD : t ^ 2 = 1 := hto ▸ pow_orderOf_eq_one t
  have htU : (t : internalActionImage M V hn) ∈ subspaceStabilizer ρ F.space := by
    apply le_subspaceStabilizer ρ F.space (A := F.actor) ?_ htB.2
    rintro a ⟨b,rfl⟩ v ⟨w,rfl⟩
    exact ⟨F.action b w,F.embedding.equivariant b w⟩
  have hBgen : zpowers t = B := ht
  have hres := residual_fixes_support_of_involution_fixed ρ F.space K hKU t htU htD
    (fun k hk _ h => h ▸ hCB hk t htB)
    (fun k hk v hv htfix => (show k ∈ subspaceKernel ρ W ⊤ from hk).2 v (by
      rw [hW]
      refine ⟨hv,?_⟩
      rw [←hBgen]
      exact (mem_fixedSpace_zpowers_iff ρ t v).mpr htfix))
  exact fun v hv r => (hres r.property).2 v hv

/-- The full residual has exactly the original fixed and moved supports.
The same opposite prime kernel supplies the lower bound and the splitting. -/
theorem ThompsonPair.full_image_residual_geometry {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hTM : (T : Subgroup G) ≤ M)
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn)) :
    let ρ := imageRepresentation M V hn
    let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
      (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict)
    let K := subspaceKernel ρ W ⊤
    let R := (pResidual 2 K).map K.subtype
    fixedSpace ρ R = (c.ambientFactor d s.first).space ∧
      subspaceCommutator ρ ⊤ R = (c.ambientFactor d s.second).space := by
  intro ρ W K R
  let P := (s.marking s.second).kernel.map (c.ambientFactor d s.second).embedding.groupMap
  have hPR : P ≤ R := (s.full_image_residual hTM hn c d hJ).1
  have hKP : K ≤ normalizer (P : Set _) := (s.full_image_residual hTM hn c d hJ).2.1
  have hfix : (c.ambientFactor d s.first).space ≤ fixedSpace ρ R :=
    s.full_residual_fixes_first hTM hn c d π hp hs hJ
  have hf : fixedSpace ρ R = (c.ambientFactor d s.first).space := by
    apply le_antisymm _ hfix
    rw [←s.kernel_fixed s.second s.first s.distinct.symm]
    exact fixedSpace_antitone ρ hPR
  have hodd : Odd (Nat.card P) := by
    rw [s.kernel_card]
    rcases s.prime_cases with h | h <;> rw [h] <;> decide
  have hcompl : IsCompl (c.ambientFactor d s.first).space (c.ambientFactor d s.second).space := by
    rw [←s.kernel_fixed s.second s.first s.distinct.symm,←s.kernel_moved s.second]
    simpa only [RegularCyclicNormalClosure.displacementSpan,subspaceCommutator,eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) hodd)
  have hstable : R ≤ subspaceStabilizer ρ (c.ambientFactor d s.second).space := by
    rw [←s.kernel_moved s.second]
    exact subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) ((map_subtype_le _).trans hKP)
  refine ⟨hf,le_antisymm ?_ ?_⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨r,hr,v,_,rfl⟩
    obtain ⟨a,ha,b,hb,he⟩ := Submodule.mem_sup.mp
      (hcompl.sup_eq_top ▸ (Submodule.mem_top (R := ZMod 2) (x := v)))
    have hra : ρ r a = a := hfix ha ⟨r,hr⟩
    rw [←he,map_add,hra]
    have he' : a + ρ r b - (a + b) = ρ r b - b := by abel
    rw [he']
    exact (c.ambientFactor d s.second).space.sub_mem ((hstable hr b).2 hb) hb
  · rw [←s.kernel_moved s.second]
    apply Submodule.span_mono
    rintro _ ⟨p,hp,v,hv,rfl⟩
    exact ⟨p,hPR hp,v,hv,rfl⟩

/-- Transport the full residual through the original action quotient. Both
fixed and moved subgroups have order sixteen and are the original supports. -/
theorem ThompsonPair.full_residual_geometry {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hTM : (T : Subgroup G) ≤ M)
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn)) :
    let Z := thompsonPlane T V (c.ambientFactor d s.first).space
    let C := M ⊓ centralizer (Z : Set G)
    let R := (pResidual 2 C).map C.subtype
    V ⊓ centralizer (R : Set G) = plane V (c.ambientFactor d s.first).space ∧
      ⁅V,R⁆ = plane V (c.ambientFactor d s.second).space ∧
      Nat.card (V ⊓ centralizer (R : Set G) : Subgroup G) = 16 ∧ Nat.card (⁅V,R⁆ : Subgroup G) = 16 := by
  let ρ := imageRepresentation M V hn
  let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
    (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict)
  let K := subspaceKernel ρ W ⊤
  obtain ⟨hf,hm⟩ := s.full_image_residual_geometry hTM hn c d π hp hs hJ
  have hW : plane V W = thompsonPlane T V (c.ambientFactor d s.first).space :=
    plane_thompson_intersection hTM hn _
  intro Z C R
  have hspaces :
      (V ⊓ centralizer (R : Set G)).subgroupOf V =
        binarySubgroup (fixedSpace ρ ((pResidual 2 K).map K.subtype)) ∧
      ⁅V,R⁆.subgroupOf V =
        binarySubgroup (subspaceCommutator ρ ⊤ ((pResidual 2 K).map K.subtype)) := by
    have hR : R = (pResidual 2 (M ⊓ centralizer (plane V W : Set G) : Subgroup G)).map
        (M ⊓ centralizer (plane V W : Set G)).subtype := by
      apply congrArg (fun D : Subgroup G => (pResidual 2 D).map D.subtype)
      exact congrArg (fun A : Subgroup G => M ⊓ centralizer (A : Set G)) hW.symm
    rw [hR]
    exact ExtraspecialMarker.residual_spaces M V hn W
  have hRnorm : R ≤ normalizer (V : Set G) :=
    ((map_subtype_le _).trans inf_le_left).trans hn
  have hRle : ⁅V,R⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp hRnorm
  have hF : V ⊓ centralizer (R : Set G) = plane V (c.ambientFactor d s.first).space := by
    rw [←map_subgroupOf_eq_of_le (show V ⊓ centralizer (R : Set G) ≤ V from inf_le_left),hspaces.1,hf]
    rfl
  have hB : ⁅V,R⁆ = plane V (c.ambientFactor d s.second).space := by
    rw [←map_subgroupOf_eq_of_le hRle,hspaces.2,hm]
    rfl
  exact ⟨hF,hB,by rw [hF]; exact s.support_card s.first,
    by rw [hB]; exact s.support_card s.second⟩

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
