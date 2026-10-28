module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalAlignment
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicKernelTransport
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardRigidity
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ElementaryKernelModel

public import Theory.Representation.BinaryPermutation.CoreFixedLine
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.BinaryOffender.NormalizerConjugateDimension

/-!
# Saturation of the terminal moving attachment

In the nonnormalizing branch of MS93 (5.10), the restricted commutator
and the last critical line span the entire moving central attachment.
On the augmentation cover, an actor centralizing a transposition moves
its fixed hyperplane away from the transposition's displacement line;
the remaining fixed space has dimension at most one. On the natural
cover that fixed space is zero. This gives saturation on both full covers.

The original cubic projection and faithful graph charts transfer this
calculation to the actual critical seeds. The common edge intersection
is therefore the whole moving attachment at the last shifted vertex.
The literal backward transporters carry the equality to the reverse
endpoint at distance six. Alignment there puts the preceding critical
line in the last selected seed. TerminalAvoidance uses this containment
to exclude the nonnormalizing branch.

The projection kernel remains E, including its odd quotient E/Q, and
all fixed parts of the order-32 cover are retained. The literal original
source application is in OriginalSylowExceptional.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.10), printed p.922.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.AttachmentModel
local notation "S" => Equiv.Perm (Fin 6)
local notation "ρ" => coreRepresentation (Fin 6)

private theorem core_fixed_disjoint (t : S) (hs : t.IsSwap) (P : Subgroup S)
    (hP : P ≤ centralizer ({t} : Set S)) :
    Disjoint (subspaceCommutator ρ (fixedSpace ρ (zpowers t)) P)
      (subspaceCommutator ρ ⊤ (zpowers t)) := by
  obtain ⟨i,j,hij,rfl⟩ := hs
  let f : core (Fin 6) →ₗ[ZMod 2] ZMod 2 :=
    (LinearMap.proj i).comp (core (Fin 6)).subtype
  have hzero : subspaceCommutator ρ (fixedSpace ρ (zpowers (Equiv.swap i j))) P ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,hv,rfl⟩
    have hc : Commute g (Equiv.swap i j) :=
      ((hP hg) _ (Set.mem_singleton _)).symm
    have hm := (Equiv.Perm.mem_support_iff_of_commute hc.inv_left i).mpr
      (by simp [Equiv.Perm.support_swap hij])
    have hp : g⁻¹ i = i ∨ g⁻¹ i = j := by
      simpa [Equiv.Perm.support_swap hij] using hm
    have he : v.val j = v.val i := by
      have hh := congrArg (fun w : core (Fin 6) => w.val i)
        ((mem_fixedSpace_zpowers_iff ρ (Equiv.swap i j) v).mp hv)
      simpa using hh
    change v.val (g⁻¹ i) - v.val i = 0
    rcases hp with hi | hj
    · rw [hi,sub_self]
    · rw [hj,he,sub_self]
  apply Submodule.disjoint_def.mpr
  intro v hv hd
  have hz : v.val i = 0 := hzero hv
  rw [Representation.CyclicFixedRank.commutator_eq_range] at hd
  obtain ⟨w,rfl⟩ := hd
  have he : w.val j = w.val i := by
    apply sub_eq_zero.mp
    simpa using hz
  apply Subtype.ext
  ext k
  change w.val ((Equiv.swap i j)⁻¹ k) - w.val k = 0
  by_cases hki : k=i
  · subst k; simpa using sub_eq_zero.mpr he
  by_cases hkj : k=j
  · subst k; simpa using sub_eq_zero.mpr he.symm
  simp [Equiv.swap_apply_of_ne_of_ne hki hkj]

private theorem core_fixed_finrank :
    Module.finrank (ZMod 2) (fixedSpace ρ ⊤) ≤ 1 := by
  have hle : fixedSpace ρ ⊤ ≤ coreConstants (Ω := Fin 6) := by
    intro v hv
    exact (core_fixed_iff_constant (by simp : 3 ≤ Nat.card (Fin 6)) v).mp
      (fun a => hv ⟨a.val,mem_top _⟩)
  have hd : Module.finrank (ZMod 2) (coreConstants (Ω := Fin 6)) = 1 := by
    have hc := card_coreConstants (Ω := Fin 6) (by decide)
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) (show 2 ^ _ = 2 ^ 1 from hc)
  exact (Submodule.finrank_mono hle).trans_eq hd

private theorem natural_fixed_zero : fixedSpace (naturalRepresentation (Fin 6)) ⊤ = ⊥ := by
  apply le_bot_iff.mp
  intro v hv
  have hf : Function.Injective (alternatingNaturalRepresentation (Fin 6)) := by
    intro g k he
    exact Subtype.ext (naturalRepresentation_injective (Fin 6) (by decide) he)
  exact (invariants_eq_bot_of_faithful_irreducible _ hf
    (alternatingNatural_isIrreducible (by decide : 5 ≤ Fintype.card (Fin 6)))).le
      (fun a => hv ⟨a.val,mem_top _⟩)

private theorem attachment_saturation
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y]
    (H D C : Submodule (ZMod 2) Y) (hne : H ≠ ⊥)
    (hdis : Disjoint H D) (hle : H ≤ D ⊔ C)
    (hC : Module.finrank (ZMod 2) C ≤ 1) : C ≤ H ⊔ D := by
  have hpos : 0 < Module.finrank (ZMod 2) H := by
    by_contra! hh
    exact hne (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hh))
  have he := Submodule.finrank_sup_add_finrank_inf_eq H D
  rw [disjoint_iff.mp hdis,finrank_bot,add_zero] at he
  have hu := Submodule.finrank_sup_add_finrank_inf_eq D C
  have hd : Module.finrank (ZMod 2) ↥(D ⊔ C) ≤ Module.finrank (ZMod 2) ↥(H ⊔ D) := by omega
  have heq := Submodule.eq_of_le_of_finrank_le (sup_le hle le_sup_left) hd
  exact le_sup_right.trans_eq heq.symm

/-- The full fixed attachment is generated by a nonzero aligned
fixed-hyperplane commutator and the transposition displacement line. -/
private theorem cover_attachment_saturation
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y]
    (σ : Representation (ZMod 2) S Y)
    (hm : SixCover.IsNaturalOrCore σ (MonoidHom.id S))
    (t : S) (hs : t.IsSwap) (P : Subgroup S)
    (hP : P ≤ centralizer ({t} : Set S))
    (H : Submodule (ZMod 2) Y) (hne : H ≠ ⊥)
    (hH : H ≤ subspaceCommutator σ (fixedSpace σ (zpowers t)) P)
    (halign : H ≤ subspaceCommutator σ ⊤ (zpowers t) ⊔ fixedSpace σ ⊤) :
    fixedSpace σ ⊤ ≤ H ⊔ subspaceCommutator σ ⊤ (zpowers t) := by
  rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩
  · have he := fixedSpace_map_equivariant σ (naturalRepresentation (Fin 6))
      (MonoidHom.id S) E hE ⊤
    rw [map_id,natural_fixed_zero] at he
    have hz : fixedSpace σ ⊤ = ⊥ := by
      apply le_bot_iff.mp
      intro v hv
      have hh : E v ∈ (fixedSpace σ ⊤).map E.toLinearMap := ⟨v,hv,rfl⟩
      rw [he] at hh
      exact E.injective (hh.trans E.map_zero.symm)
    rw [hz]
    exact bot_le
  · have hfix (A : Subgroup S) := fixedSpace_map_equivariant σ ρ (MonoidHom.id S) E hE A
    simp only [map_id] at hfix
    have hmap (W : Submodule (ZMod 2) Y) (A : Subgroup S) :
        (subspaceCommutator σ W A).map E.toLinearMap = subspaceCommutator ρ (W.map E.toLinearMap) A := by
      have he := subspaceCommutator_map_embedding ρ σ (MonoidHom.id S) E.toLinearMap
        (fun g v => (hE g v).symm) A W
      simpa only [map_id] using he.symm
    have hdis := core_fixed_disjoint t hs P hP
    have hh := Submodule.map_mono (f := E.toLinearMap) hH
    rw [hmap,hfix] at hh
    have hdmap : (subspaceCommutator σ ⊤ (zpowers t)).map E.toLinearMap =
        subspaceCommutator ρ ⊤ (zpowers t) := by rw [hmap,Submodule.map_top,E.range]
    have hdis' : Disjoint H (subspaceCommutator σ ⊤ (zpowers t)) := by
      apply Submodule.disjoint_def.mpr
      intro v hv hd
      have hv' := hh (show E v ∈ H.map E.toLinearMap from ⟨v,hv,rfl⟩)
      have hd' : E v ∈ (subspaceCommutator σ ⊤ (zpowers t)).map E.toLinearMap := ⟨v,hd,rfl⟩
      rw [hdmap] at hd'
      exact E.injective ((Submodule.disjoint_def.mp hdis _ hv' hd').trans E.map_zero.symm)
    have hdim : Module.finrank (ZMod 2) (fixedSpace σ ⊤) ≤ 1 := by
      rw [←LinearEquiv.finrank_map_eq E (fixedSpace σ ⊤), hfix]
      exact core_fixed_finrank
    exact attachment_saturation H _ _ hne hdis' halign hdim
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.AttachmentModel

open Theory.GroupTheory Representation.NormalElementaryQuotient
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h e hz hk in
private theorem terminal_cover_attachment_saturation
    (A B : Subgroup M) (hne : ¬ A ≤ extensionKernel h)
    (hindex : (centralizer (A : Set M)).relIndex W₀ ≤ 2)
    (hBA : B ≤ centralizer (A : Set M))
    (hHne : ⁅W₀ ⊓ centralizer (A : Set M),B⁆ ≠ ⊥)
    (halign : ⁅W₀ ⊓ centralizer (A : Set M),B⁆ ≤ ⁅W₀,A⁆ ⊔ (W₀ ⊓ center M)) :
    W₀ ⊓ center M ≤ ⁅W₀ ⊓ centralizer (A : Set M),B⁆ ⊔ ⁅W₀,A⁆ := by
  let := h.relative_normal
  let U := W₀
  let F := U ⊓ centralizer (A : Set M)
  let H := ⁅F,B⁆
  have hHU : H ≤ U := (commutator_mono inf_le_left le_rfl).trans (commutator_le_left U B)
  have hker := CubicAction.moved_projection_kernel h e hz hk
  have hsmall : fixedCodim (coverAction h e hz hk) (A.map π) ≤ 1 := by
    rw [centralizer_index_eq_fixedCodim U π (CubicEven.projection_surjective h e hz hk) hker] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction h e hz hk) (naturalRepresentation (Fin 6))
      (coverMap h e hz hk) (coverMap_surjective h e hz hk)
      (coverMap_equivariant h e hz hk) (A.map π)).trans hsmall
  have hnA : A.map π ≠ ⊥ := by
    intro he
    exact hne ((CubicAction.projection_kernel h e hz hk) ▸ (map_eq_bot_iff A).mp he)
  obtain ⟨t,ht,hs,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers (A.map π) hnA hnat
  have hF : subgroupSpace U F = fixedSpace (coverAction h e hz hk) (A.map π) := by
    ext v
    change ((v.toMul : M) ∈ U ∧ (v.toMul : M) ∈ centralizer (A : Set M)) ↔ _
    simp only [v.toMul.property,true_and]
    exact (mem_fixedSpace_image U π (CubicEven.projection_surjective h e hz hk) hker A v).symm
  have hH : subgroupSpace U H = subspaceCommutator (coverAction h e hz hk)
      (fixedSpace (coverAction h e hz hk) (A.map π)) (B.map π) := by
    rw [subgroupSpace_commutator U π (CubicEven.projection_surjective h e hz hk) hker F B inf_le_left,hF]
  have hU : subgroupSpace U U = ⊤ := by ext v; exact iff_of_true v.toMul.property trivial
  have hC : subgroupSpace U (U ⊓ center M) = fixedSpace (coverAction h e hz hk) ⊤ := by
    ext v
    have hh := mem_fixedSpace_image U π (CubicEven.projection_surjective h e hz hk) hker (⊤ : Subgroup M) v
    rw [map_top_of_surjective π (CubicEven.projection_surjective h e hz hk),coe_top,centralizer_univ] at hh
    change ((v.toMul : M) ∈ U ∧ (v.toMul : M) ∈ center M) ↔ _
    simp only [v.toMul.property,true_and]
    exact hh.symm
  have hD : subgroupSpace U ⁅U,A⁆ = subspaceCommutator (coverAction h e hz hk) ⊤ (A.map π) := by
    rw [subgroupSpace_commutator U π (CubicEven.projection_surjective h e hz hk) hker U A le_rfl,hU]
  have hnH : subgroupSpace U H ≠ ⊥ := by
    intro hzH
    apply hHne
    apply le_bot_iff.mp
    intro v hv
    have hv' : Additive.ofMul (⟨v,hHU hv⟩ : U) ∈ subgroupSpace U H := hv
    rw [hzH] at hv'
    exact congrArg (fun w : Additive U => (w.toMul : M)) hv'
  have hP : B.map π ≤ centralizer ({t} : Set S) := by
    rintro _ ⟨b,hb,rfl⟩ x rfl
    obtain ⟨a,ha,rfl⟩ := ht
    simpa only [map_mul] using congrArg π (hBA hb a ha)
  have ha : subgroupSpace U H ≤
      subspaceCommutator (coverAction h e hz hk) ⊤ (zpowers t) ⊔ fixedSpace (coverAction h e hz hk) ⊤ := by
    rw [←he,←hD,←hC,←subgroupSpace_sup U (commutator_le_left U A) inf_le_left]
    exact fun _ hv => halign hv
  have hh := AttachmentModel.cover_attachment_saturation (coverAction h e hz hk)
    (moved_subgroup_cover_model h e hz hk) t hs (B.map π) hP (subgroupSpace U H) hnH
    (by rw [←he,←hH]) ha
  rw [←he,←hD,←hC,←subgroupSpace_sup U hHU (commutator_le_left U A)] at hh
  intro v hv
  exact hh (show Additive.ofMul (⟨v,hv.1⟩ : U) ∈ subgroupSpace U (U ⊓ center M) from hv)

include h e hz hk in
/-- A nonzero aligned full critical-kernel commutator spans the entire
moving central attachment together with the critical line. The actor
centralizes the opposite seed and lies in the literal first edge. -/
theorem borel_critical_attachment_saturation
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (Y : Subgroup (FreeAmalgam Rg))
    (hYT : Y ≤ Q Rg (p.walk.getVert 1))
    (hYA : Y ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)))
    (hne : ⁅Z Rg a ⊓ Q Rg z,Y⁆ ≠ ⊥)
    (halign : ⁅Z Rg a ⊓ Q Rg z,Y⁆ ≤ ⁅Z Rg a,Z Rg z⁆ ⊔
      (U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))) :
    U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) ≤
      ⁅Z Rg a ⊓ Q Rg z,Y⁆ ⊔ ⁅Z Rg a,Z Rg z⁆ := by
  let := h.relative_normal
  have hl : 0 < p.walk.length := p.length_eq_b ▸ sourceDistance_pos h
  have hat : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hAT : Z Rg z ≤ Q Rg (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt Rg z ((sourceGeometry h).exists_critical z p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(sourceGeometry h).distance_constant _ p.end_color]
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    change p.walk.length-1 < sourceDistance h
    omega
  have hAG : Z Rg z ≤ stabilizer Rg a :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      p.critical
  have hYG : Y ≤ stabilizer Rg a := hYT.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hat))
  have hfixed : ⁅U Rg a ⊓ centralizer (Z Rg z : Set (FreeAmalgam Rg)),Y⁆ =
      ⁅Z Rg a ⊓ Q Rg z,Y⁆ := by
    rw [←critical_seed_centralizer_intersection h e p]
    exact (full_fixed_seed_edge_commutator (h := h) (e := e) (hz := hz)
      p.start_color hat (Z Rg z) hAT Y hYT).symm
  obtain ⟨i,hi,hir,hiQ,hiE,hiU,_⟩ := graph_cover h e hz hk a p.start_color
  let A := (Z Rg z).comap i
  let B := Y.comap i
  have hmA : A.map i = Z Rg z := map_comap_eq_self (hAG.trans_eq hir.symm)
  have hmB : B.map i = Y := map_comap_eq_self (hYG.trans_eq hir.symm)
  have hmC : (W₀ ⊓ center M).map i =
      U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
    have hh := map_inf_centralizer_of_injective i hi W₀ ⊤
    simpa only [←MonoidHom.range_eq_map,hir,hiU,coe_top,centralizer_univ] using hh.symm
  have hmH : (⁅W₀ ⊓ centralizer (A : Set M),B⁆).map i = ⁅Z Rg a ⊓ Q Rg z,Y⁆ := by
    rw [map_commutator,←map_inf_centralizer_of_injective i hi,hiU,hmA,hmB,hfixed]
  have hmD : (⁅W₀,A⁆).map i = ⁅Z Rg a,Z Rg z⁆ := by
    rw [map_commutator,hiU,hmA,small_critical_moving_commutator_eq h e hz hk p hp]
  have hnA : ¬ A ≤ extensionKernel h :=
    critical_comap_not_le_extension h e hz p i hi (hAG.trans_eq hir.symm) hiQ
  let := finite_Z Rg a
  let : Finite (U Rg a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg a)) (inclusion_injective _)
  have hCA : Q Rg z ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg z p.end_color))
  have hidx : (centralizer (A : Set M)).relIndex W₀ ≤ 2 := by
    rw [←inf_relIndex_right,inf_comm,←relIndex_map_map_of_injective _ _ hi,
      ←map_inf_centralizer_of_injective i hi,hiU,hmA,inf_relIndex_left]
    exact ((relIndex_le_of_le_left hCA index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg a) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk p hp).1
  have hBA : B ≤ centralizer (A : Set M) := by
    intro b hb a ha
    apply hi
    simpa only [map_mul] using hYA hb (i a) ha
  have hh := terminal_cover_attachment_saturation h e hz hk A B hnA hidx hBA
    (by intro hh; apply hne; rw [←hmH,hh,Subgroup.map_bot])
    (by
      apply (map_le_map_iff_of_injective hi).mp
      rwa [hmH,Subgroup.map_sup,hmD,hmC])
  have hm := map_mono (f := i) hh
  rwa [hmC,Subgroup.map_sup,hmH,hmD] at hm

include h e hz hk in
/-- In the nonnormalizing branch the common edge intersection is the
whole moving central attachment of the last shifted vertex. -/
theorem borel_three_shift_attachment_saturated
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path)
    (hnorm : ¬ Z Rg (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z Rg t.start ⊓ Q Rg (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z Rg r.start : Subgroup (FreeAmalgam Rg)) : Set _)) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let H := ⁅Z Rg t.start ⊓ Q Rg v,Z Rg z ⊓ Q Rg r.start⁆
    let D := ⁅Z Rg t.start,Z Rg v⁆
    (H ⊔ D) ⊓ Z Rg t.edge =
      U Rg t.start ⊓ centralizer (stabilizer Rg t.start : Set (FreeAmalgam Rg)) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let F := Z Rg z ⊓ Q Rg r.start
  let H := ⁅Z Rg t.start ⊓ Q Rg v,F⁆
  let D := ⁅Z Rg t.start,Z Rg v⁆
  let I := (H ⊔ D) ⊓ Z Rg t.edge
  let C := U Rg t.start ⊓ centralizer (stabilizer Rg t.start : Set (FreeAmalgam Rg))
  have ht := two_borel_backward_shifts_small_moving h e hz hk hb q.path r t
  have hs : (Q Rg v).relIndex (Z Rg t.start) < 4 := by rw [ht.2.1]; decide
  have hdata := borel_three_shift_kernel_intersection_central h e hz hk hb u hR p q r t
  have hdecomp := borel_three_shift_kernel_decomposition h e hz hk hb u hR p q r t
  have hIU := (borel_three_shift_attachment_transport h e hz hk hb u hR p q r t).1
  have hIC : I ≤ C := le_inf hIU hdecomp.2.2.1
  have halign : H ≤ D ⊔ C := le_sup_left.trans
    (hdecomp.1.le.trans (sup_le_sup_left hIC D))
  have htcol : color Rg t.edge = true := by
    have hh := adjacent_color_ne Rg t.adjacent_start
    rw [r.path.start_color] at hh
    cases he : color Rg t.edge
    · exact (hh he.symm).elim
    · rfl
  have hFT : F ≤ Q Rg (t.path.walk.getVert 1) := by
    rw [t.first]
    exact inf_le_right.trans (Q_le_adjacent_h Rg htcol t.adjacent_start)
  have hzv : (cosetGraph Rg).dist z v = 2 := by
    rw [SimpleGraph.dist_comm,r.path.dist_end]
    have hl : r.path.walk.length = sourceDistance h := r.path.length_eq_b
    omega
  have hFv : F ≤ Q Rg v := inf_le_left.trans (Z_le_Q_of_dist_lt Rg z
    ((sourceGeometry h).exists_critical z r.path.end_color) (by
      rw [(sourceGeometry h).distance_constant z r.path.end_color,hzv]
      change 2 < sourceDistance h
      omega))
  have hFA : F ≤ centralizer (Z Rg v : Set (FreeAmalgam Rg)) :=
    hFv.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg v t.path.end_color)))
  have hne : H ≠ ⊥ := by
    intro he
    have hc := (borel_three_shift_restricted_kernel h e hz hk hb u hR p q r t).2.2.2.2 hnorm |>.1
    change Nat.card H = 2 at hc
    rw [he,Subgroup.card_bot] at hc
    omega
  have hCH := borel_critical_attachment_saturation h e hz hk t.path hs F hFT hFA hne halign
  apply le_antisymm hIC
  exact (le_inf hCH (show C ≤ centralizer (stabilizer Rg t.start : Set (FreeAmalgam Rg)) from
    inf_le_right)).trans_eq hdata.2.2.2.2.1.symm

private theorem shift_attachment_eq
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : BorelBackwardShift (h := h) p)
    (I : Subgroup (FreeAmalgam Rg))
    (hIa : I ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))
    (heq : I = U Rg q.start ⊓ centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg))) :
    I = U Rg (p.walk.getVert 2) ⊓
      centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) := by
  have he : act Rg q.transporter⁻¹ q.start = p.walk.getVert 2 := by
    rw [←q.start_eq,←act_mul,mul_inv_cancel,act_one]
  have hf : I.map (MulAut.conj q.transporter).toMonoidHom = I :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hIa q.transporter_mem))
  have hh := congrArg (Subgroup.map (MulAut.conj q.transporter).toMonoidHom) heq
  rw [hf,←map_inf_centralizer_of_injective _ (MulAut.conj q.transporter).injective] at hh
  rw [←he,U_act,stabilizer_act,inv_inv]
  exact hh

include h e hz hk in
/-- At distance six the full reverse attachment is the same common edge
intersection. Consequently failure of endpoint normalization puts the
preceding critical line inside the last selected full seed. -/
theorem borel_six_attachment_saturated
    (hb : sourceDistance h = 6)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path)
    (hnorm : ¬ Z Rg (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z Rg t.start ⊓ Q Rg (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z Rg r.start : Subgroup (FreeAmalgam Rg)) : Set _)) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let H := ⁅Z Rg t.start ⊓ Q Rg v,Z Rg z ⊓ Q Rg r.start⁆
    let D := ⁅Z Rg t.start,Z Rg v⁆
    let I := (H ⊔ D) ⊓ Z Rg t.edge
    I = U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) ∧
      ⁅Z Rg r.start,Z Rg z⁆ ≤ Z Rg t.start := by
  have hb4 : 4 < sourceDistance h := by omega
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let H := ⁅Z Rg t.start ⊓ Q Rg v,Z Rg z ⊓ Q Rg r.start⁆
  let D := ⁅Z Rg t.start,Z Rg v⁆
  let I := (H ⊔ D) ⊓ Z Rg t.edge
  have hdata := borel_three_shift_kernel_intersection_central h e hz hk hb4 u hR p q r t
  have hIr : I ≤ centralizer (stabilizer Rg r.start : Set (FreeAmalgam Rg)) := hdata.2.2.1
  have hIa := (borel_three_shift_attachment_transport h e hz hk hb4 u hR p q r t).2.1
  have hsat := borel_three_shift_attachment_saturated h e hz hk hb4 u hR p q r t hnorm
  have hr2 : r.path.walk.getVert 2 = q.start := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using r.overlap 0 (Nat.zero_le _)
  have hq := shift_attachment_eq h r.path t I hIr hsat
  rw [hr2] at hq
  have hz2 : z = p.walk.getVert 2 := by
    have hlp : p.walk.length = 6 := p.length_eq_b.trans hb
    have hlq : q.path.walk.length = 6 := q.path.length_eq_b.trans hb
    dsimp only [z]
    rw [hlq]
    exact q.overlap 2 (by omega)
  have hzC := shift_attachment_eq h p q I hIa hq
  rw [←hz2] at hzC
  refine ⟨hzC,?_⟩
  have he := (borel_three_shift_nonnormalized_alignment h e hz hk hb4 u hR p q r t hnorm).2.2.2
  have hDH : ⁅Z Rg r.start,Z Rg z⁆ ≤ H ⊔ I := by
    rw [hzC,he]
    exact le_sup_left
  exact hDH.trans (sup_le (le_sup_left.trans hdata.2.1) (inf_le_left.trans hdata.2.1))

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
