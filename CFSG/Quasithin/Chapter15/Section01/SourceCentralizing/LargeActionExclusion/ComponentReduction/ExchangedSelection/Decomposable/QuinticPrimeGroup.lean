module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticActor
public import Theory.GroupTheory.PResidual.PermutingNormalPrimeLift
public import Theory.GroupTheory.Commutator.FixedSeedKernel
/-!
# The actual prime-five actor on the original moving support

Lift the normal order-five image in the marked centralizer to a five-group
Y permuting with its prescribed Sylow two-subgroup S. Equal images through
the original action preserve both sixteen-element supports, irreducibility,
and [V₂,Y]=V₂. The lift lies in the canonical prime-to-five residual; neither
that residual nor the full two-residual is asserted to be a five-group.

For the same component and pre-exclusion witness, the kernel of V₂ acting
on L is invariant under the canonical quintic actor. Irreducibility and
original component noncentrality make it trivial, giving the literal
sixteen-element automorphism image. The parent Decomposable consumer applies
both results to the original eight-dimensional action. Constructing the
prime-five component marker, including the ambient order-fifteen exclusion,
and the subsequent model exclusions remain necessary for final assembly.

Source: Aschbacher--Smith 15.1.16(a), 15.1.19(7), and 15.1.23,
printed pp.1092,1094,1100.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem geometry_of_same_image
    (M V Y A : Subgroup G) (hn : M ≤ normalizer (V : Set G))
    (hVM : V ≤ M) (hYM : Y ≤ M) (hAM : A ≤ M) (hYA : Y ≤ A)
    (him : (Y.subgroupOf M).map (actionHom M V hn).rangeRestrict =
      (A.subgroupOf M).map (actionHom M V hn).rangeRestrict) :
    V ⊓ centralizer (Y : Set G) = V ⊓ centralizer (A : Set G) ∧
      (∀ D : Subgroup G, D ≤ V → ⁅D,Y⁆ = ⁅D,A⁆) ∧
      ∀ D : Subgroup G, D ≤ V →
        (Y ≤ normalizer (D : Set G) ↔ A ≤ normalizer (D : Set G)) := by
  let f := (actionHom M V hn).rangeRestrict
  have hpre : A.subgroupOf M ≤ Y.subgroupOf M ⊔ f.ker := by
    rw [←comap_map_eq]
    exact map_le_iff_le_comap.mp him.ge
  have hjoin : A ≤ Y ⊔ centralizer (V : Set G) := by
    have hh := map_mono hpre (f := M.subtype)
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAM,
      map_subgroupOf_eq_of_le hYM] at hh
    apply hh.trans
    apply sup_le_sup_left
    rintro x ⟨y,hy,rfl⟩
    change y ∈ (actionHom M V hn).rangeRestrict.ker at hy
    rwa [MonoidHom.ker_rangeRestrict,actionHom_ker] at hy
  refine ⟨?_,?_,?_⟩
  · apply le_antisymm ?_ (inf_le_inf_left _ (centralizer_le hYA))
    apply le_inf inf_le_left
    apply le_centralizer_iff.mpr
    exact hjoin.trans (sup_le (le_centralizer_iff.mp inf_le_right)
      (centralizer_le inf_le_left))
  · intro D hDV
    have hk : f.ker ≤ centralizer (V.subgroupOf M : Set M) := by
      intro x hx v hv
      change x ∈ (actionHom M V hn).rangeRestrict.ker at hx
      rw [MonoidHom.ker_rangeRestrict,actionHom_ker] at hx
      exact Subtype.ext (hx v hv)
    have he := congrArg (map M.subtype)
      (commutator_eq_of_centralizing_kernel (V.subgroupOf M) (D.subgroupOf M)
        (Y.subgroupOf M) (A.subgroupOf M) f hk (subgroupOf_mono M hDV) him)
    simpa only [map_commutator,map_subgroupOf_eq_of_le hYM,
      map_subgroupOf_eq_of_le hAM,map_subgroupOf_eq_of_le (hDV.trans hVM)] using he
  · intro D hDV
    exact ⟨fun hy => hjoin.trans (sup_le hy
      ((centralizer_le hDV).trans (Subgroup.centralizer_le_normalizer _))),
      fun ha => hYA.trans ha⟩

/-- A genuine five-group on the original support, permuting with the original
marked Sylow centralizer, without assuming that the full two-residual is a five-group. -/
theorem ThompsonPair.exists_permuting_quintic_actor
    {T : Sylow 2 G}
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (hVM : V ≤ M)
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
        Jhat (imageRepresentation M V hn))
    (hfive : s.prime = 5) :
    let Z := thompsonPlane T V (c.ambientFactor d s.first).space
    let C := M ⊓ centralizer (Z : Set G)
    let S := (T : Subgroup G) ⊓ centralizer (Z : Set G)
    let B := plane V (c.ambientFactor d s.second).space
    ∃ Y : Subgroup G, IsPGroup 5 Y ∧ IsPPerfect 2 Y ∧
      Y ≤ (primeToResidual 5 C).map C.subtype ∧
      (S : Set G) * (Y : Set G) = (Y : Set G) * (S : Set G) ∧
      (Y.subgroupOf M).map (actionHom M V hn).rangeRestrict =
        (s.marking s.second).kernel.map (c.ambientFactor d s.second).embedding.groupMap ∧
      V ⊓ centralizer (Y : Set G) = plane V (c.ambientFactor d s.first).space ∧
      ⁅V,Y⁆ = B ∧ ⁅B,Y⁆ = B ∧
      (∀ D : Subgroup G, D ≤ B → Y ≤ normalizer (D : Set G) → D = ⊥ ∨ D = B) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro Z C S B
  let ρ := imageRepresentation M V hn
  let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
    (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict)
  let K := subspaceKernel ρ W ⊤
  let P := primeToResidual 5 K
  let A := (primeToResidual 5 C).map C.subtype
  have hW : plane V W = Z := plane_thompson_intersection hTM hn _
  have hprojection : ∃ q : C →* K, Function.Surjective q ∧
      ∀ x : C, (q x : internalActionImage M V hn) =
        (actionHom M V hn).rangeRestrict ⟨x,x.property.1⟩ := by
    obtain ⟨q,hq,_,hcoord⟩ := ExtraspecialMarker.stabilizer_projection M V hn W
    let eC : C ≃* (M ⊓ centralizer (plane V W : Set G) : Subgroup G) :=
      MulEquiv.subgroupCongr (congrArg (fun D : Subgroup G => M ⊓ centralizer (D : Set G)) hW.symm)
    exact ⟨q.comp eC.toMonoidHom,hq.comp eC.surjective,fun x => hcoord (eC x)⟩
  obtain ⟨q,hq,hcoord⟩ := hprojection
  have hP : Nat.card P = 5 := by
    rw [←card_map_of_injective (K := P) K.subtype_injective,
      s.full_image_quintic_residual hTM hn c d π hp hs hJ hfive,
      s.kernel_card,hfive]
  obtain ⟨SC,hSC⟩ := s.local_sylow hTM hn c d π hs
  obtain ⟨Y0,hY0,hperf,hperm,him,hYR⟩ :=
    exists_permuting_normal_prime_lift q hq SC (by decide : 5 ≠ 2) P hP
  let Y := Y0.map C.subtype
  have hYA : Y ≤ A := by
    apply map_mono
    intro y hy
    obtain ⟨n,hn⟩ := hY0 (⟨y,hy⟩ : Y0)
    apply mem_primeToResidual_of_pow (n := n)
    exact congrArg Subtype.val hn
  have hAM : A ≤ M := (map_subtype_le _).trans inf_le_left
  have hYM : Y ≤ M := hYA.trans hAM
  have hSY : (S : Set G) * (Y : Set G) = (Y : Set G) * (S : Set G) := by
    have he := congrArg (Set.image C.subtype) hperm
    rw [Set.image_mul,Set.image_mul] at he
    change ((SC : Subgroup C).map C.subtype : Set G) * (Y : Set G) =
      (Y : Set G) * ((SC : Subgroup C).map C.subtype : Set G) at he
    rwa [hSC] at he
  let f := (actionHom M V hn).rangeRestrict
  have hYim : (Y.subgroupOf M).map f = P.map K.subtype := by
    rw [←him,map_map]
    ext x
    constructor
    · rintro ⟨y,⟨y0,hy0,he⟩,rfl⟩
      exact ⟨y0,hy0,(hcoord y0).trans (congrArg f (Subtype.ext he))⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,y.property.1⟩,mem_map_of_mem C.subtype hy,(hcoord y).symm⟩
  have hYkernel : (Y.subgroupOf M).map f =
      (s.marking s.second).kernel.map (c.ambientFactor d s.second).embedding.groupMap :=
    hYim.trans (s.full_image_quintic_residual hTM hn c d π hp hs hJ hfive)
  obtain ⟨hAim,hfix,hmove,_,_,_,_,_⟩ := s.quintic_actor_geometry hTM hn c d π hp hs hJ hfive
  have hsame : (Y.subgroupOf M).map f = (A.subgroupOf M).map f := hYkernel.trans hAim.symm
  obtain ⟨hfixed,hcomm,hnorm⟩ := geometry_of_same_image M V Y A hn hVM hYM hAM hYA hsame
  refine ⟨Y,hY0.map C.subtype,
    hperf.of_surjective (C.subtype.subgroupMap Y0) (C.subtype.subgroupMap_surjective Y0),
    hYA,hSY,hYkernel,hfixed.trans hfix,(hcomm V le_rfl).trans hmove,?_,?_⟩
  · exact (hcomm B (plane_le _)).trans
      (s.quintic_actor_moves_support hTM hn c d π hp hs hJ hfive)
  · intro D hDB hYD
    exact s.quintic_actor_irreducible hTM hn c d π hp hs hJ hfive D hDB
      ((hnorm D (hDB.trans (plane_le _))).mp hYD)
end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker

namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- Irreducibility makes the same original moving support faithful on the
selected component. The pre-exclusion witness is used only for normalization
and noncentrality; no quotient model or later index conclusion is assumed. -/
theorem ThompsonPair.quintic_moving_support_faithful_on_component
    {T : Sylow 2 G}
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
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
        Jhat (imageRepresentation M V hn))
    (hfive : s.prime = 5)
    {Mc : Subgroup G} (e : CaseIComponentData T M Mc V)
    (hZ : e.Z1 = thompsonPlane T V (c.ambientFactor d s.first).space)
    (hpre : e.PreExclusionSource hn 5) :
    let B := plane V (c.ambientFactor d s.second).space
    ∃ hBL : B ≤ normalizer (e.L : Set G),
      Function.Injective (actionHom B e.L hBL) ∧
      Nat.card (internalActionImage B e.L hBL) = 16 := by
  intro B
  let Z := thompsonPlane T V (c.ambientFactor d s.first).space
  let C := M ⊓ centralizer (Z : Set G)
  let R := (pResidual 2 C).map C.subtype
  let A := (primeToResidual 5 C).map C.subtype
  have hmove : ⁅V,R⁆ = B := (s.full_residual_geometry hTM hn c d π hp hs hJ).2.1
  have hnL : R ⊔ B ≤ normalizer (e.L : Set G) := by
    have hh := hpre.residual_normalizes
    change (pResidual 2 (M ⊓ centralizer (e.Z1 : Set G) : Subgroup G)).map
        (M ⊓ centralizer (e.Z1 : Set G)).subtype ⊔
      ⁅V,(pResidual 2 (M ⊓ centralizer (e.Z1 : Set G) : Subgroup G)).map
        (M ⊓ centralizer (e.Z1 : Set G)).subtype⁆ ≤ _ at hh
    rw [hZ] at hh
    change R ⊔ ⁅V,R⁆ ≤ _ at hh
    rwa [hmove] at hh
  have hnon : ⁅e.L,B⁆ ≠ ⊥ := by
    have hh := hpre.moving_noncentral
    change ⁅e.L,⁅V,(pResidual 2 (M ⊓ centralizer (e.Z1 : Set G) : Subgroup G)).map
      (M ⊓ centralizer (e.Z1 : Set G)).subtype⁆⁆ ≠ ⊥ at hh
    rw [hZ] at hh
    change ⁅e.L,⁅V,R⁆⁆ ≠ ⊥ at hh
    rwa [hmove] at hh
  obtain ⟨_,_,hAmove,_,_,_,_,hAR⟩ := s.quintic_actor_geometry hTM hn c d π hp hs hJ hfive
  have hAB : A ≤ normalizer (B : Set G) := by
    change A ≤ normalizer (plane V (c.ambientFactor d s.second).space : Set G)
    rw [←hAmove]
    exact normalizer_commutator_ge_right V A
  have hAL : A ≤ normalizer (e.L : Set G) := hAR.trans (le_sup_left.trans hnL)
  have hbot : B ⊓ centralizer (e.L : Set G) = ⊥ := by
    rcases s.quintic_actor_irreducible hTM hn c d π hp hs hJ hfive
        (B ⊓ centralizer (e.L : Set G)) inf_le_left
        (le_normalizer_inf hAB (hAL.trans (normalizer_le_normalizer_centralizer _))) with hz | he
    · exact hz
    · exact False.elim (hnon (by
        rw [commutator_comm]
        exact commutator_eq_bot_iff_le_centralizer.mpr (he.symm.le.trans inf_le_right)))
  have hBL : B ≤ normalizer (e.L : Set G) := le_sup_right.trans hnL
  have hfaith : Function.Injective (actionHom B e.L hBL) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [actionHom_ker]
    apply bot_unique
    intro x hx
    have hh : (x : G) ∈ B ⊓ centralizer (e.L : Set G) := ⟨x.property,hx⟩
    rw [hbot] at hh
    exact Subtype.ext (mem_bot.mp hh)
  exact ⟨hBL,hfaith,(Nat.card_range_of_injective hfaith).trans (s.support_card s.second)⟩
end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
