module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallActionKernel
public import Theory.Representation.PSL3Two.WreathCubicModule
public import Theory.GroupTheory.CoprimeCentralizerCard

/-!
# The original module inside the collapsed containing radical

The literal natural coordinates identify V with a group of order sixty-four.
Its original cubic complement P maps injectively to a cubic plane in the
wreath actor. The concrete fixed-space calculation gives |C_V(P)|=4;
coprime splitting gives |[V,P]|=16. Relative normality of O²(H) in H
places this same moved subgroup in O₂(O²(H)). Thus under the remaining
collapse it lies in V∩O₂(K), with K=<O²(H)^E> and E=<N_G(T₁),H>.

The original fixed subgroup supplements V∩O₂(K), and that intersection
has index at most four in V. These statements retain the original module,
complement, exchanger and core maps. The final application constructs all
coordinates from the original source guards and narrows both literal
source contracts without adding a premise.

This module does not exclude the remaining configuration. Its exclusion
and assembly of StabilizerNormalizerAt and HalfSylowUniqueAt remain with
qt-d-10-nona5-half-sylow-unique. Only ModuleChoiceAt is external; its final
discharge remains with qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 10.2.4--6, printed pp.747--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding Parabolics
open SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

/-- The actual full module in the zero-kernel natural branch has order sixty-four. -/
theorem NaturalData.full_card (s : NaturalData D) : Nat.card D.fullModule = 64 := by
  rw [Nat.card_congr (fullCoordinates s s.fixed_zero).toEquiv,Nat.card_fun]
  change Nat.card (Fin 3 → ZMod 2) ^ Nat.card (ZMod 2) = 64
  rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  norm_num

/-- The original cubic complement fixes precisely four elements of the original full module. -/
theorem LiftData.cubic_fixed_card (f : LiftData s hz) {P : Subgroup G}
    (hPJ : P ≤ localJoin T L) (hp : IsPGroup 3 P) (hP : Nat.card P = 9) :
    Nat.card (D.fullModule ⊓ centralizer (P : Set G) : Subgroup G) = 4 := by
  let J := localJoin T L
  let A := P.subgroupOf J
  let B := A.map f.hom
  have ha : IsPGroup 3 A := hp.of_equiv (subgroupOfEquivOfLe hPJ).symm
  have hd := ha.disjoint_of_coprime f.kernel_two (by decide : Nat.Coprime 3 2)
  have hi : Function.Injective (f.hom.subgroupMap A) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    change f.hom.subgroupMap A x = 1 at hx
    exact Subtype.ext (hd.le_bot ⟨x.property,congrArg Subtype.val hx⟩)
  have hB : Nat.card B = 9 := by
    rw [←Nat.card_congr (MulEquiv.ofBijective (f.hom.subgroupMap A)
      ⟨hi,f.hom.subgroupMap_surjective A⟩).toEquiv]
    exact (Nat.card_congr (subgroupOfEquivOfLe hPJ).toEquiv).trans hP
  let c := fullCoordinates s hz
  have hfix (v : D.fullModule) :
      (v : G) ∈ centralizer (P : Set G) ↔ ∀ a ∈ B, action a (c v) = c v := by
    constructor
    · intro hv a ha
      obtain ⟨x,hx,rfl⟩ := ha
      rw [←f.equivariant]
      apply congrArg c
      apply Subtype.ext
      rw [joinAction_apply,(mem_centralizer_iff.mp hv) x hx,mul_inv_cancel_right]
    · intro hv
      rw [mem_centralizer_iff]
      intro p hp
      let x : J := ⟨p,hPJ hp⟩
      have he := hv (f.hom x) (mem_map_of_mem f.hom (show x ∈ A from hp))
      rw [←f.equivariant] at he
      have he' := congrArg Subtype.val (c.injective he)
      change p * (v:G) * p⁻¹ = (v:G) at he'
      exact mul_inv_eq_iff_eq_mul.mp he'
  let e : (D.fullModule ⊓ centralizer (P : Set G) : Subgroup G) ≃
      {w : Space // ∀ a ∈ B, action a w = w} := {
    toFun v := ⟨c ⟨v,v.property.1⟩,(hfix _).mp v.property.2⟩
    invFun w := ⟨c.symm w, (c.symm w).property, (hfix _).mpr (by simpa using w.property)⟩
    left_inv v := by
      apply Subtype.ext
      change ((c.symm (c ⟨v,v.property.1⟩) : D.fullModule) : G) = v
      rw [c.symm_apply_apply]
    right_inv w := by apply Subtype.ext; exact c.apply_symm_apply _ }
  rw [Nat.card_congr e]
  exact Matrix.PSL3Two.WreathCubicModule.cubic_fixed_card action action_apply B hB

/-- Coprime splitting gives the exact size of the moved subgroup, on the original carriers. -/
theorem LiftData.cubic_moved_card (f : LiftData s hz) {P : Subgroup G}
    (hPJ : P ≤ localJoin T L) (hp : IsPGroup 3 P) (hP : Nat.card P = 9) :
    Nat.card (⁅D.fullModule,P⁆ : Subgroup G) = 16 := by
  let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  have hn : P ≤ normalizer (D.fullModule : Set G) := by
    rw [s.full_eq_local]
    exact hPJ.trans D.join_normalizes_module
  have hh := commutator_card_mul_centralizer_card D.fullModule P hn
    (by rw [hP,s.full_card]; decide)
  rw [f.cubic_fixed_card hPJ hp hP,s.full_card] at hh
  omega

namespace Parabolics
variable {H P : Subgroup G}

/-- Movement of the original module by the complement lies in the original residual core. -/
theorem Data.cubic_module_moved_le_residual_core (h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H)) :
    ⁅D.fullModule,P⁆ ≤ (residual H).pCoreIn 2 := by
  have hVH : D.fullModule ≤ H := by
    rw [hfull]
    exact D.module_le_core.trans ((join_core_le_stabilizer D).trans (inf_le_left.trans h.sylow_le))
  have hnorm : P ≤ normalizer (D.fullModule : Set G) := by
    rw [hfull]
    exact (hi.complement_le.trans ((map_subtype_le _).trans h.le_join)).trans D.join_normalizes_module
  have hVX : ⁅D.fullModule,P⁆ ≤ residual H :=
    (commutator_mono le_rfl hi.complement_le).trans
      (le_normalizer_iff_commutator_le_right.mp (hVH.trans (le_normalizer_embedded_pResidual 2 H)))
  have hVQ : D.fullModule ≤ H.pCoreIn 2 := by
    rw [hfull]
    apply D.module_le_core.trans
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
      ((join_core_le_stabilizer D).trans (inf_le_left.trans h.sylow_le))
      (h.le_join.trans ((localJoin T L).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))))
  exact (le_inf hVX ((le_normalizer_iff_commutator_le_left.mp hnorm).trans hVQ)).trans
    (inf_pCoreIn_le_of_le 2 (map_subtype_le _))

/-- The containing core contains the actual sixteen-element moved subgroup under collapse. -/
theorem Data.collapsed_cubic_module (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    Nat.card (⁅D.fullModule,P⁆ : Subgroup G) = 16 ∧
      ⁅D.fullModule,P⁆ ≤ D.fullModule ⊓ (enlargedResidual T L H).pCoreIn 2 ∧
      16 ≤ Nat.card (D.fullModule ⊓ (enlargedResidual T L H).pCoreIn 2 : Subgroup G) := by
  have hPJ := hi.complement_le.trans ((map_subtype_le _).trans h.le_join)
  have hm := f.cubic_moved_card hPJ hi.odd_complement.isPGroup hP
  have hn : P ≤ normalizer (D.fullModule : Set G) := by
    rw [s.full_eq_local]
    exact hPJ.trans D.join_normalizes_module
  have hle := le_inf (le_normalizer_iff_commutator_le_left.mp hn)
    ((h.cubic_module_moved_le_residual_core s.full_eq_local hi).trans hc)
  exact ⟨hm,hle,hm ▸ Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)⟩

/-- Only a quotient of the four-element cubic fixed subgroup can survive outside the containing core. -/
theorem Data.collapsed_module_fixed_supplement (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    D.fullModule =
      (D.fullModule ⊓ (enlargedResidual T L H).pCoreIn 2) ⊔
        (D.fullModule ⊓ centralizer (P : Set G)) ∧
      (D.fullModule ⊓ (enlargedResidual T L H).pCoreIn 2).relIndex D.fullModule ≤ 4 := by
  let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  have hPJ := hi.complement_le.trans ((map_subtype_le _).trans h.le_join)
  have hn : P ≤ normalizer (D.fullModule : Set G) := by
    rw [s.full_eq_local]
    exact hPJ.trans D.join_normalizes_module
  have hdecomp := eq_commutator_sup_centralizer_of_solvable_coprime D.fullModule P hn
    (Group.isSolvable_of_comm fun x y => mul_comm x y) (by rw [hP,s.full_card]; decide)
  obtain ⟨hm,hle,hsize⟩ := h.collapsed_cubic_module f hi hP hc
  refine ⟨le_antisymm (hdecomp.le.trans (sup_le_sup_right hle _))
    (sup_le inf_le_left inf_le_left),?_⟩
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G)
    (D.fullModule ⊓ (enlargedResidual T L H).pCoreIn 2) D.fullModule bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,s.full_card] at hh
  nlinarith

end Parabolics
end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding BinaryThreeAction BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual source obstruction contains a sixteen-element piece of the original
module in its containing radical, with the same cubic complement and quotient. -/
theorem SourceCubicNormalizerEnlargement.exists_cubic_module
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ (H P I : Subgroup G) (p : ℕ), Data D H ∧
      SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
        (residual H) P (enlargement T L H) I ∧
      enlargedResidual T L H = componentOrbit I (T : Subgroup G) ∧
      p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient I) 2 p ∧
      (p % 24 = 11 ∨ p % 24 = 13) ∧
      (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2 ∧
      Nat.card D.fullModule = 64 ∧
      Nat.card (D.fullModule ⊓ centralizer (P : Set G) : Subgroup G) = 4 ∧
      Nat.card (⁅D.fullModule,P⁆ : Subgroup G) = 16 ∧
      ⁅D.fullModule,P⁆ ≤ D.fullModule ⊓ (enlargedResidual T L H).pCoreIn 2 ∧
      D.fullModule = (D.fullModule ⊓ (enlargedResidual T L H).pCoreIn 2) ⊔
        (D.fullModule ⊓ centralizer (P : Set G)) ∧
      (D.fullModule ⊓ (enlargedResidual T L H).pCoreIn 2).relIndex D.fullModule ≤ 4 := by
  obtain ⟨_,_,hfull,hn,_,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,hmod,h24,_,_,_,hcollapse⟩ := hc
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hcross := Selection.ModuleChoice.crossed_of_local_thompson D (hfull ▸ hJ) ht htn
  obtain ⟨s,_⟩ := exists_naturalData D hmodel hzero hfull ht htn hcross
  let f := originalLift s s.fixed_zero
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hP := (hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))).2
  obtain ⟨hmoved,hle,_⟩ := h.collapsed_cubic_module f hs.toLocalInput hP hcollapse
  exact ⟨H,P,I,p,h,hs,hK,hp,ho,hm,h24,hcollapse,s.full_card,
    f.cubic_fixed_card (hs.toLocalInput.complement_le.trans ((map_subtype_le _).trans h.le_join))
      hs.toLocalInput.odd_complement.isPGroup hP,hmoved,hle,
    h.collapsed_module_fixed_supplement f hs.toLocalInput hP hcollapse⟩

/-- Both literal source contracts reduce to the same obstruction with its original
module almost contained in the containing two-core. No additional source premise is added. -/
theorem sourceContracts_or_cubicModuleInCore (hchoice : Selection.ModuleChoiceAt T) :
    (StabilizerNormalizerAt T ∧ HalfSylowUniqueAt T) ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        SourceCubicNormalizerEnlargement D ∧
        ∃ H P : Subgroup G, Data D H ∧
          LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H) ∧
          Nat.card (⁅D.fullModule,P⁆ : Subgroup G) = 16 ∧
          ⁅D.fullModule,P⁆ ≤ D.fullModule ⊓ (enlargedResidual T L H).pCoreIn 2 ∧
          (D.fullModule ⊓ (enlargedResidual T L H).pCoreIn 2).relIndex D.fullModule ≤ 4 := by
  rcases sourceContracts_or_cubicNormalizerEnlargement hchoice with hh | ⟨L,D,hc⟩
  · exact Or.inl hh
  · obtain ⟨H,P,I,p,h,hs,_,_,_,_,_,_,_,_,hcard,hle,_,hindex⟩ := hc.exists_cubic_module
    exact Or.inr ⟨L,D,hc,H,P,h,hs.toLocalInput,hcard,hle,hindex⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
