module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityKernelD45
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityDefs
public import Theory.GroupTheory.NormalModuleCore
public import Theory.GroupTheory.IndexTwoFixedSylowComplement
public import Theory.GroupTheory.TwoPerfectElementaryIndexTwo
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Hyperplane normalizers and the residual action in 12.2.25

The full kernel on V inside LT is a two-group. The pointwise fixer of the
index-two subgroup U∩V in V is also a two-group. Its preimage in LT is
normalized by T and therefore lies in T. This identifies C_T(U∩V) with
the full centralizer inside LT, proving its invariance under N_L(U∩V).

In dimensions four and five the previous decompositions make R=C_T(U)
elementary of index two in this non-elementary group. A two-perfect group
normalizing a finite non-elementary group fixes its elementary index-two
subgroups. Applied to the literal Y=O²(N_L(U∩V)), this proves Y≤N_G(R).
This replaces the source's Thompson-subgroup calculation at the exact
normalization interface.

The final conditional record application consumes all established fields.
Its Sylow-factor disjointness premise and the dimension-three branch remain
with qt-d-12225-common-centralizers. Final source-theorem assembly belongs
to qt-d-12213-local-rigidity; no completion of 12.2.25 is asserted here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
original 12.2.25, printed pp.804–805.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}
namespace RigidityKernel

omit [Finite G] in
private theorem hyperplane_index'
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    (U ⊓ V : Subgroup G).relIndex V = 2 := by
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (U ⊓ V) V bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, C.hyperplane, chosen_card A] at hh
  have hd : d = d - 1 + 1 := by have := A.dimension.1; omega
  have hc : 2 ^ d = 2 * 2 ^ (d - 1) := by
    calc
      2 ^ d = 2 ^ (d - 1 + 1) := congrArg (fun n : ℕ => 2 ^ n) hd
      _ = _ := by rw [pow_succ, Nat.mul_comm]
  rw [hc] at hh
  have hp : 0 < 2 ^ (d - 1) := pow_pos (by decide) _
  nlinarith

/-- The full kernel inside LT is the same literal two-core as C_T(V). -/
theorem local_join_kernel
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  have hc : L ⊓ centralizer (V : Set G) = L.pCoreIn 2 := by
    have hm := congrArg (map L.subtype) C.block.2.1.centralizer_blockU
    rw [map_centralizer_subtype, LiteralNaturalBlock.blockLayer_eq D A C] at hm
    exact hm
  rw [ambient_centralizer_eq_core_of_normal_supplement L V (T : Subgroup G)
    D.sylow_normalizes_component (D.le_component.trans le_sup_left)
    (sup_le D.normalizes (((structural G T L h).2.2 V D).1)) T.isPGroup' hc D.core_centralizes,
    LiteralNaturalBlock.kernel_eq_local_core D A C]

/-- The full pointwise hyperplane stabilizer inside LT is a two-group,
so it equals the centralizer in the original Sylow subgroup. -/
theorem local_join_hyperplane_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    (L ⊔ (T : Subgroup G)) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G) =
      (T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G) := by
  let J := L ⊔ (T : Subgroup G)
  let W := U ⊓ V
  let K := J ⊓ centralizer (W : Set G)
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  have hTV := (((structural G T L h).2.2 V D).1)
  have hJV : J ≤ normalizer (V : Set G) := sup_le D.normalizes hTV
  let f : K →* MulAut V := V.normalizerMonoidHom.comp (inclusion (inf_le_left.trans hJV))
  let W' := W.subgroupOf V
  let F := fixingSubgroup (MulAut V) (W' : Set V)
  have hfix : f.range ≤ F := by
    rintro _ ⟨k,rfl⟩
    apply (mem_fixingSubgroup_iff (MulAut V)).mpr
    intro w hw
    apply Subtype.ext
    change (k : G) * (w : G) * (k : G)⁻¹ = w
    rw [← k.property.2 w hw, mul_inv_cancel_right]
  have hk : IsPGroup 2 f.ker := by
    apply (T.isPGroup'.to_le (show Q ≤ (T : Subgroup G) from inf_le_left)).comap_subtype.to_le
    intro k hk
    have hkc : (k : G) ∈ centralizer (V : Set G) := by
      have hh : (⟨k,(inf_le_left.trans hJV) k.property⟩ : normalizer (V : Set G)) ∈
          V.normalizerMonoidHom.ker := hk
      rw [normalizerMonoidHom_ker] at hh
      exact hh
    exact (local_join_kernel h D structural A C).le ⟨k.property.1,hkc⟩
  have hFp : IsPGroup 2 F := W'.isPGroup_fixingSubgroup_of_index_two
    (hyperplane_index' A C) ((T.isPGroup'.to_le (show W ≤ (T : Subgroup G) from inf_le_right.trans D.le_sylow)).comap_subtype)
  have hKp : IsPGroup 2 K := by
    have hp := hFp.comap_of_ker_isPGroup f hk
    have he : F.comap f = ⊤ := top_unique (fun k _ => hfix ⟨k,rfl⟩)
    rw [he] at hp
    exact hp.of_equiv Subgroup.topEquiv
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) :=
    (le_inf C.sylow_normalizes_core hTV).trans inf_normalizer_le_normalizer_inf
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (le_inf (le_sup_right.trans J.le_normalizer)
      (hTW.trans (normalizer_le_normalizer_centralizer W))).trans inf_normalizer_le_normalizer_inf
  have he := T.is_maximal' (T.isPGroup'.to_sup_of_normal_right' hKp hTK) le_sup_left
  have hKT : K ≤ (T : Subgroup G) := he ▸ le_sup_right
  exact le_antisymm (le_inf hKT inf_le_right) (inf_le_inf_right _ le_sup_right)

/-- The literal hyperplane normalizer in L normalizes C_T(U∩V), as asserted
immediately before 12.2.25. No normality of T in that normalizer is assumed. -/
theorem hyperplane_normalizer_normalizes_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G) ≤
      normalizer (((T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  rw [← local_join_hyperplane_centralizer h D structural A C]
  exact (le_inf ((inf_le_left.trans le_sup_left).trans (L ⊔ (T : Subgroup G)).le_normalizer)
    (inf_le_right.trans (normalizer_le_normalizer_centralizer (U ⊓ V)))).trans inf_normalizer_le_normalizer_inf

/-- The centralizer R has index two in the hyperplane centralizer in the
higher-dimensional branch. -/
theorem higher_radical_index
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 4 ≤ d) :
    ((T : Subgroup G) ⊓ centralizer (U : Set G)).relIndex
      ((T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G)) = 2 := by
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let K := (T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G)
  have hRV : R ⊓ V = U ⊓ V := by
    rw [inf_assoc, inf_comm (centralizer _) V, chosen_centralizer_core A C,
      inf_eq_right.mpr (inf_le_right.trans D.le_sylow)]
  have hRK : R ≤ K := inf_le_inf_left _ (centralizer_le inf_le_left)
  have hs : R ⊔ V = K := by
    dsimp only [K]
    rw [higher_hyperplane_centralizer h D structural A C hnone hd]
    dsimp only [R]
    rw [C.sylow_centralizer_core_decomposition (by have := A.dimension.1; omega)
      (((structural G T L h).2.2 V D).1) D.le_sylow hnone]
    ac_rfl
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes R V
    (D.le_sylow.trans ((le_inf (T : Subgroup G).le_normalizer
      (C.sylow_normalizes_core.trans (normalizer_le_normalizer_centralizer U))).trans
        inf_normalizer_le_normalizer_inf))
  rw [hRV,hs] at hp
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) R K bot_le hRK
  rw [relIndex_bot_left,relIndex_bot_left] at hi
  have hv := relIndex_mul_relIndex (⊥ : Subgroup G) (U ⊓ V) V bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,hyperplane_index' A C] at hv
  have hr := Nat.card_pos (α := R)
  have hw := Nat.card_pos (α := ↥(U ⊓ V))
  change R.relIndex K = 2
  rw [← hi, ← hv] at hp
  have he : Nat.card R * Nat.card ↥(U ⊓ V) * 2 =
      Nat.card R * Nat.card ↥(U ⊓ V) * R.relIndex K := by nlinarith only [hp]
  exact (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hr hw) he).symm

/-- The two-residual of the literal hyperplane normalizer fixes R. The
index-two elementary argument replaces the source's Thompson calculation
without requiring a complement or self-normalization. -/
theorem higher_residual_normalizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 4 ≤ d) :
    rigidityHyperplaneResidual L U V ≤
      normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) := by
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let K := (T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G)
  have hUK : U ≤ K := le_inf C.core_le_sylow (by
    let := C.elementary
    exact (le_centralizer U).trans (centralizer_le inf_le_left))
  have hVK : V ≤ K := le_inf D.le_sylow (by
    let := D.elementary
    exact (le_centralizer V).trans (centralizer_le inf_le_right))
  have hnot : ¬ IsElementaryAbelian 2 K := by
    intro hk
    let := hk
    have hu : U ≤ centralizer (V : Set G) :=
      hUK.trans ((le_centralizer K).trans (centralizer_le hVK))
    have hz : U ⊓ V = ⊥ := C.transvections.symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr hu)
    have hh := C.hyperplane
    rw [hz,card_bot] at hh
    have hd1 : 0 < d-1 := by have := A.dimension.1; omega
    have hp : 1 < 2^(d-1) := one_lt_pow₀ (by decide) (by omega)
    omega
  exact twoPerfect_le_normalizer_elementary_index_two _ K R
    (isPPerfect_embedded_pResidual 2 _)
    ((map_subtype_le _).trans (hyperplane_normalizer_normalizes_centralizer h D structural A C))
    (inf_le_inf_left _ (centralizer_le inf_le_left))
    (radical_elementary h D structural A C hnone)
    (higher_radical_index h D structural A C hnone hd) hnot

/-- Assembly of the higher-dimensional record after the still-owned Sylow
intersection step. The common-centralizers owner must discharge `hdisjoint`;
this conditional application is not a completed source theorem. -/
theorem higher_centralizers_of_sylow_disjoint
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 4 ≤ d)
    (hdisjoint : Disjoint ((T : Subgroup G) ⊓ L)
      ((T : Subgroup G) ⊓ centralizer (L : Set G))) :
    LocalRigidityCentralizers T L V U P where
  kernel_split := higher_kernel_split D A C hd
  kernel_disjoint := kernel_disjoint D A
  centralizer_split := higher_centralizer_split h D structural A C hnone hd
  centralizer_disjoint := core_disjoint_component_centralizer D A C
  common_trivial := common_trivial h D C
  elementary := radical_elementary h D structural A C hnone
  component_centralizer_card := higher_component_centralizer_card h D structural A C hnone hd
  sylow_split := higher_sylow_split h D structural A C hd
  sylow_disjoint := hdisjoint
  component_centralizer_central := higher_component_centralizer_central h D structural A C hnone hd
  pair_centralizer_central := higher_pair_centralizer_central h D structural A C hnone hd
  hyperplane_centralizer := higher_hyperplane_centralizer h D structural A C hnone hd
  residual_normalizes := higher_residual_normalizes h D structural A C hnone hd

end RigidityKernel
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
