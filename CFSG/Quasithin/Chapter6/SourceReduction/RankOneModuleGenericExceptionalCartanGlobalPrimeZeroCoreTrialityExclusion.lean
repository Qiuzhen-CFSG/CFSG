module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreCenter
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreDegree
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import Theory.SpecificGroups.Triality.BinaryTorusCentralizer

/-!
# Excluding the marked zero-core binary-triality pair

A nontrivial subgroup normal in the original Sylow meets its center.
When the omega-center has order two it therefore lies in the original
moved reduced subgroup. Its L-span is elementary and remains inside the
overlap S. This span cannot be centralized by L: otherwise the prime
actor and H would both centralize the omega-center, contradicting the
trivial two-core of the actual generated pair.

The noncentral PSL₂ constituent gives the span order at least sixteen,
since the marked right parabolic already forces the original degree two.
The checked seven-action theorem makes B ∩ R fix the whole span. The
literal Borel isomorphism now transports both subgroups to the genuine
binary-triality Borel, where the seven-centralizer bound is eight.

Thus this actual parabolic marking is excluded without identifying S with
T, or the original field degree with the right quotient degree three.
Marked recognition, the unitary row, higher-field reduction and the
changed-Sylow argument remain with qt-d-1222-rankone-cartan-local-to-global.
Source: Aschbacher–Smith 5.2.2, printed pp.647–648 (`refs/quasithin.pdf`),
using the E.2.13(4) constituent bound, printed p.225.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
open Triality.Standard Triality.Standard.Parabolics

/-- An omega-center of order two lies in the original nontrivial moved subgroup. -/
theorem Input.omega_le_moved_of_card_two
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hZcard : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤ ⁅W,L⁆ := by
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  let U := ⁅W,L⁆
  obtain ⟨hU,hUT,_⟩ := h.moved_reduced_size
  let := hU
  obtain ⟨z,hzne⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' h.noncentral
      (show U ≤ (T : Subgroup G) from hUT.trans inf_le_left) h.moved_reduced_normalizes)
  have hzZ : (z : G) ∈ Z :=
    (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hUT z.property.1 |>.1,elemPow_eq_one_of_isElementaryAbelian _ z.property.1,
        z.property.2.2⟩
  have hI : Z ⊓ U ≠ ⊥ := by
    intro hi
    exact hzne (Subtype.ext (mem_bot.mp (hi ▸ (show (z : G) ∈ Z ⊓ U from ⟨hzZ,z.property.1⟩))))
  have he : Z ⊓ U = Z := eq_of_le_of_card_ge inf_le_left (by
    rw [hZcard]
    exact Nat.succ_le_iff.mpr ((one_lt_card_iff_ne_bot _).mpr hI))
  exact he.symm.le.trans inf_le_right

/-- Every noncentral elementary subgroup in L normalized by L has the source degree bound. -/
theorem Input.moved_elementary_subgroup_size
    {T : Sylow 2 G} {L W V : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n) [IsElementaryAbelian 2 V]
    (hVL : V ≤ L) (hVN : L ≤ normalizer (V : Set G)) (hmove : ⁅V,L⁆ ≠ ⊥) :
    2 ^ (2*n) ≤ Nat.card V := by
  have hm : ⁅⁅V,L⁆,L⁆ = ⁅V,L⁆ := commutator_isPPerfect_idempotent L V
    h.local_mem.2.2.1 (IsElementaryAbelian.isPGroup 2 V) hVN
  have hEV : ⁅V,L⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp hVN
  let : IsElementaryAbelian 2 (⁅V,L⁆ : Subgroup G) := IsElementaryAbelian.of_le hEV
  let := h.local_mem.1.1.1.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := h.linear
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have hsize := Representation.SL2.moved_subgroup_card_bound L ⁅V,L⁆
    (hEV.trans hVL) hmove hm (a.trans (Theory.PSL2.sl2QuotientEquiv F).symm)
    (by have := h.exponent; omega : n ≠ 0) hF
  exact hsize.trans (Nat.card_le_card_of_injective (inclusion hEV) (inclusion_injective hEV))

namespace Prime

/-- The original omega-span has order at least sixteen and is fixed by the actual seven-subgroup. -/
theorem LocalData.zeroCore_binaryTriality_large_fixed_module
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (e : RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      binaryTrialityPrimeAmalgam) :
    let V := conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L
    IsElementaryAbelian 2 V ∧ V ≤ Global.sourceS L H ∧ 16 ≤ Nat.card V ∧
      (B ⊓ R : Subgroup G) ≤ centralizer (V : Set G) := by
  let S := Global.sourceS L H
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  let U := ⁅W,L⁆
  let V := conjugateSpanBy Z L
  have hn := d.binaryTriality_original_degree h e.right
  obtain ⟨hcenter,hZcard,hHC⟩ := d.zeroCore_binaryTriality_omega_center h hH c hd hz e
  obtain ⟨hU,hUT,hlow⟩ := h.moved_reduced_size
  let := hU
  have hUS : U ≤ S := by
    rw [←d.S_intersection_left] at hUT
    exact hUT.trans inf_le_left
  have hZU : Z ≤ U := h.omega_le_moved_of_card_two hZcard
  have hVU : V ≤ U := conjugateSpanBy_le hZU (normalizer_commutator_ge_right W L)
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le hVU
  have hVS : V ≤ S := hVU.trans hUS
  have hVL : V ≤ L := hVU.trans (hUT.trans inf_le_right)
  have hVN : L ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy Z L
  have hmove : ⁅V,L⁆ ≠ ⊥ := by
    intro hm
    have hLC : L ≤ centralizer (Z : Set G) :=
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hm)).trans
        (centralizer_le (le_conjugateSpanBy Z L))
    have hDC : D ≤ centralizer (Z : Set G) :=
      hd.le_cartan.trans (c.left_le.trans (inf_le_left.trans hLC))
    have hRH : R ≤ H := d.right_le_residual.trans (map_subtype_le _)
    have hGC : generated L H D R ≤ centralizer (Z : Set G) :=
      sup_le hDC (sup_le (hRH.trans hHC)
        ((Global.sourceS_le_sylow h.sylow_normalizes hH.1.1.2).trans sylow_le_omegaCentralizer))
    have hZS : Z ≤ S := hZU.trans hUS
    have hcore : Z ≤ (generated L H D R).pCoreIn 2 :=
      le_pCoreIn_of_normalizes (T.isPGroup'.to_le (fun x hx =>
        ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx).1))
        (hZS.trans (le_sup_right.trans le_sup_right)) (hGC.trans (Subgroup.centralizer_le_normalizer _))
    have hb : Z = ⊥ := bot_unique (hz ▸ hcore)
    have hc : Nat.card Z = 1 := hb ▸ card_bot
    exact (by decide : (2 : ℕ) ≠ 1) (hZcard.symm.trans hc)
  have hsize := h.moved_elementary_subgroup_size hVL hVN hmove
  refine ⟨inferInstance,hVS,?_,d.zeroCore_binaryTriality_fixes_omega_span h hH c hd
    (Or.inl hn) hz e⟩
  simpa [hn] using hsize

/-- A genuine binary-triality parabolic marking is impossible in the original
zero-core prime pair. Both field comparisons and the seven action are derived. -/
theorem LocalData.zeroCore_not_binaryTriality_parabolic
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥) :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      binaryTrialityPrimeAmalgam) := by
  rintro ⟨e⟩
  let S := Global.sourceS L H
  let E := B ⊓ R
  let C := S ⊔ E
  let V := conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L
  obtain ⟨hV,hVS,hsize,hfix⟩ := d.zeroCore_binaryTriality_large_fixed_module h hH c hd hz e
  let : IsElementaryAbelian 2 V := hV
  have hVC : V ≤ C := hVS.trans le_sup_left
  let U := V.subgroupOf C
  let F := E.subgroupOf C
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVC
  have hF : Nat.card F = 7 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show E ≤ C from le_sup_right)).toEquiv]
    exact (d.zeroCore_binaryTriality_configuration h hH c hd hz e).2.2.2
  have hUF : U ≤ centralizer (F : Set C) := by
    intro u hu f hf
    exact Subtype.ext (((le_centralizer_iff.mp hfix) hu) f hf)
  have hfix' : U.map e.middle.toMonoidHom ≤
      centralizer (F.map e.middle.toMonoidHom : Set (borel (binaryParameters 1 Nat.zero_lt_one))) :=
    (map_mono hUF).trans (map_centralizer_le_centralizer_image F e.middle.toMonoidHom)
  have hupper := BinaryTorusCentralizer.borel_two_subgroup_card_le_eight
    (U.map e.middle.toMonoidHom) (F.map e.middle.toMonoidHom)
    ((IsElementaryAbelian.isPGroup 2 U).map e.middle.toMonoidHom)
    (by rw [card_map_of_injective e.middle.injective]; exact hF) hfix'
  rw [card_map_of_injective e.middle.injective,
    Nat.card_congr (subgroupOfEquivOfLe hVC).toEquiv] at hupper
  change 16 ≤ Nat.card V at hsize
  omega

end Prime
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
