module
public import CFSG.Quasithin.Chapter10.SourceA5PointQuasisimple
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.SpecificGroups.PSL3Four.PerfectSubgroupFixer
/-!
# The linear containing-component rows for the original A5 module

The original nonzero moved elementary subgroup remains noncentral under every
central quotient of L. The binary A5 degree bound therefore forces each central
image to have two-rank at least four. Every involution centralizing L then fixes
a perfect subgroup of this rank in PSL3(4), so the model fixer theorem and faithful
perfect-cover descent force it to centralize the original containing component.

All maps use the actual inclusions and quotient by center I; no faithfulness of
the moved module in that quotient or identification of the cover with SL3(4) is
assumed. Source: Aschbacher–Smith, proof of 10.2.9, pp.750–751, combined manuscript
of 1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The original moved module survives every central image with two-rank at least four. -/
theorem source_a5_central_image_twoRank
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {H : Type*} [Group H] [Finite H] (f : L →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ center L) : 4 ≤ primeRank 2 H := by
  let W := ⁅D.fullModule,L⁆
  let A := W.subgroupOf L
  have hWL : W ≤ L := source_full_moved_le_component D
  have hmapA : A.map L.subtype = W := map_subgroupOf_eq_of_le hWL
  have hA : A.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_right _ _)
  let := hA
  let := source_original_full_moved_elementary D
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hWL
  have hmove : ⁅A,(⊤ : Subgroup L)⁆ = A := by
    apply map_injective L.subtype_injective
    rw [map_commutator,hmapA,←MonoidHom.range_eq_map,range_subtype]
    exact source_full_moved_eq_commutator D
  have hAne : A ≠ ⊥ := by
    intro h
    have hh := congrArg (map L.subtype) h
    rw [hmapA,Subgroup.map_bot] at hh
    exact source_full_moved_ne_bot D hh
  let N := A.map f
  let : N.Normal := hA.map f hf
  let : IsElementaryAbelian 2 N := IsElementaryAbelian.map f
  have hNmove : ⁅N,(⊤ : Subgroup H)⁆ = N := by
    rw [show (⊤ : Subgroup H) = (⊤ : Subgroup L).map f from
      (map_top_of_surjective _ hf).symm,←map_commutator,hmove]
  have hNnoncentral : ¬ N ≤ center H := by
    intro hn
    have hNzero : N = ⊥ := hNmove.symm.trans
      (commutator_top_right_eq_bot_iff_le_center.mpr hn)
    have hak : A ≤ f.ker := (map_eq_bot_iff A).mp hNzero
    have haz : A ≤ center L := hak.trans hker
    exact hAne (hmove.symm.trans (commutator_top_right_eq_bot_iff_le_center.mpr haz))
  let rho : L →* MulAut N := (MulAut.conjNormal : H →* MulAut N).comp f
  have hrho : rho ≠ 1 := by
    intro he
    apply hNnoncentral
    intro n hn
    apply mem_center_iff.mpr
    intro h
    obtain ⟨l,rfl⟩ := hf h
    have hh := congrArg (fun a : MulAut N => (a ⟨n,hn⟩ : H))
      (congrArg (fun r : L →* MulAut N => r l) he)
    change f l*n*(f l)⁻¹=n at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have h16 := alternatingGroup.FiveChiefDegree.sixteen_le_card_of_nontrivial_action
    D.faithful.1.2.1 e rho hrho (IsElementaryAbelian.isPGroup 2 N)
  by_contra! hr
  have hsmall : Nat.card N ≤ 2 ^ 3 :=
    (primeRank_le_iff_elementary_card_le H).mp (by omega : primeRank 2 H ≤ 3)
      N inferInstance
  norm_num at hsmall
  omega

include D in
/-- The original A5 image centralizes every perfect containing component with
central quotient PSL3(4), including SL3(4) and nontrivial central covers. -/
theorem source_a5_psl3Four_containing_centralizer
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L ≤ I)
    (eI : I ⧸ center I ≃* Matrix.PSL3Four.PSL)
    (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hUI : U ≤ normalizer (I : Set G)) (hUL : U ≤ centralizer (L : Set G)) :
    U ≤ centralizer (I : Set G) := by
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let A := L.subgroupOf I
  let k : L ≃* A := (subgroupOfEquivOfLe hLI).symm
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := k.toMonoidHom) k.surjective
  let q := eI.toMonoidHom.comp (QuotientGroup.mk' (center I))
  let f := (q.subgroupMap A).comp k.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective A).comp k.surjective
  have hk : f.ker ≤ center L := by
    intro l hl
    have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
    change eI (QuotientGroup.mk' (center I) (inclusion hLI l)) = 1 at hh
    have hz : QuotientGroup.mk' (center I) (inclusion hLI l) = 1 :=
      eI.injective (hh.trans eI.map_one.symm)
    have hc := (QuotientGroup.eq_one_iff (inclusion hLI l)).mp hz
    apply mem_center_iff.mpr
    intro m
    exact Subtype.ext (congrArg I.subtype (mem_center_iff.mp hc (inclusion hLI m)))
  have hr : 2 < primeRank 2 (A.map q) := by
    have hh := source_a5_central_image_twoRank D e f hf hk
    change 4 ≤ primeRank 2 (A.map q) at hh
    omega
  let act : U →* MulAut I := I.normalizerMonoidHom.comp (inclusion hUI)
  intro u hu
  have hau : act ⟨u,hu⟩ = 1 := by
    apply Matrix.PSL3Four.PerfectSubgroupFixer.centralCover_eq_one_of_fixes_perfect_high_rank
      eI _ (by
        rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 U) ⟨u,hu⟩, map_one]) A hr
    intro b hb
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply Subtype.ext
    change u * ((b : I) : G) * u⁻¹ = ((b : I) : G)
    exact mul_inv_eq_iff_eq_mul.mpr (hUL hu (b : I) hb).symm
  have hker : inclusion hUI ⟨u,hu⟩ ∈ I.normalizerMonoidHom.ker := hau
  rwa [Subgroup.normalizerMonoidHom_ker] at hker

end CFSG.Quasithin.Chapter10
