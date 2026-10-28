module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.FactorKernel
public import Theory.GroupTheory.PointCentralizerGeneration
public import Theory.GroupTheory.CommutatorPreimage.Membership

/-!
# Point centralizers generate the original A₅ component

For the original component L, a supplement Q to a subgroup U of the full
binary module suffices to test containment of L when U centralizes L.
Every lift of a square-one element in L/O₂(L) either fixes a nonidentity
point of Q, or has all displacements in U. The latter alternative puts
its action on W/C_W(L) in the known kernel O₂(L). The core centralizes Q,
so it also lies in the target subgroup. Involutions generate the simple
quotient A₅, completing the containment without assuming Q is invariant.

This is the point-centralizer generation step in Aschbacher–Smith 10.2.12,
printed p.754 (PDF p.771). The generic perfect-group theorem also applies
directly to the original moved factor W=[V,L].
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))

/-- The original component is forced into any subgroup containing all
point centralizers of the original moved factor. -/
theorem source_le_of_full_moved_point_centralizers
    (N : Subgroup G)
    (hcent : ∀ w ∈ ⁅D.fullModule,L⁆, w ≠ 1 → centralizer ({w} : Set G) ≤ N) : L ≤ N := by
  have hLperfect : Group.IsPerfect L := by
    let := D.maximal.1.1.perfect
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  let := hLperfect
  exact le_of_point_centralizers L ⁅D.fullModule,L⁆ N
    (normalizer_commutator_ge_right _ _)
    (source_original_full_moved_elementary D).isPGroup
    (source_full_moved_ne_bot D) hcent

include e in
/-- Point centralizers on any supplement to a component-fixed subgroup of
the original full module force containment of the original component. -/
theorem source_a5_le_of_supplement_point_centralizers
    (Q U N : Subgroup G) (hQ : Q ≤ D.fullModule) (hU : U ≤ D.fullModule)
    (hsup : D.fullModule = Q ⊔ U) (hUL : U ≤ centralizer (L : Set G))
    (hcent : ∀ q ∈ Q, q ≠ 1 → centralizer ({q} : Set G) ≤ N) : L ≤ N := by
  classical
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  have hLV : L ≤ normalizer (D.fullModule : Set G) :=
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule :=
    le_normalizer_iff_commutator_le_left.mp hLV
  have hUQ : U ≤ centralizer (Q : Set G) :=
    hU.trans (D.fullModule.le_centralizer.trans (centralizer_le hQ))
  have hdecomp : ∀ v ∈ D.fullModule, ∃ q ∈ Q, ∃ u ∈ U, q * u = v := by
    intro v hv
    have hv' : v ∈ Q ⊔ U := hsup ▸ hv
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left Q U
      (hUQ.trans (Subgroup.centralizer_le_normalizer _))] at hv'
    exact hv'
  have hQne : Q ≠ ⊥ := by
    intro hz
    have hVU : D.fullModule ≤ U := by rw [hsup,hz,bot_sup_eq]
    have hWC : ⁅D.fullModule,L⁆ ≤ centralizer (L : Set G) :=
      hWV.trans (hVU.trans hUL)
    have hzero : ⁅⁅D.fullModule,L⁆,L⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr hWC
    rw [source_full_moved_eq_commutator D] at hzero
    exact source_full_moved_ne_bot D hzero
  obtain ⟨q,hqne'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hQne
  have hq := q.property
  have hqne : (q:G) ≠ 1 := fun h => hqne' (Subtype.ext h)
  have hcoreN : L.pCoreIn 2 ≤ N := by
    intro x hx
    apply hcent (q:G) hq hqne
    apply mem_centralizer_singleton_iff.mpr
    exact (mem_centralizer_iff.mp (source_component_core_centralizes_fullModule D hx)
      (q:G) (hQ hq)).symm
  let f : L →* alternatingGroup (Fin 5) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hker : f.ker = pCore 2 L := by
    exact (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (pCore 2 L))
      e.toMonoidHom e.injective).trans (QuotientGroup.ker_mk' _)
  have hlifts : ∀ x : L, f x ^ 2 = 1 → x ∈ N.subgroupOf L := by
    intro x hx2
    change (x : G) ∈ N
    by_contra hxN
    have hx2core : x*x ∈ pCore 2 L := by
      rw [←hker,MonoidHom.mem_ker,map_mul]
      simpa only [pow_two] using hx2
    have hsq : ∀ v ∈ D.fullModule, ((x:G)*(x:G))*v = v*((x:G)*(x:G)) := by
      intro v hv
      have hc : ((x:G)*(x:G)) ∈ L.pCoreIn 2 := mem_map.mpr ⟨x*x,hx2core,rfl⟩
      exact (mem_centralizer_iff.mp (source_component_core_centralizes_fullModule D hc) v hv).symm
    have hno : ∀ q ∈ Q, (x:G)*q=q*(x:G) → q=1 := by
      intro q hq hfix
      by_contra hqne
      exact hxN (hcent q hq hqne (mem_centralizer_singleton_iff.mpr hfix))
    have hdisp := displacement_mem_of_no_fixed_supplement D.fullModule Q U
      hdecomp (x:G) (hLV x.property)
      (fun u hu => mem_centralizer_iff.mp (hUL hu) (x:G) x.property) hsq hno
    have hfixnorm : L ≤ normalizer (sourceMovedFixed D : Set G) :=
      (le_inf L.le_normalizer (normalizer_commutator_ge_right _ _)).trans
        (source_original_moved_fixed_normalizer D)
    have hxkernel : (x:G) ∈ commutatorPreimage L ⁅D.fullModule,L⁆ (sourceMovedFixed D) := by
      apply (mem_commutatorPreimage_iff _ _ _ hfixnorm _).mpr
      refine ⟨x.property,?_⟩
      intro w hw
      change ⁅(x:G),w⁆ ∈ ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)
      refine ⟨?_,hUL (hdisp w (hWV hw))⟩
      exact le_normalizer_iff_commutator_le_right.mp
        (normalizer_commutator_ge_right D.fullModule L)
        (commutator_mem_commutator x.property hw)
    rw [source_a5_original_moved_quotient_kernel D e] at hxkernel
    exact hxN (hcoreN hxkernel)
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have htop : N.subgroupOf L = ⊤ := eq_top_of_square_one_lifts f
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (by rw [nat_card_alternatingGroup]; norm_num [Nat.factorial])
    (N.subgroupOf L) hlifts
  intro x hx
  exact show (⟨x,hx⟩ : L) ∈ N.subgroupOf L from htop ▸ mem_top _

end CFSG.Quasithin.Chapter10
