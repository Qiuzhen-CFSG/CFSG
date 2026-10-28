module
public import CFSG.Quasithin.Chapter10.SourceA5FiveResidual
public import CFSG.Quasithin.Chapter10.SourceA5LocalSeedReduction
public import CFSG.Quasithin.Chapter10.SourceA5ModuleQuadraticBound
public import CFSG.Quasithin.Chapter3.Section02.FundamentalActor
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# The final full/local passage for the original A₅ module

The actual image J of L₀ in the faithful full actor Q=M/C_M(V_M) has
index prime to three and five, and Q retains the K-group hypothesis.
If Q/J is a two-group, the image of the original Sylow subgroup supplements
J. Both subgroups preserve the original local module, and the kernel of
M → Q centralizes the full module. Thus M preserves the local module and
its M-orbit is already local.

The final consumer applies this equality to the original moved quotient
and separated chosen seed. The two-group quotient and seed separation are
explicit inputs from the multiplicity and local support arguments; this
module does not assert those earlier source conclusions.

Source: Aschbacher--Smith D.3.21 and 3.2.6, printed pp.204--207 and581;
A₅ specialization in10.1.1, printed p.741.
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))

private theorem eq_top_of_sylow_image_quotient_two
    {H Q : Type*} [Group H] [Finite H] [Group Q] [Finite Q]
    (q : H →* Q) (hq : Function.Surjective q)
    (R K : Subgroup H) [R.Normal] (S : Sylow 2 H)
    (hR : R ≤ K) (hS : (S : Subgroup H) ≤ K) (hker : q.ker ≤ K)
    (htwo : let _ : (R.map q).Normal := Subgroup.Normal.map inferInstance q hq
      IsPGroup 2 (Q ⧸ R.map q)) : K = ⊤ := by
  let _ : (R.map q).Normal := Subgroup.Normal.map inferInstance q hq
  have htop : K.map q = ⊤ := by
    apply top_unique
    rw [← (S.mapSurjective hq).sup_eq_top_of_quotient_isPGroup (R.map q) htwo]
    exact sup_le (by simpa only [Sylow.coe_mapSurjective] using map_mono hS)
      (map_mono hR)
  have hc := congrArg (Subgroup.comap q) htop
  rw [comap_map_eq, sup_of_le_left hker, comap_top] at hc
  exact hc

include D e in
/-- The three-prime index of the original orbit. -/
theorem source_nonnormal_a5_orbit_index_coprime_three
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Nat.Coprime 3 ((localOrbit T L).subgroupOf D.maximalLocal).index := by
  have hd : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have he : (localOrbit T L).subgroupOf D.maximalLocal =
      primeToResidual 3 D.maximalLocal := by
    apply map_injective D.maximalLocal.subtype_injective
    rw [map_subgroupOf_eq_of_le (localOrbit T L).le_normalizer,
      source_nonnormal_cubic_residual D hn hd]
  rw [he]
  exact primeToResidual_index_coprime 3

include D e in
/-- The actual image of the orbit has index prime to both three and five. -/
theorem source_a5_original_actor_orbit_index_coprime
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    Nat.Coprime 3 J.index ∧ Nat.Coprime 5 J.index := by
  dsimp only
  let := (source_full_module_reduced D).normal
  have hd := ((localOrbit T L).subgroupOf D.maximalLocal).index_map_dvd
    (QuotientGroup.mk'_surjective
      (centralizer (D.fullModule.subgroupOf D.maximalLocal : Set D.maximalLocal)))
  exact ⟨(source_nonnormal_a5_orbit_index_coprime_three D e hn).coprime_dvd_right hd,
    (source_nonnormal_a5_orbit_index_coprime_five D e hn).coprime_dvd_right hd⟩

/-- A two-group outer actor forces the literal full and local modules to agree. -/
theorem source_full_eq_local_of_actor_orbit_quotient_two :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    let _ : J.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
    IsPGroup 2 ((D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)) ⧸ J) →
      D.fullModule = D.moduleSubgroup := by
  dsimp only
  intro htwo
  let M := D.maximalLocal
  let R := (localOrbit T L).subgroupOf M
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let K := (normalizer (D.moduleSubgroup : Set G)).subgroupOf M
  have hV : D.moduleSubgroup ≤ D.fullModule := le_componentOrbit _ _
  have hVM : D.moduleSubgroup ≤ M :=
    hV.trans (D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer)
  have hR : R ≤ K := fun _ hx => D.orbit_normalizes_module hx
  have hS : (D.ambientSylow : Subgroup M) ≤ K := by
    intro x hx
    exact D.sylow_normalizes_module hx
  have hker : q.ker ≤ K := by
    intro x hx
    have hxc : x ∈ centralizer (U : Set M) := (QuotientGroup.eq_one_iff _).mp hx
    apply centralizer_le_normalizer (D.moduleSubgroup : Set G)
    intro v hv
    exact congrArg (fun z : M => (z : G)) (hxc ⟨v,hVM hv⟩ (hV hv))
  have hK : K = ⊤ := eq_top_of_sylow_image_quotient_two q
    (QuotientGroup.mk'_surjective _) R K D.ambientSylow hR hS hker htwo
  have hn : M ≤ normalizer (D.moduleSubgroup : Set G) := by
    intro m hm
    exact show (⟨m,hm⟩ : M) ∈ K from hK.symm ▸ mem_top _
  exact le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hn) hV

/-- The literal full actor inherits the K-group hypothesis from the maximal two-local. -/
theorem source_full_actor_isKGroup :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    IsKGroup KnownSimple.IsKnownSimple
      (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)) := by
  dsimp only
  let := (source_full_module_reduced D).normal
  have hu := source_module_nonsolvable_uniqueness D
  exact (D.simpleQTKE.twoLocal_sqtk hu.normalizer_maximal.1).isKGroup.quotient _

local instance originalLocalPassageMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The original moved quotient consumer after the outer actor is a two-group. -/
theorem source_a5_original_irreducible_of_actor_orbit_quotient_two
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (htwo : let U := D.fullModule.subgroupOf D.maximalLocal
      let := (source_full_module_reduced D).normal
      let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
      let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
      let _ : J.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
      IsPGroup 2 ((D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)) ⧸ J)) :
    (originalMovedQuotientAction D e).IsIrreducible ∧
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
  source_a5_original_irreducible_of_separated_seed D hn ht htn e
    (source_full_eq_local_of_actor_orbit_quotient_two D htwo) hsep

end CFSG.Quasithin.Chapter10
