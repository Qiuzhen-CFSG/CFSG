module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.Context
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.SecondComponent.Projections
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.PResidual.PrimeToMonotone


/-!
# Residual and offender placement for two natural components

The literal SQTK cover of the FF action has three-rank at most two. Applying
full Theorem A(2) to its semisimple section E(G) bounds the three-rank of E(G),
without asserting rank inheritance for arbitrary quotients. The two natural
seeds make L and M centerless. Distinct components commute, so any third
component would contribute a third independent unit of three-rank. Thus
E(G) = LM.

Each of L and M is its own prime-to-three residual: a proper normal subgroup
is central, whereas the residual has index prime to three and the component
has positive three-rank. Residual functoriality then identifies the actual
embedded residual of E(G) with LM.

Finally, the two inner actions combine to an inner action on the centerless
product LM. Its central projection is a two-group centralizing both E(G)
and F(G). Generalized-Fitting self-centralization and O₂(G)=1 make that
projection trivial, proving A ≤ LM.

The sole earlier-source parameter beyond Setup is universal full Theorem A,
with all hypotheses and clauses retained in ChapterA.Section02.Statements.
The two natural seeds are the explicit inputs of this independent conditional
step; their construction remains with the B.5.9 assembly owner. No residual,
placement, component-list or quotient-rank conclusion is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108, the sentence invoking Theorem A(2) in the final paragraph.
-/

public section

open scoped Pointwise
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.ResidualPlacement
open QuasisimpleSource ChapterA.Section02
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [Finite G] in
private theorem layer_semisimple : IsSemisimple (componentLayer G) := by
  apply (Subgroup.map_injective (componentLayer G).subtype_injective)
  apply le_antisymm
  · exact map_mono le_top
  · rw [← MonoidHom.range_eq_map, range_subtype]
    apply sSup_le
    intro L hL
    have hLE : L ≤ componentLayer G := le_sSup hL
    have h := map_mono (f := (componentLayer G).subtype)
      (show L.subgroupOf (componentLayer G) ≤ componentLayer (componentLayer G) from
        le_sSup (hL.subgroupOf hLE))
    rwa [map_subgroupOf_eq_of_le hLE] at h

private theorem layer_three_rank {K : GroupClass.{u}} {A : Subgroup G}
    (setup : Setup ρ K A)
    (theoremA : ∀ (D : Type u) [Group D] [Finite D], TheoremA K D) :
    primeRank 3 (componentLayer G) ≤ 2 := by
  obtain ⟨q⟩ := setup.hypothesis.quotient
  let f : q.Cover →* G := q.equiv.toMonoidHom.comp (QuotientGroup.mk' q.kernel)
  have hf : Function.Surjective f :=
    q.equiv.surjective.comp (QuotientGroup.mk'_surjective q.kernel)
  have hs : IsSectionOf (componentLayer G) q.Cover :=
    (IsSectionOf.subgroup (componentLayer G)).ambient_surjective f hf
  have hr := q.sqtk.stronglyQuasithin 3 (by decide) (by decide)
  exact ((theoremA q.Cover q.sqtk.stronglyQuasithin.quasithin q.sqtk.isKGroup
    (componentLayer G) hs layer_semisimple 3 (by decide) (by decide)).2 hr).trans hr

omit [Finite G] in
private theorem disjoint_of_centerless {L N : Subgroup G}
    (hz : center L = ⊥) (hc : N ≤ centralizer (L : Set G)) : Disjoint L N := by
  apply Subgroup.disjoint_def.mpr
  intro x hx hn
  have hxc : (⟨x, hx⟩ : L) ∈ center L := by
    apply mem_center_iff.mpr
    intro l
    exact Subtype.ext (hc hn l l.property)
  have hxe : (⟨x, hx⟩ : L) = 1 := by simpa only [hz, mem_bot] using hxc
  exact congrArg Subtype.val hxe

private theorem layer_eq_pair {K : GroupClass.{u}} {A L M : Subgroup G}
    (setup : Setup ρ K A)
    (theoremA : ∀ (D : Type u) [Group D] [Finite D], TheoremA K D)
    (hL : IsComponent G L) (hM : IsComponent G M) (hne : L ≠ M)
    (sL : NaturalSeed ρ A L) (sM : NaturalSeed ρ A M) :
    componentLayer G = L ⊔ M := by
  have hr := layer_three_rank ρ setup theoremA
  have hzL := seed_center_eq_bot ρ sL
  have hzM := seed_center_eq_bot ρ sM
  have hcLM : L ≤ centralizer (M : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hL.commutator_eq_bot_of_ne hM hne)
  have hLE : L ≤ componentLayer G := le_sSup hL
  have hME : M ≤ componentLayer G := le_sSup hM
  apply le_antisymm ?_ (sup_le hLE hME)
  apply sSup_le
  intro N hN
  by_cases hNL : N = L
  · exact hNL ▸ le_sup_left
  by_cases hNM : N = M
  · exact hNM ▸ le_sup_right
  have hcNL : N ≤ centralizer (L : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hN.commutator_eq_bot_of_ne hL hNL)
  have hcNM : N ≤ centralizer (M : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hN.commutator_eq_bot_of_ne hM hNM)
  have hcMLN : M ⊔ N ≤ centralizer (L : Set G) :=
    sup_le (le_centralizer_iff.mp hcLM) hcNL
  have hMN := M.primeRank_sup_eq_add_of_disjoint_commuting N
    (disjoint_of_centerless hzM hcNM) (le_centralizer_iff.mp hcNM) 3
  have hLMN := L.primeRank_sup_eq_add_of_disjoint_commuting (M ⊔ N)
    (disjoint_of_centerless hzL hcMLN) (le_centralizer_iff.mp hcMLN) 3
  have hbound : primeRank 3 ↥(L ⊔ (M ⊔ N)) ≤ primeRank 3 (componentLayer G) :=
    primeRank_le_of_injective 3 (inclusion
      (sup_le hLE (sup_le hME (show N ≤ componentLayer G from le_sSup hN))))
      (inclusion_injective _)
  rw [hLMN, hMN, setup.component_three_rank L hL,
    setup.component_three_rank M hM, setup.component_three_rank N hN] at hbound
  omega

private theorem quasisimple_residual_eq_top {H : Type*} [Group H] [Finite H]
    [IsQuasisimple H] (hz : center H = ⊥) (hr : primeRank 3 H = 1) :
    primeToResidual 3 H = ⊤ := by
  rcases IsQuasisimple.normal_le_center_or_eq_top (primeToResidual 3 H) with hc | ht
  · have hb : primeToResidual 3 H = ⊥ := le_bot_iff.mp (hc.trans hz.le)
    have hcop := primeToResidual_index_coprime (G := H) 3
    rw [hb, index_bot] at hcop
    have hr0 : primeRank 3 H = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr
      (Nat.prime_three.coprime_iff_not_dvd.mp hcop)
    omega
  · exact ht

private theorem residual_eq_pair {K : GroupClass.{u}} {A L M : Subgroup G}
    (setup : Setup ρ K A) (hL : IsComponent G L) (hM : IsComponent G M)
    (sL : NaturalSeed ρ A L) (sM : NaturalSeed ρ A M)
    (he : componentLayer G = L ⊔ M) :
    L ⊔ M = (primeToResidual 3 ↥(componentLayer G)).map (componentLayer G).subtype := by
  let : IsQuasisimple L := hL.2
  let : IsQuasisimple M := hM.2
  have hl := embedded_primeToResidual_mono 3 (show L ≤ componentLayer G from le_sSup hL)
  have hm := embedded_primeToResidual_mono 3 (show M ≤ componentLayer G from le_sSup hM)
  rw [quasisimple_residual_eq_top (seed_center_eq_bot ρ sL)
    (setup.component_three_rank L hL), ← MonoidHom.range_eq_map, range_subtype] at hl
  rw [quasisimple_residual_eq_top (seed_center_eq_bot ρ sM)
    (setup.component_three_rank M hM), ← MonoidHom.range_eq_map, range_subtype] at hm
  exact le_antisymm (sup_le hl hm) (he ▸ map_subtype_le _)

omit [Finite G] in
private theorem centerless_sup {L M : Subgroup G}
    (hzL : center L = ⊥) (hzM : center M = ⊥)
    (hc : L ≤ centralizer (M : Set G)) : center ↥(L ⊔ M) = ⊥ := by
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting L M
    (disjoint_of_centerless hzL (le_centralizer_iff.mp hc)) hc
  apply Subgroup.card_eq_one.mp
  rw [← Nat.card_congr (centerCongr e).toEquiv, Subgroup.center_prod, hzL, hzM]
  simp

omit [Finite G] in
private theorem inner_sup {A L M : Subgroup G}
    (hL : InducesInner A L) (hM : InducesInner A M)
    (hc : L ≤ centralizer (M : Set G)) : InducesInner A (L ⊔ M) := by
  intro a ha
  obtain ⟨l, hl, hleft⟩ := hL a ha
  obtain ⟨m, hm, hright⟩ := hM a ha
  refine ⟨l * m, mul_mem (mem_sup_left hl) (mem_sup_right hm), ?_⟩
  change L ⊔ M ≤ (MulAut.conj a).toMonoidHom.eqLocus
    (MulAut.conj (l * m)).toMonoidHom
  apply sup_le
  · intro x hx
    change a * x * a⁻¹ = (l * m) * x * (l * m)⁻¹
    have hmx : m * x = x * m := hc hx m hm
    calc
      a * x * a⁻¹ = l * x * l⁻¹ := hleft x hx
      _ = l * (m * x * m⁻¹) * l⁻¹ := by rw [hmx, mul_inv_cancel_right]
      _ = (l * m) * x * (l * m)⁻¹ := by group
  · intro x hx
    change a * x * a⁻¹ = (l * m) * x * (l * m)⁻¹
    have hlt : l * (m * x * m⁻¹) = (m * x * m⁻¹) * l :=
      (hc hl _ (M.mul_mem (M.mul_mem hm hx) (M.inv_mem hm))).symm
    calc
      a * x * a⁻¹ = m * x * m⁻¹ := hright x hx
      _ = l * (m * x * m⁻¹) * l⁻¹ := by rw [hlt, mul_inv_cancel_right]
      _ = (l * m) * x * (l * m)⁻¹ := by group

private theorem component_centralizes_fitting {L : Subgroup G} (hL : IsComponent G L) :
    L ≤ centralizer (fittingSubgroup G : Set G) := by
  rcases hL.normal_dichotomy (fittingSubgroup G) with h | h
  · let : IsQuasisimple L := hL.2
    let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    have hs : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective h)
    exact (Group.IsPerfect.not_isSolvable L hs).elim
  · exact commutator_eq_bot_iff_le_centralizer.mp h

private theorem offender_le_pair {K : GroupClass.{u}} {A L M : Subgroup G}
    (setup : Setup ρ K A)
    (hL : IsComponent G L) (hM : IsComponent G M) (hne : L ≠ M)
    (sL : NaturalSeed ρ A L) (sM : NaturalSeed ρ A M)
    (he : componentLayer G = L ⊔ M) : A ≤ L ⊔ M := by
  have hc : L ≤ centralizer (M : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hL.commutator_eq_bot_of_ne hM hne)
  let d := InnerProjections.ofInner
    (centerless_sup (seed_center_eq_bot ρ sL) (seed_center_eq_bot ρ sM) hc)
    (inner_sup sL.inner sM.inner hc)
  have hfit : L ⊔ M ≤ centralizer (fittingSubgroup G : Set G) :=
    sup_le (component_centralizes_fitting hL) (component_centralizes_fitting hM)
  have hCF : d.centralProjection ≤ centralizer (fittingSubgroup G : Set G) :=
    d.centralProjection_le_join.trans (sup_le hfit setup.centralizes_fitting)
  have hCE : d.centralProjection ≤ centralizer (componentLayer G : Set G) := by
    rw [he]
    exact d.centralProjection_le
  have hCFstar : d.centralProjection ≤ centralizer (generalizedFitting G : Set G) :=
    le_centralizer_iff.mp
      (sup_le (le_centralizer_iff.mp hCF) (le_centralizer_iff.mp hCE))
  let : IsElementaryAbelian 2 A := setup.minimal.1.1.2
  have hd := ChapterB.QuasisimpleSections.disjoint_centralizer_fitting
    setup.hypothesis.twoCore d.centralProjection
    (d.centralProjection_isPGroup (IsElementaryAbelian.isPGroup 2 A))
  have hbot : d.centralProjection = ⊥ := hd.eq_bot_of_le hCFstar
  simpa only [hbot, sup_bot_eq] using d.offender_le

/-- The genuine offender containment and embedded prime-to-three residual
identity in B.5.9. The component commutator equalities in the source are not
needed after the two natural seeds and the Setup rank bounds are available. -/
theorem residual_and_offender_placement {K : GroupClass.{u}} {A L M : Subgroup G}
    (setup : Setup ρ K A)
    (theoremA : ∀ (D : Type u) [Group D] [Finite D], TheoremA K D)
    (hL : IsComponent G L) (hM : IsComponent G M) (hne : L ≠ M)
    (sL : NaturalSeed ρ A L) (sM : NaturalSeed ρ A M) :
    A ≤ L ⊔ M ∧
      L ⊔ M = (primeToResidual 3 ↥(componentLayer G)).map (componentLayer G).subtype := by
  have he := layer_eq_pair ρ setup theoremA hL hM hne sL sM
  exact ⟨offender_le_pair ρ setup hL hM hne sL sM he,
    residual_eq_pair ρ setup hL hM sL sM he⟩

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.ResidualPlacement
