module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ResidualConstituent
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NeighborSylow
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.QuotientFaithfulness
public import Theory.Representation.NormalSylowSeed
public import Theory.SpecificGroups.SL2.ResidualSylowGeneration

/-!
# Whole residual descent from the sharp reciprocal indices

The original actor index equals the linear field order, and its centralizer
index is at most that order. An irreducible constituent therefore accounts
for all actor displacement. The remaining quotient is fixed by the
2-residual, because the actor has a full Sylow image in SL₂.

The neighboring core is normal in the preimage Sylow and its fixed space
generates the original section. If that fixed space extended beyond the
constituent, a fixed vector in its quotient would lift to a vector fixed by
the whole Sylow: its core displacements form an invariant subspace of the
constituent fixed by a nontrivial Sylow image, hence vanish. Odd-coset
averaging then gives a nonzero residual-fixed vector, a contradiction.
Thus the constituent is the whole section, and the original action descends
through the actual local two-core quotient.

The source application keeps the earlier 6.5 obstruction explicit. It needs
no opposite-type marking or later 9.4 natural-center conclusion. The
reciprocal consumer discharges both numerical premises from the proved
original indices. Source: DGS, Groups and Graphs (1985), 9.3, printed p.142,
and the corrected fixed-space-generation hypothesis of 5.12, pp.113--115.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

private theorem residual_le_normal_of_linear_sylow_image
    {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
    (q : H →* SL(2,F)) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (N : Subgroup H) [N.Normal] (T : Sylow 2 SL(2,F))
    (hT : (T : Subgroup SL(2,F)) ≤ N.map q) : pResidual 2 H ≤ N := by
  let : (N.map q).Normal := (inferInstance : N.Normal).map q hq
  obtain ⟨g,_,hg⟩ := Matrix.SpecialLinearGroup.exists_residual_conjugate_sylow_image_sup_eq_top
    T (MonoidHom.id SL(2,F)) Function.surjective_id
  simp only [Subgroup.map_id] at hg
  have hmap : N.map q = ⊤ := by
    apply top_unique
    rw [←hg]
    apply sup_le hT
    rintro _ ⟨x,hx,rfl⟩
    exact (inferInstance : (N.map q).Normal).conj_mem x (hT hx) g
  have hsup : N ⊔ q.ker = ⊤ := by
    simpa only [comap_map_eq,comap_top] using congrArg (Subgroup.comap q) hmap
  exact sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top N q.ker hk hsup⟩

private theorem linear_saturated_descent
    {H F W : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) H W) (q : H →* SL(2,F))
    (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (E : Subgroup H) {x y n : ℕ}
    (d : ResidualConstituent ρ q (E.map q) x y)
    (hn : 0 < n) (hF : Nat.card F = 2^n) (hf : Function.Injective d.action)
    (B : Subgroup H) (T : Sylow 2 SL(2,F)) (hT : B.map q = T)
    (hnormal : (T : Subgroup SL(2,F)).comap q ≤ normalizer (B : Set H))
    (hzero : fixedSpace ρ (pResidual 2 H) = ⊥) (hgen : GeneratedByFixedSpace ρ B)
    (hactor : x = Nat.card F) (hupper : Nat.card (W ⧸ fixedSpace ρ E) ≤ Nat.card F) :
    ∃ σ : Representation (ZMod 2) SL(2,F) W, ∀ l, σ (q l) = ρ l := by
  let : Finite d.space.toSubmodule := d.finiteSpace
  have he : d.action.comp q = d.space.toRepresentation := MonoidHom.ext d.descent
  have hi : d.space.toRepresentation.IsIrreducible :=
    he ▸ (irreducible_comp_surjective_iff q hq d.action).mpr d.irreducible
  let := hi
  let S : Sylow 2 H := T.comapOfKerIsPGroup q hp (by rw [MonoidHom.range_eq_top.mpr hq]; exact le_top)
  have hS : q.ker ⊔ B = S := by
    have hh := congrArg (Subgroup.comap q) hT
    rw [comap_map_eq] at hh
    exact (sup_comm _ _).trans hh
  have hBK : ¬ d.space.toSubmodule ≤ fixedSpace ρ B := by
    intro hh
    have htker : (T : Subgroup SL(2,F)) ≤ d.action.ker := by
      rw [←hT]
      rintro _ ⟨l,hl,rfl⟩
      apply LinearMap.ext
      intro w
      rw [d.descent]
      exact Subtype.ext (hh w.property ⟨l,hl⟩)
    have hbot : (T : Subgroup SL(2,F)) = ⊥ :=
      bot_unique (htker.trans_eq ((MonoidHom.ker_eq_bot_iff _).mpr hf))
    have hcT := Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).symm.toEquiv
    change Nat.card (T : Subgroup SL(2,F)) = Nat.card F at hcT
    rw [hbot,card_bot,hF] at hcT
    have hg : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
    omega
  have hkill : q.ker ≤ d.space.toRepresentation.ker :=
    normal_p_subgroup_le_ker d.space.toRepresentation q.ker hp
  obtain ⟨R,hER⟩ := d.elementary.isPGroup.exists_le_sylow
  have hER' : E.map q = (R : Subgroup SL(2,F)) := by
    apply eq_of_le_of_card_ge hER
    exact (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 R).symm.toEquiv).le.trans_eq
      (d.actorCard.trans hactor).symm
  have hEne : E.map q ≠ ⊥ := by
    intro hz
    have hh := d.actorCard.trans hactor
    change Nat.card (E.map q) = Nat.card F at hh
    rw [hz,card_bot,hF] at hh
    have hg : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
    omega
  have hlo := sl2_actor_field_bound d.action hf R (E.map q) hER hEne hF
  let : Finite (W ⧸ fixedSpace ρ E) := Finite.of_surjective _ (fixedSpace ρ E).mkQ_surjective
  let : Finite (d.space.toSubmodule ⧸ fixedSpace d.action (E.map q)) :=
    Finite.of_surjective _ (fixedSpace d.action (E.map q)).mkQ_surjective
  rw [hF,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hlo hupper
  have hlowdim : n ≤ fixedCodim d.space.toRepresentation E := by
    change n ≤ Module.finrank (ZMod 2) (_ ⧸ fixedSpace d.space.toRepresentation E)
    rw [←he,fixedSpace_comp_map]
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hlo
  have huppdim : fixedCodim ρ E ≤ n :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hupper
  have hsat : fixedCodim d.space.toRepresentation E = fixedCodim ρ E :=
    le_antisymm (fixedCodim_subrepresentation_le ρ d.space E) (huppdim.trans hlowdim)
  have hEkill : E ≤ d.space.quotientRepresentation.ker := by
    intro l hl
    apply LinearMap.ext
    exact quotient_trivial_of_sup_fixedSpace ρ d.space E
      ((fixedCodim_subrepresentation_eq_iff ρ d.space E).mp hsat) l hl
  have hquot : pResidual 2 H ≤ d.space.quotientRepresentation.ker :=
    residual_le_normal_of_linear_sylow_image q hq hp _ R (hER' ▸ map_mono hEkill)
  have htop := constituent_eq_top_of_normal_sylow_seed ρ d.space q.ker B S hS hnormal hkill
    hBK hquot hzero hgen
  have hwhole : q.ker ≤ ρ.ker := by
    intro k hk'
    apply LinearMap.ext
    intro w
    have hw : w ∈ d.space.toSubmodule := htop ▸ Submodule.mem_top
    exact congrArg Subtype.val (LinearMap.congr_fun (hkill hk') (⟨w,hw⟩ : d.space.toSubmodule))
  let f := QuotientGroup.quotientKerEquivOfSurjective q hq
  let σ := (quotientOfLEKer ρ q.ker hwhole).comp f.symm.toMonoidHom
  refine ⟨σ,?_⟩
  intro l
  change quotientOfLEKer ρ q.ker hwhole (f.symm (f (QuotientGroup.mk' q.ker l))) = ρ l
  rw [f.symm_apply_apply]
  rfl


open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open Representation.NormalElementaryQuotient
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- Sharp original indices force descent of the whole residual section.
No opposite-type linear marking or neighboring natural module is assumed. -/
theorem reduced_critical_saturated_residual_action (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (hob : ¬ stabilizer (Reduction.reducedFamily L S₀) a ≤ normalizer
      ((Q (Reduction.reducedFamily L S₀) beta ⊓ Q (Reduction.reducedFamily L S₀) a :
        Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hactor : (Q (Reduction.reducedFamily L S₀) beta).relIndex
      (V (Reduction.reducedFamily L S₀) a' 1) = Nat.card F)
    (hindex : (centralizer (V (Reduction.reducedFamily L S₀) a' 1 :
      Set (Reduction.G₀ L S₀))).relIndex (V (Reduction.reducedFamily L S₀) beta 1) ≤ Nat.card F) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ beta
    let A := (V Γ beta 1).subgroupOf H
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    letI : ∀ i, Finite (Γ i) := finite_endpoints (Reduction.reduced_triple h)
    letI := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
    ∃ hb2 : 2 < b Γ,
      letI := neighborhoodIn_elementary Γ (Reduction.reduced_triple h).generate
        (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
        (Reduction.reduced_kernel_sylow h) beta hb2 H
      ∃ σ : Representation (ZMod 2) SL(2,F) (FixedQuotient A (pResidual 2 H)),
        (∀ l : H, σ (q l) = fixedQuotientAction A (pResidual 2 H) l) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let A := (V Γ beta 1).subgroupOf H
  let B := (Q Γ a).subgroupOf H
  let E := (V Γ a' 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  obtain ⟨hb2,⟨d⟩⟩ := reduced_critical_residual_constituent h hc hab hd hb hcomm e
  refine ⟨hb2,?_⟩
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  let W := FixedQuotient A (pResidual 2 H)
  let ρ := fixedQuotientAction A (pResidual 2 H)
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  obtain ⟨_,hnz,⟨c⟩,hzero,hVH,hquad,hBH,hgen⟩ :=
    reduced_critical_residual_actor_generated h hc hab hd hb hcomm
  have hVL : V Γ beta 1 ≤ H := neighbor_le_graphLocalGroup ht
    (Reduction.reduced_kernel_sylow h) beta beta hb
    (show (graph Γ).dist beta beta + 1 ≤ b Γ by simpa only [SimpleGraph.dist_self,zero_add] using hb.le)
  let : Finite (V Γ beta 1) := Finite.of_injective (inclusion hVL) (inclusion_injective _)
  let : Finite W := Finite.of_surjective (fun x : V Γ beta 1 => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let : Finite d.space.toSubmodule := d.finiteSpace
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hp : IsPGroup 2 q.ker := hk.symm ▸ pCore_isPGroup
  let : d.action.IsIrreducible := d.irreducible
  let : Nontrivial d.space.toSubmodule := Subrepresentation.irreducible_module_nontrivial d.action
  have hf := CommutingNontrivial.linear_quotient_action_faithful hn hF e d.action d.residualFixed
  obtain ⟨T,hT,hTf⟩ := linear_neighbor_core_sylow_image ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hab.symm
    (core_escape_of_intersection_obstruction Γ hob) e
  have hnormal : (T : Subgroup SL(2,F)).comap q ≤ normalizer (B : Set H) := by
    intro l hl
    apply le_normalizer_comap H.subtype
    apply stabilizer_normalizes_Q Γ a
    exact (hTf l).mp ((T : Subgroup SL(2,F)).le_normalizer hl)
  have hu := BinaryConjugationSection.fixed_quotient_card_le_centralizer_index
    ρ (MonoidHom.id H) c (V Γ a' 1)
  simp only [Subgroup.map_id] at hu
  exact linear_saturated_descent ρ q hq hp E d hn hF hf B T hT hnormal hzero hgen
    hactor (hu.trans hindex)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
