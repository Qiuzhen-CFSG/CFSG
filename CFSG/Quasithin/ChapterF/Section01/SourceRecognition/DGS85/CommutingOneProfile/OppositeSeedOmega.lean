module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CenterOmegaImage

/-!
# The opposite seed in the exact further beta-core quotient

On the source Cartan-fixed three-vertex path, the path fixer supplements
its edge two-core. The fixer preserves the opposite seed, while the edge
two-core acts trivially on its image modulo Q_alpha. Thus the entire edge
normalizes that image. Involution fusion under the actual Sylow normalizer
identifies it with Omega_1(Z(S/Q_alpha)), for every rank-one model.

Every involution of Q_beta/(Q_alpha intersect Q_beta) consequently belongs
to that same opposite-seed image. Conversely the seed is elementary, giving
equality with the first omega subgroup of this literal further quotient.
The arbitrary-image theorem retains the exact kernel; the quotient theorem
constructs relative normality and uses its actual projection. No assertion
about Omega_1(Q_beta/D), or linear alpha selection, is used.

ReducedOppositeSeedOmega supplies the path supplement from the earlier
source path-product theorem and transports the result to the original
completion. PairCoreDescent uses this exact quotient to descend the pair
splitting and prove (11.3)(h). The (11.4) core product remains separate.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(c,h), printed pp.169--171, using (5.9) and the Cartan-fixed path.
-/

public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem normalizes_seed_core (A N T : Subgroup G)
    (hn : T ≤ normalizer (N : Set G)) (hc : ⁅T,A⁆ ≤ N) :
    T ≤ normalizer ((A ⊔ N : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro t ht x hx
  have ha : A ≤ (A ⊔ N).comap (MulAut.conj t).toMonoidHom := by
    intro a ha
    change t*a*t⁻¹ ∈ A ⊔ N
    have hh := (A ⊔ N).mul_mem (mem_sup_right (hc (commutator_mem_commutator ht ha)))
      (mem_sup_left ha)
    simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hh
  have hN : N ≤ (A ⊔ N).comap (MulAut.conj t).toMonoidHom := by
    intro n hn'
    exact mem_sup_right (le_normalizer_iff.mp hn t ht n hn')
  exact (sup_le ha hN) hx

/-- The opposite seed is the full Sylow omega-center when the chosen
three-vertex fixer supplements the edge two-core, as on the source Cartan path. -/
theorem source_opposite_seed_image_omega_of_supplement
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hcover : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 ⊔
      ((stabilizer (family P) a ⊓ stabilizer (family P) b) ⊓ stabilizer (family P) c) =
        stabilizer (family P) a ⊓ stabilizer (family P) b)
    (T : Sylow 2 (d.localGroup a))
    (hT : (T : Subgroup (d.localGroup a)).map (d.localGroup a).subtype =
      (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) :
    ((Z (family P) c ⊓ Q (family P) b).subgroupOf (d.localGroup a)).map
        (QuotientGroup.mk' (pCore 2 (d.localGroup a))) =
      omegaCenterIn ((T : Subgroup (d.localGroup a)).map
        (QuotientGroup.mk' (pCore 2 (d.localGroup a)))) := by
  let := finite_endpoints h
  let := source_center_elementary h c
  let L := d.localGroup a
  let : Finite L := Finite.of_injective (inclusion (d.local_le a)) (inclusion_injective _)
  let E := stabilizer (family P) a ⊓ stabilizer (family P) b
  let S := E.pCoreIn 2
  let F := Z (family P) c ⊓ Q (family P) b
  let W := F ⊔ Q (family P) a
  let A := F.subgroupOf L
  let q := QuotientGroup.mk' (pCore 2 L)
  change (T : Subgroup L).map L.subtype = S at hT
  change S ⊔ (E ⊓ stabilizer (family P) c) = E at hcover
  have hab := source_critical_one_adjacent hc hb
  have hQS : Q (family P) b ≤ S := by
    simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm
  have hFS : F ≤ S := inf_le_right.trans hQS
  have hFL : F ≤ L := hFS.trans (hT ▸ map_subtype_le _)
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hFL
  have hAT : A ≤ (T : Subgroup L) := by
    intro x hx
    obtain ⟨y,hy,he⟩ := (hT.symm ▸ hFS hx)
    exact (Subtype.ext he : y = x) ▸ hy
  have hdisp : ⁅S,F⁆ ≤ Q (family P) a := by
    have hh := elementary_actor_displacement_le_kernel L q
      (QuotientGroup.mk'_surjective _) Ma T F hFL (hT.symm ▸ hFS)
    rw [hT,QuotientGroup.ker_mk'] at hh
    exact hh.trans_eq (localGroup_core_eq (family P) d a)
  have hSW : S ≤ normalizer (W : Set G) := normalizes_seed_core F _ S
    ((pCoreIn_le 2 E).trans (inf_le_left.trans (stabilizer_normalizes_Q _ a))) hdisp
  have hKW : E ⊓ stabilizer (family P) c ≤ normalizer (W : Set G) := by
    apply (le_inf ?_ ?_).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact (le_inf
        (inf_le_right.trans ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ c)).mp (Z_normal _ c)))
        ((inf_le_left.trans inf_le_right).trans (stabilizer_normalizes_Q _ b))).trans
          inf_normalizer_le_normalizer_inf
    · exact (inf_le_left.trans inf_le_left).trans (stabilizer_normalizes_Q _ a)
  have hEW : E ≤ normalizer (W : Set G) := hcover ▸ sup_le hSW hKW
  have hNW : normalizer (T : Set L) ≤ normalizer (W.subgroupOf L : Set L) := by
    rw [←(source_edge_local_normalizer h d hab Ma T hT).2]
    intro x hx
    exact le_normalizer_comap L.subtype (hEW ⟨d.local_le a x.property,hx⟩)
  have hAW : A ≤ W.subgroupOf L := comap_mono le_sup_left
  have hspan : conjugateSpanBy A (normalizer (T : Set L)) ≤ W.subgroupOf L :=
    conjugateSpanBy_le hAW hNW
  obtain ⟨g,hg,hga⟩ := d.transitive b ⟨a,hab.symm⟩ ⟨c,hbc⟩
  have hgb : g • b = b := d.local_le b hg
  have hcc : IsCriticalPair (family P) c b := by
    simpa only [hga,hgb] using criticalPair_translate (family P) hc g
  have hescape : ¬ F ≤ Q (family P) a :=
    (source_rankOne_seed_escape h hB d hcc hb hab.symm hac.symm Mb).1
  have hne : A.map q ≠ ⊥ := by
    intro he
    have hh := (Subgroup.map_eq_bot_iff _).mp he
    rw [QuotientGroup.ker_mk'] at hh
    apply hescape
    have hm := map_mono (f := L.subtype) hh
    rw [map_subgroupOf_eq_of_le hFL] at hm
    exact hm.trans_eq (localGroup_core_eq (family P) d a)
  have hp := source_rank_one_omega_preimage q (QuotientGroup.mk'_surjective _) Ma T
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal T) A hAT hne
  have hW : W.subgroupOf L = A ⊔ pCore 2 L := by
    have hQL : Q (family P) a ≤ L := by
      rw [←localGroup_core_eq (family P) d a]
      exact map_subtype_le _
    dsimp only [W,A]
    rw [subgroupOf_sup hFL hQL]
    congr 1
    rw [←localGroup_core_eq (family P) d a]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  have hle := congrArg (map q) hp
  have hker : q.ker.map q = ⊥ := (Subgroup.map_eq_bot_iff _).mpr le_rfl
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),Subgroup.map_sup,hker,sup_bot_eq] at hle
  change omegaCenterIn ((T : Subgroup L).map q) = _ at hle
  apply le_antisymm
  · let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
    exact source_rank_one_elementary_le_sylow_omega Ma
      (T.mapSurjective (QuotientGroup.mk'_surjective _)) (A.map q) (map_mono hAT)
  · change omegaCenterIn ((T : Subgroup L).map q) ≤ A.map q
    rw [hle]
    have hm := map_mono (f := q) hspan
    rw [hW,Subgroup.map_sup,show (pCore 2 L).map q = ⊥ from
      (by simpa only [q,QuotientGroup.ker_mk'] using hker),sup_bot_eq] at hm
    exact hm

/-- The exact further quotient at p.170: its first omega subgroup is the
image of the opposite seed. The kernel is the literal adjacent-core intersection. -/
theorem source_opposite_seed_omega_image_of_supplement {K : Type*} [Group K]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hcover : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 ⊔
      ((stabilizer (family P) a ⊓ stabilizer (family P) b) ⊓ stabilizer (family P) c) =
        stabilizer (family P) a ⊓ stabilizer (family P) b)
    (π : Q (family P) b →* K)
    (hker : π.ker = (Q (family P) a ⊓ Q (family P) b).subgroupOf (Q (family P) b)) :
    omegaOneAmbient π.range =
      ((Z (family P) c ⊓ Q (family P) b).subgroupOf (Q (family P) b)).map π := by
  let := finite_endpoints h
  let := source_center_elementary h c
  let L := d.localGroup a
  let : Finite L := Finite.of_injective (inclusion (d.local_le a)) (inclusion_injective _)
  let F := Z (family P) c ⊓ Q (family P) b
  let Qb := Q (family P) b
  let q := QuotientGroup.mk' (pCore 2 L)
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab
  have hQT : Qb ≤ (T : Subgroup L).map L.subtype := by
    rw [hT]
    simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm
  have hQL : Qb ≤ L := hQT.trans (map_subtype_le _)
  let f : Qb →* L := inclusion hQL
  have hfT (x : Qb) : f x ∈ (T : Subgroup L) := by
    obtain ⟨y,hy,he⟩ := hQT x.property
    exact (Subtype.ext he : y = f x) ▸ hy
  have hseed := source_opposite_seed_image_omega_of_supplement h hB d hc hb hbc hac Ma Mb hcover T hT
  let T' := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 (F.subgroupOf Qb) := IsElementaryAbelian.subgroupOf inf_le_right
  let : IsElementaryAbelian 2 ((F.subgroupOf Qb).map π) := IsElementaryAbelian.map π
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    rintro z ⟨x,rfl⟩ hz
    have hx2 : x^2 ∈ π.ker := by simpa only [MonoidHom.mem_ker,map_pow] using hz
    rw [hker] at hx2
    have hcore : (pCore 2 L).map L.subtype = Q (family P) a := localGroup_core_eq (family P) d a
    have hqx : q (f x)^2 = 1 := by
      rw [←map_pow,←map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      have hh : ((x:G)^2) ∈ (pCore 2 L).map L.subtype :=
        hcore.symm ▸ hx2.1
      obtain ⟨u,hu,he⟩ := hh
      exact (Subtype.ext he : u = f (x^2)) ▸ hu
    have hmem : q (f x) ∈ omegaCenterIn (T' : Subgroup (L ⧸ pCore 2 L)) := by
      have ht : q (f x) ∈ (T' : Subgroup (L ⧸ pCore 2 L)) := mem_map_of_mem q (hfT x)
      have hz' := source_rank_one_sylow_square_central Ma T' ⟨q (f x),ht⟩ (Subtype.ext hqx)
      apply (mem_omegaCenterIn_iff _ _).mpr
      refine ⟨ht,?_,hqx⟩
      intro y hy
      exact congrArg Subtype.val (mem_center_iff.mp hz' ⟨y,hy⟩)
    change q (f x) ∈ omegaCenterIn ((T : Subgroup L).map q) at hmem
    change (F.subgroupOf L).map q = omegaCenterIn ((T : Subgroup L).map q) at hseed
    rw [←hseed] at hmem
    obtain ⟨v,hv,he⟩ := hmem
    let vQ : Qb := ⟨v.val,hv.2⟩
    have hdiff : x*vQ⁻¹ ∈ π.ker := by
      rw [hker]
      refine ⟨?_,Qb.mul_mem x.property (Qb.inv_mem vQ.property)⟩
      have hq : q (f x * v⁻¹) = 1 := by
        rw [map_mul,map_inv,he,mul_inv_cancel]
      have hk := (QuotientGroup.eq_one_iff _).mp hq
      have hm := mem_map_of_mem L.subtype hk
      rw [hcore] at hm
      exact hm
    have heπ : π vQ = π x := by
      have hh : π x * (π vQ)⁻¹ = 1 := by simpa only [MonoidHom.mem_ker,map_mul,map_inv] using hdiff
      exact (mul_inv_eq_one.mp hh).symm
    exact ⟨vQ,hv,heπ⟩
  · intro z hz
    exact (omegaOneAmbient_le_iff π.range (omegaOneAmbient π.range)).mp le_rfl z
      (Subgroup.map_le_range _ _ hz) (elemPow_eq_one_of_isElementaryAbelian z hz)

/-- Relative normality and the actual quotient projection are retained in the
source opposite-seed omega identification. -/
theorem source_opposite_seed_omega_quotient_of_supplement
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hcover : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 ⊔
      ((stabilizer (family P) a ⊓ stabilizer (family P) b) ⊓ stabilizer (family P) c) =
        stabilizer (family P) a ⊓ stabilizer (family P) b) :
    let Qb := Q (family P) b
    let I := Q (family P) a ⊓ Qb
    ∃ hN : (I.subgroupOf Qb).Normal, letI := hN
      omegaOneAmbient (⊤ : Subgroup (Qb ⧸ I.subgroupOf Qb)) =
        ((Z (family P) c ⊓ Qb).subgroupOf Qb).map (QuotientGroup.mk' (I.subgroupOf Qb)) := by
  let Qb := Q (family P) b
  let I := Q (family P) a ⊓ Qb
  let hN : (I.subgroupOf Qb).Normal := normal_subgroupOf_of_le_normalizer
    ((le_inf (source_adjacent_core_normalizes_core h (source_critical_one_adjacent hc hb).symm)
      Qb.le_normalizer).trans inf_normalizer_le_normalizer_inf)
  refine ⟨hN,?_⟩
  have hh := source_opposite_seed_omega_image_of_supplement h hB d hc hb hbc hac Ma Mb hcover
    (QuotientGroup.mk' (I.subgroupOf Qb)) (QuotientGroup.ker_mk' _)
  rwa [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at hh


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
