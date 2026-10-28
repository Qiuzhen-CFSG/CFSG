module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.AmbientAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.SmallSeedChoice
public import Theory.GroupTheory.CComponent.SimpleNormalCentralizer

/-!
# Critical endpoint generation before outer removal

The genuine residual--radical factorization transports to every incident
edge. A nontrivial normal image contains the centric simple component, so
conjugates of a critical endpoint generate with that edge even when the
whole quotient has outer automorphisms. The small fixed-seed nonnormality
then gives an escaping conjugate via the original source2.1(vii).

Source: MS93 (2.1)(vii), (3.4), printed pp.856,868. The literal seed-cardinality
and normalization inputs are the separate full-Sylow cover producers.
-/

public section
open Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {M J : Type*} [Group M] [Finite M] [Group J]

theorem local_residual_edge_generation (R : Subgroup M)
    (hgen : pResidual 2 M ⊔ R = ⊤)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    Ltilde R a ⊔ Q R t = stabilizer R a := by
  obtain ⟨g, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adjacent_iff_exists_common R a t).mp hat
  · have hL := Ltilde_act R g (alpha R)
    have hQ := Q_act R g (beta R)
    simp only [alpha,beta,act_mVertex,act_hVertex,one_mul] at hL hQ
    rw [hL,hQ,←Subgroup.map_sup,show Ltilde R (mVertex R 1) =
      (pResidual 2 M).map (embedM R) from Ltilde_alpha R,
      show Q R (hVertex R 1) = R.map (embedM R) from Q_beta R,
      ←Subgroup.map_sup,hgen,←MonoidHom.range_eq_map]
    exact (stabilizer_mVertex R g).symm
  · cases ha

theorem edge_conjugate_generation_of_centric_component (R : Subgroup M)
    (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hgen : pResidual 2 M ⊔ R = ⊤)
    (q : M →* J) (hq : Function.Surjective q) (hk : q.ker = pCore 2 M)
    [((pResidual 2 M).map q).Normal] [IsSimpleGroup ((pResidual 2 M).map q)]
    [IsQuasisimple ((pResidual 2 M).map q)]
    (hcent : centralizer ((pResidual 2 M).map q : Set J) = ⊥)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ stabilizer R a)
    (hnot : ¬ A ≤ Q R a) :
    conjugatesIn A (stabilizer R a) ⊔ Q R t = stabilizer R a := by
  let G := stabilizer R a
  let N := conjugatesIn A G
  have hNG : N ≤ G := conjugatesIn_le A G hA
  have hAN : A ≤ N := by
    intro x hx
    apply le_iSup (fun g : G => rightConjugate A g) (1 : G)
    exact ⟨x,hx,by simp⟩
  let : (N.subgroupOf G).Normal := normal_subgroupOf_of_le_normalizer
    (conjugatesIn_normalized A G)
  obtain ⟨i,hi,hir,hiL,_,hiQ⟩ := SourceComparison.vertex_coordinates_with_kernel R hp hQR ha
  let κ := ElementaryMovedCover.embeddedQuotient q i hi G hir
  have hκ := ElementaryMovedCover.embeddedQuotient_surjective q i hi G hir hq
  have hκQ : κ.ker.map G.subtype = Q R a := by
    rw [ElementaryMovedCover.embeddedQuotient_kernel,hk]
    exact hiQ
  have hκL : ((Ltilde R a).subgroupOf G).map κ = (pResidual 2 M).map q := by
    rw [←hiL]
    exact ElementaryMovedCover.embeddedQuotient_subgroup q i hi G hir _
  let : ((N.subgroupOf G).map κ).Normal := Normal.map inferInstance κ hκ
  have hNne : (N.subgroupOf G).map κ ≠ ⊥ := by
    intro hz
    have hNK := (Subgroup.map_eq_bot_iff _).mp hz
    apply hnot
    intro x hx
    rw [←hκQ]
    exact mem_map_of_mem G.subtype
      (hNK (show (⟨x,hNG (hAN hx)⟩ : G) ∈ N.subgroupOf G from hAN hx))
  have hB := simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot
    ((pResidual 2 M).map q) (Group.IsPerfect.not_isMulCommutative _)
    hcent ((N.subgroupOf G).map κ) hNne
  have hLN : (Ltilde R a).subgroupOf G ≤ N.subgroupOf G ⊔ κ.ker := by
    rw [←comap_map_eq]
    exact map_le_iff_le_comap.mp (hκL ▸ hB)
  have hL : Ltilde R a ≤ N ⊔ Q R a := by
    have hh := map_mono (f := G.subtype) hLN
    simpa only [Subgroup.map_sup,map_subgroupOf_eq_of_le (show Ltilde R a ≤ G from Ltilde_le_stabilizer a),
      map_subgroupOf_eq_of_le hNG,hκQ] using hh
  have ht : color R t = true := by
    have hh := adjacent_color_ne R hat
    cases he : color R t <;> simp_all
  have hQtG : Q R t ≤ G := fun _ hx => hx.2 a (adjacent_symm R hat)
  apply le_antisymm (sup_le hNG hQtG)
  change stabilizer R a ≤ N ⊔ Q R t
  rw [←local_residual_edge_generation R hgen ha hat]
  exact sup_le (hL.trans (sup_le_sup_left (Q_le_adjacent_h R ht hat) N)) le_sup_right

theorem local_residual_projection (R : Subgroup M)
    (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (q : M →* J) (hk : q.ker = pCore 2 M)
    {a : Vertex R} (ha : color R a = false) :
    ∃ r : Ltilde R a →* (pResidual 2 M).map q,
      Function.Surjective r ∧ IsPGroup 2 r.ker := by
  obtain ⟨i,hi,_,hiL,_,_⟩ := SourceComparison.vertex_coordinates_with_kernel R hp hQR ha
  let e : pResidual 2 M ≃* Ltilde R a :=
    ((pResidual 2 M).equivMapOfInjective i hi).trans (MulEquiv.subgroupCongr hiL)
  let r := (q.subgroupMap (pResidual 2 M)).comp e.symm.toMonoidHom
  refine ⟨r,(q.subgroupMap_surjective _).comp e.symm.surjective,?_⟩
  have hker : IsPGroup 2 (q.subgroupMap (pResidual 2 M)).ker := by
    rw [Subgroup.ker_subgroupMap,hk]
    exact pCore_isPGroup.comap_subtype
  exact hker.comap_of_injective e.symm.toMonoidHom e.symm.injective

theorem exists_critical_escape_of_bad_small_seed (R : Subgroup M)
    (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hgen : pResidual 2 M ⊔ R = ⊤)
    (q : M →* J) (hq : Function.Surjective q) (hk : q.ker = pCore 2 M)
    [Finite J] [((pResidual 2 M).map q).Normal]
    [IsSimpleGroup ((pResidual 2 M).map q)] [IsQuasisimple ((pResidual 2 M).map q)]
    (hcent : centralizer ((pResidual 2 M).map q : Set J) = ⊥)
    (hS : 17 ∣ Nat.card ((pResidual 2 M).map q))
    (geometry : Geometry R) (hb : 0 < geometry.b R) (hC : EdgeCentralizerCondition R)
    {a d t e : Vertex R} (ha : color R a = false) (hd : color R d = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hcrit : CriticalPair R a e (geometry.exists_critical a ha))
    (Y : Subgroup (FreeAmalgam R)) (hY : Y ≤ U R d)
    (hcard : Nat.card Y ≤ 64)
    (hbad : ¬ ⁅Y,Ltilde R a⁆ ≤ Z R a)
    (hYn : Q R t ≤ normalizer (Y : Set (FreeAmalgam R))) :
    ∃ g ∈ stabilizer R a,
      ¬ Z R e ≤ normalizer ((Y ⊔ Z R a).map (MulAut.conj g⁻¹).toMonoidHom) := by
  have ht : color R t = true := by
    have hh := adjacent_color_ne R hat
    cases he : color R t <;> simp_all
  have hQG : Q R t ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hat)
  have hZaQ : Z R a ≤ Q R a :=
    (geometry.omega_bound a ha (by rwa [geometry.distance_constant a ha])).trans (omegaCenter_le _)
  have hZdQ : Z R d ≤ Q R d :=
    (geometry.omega_bound d hd (by rwa [geometry.distance_constant d hd])).trans (omegaCenter_le _)
  have hYQ : Y ≤ Q R t := (hY.trans (U_le_Z d)).trans (hZdQ.trans (Q_le_adjacent_h R ht hdt))
  have hXQ : Y ⊔ Z R a ≤ Q R t := sup_le hYQ (hZaQ.trans (Q_le_adjacent_h R ht hat))
  have hXG := hXQ.trans hQG
  have hNQ : Q R t ≤ normalizer ((Y ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) :=
    (le_inf hYn (hQG.trans (Z_normalized R a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup Y (Z R a))
  have hQt : IsPGroup 2 (Q R t) := by
    obtain ⟨g, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adjacent_iff_exists_common R a t).mp hat
    · have hh := Q_act R g (beta R)
      simp only [beta,act_hVertex,one_mul] at hh
      rw [hh,show Q R (hVertex R 1) = R.map (embedM R) from Q_beta R]
      exact (hp.map _).map _
    · cases ha
  obtain ⟨r,hr,hrker⟩ := local_residual_projection R hp hQR q hk ha
  let := finite_stabilizer R d
  let := finite_stabilizer R a
  let : Finite Y := Finite.of_injective
    (inclusion ((hY.trans (U_le_Z d)).trans (Z_le_stabilizer R d))) (inclusion_injective _)
  let : Finite (Z R a) := Finite.of_injective
    (inclusion (Z_le_stabilizer R a)) (inclusion_injective _)
  have hidx : (Z R a).relIndex (Y ⊔ Z R a) ≤ 64 := by
    have hn := (hZaQ.trans (Q_le_adjacent_h R ht hat)).trans hYn
    rw [relIndex_sup_of_normalizes Y (Z R a) hn]
    exact (Nat.le_of_dvd (Nat.card_pos (α := Y)) ((Z R a).relIndex_dvd_card Y)).trans hcard
  have hnotN : ¬ ((Y ⊔ Z R a).subgroupOf (stabilizer R a)).Normal := by
    intro hn
    exact bad_seed_join_not_normalized geometry hb ha hd hat hdt hQt r hr hrker hS Y hY hidx hbad
      ((normal_subgroupOf_iff_le_normalizer hXG).mp hn)
  have hbe : 0 < criticalDistance R a (geometry.exists_critical a ha) := by
    rwa [geometry.distance_constant a ha]
  have he := critical_endpoint_color R a ha _ hcrit
  have hrev := critical_reverse R geometry hC a ha hbe e he hcrit
  have hgenerate := edge_conjugate_generation_of_centric_component R hp hQR hgen
    q hq hk hcent ha hat (Z R e) (critical_Z_le_stabilizer R geometry a ha hbe hcrit) hrev.2
  obtain ⟨g,hg,hg₁,_⟩ := source_2_1_vii R a e t ha hat (Y ⊔ Z R a) (Y ⊔ Z R a)
    hXQ hXQ (normal_subgroupOf_of_le_normalizer hNQ)
    (normal_subgroupOf_of_le_normalizer hNQ) hnotN hnotN hgenerate
  exact ⟨g,hg,hg₁⟩

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
