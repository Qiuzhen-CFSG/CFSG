module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.NonsylowImage
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SmallBackward
public import Theory.GroupAction.SymmetricSixSmallSection

/-!
# Two critical seeds for the nonsylow three-pair branch

A three-pair group and one transposition do not generate S₆. Two crossing
transpositions, related by the rotation of the three pairs, do. Conjugating
this calculation and lifting through the actual quotient constructs an
incident edge and a component element relating two small critical seeds.
Together with the edge kernel these seeds generate the starting stabilizer.
The component element normalizes that kernel and its cube lies in the
starting two-core; no assertion that it fixes the edge vertex is needed.

On either permitted central cover the three-pair group has fixed codimension
two. Thus the full vertex seed has index four over the incident edge seed.
For an eligible backward neighbor, its product with the starting seed has
index at most four over that seed. If both selected critical seeds normalized
this product, it would be normal in the starting stabilizer. The small-section
residual-action theorem would put it in the Baumann slice, contradicting
eligibility. Hence at least one selected critical seed fails normalization.

The final consumer selects that same critical walk. If the backward seed
escapes its predecessor core, it constructs the backward critical walk with
its first edge and every overlapping vertex. Otherwise the backward seed has
a nonzero commutator with the selected walk's full critical kernel. This is
the remaining local branch, not an exclusion of all large distances. The
strict-slice argument, coherent terminal paths and distance-four estimates
remain with the large-distance assembly owner.

The application starts with the original nonsylow MS2(a) radical and the
literal minimum characteristic replacement. It discharges the three-pair
image, symmetric action and central-layer inputs internally, and retains
both moved-cover orders sixteen and thirty-two. All vertices, kernels and
conjugators belong to this replacement's original graph.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the two-seed selection and normalization argument in (5.5)--(5.7),
printed pp.915--919; (3.3)(ii), pp.866--867; characteristic reduction,
pp.932--933. The edge-index and small-section proofs adapt the existing
SymplecticSetup/EdgeLayer and BackwardCritical arguments to the three-pair
image and both full covers. This does not assert all clauses of (5.5) or
(5.7), or identify the graph with the exceptional reconstruction graph.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace CubeSmallSeeds
local notation "S" => Equiv.Perm (Fin 6)
private abbrev t : S := Equiv.swap 1 2
private abbrev r : S := BinaryFlags.pairRotation

private theorem pair_generates :
    D 6 ⊔ zpowers t ⊔ zpowers ((MulAut.conj r) t) = ⊤ := by
  let N := D 6 ⊔ zpowers t ⊔ zpowers ((MulAut.conj r) t)
  have hpair (i : Fin 3) : pairSwap 6 i ∈ N :=
    mem_sup_left (mem_sup_left (pairSwap_mem (n := 6) (m := 3) i (by omega)))
  have ht : t ∈ N := mem_sup_left (mem_sup_right (mem_zpowers _))
  have hrt : Equiv.swap (3 : Fin 6) 4 ∈ N := by
    have he : (MulAut.conj r) t = Equiv.swap 3 4 := by decide +kernel
    exact he ▸ mem_sup_right (mem_zpowers ((MulAut.conj r) t))
  apply top_unique
  rw [←Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 5)]
  apply (closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · exact hpair 0
  · exact ht
  · exact hpair 1
  · exact hrt
  · exact hpair 2

private theorem rotation_normalizes : r ∈ normalizer (D 6 : Set S) := by
  apply (mem_normalizer_iff_map_conj_eq).mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨i,rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) _).mp hx
    have cert : ∀ i : Fin 8, ∃ j : Fin 8,
        dWords j = r * dWords i * r⁻¹ := by decide +kernel
    exact (mem_disjointTranspositions_iff (3 : Fin 4) _).mpr (cert i)
  · rw [card_map_of_injective (MulAut.conj r).injective]

private theorem swap_conjugator (a : S) (ha : a.IsSwap) :
    ∃ g : alternatingGroup (Fin 6), g.val * t * g.val⁻¹ = a := by
  have hc : IsConj t a := Equiv.Perm.isConj_of_cycleType_eq
    ((by decide +kernel : t.cycleType = {2}).trans
      (Equiv.Perm.isSwap_iff_cycleType.mp ha).symm)
  obtain ⟨c,hc⟩ := isConj_iff.mp hc
  rcases Int.units_eq_one_or (Equiv.Perm.sign c) with he | he
  · exact ⟨⟨c,he⟩,hc⟩
  · have hk : c*t ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup,map_mul,he]
      decide +kernel
    refine ⟨⟨c*t,hk⟩,?_⟩
    change (c*t)*t*(c*t)⁻¹=a
    rw [←hc]
    group

private theorem marked_pair (a : S) (ha : a.IsSwap) :
    ∃ k x : S, x ∈ alternatingGroup (Fin 6) ∧ orderOf x=3 ∧
      x ∈ normalizer (((D 6).map (MulAut.conj k).toMonoidHom) : Set S) ∧
      ((D 6).map (MulAut.conj k).toMonoidHom) ⊔ zpowers a ⊔
        zpowers ((MulAut.conj x) a) = ⊤ := by
  obtain ⟨k,hk⟩ := swap_conjugator a ha
  let x := (MulAut.conj k.val) r
  have hx : x ∈ alternatingGroup (Fin 6) := by
    have hr : r ∈ alternatingGroup (Fin 6) := by decide +kernel
    exact (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem r hr k.val
  have hxN : x ∈ normalizer (((D 6).map (MulAut.conj k.val).toMonoidHom) : Set S) :=
    (le_normalizer_map (MulAut.conj k.val).toMonoidHom)
      (mem_map_of_mem _ rotation_normalizes)
  have hro : orderOf r = 3 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  refine ⟨k.val,x,hx,((MulAut.conj k.val).orderOf_eq r).trans hro,hxN,?_⟩
  have hh := congrArg (Subgroup.map (MulAut.conj k.val).toMonoidHom) pair_generates
  have ht : (MulAut.conj k.val).toMonoidHom t = a := hk
  have hrt : (MulAut.conj k.val).toMonoidHom ((MulAut.conj r) t) = (MulAut.conj x) a := by
    rw [←ht]
    change k.val*(r*t*r⁻¹)*k.val⁻¹=
      (k.val*r*k.val⁻¹)*(k.val*t*k.val⁻¹)*(k.val*r*k.val⁻¹)⁻¹
    group
  simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,ht,hrt,
    map_top_of_surjective (MulAut.conj k.val).toMonoidHom (MulAut.conj k.val).surjective] using hh

end CubeSmallSeeds
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
local notation "S" => Equiv.Perm (Fin 6)

include s in
private theorem small_cube_paired_neighbor
    (hc : DistanceTwo.CentralLayer d) (u : S)
    (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ x ∈ Ltilde d.radical (alpha d.radical),
        x ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ∧
        x^3 ∈ Q d.radical (alpha d.radical) ∧
        Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
          stabilizer d.radical (alpha d.radical) := by
  obtain ⟨a,ha,hswap⟩ := small_critical_image_swap s hc p hsmall
  obtain ⟨k,b,hbeven,hbo,hbN,hgen⟩ := CubeSmallSeeds.marked_pair a hswap
  obtain ⟨g,hg⟩ := s.surjective (k*u⁻¹)
  have hbL : b ∈ (replacementComponent d).map s.projection := by
    rw [s.component_image]
    exact hbeven
  obtain ⟨y,hy,hyb⟩ := hbL
  let R₁ := d.radical.map (MulAut.conj g).toMonoidHom
  let A := (Z d.radical a').comap (embedM d.radical)
  let A₁ := A.map (MulAut.conj y).toMonoidHom
  have hR : R₁.map s.projection = (D 6).map (MulAut.conj k).toMonoidHom := by
    have he : s.projection.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (k*u⁻¹)).toMonoidHom.comp s.projection := by
      apply MonoidHom.ext
      intro v
      change s.projection (g*v*g⁻¹)=(k*u⁻¹)*s.projection v*(k*u⁻¹)⁻¹
      rw [map_mul,map_mul,map_inv,hg]
    change (d.radical.map (MulAut.conj g).toMonoidHom).map s.projection = _
    rw [map_map,he,←map_map,hfull,map_map]
    congr 1
    apply MonoidHom.ext
    intro v
    change (k*u⁻¹)*(u*v*u⁻¹)*(k*u⁻¹)⁻¹=k*v*k⁻¹
    group
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hker : s.projection.ker ≤ R₁ := by
    rw [s.projection_kernel,←hQ]
    exact map_mono (replacement_core_le_radical h d)
  have hyN : y ∈ normalizer (R₁ : Set d.overgroup) := by
    have he : R₁ = (R₁.map s.projection).comap s.projection := by
      rw [comap_map_eq,sup_eq_left.mpr hker]
    rw [he]
    apply le_normalizer_comap s.projection
    change s.projection y ∈ normalizer (R₁.map s.projection : Set S)
    rw [hyb,hR]
    exact hbN
  have hA₁ : A₁.map s.projection =
      (A.map s.projection).map (MulAut.conj b).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro v
    change s.projection (y*v*y⁻¹)=b*s.projection v*b⁻¹
    rw [map_mul,map_mul,map_inv,hyb]
  have htop : R₁ ⊔ A ⊔ A₁ = ⊤ := by
    apply map_injective_of_ker_le s.projection
      (hker.trans (le_sup_left.trans le_sup_left)) le_top
    rw [Subgroup.map_sup,Subgroup.map_sup,hR,hA₁,
      map_top_of_surjective s.projection s.surjective]
    apply top_unique
    rw [←hgen]
    exact sup_le_sup (sup_le_sup_left (zpowers_le.mpr ha) _)
      (zpowers_le.mpr (mem_map_of_mem _ ha))
  let f := (embedM d.radical g)⁻¹
  let x := (embedM d.radical y)⁻¹
  let t := act d.radical f (beta d.radical)
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    change f ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have ht : Q d.radical t = R₁.map (embedM d.radical) := by
    rw [Q_act,Q_beta,map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro v
    change f⁻¹*embedM d.radical v*(f⁻¹)⁻¹=embedM d.radical (g*v*g⁻¹)
    simp only [f,inv_inv,map_mul,map_inv]
  have hxL : x ∈ Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d]
    exact mem_map_of_mem _ ((replacementComponent d).inv_mem hy)
  have hAm : A.map (embedM d.radical) = Z d.radical a' :=
    map_comap_eq_self ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
        (stabilizer_m_base d.radical))
  refine ⟨t,?_,x,hxL,?_,?_,?_⟩
  · have hfix : act d.radical f (alpha d.radical)=alpha d.radical := hf
    rw [←hfix]
    exact (adjacent_act_iff d.radical f _ _).mpr (base_adjacent d.radical)
  · rw [ht]
    exact le_normalizer_map (embedM d.radical)
      (mem_map_of_mem _ ((normalizer (R₁ : Set d.overgroup)).inv_mem hyN))
  · have hy3 : y^3 ∈ pCore 2 d.overgroup := by
      rw [←s.projection_kernel,MonoidHom.mem_ker,map_pow,hyb]
      simpa only [hbo] using pow_orderOf_eq_one b
    rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    have hx3 : x^3=embedM d.radical ((y^3)⁻¹) := by simp only [x,inv_pow,map_inv,map_pow]
    rw [hx3]
    exact mem_map_of_mem _ ((pCore 2 d.overgroup).inv_mem hy3)
  · have hh := congrArg (Subgroup.map (embedM d.radical)) htop
    rw [Subgroup.map_sup,Subgroup.map_sup,hAm,←ht,←MonoidHom.range_eq_map] at hh
    have hA₁m : A₁.map (embedM d.radical) = Z d.radical (act d.radical x a') := by
      rw [Z_act,←hAm,map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro v
      change embedM d.radical (y*v*y⁻¹)=x⁻¹*embedM d.radical v*(x⁻¹)⁻¹
      simp only [x,inv_inv,map_mul,map_inv]
    rw [hA₁m] at hh
    exact hh.trans (stabilizer_m_base d.radical).symm

include s in
/-- The full vertex seed has index four over any incident edge seed in
 the three-pair branch, on both the natural and augmentation covers. -/
theorem cube_edge_seed_index (u : S)
    (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    (Z d.radical t).relIndex (Z d.radical a) = 4 := by
  have hbase : (Z d.radical (beta d.radical)).relIndex
      (Z d.radical (alpha d.radical)) = 4 := by
    let := replacementMoved_normal h d
    have hfix : replacementMoved d ⊓ omegaCenter d.radical =
        replacementMoved d ⊓ centralizer (d.radical : Set d.overgroup) := by
      apply le_antisymm
      · exact inf_le_inf_left _ (fun _ hx => (mem_omegaCenter_iff.mp hx).2.2)
      · intro v hv
        exact ⟨hv.1,mem_omegaCenter_iff.mpr ⟨replacement_core_le_radical h d
          ((mem_omegaCenterIn_iff _ _).mp (replacementMoved_le_omegaCenter h d hv.1)).1,
          elemPow_eq_one_of_isElementaryAbelian v hv.1,hv.2⟩⟩
    have hcodim : Representation.BinaryOffender.fixedCodim (coverAction s)
        (d.radical.map s.projection) = 2 := by
      rcases cover_model s with ⟨E,hE⟩ | ⟨E,hE⟩
      · have hh := Representation.BinaryOffender.fixedCodim_map_equivariant
          (coverAction s) (naturalRepresentation (Fin 6)) (MonoidHom.id S) E hE
          (d.radical.map s.projection)
        rw [hh,map_id,hfull,Representation.BinaryOffender.fixedCodim_map_conj]
        exact fixedCodim_D.2.2.2
      · have hh := Representation.BinaryOffender.fixedCodim_map_equivariant
          (coverAction s) (coreRepresentation (Fin 6)) (MonoidHom.id S) E hE
          (d.radical.map s.projection)
        rw [hh,map_id,hfull,Representation.BinaryOffender.fixedCodim_map_conj]
        exact fixedCodim_D.2.2.1
    have hindex : (omegaCenter d.radical).relIndex (replacementMoved d) = 4 := by
      rw [←inf_relIndex_right,inf_comm,hfix,inf_comm,inf_relIndex_right,
        NormalElementaryQuotient.centralizer_index_eq_fixedCodim
          (replacementMoved d) s.projection s.surjective
          (s.projection_kernel.trans (moved_centralizer s).symm)]
      change 2 ^ Representation.BinaryOffender.fixedCodim (coverAction s)
        (d.radical.map s.projection) = 4
      rw [hcodim]
      rfl
    have hseed : Z d.radical (beta d.radical) = (omegaCenter d.radical).map (embedM d.radical) := by
      rw [Z,if_neg (by exact Bool.noConfusion : color d.radical (beta d.radical) ≠ false),
        edgeOmega,Q_beta,omegaCenter_map _ _ (embedM_injective d.radical)]
    rw [hseed,ChapterC.NaturalSixControl.SymplecticSeed.Z_eq_seedHull,
      relIndex_map_map_of_injective _ _ (embedM_injective d.radical),
      DistanceTwo.CentralLayer.seedHull_eq_moved_sup_seed h e hz d,
      relIndex_sup_of_normalizes _ _ (show omegaCenter d.radical ≤
        normalizer (replacementMoved d : Set d.overgroup) from le_normalizer_of_normal)]
    exact hindex
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have he := relIndex_map_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (Z d.radical (beta d.radical)) (Z d.radical (alpha d.radical))
      (MulAut.conj g⁻¹).injective
    rw [←Z_act,←Z_act] at he
    simp only [alpha,beta,act_mVertex,act_hVertex,one_mul] at he
    exact he.trans hbase
  · rw [hg.1] at ha
    cases ha

include s in
private theorem normal_small_radius_le_slice
    (hb : 2 < replacementDistance h d)
    (Y : Subgroup (FreeAmalgam d.radical)) (hYV : Y ≤ V d.radical (alpha d.radical))
    (hYN : stabilizer d.radical (alpha d.radical) ≤ normalizer (Y : Set (FreeAmalgam d.radical)))
    (hindex : (Z d.radical (alpha d.radical)).relIndex Y ≤ 8) :
    Y ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
  let f := embedM d.radical
  let Y₀ := Y.comap f
  let Z₀ := (Z d.radical (alpha d.radical)).comap f
  have hg (m : d.overgroup) : f m ∈ stabilizer d.radical (alpha d.radical) := by
    change f m ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩
  let : Y₀.Normal := ⟨by
    intro v hv m
    change f (m*v*m⁻¹) ∈ Y
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hYN (hg m)) (f v)).mp hv⟩
  let : Z₀.Normal := ⟨by
    intro v hv m
    change f (m*v*m⁻¹) ∈ Z d.radical (alpha d.radical)
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp ((Z_normalized d.radical _) (hg m)) (f v)).mp hv⟩
  have hVQ : V d.radical (alpha d.radical) ≤ Q d.radical (alpha d.radical) :=
    V_le_Q d.radical rfl hb
  have hYG : Y ≤ f.range := (hYV.trans ((replacementGeometry h d).V_local _ rfl hb)).trans_eq
    (stabilizer_m_base d.radical)
  have hYm : Y₀.map f = Y := map_comap_eq_self hYG
  have hZm : Z₀.map f = Z d.radical (alpha d.radical) :=
    map_comap_eq_self ((Z_le_stabilizer d.radical _).trans_eq (stabilizer_m_base d.radical))
  have hYker : Y₀ ≤ s.projection.ker := by
    rw [s.projection_kernel]
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    rw [hYm,←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    exact hYV.trans hVQ
  have hk : IsPGroup 2 s.projection.ker := s.projection_kernel.symm ▸ pCore_isPGroup
  have hi : Z₀.relIndex Y₀ ≤ 8 := by
    rw [relIndex_comap,hYm]
    exact hindex
  have hh := map_mono (f := f)
    (commutator_pResidual_le_of_symmetricSix_small_section s.projection s.surjective hk Y₀ Z₀ hYker hi)
  rw [map_commutator,hYm,hZm,←Ltilde_alpha] at hh
  intro v hv
  apply (mem_B_iff d.radical _ ((replacementGeometry h d).Z_normal _)
    ((replacementGeometry h d).V_local _ rfl hb) v).mpr
  refine ⟨hYV hv,fun l hl => ?_⟩
  rw [commutator_comm] at hh
  exact hh (commutator_mem_commutator hl hv)

include s in
private theorem cube_backward_product_index (u : S)
    (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {c t : Vertex d.radical}
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t) :
    (Z d.radical (alpha d.radical)).relIndex
      (Z d.radical c ⊔ Z d.radical (alpha d.radical)) ≤ 4 := by
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hZaQ : Z d.radical (alpha d.radical) ≤ Q d.radical (alpha d.radical) := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ rfl)
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant _ rfl]
    exact replacementDistance_pos h d
  have hZaN : Z d.radical (alpha d.radical) ≤ normalizer
      (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    (hZaQ.trans (Q_le_adjacent_h d.radical ht hat)).trans
      ((show Q d.radical t ≤ stabilizer d.radical c from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c))
  let := finite_Z d.radical c
  let := finite_Z d.radical (alpha d.radical)
  rw [relIndex_sup_of_normalizes _ _ hZaN]
  exact (relIndex_le_of_le_left (adjacent_Z_le d.radical rfl hat)
    index_ne_zero_of_finite).trans_eq (cube_edge_seed_index s u hfull hcol hct)

include e hz hn in
/-- A prescribed eligible neighbor has two small critical seed candidates.
One component element relates the candidates and normalizes the same edge
kernel. At least one candidate fails to normalize the backward seed product. -/
theorem nonsylow_small_paired_seed_obstruction_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        ∃ x ∈ Ltilde d.radical (alpha d.radical),
          x ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ∧
          x^3 ∈ Q d.radical (alpha d.radical) ∧
          ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (alpha d.radical) (act d.radical x a'),
            (∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i)) ∧
            (Q d.radical (act d.radical x a')).relIndex (Z d.radical (alpha d.radical)) < 4 ∧
            Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
              stabilizer d.radical (alpha d.radical) ∧
            ((¬ Z d.radical a' ≤ normalizer ((Z d.radical (act d.radical g delta) ⊔
              Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) ∨
            (¬ Z d.radical (act d.radical x a') ≤ normalizer ((Z d.radical (act d.radical g delta) ⊔
              Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))) := by
  have hb : 2 < replacementDistance h d := by omega
  obtain ⟨u,hfull⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hns
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull' : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨t,hat,x,hxL,hxN,hx3,hgen⟩ := small_cube_paired_neighbor s hc u hfull' p hsmall
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) ha1 hat
  let c := act d.radical g delta
  have hct : Adjacent d.radical c t := by
    rw [←hgt]
    exact (adjacent_act_iff d.radical g delta (p.walk.getVert 1)).mpr hdelta
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
  have helc : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    apply hel
    change U d.radical (act d.radical g delta) ≤ _ at hh
    rw [U_act,←hB] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh
  have hx : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hxL
  have hfix : act d.radical x (alpha d.radical)=alpha d.radical := hx
  have hq : ∃ q : CriticalPath d.radical (replacementGeometry h d)
      (alpha d.radical) (act d.radical x a'),
      ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) := by
    have hq : ∃ q : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical x (alpha d.radical)) (act d.radical x a'),
        ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) :=
      ⟨p.act x,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
    rwa [hfix] at hq
  obtain ⟨q,hq⟩ := hq
  have hqsmall : (Q d.radical (act d.radical x a')).relIndex
      (Z d.radical (alpha d.radical)) < 4 := by
    conv_lhs => rhs; rw [←hfix]
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hsmall
  refine ⟨t,hat,g,hg,hgt,hct,x,hxL,hxN,hx3,q,hq,hqsmall,hgen,?_⟩
  by_contra! hboth
  apply helc
  let Y := Z d.radical c ⊔ Z d.radical (alpha d.radical)
  have hYN : stabilizer d.radical (alpha d.radical) ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    refine sup_le (sup_le ?_ hboth.1) hboth.2
    apply le_trans (le_inf _ _) (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact (show Q d.radical t ≤ stabilizer d.radical c from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c)
    · exact (show Q d.radical t ≤ stabilizer d.radical (alpha d.radical) from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hat)).trans (Z_normalized d.radical _)
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hYV : Y ≤ V d.radical (alpha d.radical) :=
    sup_le ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist))
      (Z_le_VBall d.radical _ 2)
  exact (DistanceEight.U_le_Z d.radical c).trans (le_sup_left.trans
    (normal_small_radius_le_slice s hb Y hYV hYN
      ((cube_backward_product_index s u hfull' hat hct).trans (by decide))))

include s in
private theorem small_nonnormalized_seed_kernel
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hZG : Z d.radical c ≤ stabilizer d.radical (alpha d.radical))
    (hnorm : ¬ Z d.radical a' ≤ normalizer ((Z d.radical c ⊔
      Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    (¬ Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) ∨
      ⁅Z d.radical c,Z d.radical a' ⊓ Q d.radical (alpha d.radical)⁆ ≠ ⊥ := by
  by_cases hbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))
  · refine Or.inr (fun hzero => hnorm ?_)
    have hmove := small_critical_predecessor_commutator s hc hb p hsmall
      (Z d.radical c) hbad (commutator_eq_bot_iff_le_centralizer.mp hzero)
    have hZmove : ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ≤
        Z d.radical (alpha d.radical) :=
      ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
        (DistanceEight.U_le_Z d.radical _)
    have hh := commutator_sup_le_of_relative_normal (stabilizer d.radical (alpha d.radical))
      (Z d.radical c) (Z d.radical (alpha d.radical)) (Z d.radical a')
      (Z d.radical (alpha d.radical)) (Z_normalized d.radical _) hZG
      (Z_le_stabilizer d.radical _) hmove hZmove
    exact le_normalizer_iff_commutator_le_left.mpr (hh.trans le_sup_right)
  · exact Or.inl hbad

include e hz hn in
/-- The actual nonsylow small-image selection either constructs a backward
critical walk, retaining every overlapping vertex, or has a nonzero
commutator with that same candidate's full critical kernel. The candidate
walk and neighbor transporter are retained for both central covers. -/
theorem nonsylow_small_backward_kernel_alternative_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        ∃ x ∈ Ltilde d.radical (alpha d.radical),
          x ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ∧
          x^3 ∈ Q d.radical (alpha d.radical) ∧
          ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
            ((z=a' ∧ ∀ i, q.walk.getVert i=p.walk.getVert i) ∨
              (z=act d.radical x a' ∧ ∀ i, q.walk.getVert i=act d.radical x (p.walk.getVert i))) ∧
            (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 ∧
            ((∃ v : CriticalPath d.radical (replacementGeometry h d) (act d.radical g delta)
                (q.walk.getVert (q.walk.length-2)), v.walk.getVert 1=t ∧
                ∀ i ≤ q.walk.length-2, v.walk.getVert (i+2)=q.walk.getVert i) ∨
              ⁅Z d.radical (act d.radical g delta),Z d.radical z ⊓ Q d.radical (alpha d.radical)⁆ ≠ ⊥) := by
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨t,hat,g,hg,hgt,hct,x,hx,hxN,hx3,q,hq,hqsmall,_,hbad⟩ :=
    nonsylow_small_paired_seed_obstruction_knownSimple (e := e) (hz := hz) (hn := hn)
      hb4 hns p hsmall hdelta hel
  have hdist : (cosetGraph d.radical).dist (act d.radical g delta) (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist (act d.radical g delta) t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := act d.radical g delta) (v := t) (w := alpha d.radical)
  have hZG : Z d.radical (act d.radical g delta) ≤ stabilizer d.radical (alpha d.radical) :=
    ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)).trans
      ((replacementGeometry h d).V_local _ rfl hb)
  have hcol : color d.radical (act d.radical g delta) = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical (act d.radical g delta) <;>
      cases ht : color d.radical t <;> simp_all
  have hstep (z : Vertex d.radical)
      (r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
      (hrsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
      (hrbad : ¬ Z d.radical z ≤ normalizer ((Z d.radical (act d.radical g delta) ⊔
        Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
      (∃ v : CriticalPath d.radical (replacementGeometry h d) (act d.radical g delta)
          (r.walk.getVert (r.walk.length-2)), v.walk.getVert 1=t ∧
          ∀ i ≤ r.walk.length-2, v.walk.getVert (i+2)=r.walk.getVert i) ∨
        ⁅Z d.radical (act d.radical g delta),Z d.radical z ⊓ Q d.radical (alpha d.radical)⁆ ≠ ⊥ := by
    rcases small_nonnormalized_seed_kernel s hc hb r hrsmall hZG hrbad with hne | hn
    · let w : (cosetGraph d.radical).Walk (act d.radical g delta) (alpha d.radical) :=
        .cons ((cosetGraph_adj d.radical _ _).mpr hct)
          (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
      have hw : w.length=2 := rfl
      let v := r.prepend_two (Nat.le_of_lt hb) hcol w hw hne
      have hvt : v.walk.getVert 1=t := by
        simp only [v,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
          hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
          SimpleGraph.Walk.getVert_zero]
      exact Or.inl ⟨v,hvt,fun i hi => r.prepend_two_overlap _ _ _ _ _ hi⟩
    · exact Or.inr hn
  refine ⟨t,hat,g,hg,hgt,hct,x,hx,hxN,hx3,?_⟩
  rcases hbad with hbad | hbad
  · exact ⟨a',p,Or.inl ⟨rfl,fun _ => rfl⟩,hsmall,
      hstep a' p hsmall hbad⟩
  · exact ⟨act d.radical x a',q,Or.inr ⟨rfl,hq⟩,hqsmall,
      hstep (act d.radical x a') q hqsmall hbad⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
