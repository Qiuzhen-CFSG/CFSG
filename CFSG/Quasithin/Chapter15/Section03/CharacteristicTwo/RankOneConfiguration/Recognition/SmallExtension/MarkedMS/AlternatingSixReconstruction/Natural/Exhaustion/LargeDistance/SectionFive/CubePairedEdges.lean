module
public import Theory.GroupTheory.NormalizedSupCard
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePairedChain
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePairedChain
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeCommonFixer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSmallSeeds
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSmallKernel

/-!
# Paired backward shifts with their original first edge retained

The three-pair selector can keep the original first-edge kernel as well
as the two previous generating pairs. In six-letter coordinates choose the
conjugator of the critical transposition inside the normalizer of that
original three-pair group. Its cubic therefore normalizes the original
kernel. The original and selected matchings form a six-cycle, so their
transpositions generate S₆. Lift this equality through the literal
projection and two-core, and retain it in both orientations of the backward
selection. The inverse orientation uses the same cubic normalizer, not a
newly chosen path. Transport preserves all three joins on the actual graph.

The original and selected edge seeds consequently have central intersection
at the starting component. Its critical line has order two and is noncentral
there, so it misses the selected edge seed. Successive selected critical
lines are therefore disjoint. Their join has order four in the full common
seed, including either moved cover and every central attachment. Three
successive shifts give an actual four-group R₄R₆ centralizing the full radius
at the R₄ endpoint. This strengthens the earlier two separate line bounds;
it does not establish the strict endpoint-radius index or the two
intermediate-stabilizer noncentrality statements required for the final
contradiction.

The private imports are an intentional continuation of the local selector
and transport proofs. They reuse the small normal-section, finite matching,
and conjugation helpers without changing the earlier public boundaries.
All consumers use the original nonsylow radical and minimum characteristic
replacement. No natural graph, core or quotient is identified with an
exceptional reconstruction graph.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the simultaneous selections in (5.6)--(5.11), printed pp.917--924,
and the R₄/R₆ endpoint-radius centralization on p.924.
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
namespace CubePairedEdges
local notation "S" => Equiv.Perm (Fin 6)
open CubeCommonFixer

private theorem original_kernels_generate : D 6 ⊔ D' = ⊤ := by
  let v : S := Equiv.swap 2 4 * Equiv.swap 3 5 * Equiv.swap 4 5
  apply chain_generates v
  intro i
  have cert : ∀ i : Fin 5, ∃ j : Fin 3,
      (MulAut.conj v) (Equiv.swap i.castSucc i.succ) = pairSwap 6 j ∨
      (MulAut.conj v) (Equiv.swap i.castSucc i.succ) = (MulAut.conj k) (pairSwap 6 j) := by
    decide +kernel
  obtain ⟨j,hj | hj⟩ := cert i
  · rw [hj]; exact mem_sup_left (pairSwap_mem (n := 6) (m := 3) j (by omega))
  · rw [hj]; exact mem_sup_right (mem_map_of_mem _ (pairSwap_mem (n := 6) (m := 3) j (by omega)))

private theorem marked_edge_pair (u a : S)
    (haD : a ∈ (D 6).map (MulAut.conj u).toMonoidHom) (ha : a.IsSwap) :
    ∃ v x : S, x ∈ alternatingGroup (Fin 6) ∧ orderOf x = 3 ∧
      x ∈ normalizer ((D 6).map (MulAut.conj u).toMonoidHom : Set S) ∧
      ((D 6).map (MulAut.conj u).toMonoidHom) ⊔
        ((D 6).map (MulAut.conj v).toMonoidHom) = ⊤ ∧
      ((D 6).map (MulAut.conj v).toMonoidHom) ⊔ zpowers a ⊔
        zpowers ((MulAut.conj x) a) = ⊤ ∧
      ((D 6).map (MulAut.conj v).toMonoidHom) ⊔
        ((D 6).map (MulAut.conj v).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = ⊤ := by
  obtain ⟨a₀,ha₀,rfl⟩ := haD
  have hs : a₀.IsSwap := by
    apply Equiv.Perm.isSwap_iff_cycleType.mpr
    have hi : (MulAut.conj u a₀).cycleType = a₀.cycleType :=
      Equiv.Perm.cycleType_conj
    simpa only [MulEquiv.coe_toMonoidHom,hi] using Equiv.Perm.isSwap_iff_cycleType.mp ha
  obtain ⟨i,rfl⟩ := CubeSmallKernel.swaps_in_cube a₀ ha₀ hs
  let c := u*r^i.val
  let x := (MulAut.conj c) r
  have hct : (MulAut.conj c).toMonoidHom t = (MulAut.conj u) (pairSwap 6 i) := by
    have hi : ∀ i : Fin 3, (MulAut.conj (r^i.val)) t = pairSwap 6 i := by decide +kernel
    change (u*r^i.val)*t*(u*r^i.val)⁻¹=u*(pairSwap 6 i)*u⁻¹
    rw [←hi i]
    simp only [MulAut.conj_apply,mul_inv_rev,mul_assoc]
  have hrN : r ∈ normalizer (D 6 : Set S) := CubeSmallSeeds.rotation_normalizes
  have hD : (D 6).map (MulAut.conj c).toMonoidHom =
      (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [show c=u*r^i.val from rfl,←conjugate_twice]
    congr 1
    exact mem_normalizer_iff_map_conj_eq.mp ((normalizer (D 6 : Set S)).pow_mem hrN i.val)
  have hx : x ∈ alternatingGroup (Fin 6) :=
    (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem r (by decide +kernel) c
  have hxo : orderOf x = 3 := ((MulAut.conj c).orderOf_eq r).trans
    (orderOf_eq_prime (by decide +kernel) (by decide +kernel))
  have hxN : x ∈ normalizer ((D 6).map (MulAut.conj u).toMonoidHom : Set S) := by
    rw [←hD]
    exact le_normalizer_map (MulAut.conj c).toMonoidHom (mem_map_of_mem _ hrN)
  have hD' : D'.map (MulAut.conj c).toMonoidHom = (D 6).map (MulAut.conj (c*k)).toMonoidHom :=
    conjugate_twice _ _ _
  have hrt : (MulAut.conj c).toMonoidHom ((MulAut.conj r) t) =
      (MulAut.conj x) ((MulAut.conj u) (pairSwap 6 i)) := by
    rw [←hct]
    change c*(r*t*r⁻¹)*c⁻¹=(c*r*c⁻¹)*(c*t*c⁻¹)*(c*r*c⁻¹)⁻¹
    group
  have hDx : (D'.map (MulAut.conj r).toMonoidHom).map (MulAut.conj c).toMonoidHom =
      (D'.map (MulAut.conj c).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    rw [conjugate_twice D' r c,conjugate_twice D' c x]
    have he : c*r=x*c := by change c*r=(c*r*c⁻¹)*c; group
    rw [he]
  refine ⟨c*k,x,hx,hxo,hxN,?_,?_,?_⟩
  · have hh := congrArg (Subgroup.map (MulAut.conj c).toMonoidHom) original_kernels_generate
    simpa only [Subgroup.map_sup,hD,hD',map_top_of_surjective (MulAut.conj c).toMonoidHom
      (MulAut.conj c).surjective] using hh
  · have hh := congrArg (Subgroup.map (MulAut.conj c).toMonoidHom) pair_generates
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,hct,hrt,hD',MulEquiv.coe_toMonoidHom,
      map_top_of_surjective (MulAut.conj c).toMonoidHom (MulAut.conj c).surjective] using hh
  · apply inverse_pair
    have hh := congrArg (Subgroup.map (MulAut.conj c).toMonoidHom) kernels_generate
    simpa only [Subgroup.map_sup,hDx,hD',
      map_top_of_surjective (MulAut.conj c).toMonoidHom (MulAut.conj c).surjective] using hh

end CubePairedEdges

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
local notation "S" => Equiv.Perm (Fin 6)

include s in
/-- Lift the compatible selector, retaining the original first-edge
kernel and the cubic that normalizes it. -/
private theorem aligned_cube_neighbor
    (hc : DistanceTwo.CentralLayer d) (u : S)
    (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (E : Subgroup d.overgroup) (w : S)
    (hEm : E.map (embedM d.radical) = Q d.radical (p.walk.getVert 1))
    (hEi : E.map s.projection = (D 6).map (MulAut.conj w).toMonoidHom)
    (hEk : s.projection.ker ≤ E)
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical (p.walk.getVert 1) ⊔ Q d.radical t = stabilizer d.radical (alpha d.radical) ∧
      ∃ x ∈ Ltilde d.radical (alpha d.radical),
        Q d.radical t ⊔ (Q d.radical t).map (MulAut.conj x).toMonoidHom =
          stabilizer d.radical (alpha d.radical) ∧
        x ∈ normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ∧
        x^3 ∈ Q d.radical (alpha d.radical) ∧
        Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
          stabilizer d.radical (alpha d.radical) := by
  obtain ⟨a,ha,hswap⟩ := small_critical_image_swap s hc p hsmall
  have hAe : (Z d.radical a').comap (embedM d.radical) ≤ E := by
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    rw [hEm]
    apply (map_comap_le _ _).trans
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(replacementGeometry h d).distance_constant a' p.end_color]
    have hl : p.walk.length = replacementDistance h d := p.length_eq_b
    have hp := replacementDistance_pos h d
    change p.walk.length-1 < replacementDistance h d
    omega
  have haE : a ∈ (D 6).map (MulAut.conj w).toMonoidHom :=
    hEi ▸ map_mono hAe ha
  obtain ⟨k,b,hbeven,hbo,hbE,hanchor,hgen,hpair⟩ := CubePairedEdges.marked_edge_pair w a haE hswap
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
  have hRpair : R₁ ⊔ R₁.map (MulAut.conj y⁻¹).toMonoidHom = ⊤ := by
    apply map_injective_of_ker_le s.projection (hker.trans le_sup_left) le_top
    rw [Subgroup.map_sup,map_top_of_surjective s.projection s.surjective]
    have he : (R₁.map (MulAut.conj y⁻¹).toMonoidHom).map s.projection =
        (R₁.map s.projection).map (MulAut.conj b⁻¹).toMonoidHom := by
      rw [map_map (K := R₁) s.projection (MulAut.conj y⁻¹).toMonoidHom,
        map_map (K := R₁) (MulAut.conj b⁻¹).toMonoidHom s.projection]
      apply congrArg (fun f => R₁.map f)
      apply MonoidHom.ext
      intro v
      change s.projection (y⁻¹*v*(y⁻¹)⁻¹)=b⁻¹*s.projection v*(b⁻¹)⁻¹
      simp only [map_mul,map_inv,hyb]
    rw [he,hR]
    exact hpair
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
  have hEtop : E ⊔ R₁ = ⊤ := by
    apply map_injective_of_ker_le s.projection (hEk.trans le_sup_left) le_top
    rw [Subgroup.map_sup,hEi,hR,map_top_of_surjective s.projection s.surjective]
    exact hanchor
  have hyE : y ∈ normalizer (E : Set d.overgroup) := by
    have he : E = (E.map s.projection).comap s.projection := by
      rw [comap_map_eq,sup_eq_left.mpr hEk]
    rw [he]
    apply le_normalizer_comap s.projection
    change s.projection y ∈ normalizer (E.map s.projection : Set S)
    rw [hyb,hEi]
    exact hbE
  refine ⟨t,?_,?_,x,hxL,?_,?_,?_,?_⟩
  · have hfix : act d.radical f (alpha d.radical)=alpha d.radical := hf
    rw [←hfix]
    exact (adjacent_act_iff d.radical f _ _).mpr (base_adjacent d.radical)
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hEtop
    rw [Subgroup.map_sup,hEm,←ht,←MonoidHom.range_eq_map] at hh
    exact hh.trans (stabilizer_m_base d.radical).symm
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hRpair
    rw [Subgroup.map_sup,←ht,←MonoidHom.range_eq_map] at hh
    have he : (R₁.map (MulAut.conj y⁻¹).toMonoidHom).map (embedM d.radical) =
        (Q d.radical t).map (MulAut.conj x).toMonoidHom := by
      rw [ht,map_map (K := R₁) (embedM d.radical) (MulAut.conj y⁻¹).toMonoidHom,
        map_map (K := R₁) (MulAut.conj x).toMonoidHom (embedM d.radical)]
      apply congrArg (fun f => R₁.map f)
      apply MonoidHom.ext
      intro v
      change embedM d.radical (y⁻¹*v*(y⁻¹)⁻¹)=x*embedM d.radical v*x⁻¹
      simp only [x,map_mul,map_inv]
    rw [he] at hh
    exact hh.trans (stabilizer_m_base d.radical).symm
  · rw [←hEm]
    apply le_normalizer_map (embedM d.radical)
    exact mem_map_of_mem _ ((normalizer (E : Set d.overgroup)).inv_mem hyE)
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
private theorem cube_first_edge_marking (u : S)
    (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    ∃ (E : Subgroup d.overgroup) (w : S),
      E.map (embedM d.radical) = Q d.radical (p.walk.getVert 1) ∧
      E.map s.projection = (D 6).map (MulAut.conj w).toMonoidHom ∧
      s.projection.ker ≤ E := by
  have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ
      (i := 0) (p.length_eq_b ▸ replacementDistance_pos h d)
  obtain ⟨j,hj,hjt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical)
    (base_adjacent d.radical) hat
  change j ∈ stabilizer d.radical (mVertex d.radical 1) at hj
  rw [stabilizer_m_base] at hj
  obtain ⟨m,rfl⟩ := hj
  change act d.radical (embedM d.radical m) (beta d.radical) = p.walk.getVert 1 at hjt
  let E := d.radical.map (MulAut.conj m⁻¹).toMonoidHom
  refine ⟨E,s.projection m⁻¹*u,?_,?_,?_⟩
  · rw [←hjt,Q_act,Q_beta]
    change (d.radical.map (MulAut.conj m⁻¹).toMonoidHom).map (embedM d.radical) = _
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro z
    change embedM d.radical (m⁻¹*z*(m⁻¹)⁻¹) =
      (embedM d.radical m)⁻¹*embedM d.radical z*((embedM d.radical m)⁻¹)⁻¹
    simp only [map_mul,map_inv]
  · have he : s.projection.comp (MulAut.conj m⁻¹).toMonoidHom =
        (MulAut.conj (s.projection m⁻¹)).toMonoidHom.comp s.projection := by
      apply MonoidHom.ext
      intro z
      change s.projection (m⁻¹*z*(m⁻¹)⁻¹)=s.projection m⁻¹*s.projection z*(s.projection m⁻¹)⁻¹
      simp only [map_mul,map_inv]
    change (d.radical.map (MulAut.conj m⁻¹).toMonoidHom).map s.projection = _
    rw [map_map,he,←map_map,hfull,CubeCommonFixer.conjugate_twice]
  · have hcore : (pCore 2 d.overgroup).map (MulAut.conj m⁻¹).toMonoidHom = pCore 2 d.overgroup :=
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top _)
    rw [s.projection_kernel,←hcore]
    exact map_mono (replacement_core_le_radical h d)

include e hz hn in
/-- A prescribed eligible neighbor has two small critical seed candidates.
One component element relates the candidates; the chosen edge kernel
and its conjugate generate the starting stabilizer. At least one candidate fails to normalize the backward seed product. -/
private theorem edge_aligned_paired_seed
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
          Q d.radical (p.walk.getVert 1) ⊔ Q d.radical t = stabilizer d.radical (alpha d.radical) ∧
          x ∈ normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ∧
          Q d.radical t ⊔ (Q d.radical t).map (MulAut.conj x).toMonoidHom =
            stabilizer d.radical (alpha d.radical) ∧
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
  obtain ⟨E,w,hEm,hEi,hEk⟩ := cube_first_edge_marking s u hfull' p
  obtain ⟨t,hat,hanchor,x,hxL,hxN,hxAnchor,hx3,hgen⟩ :=
    aligned_cube_neighbor s hc u hfull' p E w hEm hEi hEk hsmall
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
  refine ⟨t,hat,g,hg,hgt,hct,x,hxL,hanchor,hxAnchor,hxN,hx3,q,hq,hqsmall,hgen,?_⟩
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

include e hz hn in
/-- The strict source slice on the original nonsylow replacement produces
a backward critical path. The simultaneous common-fixer selection eliminates
both orientations of the trapped line pair and retains the cubic, neighbor
transporter, strict slice, and every overlapping vertex. -/
private theorem strict_edge_aligned_shift
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hindex : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ x ∈ Ltilde d.radical (alpha d.radical),
          Q d.radical (p.walk.getVert 1) ⊔ Q d.radical t = stabilizer d.radical (alpha d.radical) ∧
          x ∈ normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ∧
          Q d.radical t ⊔ (Q d.radical t).map (MulAut.conj x).toMonoidHom =
            stabilizer d.radical (alpha d.radical) ∧
          x^3 ∈ Q d.radical (alpha d.radical) ∧
          ∃ q : CriticalPath d.radical (replacementGeometry h d)
              (alpha d.radical) (act d.radical x a'),
            (∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i)) ∧
            (Q d.radical (act d.radical x a')).relIndex (Z d.radical (alpha d.radical)) < 4 ∧
            Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
              stabilizer d.radical (alpha d.radical) ∧
            let c := act d.radical g delta
            ((∃ v : CriticalPath d.radical (replacementGeometry h d) c
                (p.walk.getVert (p.walk.length-2)), v.walk.getVert 1=t ∧
                ∀ i ≤ p.walk.length-2, v.walk.getVert (i+2)=p.walk.getVert i) ∨
              (∃ v : CriticalPath d.radical (replacementGeometry h d) c
                (q.walk.getVert (q.walk.length-2)), v.walk.getVert 1=t ∧
                ∀ i ≤ q.walk.length-2, v.walk.getVert (i+2)=q.walk.getVert i)) := by
  have hb : 2 < replacementDistance h d := by omega
  have hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    have he := relIndex_eq_one.mpr hh
    omega
  obtain ⟨t,hat,g,hg,hgt,hct,x,hx,hanchor,hxAnchor,hxN,hx3,q,hq,hqs,hgen,hnorm⟩ :=
    edge_aligned_paired_seed (e := e) (hz := hz) (hn := hn)
      hb4 hns p hsmall hdelta hel
  let c := act d.radical g delta
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
  have hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) := by
    change 2 < (B d.radical (alpha d.radical) _).relIndex (U d.radical (act d.radical g delta))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hindex
  refine ⟨t,hat,g,hg,hgt,hct,hstrict,x,hx,hanchor,hxAnchor,hxN,hx3,q,hq,hqs,hgen,?_⟩
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change color d.radical c ≠ color d.radical t at h2
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have hpath {z : Vertex d.radical}
      (r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
      (hescape : ¬ Z d.radical c ≤ Q d.radical (r.walk.getVert (r.walk.length-2))) :
      ∃ v : CriticalPath d.radical (replacementGeometry h d) c (r.walk.getVert (r.walk.length-2)),
        v.walk.getVert 1=t ∧ ∀ i ≤ r.walk.length-2, v.walk.getVert (i+2)=r.walk.getVert i := by
    let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
      .cons ((cosetGraph_adj d.radical _ _).mpr hct)
        (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
    have hw : w.length=2 := rfl
    let v := r.prepend_two (Nat.le_of_lt hb) hcol w hw hescape
    have hvt : v.walk.getVert 1=t := by
      simp only [v,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
        hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
        SimpleGraph.Walk.getVert_zero]
    exact ⟨v,hvt,fun i hi => r.prepend_two_overlap _ _ _ _ _ hi⟩
  by_cases hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))
  · by_cases hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2))
    · exfalso
      let s := fullSymmetricAction_knownSimple h e hz hn d hb
      have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
      obtain ⟨u,hu⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
        (e := e) (hz := hz) (hn := hn) hb4 hns
      have hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
        rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
      have hxG : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hx
      rcases hnorm with hnp | hnq
      · exact cube_common_fixer_excludes_trapped_pair s hc hb u hfull p hsmall hat hct
          x hxG q hq hqs hgen hxN hpbad hqbad hstrict hnp
      · have hgen' : Q d.radical t ⊔ Z d.radical (act d.radical x a') ⊔ Z d.radical a' =
            stabilizer d.radical (alpha d.radical) := by
          calc
            _ = Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') := by ac_rfl
            _ = _ := hgen
        have hqback (i : ℕ) : p.walk.getVert i = act d.radical x⁻¹ (q.walk.getVert i) := by
          rw [hq,←act_mul,mul_inv_cancel,act_one]
        exact cube_common_fixer_excludes_trapped_pair s hc hb u hfull q hqs hat hct
          x⁻¹ ((stabilizer d.radical (alpha d.radical)).inv_mem hxG) p hqback hsmall hgen'
          (reverse_generating_pair _ _ x hxG hxN) hqbad hpbad hstrict hnq
    · exact Or.inr (hpath q hqbad)
  · exact Or.inl (hpath p hpbad)

/-- A paired backward shift whose selected kernel also generates with
its parent's literal first-edge kernel. -/
structure EdgePairedBackwardShift {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    extends PairedBackwardShift (h := h) p where
  first_kernel_generation : Q d.radical (p.walk.getVert 1) ⊔ Q d.radical edge =
    stabilizer d.radical a

/-- Transport preserves the same paired generators, conjugated by the
literal graph action, together with the parent walk and every overlap. -/
theorem EdgePairedBackwardShift.conjugate {a a' : Vertex d.radical}
    {p : CriticalPath d.radical (replacementGeometry h d) a a'}
    (q : EdgePairedBackwardShift (h := h) p) (j : FreeAmalgam d.radical) :
    Nonempty (EdgePairedBackwardShift (h := h) (p.act j)) := by
  let f := (MulAut.conj j⁻¹).toMonoidHom
  have hact (x : FreeAmalgam d.radical) (v : Vertex d.radical) :
      act d.radical (f x) (act d.radical j v) = act d.radical j (act d.radical x v) := by
    simp only [f,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,←act_mul]
    congr 1
    group
  have hstab : f q.transporter ∈ stabilizer d.radical (act d.radical j a) := by
    rw [stabilizer_act]
    exact mem_map_of_mem _ q.transporter_mem
  have hcubic : f q.cubic ∈ Ltilde d.radical (act d.radical j a) := by
    rw [Ltilde_act]
    exact mem_map_of_mem _ q.cubic_mem
  have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical j q.start) ((p.act j).walk.getVert ((p.act j).walk.length-2)),
      w.walk.getVert 1=act d.radical j q.edge ∧
      ∀ i ≤ (p.act j).walk.length-2, w.walk.getVert (i+2)=(p.act j).walk.getVert i := by
    have hend : (p.act j).walk.getVert ((p.act j).walk.length-2) =
        act d.radical j (p.walk.getVert (p.walk.length-2)) := by
      simp only [CriticalPath.act,actWalk_length,actWalk_getVert]
    rw [hend]
    refine ⟨q.path.act j,?_,?_⟩
    · simp only [CriticalPath.act,actWalk_getVert,q.first]
    · intro i hi
      have hi0 : i ≤ p.walk.length-2 := by
        simpa only [CriticalPath.act,actWalk_length] using hi
      simp only [CriticalPath.act,actWalk_getVert,q.overlap i hi0]
  obtain ⟨w,hw1,hwo⟩ := hex
  refine ⟨⟨⟨act d.radical j q.start,act d.radical j q.edge,f q.transporter,hstab,
    ?_,?_,(adjacent_act_iff d.radical j _ _).mpr q.adjacent_start,
    (adjacent_act_iff d.radical j _ _).mpr q.adjacent_shift,
    f q.cubic,hcubic,?_,?_,?_,w,hw1,hwo⟩,?_⟩⟩
  · simpa only [CriticalPath.act,actWalk_getVert,hact] using congrArg (act d.radical j) q.first_eq
  · simpa only [CriticalPath.act,actWalk_getVert,hact] using congrArg (act d.radical j) q.start_eq
  · rw [Q_act,←map_pow]
    exact mem_map_of_mem _ q.cubic_pow
  · have hh := congrArg (Subgroup.map f) q.kernel_generation
    rw [Subgroup.map_sup,map_conj_conj] at hh
    simpa only [Q_act,stabilizer_act,f,inv_inv,MulEquiv.coe_toMonoidHom,MulAut.conj_apply] using hh
  · have hh := congrArg (Subgroup.map f) q.endpoint_generation
    simpa only [Subgroup.map_sup,hact,Q_act,Z_act,stabilizer_act,f] using hh

  · have hh := congrArg (Subgroup.map f) q.first_kernel_generation
    simpa only [Subgroup.map_sup,Q_act,stabilizer_act,CriticalPath.act,actWalk_getVert,f] using hh

include e hz hn in
private theorem edge_paired_backward_shift_base
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    Nonempty (EdgePairedBackwardShift (h := h) p) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by
    rw [(nonsylow_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p).1]
    decide
  obtain ⟨t,hat,g,hg,hgt,hct,_,x,hx,hanchor,hxAnchor,hpair,hx3,q,hq,_,hgen,halt⟩ :=
    strict_edge_aligned_shift (e := e) (hz := hz) (hn := hn)
      hb hns p hsmall hdelta
      (nonsylow_forward_slice_strict_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p)
  rcases halt with ⟨v,hvt,hover⟩ | ⟨v,hvt,hover⟩
  · exact ⟨⟨⟨_,t,g,hg,hgt,rfl,hat,hct,x,hx,hx3,hpair,hgen,v,hvt,hover⟩,hanchor⟩⟩
  · let y := g*x⁻¹
    have hxG : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hx
    have hy : y ∈ stabilizer d.radical (alpha d.radical) := mul_mem hg (inv_mem hxG)
    have hfix : act d.radical x⁻¹ (alpha d.radical) = alpha d.radical := inv_mem hxG
    have hat' : Adjacent d.radical (alpha d.radical) (act d.radical x⁻¹ t) := by
      rw [←hfix]
      exact (adjacent_act_iff d.radical x⁻¹ _ _).mpr hat
    have hyt : act d.radical y (p.walk.getVert 1) = act d.radical x⁻¹ t := by
      rw [show y=g*x⁻¹ from rfl,act_mul,hgt]
    have hstart : act d.radical x⁻¹ (act d.radical g (p.walk.getVert 2)) =
        act d.radical y (p.walk.getVert 2) := (act_mul d.radical g x⁻¹ _).symm
    have hct' : Adjacent d.radical (act d.radical y (p.walk.getVert 2))
        (act d.radical x⁻¹ t) := by
      rw [←hstart]
      exact (adjacent_act_iff d.radical x⁻¹ _ _).mpr hct
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    have hend : act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2)) =
        p.walk.getVert (p.walk.length-2) := by
      rw [hlen,hq,←act_mul,mul_inv_cancel,act_one]
    have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical y (p.walk.getVert 2)) (p.walk.getVert (p.walk.length-2)),
        w.walk.getVert 1=act d.radical x⁻¹ t ∧
        ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2)=p.walk.getVert i := by
      have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical x⁻¹ (act d.radical g (p.walk.getVert 2)))
          (act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2))),
          w.walk.getVert 1=act d.radical x⁻¹ t ∧
          ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2)=p.walk.getVert i := by
        refine ⟨v.act x⁻¹,?_,?_⟩
        · simp only [CriticalPath.act,actWalk_getVert,hvt]
        · intro i hi
          simp only [CriticalPath.act,actWalk_getVert,hover i (hlen.symm ▸ hi),hq,
            ←act_mul,mul_inv_cancel,act_one]
      rwa [hstart,hend] at hex
    obtain ⟨w,hw1,hwo⟩ := hex
    refine ⟨⟨⟨_,_,y,hy,hyt,rfl,hat',hct',x⁻¹,inv_mem hx,?_,?_,?_,w,hw1,hwo⟩,?_⟩⟩
    · simpa only [inv_pow] using (Q d.radical (alpha d.radical)).inv_mem hx3
    · rw [Q_act,inv_inv,map_map]
      have he : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
          MonoidHom.id (FreeAmalgam d.radical) := by
        apply MonoidHom.ext
        intro z
        change x⁻¹*(x*z*x⁻¹)*(x⁻¹)⁻¹=z
        group
      rw [he,map_id]
      exact (sup_comm _ _).trans hpair
    · have hQt : (Q d.radical t).map (MulAut.conj x).toMonoidHom =
          Q d.radical (act d.radical x⁻¹ t) := by rw [Q_act,inv_inv]
      have hZa (z : Vertex d.radical) : (Z d.radical z).map (MulAut.conj x).toMonoidHom =
          Z d.radical (act d.radical x⁻¹ z) := by rw [Z_act,inv_inv]
      have hGa : (stabilizer d.radical (alpha d.radical)).map (MulAut.conj x).toMonoidHom =
          stabilizer d.radical (alpha d.radical) :=
        mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical (alpha d.radical)).le_normalizer hxG)
      have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hgen
      simp only [Subgroup.map_sup,hQt,hZa,hGa,←act_mul,mul_inv_cancel,act_one] at hh
      calc
        _ = Q d.radical (act d.radical x⁻¹ t) ⊔ Z d.radical (act d.radical x⁻¹ a') ⊔
          Z d.radical a' := by ac_rfl
        _ = _ := hh

    · have hQfirst : (Q d.radical (p.walk.getVert 1)).map (MulAut.conj x).toMonoidHom =
          Q d.radical (p.walk.getVert 1) := mem_normalizer_iff_map_conj_eq.mp hxAnchor
      have hGa : (stabilizer d.radical (alpha d.radical)).map (MulAut.conj x).toMonoidHom =
          stabilizer d.radical (alpha d.radical) :=
        mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical (alpha d.radical)).le_normalizer hxG)
      have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hanchor
      simpa only [Subgroup.map_sup,hQfirst,hGa,Q_act,inv_inv] using hh

private theorem edge_paired_backward_shift_of_vertices
    {a a' c c' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) c c')
    (ha : c=a) (he : c'=a') (hv : ∀ i, q.walk.getVert i=p.walk.getVert i)
    (hr : Nonempty (EdgePairedBackwardShift (h := h) q)) :
    Nonempty (EdgePairedBackwardShift (h := h) p) := by
  subst c
  subst c'
  obtain ⟨r⟩ := hr
  have hl : q.walk.length=p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
  have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d) r.start
      (q.walk.getVert (q.walk.length-2)),
      w.walk.getVert 1=r.edge ∧
      ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2)=p.walk.getVert i := by
    refine ⟨r.path,r.first,?_⟩
    intro i hi
    rw [r.overlap i (by omega),hv]
  rw [hl,hv] at hex
  obtain ⟨w,hw1,hwo⟩ := hex
  exact ⟨⟨⟨r.start,r.edge,r.transporter,r.transporter_mem,
    by simpa only [hv] using r.first_eq,by simpa only [hv] using r.start_eq,
    r.adjacent_start,r.adjacent_shift,r.cubic,r.cubic_mem,r.cubic_pow,
    r.kernel_generation,r.endpoint_generation,w,hw1,hwo⟩,by
      simpa only [hv] using r.first_kernel_generation⟩⟩

include e hz hn in
/-- Repeated selection retains the original-edge generating join and
both earlier generating pairs at every vertex, with no additional premise. -/
theorem nonsylow_edge_paired_backward_shift_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    Nonempty (EdgePairedBackwardShift (h := h) p) := by
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical j⁻¹ a = alpha d.radical := by
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have base := edge_paired_backward_shift_base (e := e) (hz := hz) (hn := hn)
    hb hns (a' := act d.radical j⁻¹ a')
  rw [←hbase] at base
  obtain ⟨q⟩ := base (p.act j⁻¹)
  have hcancel (v : Vertex d.radical) : act d.radical j (act d.radical j⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  exact edge_paired_backward_shift_of_vertices p ((p.act j⁻¹).act j)
    (hcancel a) (hcancel a') (by
      intro i
      simp only [CriticalPath.act,actWalk_getVert,hcancel]) (q.conjugate j)


/-- The two literal edge seeds have only central intersection, because their
full edge kernels generate the intervening component stabilizer. -/
theorem EdgePairedBackwardShift.edge_seed_intersection_central
    {a a' : Vertex d.radical}
    {p : CriticalPath d.radical (replacementGeometry h d) a a'}
    (q : EdgePairedBackwardShift (h := h) p) :
    Z d.radical (p.walk.getVert 1) ⊓ Z d.radical q.edge ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ
      (i := 0) (p.length_eq_b ▸ replacementDistance_pos h d)
  have hcent {t : Vertex d.radical} (ht : Adjacent d.radical a t) :
      Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    have hcol : color d.radical t = true := by
      have hh := adjacent_color_ne d.radical ht
      rw [p.start_color] at hh
      cases he : color d.radical t <;> simp_all
    intro x hx
    rw [Z,if_neg (by simp [hcol])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  apply le_centralizer_iff.mpr
  rw [←q.first_kernel_generation]
  exact sup_le (le_centralizer_iff.mp (inf_le_left.trans (hcent hat)))
    (le_centralizer_iff.mp (inf_le_right.trans (hcent q.adjacent_start)))

include e hz hn in
/-- The original critical line misses the selected backward edge seed.
This uses the original and selected kernels together; a single endpoint
transposition is not asserted to generate the stabilizer. -/
theorem nonsylow_edge_paired_critical_line_disjoint_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : EdgePairedBackwardShift (h := h) p) :
    ⁅Z d.radical a,Z d.radical a'⁆ ⊓ Z d.radical q.edge = ⊥ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hfull⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  let H := ⁅Z d.radical a,Z d.radical a'⁆
  have hfirst : H ≤ Z d.radical (p.walk.getVert 1) :=
    cube_critical_commutator_le_first_seed s hc u hR p
  have hcard : Nat.card H = 2 :=
    (nonsylow_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p).2.2
  have hnc : ¬ H ≤ Z d.radical q.edge := by
    intro hh
    exact critical_commutator_not_central s hc p
      ((le_inf hfirst hh).trans q.edge_seed_intersection_central)
  let := finite_Z d.radical (p.walk.getVert 1)
  let : Finite H := Finite.of_injective (inclusion hfirst) (inclusion_injective _)
  let : Finite (H ⊓ Z d.radical q.edge : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  by_contra hne
  have hp := (one_lt_card_iff_ne_bot (H ⊓ Z d.radical q.edge)).mpr hne
  have he : H ⊓ Z d.radical q.edge = H := eq_of_le_of_card_ge inf_le_left (by omega)
  exact hnc (he ▸ inf_le_right)

include e hz hn in
/-- Successive selected critical lines are independent in the same full
seed, and their join has order four on both central covers. -/
theorem nonsylow_edge_paired_critical_plane_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : EdgePairedBackwardShift (h := h) p) :
    let H := ⁅Z d.radical a,Z d.radical a'⁆
    let K := ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆
    H ⊓ K = ⊥ ∧ H ⊔ K ≤ Z d.radical a ∧ Nat.card (H ⊔ K : Subgroup (FreeAmalgam d.radical)) = 4 := by
  let H := ⁅Z d.radical a,Z d.radical a'⁆
  let K := ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆
  have hs := nonsylow_paired_shift_commutator_knownSimple (e := e) (hz := hz) (hn := hn)
    hb hns p q.toPairedBackwardShift
  have hHZ : H ≤ Z d.radical a :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans (DistanceEight.U_le_Z d.radical a)
  have hKZ : K ≤ Z d.radical a := hs.2.2.1
  have hdis : H ⊓ K = ⊥ := by
    apply bot_unique
    exact (inf_le_inf_left H hs.2.1).trans_eq
      (nonsylow_edge_paired_critical_line_disjoint_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p q)
  have hHK : K ≤ centralizer (H : Set (FreeAmalgam d.radical)) := by
    let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
    exact (hKZ.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)).trans (centralizer_le hHZ)
  have hcH : Nat.card H = 2 :=
    (nonsylow_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p).2.2
  have hcK : Nat.card K = 2 := hs.1
  refine ⟨hdis,sup_le hHZ hKZ,?_⟩
  rw [card_sup_eq_mul_of_normalizes_of_disjoint H K
    (hHK.trans (Subgroup.centralizer_le_normalizer (H : Set (FreeAmalgam d.radical)))) (disjoint_iff.mpr hdis),hcH,hcK]

include e hz hn in
/-- The source R₄/R₆ configuration now has an actual four-group in the
centralizer of the common endpoint radius, with both original-edge joins
retained. This does not assert intermediate-stabilizer noncentrality. -/
theorem nonsylow_edge_paired_terminal_plane_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ q : EdgePairedBackwardShift (h := h) p,
      ∃ r : EdgePairedBackwardShift (h := h) q.path,
        ∃ t : EdgePairedBackwardShift (h := h) r.path,
          let z₄ := q.path.walk.getVert (q.path.walk.length-2)
          let z₆ := r.path.walk.getVert (r.path.walk.length-2)
          let R₄ := ⁅Z d.radical r.start,Z d.radical z₄⁆
          let R₆ := ⁅Z d.radical t.start,Z d.radical z₆⁆
          R₄ ⊓ R₆ = ⊥ ∧ Nat.card (R₄ ⊔ R₆ : Subgroup (FreeAmalgam d.radical)) = 4 ∧
          R₄ ⊔ R₆ ≤ Z d.radical r.start ⊓
            centralizer (V d.radical z₄ : Set (FreeAmalgam d.radical)) := by
  obtain ⟨q⟩ := nonsylow_edge_paired_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p
  obtain ⟨r⟩ := nonsylow_edge_paired_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn) hb hns q.path
  obtain ⟨t⟩ := nonsylow_edge_paired_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn) hb hns r.path
  have hp := nonsylow_edge_paired_critical_plane_knownSimple (e := e) (hz := hz) (hn := hn) hb hns r.path t
  have ht := nonsylow_paired_shift_commutator_knownSimple (e := e) (hz := hz) (hn := hn)
    hb hns r.path t.toPairedBackwardShift
  have hR₄Z : ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) :=
    ((critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_right).trans (DistanceEight.U_le_Z d.radical _)
  have hR₄V := (hR₄Z.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical _ r.path.end_color))).trans
    (centralizer_le (V_le_Q d.radical (geometry := replacementGeometry h d) r.path.end_color
      (by change 2 < replacementDistance h d; omega)))
  exact ⟨q,r,t,hp.1,hp.2.2,le_inf hp.2.1 (sup_le hR₄V ht.2.2.2.2.1)⟩


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
