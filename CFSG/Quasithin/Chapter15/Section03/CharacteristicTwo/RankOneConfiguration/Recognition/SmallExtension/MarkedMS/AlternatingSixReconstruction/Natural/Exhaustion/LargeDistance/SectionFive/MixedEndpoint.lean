module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedConjugateKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedLarge
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowNormalizer

/-!
# Simultaneous mixed-plane generation and terminal kernel movement

In the marked symmetric quotient, the mixed plane has a unique
transposition. Its normalizer centralizes that transposition. A critical
transposition generating S₆ with this normalizer must cross its support.
Eight small alignment permutations reduce the crossing to (04). One explicit
conjugator then gives both source generation identities simultaneously:
the two mixed planes generate S₆, and the original plane together with the
two conjugate critical transpositions also generates S₆. The certificates
use short words in four permutations, rather than enumerating S₆ subgroups.

Lift both identities through the actual projection and free-amalgam
embedding. Apply the same conjugator to the original strict backward walk
and its full seed kernel. The previously proved conjugate-kernel containment
therefore holds for a conjugator satisfying the endpoint generation as well.
Both the trapped and escaping conjugate-seed cases are retained.

If the whole radius kernel V_a intersect Q_(a'-2) had commutator with Z_(a')
inside Z_a, the full backward seed kernel joined with Z_a would be normalized
by each of these three generators. The residual-action theorem would place
that kernel in the Baumann slice, whose index would be at most two. This
contradicts the already proved strict slice. Consequently the whole radius
kernel's endpoint commutator escapes Z_a, at every original component vertex.
The positive upper estimate needed to contradict this escape remains open;
this module does not claim the mixed-plane terminal exclusion.

Both central covers, all full seed attachments, the original Sylow distinction,
and the minimum characteristic replacement are retained. The larger original
Sylow and distance-four exclusions, LargeDistanceInput, and unconditional
distance two remain necessary. Private imports continue the same local proof
family without widening any earlier public boundary.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the simultaneous generation of (5.6)(b,c) and the kernel normalization
in (5.11)(1), printed pp.917--918,923. All graph maps use the original
natural graph and its inverse-conjugation convention.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedEndpoint
local notation "S" => Equiv.Perm (Fin 6)
private def aligner : Fin 8 → S := ![1, swap45, Equiv.swap 0 1,
  Equiv.swap 0 1 * swap45, Equiv.swap 0 2 * Equiv.swap 1 3,
  Equiv.swap 0 2 * Equiv.swap 1 3 * swap45, Equiv.swap 0 3 * Equiv.swap 1 2,
  Equiv.swap 0 3 * Equiv.swap 1 2 * swap45]

private theorem aligner_normalizes (k : Fin 8) : aligner k ∈ normalizer (plus : Set S) := by
  apply Subgroup.centralizer_le_normalizer
  intro a ha
  obtain ⟨i,rfl⟩ := (mem_plus_iff a).mp ha
  have cert : ∀ k : Fin 8, ∀ i : Fin 4,
      planeWords 0 i * aligner k = aligner k * planeWords 0 i := by decide +kernel
  exact cert k i

private theorem canonical_endpoints :
    plus ⊔ zpowers (Equiv.swap (0 : Fin 6) 4) ⊔
      zpowers ((MulAut.conj MixedLarge.crossing⁻¹) (Equiv.swap (0 : Fin 6) 4)) = ⊤ := by
  let H := plus ⊔ zpowers (Equiv.swap (0 : Fin 6) 4) ⊔
    zpowers ((MulAut.conj MixedLarge.crossing⁻¹) (Equiv.swap (0 : Fin 6) 4))
  have hb : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3 ∈ H :=
    mem_sup_left (mem_sup_left ((mem_plus_iff _).mpr ⟨1,by decide +kernel⟩))
  have hc : swap45 ∈ H := mem_sup_left (mem_sup_left ((mem_plus_iff _).mpr ⟨2,by decide +kernel⟩))
  have hd : Equiv.swap (0 : Fin 6) 4 ∈ H := mem_sup_left (mem_sup_right (mem_zpowers _))
  have he : Equiv.swap (0 : Fin 6) 3 ∈ H := by
    have hh : (MulAut.conj MixedLarge.crossing⁻¹) (Equiv.swap (0 : Fin 6) 4) = Equiv.swap 0 3 := by decide +kernel
    exact hh ▸ mem_sup_right (mem_zpowers _)
  let gs : Fin 4 → S := ![Equiv.swap 0 1 * Equiv.swap 2 3,swap45,Equiv.swap 0 4,Equiv.swap 0 3]
  let words : Fin 5 → List (Fin 4) := ![[1,2,1],[0,1,2,0,1],[0,1,2,3,2,0,1],[1,2,3,2,1],[1]]
  have cert : ∀ i : Fin 5, ((words i).map gs).prod = Equiv.swap i.castSucc (5 : Fin 6) := by decide +kernel
  have hs (i : Fin 5) : Equiv.swap i.castSucc (5 : Fin 6) ∈ H := by
    rw [←cert i]
    apply list_prod_mem
    intro g hg
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hg
    fin_cases j
    · exact hb
    · exact hc
    · exact hd
    · exact he
  apply top_unique
  rw [←Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 5)]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i,rfl⟩
  have cert' : ∀ i : Fin 4, Equiv.swap (i.castSucc.castSucc : Fin 6) i.castSucc.succ =
      Equiv.swap i.castSucc.castSucc 5 * Equiv.swap i.succ.castSucc 5 *
        Equiv.swap i.castSucc.castSucc 5 := by decide +kernel
  fin_cases i
  · change Equiv.swap (0 : Fin 6) 1 ∈ H
    rw [show Equiv.swap (0 : Fin 6) 1 = _ from cert' 0]
    exact H.mul_mem (H.mul_mem (hs 0) (hs 1)) (hs 0)
  · change Equiv.swap (1 : Fin 6) 2 ∈ H
    rw [show Equiv.swap (1 : Fin 6) 2 = _ from cert' 1]
    exact H.mul_mem (H.mul_mem (hs 1) (hs 2)) (hs 1)
  · change Equiv.swap (2 : Fin 6) 3 ∈ H
    rw [show Equiv.swap (2 : Fin 6) 3 = _ from cert' 2]
    exact H.mul_mem (H.mul_mem (hs 2) (hs 3)) (hs 2)
  · change Equiv.swap (3 : Fin 6) 4 ∈ H
    rw [show Equiv.swap (3 : Fin 6) 4 = _ from cert' 3]
    exact H.mul_mem (H.mul_mem (hs 3) (hs 4)) (hs 3)
  · exact hc

private theorem mixed_simultaneous_pair (u a : S) (ha : a.IsSwap)
    (hgen : normalizer (plus.map (MulAut.conj u).toMonoidHom : Set S) ⊔ zpowers a = ⊤) :
    ∃ k : S,
      plus.map (MulAut.conj u).toMonoidHom ⊔
        (plus.map (MulAut.conj u).toMonoidHom).map (MulAut.conj k).toMonoidHom = ⊤ ∧
      plus.map (MulAut.conj u).toMonoidHom ⊔ zpowers a ⊔
        zpowers ((MulAut.conj k⁻¹) a) = ⊤ := by
  let a₀ := (MulAut.conj u⁻¹) a
  have hswap : a₀.IsSwap := by
    apply Equiv.Perm.isSwap_iff_cycleType.mpr
    have hi : ((MulAut.conj u⁻¹) a).cycleType = a.cycleType := Equiv.Perm.cycleType_conj
    exact hi.trans (Equiv.Perm.isSwap_iff_cycleType.mp ha)
  have hmul : a₀ * swap45 ≠ swap45 * a₀ := by
    intro he
    have hN : normalizer (plus.map (MulAut.conj u).toMonoidHom : Set S) ≤
        centralizer ({(MulAut.conj u) swap45} : Set S) := by
      apply (SylowNormalizer.mixed_conjugate_normalizer_centralizes u).trans
      apply centralizer_le
      exact Set.singleton_subset_iff.mpr (mem_map_of_mem _ ((mem_plus_iff _).mpr ⟨2,by decide +kernel⟩))
    have hA : zpowers a ≤ centralizer ({(MulAut.conj u) swap45} : Set S) := by
      apply zpowers_le.mpr
      rw [mem_centralizer_singleton_iff]
      have hh := congrArg (MulAut.conj u) he
      have hcancel : (MulAut.conj u) a₀ = a := by
        change u*(u⁻¹*a*(u⁻¹)⁻¹)*u⁻¹ = a
        group
      simpa only [map_mul,hcancel] using hh
    have htop := sup_le hN hA
    rw [hgen] at htop
    have hz : (MulAut.conj u) swap45 ∈ center S := by
      apply mem_center_iff.mpr
      intro b
      exact mem_centralizer_singleton_iff.mp (htop (mem_top b))
    rw [Theory.SpecificGroups.SymmetricSix.s6_center_eq_bot,mem_bot] at hz
    have hh : swap45 = 1 := (MulAut.conj u).injective (hz.trans (map_one _).symm)
    exact (by decide +kernel : swap45 ≠ (1 : S)) hh
  obtain ⟨i,j,hij,he⟩ := hswap
  have cert : ∀ i j : Fin 6, Equiv.swap i j * swap45 ≠ swap45 * Equiv.swap i j →
      ∃ r : Fin 8, (MulAut.conj (aligner r)) (Equiv.swap i j) = Equiv.swap 0 4 := by decide +kernel
  obtain ⟨r,hr⟩ := cert i j (he ▸ hmul)
  have hn := mem_normalizer_iff_map_conj_eq.mp ((normalizer (plus : Set S)).inv_mem (aligner_normalizes r))
  change plus.map (MulAut.conj (aligner r)⁻¹).toMonoidHom = plus at hn
  let v := u * (aligner r)⁻¹
  let k := (MulAut.conj v) MixedLarge.crossing
  let f := (MulAut.conj v).toMonoidHom
  have hP : plus.map f = plus.map (MulAut.conj u).toMonoidHom := by
    have hf : f = (MulAut.conj u).toMonoidHom.comp (MulAut.conj (aligner r)⁻¹).toMonoidHom := by
      apply MonoidHom.ext
      intro g
      change (u*(aligner r)⁻¹)*g*(u*(aligner r)⁻¹)⁻¹=u*((aligner r)⁻¹*g*((aligner r)⁻¹)⁻¹)*u⁻¹
      group
    rw [hf,←map_map,hn]
  have haeq : f (Equiv.swap (0 : Fin 6) 4) = a := by
    rw [←hr,←he]
    change (u*(aligner r)⁻¹)*((aligner r)*(u⁻¹*a*u)*(aligner r)⁻¹)*(u*(aligner r)⁻¹)⁻¹=a
    group
  have hcomm (g : S) : f.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (f g)).toMonoidHom.comp f := by
    apply MonoidHom.ext
    intro b
    change f (g*b*g⁻¹) = f g * f b * (f g)⁻¹
    simp only [map_mul,map_inv]
  refine ⟨k,?_,?_⟩
  · have hh := congrArg (Subgroup.map f) MixedLarge.crossing_generates
    rw [Subgroup.map_sup,map_map,hcomm,←map_map,hP,map_top_of_surjective _ (MulAut.conj v).surjective] at hh
    exact hh
  · have hh := congrArg (Subgroup.map f) canonical_endpoints
    rw [Subgroup.map_sup,Subgroup.map_sup,hP,MonoidHom.map_zpowers,MonoidHom.map_zpowers,haeq,
      map_top_of_surjective _ (MulAut.conj v).surjective] at hh
    have heq : f ((MulAut.conj MixedLarge.crossing⁻¹) (Equiv.swap (0 : Fin 6) 4)) =
        (MulAut.conj k⁻¹) a := by
      change f (MixedLarge.crossing⁻¹ * Equiv.swap (0 : Fin 6) 4 * (MixedLarge.crossing⁻¹)⁻¹) = _
      rw [map_mul,map_mul,map_inv,map_inv,haeq]
      rfl
    rwa [heq] at hh

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

private theorem edge_preimage
    (s : FullSymmetricAction h e hz hn d) (u : S)
    (him : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom)
    {t : Vertex d.radical} (hat : Adjacent d.radical (alpha d.radical) t) :
    ∃ E : Subgroup d.overgroup, ∃ v : S,
      E.map (embedM d.radical) = Q d.radical t ∧ s.projection.ker ≤ E ∧
      E.map s.projection = plus.map (MulAut.conj v).toMonoidHom := by
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical)
    (base_adjacent d.radical) hat
  have hbase : stabilizer d.radical (alpha d.radical) = (embedM d.radical).range := stabilizer_m_base d.radical
  rw [hbase] at hg
  change act d.radical g (beta d.radical) = t at hgt
  obtain ⟨m,rfl⟩ := hg
  let E := d.radical.map (MulAut.conj m⁻¹).toMonoidHom
  refine ⟨E,s.projection m⁻¹*u,?_,?_,?_⟩
  · rw [←hgt,Q_act,Q_beta,map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro z
    change embedM d.radical (m⁻¹*z*(m⁻¹)⁻¹) =
      (embedM d.radical m)⁻¹*embedM d.radical z*((embedM d.radical m)⁻¹)⁻¹
    simp only [map_mul,map_inv]
  · have hQ : (pCore 2 d.overgroup).map (MulAut.conj m⁻¹).toMonoidHom = pCore 2 d.overgroup :=
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top _)
    rw [s.projection_kernel,←hQ]
    exact map_mono (replacement_core_le_radical h d)
  · have he : E.map s.projection = (d.radical.map s.projection).map
        (MulAut.conj (s.projection m⁻¹)).toMonoidHom := by
      rw [show E = d.radical.map (MulAut.conj m⁻¹).toMonoidHom from rfl,map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro z
      change s.projection (m⁻¹*z*(m⁻¹)⁻¹) =
        s.projection m⁻¹*s.projection z*(s.projection m⁻¹)⁻¹
      simp only [map_mul,map_inv]
    rw [he,him,map_map]
    congr 1

/-- A selected relative-normalizer edge admits one actual conjugator for
both source generation requirements: the two full edge kernels, and the
edge kernel together with the two endpoint seeds. -/
theorem mixed_simultaneous_edge_endpoint_conjugate_knownSimple
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hat : Adjacent d.radical (alpha d.radical) t)
    (hgen : (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
        stabilizer d.radical (alpha d.radical)) :
    ∃ x ∈ stabilizer d.radical (alpha d.radical),
      Q d.radical t ⊔ Q d.radical (act d.radical x⁻¹ t) = stabilizer d.radical (alpha d.radical) ∧
      Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
        stabilizer d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have him' : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨E,v,hEm,hEk,hEi⟩ := edge_preimage s u him' hat
  have hbase : stabilizer d.radical (alpha d.radical) = (embedM d.radical).range := stabilizer_m_base d.radical
  let A := (Z d.radical a').comap (embedM d.radical)
  have hAm : A.map (embedM d.radical) = Z d.radical a' :=
    map_comap_eq_self ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
        (stabilizer_m_base d.radical))
  obtain ⟨a,ha,hAi⟩ := small_critical_image_eq_swap s hc p (by
    rw [(MixedLarge.mixed_critical_indices_two_knownSimple hb u him p).1]
    decide)
  change A.map s.projection = zpowers a at hAi
  have hNg : normalizer (E : Set d.overgroup) ⊔ A = ⊤ := by
    apply map_injective (embedM_injective d.radical)
    rw [Subgroup.map_sup,SylowNormalizer.normalizer_embed,hEm,hAm,←MonoidHom.range_eq_map,
      ←hbase]
    exact hgen
  have hNi : normalizer (plus.map (MulAut.conj v).toMonoidHom : Set S) ⊔ zpowers a = ⊤ := by
    apply top_unique
    have hh := congrArg (Subgroup.map s.projection) hNg
    rw [Subgroup.map_sup,hAi,map_top_of_surjective _ s.surjective] at hh
    rw [←hh,←hEi]
    exact sup_le_sup (le_normalizer_map s.projection) le_rfl
  obtain ⟨k,hpair,hend⟩ := mixed_simultaneous_pair v a ha hNi
  obtain ⟨g,hgk⟩ := s.surjective k
  have hmap (C : Subgroup d.overgroup) (j : d.overgroup) :
      (C.map (MulAut.conj j).toMonoidHom).map s.projection =
        (C.map s.projection).map (MulAut.conj (s.projection j)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro z
    change s.projection (j*z*j⁻¹) = s.projection j*s.projection z*(s.projection j)⁻¹
    simp only [map_mul,map_inv]
  have hpair' : E ⊔ E.map (MulAut.conj g).toMonoidHom = ⊤ := by
    apply map_injective_of_ker_le s.projection (hEk.trans le_sup_left) le_top
    rw [Subgroup.map_sup,hmap,hEi,hgk,map_top_of_surjective _ s.surjective]
    exact hpair
  have hend' : E ⊔ A ⊔ A.map (MulAut.conj g⁻¹).toMonoidHom = ⊤ := by
    apply map_injective_of_ker_le s.projection (hEk.trans (le_sup_left.trans le_sup_left)) le_top
    rw [Subgroup.map_sup,Subgroup.map_sup,hmap,hEi,hAi,map_inv,hgk,
      MonoidHom.map_zpowers,map_top_of_surjective _ s.surjective]
    exact hend
  have hmap' (C : Subgroup d.overgroup) (j : d.overgroup) :
      (C.map (MulAut.conj j).toMonoidHom).map (embedM d.radical) =
        (C.map (embedM d.radical)).map (MulAut.conj (embedM d.radical j)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro z
    change embedM d.radical (j*z*j⁻¹) =
      embedM d.radical j*embedM d.radical z*(embedM d.radical j)⁻¹
    simp only [map_mul,map_inv]
  refine ⟨embedM d.radical g,?_,?_,?_⟩
  · rw [hbase]
    exact ⟨g,rfl⟩
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hpair'
    rw [Subgroup.map_sup,hmap',hEm,←MonoidHom.range_eq_map,←hbase] at hh
    simpa only [Q_act,inv_inv] using hh
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hend'
    rw [Subgroup.map_sup,Subgroup.map_sup,hmap',hEm,hAm,←MonoidHom.range_eq_map,
      ←hbase,map_inv] at hh
    simpa only [Z_act] using hh

/-- The original strict backward construction supplies the new conjugate
kernel containment with no generation or radius-index premise. Both
transporters, every shared walk vertex, and the strict slice survive. The same conjugator also supplies the full endpoint-seed generation. The
conjugate seed is trapped, or the intrinsic radius line is central at the
original start; it remains noncentral at the predecessor in either case. -/
theorem mixed_backward_simultaneous_kernel_knownSimple
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
          stabilizer d.radical (alpha d.radical) ∧
      ∃ y ∈ stabilizer d.radical (alpha d.radical), act d.radical y (p.walk.getVert 1) = t ∧
      ∃ k ∈ stabilizer d.radical t,
      ∃ q : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical k (act d.radical y (p.walk.getVert 2)))
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical k (act d.radical y (p.walk.getVert 2)))) =
        (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (p.walk.getVert 2)) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical k (act d.radical y (p.walk.getVert 2)))) ∧
        ∃ x ∈ stabilizer d.radical (alpha d.radical),
          Q d.radical t ⊔ Q d.radical (act d.radical x⁻¹ t) = stabilizer d.radical (alpha d.radical) ∧
          Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
            stabilizer d.radical (alpha d.radical) ∧
          Z d.radical (act d.radical k (act d.radical y (p.walk.getVert 2))) ⊓
            Q d.radical (p.walk.getVert (p.walk.length-2)) ≤
              Q d.radical (act d.radical x (p.walk.getVert (p.walk.length-2))) ∧
          (Z d.radical (act d.radical x⁻¹ (act d.radical k (act d.radical y (p.walk.getVert 2)))) ≤
              Q d.radical (p.walk.getVert (p.walk.length-2)) ∨
            ⁅V d.radical (alpha d.radical),Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
              centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))) := by
  obtain ⟨t,hat,hgen,y,hy,hyt,k,hk,q,hq1,hover,hidx,hstrict⟩ :=
    MixedLarge.mixed_backward_path_of_four_lt_knownSimple hb u him p
  obtain ⟨x,hx,hpair,hend⟩ := mixed_simultaneous_edge_endpoint_conjugate_knownSimple hb u him p hat hgen
  have hzt : Adjacent d.radical (act d.radical k (act d.radical y (p.walk.getVert 2))) t := by
    have hl : 0 < q.walk.length := q.length_eq_b ▸ replacementDistance_pos h d
    have hh := q.walk.adj_getVert_succ (i := 0) hl
    rw [SimpleGraph.Walk.getVert_zero,hq1] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  refine ⟨t,hat,hgen,y,hy,hyt,k,hk,q,hq1,hover,hidx,hstrict,x,hx,hpair,hend,
    MixedConjugateKernel.mixed_generating_conjugate_kernel_knownSimple hb u him p q hat hzt x hx hpair,?_⟩
  by_cases hout : Z d.radical (act d.radical x⁻¹ (act d.radical k (act d.radical y (p.walk.getVert 2)))) ≤
      Q d.radical (p.walk.getVert (p.walk.length-2))
  · exact Or.inl hout
  · exact Or.inr (MixedConjugateKernel.mixed_generating_conjugate_common_line_knownSimple hb u him p q hat hzt x hx hpair hout).2


/-- The mixed-plane terminal hypotheses force genuine movement of the
whole predecessor radius kernel outside the starting seed. This is the
remaining source commutator estimate whose upper bound would exclude this
branch; both conjugate-seed alternatives and both generation premises are
discharged on the same strict backward walk. -/
theorem mixed_radius_kernel_commutator_escape_knownSimple
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    ¬ ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),
        Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) := by
  intro hcontrol
  obtain ⟨t,hat,hgen,y,hy,hyt,k,hk,q,hq1,hover,hidx,hstrict,x,hx,hpair,hend,hKother,_⟩ :=
    mixed_backward_simultaneous_kernel_knownSimple hb u him p
  let a := alpha d.radical
  let c := p.walk.getVert (p.walk.length-2)
  let z := act d.radical k (act d.radical y (p.walk.getVert 2))
  let K := Z d.radical z ⊓ Q d.radical c
  let Y := K ⊔ Z d.radical a
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hb2 : 2 < replacementDistance h d := by omega
  have hq2 : q.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hnear : (cosetGraph d.radical).dist z a ≤ 2 := by
    rw [←hq2,q.dist_start (by have hl : q.walk.length = replacementDistance h d := q.length_eq_b; omega)]
  have hZV : Z d.radical z ≤ V d.radical a :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hnear)
  have hKV : K ≤ V d.radical a := inf_le_left.trans hZV
  have hYV : Y ≤ V d.radical a := sup_le hKV (Z_le_VBall d.radical _ 2)
  have hVG : V d.radical a ≤ stabilizer d.radical a :=
    (V_le_Q d.radical (geometry := replacementGeometry h d) rfl hb2).trans (fun _ hx => hx.1)
  have hsmall : (Q d.radical c).relIndex (Z d.radical z) < 4 := by
    rw [(MixedLarge.mixed_critical_indices_two_knownSimple hb u him q).1]
    decide
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him]
    exact map_mono plus_le_D
  have hline : ⁅Z d.radical z,Z d.radical c⁆ ≤ Z d.radical t := by
    simpa only [hq1] using cube_critical_commutator_le_first_seed s hc u hR q
  have hKN : Q d.radical t ≤ normalizer (K : Set (FreeAmalgam d.radical)) := by
    have hh := (small_critical_kernel_normalized_iff_first_seed s hc q hsmall).mpr
      (hq1.symm ▸ hline)
    simpa only [hq1] using hh
  have hKG : K ≤ stabilizer d.radical a := hKV.trans hVG
  have hKmove : ⁅K,Z d.radical a'⁆ ≤ Z d.radical a :=
    (commutator_mono (le_inf hKV inf_le_right) le_rfl).trans hcontrol
  have hZmap : (Z d.radical a).map (MulAut.conj x⁻¹).toMonoidHom = Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp ((Z_normalized d.radical a) ((stabilizer d.radical a).inv_mem hx))
  have hVmap : (V d.radical a).map (MulAut.conj x⁻¹).toMonoidHom = V d.radical a := by
    rw [←V_act,show act d.radical x a=a from hx]
  have hKmove' : ⁅K,Z d.radical (act d.radical x a')⁆ ≤ Z d.radical a := by
    have hm := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hcontrol
    rw [map_commutator,map_inf _ _ _ (MulAut.conj x⁻¹).injective,hVmap,←Q_act,←Z_act,hZmap] at hm
    exact (commutator_mono (le_inf hKV hKother) le_rfl).trans hm
  have hAG := critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
    (by rw [(replacementGeometry h d).distance_constant a p.start_color]
        exact replacementDistance_pos h d) p.critical
  have hA'G : Z d.radical (act d.radical x a') ≤ stabilizer d.radical a := by
    have hm := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hAG
    rw [←Z_act,←stabilizer_act,show act d.radical x a=a from hx] at hm
    exact hm
  have hYmove (A : Subgroup (FreeAmalgam d.radical))
      (hA : A ≤ stabilizer d.radical a) (hK : ⁅K,A⁆ ≤ Z d.radical a) :
      ⁅Y,A⁆ ≤ Z d.radical a := by
    apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      K (Z d.radical a) A (Z d.radical a) (Z_normalized d.radical a)
      hKG (Z_le_stabilizer d.radical a) hK
    exact le_normalizer_iff_commutator_le_left.mp (hA.trans (Z_normalized d.radical a))
  have hYN : stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hend]
    refine sup_le (sup_le ?_ ?_) ?_
    · apply le_trans (le_inf hKN _) (normalizer_inf_normalizer_le_normalizer_sup _ _)
      exact (show Q d.radical t ≤ stabilizer d.radical a from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hat)).trans (Z_normalized d.radical a)
    · exact le_normalizer_iff_commutator_le_left.mpr ((hYmove _ hAG hKmove).trans le_sup_right)
    · exact le_normalizer_iff_commutator_le_left.mpr ((hYmove _ hA'G hKmove').trans le_sup_right)
  have hKB : K ≤ B d.radical a ((replacementGeometry h d).Z_normal _) :=
    le_sup_left.trans (normalized_radius_le_slice_of_actor_at s hb2 rfl Y (Z d.radical a')
      hYV hYN hAG (critical_reverse_pair s hc p).2 (hYmove _ hAG hKmove))
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical z)) (inclusion_injective _)
  have hupper : (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2 := by
    have hh := (relIndex_le_of_le_left hKB (L := U d.radical z) index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (H := K) (DistanceEight.U_le_Z d.radical z) index_ne_zero_of_finite)
    have hidx : K.relIndex (Z d.radical z)=2 := by
      dsimp only [K]
      rw [inf_relIndex_left]
      exact (MixedLarge.mixed_critical_indices_two_knownSimple hb u him q).1
    exact hh.trans_eq hidx
  exact (Nat.not_le_of_gt hstrict) hupper

/-- The same full radius-kernel escape at every original component vertex,
transporting the actual endpoint and predecessor of the given critical walk. -/
theorem mixed_radius_kernel_commutator_escape_at_knownSimple
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ¬ ⁅V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),
        Z d.radical a'⁆ ≤ Z d.radical a := by
  obtain ⟨g,hga⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hga,act_mVertex,mul_inv_cancel]
    rfl
  have base := mixed_radius_kernel_commutator_escape_knownSimple hb u him
    (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  have hn := base (p.act g⁻¹)
  intro hle
  apply hn
  dsimp only [CriticalPath.act]
  simp only [actWalk_length,actWalk_getVert]
  rw [V_act,Q_act,Z_act,Z_act,←map_inf _ _ _ (MulAut.conj g⁻¹⁻¹).injective,
    ←map_commutator]
  exact map_mono hle

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedEndpoint
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
