module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightBaumann
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowShiftChain
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightStrictShift
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightSmallMovers
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePaths
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowCompatible
/-!
# Generating large-image shifts for the surviving image-eight radical

The actual replacement image contains an odd permutation, by the literal
component–radical product and its symmetric quotient. Conjugate into the
canonical Sylow group. A non-elementary element gives a four-cycle and
its square; the three-duad mover supplies an element moving the last pair.
Short permutation identities, using oddness when the initial generators
are even, show that this image and a specified even involution generate
the symmetric group. Involution fusion transports the calculation.

Lift generation through the entire two-core. The controlled endpoint actor
then generates with an actual edge kernel. Its radius-intersection bound
forces every prescribed eligible neighboring seed to be critical with the
old predecessor. This gives one starting-stabilizer transporter for both
initial vertices, together with every overlap of the backward path.
Conjugation gives the construction at every original component vertex.

Two successive large-image shifts cannot both stay large: the proved
three-shift commutator comparison forces the second shifted image to have
order two. Thus a small critical pair exists above distance four without
any mover-model or image-size selection premise. Its strict forward slice
transports to a strict neighboring seed at every incident edge. The original
MS radical application retains its relative index two over the selected
replacement edge kernel. Both cover orders and all central attachments remain.

These are generating paths and a small-pair reduction, not an exclusion of
all large critical images. Generating small-image shifts, the terminal
image-eight contradiction and the general distance-four estimates remain
necessary for the unconditional distance bound.

Source: Meierfrankenfeld–Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)--(5.10), printed pp.915--923, and Section 7, pp.932--933;
the finite coordinates are the six-letter models of Aschbacher–Smith B.3.2--4.
The import-all edges reuse internal model and controlled-kernel proofs
without changing their public boundaries.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightLarge
local notation "S" => Equiv.Perm (Fin 6)
private abbrev a : S := Equiv.swap 0 1
private abbrev b : S := Equiv.swap 2 3
private abbrev c : S := Equiv.swap 4 5
private abbrev z : S := a*b
private abbrev u : S := a * (Equiv.swap 0 2 * Equiv.swap 1 3)
private abbrev r : S := Equiv.swap 0 4 * b
private abbrev t : S := Equiv.swap 0 4
private def evenWord (i : Fin 8) : S := (u*c)^(i.val%4) * (a*c)^(i.val/4)

private theorem canonical_even_generates (E : Subgroup S) (hES : E ≤ sylowCarrier)
    (hne : ¬ IsElementaryAbelian 2 E) (hodd : ¬ E ≤ alternatingGroup (Fin 6))
    (hy : ∃ y ∈ E ⊓ D 6, y (4 : Fin 6) ≠ 4) :
    E ⊔ zpowers r = ⊤ := by
  have hex : ∃ x ∈ E, x^2 ≠ 1 := by
    by_contra! hh
    exact hne (NonsylowImage.elementary_of_squares E hh)
  obtain ⟨x,hx,hsq⟩ := hex
  obtain ⟨i,rfl⟩ := (mem_sylowCarrier_iff _).mp (hES hx)
  have hz : z ∈ E := by
    have he := (NonsylowImage.sylow_square_certificate i).resolve_left hsq
    change (sylowWords i)^2=z at he
    exact he ▸ E.pow_mem hx 2
  have hu : u ∈ E ∨ u*c ∈ E := by
    have cert : ∀ i : Fin 16, (sylowWords i)^2 ≠ 1 →
        sylowWords i=u ∨ sylowWords i=u⁻¹ ∨
        sylowWords i=u*c ∨ sylowWords i=(u*c)⁻¹ := by decide +kernel
    rcases cert i hsq with he | he | he | he
    · exact Or.inl (he ▸ hx)
    · exact Or.inl (inv_mem_iff.mp (he ▸ hx))
    · exact Or.inr (he ▸ hx)
    · exact Or.inr (inv_mem_iff.mp (he ▸ hx))
  obtain ⟨y,hyE,hy4⟩ := hy
  obtain ⟨j,rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) _).mp hyE.2
  have hyj : dWords j ∈ E := hyE.1
  have hcy : c ∈ E ∨ a*c ∈ E := by
    have cert : ∀ j : Fin 8, dWords j (4 : Fin 6) ≠ 4 →
        dWords j=c ∨ dWords j=z*c ∨ dWords j=a*c ∨ dWords j=z*(a*c) := by
      decide +kernel
    rcases cert j hy4 with he | he | he | he
    · exact Or.inl (he ▸ hyE.1)
    · have hh := E.mul_mem hz (he ▸ hyj)
      have eq : z*(z*c)=c := by decide +kernel
      exact Or.inl (eq ▸ hh)
    · exact Or.inr (he ▸ hyE.1)
    · have hh := E.mul_mem hz (he ▸ hyj)
      have eq : z*(z*(a*c))=a*c := by decide +kernel
      exact Or.inr (eq ▸ hh)
  have hchoice : c ∈ E ∨ (u ∈ E ∧ a*c ∈ E) := by
    rcases hcy with hc | hac
    · exact Or.inl hc
    rcases hu with hu | huc
    · exact Or.inr ⟨hu,hac⟩
    have hexodd : ∃ w ∈ E, w ∉ alternatingGroup (Fin 6) := by
      by_contra! he
      exact hodd he
    obtain ⟨w,hw,hwo⟩ := hexodd
    obtain ⟨k,rfl⟩ := (mem_sylowCarrier_iff _).mp (hES hw)
    have cert : ∀ k : Fin 16, sylowWords k ∉ alternatingGroup (Fin 6) →
        ∃ n : Fin 8, evenWord n = c*sylowWords k := by decide +kernel
    obtain ⟨n,hn⟩ := cert k hwo
    have he : evenWord n ∈ E := E.mul_mem (E.pow_mem huc _) (E.pow_mem hac _)
    have hc := E.mul_mem (hn ▸ he) (E.inv_mem hw)
    rw [mul_inv_cancel_right] at hc
    exact Or.inl hc
  let N := E ⊔ zpowers r
  have hr : r ∈ N := mem_sup_right (mem_zpowers _)
  have ht : t ∈ N := by
    rcases hchoice with hc | ⟨hu,hac⟩
    · have hcN : c ∈ N := mem_sup_left hc
      have cert : c*r*c*r*c=t := by decide +kernel
      rw [←cert]
      exact N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem hcN hr) hcN) hr) hcN
    · have huN : u ∈ N := mem_sup_left hu
      have hacN : a*c ∈ N := mem_sup_left hac
      have cert : u*r*u*r*(a*c)*r*u*r*u*r*u*(a*c)=t := by decide +kernel
      rw [←cert]
      exact N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem
        (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem huN hr) huN) hr)
          hacN) hr) huN) hr) huN) hr) huN) hacN
  apply top_unique
  rw [←EightStrictShift.canonical_generates E hES hne ⟨dWords j,hyE,hy4⟩]
  exact sup_le le_sup_left (zpowers_le.mpr ht)

private theorem conjugate_even_generates (E J : Subgroup S) (v : S)
    (hES : E ≤ sylowCarrier.map (MulAut.conj v).toMonoidHom)
    (hne : ¬ IsElementaryAbelian 2 E) (hodd : ¬ E ≤ alternatingGroup (Fin 6))
    (hJ : J = E ⊓ (D 6).map (MulAut.conj v).toMonoidHom)
    (hmodel : IsConjugateTo J plus ∨ IsConjugateTo J (evenPart 6))
    (a₀ : alternatingGroup (Fin 6)) (hao : orderOf a₀ = 2) :
    ∃ w : S, E.map (MulAut.conj w).toMonoidHom ⊔ zpowers a₀.val = ⊤ := by
  let f := (MulAut.conj v⁻¹).toMonoidHom
  have back (A : Subgroup S) : (A.map (MulAut.conj v).toMonoidHom).map f = A := by
    rw [CubeCommonFixer.conjugate_twice,inv_mul_cancel,
      show (MulAut.conj (1 : S)).toMonoidHom = MonoidHom.id S from rfl,map_id]
  have hE : E.map f ≤ sylowCarrier := (map_mono hES).trans_eq (back _)
  have hn : ¬ IsElementaryAbelian 2 (E.map f) := by
    intro hh
    let := hh
    apply hne
    apply NonsylowImage.elementary_of_squares
    intro x hx
    apply (MulAut.conj v⁻¹).injective
    rw [map_pow,map_one]
    exact elemPow_eq_one_of_isElementaryAbelian _ (mem_map_of_mem f hx)
  have ho : ¬ E.map f ≤ alternatingGroup (Fin 6) := by
    intro hh
    apply hodd
    intro x hx
    have he := (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem
      (f x) (hh (mem_map_of_mem f hx)) v
    change v*(v⁻¹*x*v)*v⁻¹ ∈ alternatingGroup (Fin 6) at he
    have eq : v*(v⁻¹*x*v)*v⁻¹=x := by group
    rwa [eq] at he
  have hJF : J.map f = E.map f ⊓ D 6 := by
    rw [hJ,map_inf _ _ _ (MulAut.conj v⁻¹).injective,back]
  obtain ⟨m,k,hk⟩ : ∃ m : Fin 2, ∃ k : S,
      J = (EightSelection.model m).map (MulAut.conj k).toMonoidHom := by
    rcases hmodel with ⟨k,hk⟩ | ⟨k,hk⟩
    · exact ⟨0,k,hk⟩
    · exact ⟨1,k,hk⟩
  have hm : ∃ y ∈ E.map f ⊓ D 6, y (4 : Fin 6) ≠ 4 := by
    rw [←hJF,hk,CubeCommonFixer.conjugate_twice]
    exact EightStrictShift.model_moves m (v⁻¹*k) 4
  have hgen := canonical_even_generates (E.map f) hE hn ho hm
  let r₀ : alternatingGroup (Fin 6) := ⟨r,by decide +kernel⟩
  have hro : orderOf r₀ = 2 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  obtain ⟨k,hk⟩ := isConj_iff.mp
    (AlternatingSix.ShadowLocal.involutions_isConj r₀ a₀ hro hao)
  have hr : (MulAut.conj k.val).toMonoidHom r = a₀.val := congrArg Subtype.val hk
  refine ⟨k.val*v⁻¹,?_⟩
  have hh := congrArg (Subgroup.map (MulAut.conj k.val).toMonoidHom) hgen
  rwa [Subgroup.map_sup,CubeCommonFixer.conjugate_twice,MonoidHom.map_zpowers,hr,
    map_top_of_surjective (MulAut.conj k.val).toMonoidHom (MulAut.conj k.val).surjective] at hh


universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

private theorem generating_neighbor_of_even_actor
    (s : FullSymmetricAction h e hz hn d) (hb : 4 < replacementDistance h d)
    (W : Subgroup (FreeAmalgam d.radical))
    (hWG : W ≤ stabilizer d.radical (alpha d.radical))
    (a : Equiv.Perm (Fin 6)) (ha : a ∈ (W.comap (embedM d.radical)).map s.projection)
    (hao : orderOf a = 2) (haeven : a ∈ alternatingGroup (Fin 6)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical t ⊔ W = stabilizer d.radical (alpha d.radical) := by
  let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  obtain ⟨v,hN,_,_,hJ,_,_,_,_⟩ := EightSmallMovers.radical_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d _,
    ←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hN hJ
  obtain ⟨_,hne,_,_⟩ := SylowWholeCore.four_lt_original_sylow_eight_image_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  rw [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hne
  have hmodel : IsConjugateTo (J.map s.projection) plus ∨
      IsConjugateTo (J.map s.projection) (evenPart 6) := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    exact EightBaumann.three_duad_mover_knownSimple (e := e) (hz := hz) (hn := hn) hb
  have hodd : ¬ d.radical.map s.projection ≤ alternatingGroup (Fin 6) := by
    intro hle
    obtain ⟨x,hx⟩ := s.surjective (Equiv.swap 0 1)
    obtain ⟨k,hk,r,hr,hkr⟩ := replacement_product h d x
    have hk' : s.projection k ∈ alternatingGroup (Fin 6) := by
      rw [←s.component_image]
      exact mem_map_of_mem s.projection hk
    have hr' := hle (mem_map_of_mem s.projection hr)
    have hswap : Equiv.swap (0 : Fin 6) 1 ∈ alternatingGroup (Fin 6) := by
      rw [←hx,←hkr,map_mul]
      exact mul_mem hk' hr'
    exact (by decide : Equiv.swap (0 : Fin 6) 1 ∉ alternatingGroup (Fin 6)) hswap
  obtain ⟨k,hk⟩ := conjugate_even_generates (d.radical.map s.projection) (J.map s.projection) v
    ((map_mono d.radical.le_normalizer).trans_eq hN) hne hodd hJ hmodel
      ⟨a,haeven⟩ ((Subgroup.orderOf_coe ⟨a,haeven⟩).symm.trans hao)
  obtain ⟨g,hgk⟩ := s.surjective k
  let A := W.comap (embedM d.radical)
  have hm : (d.radical.map (MulAut.conj g).toMonoidHom).map s.projection =
      (d.radical.map s.projection).map (MulAut.conj k).toMonoidHom := by
    rw [SylowCompatible.image_conjugate,hgk]
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hker : s.projection.ker ≤ d.radical.map (MulAut.conj g).toMonoidHom := by
    rw [s.projection_kernel,←hQ]
    exact map_mono (replacement_core_le_radical h d)
  have hgen : d.radical.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
    apply map_injective_of_ker_le s.projection (hker.trans le_sup_left) le_top
    rw [Subgroup.map_sup,hm,map_top_of_surjective s.projection s.surjective]
    apply top_unique
    rw [←hk]
    exact sup_le_sup_left (zpowers_le.mpr ha) _
  let f := (embedM d.radical g)⁻¹
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    change f ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have hfix : act d.radical f (alpha d.radical) = alpha d.radical := hf
  refine ⟨act d.radical f (beta d.radical),?_,?_⟩
  · rw [←hfix]
    exact (adjacent_act_iff d.radical f (alpha d.radical) (beta d.radical)).mpr
      (base_adjacent d.radical)
  · have hmapA : A.map (embedM d.radical) = W :=
      map_comap_eq_self (hWG.trans_eq (stabilizer_m_base d.radical))
    have hh := congrArg (Subgroup.map (embedM d.radical)) hgen
    rw [Subgroup.map_sup,hmapA,←MonoidHom.range_eq_map] at hh
    rw [Q_act,Q_beta]
    change _ = stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    have hmapR : (d.radical.map (embedM d.radical)).map (MulAut.conj f⁻¹).toMonoidHom =
        (d.radical.map (MulAut.conj g).toMonoidHom).map (embedM d.radical) := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change f⁻¹*embedM d.radical x*(f⁻¹)⁻¹=embedM d.radical (g*x*g⁻¹)
      simp only [f,inv_inv,map_mul,map_inv]
    rw [hmapR]
    exact hh

include e hz hn

/-- The restricted even endpoint actor generates with an actual full edge kernel. -/
theorem large_image_controlled_neighbor_knownSimple
    (hb : 4 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ W : Subgroup (FreeAmalgam d.radical), W ≤ U d.radical a' ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤
        Z d.radical (alpha d.radical) ∧
      (¬ W ≤ Q d.radical (alpha d.radical)) ∧
      ∃ t, Adjacent d.radical (alpha d.radical) t ∧
        Q d.radical t ⊔ W = stabilizer d.radical (alpha d.radical) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hWU,hbound,a,ha,hao,haeven⟩ := critical_radius_even_actor s hc hb2 p hlarge
  have hWG : W ≤ stabilizer d.radical (alpha d.radical) :=
    (hWU.trans (DistanceEight.U_le_Z d.radical a')).trans
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
        (replacementDistance_pos h d) p.critical)
  refine ⟨W,hWU,hbound,?_,generating_neighbor_of_even_actor s hb W hWG a ha hao haeven⟩
  intro hWQ
  have hWker : W.comap (embedM d.radical) ≤ s.projection.ker := by
    rw [s.projection_kernel]
    have hh := comap_mono (f := embedM d.radical) hWQ
    rwa [Q_alpha_comap d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)] at hh
  have hbot := (Subgroup.map_eq_bot_iff (W.comap (embedM d.radical))).mpr hWker
  have hone : a=1 := by
    have hh : a ∈ (⊥ : Subgroup (Equiv.Perm (Fin 6))) := hbot ▸ ha
    exact hh
  rw [hone,orderOf_one] at hao
  omega

/-- A prescribed eligible first-edge seed gives a literal backward critical path. -/
theorem large_image_backward_shift_knownSimple
    (hb : 4 < replacementDistance h d)
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) (act d.radical g delta)
          (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          (∀ k ≤ p.walk.length-2, q.walk.getVert (k+2) = p.walk.getVert k) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hWU,hbound,hWne,t,hat,hgen⟩ := large_image_controlled_neighbor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hlarge
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) ha1 hat
  let c := act d.radical g delta
  have hct : Adjacent d.radical c t := by
    rw [←hgt]
    exact (adjacent_act_iff d.radical g delta (p.walk.getVert 1)).mpr hdelta
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
  have helc : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    apply hel
    change U d.radical (act d.radical g delta) ≤ _ at hh
    rw [U_act,←hB] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh
  have hbad : ¬ Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    intro hbad
    apply helc
    apply (DistanceEight.U_le_Z d.radical c).trans
    apply backward_kernel_le_slice_of_controlled_actor s hb2 p W hWU hWne hbound hat hct hgen
      (Z d.radical c) le_rfl hbad
    exact (show Q d.radical t ≤ stabilizer d.radical c from
      fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c)
  let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct)
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  have hw : w.length = 2 := rfl
  let q := p.prepend_two (by exact Nat.le_of_lt hb2) hcol w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  have hgenZ : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) := by
    apply le_antisymm
    · exact sup_le (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
        (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
          (replacementDistance_pos h d) p.critical)
    · rw [←hgen]
      exact sup_le_sup_left (hWU.trans (DistanceEight.U_le_Z d.radical a')) _
  exact ⟨t,hat,hgenZ,g,hg,hgt,q,hqt,fun i hi => p.prepend_two_overlap _ _ _ _ _ hi⟩

private theorem large_backward_step_base
    (hb : 4 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ c t x, x ∈ stabilizer d.radical (alpha d.radical) ∧
      act d.radical x (p.walk.getVert 1) = t ∧
      act d.radical x (p.walk.getVert 2) = c ∧
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hel := critical_forward_not_le_slice_of_escape s hc hb2
    (EightBaumann.criticalEscape_knownSimple
      (e := e) (hz := hz) (hn := hn) hb) p
  obtain ⟨t,hat,hgen,x,hx,hxt,q,hqt,hover⟩ :=
    large_image_backward_shift_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hlarge hdelta hel
  refine ⟨_,t,x,hx,hxt,rfl,hat,?_,hgen,q,hqt,hover⟩
  rw [←hxt]
  exact (adjacent_act_iff d.radical x _ _).mpr hdelta

/-- Every large critical image above four supplies a generating backward shift.
The chosen local conjugator and every shared vertex are retained. -/
theorem large_backward_step_at_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ c t x, x ∈ stabilizer d.radical a ∧
      act d.radical x (p.walk.getVert 1) = t ∧
      act d.radical x (p.walk.getVert 2) = c ∧
      Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical a ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := large_backward_step_base (e := e) (hz := hz) (hn := hn) hb
    (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  obtain ⟨c,t,x,hx,hxt,hxc,hat,hct,hgen,q,hq1,hover⟩ := base (p.act g⁻¹) (by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge)
  change act d.radical x ((actWalk d.radical g⁻¹ p.walk).getVert 2) = c at hxc
  rw [actWalk_getVert] at hxc
  let y := g⁻¹*x*g
  have hy (v : Vertex d.radical) :
      act d.radical y v = act d.radical g (act d.radical x (act d.radical g⁻¹ v)) := by
    simp only [y,act_mul]
  have hcancel (v : Vertex d.radical) : act d.radical g (act d.radical g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hqc : ∃ r : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g c)
      (act d.radical g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2))),
      r.walk.getVert 1 = act d.radical g t ∧
      ∀ i ≤ p.walk.length-2, r.walk.getVert (i+2) = p.walk.getVert i := by
    refine ⟨q.act g,?_,?_⟩
    · simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act d.radical g) hq1
    · intro i hi
      have he := congrArg (act d.radical g) (hover i (by
        simpa only [CriticalPath.act,actWalk_length] using hi))
      simpa only [CriticalPath.act,actWalk_getVert,hcancel] using he
  have hend : act d.radical g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2)) =
      p.walk.getVert (p.walk.length-2) := by
    change act d.radical g ((actWalk d.radical g⁻¹ p.walk).getVert
      ((actWalk d.radical g⁻¹ p.walk).length-2)) = _
    rw [actWalk_length,actWalk_getVert,hcancel]
  rw [hend] at hqc
  obtain ⟨r,hr1,hrover⟩ := hqc
  refine ⟨act d.radical g c,act d.radical g t,y,?_,?_,?_,?_,?_,?_,r,hr1,hrover⟩
  · change act d.radical y a = a
    rw [hy,show act d.radical x (act d.radical g⁻¹ a) = act d.radical g⁻¹ a from hx,hcancel]
  · rw [hy]
    have hh := congrArg (act d.radical g) hxt
    simpa only [CriticalPath.act,actWalk_getVert] using hh
  · rw [hy,hxc]
  · simpa only [hcancel] using (adjacent_act_iff d.radical g _ _).mpr hat
  · exact (adjacent_act_iff d.radical g _ _).mpr hct
  · have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
    rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hcancel,hcancel] at he
    exact he

/-- Every large critical image admits an actual generating backward shift. -/
theorem large_backwardShift_with_edge_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) : ∃ q : BackwardShift (h := h) p,
      act d.radical q.transporter (p.walk.getVert 1) = q.edge := by
  obtain ⟨c,t,x,hx,hxt,hxc,hat,hct,hgen,q,hq1,hqo⟩ :=
    large_backward_step_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p hlarge
  exact ⟨⟨c,t,x,hx,hxc,hat,hct,hgen,q,hq1,hqo⟩,hxt⟩


/-- Starting with a large critical image, at most two actual generating
backward shifts reach a small critical image. Every shift retains the same
transporter on its first two vertices and all shared walk vertices. -/
theorem large_image_reaches_small_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ q : BackwardShift (h := h) p,
      act d.radical q.transporter (p.walk.getVert 1) = q.edge ∧
      ((Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex
          (Z d.radical q.start) < 4 ∨
        ∃ r : BackwardShift (h := h) q.path,
          act d.radical r.transporter (q.path.walk.getVert 1) = r.edge ∧
          (Q d.radical (q.path.walk.getVert (q.path.walk.length-2))).relIndex
            (Z d.radical r.start) < 4) := by
  obtain ⟨q,hqe⟩ := large_backwardShift_with_edge_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hlarge
  refine ⟨q,hqe,?_⟩
  by_cases hq : (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex
      (Z d.radical q.start) < 4
  · exact Or.inl hq
  obtain ⟨r,hre⟩ := large_backwardShift_with_edge_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q.path (by omega)
  have hh := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r
  exact Or.inr ⟨r,hre,by rw [hh.2.1]; decide⟩

/-- Above four a genuine critical pair has both images and its full
commutator of order two, and its actual forward slice has index greater than two.
No mover model or critical-image choice remains as an input. -/
theorem exists_small_critical_knownSimple (hb : 4 < replacementDistance h d) :
    ∃ a z : Vertex d.radical, ∃ p : CriticalPath d.radical (replacementGeometry h d) a z,
      (Q d.radical z).relIndex (Z d.radical a) = 2 ∧
      (Q d.radical a).relIndex (Z d.radical z) = 2 ∧
      Nat.card (⁅Z d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) := by
  obtain ⟨z,⟨p⟩⟩ := CriticalPath.exists_from (R := d.radical)
    (geometry := replacementGeometry h d) (a := alpha d.radical) rfl
  have hex : ∃ a z : Vertex d.radical,
      ∃ p : CriticalPath d.radical (replacementGeometry h d) a z,
        (Q d.radical z).relIndex (Z d.radical a) < 4 := by
    by_cases hs : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4
    · exact ⟨_,_,p,hs⟩
    obtain ⟨q,_,hq | ⟨r,_,hr⟩⟩ := large_image_reaches_small_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p (by omega)
    · exact ⟨_,_,q.path,hq⟩
    · exact ⟨_,_,r.path,hr⟩
  obtain ⟨a,z,p,hs⟩ := hex
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hi := small_critical_indices s hc p hs
  exact ⟨a,z,p,hi.1,hi.2,small_critical_commutator_card s hc p hs,
    EightBaumann.small_forward_slice_strict_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hs⟩

/-- Each actual edge at each component vertex has a neighboring seed with
strict Baumann slice. This uses a constructed small critical pair, transported
on the same replacement graph. -/
theorem edge_strict_seed_knownSimple
    (hb : 4 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ∃ c : Vertex d.radical, Adjacent d.radical c t ∧
      2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical c) := by
  obtain ⟨c,z,p,_,_,_,hi⟩ := exists_small_critical_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  have hl : 4 < p.walk.length := p.length_eq_b ▸ hb
  have hc1 : Adjacent d.radical c (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have h21 : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨g,hg | hg⟩ := edge_transitive d.radical hc1 hat
  · refine ⟨act d.radical g (p.walk.getVert 2),?_,?_⟩
    · rw [←hg.2]
      exact (adjacent_act_iff d.radical g _ _).mpr h21
    · rw [←hg.1,Escape.PairingControl.FirstPairing.B_act
        (by omega : 2 < replacementDistance h d) g c p.start_color,U_act,
        relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
      exact hi
  · have ht : color d.radical t = false := by
      rw [←hg.1,action_preserves_color,p.start_color]
    exact False.elim ((adjacent_color_ne d.radical hat) (ha.trans ht.symm))

/-- Apply the large-image generating shift to the original MS radical.
Its restriction has index two over the transported replacement edge core;
neither the original radical nor the whole quotient kernel is discarded. -/
theorem original_radical_large_backward_knownSimple
    (hb : 4 < replacementDistance h d)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical)))
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    ∃ q : BackwardShift (h := h) p,
      act d.radical q.transporter (beta d.radical) = q.edge ∧
      (Q d.radical q.edge).relIndex
        (T.map (MulAut.conj q.transporter⁻¹).toMonoidHom) = 2 := by
  obtain ⟨q,hqe⟩ := large_backwardShift_with_edge_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hlarge
  rw [hfirst] at hqe
  refine ⟨q,hqe,?_⟩
  rw [←hqe,Q_act,relIndex_map_map_of_injective _ _ (MulAut.conj q.transporter⁻¹).injective,
    Q_beta,relIndex_map_map_of_injective _ _ (embedM_injective d.radical)]
  exact (SylowWholeCore.four_lt_original_sylow_eight_image_knownSimple
    (e := e) (hz := hz) (hn := hn) hb).2.2.1

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightLarge
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

