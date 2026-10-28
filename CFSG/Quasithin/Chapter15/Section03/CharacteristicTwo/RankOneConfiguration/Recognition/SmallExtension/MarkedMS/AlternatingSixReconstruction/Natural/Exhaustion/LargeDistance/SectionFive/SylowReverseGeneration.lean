module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowReverseOmega
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowCompatible

/-!
# Reverse-mover generation and equality above distance six

Every index-two subgroup of the six-letter Sylow group contains a common
square. Two explicit selectors carry that square to involutions which,
together with the critical transposition, generate the full symmetric group.
Each selected Sylow group also generates with the same transposition. These
identities lift through the actual replacement quotient and graph embedding,
retaining the whole quotient kernel and both central covers.

In the nonsplit omega case, each selected generating edge supplies a literal
backward shift. The previously proved whole-core containment allows the paired
index-two generation identity to apply to their opposite movers. Both movers
and the endpoint seed fix the common reverse line, hence so does the whole
intermediate stabilizer. The full critical-kernel normalizer is its line
centralizer; this makes the kernel/seed join invariant and forces it into the
Baumann slice, contrary to the strict slice estimate.

Thus the terminal movers agree above distance six. Repeated aligned backward
shifts construct the required orbit relations, and their actual transporters
pull equality back to the first two edges of every original critical path.
The original-radical consumer retains its restriction, transporter and both
whole adjacent cores. The terminal distance exclusion, distance-six case,
image-eight branch and distance-four estimates remain separate obligations.

The finite common-square argument and strict-line contradiction follow the
source comparison also used in Exceptional/OriginalSylow/BorelSelectors and
TerminalMoverEquality. All quotient lifts and graph applications here are
proved on the natural replacement itself.
Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)(c), (5.9)--(5.10), printed pp.915--923, especially p.923.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders.Six
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace SylowReverseGeneration
local notation "S" => Equiv.Perm (Fin 6)
private def selector (i : Fin 2) : S :=
  if i = 0 then Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4
  else Equiv.swap 1 3 * Equiv.swap 3 5 * Equiv.swap 5 4
private abbrev square : S := Equiv.swap 0 1 * Equiv.swap 2 3
private abbrev transposition : S := Equiv.swap 0 1

private theorem square_in_index_two (J : Subgroup S) (hi : J.relIndex sylowCarrier = 2) :
    square ∈ J := by
  let : (J.subgroupOf sylowCarrier).Normal := normal_of_index_eq_two hi
  have hr : sylowWords 9 ∈ sylowCarrier := (mem_sylowCarrier_iff _).mpr ⟨9,rfl⟩
  have hh := (J.subgroupOf sylowCarrier).pow_index_mem ⟨sylowWords 9,hr⟩
  change sylowWords 9 ^ J.relIndex sylowCarrier ∈ J at hh
  rw [hi,show sylowWords 9 ^ 2 = square by decide +kernel] at hh
  exact hh

private theorem selector_generates (i : Fin 2) :
    sylowCarrier.map (MulAut.conj (selector i)).toMonoidHom ⊔ zpowers transposition = ⊤ := by
  let F := sylowCarrier.map (MulAut.conj (selector i)).toMonoidHom ⊔ zpowers transposition
  let root (j : Fin 16) : S := (MulAut.conj ((MulAut.conj (selector i)) (sylowWords j))) transposition
  have hr (j : Fin 16) : root j ∈ F := by
    have hj : (MulAut.conj (selector i)) (sylowWords j) ∈ F :=
      mem_sup_left (mem_map_of_mem _ ((mem_sylowCarrier_iff _).mpr ⟨j,rfl⟩))
    exact F.mul_mem (F.mul_mem hj (mem_sup_right (mem_zpowers _))) (F.inv_mem hj)
  apply CubeCommonFixer.chain_generates 1
  intro j
  have cert : ∀ i : Fin 2, ∀ j : Fin 5, ∃ k l : Fin 16,
      let f := fun k => (MulAut.conj ((MulAut.conj (selector i)) (sylowWords k))) transposition
      f k * f l * f k = Equiv.swap j.castSucc j.succ := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact ⟨0,0,by decide +kernel⟩
    · exact ⟨0,1,by decide +kernel⟩
    · exact ⟨1,8,by decide +kernel⟩
    · exact ⟨8,10,by decide +kernel⟩
    · exact ⟨0,14,by decide +kernel⟩
    · exact ⟨0,0,by decide +kernel⟩
    · exact ⟨4,8,by decide +kernel⟩
    · exact ⟨1,8,by decide +kernel⟩
    · exact ⟨0,5,by decide +kernel⟩
    · exact ⟨0,14,by decide +kernel⟩
  obtain ⟨k,l,hkl⟩ := cert i j
  change Equiv.swap j.castSucc j.succ ∈ F
  rw [←hkl]
  exact F.mul_mem (F.mul_mem (hr k) (hr l)) (hr k)

private theorem selectors_generate_index_two (J : Subgroup S) (hi : J.relIndex sylowCarrier = 2) :
    (J.map (MulAut.conj (selector 0)).toMonoidHom ⊔
      J.map (MulAut.conj (selector 1)).toMonoidHom) ⊔ zpowers transposition = ⊤ := by
  let F := (J.map (MulAut.conj (selector 0)).toMonoidHom ⊔
    J.map (MulAut.conj (selector 1)).toMonoidHom) ⊔ zpowers transposition
  let b := (MulAut.conj (selector 0)) square
  let c := (MulAut.conj (selector 1)) square
  have hb : b ∈ F := mem_sup_left (mem_sup_left (mem_map_of_mem _ (square_in_index_two J hi)))
  have hc : c ∈ F := mem_sup_left (mem_sup_right (mem_map_of_mem _ (square_in_index_two J hi)))
  let word (i : Fin 6) : S := (b*c)^(i.val/2) * (if i.val%2 = 0 then 1 else b)
  have hw (i : Fin 6) : word i ∈ F := by
    apply F.mul_mem (F.pow_mem (F.mul_mem hb hc) _)
    split
    · exact F.one_mem
    · exact hb
  let v : S := Equiv.swap 2 3 * Equiv.swap 3 5
  apply CubeCommonFixer.chain_generates v
  have cert : ∀ j : Fin 5, ∃ k : Fin 6,
      (MulAut.conj (word k)) transposition = (MulAut.conj v) (Equiv.swap j.castSucc j.succ) := by
    intro j
    fin_cases j
    · exact ⟨0,by decide +kernel⟩
    · exact ⟨5,by decide +kernel⟩
    · exact ⟨4,by decide +kernel⟩
    · exact ⟨3,by decide +kernel⟩
    · exact ⟨2,by decide +kernel⟩
  intro j
  obtain ⟨k,hk⟩ := cert j
  rw [←hk]
  exact F.mul_mem (F.mul_mem (hw k) (mem_sup_right (mem_zpowers _))) (F.inv_mem (hw k))

private theorem paired_selectors (u a : S) (ha : a.IsSwap) :
    ∃ g : Fin 2 → S,
      (∀ i, (sylowCarrier.map (MulAut.conj u).toMonoidHom).map
        (MulAut.conj (g i)).toMonoidHom ⊔ zpowers a = ⊤) ∧
      ∀ J : Subgroup S, J.relIndex (sylowCarrier.map (MulAut.conj u).toMonoidHom) = 2 →
        (J.map (MulAut.conj (g 0)).toMonoidHom ⊔
          J.map (MulAut.conj (g 1)).toMonoidHom) ⊔ zpowers a = ⊤ := by
  obtain ⟨v,hv⟩ := CubeCommonFixer.swap_conjugator a ha
  let g := fun i => v.val * selector i * u⁻¹
  have hm (J : Subgroup S) (i : Fin 2) :
      (J.map (MulAut.conj u).toMonoidHom).map (MulAut.conj (g i)).toMonoidHom =
        (J.map (MulAut.conj (selector i)).toMonoidHom).map (MulAut.conj v.val).toMonoidHom := by
    rw [CubeCommonFixer.conjugate_twice,CubeCommonFixer.conjugate_twice]
    congr 3
    dsimp only [g]
    group
  have hta : (MulAut.conj v.val).toMonoidHom transposition = a := hv
  refine ⟨g,?_,?_⟩
  · intro i
    have hh := congrArg (Subgroup.map (MulAut.conj v.val).toMonoidHom) (selector_generates i)
    rwa [Subgroup.map_sup,MonoidHom.map_zpowers,hta,
      map_top_of_surjective _ (MulAut.conj v.val).surjective,←hm] at hh
  · intro J hi
    let J₀ := J.map (MulAut.conj u⁻¹).toMonoidHom
    have hJ : J₀.map (MulAut.conj u).toMonoidHom = J := by
      dsimp only [J₀]
      rw [CubeCommonFixer.conjugate_twice,mul_inv_cancel]
      exact map_id J
    have hi₀ : J₀.relIndex sylowCarrier = 2 := by
      rw [←relIndex_map_map_of_injective (f := (MulAut.conj u).toMonoidHom) J₀ sylowCarrier (MulAut.conj u).injective,hJ]
      exact hi
    have hh := congrArg (Subgroup.map (MulAut.conj v.val).toMonoidHom)
      (selectors_generate_index_two J₀ hi₀)
    rwa [Subgroup.map_sup,Subgroup.map_sup,MonoidHom.map_zpowers,hta,
      map_top_of_surjective _ (MulAut.conj v.val).surjective,←hm,←hm,hJ] at hh

private theorem paired_lifts {H : Type*} [Group H]
    (π : H →* S) (hs : Function.Surjective π) (T A : Subgroup H)
    (hkT : π.ker ≤ T) (u : S)
    (hT : T.map π = sylowCarrier.map (MulAut.conj u).toMonoidHom)
    (a : S) (ha : a.IsSwap) (haA : a ∈ A.map π) :
    ∃ g : Fin 2 → H,
      (∀ i, T.map (MulAut.conj (g i)).toMonoidHom ⊔ A = ⊤) ∧
      ∀ J : Subgroup H, π.ker ≤ J → J ≤ T → J.relIndex T = 2 →
        (J.map (MulAut.conj (g 0)).toMonoidHom ⊔
          J.map (MulAut.conj (g 1)).toMonoidHom) ⊔ A = ⊤ := by
  obtain ⟨f,hgen,hpair⟩ := paired_selectors u a ha
  choose g hg using fun i => hs (f i)
  have hker (i : Fin 2) : π.ker.map (MulAut.conj (g i)).toMonoidHom = π.ker :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top _)
  have hkmap (J : Subgroup H) (hkJ : π.ker ≤ J) (i : Fin 2) :
      π.ker ≤ J.map (MulAut.conj (g i)).toMonoidHom := by
    rw [←hker i]
    exact map_mono hkJ
  have lift (J : Subgroup H) (hkJ : π.ker ≤ J) (him : J.map π = ⊤) : J = ⊤ := by
    apply map_injective_of_ker_le π hkJ le_top
    rw [him,map_top_of_surjective π hs]
  refine ⟨g,?_,?_⟩
  · intro i
    apply lift _ ((hkmap T hkT i).trans le_sup_left)
    rw [Subgroup.map_sup,SylowCompatible.image_conjugate,hg,hT]
    apply top_unique
    rw [←hgen i]
    exact sup_le_sup_left (zpowers_le.mpr haA) _
  · intro J hkJ hJT hi
    have hji : (J.map π).relIndex (sylowCarrier.map (MulAut.conj u).toMonoidHom) = 2 := by
      rw [←hT,relIndex_map_map,sup_of_le_left hkJ,sup_of_le_left hkT]
      exact hi
    apply lift _ ((hkmap J hkJ 0).trans (le_sup_left.trans le_sup_left))
    rw [Subgroup.map_sup,Subgroup.map_sup,SylowCompatible.image_conjugate,
      SylowCompatible.image_conjugate,hg,hg]
    apply top_unique
    rw [←hpair (J.map π) hji]
    exact sup_le_sup_left (zpowers_le.mpr haA) _

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
private theorem paired_transports_base
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4) :
    ∃ g : Fin 2 → FreeAmalgam d.radical,
      (∀ i, g i ∈ stabilizer d.radical (alpha d.radical)) ∧
      (∀ i, Q d.radical (act d.radical (g i) (beta d.radical)) ⊔ Z d.radical z =
        stabilizer d.radical (alpha d.radical)) ∧
      ∀ J : Subgroup (FreeAmalgam d.radical), Q d.radical (alpha d.radical) ≤ J →
        J ≤ Q d.radical (beta d.radical) → J.relIndex (Q d.radical (beta d.radical)) = 2 →
        (J.map (MulAut.conj (g 0)⁻¹).toMonoidHom ⊔
          J.map (MulAut.conj (g 1)⁻¹).toMonoidHom) ⊔ Z d.radical z =
            stabilizer d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨a,ha,hswap⟩ := small_critical_image_swap s hc p hsmall
  obtain ⟨u,hN,_⟩ := SylowSmallMovers.normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  have hnormal := SylowLarge.sixteen_radical_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard
  rw [hnormal] at hN
  let A := (Z d.radical z).comap (embedM d.radical)
  obtain ⟨f,hgen,hpair⟩ := paired_lifts s.projection s.surjective d.radical A
    (s.projection_kernel.symm ▸ replacement_core_le_radical h d) u hN a hswap ha
  let g := fun i => (embedM d.radical (f i))⁻¹
  have hg (i : Fin 2) : g i ∈ stabilizer d.radical (alpha d.radical) := by
    change g i ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨(f i)⁻¹,by rw [map_inv]⟩
  have hm (J : Subgroup d.overgroup) (i : Fin 2) :
      (J.map (MulAut.conj (f i)).toMonoidHom).map (embedM d.radical) =
        (J.map (embedM d.radical)).map (MulAut.conj (g i)⁻¹).toMonoidHom := by
    rw [SylowCompatible.image_conjugate]
    simp only [g,inv_inv]
  have hrange : (embedM d.radical).range = stabilizer d.radical (alpha d.radical) :=
    (stabilizer_m_base d.radical).symm
  have hAm : A.map (embedM d.radical) = Z d.radical z := map_comap_eq_self
    ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq hrange.symm)
  refine ⟨g,hg,?_,?_⟩
  · intro i
    have hh := congrArg (Subgroup.map (embedM d.radical)) (hgen i)
    rwa [Subgroup.map_sup,hm,←Q_beta,←Q_act,hAm,←MonoidHom.range_eq_map,hrange] at hh
  · intro J hQJ hJT hi
    let J₀ := J.comap (embedM d.radical)
    have hJm : J₀.map (embedM d.radical) = J := map_comap_eq_self
      ((hJT.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical (base_adjacent d.radical)))).trans_eq hrange.symm)
    have hkJ : s.projection.ker ≤ J₀ := by
      rw [s.projection_kernel]
      apply map_le_iff_le_comap.mp
      rw [←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
      exact hQJ
    have hJ₀T : J₀ ≤ d.radical := by
      apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
      rw [hJm,←Q_beta]
      exact hJT
    have hi₀ : J₀.relIndex d.radical = 2 := by
      rw [←relIndex_map_map_of_injective J₀ d.radical (embedM_injective d.radical),hJm,←Q_beta]
      exact hi
    have hh := congrArg (Subgroup.map (embedM d.radical)) (hpair J₀ hkJ hJ₀T hi₀)
    rwa [Subgroup.map_sup,Subgroup.map_sup,hm,hm,hJm,hAm,←MonoidHom.range_eq_map,hrange] at hh

include e hz hn in
/-- Two actual transporters simultaneously generate with the critical seed
and with every index-two subgroup of the original first-edge core containing
the starting whole core. Both transports use the natural replacement graph. -/
theorem paired_transports_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4) :
    ∃ g : Fin 2 → FreeAmalgam d.radical,
      (∀ i, g i ∈ stabilizer d.radical a) ∧
      (∀ i, Q d.radical (act d.radical (g i) (p.walk.getVert 1)) ⊔ Z d.radical z =
        stabilizer d.radical a) ∧
      ∀ J : Subgroup (FreeAmalgam d.radical), Q d.radical a ≤ J →
        J ≤ Q d.radical (p.walk.getVert 1) → J.relIndex (Q d.radical (p.walk.getVert 1)) = 2 →
        (J.map (MulAut.conj (g 0)⁻¹).toMonoidHom ⊔
          J.map (MulAut.conj (g 1)⁻¹).toMonoidHom) ⊔ Z d.radical z = stabilizer d.radical a := by
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ replacementDistance_pos h d)
  obtain ⟨k,⟨hka,hkt⟩ | ⟨hka,hkt⟩⟩ := (adjacent_iff_exists_common d.radical _ _).mp hat
  swap
  · have hh := p.start_color
    rw [hka] at hh
    cases hh
  have ha : act d.radical k⁻¹ a = alpha d.radical := by
    rw [hka,act_mVertex,mul_inv_cancel]
    rfl
  have ht : act d.radical k⁻¹ (p.walk.getVert 1) = beta d.radical := by
    rw [hkt,act_hVertex,mul_inv_cancel]
    rfl
  have hs : (Q d.radical (act d.radical k⁻¹ z)).relIndex (Z d.radical (act d.radical k⁻¹ a)) < 4 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hsmall
  have hh := paired_transports_base (h := h) (e := e) (hz := hz) (hn := hn)
    (d := d) (z := act d.radical k⁻¹ z) hb hcard
  rw [←ha,←ht] at hh
  obtain ⟨g,hg,hgen,hpair⟩ := hh (p.act k⁻¹) hs
  let f := fun i => k⁻¹*g i*k
  have transform (i : Fin 2) (v : Vertex d.radical) :
      act d.radical (f i) v = act d.radical k (act d.radical (g i) (act d.radical k⁻¹ v)) := by
    simp only [f,act_mul]
  have cancel (v : Vertex d.radical) : act d.radical k (act d.radical k⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hf (i : Fin 2) : f i ∈ stabilizer d.radical a := by
    change act d.radical (f i) a = a
    rw [transform,show act d.radical (g i) (act d.radical k⁻¹ a) = act d.radical k⁻¹ a from hg i,cancel]
  refine ⟨f,hf,?_,?_⟩
  · intro i
    have hm := congrArg (Subgroup.map (MulAut.conj k⁻¹).toMonoidHom) (hgen i)
    rwa [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,cancel,cancel,←transform] at hm
  · intro J hQJ hJT hi
    let Jb := J.map (MulAut.conj k).toMonoidHom
    have hQb : Q d.radical (act d.radical k⁻¹ a) ≤ Jb := by
      rw [Q_act,inv_inv]
      exact map_mono hQJ
    have hTb : Jb ≤ Q d.radical (act d.radical k⁻¹ (p.walk.getVert 1)) := by
      rw [Q_act,inv_inv]
      exact map_mono hJT
    have hib : Jb.relIndex (Q d.radical (act d.radical k⁻¹ (p.walk.getVert 1))) = 2 := by
      rw [Q_act,inv_inv,relIndex_map_map_of_injective _ _ (MulAut.conj k).injective]
      exact hi
    have hm := congrArg (Subgroup.map (MulAut.conj k⁻¹).toMonoidHom) (hpair Jb hQb hTb hib)
    have mapJ (i : Fin 2) : (Jb.map (MulAut.conj (g i)⁻¹).toMonoidHom).map
        (MulAut.conj k⁻¹).toMonoidHom = J.map (MulAut.conj (f i)⁻¹).toMonoidHom := by
      dsimp only [Jb]
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro v
      change k⁻¹*((g i)⁻¹*(k*v*k⁻¹)*(g i)⁻¹⁻¹)*k⁻¹⁻¹ = (f i)⁻¹*v*(f i)⁻¹⁻¹
      dsimp only [f]
      group
    rwa [Subgroup.map_sup,Subgroup.map_sup,mapJ,mapJ,←Z_act,←stabilizer_act,cancel,cancel] at hm

include e hz hn in
private theorem generating_backward_of_nonsplit
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hns : X d.radical z ≠ U d.radical z ⊔
      (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))))
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a)
    (hgen : Q d.radical (act d.radical g (p.walk.getVert 1)) ⊔ Z d.radical z = stabilizer d.radical a) :
    ∃ b : BackwardShift (h := h) p,
      b.transporter = g ∧ b.edge = act d.radical g (p.walk.getVert 1) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  let t := act d.radical g (p.walk.getVert 1)
  let c := act d.radical g (p.walk.getVert 2)
  have hat : Adjacent d.radical a t := by
    have hh := (adjacent_act_iff d.radical g _ _).mpr ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 0) (by omega)))
    simpa only [SimpleGraph.Walk.getVert_zero,show act d.radical g a = a from hg] using hh
  have hct : Adjacent d.radical c t := (adjacent_act_iff d.radical g _ _).mpr
    (adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega))))
  have hcol : color d.radical c = false := by
    have hh₁ := adjacent_color_ne d.radical hat
    have hh₂ := adjacent_color_ne d.radical hct
    rw [p.start_color] at hh₁
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have hBm : (B d.radical a ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical a ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 a p.start_color ((stabilizer d.radical a).inv_mem hg))
  have hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) := by
    dsimp only [c]
    rw [U_act,←hBm,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact SylowForwardSpan.sixteen_small_forward_slice_strict_at_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall
  have hnorm := SylowCompatible.generating_endpoint_does_not_normalize
    (e := e) (hz := hz) (hn := hn) hb p.start_color hat hct hgen hstrict
  have hescape : ¬ Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    intro htrap
    exact hns (SylowPairedFixer.trapped_nonnormalized_full_kernel_knownSimple
      (e := e) (hz := hz) (hn := hn) hb2 p hsmall hat hct htrap hnorm).1
  let walk : (cosetGraph d.radical).Walk c a :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct)
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  have hw : walk.length = 2 := rfl
  let q := p.prepend_two (Nat.le_of_lt hb2) hcol walk hw hescape
  have hq : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,hw,
      show 1<2 from by decide,ite_true,walk,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  exact ⟨⟨c,t,g,hg,rfl,hat,hct,hgen,q,hq,fun i hi => p.prepend_two_overlap _ _ _ _ _ hi⟩,rfl,rfl⟩

include e hz hn in
private theorem paired_backward_generation
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hns : X d.radical z ≠ U d.radical z ⊔
      (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))))
    (hcores : ∀ b : BackwardShift (h := h) p, Q d.radical a ≤
      SmallMover.join (U d.radical b.start) (Q d.radical b.start) (Q d.radical b.edge) 4) :
    ∃ b₀ b₁ : BackwardShift (h := h) p,
      (SmallMover.join (U d.radical b₀.start) (Q d.radical b₀.start) (Q d.radical b₀.edge) 4 ⊔
        SmallMover.join (U d.radical b₁.start) (Q d.radical b₁.start) (Q d.radical b₁.edge) 4) ⊔
          Z d.radical z = stabilizer d.radical a := by
  obtain ⟨g,hg,hgen,hpair⟩ := paired_transports_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall
  choose b hbtrans hbedge using fun i => generating_backward_of_nonsplit
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hns (g i) (hg i) (hgen i)
  let E := SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2))
    (Q d.radical (p.walk.getVert 1)) 4
  have hEm (i : Fin 2) : E.map (MulAut.conj (g i)⁻¹).toMonoidHom =
      SmallMover.join (U d.radical (b i).start) (Q d.radical (b i).start) (Q d.radical (b i).edge) 4 := by
    dsimp only [E]
    rw [SmallMover.join_map _ (MulAut.conj _).injective,←U_act,←Q_act,←Q_act,←hbedge]
    have hs : act d.radical (g i) (p.walk.getVert 2) = (b i).start :=
      hbtrans i ▸ (b i).start_eq
    rw [hs]
  have hcore : Q d.radical a ≤ E := by
    have hh := hcores (b 0)
    rw [←hEm] at hh
    have hQa : (Q d.radical a).map (MulAut.conj (g 0)⁻¹).toMonoidHom = Q d.radical a := by
      rw [←Q_act,show act d.radical (g 0) a = a from hg 0]
    rw [←hQa] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj _).injective).mp hh
  have hcol : color d.radical (p.walk.getVert 2) = false := by
    have hh := (b 0).path.start_color
    rw [←(b 0).start_eq,action_preserves_color] at hh
    exact hh
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have had : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hmover := SylowAdjacent.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard hcol had
  have hh := hpair E hcore hmover.2.1 hmover.2.2.2.1
  rw [hEm,hEm] at hh
  exact ⟨b 0,b 1,hh⟩

include e hz hn in
private theorem backward_line_not_central
    (hb : 4 < replacementDistance h d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (b : BackwardShift (h := h) p)
    (hsmall : (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z d.radical b.start) < 4)
    (hnorm : Z d.radical z ≤ normalizer
      (((Z d.radical b.start ⊓ Q d.radical (p.walk.getVert (p.walk.length-2))) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hnot : ¬ Z d.radical b.start ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)) ≤
      B d.radical a ((replacementGeometry h d).Z_normal _)) :
    ¬ ⁅Z d.radical b.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  intro hcentral
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let K := Z d.radical b.start ⊓ Q d.radical (p.walk.getVert (p.walk.length-2))
  let N := K ⊔ Z d.radical a
  have hTa : Q d.radical b.edge ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical b.adjacent_start)
  have hTb : Q d.radical b.edge ≤ stabilizer d.radical b.start :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical b.adjacent_shift)
  have hTK : Q d.radical b.edge ≤ normalizer (K : Set (FreeAmalgam d.radical)) := by
    have hh := le_inf hTb (hTa.trans (le_centralizer_iff.mp hcentral))
    rw [←small_critical_kernel_normalizer_eq_line_centralizer s hc b.path hsmall] at hh
    exact hh.trans inf_le_right
  have hGN : stabilizer d.radical a ≤ normalizer (N : Set (FreeAmalgam d.radical)) := by
    rw [←b.generation]
    exact sup_le ((le_inf hTK (hTa.trans (Z_normalized d.radical a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)) hnorm
  have hZV : Z d.radical b.start ≤ V d.radical a := by
    have hdist : (cosetGraph d.radical).dist b.start a ≤ 2 := by
      have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr b.adjacent_shift)
      have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical b.adjacent_start))
      simpa only [h₁,h₂] using (cosetGraph_connected d.radical).dist_triangle
        (u := b.start) (v := b.edge) (w := a)
    exact (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)
  have hNV : N ≤ V d.radical a := sup_le (inf_le_left.trans hZV) (Z_le_VBall d.radical a 2)
  let := finite_stabilizer d.radical a
  have hVG : V d.radical a ≤ stabilizer d.radical a :=
    (replacementGeometry h d).V_local a p.start_color (by
      rw [(replacementGeometry h d).distance_constant a p.start_color]
      exact (show 2 < replacementDistance h d by omega))
  let : Finite (Z d.radical b.start ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (sup_le (hZV.trans hVG) (Z_le_stabilizer d.radical a)))
      (inclusion_injective _)
  have hNi : (Z d.radical a).relIndex N ≤ 8 :=
    (relIndex_le_of_le_right (show N ≤ Z d.radical b.start ⊔ Z d.radical a from
      sup_le_sup inf_le_left le_rfl) index_ne_zero_of_finite).trans
      (SylowSpanSelection.adjacent_seed_span_index_le_eight
        (e := e) (hz := hz) (hn := hn) hb p.start_color b.adjacent_start b.adjacent_shift)
  exact hnot (le_sup_left.trans (residual_small_radius_le_slice_knownSimple (e := e)
    (by omega) p.start_color N hNV ((Ltilde_le_stabilizer a).trans hGN) hNi))

include e hz hn in
private theorem reverse_shift_small
    (hb : 6 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) (v : BackwardShift (h := h) t.path)
    (w : BackwardShift (h := h) v.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d))
    (hv : act d.radical v.transporter (t.path.walk.getVert 1) = v.edge)
    (hne : SmallMover.join (U d.radical v.start) (Q d.radical v.start) (Q d.radical v.edge) 4 ≠
      SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical v.edge) 4)
    (p' : CriticalPath d.radical (replacementGeometry h d)
      (v.path.walk.getVert (v.path.walk.length-2)) w.start)
    (hrev : ∀ i, p'.walk.getVert i = w.path.walk.getVert (w.path.walk.length-i))
    (b₀ : BackwardShift (h := h) p') :
    (Q d.radical v.start).relIndex (Z d.radical b₀.start) < 4 := by
  have hb4 : 4 < replacementDistance h d := by omega
  obtain ⟨cp,_,hQ,hC⟩ := reverse_backward_seed_locations (h := h) (d := d)
    (a := t.start) (a' := r.path.walk.getVert (r.path.walk.length-2)) hb t.path v w p' hrev b₀
  have hpair := four_shift_terminal_seed_pair_knownSimple
    (h := h) (e := e) (hz := hz) (hn := hn) hb4 hcard p q r t v hr hv hne cp cp hQ hQ hC hC
  have hi := hpair.1
  have hle := relIndex_le_of_le_right (H := Q d.radical v.start)
      (show Z d.radical b₀.start ≤ Q d.radical v.start ⊔
        (Z d.radical b₀.start ⊔ Z d.radical b₀.start) from le_sup_left.trans le_sup_right)
      (by rw [hi]; decide)
  omega

include e hz hn in
set_option maxHeartbeats 300000 in
/-- The two literal reverse movers and the endpoint seed centralize their
common line and generate the whole intermediate stabilizer. The resulting
kernel invariance contradicts the strict slice, so the terminal movers agree. -/
theorem five_shift_mover_eq_gt_six_knownSimple
    (hb : 6 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) (v : BackwardShift (h := h) t.path)
    (w : BackwardShift (h := h) v.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d))
    (hv : act d.radical v.transporter (t.path.walk.getVert 1) = v.edge) :
    SmallMover.join (U d.radical v.start) (Q d.radical v.start) (Q d.radical v.edge) 4 =
      SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical v.edge) 4 := by
  by_contra hne
  have hb4 : 4 < replacementDistance h d := by omega
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨p',hrev,b,_,hHcard,hHX,hall⟩ := five_shift_reverse_omega_knownSimple
    (h := h) (e := e) (hz := hz) (hn := hn) hb hcard p q r t v w hr hv hne
  let z := v.path.walk.getVert (v.path.walk.length-2)
  let H := ⁅Z d.radical b.start,Z d.radical v.start⁆
  have hpre : p'.walk.getVert (p'.walk.length-2) = v.start := by
    rw [hrev]
    have hl : w.path.walk.length = replacementDistance h d := w.path.length_eq_b
    have hl' : p'.walk.length = replacementDistance h d := p'.length_eq_b
    rw [show w.path.walk.length-(p'.walk.length-2)=2 by omega]
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using w.overlap 0 (Nat.zero_le _)
  have hs₀ := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 t.path v w
  have hs : (Q d.radical z).relIndex (Z d.radical w.start) < 4 := by rw [hs₀.2.1]; decide
  have hs' : (Q d.radical w.start).relIndex (Z d.radical z) < 4 := by
    rw [(small_critical_indices s hc w.path hs).2]; decide
  have hns := four_shift_unequal_omega_not_centrally_generated_knownSimple
    (h := h) (e := e) (hz := hz) (hn := hn) hb4 hcard p q r t v hr hv hne w.start w.path.start_color
  obtain ⟨b₀,b₁,hgen⟩ := paired_backward_generation
    (e := e) (hz := hz) (hn := hn) hb4 hcard p' hs' hns (fun b' => (hall b').1)
  have hHv : H ≤ Z d.radical v.start := by
    have hh := ((critical_Z_commutator_le_moving (h := h) b.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical (p'.walk.getVert (p'.walk.length-2)))
    rwa [hpre] at hh
  have hvw : (cosetGraph d.radical).dist v.start w.start = 2 := by
    have hw2 : w.path.walk.getVert 2 = v.start := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using w.overlap 0 (Nat.zero_le _)
    rw [SimpleGraph.dist_comm]
    exact (congrArg (fun y => (cosetGraph d.radical).dist w.start y) hw2).symm.trans
      (w.path.dist_start (by have hh : w.path.walk.length = replacementDistance h d := w.path.length_eq_b; omega : 2 ≤ w.path.walk.length))
  have hvQ : Z d.radical v.start ≤ Q d.radical w.start := by
    apply Z_le_Q_of_dist_lt d.radical v.start ((replacementGeometry h d).exists_critical _ v.path.start_color)
    rw [hvw,(replacementGeometry h d).distance_constant _ v.path.start_color]
    exact hb2
  have hHw : H ≤ centralizer (Z d.radical w.start : Set (FreeAmalgam d.radical)) :=
    (hHv.trans hvQ).trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical w.start w.path.start_color)))
  have hcentral : H ≤ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    rw [←hgen]
    exact sup_le (sup_le (hall b₀).2.1 (hall b₁).2.1) (le_centralizer_iff.mp hHw)
  have hsmall : (Q d.radical (p'.walk.getVert (p'.walk.length-2))).relIndex (Z d.radical b₀.start) < 4 := by
    rw [hpre]
    exact reverse_shift_small (e := e) (hz := hz) (hn := hn) hb hcard p q r t v w hr hv hne p' hrev b₀
  have hnorm := backward_full_omega_normalization_of_not_centrally_generated s hc hb2 p' hs' b₀ hns
  have hZX : Z d.radical w.start ≤ X d.radical w.start := by
    apply (replacementGeometry h d).omega_bound _ w.path.start_color
    rw [(replacementGeometry h d).distance_constant _ w.path.start_color]
    exact replacementDistance_pos h d
  have hnot := (hall b₀).2.2.2
  have hline := (hall b₀).2.2.1
  have hnot' : ¬ Z d.radical b₀.start ⊓ Q d.radical (p'.walk.getVert (p'.walk.length-2)) ≤
      B d.radical z ((replacementGeometry h d).Z_normal _) := by simpa only [hpre] using hnot
  have hbad := backward_line_not_central (h := h) (d := d) (e := e) (hz := hz) (hn := hn)
    hb4 p' b₀ hsmall (hZX.trans hnorm) hnot'
  rw [hpre,hline] at hbad
  exact hbad hcentral

include e hz hn in
/-- The original radical and its literal transporter supply a chain whose
terminal movers agree above distance six and contain both whole adjacent
cores. No radical, central-cover or graph identification is added. -/
theorem original_radical_mover_eq_gt_six_knownSimple
    (hb : 6 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    ∃ q₀ : BackwardShift (h := h) p,
      act d.radical q₀.transporter (beta d.radical) = q₀.edge ∧
      T.map (MulAut.conj q₀.transporter⁻¹).toMonoidHom = Q d.radical q₀.edge ∧
      T.map (MulAut.conj q₀.transporter⁻¹).toMonoidHom ⊔ Z d.radical a' =
        stabilizer d.radical (alpha d.radical) ∧
      ∃ c c', ∃ p₀ : CriticalPath d.radical (replacementGeometry h d) c c',
      SylowTerminalPath.ShiftChain (h := h) q₀.path p₀ (replacementDistance h d) ∧
      ∃ (q : BackwardShift (h := h) p₀) (r : BackwardShift (h := h) q.path)
        (t : BackwardShift (h := h) r.path) (v : BackwardShift (h := h) t.path),
      SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d) ∧
      act d.radical v.transporter (t.path.walk.getVert 1) = v.edge ∧
      let J := SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical v.edge) 4
      let E := SmallMover.join (U d.radical v.start) (Q d.radical v.start) (Q d.radical v.edge) 4
      E = J ∧ Q d.radical t.start ⊔ Q d.radical v.start ≤ E := by
  obtain ⟨q₀,hqe,hqT,hqgen,c,c',p₀,hchain,q,r,t,v,w,hr,hv,_⟩ :=
    original_radical_reverse_omega_knownSimple (e := e) (hz := hz) (hn := hn) hb hcard p hfirst
  have heq := five_shift_mover_eq_gt_six_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p₀ q r t v w hr hv
  have hcore := four_shift_core_product_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 4 < replacementDistance h d) hcard p₀ q r t v hr hv
  exact ⟨q₀,hqe,hqT,hqgen,c,c',p₀,hchain,q,r,t,v,hr,hv,heq,hcore.2.2.trans inf_le_right⟩

include h in
private theorem shift_mover_eq_pullback
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (b : BackwardShift (h := h) p)
    (he : act d.radical b.transporter (p.walk.getVert 1) = b.edge)
    (heq : SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical b.edge) 4 =
      SmallMover.join (U d.radical b.start) (Q d.radical b.start) (Q d.radical b.edge) 4) :
    SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical (p.walk.getVert 1)) 4 =
      SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2))
        (Q d.radical (p.walk.getVert 1)) 4 := by
  apply map_injective (f := (MulAut.conj b.transporter⁻¹).toMonoidHom) (MulAut.conj _).injective
  rw [SmallMover.join_map _ (MulAut.conj _).injective,SmallMover.join_map _ (MulAut.conj _).injective,
    ←U_act,←Q_act,←Q_act,←U_act,←Q_act,
    show act d.radical b.transporter a = a from b.transporter_mem,he,b.start_eq]
  exact heq

private def FirstMoversEqual {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z) : Prop :=
    SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical (p.walk.getVert 1)) 4 =
      SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2))
        (Q d.radical (p.walk.getVert 1)) 4

include h in
private theorem first_movers_pullback
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (b : BackwardShift (h := h) p)
    (he : act d.radical b.transporter (p.walk.getVert 1) = b.edge)
    (hb : FirstMoversEqual (h := h) b.path) : FirstMoversEqual (h := h) p := by
  have htwo : b.path.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using b.overlap 0 (Nat.zero_le _)
  dsimp only [FirstMoversEqual] at hb ⊢
  rw [b.first,htwo] at hb
  exact shift_mover_eq_pullback (h := h) p b he hb.symm

include e hz hn in
private theorem orbit_prefix_with_mover_pullback
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z) (n : ℕ) :
    ∃ c c', ∃ v : CriticalPath d.radical (replacementGeometry h d) c c',
      SylowTerminalPath.OrbitPrefix (h := h) v n ∧
      (FirstMoversEqual (h := h) v → FirstMoversEqual (h := h) p) := by
  induction n with
  | zero => exact ⟨a,z,p,by intro i hi; omega,id⟩
  | succ n ih =>
    obtain ⟨c,c',v,hv,hback⟩ := ih
    obtain ⟨b,he⟩ := SylowShiftChain.backwardShift_with_edge
      (e := e) (hz := hz) (hn := hn) hb hcard v
    exact ⟨_,_,b.path,SylowTerminalPath.orbitPrefix_backwardShift hb v b hv,
      fun hh => hback (first_movers_pullback (h := h) v b he hh)⟩

include e hz hn in
/-- Above distance six the opposite small movers agree at the first two
edges of every literal natural replacement critical path. The orbit
relations and all backward transporters are constructed in the proof. -/
theorem critical_mover_eq_gt_six_knownSimple
    (hb : 6 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z) :
    SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical (p.walk.getVert 1)) 4 =
      SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2))
        (Q d.radical (p.walk.getVert 1)) 4 := by
  have hb4 : 4 < replacementDistance h d := by omega
  obtain ⟨c,c',p₀,hp₀,hback⟩ := orbit_prefix_with_mover_pullback
    (e := e) (hz := hz) (hn := hn) hb4 hcard p (replacementDistance h d)
  obtain ⟨q,hq⟩ := SylowShiftChain.backwardShift_with_edge (e := e) (hz := hz) (hn := hn) hb4 hcard p₀
  obtain ⟨r,hr⟩ := SylowShiftChain.backwardShift_with_edge (e := e) (hz := hz) (hn := hn) hb4 hcard q.path
  obtain ⟨t,ht⟩ := SylowShiftChain.backwardShift_with_edge (e := e) (hz := hz) (hn := hn) hb4 hcard r.path
  obtain ⟨v,hv⟩ := SylowShiftChain.backwardShift_with_edge (e := e) (hz := hz) (hn := hn) hb4 hcard t.path
  obtain ⟨w,_⟩ := SylowShiftChain.backwardShift_with_edge (e := e) (hz := hz) (hn := hn) hb4 hcard v.path
  have hqr := SylowTerminalPath.orbitPrefix_backwardShift hb4 p₀ q hp₀
  have hrr := SylowTerminalPath.orbitPrefix_backwardShift hb4 q.path r hqr
  have hrfull : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d) := by
    intro i hi hlen
    exact hrr i (by omega) hlen
  have he := five_shift_mover_eq_gt_six_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p₀ q r t v w hrfull hv
  have het : FirstMoversEqual (h := h) t.path := shift_mover_eq_pullback (h := h) t.path v hv he.symm
  exact hback (first_movers_pullback (h := h) p₀ q hq
    (first_movers_pullback (h := h) q.path r hr (first_movers_pullback (h := h) r.path t ht het)))

end SylowReverseGeneration
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
