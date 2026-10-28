module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSpanSelection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSpanSelection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeCommonFixer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSmallSeeds

/-!
# Compatible paired small movers in the order-sixteen image branch

For a small critical path, choose one edge and one residual transporter.
The edge core generates the starting stabilizer with either of the two
endpoint seeds. Its actual maximum small mover generates with the two
endpoint seeds together, and also with its own conjugate under the same
transporter. Hence the common fixed subgroup of the full starting seed is
exactly its whole-stabilizer fixed subgroup, with every central attachment
retained.

The finite calculation starts with the existing three-pair selector and
chooses a containing Sylow subgroup that generates with each endpoint
transposition separately. Two small tables express adjacent transpositions
as Sylow elements or conjugates of the selected transposition. The already
proved small-mover image identification lifts these simultaneous equations
through the full quotient kernel, then through the literal graph embedding.
The transporter has cube in the starting core; no order-three lift or split
central cover is assumed.

In the equal-neighbor-mover branch of MS93 (5.6), a prescribed strict slice
transports to the same selected edge. We retain both actual neighbor
candidates, their critical endpoint transporter, the entire transported
walk, and their common small-mover fixed subgroup. The original endpoint
fails to normalize both candidate spans. The final application uses the
literal restriction of the original MS radical and its source small mover.

These are simultaneous generation and fixed-space identities used in
(5.6)--(5.7), not the whole source theorem. Trapped-kernel commutator control
and its required normalizer alignment, the unequal-mover branch of (5.5),
residual transport and the same-commutator alignment of (5.8) remain to be
proved. Both small-critical-index and strict-slice premises are genuine.
Neither distance exclusion, nor the unconditional replacement distance,
is asserted here. Both moved-cover orders sixteen and thirty-two and the
original versus replacement radicals remain distinct.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.5)--(5.8), printed pp.915--920.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowCompatible
local notation "S" => Equiv.Perm (Fin 6)
open CubeCommonFixer

private abbrev w : S := k*r
private abbrev T : Subgroup S := sylowCarrier.map (MulAut.conj w).toMonoidHom

private theorem sylow_one_seed (b : Fin 2) : T ⊔ zpowers (pairSwap 6 b.castSucc) = ⊤ := by
  let v : S := Equiv.swap 0 4 * Equiv.swap 4 3 * Equiv.swap 3 2
  apply chain_generates v
  intro i
  have cert : ∀ b : Fin 2, ∀ i : Fin 5,
      (∃ j : Fin 16, (MulAut.conj v) (Equiv.swap i.castSucc i.succ) =
        (MulAut.conj w) (sylowWords j)) ∨
      (∃ j : Fin 16, (MulAut.conj v) (Equiv.swap i.castSucc i.succ) =
        (MulAut.conj ((MulAut.conj w) (sylowWords j))) (pairSwap 6 b.castSucc)) := by
    decide +kernel
  rcases cert b i with ⟨j,hj⟩ | ⟨j,hj⟩
  · rw [hj]
    exact mem_sup_left (mem_map_of_mem _ ((mem_sylowCarrier_iff _).mpr ⟨j,rfl⟩))
  · rw [hj]
    exact (T ⊔ zpowers (pairSwap 6 b.castSucc)).mul_mem
      ((T ⊔ zpowers (pairSwap 6 b.castSucc)).mul_mem
        (mem_sup_left (mem_map_of_mem _ ((mem_sylowCarrier_iff _).mpr ⟨j,rfl⟩)))
        (mem_sup_right (mem_zpowers _)))
      ((T ⊔ zpowers (pairSwap 6 b.castSucc)).inv_mem
        (mem_sup_left (mem_map_of_mem _ ((mem_sylowCarrier_iff _).mpr ⟨j,rfl⟩))))

private theorem compatible_pair (a : S) (ha : a.IsSwap) :
    ∃ v x : S, x ∈ alternatingGroup (Fin 6) ∧ orderOf x = 3 ∧
      sylowCarrier.map (MulAut.conj v).toMonoidHom ⊔ zpowers a = ⊤ ∧
      sylowCarrier.map (MulAut.conj v).toMonoidHom ⊔
        zpowers ((MulAut.conj x) a) = ⊤ ∧
      (D 6).map (MulAut.conj v).toMonoidHom ⊔ zpowers a ⊔
        zpowers ((MulAut.conj x) a) = ⊤ ∧
      (D 6).map (MulAut.conj v).toMonoidHom ⊔
        ((D 6).map (MulAut.conj v).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = ⊤ := by
  obtain ⟨c,hc⟩ := swap_conjugator a ha
  let x := (MulAut.conj c.val) r
  have hx : x ∈ alternatingGroup (Fin 6) :=
    (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem r (by decide +kernel) c.val
  have ht : (MulAut.conj c.val).toMonoidHom t = a := hc
  have hrt : (MulAut.conj c.val).toMonoidHom ((MulAut.conj r) t) = (MulAut.conj x) a := by
    rw [←ht]
    change c.val*(r*t*r⁻¹)*c.val⁻¹=
      (c.val*r*c.val⁻¹)*(c.val*t*c.val⁻¹)*(c.val*r*c.val⁻¹)⁻¹
    group
  have hw : (D 6).map (MulAut.conj w).toMonoidHom = D' := by
    have hr : (D 6).map (MulAut.conj r).toMonoidHom = D 6 :=
      mem_normalizer_iff_map_conj_eq.mp CubeSmallSeeds.rotation_normalizes
    rw [show w=k*r from rfl,←conjugate_twice,hr]
  have hD : D'.map (MulAut.conj c.val).toMonoidHom =
      (D 6).map (MulAut.conj (c.val*w)).toMonoidHom := by
    rw [←hw,conjugate_twice]
  have hT : T.map (MulAut.conj c.val).toMonoidHom =
      sylowCarrier.map (MulAut.conj (c.val*w)).toMonoidHom := conjugate_twice _ _ _
  have hDx : (D'.map (MulAut.conj r).toMonoidHom).map (MulAut.conj c.val).toMonoidHom =
      (D'.map (MulAut.conj c.val).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    rw [conjugate_twice D' r c.val,conjugate_twice D' c.val x]
    have he : c.val*r=x*c.val := by change c.val*r=(c.val*r*c.val⁻¹)*c.val; group
    rw [he]
  refine ⟨c.val*w,x,hx,((MulAut.conj c.val).orderOf_eq r).trans
    (orderOf_eq_prime (by decide +kernel) (by decide +kernel)),?_,?_,?_,?_⟩
  · have hh := congrArg (Subgroup.map (MulAut.conj c.val).toMonoidHom) (sylow_one_seed 0)
    change (T ⊔ zpowers t).map (MulAut.conj c.val).toMonoidHom = _ at hh
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,ht,hT,
      map_top_of_surjective (MulAut.conj c.val).toMonoidHom (MulAut.conj c.val).surjective] using hh
  · have hbase : T ⊔ zpowers ((MulAut.conj r) t) = ⊤ := by
      have he : (MulAut.conj r) t = pairSwap 6 (1 : Fin 2).castSucc := by decide +kernel
      rw [he]
      exact sylow_one_seed 1
    have hh := congrArg (Subgroup.map (MulAut.conj c.val).toMonoidHom) hbase
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,hrt,hT,
      map_top_of_surjective (MulAut.conj c.val).toMonoidHom (MulAut.conj c.val).surjective] using hh
  · have hh := congrArg (Subgroup.map (MulAut.conj c.val).toMonoidHom) pair_generates
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,ht,hrt,hD,
      map_top_of_surjective (MulAut.conj c.val).toMonoidHom (MulAut.conj c.val).surjective] using hh
  · apply inverse_pair
    have hh := congrArg (Subgroup.map (MulAut.conj c.val).toMonoidHom) kernels_generate
    simpa only [Subgroup.map_sup,hDx,hD,
      map_top_of_surjective (MulAut.conj c.val).toMonoidHom (MulAut.conj c.val).surjective] using hh

private theorem image_conjugate {H K : Type*} [Group H] [Group K]
    (f : H →* K) (A : Subgroup H) (g : H) :
    (A.map (MulAut.conj g).toMonoidHom).map f =
      (A.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]

private theorem compatible_lifts {H : Type*} [Group H]
    (π : H →* S) (hs : Function.Surjective π) (R J C A : Subgroup H)
    (hC : C.map π = alternatingGroup (Fin 6))
    (hkR : π.ker ≤ R) (hkJ : π.ker ≤ J) (u : S)
    (hRimage : R.map π = sylowCarrier.map (MulAut.conj u).toMonoidHom)
    (hJimage : J.map π = (D 6).map (MulAut.conj u).toMonoidHom)
    (a : S) (ha : a ∈ A.map π) (hswap : a.IsSwap) :
    ∃ g y : H, y ∈ C ∧ y^3 ∈ π.ker ∧
      let R₁ := R.map (MulAut.conj g).toMonoidHom
      let J₁ := J.map (MulAut.conj g).toMonoidHom
      let A₁ := A.map (MulAut.conj y).toMonoidHom
      R₁ ⊔ A = ⊤ ∧ R₁ ⊔ A₁ = ⊤ ∧ J₁ ⊔ A ⊔ A₁ = ⊤ ∧
        J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom = ⊤ := by
  obtain ⟨v,b,hbeven,hbo,hgen₀,hgen₁,hgen,hpair⟩ := compatible_pair a hswap
  obtain ⟨g,hg⟩ := hs (v*u⁻¹)
  have hbL : b ∈ C.map π := hC.symm ▸ hbeven
  obtain ⟨y,hy,hyb⟩ := hbL
  let R₁ := R.map (MulAut.conj g).toMonoidHom
  let J₁ := J.map (MulAut.conj g).toMonoidHom
  let A₁ := A.map (MulAut.conj y).toMonoidHom
  have hm (B : Subgroup S) : (B.map (MulAut.conj u).toMonoidHom).map
      (MulAut.conj (v*u⁻¹)).toMonoidHom = B.map (MulAut.conj v).toMonoidHom := by
    rw [conjugate_twice,inv_mul_cancel_right]
  have hR : R₁.map π = sylowCarrier.map (MulAut.conj v).toMonoidHom := by
    rw [image_conjugate,hg,hRimage,hm]
  have hJ : J₁.map π = (D 6).map (MulAut.conj v).toMonoidHom := by
    rw [image_conjugate,hg,hJimage,hm]
  have hker : π.ker.map (MulAut.conj g).toMonoidHom = π.ker :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hkR₁ : π.ker ≤ R₁ := by rw [←hker]; exact map_mono hkR
  have hkJ₁ : π.ker ≤ J₁ := by rw [←hker]; exact map_mono hkJ
  have hA₁ : A₁.map π = (A.map π).map (MulAut.conj b).toMonoidHom := by
    rw [image_conjugate,hyb]
  have lift (B C : Subgroup H) (hkB : π.ker ≤ B)
      (he : B.map π ⊔ C.map π = ⊤) : B ⊔ C = ⊤ := by
    apply map_injective_of_ker_le π (hkB.trans le_sup_left) le_top
    rwa [Subgroup.map_sup,map_top_of_surjective π hs]
  have htop₀ : R₁ ⊔ A = ⊤ := lift R₁ A hkR₁ (by
    rw [hR]
    apply top_unique
    rw [←hgen₀]
    exact sup_le_sup_left (zpowers_le.mpr ha) _)
  have htop₁ : R₁ ⊔ A₁ = ⊤ := lift R₁ A₁ hkR₁ (by
    rw [hR,hA₁]
    apply top_unique
    rw [←hgen₁]
    exact sup_le_sup_left (zpowers_le.mpr (mem_map_of_mem (MulAut.conj b).toMonoidHom ha)) _)
  have htop : J₁ ⊔ A ⊔ A₁ = ⊤ := lift (J₁ ⊔ A) A₁ (hkJ₁.trans le_sup_left) (by
    rw [Subgroup.map_sup,hJ,hA₁]
    apply top_unique
    rw [←hgen]
    exact sup_le_sup (sup_le_sup_left (zpowers_le.mpr ha) _)
      (zpowers_le.mpr (mem_map_of_mem (MulAut.conj b).toMonoidHom ha)))
  have hJpair : J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom = ⊤ :=
    lift J₁ _ hkJ₁ (by rw [image_conjugate π J₁ y⁻¹,map_inv,hyb,hJ]; exact hpair)
  refine ⟨g,y,hy,?_,htop₀,htop₁,htop,hJpair⟩
  rw [MonoidHom.mem_ker,map_pow,hyb]
  simpa only [hbo] using pow_orderOf_eq_one b

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- Simultaneous small-mover generation and common fixed space on the actual
order-sixteen replacement. Both full edge generation equations use the same
edge and endpoint transporter as the small-mover equations. -/
theorem sixteen_paired_small_mover_neighbor_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ x ∈ Ltilde d.radical (alpha d.radical),
        x^3 ∈ Q d.radical (alpha d.radical) ∧
        let J := SmallMover.join (U d.radical (alpha d.radical))
          (Q d.radical (alpha d.radical)) (Q d.radical t) 4
        Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
        Q d.radical t ⊔ Z d.radical (act d.radical x a') = stabilizer d.radical (alpha d.radical) ∧
        J ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') = stabilizer d.radical (alpha d.radical) ∧
        J ⊔ J.map (MulAut.conj x).toMonoidHom = stabilizer d.radical (alpha d.radical) ∧
        (Z d.radical (alpha d.radical) ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
          centralizer (J.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) =
          Z d.radical (alpha d.radical) ⊓
            centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨a,ha,hswap⟩ := small_critical_image_swap s hc p hsmall
  obtain ⟨u,hN,_,hj,himage,_⟩ := SylowSmallMovers.normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  have hnormal := SylowLarge.sixteen_radical_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard
  let J₀ := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  have hJimage : J₀.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [hnormal] at hj himage
    rw [show J₀ = _ from hj]
    exact himage
  have hRimage : d.radical.map s.projection = sylowCarrier.map (MulAut.conj u).toMonoidHom := by
    rwa [hnormal] at hN
  have hkJ : s.projection.ker ≤ J₀ := by
    rw [s.projection_kernel]
    let := replacementMoved_normal h d
    exact SmallMover.kernel_le_join _ _ _ 4 (by decide) (replacement_core_le_radical h d)
      (by rw [←moved_centralizer s]; exact le_centralizer_iff.mpr le_rfl)
  let A := (Z d.radical a').comap (embedM d.radical)
  obtain ⟨g,y,hy,hy3,htop₀,htop₁,htop,hJpair⟩ := compatible_lifts s.projection s.surjective
    d.radical J₀ (replacementComponent d) A s.component_image
    (s.projection_kernel.symm ▸ replacement_core_le_radical h d) hkJ u hRimage hJimage a ha hswap
  let R₁ := d.radical.map (MulAut.conj g).toMonoidHom
  let J₁ := J₀.map (MulAut.conj g).toMonoidHom
  let A₁ := A.map (MulAut.conj y).toMonoidHom
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hU : (replacementMoved d).map (MulAut.conj g).toMonoidHom = replacementMoved d := by
    let := replacementMoved_normal h d
    exact mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  let f := (embedM d.radical g)⁻¹
  let x := (embedM d.radical y)⁻¹
  let t := act d.radical f (beta d.radical)
  let J := SmallMover.join (U d.radical (alpha d.radical))
    (Q d.radical (alpha d.radical)) (Q d.radical t) 4
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    change f ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have ht : Q d.radical t = R₁.map (embedM d.radical) := by
    rw [Q_act,Q_beta,image_conjugate]
    simp only [f,inv_inv]
  have hJm : J₁.map (embedM d.radical) = J := by
    change ((SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4).map
      (MulAut.conj g).toMonoidHom).map (embedM d.radical) = J
    rw [SmallMover.join_map _ (MulAut.conj g).injective,
      hU,hQ,SmallMover.join_map _ (embedM_injective d.radical),←hc.U_eq_moved,
      ←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d),←ht]
  have hxL : x ∈ Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d]
    exact mem_map_of_mem _ ((replacementComponent d).inv_mem hy)
  have hAm : A.map (embedM d.radical) = Z d.radical a' :=
    map_comap_eq_self ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
        (stabilizer_m_base d.radical))
  have hA₁m : A₁.map (embedM d.radical) = Z d.radical (act d.radical x a') := by
    rw [image_conjugate,hAm,Z_act]
    simp only [x,inv_inv]
  have hrange : (embedM d.radical).range = stabilizer d.radical (alpha d.radical) :=
    (stabilizer_m_base d.radical).symm
  have hpair' : J ⊔ J.map (MulAut.conj x).toMonoidHom = stabilizer d.radical (alpha d.radical) := by
    have hh := congrArg (Subgroup.map (embedM d.radical)) hJpair
    rwa [Subgroup.map_sup,image_conjugate (embedM d.radical) J₁ y⁻¹,map_inv,hJm,←MonoidHom.range_eq_map,
      hrange] at hh
  refine ⟨t,?_,x,hxL,?_,?_,?_,?_,hpair',?_⟩
  · have hfix : act d.radical f (alpha d.radical)=alpha d.radical := hf
    rw [←hfix]
    exact (adjacent_act_iff d.radical f _ _).mpr (base_adjacent d.radical)
  · rw [s.projection_kernel] at hy3
    rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    have hx3 : x^3=embedM d.radical ((y^3)⁻¹) := by simp only [x,inv_pow,map_inv,map_pow]
    rw [hx3]
    exact mem_map_of_mem _ ((pCore 2 d.overgroup).inv_mem hy3)
  · have hh := congrArg (Subgroup.map (embedM d.radical)) htop₀
    rwa [Subgroup.map_sup,←ht,hAm,←MonoidHom.range_eq_map,hrange] at hh
  · have hh := congrArg (Subgroup.map (embedM d.radical)) htop₁
    rwa [Subgroup.map_sup,←ht,hA₁m,←MonoidHom.range_eq_map,hrange] at hh
  · have hh := congrArg (Subgroup.map (embedM d.radical)) htop
    rwa [Subgroup.map_sup,Subgroup.map_sup,hJm,hAm,hA₁m,←MonoidHom.range_eq_map,
      hrange] at hh
  · ext z
    constructor
    · rintro ⟨⟨hz,hzJ⟩,hzJx⟩
      refine ⟨hz,?_⟩
      have hfix : J ⊔ J.map (MulAut.conj x).toMonoidHom ≤ centralizer ({z} : Set _) :=
        sup_le (fun j hj => mem_centralizer_singleton_iff.mpr (hzJ j hj))
          (fun j hj => mem_centralizer_singleton_iff.mpr (hzJx j hj))
      rw [hpair'] at hfix
      exact fun j hj => mem_centralizer_singleton_iff.mp (hfix hj)
    · rintro ⟨hz,hzG⟩
      exact ⟨⟨hz,fun j hj => hzG j (hpair' ▸ mem_sup_left hj)⟩,
        fun j hj => hzG j (hpair' ▸ mem_sup_right hj)⟩

include e hz hn in
private theorem generating_endpoint_does_not_normalize
    (hb : 4 < replacementDistance h d)
    {a z c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical z = stabilizer d.radical a)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    ¬ Z d.radical z ≤ normalizer ((Z d.radical c ⊔ Z d.radical a :
      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  intro hnorm
  let Y := Z d.radical c ⊔ Z d.radical a
  have hYN : stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    refine sup_le ?_ hnorm
    apply le_trans (le_inf _ _) (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact (show Q d.radical t ≤ stabilizer d.radical c from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c)
    · exact (show Q d.radical t ≤ stabilizer d.radical a from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hat)).trans (Z_normalized d.radical a)
  have hdist : (cosetGraph d.radical).dist c a ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t a = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle (u := c) (v := t) (w := a)
  have hYV : Y ≤ V d.radical a :=
    sup_le ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist))
      (Z_le_VBall d.radical _ 2)
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hUB : U d.radical c ≤ B d.radical a ((replacementGeometry h d).Z_normal _) :=
    (DistanceEight.U_le_Z d.radical c).trans (le_sup_left.trans
      (SylowSpanSelection.normal_small_radius_le_slice_at s (by omega) ha Y hYV hYN
        (SylowSpanSelection.adjacent_seed_span_index_le_eight
          (e := e) (hz := hz) (hn := hn) hb ha hat hct)))
  have hi := relIndex_eq_one.mpr hUB
  omega

include e hz hn in
/-- In the equal-mover source branch, a prescribed strict slice supplies
one compatible pair. Its actual neighboring mover gives both generation
and the common fixed subgroup. Both endpoints fail to normalize the same
selected seed span; the endpoint transporter retains the whole critical walk. -/
theorem sixteen_equal_mover_strict_pair_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hequal : SmallMover.join (U d.radical delta) (Q d.radical delta)
        (Q d.radical (p.walk.getVert 1)) 4 =
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical (p.walk.getVert 1)) 4)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ x ∈ Ltilde d.radical (alpha d.radical),
          x^3 ∈ Q d.radical (alpha d.radical) ∧
          ∃ q : CriticalPath d.radical (replacementGeometry h d)
              (alpha d.radical) (act d.radical x a'),
            (∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i)) ∧
            (Q d.radical (act d.radical x a')).relIndex (Z d.radical (alpha d.radical)) < 4 ∧
            let c := act d.radical g delta
            let J := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
            J = SmallMover.join (U d.radical (alpha d.radical))
              (Q d.radical (alpha d.radical)) (Q d.radical t) 4 ∧
            Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
            Q d.radical t ⊔ Z d.radical (act d.radical x a') = stabilizer d.radical (alpha d.radical) ∧
            J ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') = stabilizer d.radical (alpha d.radical) ∧
            J ⊔ J.map (MulAut.conj x).toMonoidHom = stabilizer d.radical (alpha d.radical) ∧
            (Z d.radical (alpha d.radical) ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
              centralizer (J.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) =
              Z d.radical (alpha d.radical) ⊓
                centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
            ¬ Z d.radical a' ≤ normalizer ((Z d.radical c ⊔ Z d.radical (alpha d.radical) :
              Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
            ¬ Z d.radical (act d.radical x a') ≤ normalizer
              ((Z d.radical c ⊔ Z d.radical (alpha d.radical) :
                Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
            Adjacent d.radical (alpha d.radical) (act d.radical x⁻¹ t) ∧
            Adjacent d.radical (act d.radical x⁻¹ c) (act d.radical x⁻¹ t) ∧
            2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
              (U d.radical (act d.radical x⁻¹ c)) ∧
            J.map (MulAut.conj x).toMonoidHom =
              SmallMover.join (U d.radical (act d.radical x⁻¹ c))
                (Q d.radical (act d.radical x⁻¹ c)) (Q d.radical (act d.radical x⁻¹ t)) 4 ∧
            Q d.radical (act d.radical x⁻¹ t) ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
            ¬ Z d.radical a' ≤ normalizer
              ((Z d.radical (act d.radical x⁻¹ c) ⊔ Z d.radical (alpha d.radical) :
                Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  obtain ⟨t,hat,x,hxL,hx3,hgen₀,hgen₁,hgen,hpair,hfix⟩ :=
    sixteen_paired_small_mover_neighbor_knownSimple (e := e) (hz := hz) (hn := hn) hb hcard p hsmall
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hfirst : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) hfirst hat
  have hct : Adjacent d.radical (act d.radical g delta) t := by
    rw [←hgt]
    exact (adjacent_act_iff d.radical g delta (p.walk.getVert 1)).mpr hdelta
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      (by omega : 2 < replacementDistance h d) (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
  have hstrict' : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical g delta)) := by
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hstrict
  have heq : SmallMover.join (U d.radical (act d.radical g delta))
      (Q d.radical (act d.radical g delta)) (Q d.radical t) 4 =
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical)) (Q d.radical t) 4 := by
    have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hequal
    have hga : act d.radical g (alpha d.radical) = alpha d.radical := hg
    rwa [SmallMover.join_map _ (MulAut.conj g⁻¹).injective,
      SmallMover.join_map _ (MulAut.conj g⁻¹).injective,←U_act,←Q_act,←Q_act,←U_act,←Q_act,hga,hgt] at hh
  have hx : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hxL
  have hxa : act d.radical x (alpha d.radical)=alpha d.radical := hx
  have hq : ∃ q : CriticalPath d.radical (replacementGeometry h d)
      (alpha d.radical) (act d.radical x a'),
      ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) := by
    have hh : ∃ q : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical x (alpha d.radical)) (act d.radical x a'),
        ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) :=
      ⟨p.act x,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
    rwa [hxa] at hh
  obtain ⟨q,hq⟩ := hq
  have hqs : (Q d.radical (act d.radical x a')).relIndex (Z d.radical (alpha d.radical)) < 4 := by
    conv_lhs => rhs; rw [←hxa]
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hsmall
  have hxainv : act d.radical x⁻¹ (alpha d.radical) = alpha d.radical :=
    (stabilizer d.radical (alpha d.radical)).inv_mem hx
  have hat₂ : Adjacent d.radical (alpha d.radical) (act d.radical x⁻¹ t) := by
    rw [←hxainv]
    exact (adjacent_act_iff d.radical x⁻¹ _ _).mpr hat
  have hct₂ : Adjacent d.radical (act d.radical x⁻¹ (act d.radical g delta))
      (act d.radical x⁻¹ t) := (adjacent_act_iff d.radical x⁻¹ _ _).mpr hct
  have hBx : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      (by omega : 2 < replacementDistance h d) (alpha d.radical) rfl hx)
  have hstrict₂ : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical x⁻¹ (act d.radical g delta))) := by
    rw [U_act,inv_inv,←hBx,relIndex_map_map_of_injective _ _ (MulAut.conj x).injective]
    exact hstrict'
  have hgen₂ : Q d.radical (act d.radical x⁻¹ t) ⊔ Z d.radical a' =
      stabilizer d.radical (alpha d.radical) := by
    have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hgen₁
    have hQt : (Q d.radical t).map (MulAut.conj x).toMonoidHom = Q d.radical (act d.radical x⁻¹ t) := by
      rw [Q_act,inv_inv]
    have hZa : (Z d.radical (act d.radical x a')).map (MulAut.conj x).toMonoidHom = Z d.radical a' := by
      have hh := Z_act d.radical x⁻¹ (act d.radical x a')
      rw [inv_inv,←act_mul,mul_inv_cancel,act_one] at hh
      exact hh.symm
    have hG : (stabilizer d.radical (alpha d.radical)).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical (alpha d.radical) :=
      mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical (alpha d.radical)).le_normalizer hx)
    rwa [Subgroup.map_sup,hQt,hZa,hG] at hh
  refine ⟨t,hat,g,hg,hgt,hct,hstrict',x,hxL,hx3,q,hq,hqs,heq,hgen₀,hgen₁,
    ?_,?_,?_,?_,?_,hat₂,hct₂,hstrict₂,?_,hgen₂,?_⟩
  · rwa [heq]
  · rwa [heq]
  · rwa [heq]
  · exact generating_endpoint_does_not_normalize (e := e) (hz := hz) (hn := hn)
      hb rfl hat hct hgen₀ hstrict'
  · exact generating_endpoint_does_not_normalize (e := e) (hz := hz) (hn := hn)
      hb rfl hat hct hgen₁ hstrict'
  · rw [SmallMover.join_map _ (MulAut.conj x).injective,
      U_act d.radical x⁻¹ (act d.radical g delta),Q_act d.radical x⁻¹ (act d.radical g delta),
      Q_act d.radical x⁻¹ t,inv_inv]
  · exact generating_endpoint_does_not_normalize (e := e) (hz := hz) (hn := hn)
      hb rfl hat₂ hct₂ hgen₂ hstrict₂

include e hz hn in
/-- The simultaneous generators use the literal restriction of the original
MS radical. Its source small mover is transported through the same replacement
embedding and conjugator as the full radical, retaining both covers. -/
theorem original_radical_paired_small_mover_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let J := SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical)) T 4
    ∃ g ∈ stabilizer d.radical (alpha d.radical),
      ∃ x ∈ Ltilde d.radical (alpha d.radical),
        x^3 ∈ Q d.radical (alpha d.radical) ∧
        let T₁ := T.map (MulAut.conj g⁻¹).toMonoidHom
        let J₁ := J.map (MulAut.conj g⁻¹).toMonoidHom
        T₁ ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
        T₁ ⊔ Z d.radical (act d.radical x a') = stabilizer d.radical (alpha d.radical) ∧
        J₁ ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') = stabilizer d.radical (alpha d.radical) ∧
        J₁ ⊔ J₁.map (MulAut.conj x).toMonoidHom = stabilizer d.radical (alpha d.radical) ∧
        (Z d.radical (alpha d.radical) ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical))) ⊓
          centralizer (J₁.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) =
          Z d.radical (alpha d.radical) ⊓
            centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  obtain ⟨t,hat,x,hx,hx3,hgen₀,hgen₁,hgen,hpair,hfix⟩ :=
    sixteen_paired_small_mover_neighbor_knownSimple (e := e) (hz := hz) (hn := hn) hb hcard p hsmall
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical)
    (base_adjacent d.radical) hat
  change act d.radical g (beta d.radical) = t at hgt
  have hrestriction := (SylowLarge.sixteen_original_restriction_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard).2.1
  have hT : ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) =
      Q d.radical (beta d.radical) := by
    rw [Q_beta]
    exact congrArg (Subgroup.map (embedM d.radical)) hrestriction.symm
  have hga : act d.radical g (alpha d.radical) = alpha d.radical := hg
  dsimp only
  refine ⟨g,hg,x,hx,hx3,?_,?_,?_,?_,?_⟩
  · rwa [hT,←Q_act,hgt]
  · rwa [hT,←Q_act,hgt]
  · rwa [SmallMover.join_map _ (MulAut.conj g⁻¹).injective,hT,←U_act,←Q_act,←Q_act,hga,hgt]
  · rwa [SmallMover.join_map _ (MulAut.conj g⁻¹).injective,hT,←U_act,←Q_act,←Q_act,hga,hgt]
  · rwa [SmallMover.join_map _ (MulAut.conj g⁻¹).injective,hT,←U_act,←Q_act,←Q_act,hga,hgt]

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowCompatible
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
