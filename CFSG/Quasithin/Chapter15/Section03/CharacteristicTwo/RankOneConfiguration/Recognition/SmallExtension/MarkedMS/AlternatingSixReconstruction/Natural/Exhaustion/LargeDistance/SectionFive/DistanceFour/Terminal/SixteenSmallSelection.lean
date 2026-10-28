module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenEqual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowCompatible
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenEqual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenUnequal

/-!
# Compatible image-sixteen selection retaining the original mover

For a small critical endpoint the image transposition belongs to the original
Sylow cube. Rotating the three pairs before applying the compatible selection
makes its order-three transporter normalize this original cube. The original
cube and the selected cube generate the full symmetric group: their matching
edges contain a connected path on all six letters.

The quotient lift retains both Sylow generation identities and both paired
cube identities. On the actual graph it also retains normalization of the
original edge mover and generation by the original and selected movers. These
are the compatibility data in MS93 (5.6)(b,d), printed pp.917--918, needed for
the strict full-seed intersection in (5.12). No central attachment is removed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenSmall
local notation "S" => Equiv.Perm (Fin 6)
open CubeCommonFixer SylowCompatible
private theorem original_selected_cubes_generate : D 6 ⊔ D' = ⊤ := by
  let v : S := Equiv.swap 2 5 * Equiv.swap 2 3 * Equiv.swap 2 4
  apply chain_generates v
  intro i
  have cert : ∀ i : Fin 5, ∃ j : Fin 3,
      (MulAut.conj v) (Equiv.swap i.castSucc i.succ) = pairSwap 6 j ∨
      (MulAut.conj v) (Equiv.swap i.castSucc i.succ) = (MulAut.conj k) (pairSwap 6 j) := by
    decide +kernel
  obtain ⟨j,hj | hj⟩ := cert i
  · rw [hj]
    exact mem_sup_left (pairSwap_mem (n := 6) (m := 3) j (by omega))
  · rw [hj]
    exact mem_sup_right (mem_map_of_mem _ (pairSwap_mem (n := 6) (m := 3) j (by omega)))

private theorem compatible_pair_preserves_original_cube (u : S) (a : S) (ha : a.IsSwap)
    (haD : a ∈ (D 6).map (MulAut.conj u).toMonoidHom) :
    ∃ v x : S, x ∈ alternatingGroup (Fin 6) ∧ orderOf x = 3 ∧
      x ∈ normalizer ((D 6).map (MulAut.conj u).toMonoidHom : Set S) ∧
      (D 6).map (MulAut.conj u).toMonoidHom ⊔ (D 6).map (MulAut.conj v).toMonoidHom = ⊤ ∧
      sylowCarrier.map (MulAut.conj v).toMonoidHom ⊔ zpowers a = ⊤ ∧
      sylowCarrier.map (MulAut.conj v).toMonoidHom ⊔
        zpowers ((MulAut.conj x) a) = ⊤ ∧
      (D 6).map (MulAut.conj v).toMonoidHom ⊔ zpowers a ⊔
        zpowers ((MulAut.conj x) a) = ⊤ ∧
      (D 6).map (MulAut.conj v).toMonoidHom ⊔
        ((D 6).map (MulAut.conj v).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = ⊤ := by
  obtain ⟨a₀,ha₀,hae⟩ := haD
  obtain ⟨j,hj⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) _).mp ha₀
  change dWords j = a₀ at hj
  have hs : (dWords j).IsSwap := by
    apply Equiv.Perm.isSwap_iff_cycleType.mpr
    have hh := Equiv.Perm.isSwap_iff_cycleType.mp ha
    rw [←hae] at hh
    change (u*a₀*u⁻¹).cycleType = {2} at hh
    rw [Equiv.Perm.cycleType_conj] at hh
    exact hj.symm ▸ hh
  have cert : ∀ j : Fin 8, (dWords j).cycleType = {2} →
      ∃ i : Fin 3, (MulAut.conj (r ^ i.val)) t = dWords j := by decide +kernel
  obtain ⟨i,hi⟩ := cert j (Equiv.Perm.isSwap_iff_cycleType.mp hs)
  let c : S := u * r ^ i.val
  have hc : c * t * c⁻¹ = a := by
    change (MulAut.conj (u * r ^ i.val)) t = a
    change (MulAut.conj u) ((MulAut.conj (r ^ i.val)) t) = a
    change dWords j = a₀ at hj
    rw [hi,hj]
    exact hae
  have hcD : (D 6).map (MulAut.conj c).toMonoidHom =
      (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [show c=u*r^i.val from rfl,←conjugate_twice]
    congr 1
    apply mem_normalizer_iff_map_conj_eq.mp
    exact (normalizer (D 6 : Set S)).pow_mem CubeSmallSeeds.rotation_normalizes i.val
  let x := (MulAut.conj c) r
  have hx : x ∈ alternatingGroup (Fin 6) :=
    (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem r (by decide +kernel) c
  have ht : (MulAut.conj c).toMonoidHom t = a := hc
  have hrt : (MulAut.conj c).toMonoidHom ((MulAut.conj r) t) = (MulAut.conj x) a := by
    rw [←ht]
    change c*(r*t*r⁻¹)*c⁻¹=
      (c*r*c⁻¹)*(c*t*c⁻¹)*(c*r*c⁻¹)⁻¹
    group
  have hw : (D 6).map (MulAut.conj w).toMonoidHom = D' := by
    have hr : (D 6).map (MulAut.conj r).toMonoidHom = D 6 :=
      mem_normalizer_iff_map_conj_eq.mp CubeSmallSeeds.rotation_normalizes
    rw [show w=k*r from rfl,←conjugate_twice,hr]
  have hD : D'.map (MulAut.conj c).toMonoidHom =
      (D 6).map (MulAut.conj (c*w)).toMonoidHom := by
    rw [←hw,conjugate_twice]
  have hT : T.map (MulAut.conj c).toMonoidHom =
      sylowCarrier.map (MulAut.conj (c*w)).toMonoidHom := conjugate_twice _ _ _
  have hDx : (D'.map (MulAut.conj r).toMonoidHom).map (MulAut.conj c).toMonoidHom =
      (D'.map (MulAut.conj c).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    rw [conjugate_twice D' r c,conjugate_twice D' c x]
    have he : c*r=x*c := by change c*r=(c*r*c⁻¹)*c; group
    rw [he]
  refine ⟨c*w,x,hx,((MulAut.conj c).orderOf_eq r).trans
    (orderOf_eq_prime (by decide +kernel) (by decide +kernel)),?_,?_,?_,?_,?_,?_⟩
  · rw [←hcD]
    exact le_normalizer_map (MulAut.conj c).toMonoidHom
      (mem_map_of_mem _ CubeSmallSeeds.rotation_normalizes)
  · have hh := congrArg (Subgroup.map (MulAut.conj c).toMonoidHom) original_selected_cubes_generate
    simpa only [Subgroup.map_sup,hcD,hD,
      map_top_of_surjective (MulAut.conj c).toMonoidHom (MulAut.conj c).surjective] using hh
  · have hh := congrArg (Subgroup.map (MulAut.conj c).toMonoidHom) (sylow_one_seed 0)
    change (T ⊔ zpowers t).map (MulAut.conj c).toMonoidHom = _ at hh
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,ht,hT,
      map_top_of_surjective (MulAut.conj c).toMonoidHom (MulAut.conj c).surjective] using hh
  · have hbase : T ⊔ zpowers ((MulAut.conj r) t) = ⊤ := by
      have he : (MulAut.conj r) t = pairSwap 6 (1 : Fin 2).castSucc := by decide +kernel
      rw [he]
      exact sylow_one_seed 1
    have hh := congrArg (Subgroup.map (MulAut.conj c).toMonoidHom) hbase
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,hrt,hT,
      map_top_of_surjective (MulAut.conj c).toMonoidHom (MulAut.conj c).surjective] using hh
  · have hh := congrArg (Subgroup.map (MulAut.conj c).toMonoidHom) pair_generates
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,ht,hrt,hD,
      map_top_of_surjective (MulAut.conj c).toMonoidHom (MulAut.conj c).surjective] using hh
  · apply inverse_pair
    have hh := congrArg (Subgroup.map (MulAut.conj c).toMonoidHom) kernels_generate
    simpa only [Subgroup.map_sup,hDx,hD,
      map_top_of_surjective (MulAut.conj c).toMonoidHom (MulAut.conj c).surjective] using hh


private theorem compatible_lifts_original {H : Type*} [Group H]
    (π : H →* S) (hs : Function.Surjective π) (R J C A : Subgroup H)
    (hC : C.map π = alternatingGroup (Fin 6))
    (hkR : π.ker ≤ R) (hkJ : π.ker ≤ J) (u : S)
    (hRimage : R.map π = sylowCarrier.map (MulAut.conj u).toMonoidHom)
    (hJimage : J.map π = (D 6).map (MulAut.conj u).toMonoidHom)
    (a : S) (ha : a ∈ A.map π) (hswap : a.IsSwap) (haJ : a ∈ J.map π) :
    ∃ g y : H, y ∈ C ∧ y^3 ∈ π.ker ∧ y ∈ normalizer (J : Set H) ∧
      let R₁ := R.map (MulAut.conj g).toMonoidHom
      let J₁ := J.map (MulAut.conj g).toMonoidHom
      let A₁ := A.map (MulAut.conj y).toMonoidHom
      J ⊔ J₁ = ⊤ ∧ R₁ ⊔ A = ⊤ ∧ R₁ ⊔ A₁ = ⊤ ∧ J₁ ⊔ A ⊔ A₁ = ⊤ ∧
        J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom = ⊤ := by
  obtain ⟨v,b,hbeven,hbo,hbN,hcross,hgen₀,hgen₁,hgen,hpair⟩ :=
    compatible_pair_preserves_original_cube u a hswap (hJimage ▸ haJ)
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
  have hJJ : J ⊔ J₁ = ⊤ := lift J J₁ hkJ (by rw [hJimage,hJ]; exact hcross)
  have hyN : y ∈ normalizer (J : Set H) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hkerY : π.ker.map (MulAut.conj y).toMonoidHom = π.ker :=
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top y)
    have hkY : π.ker ≤ J.map (MulAut.conj y).toMonoidHom := by
      rw [←hkerY]
      exact map_mono hkJ
    apply map_injective_of_ker_le π hkY hkJ
    rw [image_conjugate,hyb,hJimage]
    exact mem_normalizer_iff_map_conj_eq.mp hbN
  refine ⟨g,y,hy,?_,hyN,hJJ,htop₀,htop₁,htop,hJpair⟩
  rw [MonoidHom.mem_ker,map_pow,hyb]
  simpa only [hbo] using pow_orderOf_eq_one b


open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
include e hz hn in
theorem sixteen_paired_original_cube_neighbor_knownSimple
    (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ x ∈ Ltilde d.radical (alpha d.radical),
        x^3 ∈ Q d.radical (alpha d.radical) ∧
        x ∈ normalizer ((SmallMover.join (U d.radical (alpha d.radical))
          (Q d.radical (alpha d.radical)) (Q d.radical (p.walk.getVert 1)) 4 :
            Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        let J := SmallMover.join (U d.radical (alpha d.radical))
          (Q d.radical (alpha d.radical)) (Q d.radical t) 4
        SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
            (Q d.radical (p.walk.getVert 1)) 4 ⊔ J = stabilizer d.radical (alpha d.radical) ∧
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
  obtain ⟨u,hN,_,hj,himage,_⟩ := Nonelementary.normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) (SixteenUnequal.sixteen_nonelementary hcard) (by omega : 2 < replacementDistance h d)
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
  have hZrad : Z d.radical a' ≤ Q d.radical (beta d.radical) := by
    rw [←hfirst]
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end]
    have hl : p.walk.length = 4 := p.length_eq_b.trans hb
    change p.walk.length-1 < replacementDistance h d
    rw [hl,hb]
    decide
  have hAR : A ≤ d.radical := by
    have hh := comap_mono (f := embedM d.radical) hZrad
    rw [Q_beta,comap_map_eq_self_of_injective (embedM_injective _)] at hh
    exact hh
  have haR : a ∈ sylowCarrier.map (MulAut.conj u).toMonoidHom := hRimage ▸ (map_mono hAR ha)
  obtain ⟨a₀,ha₀,hae⟩ := haR
  obtain ⟨j,hj⟩ := (mem_sylowCarrier_iff _).mp ha₀
  have hs : (sylowWords j).cycleType = {2} := by
    have hh := Equiv.Perm.isSwap_iff_cycleType.mp hswap
    rw [←hae] at hh
    change (u*a₀*u⁻¹).cycleType = {2} at hh
    rw [Equiv.Perm.cycleType_conj] at hh
    exact hj.symm ▸ hh
  have haD : a₀ ∈ D 6 := by
    rw [←hj]
    have cert : ∀ j : Fin 16, (sylowWords j).cycleType = {2} →
        ∃ k : Fin 8, sylowWords j = dWords k := by decide +kernel
    obtain ⟨k,hk⟩ := cert j hs
    rw [hk]
    exact (mem_disjointTranspositions_iff (3 : Fin 4) _).mpr ⟨k,rfl⟩
  have haJ : a ∈ J₀.map s.projection := by
    rw [hJimage]
    exact ⟨a₀,haD,hae⟩
  obtain ⟨g,y,hy,hy3,hyN,hJJ,htop₀,htop₁,htop,hJpair⟩ := compatible_lifts_original s.projection s.surjective
    d.radical J₀ (replacementComponent d) A s.component_image
    (s.projection_kernel.symm ▸ replacement_core_le_radical h d) hkJ u hRimage hJimage a ha hswap haJ
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
  refine ⟨t,?_,x,hxL,?_,?_,?_,?_,?_,?_,hpair',?_⟩
  · have hfix : act d.radical f (alpha d.radical)=alpha d.radical := hf
    rw [←hfix]
    exact (adjacent_act_iff d.radical f _ _).mpr (base_adjacent d.radical)
  · rw [s.projection_kernel] at hy3
    rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    have hx3 : x^3=embedM d.radical ((y^3)⁻¹) := by simp only [x,inv_pow,map_inv,map_pow]
    rw [hx3]
    exact mem_map_of_mem _ ((pCore 2 d.overgroup).inv_mem hy3)
  · have hJN := (le_normalizer_map (embedM d.radical))
      (mem_map_of_mem (embedM d.radical) ((normalizer (J₀ : Set d.overgroup)).inv_mem hyN))
    have hbase : J₀.map (embedM d.radical) = SmallMover.join
        (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical (p.walk.getVert 1)) 4 := by
      dsimp only [J₀]
      rw [SmallMover.join_map _ (embedM_injective d.radical),←hc.U_eq_moved,
        ←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d),
        hfirst,Q_beta]
    rw [hbase] at hJN
    simpa only [map_inv] using hJN
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hJJ
    have hbase : J₀.map (embedM d.radical) = SmallMover.join
        (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical (p.walk.getVert 1)) 4 := by
      dsimp only [J₀]
      rw [SmallMover.join_map _ (embedM_injective d.radical),←hc.U_eq_moved,
        ←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d),
        hfirst,Q_beta]
    rwa [Subgroup.map_sup,hbase,hJm,←MonoidHom.range_eq_map,hrange] at hh
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

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenSmall
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
