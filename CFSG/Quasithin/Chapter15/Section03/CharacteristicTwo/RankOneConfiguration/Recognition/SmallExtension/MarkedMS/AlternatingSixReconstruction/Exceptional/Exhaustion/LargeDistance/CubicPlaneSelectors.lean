module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBorelThompson
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBorelThompson
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreEvenGeneration
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixCorePlane
import all Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreEvenGeneration

/-!
# Paired plane selectors on the original cubic graph

For a prescribed transposition, an even six-letter selector produces two
plane radicals generating S₆, while one plane and the transposition with
its selected conjugate also generate S₆. The certificate uses two connected
chains of transpositions. If the prescribed transposition belongs to the
original plane, the selector normalizes that plane.

The unique source maximum-order small mover is transported through the
literal edge charts in both remaining radical branches. The generation
identities lift across the cubic kernel using the existing no-supplement
theorem and the full two-core, without identifying that kernel with Q.
For every small critical path, this constructs two actual Thompson joins
and the same component selector, proves their full local generation, and
identifies their common fixed subgroup in the full seed with the central
attachment. Both cover orders sixteen and thirty-two are retained.

The whole-core and C.1.32 applications discharge the selector-existence
premise for these identities. The later compatible backward paths,
large-image selectors, R4/R6 comparisons and terminal contradictions remain
necessary, as do natural exhaustion and final reconstruction. Only the
image-normalizer condition is asserted; normalization of an entire lifted
radical is not inferred from it.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.6)(b--d), printed pp.917--918, and the selection used in
(5.12), pp.924--927; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull.PlaneSelection
private def shift : alternatingGroup (Fin 6) :=
  ⟨(Equiv.swap 0 2 * Equiv.swap 2 4) * (Equiv.swap 1 3 * Equiv.swap 3 5), by decide⟩
private def position : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 1 2 * Equiv.swap 3 4, by decide⟩
private def roots (i : Fin 3) : S := ![swap01,swap23,swap45] i
private theorem roots_mem (i : Fin 3) : roots i ∈ D := by
  apply Subgroup.subset_closure
  fin_cases i <;> simp [roots]
private theorem chain_generates (H : Subgroup S) (f : S)
    (hf : ∀ i : Fin 5, Equiv.swap (f i.castSucc) (f i.succ) ∈ H) : H = ⊤ := by
  have hall : (⊤ : Subgroup S) ≤ H.comap (MulAut.conj f).toMonoidHom := by
    rw [←Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 5)]
    apply (closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    change f * Equiv.swap i.castSucc i.succ * f⁻¹ ∈ H
    rw [←Equiv.swap_apply_apply]
    exact hf i
  have he := congrArg (Subgroup.map (MulAut.conj f).toMonoidHom) (top_unique hall)
  rw [map_top_of_surjective (MulAut.conj f).toMonoidHom (MulAut.conj f).surjective,
    map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr (MulAut.conj f).surjective]; exact le_top)] at he
  exact he
private def rootChain : S := Equiv.ofBijective
  (fun i : Fin 6 => (![4,1,0,2,3,5] : Fin 6 → Fin 6) i) (by decide)
private def pairChain : S := Equiv.ofBijective
  (fun i : Fin 6 => (![2,0,3,5,1,4] : Fin 6 → Fin 6) i) (by decide)
private theorem standard_generators :
    let P := D.map (MulAut.conj position.val).toMonoidHom
    (P ⊔ zpowers swap01) ⊔ zpowers (shift.val*swap01*shift.val⁻¹) = ⊤ ∧
      P ⊔ P.map (MulAut.conj shift.val).toMonoidHom = ⊤ := by
  dsimp only
  constructor
  · let H := (D.map (MulAut.conj position.val).toMonoidHom ⊔ zpowers swap01) ⊔
      zpowers (shift.val*swap01*shift.val⁻¹)
    apply chain_generates H rootChain
    have cert : ∀ i : Fin 5,
        (∃ j : Fin 3, position.val*roots j*position.val⁻¹ =
          Equiv.swap (rootChain i.castSucc) (rootChain i.succ)) ∨
        swap01 = Equiv.swap (rootChain i.castSucc) (rootChain i.succ) ∨
        shift.val*swap01*shift.val⁻¹ = Equiv.swap (rootChain i.castSucc) (rootChain i.succ) := by decide
    intro i
    rcases cert i with ⟨j,hj⟩ | he | he
    · rw [←hj]
      exact (le_sup_left.trans le_sup_left : D.map (MulAut.conj position.val).toMonoidHom ≤ H)
        (mem_map_of_mem _ (roots_mem j))
    · rw [←he]
      exact (le_sup_right.trans le_sup_left : zpowers swap01 ≤ H) (mem_zpowers _)
    · rw [←he]
      exact (le_sup_right : zpowers (shift.val*swap01*shift.val⁻¹) ≤ H) (mem_zpowers _)
  · let H := D.map (MulAut.conj position.val).toMonoidHom ⊔
      (D.map (MulAut.conj position.val).toMonoidHom).map (MulAut.conj shift.val).toMonoidHom
    apply chain_generates H pairChain
    have cert : ∀ i : Fin 5, ∃ j : Fin 3,
        position.val*roots j*position.val⁻¹ = Equiv.swap (pairChain i.castSucc) (pairChain i.succ) ∨
        shift.val*(position.val*roots j*position.val⁻¹)*shift.val⁻¹ =
          Equiv.swap (pairChain i.castSucc) (pairChain i.succ) := by decide
    intro i
    obtain ⟨j,hj | hj⟩ := cert i
    · rw [←hj]
      exact mem_sup_left (mem_map_of_mem _ (roots_mem j))
    · rw [←hj]
      exact mem_sup_right (mem_map_of_mem _ (mem_map_of_mem _ (roots_mem j)))

private theorem shift_normalizes : shift.val ∈ normalizer (D : Set S) := by
  rw [mem_normalizer_iff_map_conj_eq]
  apply eq_of_le_of_card_ge
  · rw [map_le_iff_le_comap,D,closure_le]
    intro a ha
    rcases ha with rfl | rfl | rfl
    all_goals
      change shift.val * _ * shift.val⁻¹ ∈ D
      first
      | have he : shift.val*swap01*shift.val⁻¹=swap23 := by decide
        rw [he]; exact roots_mem 1
      | have he : shift.val*swap23*shift.val⁻¹=swap45 := by decide
        rw [he]; exact roots_mem 2
      | have he : shift.val*swap45*shift.val⁻¹=swap01 := by decide
        rw [he]; exact roots_mem 0
  · rw [card_map_of_injective (MulAut.conj shift.val).injective]

private theorem swap_coordinates (a : S) (ha : a.IsSwap) :
    ∃ c : alternatingGroup (Fin 6), c.val*swap01*c.val⁻¹=a ∧
      (a ∈ D → c.val ∈ normalizer (D : Set S)) := by
  by_cases hD : a ∈ D
  · rw [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq] at hD
    obtain ⟨i,rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) a).mp hD
    have hc : ∀ i : Fin 8, (dWords i).cycleType = {2} →
        ∃ j : Fin 3, shift.val ^ j.val * swap01 * (shift.val ^ j.val)⁻¹ = dWords i := by decide
    obtain ⟨j,hj⟩ := hc i (Equiv.Perm.isSwap_iff_cycleType.mp ha)
    exact ⟨shift ^ j.val, hj, fun _ => (normalizer (D : Set S)).pow_mem shift_normalizes j.val⟩
  · obtain ⟨c,hc⟩ := PointCoreEvenGeneration.exists_even_swap_conjugator a ha
    let b : alternatingGroup (Fin 6) := ⟨Equiv.swap 1 5 * Equiv.swap 2 3,by decide⟩
    refine ⟨c*b,?_,fun he => (hD he).elim⟩
    have hb : b.val*swap01*b.val⁻¹=Equiv.swap 0 5 := by decide
    change (c.val*b.val)*swap01*(c.val*b.val)⁻¹=a
    calc
      _ = c.val*(b.val*swap01*b.val⁻¹)*c.val⁻¹ := by group
      _ = a := by rw [hb,hc]

private theorem map_conj_comp (A : Subgroup S) (g k : S) :
    (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*k)).toMonoidHom := by
  rw [map_map]
  congr 1

/-- The paired plane and two root generators, with an even selector normalizing
    the original plane whenever the prescribed root lies in that plane. -/
private theorem choices (u a : S) (ha : a.IsSwap) :
    ∃ k x : alternatingGroup (Fin 6),
      let E := D.map (MulAut.conj u).toMonoidHom
      let P := E.map (MulAut.conj k.val).toMonoidHom
      (P ⊔ zpowers a) ⊔ (zpowers a).map (MulAut.conj x.val).toMonoidHom = ⊤ ∧
        P ⊔ P.map (MulAut.conj x.val).toMonoidHom = ⊤ ∧
        (a ∈ E → x.val ∈ normalizer (E : Set S)) := by
  let b := u⁻¹*a*u
  have hb : b.IsSwap := by
    obtain ⟨i,j,hij,rfl⟩ := ha
    change (u⁻¹*Equiv.swap i j*(u⁻¹)⁻¹).IsSwap
    rw [←Equiv.swap_apply_apply]
    exact ⟨_,_,u.symm.injective.ne hij,rfl⟩
  obtain ⟨c,hc,hcn⟩ := swap_coordinates b hb
  let w := u*c.val
  let k : alternatingGroup (Fin 6) := MulAut.conjNormal u (c*position)
  let x : alternatingGroup (Fin 6) := MulAut.conjNormal w shift
  let f := (MulAut.conj w).toMonoidHom
  have ha' : f swap01 = a := by
    change (u*c.val)*swap01*(u*c.val)⁻¹=a
    calc
      _ = u*(c.val*swap01*c.val⁻¹)*u⁻¹ := by group
      _ = a := by rw [hc]; dsimp [b]; group
  have hP : (D.map (MulAut.conj u).toMonoidHom).map (MulAut.conj k.val).toMonoidHom =
      (D.map (MulAut.conj position.val).toMonoidHom).map f := by
    rw [map_conj_comp,map_conj_comp]
    congr 3
    change (u*(c.val*position.val)*u⁻¹)*u=(u*c.val)*position.val
    group
  have hPx (A : Subgroup S) : (A.map f).map (MulAut.conj x.val).toMonoidHom =
      (A.map (MulAut.conj shift.val).toMonoidHom).map f := by
    rw [map_conj_comp,map_conj_comp]
    congr 3
    change (w*shift.val*w⁻¹)*w=w*shift.val
    group
  refine ⟨k,x,?_⟩
  dsimp only
  rw [hP]
  refine ⟨?_,?_,?_⟩
  · have hh := congrArg (Subgroup.map f) standard_generators.1
    rw [Subgroup.map_sup,Subgroup.map_sup,MonoidHom.map_zpowers,ha',
      map_top_of_surjective f (MulAut.conj w).surjective] at hh
    have hz : (zpowers a).map (MulAut.conj x.val).toMonoidHom =
        (zpowers (shift.val*swap01*shift.val⁻¹)).map f := by
      rw [←ha',←MonoidHom.map_zpowers,hPx,MonoidHom.map_zpowers]
      rfl
    rwa [hz]
  · have hh := congrArg (Subgroup.map f) standard_generators.2
    rw [Subgroup.map_sup,map_top_of_surjective f (MulAut.conj w).surjective] at hh
    rwa [hPx]
  · intro haE
    have hbD : b ∈ D := by
      obtain ⟨d,hd,he⟩ := haE
      have hback : b=d := by dsimp [b]; rw [←he]; change u⁻¹*(u*d*u⁻¹)*u=d; group
      rwa [hback]
    have hcx : c.val*shift.val*c.val⁻¹ ∈ normalizer (D : Set S) :=
      (normalizer (D : Set S)).mul_mem
        ((normalizer (D : Set S)).mul_mem (hcn hbD) shift_normalizes)
        ((normalizer (D : Set S)).inv_mem (hcn hbD))
    rw [mem_normalizer_iff_map_conj_eq] at hcx ⊢
    change (D.map (MulAut.conj u).toMonoidHom).map (MulAut.conj x.val).toMonoidHom = _
    change D.map (MulAut.conj (c.val*shift.val*c.val⁻¹)).toMonoidHom = D at hcx
    rw [map_conj_comp]
    have he : x.val*u=u*(c.val*shift.val*c.val⁻¹) := by
      change ((u*c.val)*shift.val*(u*c.val)⁻¹)*u=u*(c.val*shift.val*c.val⁻¹)
      group
    rw [he,←map_conj_comp,hcx]
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull.PlaneSelection

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf M
local notation "Rg" => edge L R
local notation "W" => (⁅centralOmega L R,K⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem plane_preimage_eq_radical (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom) :
    borelPlane h e hz hk u = Rg :=
  inf_eq_left.mpr (map_le_iff_le_comap.mp hR.le)

include h e hz hk in
private theorem remaining_plane_data (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    let F := borelPlane h e hz hk u
    F.map π = D.map (MulAut.conj u).toMonoidHom ∧
      (pCore 2 M).relIndex F = 8 ∧
      (centralizer (F : Set M)).relIndex W = 4 := by
  dsimp only
  rcases hR with hp | hb
  · rw [plane_preimage_eq_radical h e hz hk u hp]
    refine ⟨hp,?_,plane_radical_fixed_index h e hz hk u hp⟩
    rw [←CubicAction.permutation_image_card_of_two h e hz hk Rg h.relative_radical.isPGroup,
      hp,card_map_of_injective (MulAut.conj u).injective,D_card]
  · exact ⟨borelPlane_image h e hz hk u hb,(borelPlane_indices h e hz hk u hb).1,
      (borelPlane_indices h e hz hk u hb).2.2.1⟩

include h e hz hk in
private theorem remaining_plane_maximal (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup M) (hAT : A ≤ Rg)
    (hsmall : (centralizer (A : Set M)).relIndex W ≤ 4)
    (hmax : Nat.card (borelPlane h e hz hk u) ≤ Nat.card A) :
    A = borelPlane h e hz hk u := by
  rcases hR with hp | hb
  · rw [plane_preimage_eq_radical h e hz hk u hp] at hmax ⊢
    exact eq_of_le_of_card_ge hAT hmax
  · exact borel_maximal_mover h e hz hk u hb A hAT hsmall hmax

include h e hz hk in
private theorem remaining_join_in_chart (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hc : color Rg c = false) (hct : Adjacent Rg c t)
    (i : M →* FreeAmalgam Rg) (hi : Function.Injective i)
    (hiR : (Rg).map i = Q Rg t) (hiQ : (pCore 2 M).map i = Q Rg c)
    (hiW : (W).map i = U Rg c) :
    edgeOffenderJoin c t = (borelPlane h e hz hk u).map i := by
  let F := borelPlane h e hz hk u
  let J := edgeOffenderJoin c t
  have hfamily := (remaining_edge_thompson h e hz hk u hR hc hct).1
  have hJ : J ∈ edgeMaximalOffenders c t := hfamily.symm ▸ Set.mem_singleton _
  have hnum := remaining_plane_data h e hz hk u hR
  have hfix : (centralizer (F.map i : Set (FreeAmalgam Rg))).relIndex (U Rg c) = 4 := by
    rw [←hiW,←inf_relIndex_right,inf_comm,map_inf_centralizer_of_injective i hi,
      relIndex_map_map_of_injective _ _ hi,inf_relIndex_left]
    exact hnum.2.2
  have hidx : (Q Rg c).relIndex (F.map i) = 8 := by
    rw [←hiQ,relIndex_map_map_of_injective _ _ hi]
    exact hnum.2.1
  have hFsmall : edgeSmallMover c t (F.map i) :=
    ⟨hiR ▸ map_mono inf_le_left,by rw [hfix,hidx]; decide,by rw [hfix]⟩
  have hJi : J ≤ i.range := hJ.1.1.trans (hiR ▸ map_le_range i Rg)
  have hJm : (J.comap i).map i = J := map_comap_eq_self hJi
  have hJT : J.comap i ≤ Rg := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [hJm,hiR]
    exact hJ.1.1
  have hsmall : (centralizer (J.comap i : Set M)).relIndex W ≤ 4 := by
    have hh := hJ.1.2.2
    rw [←hJm,←hiW,←inf_relIndex_right,inf_comm,map_inf_centralizer_of_injective i hi,
      relIndex_map_map_of_injective _ _ hi,inf_relIndex_left] at hh
    exact hh
  have hmax : Nat.card F ≤ Nat.card (J.comap i) := by
    have hh := hJ.2 (F.map i) hFsmall
    rw [←hJm,card_map_of_injective hi,card_map_of_injective hi] at hh
    exact hh
  have he := remaining_plane_maximal h e hz hk u hR (J.comap i) hJT hsmall hmax
  change J = _
  rw [←hJm,he]

private theorem selection_map_conj {A₀ B₀ : Type*} [Group A₀] [Group B₀]
    (f : A₀ →* B₀) (A : Subgroup A₀) (g : A₀) :
    (A.map (MulAut.conj g).toMonoidHom).map f =
      (A.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  apply MonoidHom.ext
  intro y
  simp only [MonoidHom.comp_apply,MulAut.conj_apply,MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe,map_mul,map_inv]

include h e hz hk in
private theorem remaining_plane_lifts (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup M) (a : S) (ha : a.IsSwap) (hA : A.map π = zpowers a) :
    ∃ g ∈ K, ∃ r ∈ K,
      let F := borelPlane h e hz hk u
      let P := F.map (MulAut.conj g).toMonoidHom
      (P ⊔ A) ⊔ A.map (MulAut.conj r).toMonoidHom = ⊤ ∧
        P ⊔ P.map (MulAut.conj r).toMonoidHom = ⊤ ∧
        (A.map π ≤ F.map π → π r ∈ normalizer (F.map π : Set S)) := by
  obtain ⟨k,x,hgen,hpair,hpos⟩ := PlaneSelection.choices u a ha
  obtain ⟨g,hg,hgk⟩ : k.val ∈ (K).map π := by
    rw [CubicAction.component_image h e hz hk]
    exact k.property
  obtain ⟨r,hr,hrx⟩ : x.val ∈ (K).map π := by
    rw [CubicAction.component_image h e hz hk]
    exact x.property
  let F := borelPlane h e hz hk u
  let P := F.map (MulAut.conj g).toMonoidHom
  have hFm : F.map π = D.map (MulAut.conj u).toMonoidHom :=
    (remaining_plane_data h e hz hk u hR).1
  have hPm : P.map π = (D.map (MulAut.conj u).toMonoidHom).map
      (MulAut.conj k.val).toMonoidHom := by
    rw [selection_map_conj,hFm,hgk]
  have hQP : pCore 2 M ≤ P := by
    have hQ : (pCore 2 M).map (MulAut.conj g).toMonoidHom = pCore 2 M :=
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
    rw [←hQ]
    exact map_mono (borelPlane_core_le h e hz hk u)
  have lift (B : Subgroup M) (hQB : pCore 2 M ≤ B) (hB : B.map π = ⊤) : B = ⊤ := by
    have hBE : B ⊔ extensionKernel h = ⊤ := by
      have he := congrArg (Subgroup.comap π) hB
      rwa [comap_map_eq,CubicAction.projection_kernel h e hz hk,comap_top] at he
    have hEB := extensionKernel_no_supplement h B (hBE ▸ (le_top : K ≤ ⊤))
    rw [extensionKernel_twoCore h,sup_of_le_left hQB] at hEB
    rwa [sup_of_le_left hEB] at hBE
  refine ⟨g,hg,r,hr,?_,?_,?_⟩
  · apply lift _ (hQP.trans (le_sup_left.trans le_sup_left))
    rw [Subgroup.map_sup,Subgroup.map_sup,selection_map_conj π A r,hPm,hA,hrx]
    exact hgen
  · apply lift _ (hQP.trans le_sup_left)
    rw [Subgroup.map_sup,selection_map_conj π P r,hPm,hrx]
    exact hpair
  · intro hAF
    rw [hFm,hrx]
    apply hpos
    rw [hA,hFm] at hAF
    exact hAF (mem_zpowers _)

include h e hz hk in
/-- On the original cubic graph the remaining plane mover admits the two
source generation identities with the same critical seed and component selector.
The common fixed subgroup is the full central attachment, for either cover. -/
theorem remaining_small_critical_plane_selectors (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ K,
      let x := (embedM Rg r)⁻¹
      let J := edgeOffenderJoin (alpha Rg) t
      let J' := edgeOffenderJoin (alpha Rg) (act Rg x t)
      (J ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        J ⊔ J' = stabilizer Rg (alpha Rg) ∧
        (Z Rg (alpha Rg) ⊓ centralizer (J : Set (FreeAmalgam Rg))) ⊓
          centralizer (J' : Set (FreeAmalgam Rg)) =
          Z Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
        (((Z Rg z).comap (embedM Rg)).map π ≤ D.map (MulAut.conj u).toMonoidHom →
          π r ∈ normalizer (D.map (MulAut.conj u).toMonoidHom : Set S)) := by
  let i := embedM Rg
  let F := borelPlane h e hz hk u
  let A := (Z Rg z).comap i
  have hAm : A.map i = Z Rg z := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base Rg))
  obtain ⟨a,ha,hA⟩ := small_critical_image_eq_swap h e hz hk p hsmall
  obtain ⟨g,hg,r,hr,hgen,hpair,hpos⟩ := remaining_plane_lifts h e hz hk u hR A a ha hA
  let f := (i g)⁻¹
  let x := (i r)⁻¹
  let t := act Rg f (beta Rg)
  have fixed (v : M) : act Rg ((i v)⁻¹) (alpha Rg) = alpha Rg := by
    have hv : (i v)⁻¹ ∈ stabilizer Rg (alpha Rg) := by
      change (i v)⁻¹ ∈ stabilizer Rg (mVertex Rg 1)
      rw [stabilizer_m_base]
      exact ⟨v⁻¹,by simp only [i,map_inv]⟩
    exact hv
  have hat : Adjacent Rg (alpha Rg) t := by
    rw [←fixed g]
    exact (adjacent_act_iff Rg f (alpha Rg) (beta Rg)).mpr (base_adjacent Rg)
  have hat' : Adjacent Rg (alpha Rg) (act Rg x t) := by
    rw [←fixed r]
    exact (adjacent_act_iff Rg x (alpha Rg) t).mpr hat
  have chart (v : M) : edgeOffenderJoin (alpha Rg) (act Rg ((i v)⁻¹) (beta Rg)) =
      (F.map (MulAut.conj v).toMonoidHom).map i := by
    let j := i.comp (MulAut.conj v).toMonoidHom
    have hadj : Adjacent Rg (alpha Rg) (act Rg ((i v)⁻¹) (beta Rg)) := by
      rw [←fixed v]
      exact (adjacent_act_iff Rg ((i v)⁻¹) (alpha Rg) (beta Rg)).mpr (base_adjacent Rg)
    have hQ : (pCore 2 M).map (MulAut.conj v).toMonoidHom = pCore 2 M :=
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top v)
    have hW : (W).map (MulAut.conj v).toMonoidHom = W := by
      let := h.relative_normal
      exact mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top v)
    have hJR : (Rg).map j = Q Rg (act Rg ((i v)⁻¹) (beta Rg)) := by
      rw [Q_act,Q_beta,inv_inv]
      change (Rg).map (i.comp (MulAut.conj v).toMonoidHom) = _
      rw [←map_map]
      exact selection_map_conj i Rg v
    have hJQ : (pCore 2 M).map j = Q Rg (alpha Rg) := by
      rw [←map_map,hQ,Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    have hJW : (W).map j = U Rg (alpha Rg) := by
      rw [←map_map,hW,graph_U_map h e hz]
    have hh := remaining_join_in_chart h e hz hk u hR rfl hadj j
      ((embedM_injective Rg).comp (MulAut.conj v).injective) hJR hJQ hJW
    simpa only [j,map_map] using hh
  have ht : edgeOffenderJoin (alpha Rg) t = (F.map (MulAut.conj g).toMonoidHom).map i := chart g
  have htt : act Rg x t = act Rg ((i (r*g))⁻¹) (beta Rg) := by
    dsimp [t,x,f]
    rw [map_mul,mul_inv_rev,act_mul]
  have ht' : edgeOffenderJoin (alpha Rg) (act Rg x t) =
      ((F.map (MulAut.conj g).toMonoidHom).map (MulAut.conj r).toMonoidHom).map i := by
    rw [htt,chart]
    congr 1
    rw [map_map]
    congr 1
    apply MonoidHom.ext
    intro v
    change (r*g)*v*(r*g)⁻¹=r*(g*v*g⁻¹)*r⁻¹
    group
  have map_top (B : Subgroup M) (hB : B = ⊤) : B.map i = stabilizer Rg (alpha Rg) := by
    rw [hB,←MonoidHom.range_eq_map]
    exact (stabilizer_m_base Rg).symm
  have hG := map_top _ hgen
  rw [Subgroup.map_sup,Subgroup.map_sup,selection_map_conj i A r,hAm,←ht] at hG
  have hZ : (Z Rg z).map (MulAut.conj (i r)).toMonoidHom = Z Rg (act Rg x z) := by
    rw [Z_act,show x⁻¹=i r from inv_inv _]
  rw [hZ] at hG
  have hJJ := map_top _ hpair
  rw [Subgroup.map_sup,←ht,←ht'] at hJJ
  refine ⟨t,hat,r,hr,hG,hJJ,?_,?_⟩
  · apply le_antisymm
    · rintro v ⟨⟨hv,hvJ⟩,hvJ'⟩
      refine ⟨hv,?_⟩
      apply le_centralizer_iff.mp ?_ (show v ∈ zpowers v from mem_zpowers _)
      rw [←hJJ]
      exact sup_le (le_centralizer_iff.mp (zpowers_le.mpr hvJ))
        (le_centralizer_iff.mp (zpowers_le.mpr hvJ'))
    · rintro v ⟨hv,hvG⟩
      exact ⟨⟨hv,centralizer_le (show edgeOffenderJoin (alpha Rg) t ≤ stabilizer Rg (alpha Rg) from le_sup_left.trans hJJ.le) hvG⟩,
        centralizer_le (show edgeOffenderJoin (alpha Rg) (act Rg x t) ≤ stabilizer Rg (alpha Rg) from le_sup_right.trans hJJ.le) hvG⟩
  · intro hAF
    have hFm := (remaining_plane_data h e hz hk u hR).1
    rw [←hFm] at hAF ⊢
    exact hpos hAF


omit hk in
include h e hz in
/-- Whole-core reconstruction now supplies the paired plane selectors on
all small critical paths of either remaining cubic image. -/
theorem coreExhaustion_or_cubic_plane_selectors :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) = D.map (MulAut.conj u).toMonoidHom ∨
          (Rg).map (CubicAction.projection h e hz hk) = borel.map (MulAut.conj u).toMonoidHom) ∧
        ∀ z (_p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
          (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4 →
          ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ K,
            let x := (embedM Rg r)⁻¹
            let J := edgeOffenderJoin (alpha Rg) t
            let J' := edgeOffenderJoin (alpha Rg) (act Rg x t)
            (J ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
              J ⊔ J' = stabilizer Rg (alpha Rg) ∧
              (Z Rg (alpha Rg) ⊓ centralizer (J : Set (FreeAmalgam Rg))) ⊓
                centralizer (J' : Set (FreeAmalgam Rg)) =
                Z Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              (((Z Rg z).comap (embedM Rg)).map (CubicAction.projection h e hz hk) ≤
                  D.map (MulAut.conj u).toMonoidHom →
                CubicAction.projection h e hz hk r ∈
                  normalizer (D.map (MulAut.conj u).toMonoidHom : Set S)) := by
  rcases coreExhaustion_or_cubic_plane_or_borel h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hR⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,hR,fun z p hsmall =>
      remaining_small_critical_plane_selectors h e hz hk u hR p hsmall⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the paired plane selectors. The remaining
critical-path contradictions are not asserted by this reduction. -/
theorem rankTwo_or_cubic_plane_selectors :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) = D.map (MulAut.conj u).toMonoidHom ∨
          (Rg).map (CubicAction.projection h e hz hk) = borel.map (MulAut.conj u).toMonoidHom) ∧
        ∀ z (_p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
          (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4 →
          ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ K,
            let x := (embedM Rg r)⁻¹
            let J := edgeOffenderJoin (alpha Rg) t
            let J' := edgeOffenderJoin (alpha Rg) (act Rg x t)
            (J ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
              J ⊔ J' = stabilizer Rg (alpha Rg) ∧
              (Z Rg (alpha Rg) ⊓ centralizer (J : Set (FreeAmalgam Rg))) ⊓
                centralizer (J' : Set (FreeAmalgam Rg)) =
                Z Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              (((Z Rg z).comap (embedM Rg)).map (CubicAction.projection h e hz hk) ≤
                  D.map (MulAut.conj u).toMonoidHom →
                CubicAction.projection h e hz hk r ∈
                  normalizer (D.map (MulAut.conj u).toMonoidHom : Set S)) :=
  (coreExhaustion_or_cubic_plane_selectors h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
