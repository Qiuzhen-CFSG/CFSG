module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSelectors
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSelectors
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBorelThompson
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms

/-!
# Normalized plane selectors on the original cubic graph

For every two-subgroup containing Q, its normalizer maps onto the normalizer
of its six-letter image. Quotient first by Q: the remaining kernel has order
three, so the coprime normalizer theorem applies. Since E lies in KQ, an even
normalizer lift can then be adjusted by Q to lie in the original component K.
This retains ker(projection) = E and the nontrivial quotient E/Q; the original
radical is not required to be Sylow.

A small critical seed lies in the plane mover on its actual first edge:
every transposition in the six-letter Borel lies in its three-pair plane.
Lift the paired plane selectors while normalizing that entire mover. The
component switch preserves both local generation identities, normalizes the
original first-edge Thompson join, and puts the original and switched endpoint
seeds in that same join. Edge-chart transport returns the construction to the
unchanged critical path and first edge.

The mover is quadratic on the entire seed Z. Indeed Z is the join of the
moving cover U with the incident edge seed, which centralizes the mover.
Consequently the commutator of Z with the two endpoint seeds is centralized
by the same first-edge mover. This includes the central attachments in both
cover orders sixteen and thirty-two, without identifying Z with the full X.

The whole-core and literal C.1.32 applications supply these normalized
selectors in both remaining cubic branches. Compatible backward critical
paths, their R4/R6 comparisons, the plane/Borel contradictions, both core
exhaustions and the final two-outcome reconstruction remain to be proved.
These are the small-image selection and normalization clauses used in the
source argument, not the full assertion of (5.6) or (5.7).

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.6)(b--d), printed pp.917--918, and their use in (5.7), p.919;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
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
/-- Normalizers lift through the actual cubic projection for every two-subgroup
containing the ambient two-core. -/
theorem cubic_two_normalizer_image (A : Subgroup M)
    (hA : IsPGroup 2 A) (hQA : pCore 2 M ≤ A) :
    (normalizer (A : Set M)).map π = normalizer (A.map π : Set S) := by
  let q := QuotientGroup.mk' (pCore 2 M)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hQπ : pCore 2 M ≤ (π).ker := by
    rw [CubicAction.projection_kernel]
    exact le_sup_right
  let f := QuotientGroup.lift (pCore 2 M) π hQπ
  have hcomp : f.comp q = π := rfl
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,rfl⟩ := CubicEven.projection_surjective h e hz hk y
    exact ⟨q x,rfl⟩
  have hcard : Nat.card f.ker = 3 := by
    rw [show f.ker = (extensionKernel h).map q from by
      rw [QuotientGroup.ker_lift,CubicAction.projection_kernel],
      ←relIndex_ker,show q.ker = pCore 2 M from QuotientGroup.ker_mk' _]
    change ((pCore 2 M).comap (extensionKernel h).subtype).index = 3
    rw [←pCore_subnormal_eq_comap 2
      (inferInstance : (extensionKernel h).Normal).isSubnormal]
    exact extensionKernel_core_index h hz
  have hnq : (normalizer (A : Set M)).map q =
      normalizer (A.map q : Set (M ⧸ pCore 2 M)) := by
    apply (comap_injective hq)
    rw [comap_map_eq,comap_normalizer_eq_of_surjective _ hq,
      comap_map_eq,show q.ker = pCore 2 M from QuotientGroup.ker_mk' _,
      sup_of_le_left hQA,sup_of_le_left (hQA.trans A.le_normalizer)]
  let : Fact (IsPGroup 2 (A.map q)) := ⟨hA.map q⟩
  have hnf := normalizer_map_eq_of_coprime_kernel 2 (A.map q) f hf
    (by rw [hcard]; decide)
  rw [←hcomp,←map_map,hnq,←hnf,map_map]

include h e hz hk in
/-- An even normalizer lifts inside the original relative component, after
removing a two-core factor that already normalizes the subgroup. -/
theorem cubic_two_normalizer_component_lift (A : Subgroup M)
    (hA : IsPGroup 2 A) (hQA : pCore 2 M ≤ A)
    (x : alternatingGroup (Fin 6))
    (hx : x.val ∈ normalizer (A.map π : Set S)) :
    ∃ r ∈ K, r ∈ normalizer (A : Set M) ∧ π r = x.val := by
  rw [←cubic_two_normalizer_image h e hz hk A hA hQA] at hx
  obtain ⟨r,hr,hrx⟩ := hx
  have hrKQ : r ∈ K ⊔ pCore 2 M := by
    have hmem : r ∈ ((K).map π).comap π := by
      change π r ∈ (K).map π
      rw [CubicAction.component_image,hrx]
      exact x.property
    rw [comap_map_eq,CubicAction.projection_kernel] at hmem
    apply (sup_le le_sup_left (show extensionKernel h ≤ K ⊔ pCore 2 M from
      sup_le ((map_subtype_le _).trans le_sup_left) le_sup_right)) hmem
  obtain ⟨k,hkK,q,hqQ,hkq⟩ := mem_sup_of_normal_right.mp hrKQ
  have hqN := A.le_normalizer (hQA hqQ)
  have hkN : k ∈ normalizer (A : Set M) := by
    apply (normalizer (A : Set M)).mul_mem_cancel_right hqN |>.mp
    rwa [hkq]
  have hqπ : π q = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [CubicAction.projection_kernel]
    exact mem_sup_right hqQ
  refine ⟨k,hkK,hkN,?_⟩
  rw [←hkq,map_mul,hqπ,mul_one] at hrx
  exact hrx

include h e hz hk in
private theorem remaining_small_image_le_plane (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup M) (hAT : A ≤ Rg) (a : S) (ha : a.IsSwap)
    (hA : A.map π = zpowers a) :
    A.map π ≤ (borelPlane h e hz hk u).map π := by
  rw [(remaining_plane_data h e hz hk u hR).1,hA]
  apply zpowers_le.mpr
  have har : a ∈ (Rg).map π := (hA ▸ map_mono hAT) (mem_zpowers _)
  rcases hR with hp | hb
  · rwa [hp] at har
  · rw [hb] at har
    obtain ⟨b,hb,he⟩ := har
    have hbs : b.IsSwap := by
      obtain ⟨i,j,hij,hs⟩ := ha
      have hback : b=u⁻¹*a*u := by rw [←he]; change b=u⁻¹*(u*b*u⁻¹)*u; group
      rw [hback,hs]
      change (u⁻¹*Equiv.swap i j*(u⁻¹)⁻¹).IsSwap
      rw [←Equiv.swap_apply_apply]
      exact ⟨_,_,u.symm.injective.ne hij,rfl⟩
    obtain ⟨i,rfl⟩ := BorelCalculation.words_complete b hb
    have cert : ∀ i : Fin 16, (BorelCalculation.words i).cycleType = {2} →
        ∃ j : Fin 8, dWords j = BorelCalculation.words i := by decide
    obtain ⟨j,hj⟩ := cert i (Equiv.Perm.isSwap_iff_cycleType.mp hbs)
    apply he ▸ mem_map_of_mem _
    rw [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq]
    exact (mem_disjointTranspositions_iff (3 : Fin 4) _).mpr ⟨j,hj⟩

include h e hz hk in
private theorem remaining_normalized_plane_lifts (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup M) (a : S) (ha : a.IsSwap) (hA : A.map π = zpowers a)
    (hAF : A.map π ≤ (borelPlane h e hz hk u).map π) :
    ∃ g ∈ K, ∃ r ∈ K,
      let F := borelPlane h e hz hk u
      let P := F.map (MulAut.conj g).toMonoidHom
      (P ⊔ A) ⊔ A.map (MulAut.conj r).toMonoidHom = ⊤ ∧
        P ⊔ P.map (MulAut.conj r).toMonoidHom = ⊤ ∧
        r ∈ normalizer (F : Set M) := by
  obtain ⟨k,x,hgen,hpair,hpos⟩ := PlaneSelection.choices u a ha
  obtain ⟨g,hg,hgk⟩ : k.val ∈ (K).map π := by
    rw [CubicAction.component_image h e hz hk]
    exact k.property
  have hpos' : x.val ∈ normalizer ((borelPlane h e hz hk u).map π : Set S) := by
    rw [(remaining_plane_data h e hz hk u hR).1]
    apply hpos
    have hh := hAF
    rw [hA,(remaining_plane_data h e hz hk u hR).1] at hh
    exact hh (mem_zpowers _)
  obtain ⟨r,hr,hrN,hrx⟩ := cubic_two_normalizer_component_lift h e hz hk
    (borelPlane h e hz hk u) (h.relative_radical.isPGroup.to_le inf_le_left)
    (borelPlane_core_le h e hz hk u) x hpos'
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
  · exact hrN

include h e hz hk in
/-- On the original cubic graph the remaining plane mover admits the two
source generation identities with the same critical seed and component selector.
The common fixed subgroup is the full central attachment, for either cover. -/
private theorem remaining_small_critical_normalized_plane_selectors_base (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hfirst : p.walk.getVert 1 = beta Rg) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ K,
      let x := (embedM Rg r)⁻¹
      let J := edgeOffenderJoin (alpha Rg) t
      let J' := edgeOffenderJoin (alpha Rg) (act Rg x t)
      (J ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        J ⊔ J' = stabilizer Rg (alpha Rg) ∧
        (Z Rg (alpha Rg) ⊓ centralizer (J : Set (FreeAmalgam Rg))) ⊓
          centralizer (J' : Set (FreeAmalgam Rg)) =
          Z Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
        x ∈ normalizer (edgeOffenderJoin (alpha Rg) (beta Rg) : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (beta Rg) := by
  let i := embedM Rg
  let F := borelPlane h e hz hk u
  let A := (Z Rg z).comap i
  have hAm : A.map i = Z Rg z := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base Rg))
  obtain ⟨a,ha,hA⟩ := small_critical_image_eq_swap h e hz hk p hsmall
  have hZedge : Z Rg z ≤ Q Rg (beta Rg) := by
    rw [←hfirst]
    apply Z_le_Q_of_dist_lt Rg z ((sourceGeometry h).exists_critical z p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(sourceGeometry h).distance_constant z p.end_color]
    change p.walk.length-1<(sourceGeometry h).b Rg
    rw [←p.length_eq_b]
    have hp : 0 < p.walk.length := p.length_eq_b ▸ sourceDistance_pos h
    omega
  have hAT : A ≤ Rg := by
    apply (map_le_map_iff_of_injective (embedM_injective Rg)).mp
    change A.map i ≤ (Rg).map i
    rw [hAm,←Q_beta]
    exact hZedge
  obtain ⟨g,hg,r,hr,hgen,hpair,hrN⟩ := remaining_normalized_plane_lifts h e hz hk
    u hR A a ha hA (remaining_small_image_le_plane h e hz hk u hR A hAT a ha hA)
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
  · have hbase : edgeOffenderJoin (alpha Rg) (beta Rg) = F.map i := by
      exact remaining_join_in_chart h e hz hk u hR rfl (base_adjacent Rg) i
        (embedM_injective Rg) (Q_beta Rg).symm
        (Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le).symm
        (graph_U_map h e hz)
    rw [hbase]
    have hxn : x ∈ normalizer (F.map i : Set (FreeAmalgam Rg)) :=
      (normalizer (F.map i : Set (FreeAmalgam Rg))).inv_mem
        (F.le_normalizer_map i (mem_map_of_mem i hrN))
    have hZA : Z Rg z ≤ F.map i := by
      rw [←hAm]
      apply map_mono
      exact le_inf hAT (map_le_iff_le_comap.mp (by
        rw [←(remaining_plane_data h e hz hk u hR).1]
        exact remaining_small_image_le_plane h e hz hk u hR A hAT a ha hA))
    refine ⟨hxn,sup_le hZA ?_⟩
    rw [Z_act]
    exact (map_mono hZA).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp ((normalizer (F.map i : Set (FreeAmalgam Rg))).inv_mem hxn))

include h e hz hk in
private theorem remaining_edge_join_act (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hc : color Rg c = false) (hct : Adjacent Rg c t)
    (g : FreeAmalgam Rg) :
    edgeOffenderJoin (act Rg g c) (act Rg g t) =
      (edgeOffenderJoin c t).map (MulAut.conj g⁻¹).toMonoidHom := by
  obtain ⟨i,hi,hir,hiR,hiQ,hiW⟩ := remaining_edge_coordinates h e hz hc hct
  have hJ := remaining_join_in_chart h e hz hk u hR hc hct i hi hiR hiQ hiW
  let j := (MulAut.conj g⁻¹).toMonoidHom.comp i
  have hRj : (Rg).map j = Q Rg (act Rg g t) := by
    rw [Q_act,←hiR,map_map]
  have hQj : (pCore 2 M).map j = Q Rg (act Rg g c) := by
    rw [Q_act,←hiQ,map_map]
  have hWj : (⁅centralOmega L R,K⁆ : Subgroup M).map j = U Rg (act Rg g c) := by
    rw [U_act,←hiW,map_map]
  have hh := remaining_join_in_chart h e hz hk u hR
    (by rw [action_preserves_color,hc]) ((adjacent_act_iff Rg g c t).mpr hct)
    j ((MulAut.conj g⁻¹).injective.comp hi) hRj hQj hWj
  rw [hh,hJ,map_map]


include h e hz hk in
/-- The source maximum mover is quadratic on the full seed, not only its
moving cover. The incident central attachment contributes no commutator. -/
theorem remaining_edge_full_seed_quadratic (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hc : color Rg c = false) (hct : Adjacent Rg c t) :
    ⁅⁅Z Rg c,edgeOffenderJoin c t⁆,edgeOffenderJoin c t⁆ = ⊥ := by
  let J := edgeOffenderJoin c t
  have hj := remaining_edge_thompson h e hz hk u hR hc hct
  have hQJ : Q Rg c ≤ J := hj.2.1
  have hJT : J ≤ Q Rg t := hj.2.2.1
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hct
    rw [hc] at hh
    cases he : color Rg t <;> simp_all
  have hseed : Z Rg t ≤ centralizer (J : Set (FreeAmalgam Rg)) := by
    apply le_trans ?_ (centralizer_le hJT)
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hUQ : U Rg c ≤ Q Rg c := by
    apply (DistanceEight.U_le_Z Rg c).trans
    apply Z_le_Q_of_dist_lt Rg c ((sourceGeometry h).exists_critical c hc)
    rw [SimpleGraph.dist_self,(sourceGeometry h).distance_constant c hc]
    exact sourceDistance_pos h
  have he : ⁅J,U Rg c⁆ = ⁅J,Z Rg c⁆ :=
    commutator_eq_of_centralizing_sup
      ((sup_comm (Z Rg t) (U Rg c)).trans
        (vertex_seed_eq_moving_sup_edge h e hz hc hct).symm) hseed
      ((hUQ.trans hQJ).trans J.le_normalizer)
  rw [commutator_comm J,commutator_comm J] at he
  rw [←he]
  exact hj.2.2.2.2.2.2.2

include h e hz hk in
/-- The same small critical path admits paired plane selectors whose switch
normalizes its actual first-edge Thompson join, including the cubic kernel. -/
theorem remaining_small_critical_normalized_plane_selectors (u : S)
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
        x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) :
          Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ∧
        ⁅⁅Z Rg (alpha Rg),Z Rg z ⊔ Z Rg (act Rg x z)⁆,
          edgeOffenderJoin (alpha Rg) (p.walk.getVert 1)⁆ = ⊥ := by
  have hat₁ : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  obtain ⟨g,hg,hgβ⟩ := stabilizer_transitive_neighbors Rg (alpha Rg)
    (base_adjacent Rg) hat₁
  change act Rg g (beta Rg) = p.walk.getVert 1 at hgβ
  have hga : act Rg g (alpha Rg) = alpha Rg := hg
  have hgia : act Rg g⁻¹ (alpha Rg) = alpha Rg :=
    (stabilizer Rg (alpha Rg)).inv_mem hg
  have hgib : act Rg g⁻¹ (p.walk.getVert 1) = beta Rg := by
    rw [←hgβ,←act_mul,mul_inv_cancel,act_one]
  have hp0 : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ (alpha Rg)) (act Rg g⁻¹ z),
      p₀.walk.getVert 1 = act Rg g⁻¹ (p.walk.getVert 1) :=
    ⟨p.act g⁻¹,by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hgia,hgib] at hp0
  obtain ⟨p₀,hp₀⟩ := hp0
  have hsmall₀ : (Q Rg (act Rg g⁻¹ z)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hgia,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹⁻¹).injective]
    exact hsmall
  obtain ⟨t₀,hat₀,r₀,hr₀,hgen,hpair,hfix,hnorm,hcontained⟩ :=
    remaining_small_critical_normalized_plane_selectors_base h e hz hk u hR p₀ hsmall₀ hp₀
  have hgm : g ∈ (embedM Rg).range := by
    change g ∈ Mbar Rg
    rwa [←stabilizer_m_base Rg]
  obtain ⟨m,hm⟩ := hgm
  let r := m⁻¹*r₀*m
  have hr : r ∈ K := by
    let := h.relative_normal
    exact (inferInstance : (K).Normal).conj_mem' r₀ hr₀ m
  let x₀ := (embedM Rg r₀)⁻¹
  let x := (embedM Rg r)⁻¹
  have hx : x = g⁻¹*x₀*g := by
    dsimp only [x,r,x₀]
    rw [map_mul,map_mul,map_inv,hm]
    group
  have hact (v : Vertex Rg) : act Rg x (act Rg g v) = act Rg g (act Rg x₀ v) := by
    rw [hx,←act_mul,←act_mul]
    congr 1
    group
  have hcancel (v : Vertex Rg) : act Rg g (act Rg g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hat : Adjacent Rg (alpha Rg) (act Rg g t₀) := by
    rw [←hga]
    exact (adjacent_act_iff Rg g _ _).mpr hat₀
  have hxt₀ : Adjacent Rg (alpha Rg) (act Rg x₀ t₀) := by
    have hx₀ : act Rg x₀ (alpha Rg) = alpha Rg := by
      change (embedM Rg r₀)⁻¹ ∈ stabilizer Rg (mVertex Rg 1)
      rw [stabilizer_m_base]
      exact ⟨r₀⁻¹,by rw [map_inv]⟩
    rw [←hx₀]
    exact (adjacent_act_iff Rg x₀ _ _).mpr hat₀
  have chart (t : Vertex Rg) (ht : Adjacent Rg (alpha Rg) t) :
      edgeOffenderJoin (alpha Rg) (act Rg g t) =
        (edgeOffenderJoin (alpha Rg) t).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [hga] using remaining_edge_join_act h e hz hk u hR rfl ht g
  have hstab : (stabilizer Rg (alpha Rg)).map (MulAut.conj g⁻¹).toMonoidHom =
      stabilizer Rg (alpha Rg) := by
    rw [←stabilizer_act,hga]
  have hgen' := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
  rw [Subgroup.map_sup,Subgroup.map_sup,←chart t₀ hat₀,←Z_act,←Z_act,hcancel,
    ←hact,hcancel,hstab] at hgen'
  have hpair' := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hpair
  rw [Subgroup.map_sup,←chart t₀ hat₀,←chart (act Rg x₀ t₀) hxt₀,←hact,hstab] at hpair'
  refine ⟨act Rg g t₀,hat,r,hr,hgen',hpair',?_,?_⟩
  · apply le_antisymm
    · rintro v ⟨⟨hv,hvJ⟩,hvJ'⟩
      refine ⟨hv,?_⟩
      apply le_centralizer_iff.mp ?_ (show v ∈ zpowers v from mem_zpowers _)
      rw [←hpair']
      exact sup_le (le_centralizer_iff.mp (zpowers_le.mpr hvJ))
        (le_centralizer_iff.mp (zpowers_le.mpr hvJ'))
    · rintro v ⟨hv,hvG⟩
      exact ⟨⟨hv,centralizer_le (show edgeOffenderJoin (alpha Rg) (act Rg g t₀) ≤
        stabilizer Rg (alpha Rg) from le_sup_left.trans hpair'.le) hvG⟩,
        centralizer_le (show edgeOffenderJoin (alpha Rg) (act Rg x (act Rg g t₀)) ≤
          stabilizer Rg (alpha Rg) from le_sup_right.trans hpair'.le) hvG⟩
  · constructor
    · rw [←hgβ,chart (beta Rg) (base_adjacent Rg)]
      have hh := (edgeOffenderJoin (alpha Rg) (beta Rg)).le_normalizer_map
        (MulAut.conj g⁻¹).toMonoidHom (mem_map_of_mem _ hnorm)
      change g⁻¹*x₀*g⁻¹⁻¹ ∈ normalizer ((edgeOffenderJoin (alpha Rg) (beta Rg)).map
        (MulAut.conj g⁻¹).toMonoidHom : Set (FreeAmalgam Rg)) at hh
      simpa only [inv_inv,←hx] using hh
    · have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hcontained
      rw [Subgroup.map_sup,←Z_act,←Z_act,hcancel,←hact,hcancel,
        ←chart (beta Rg) (base_adjacent Rg),hgβ] at hh
      refine ⟨hh,?_⟩
      apply le_bot_iff.mp
      exact (commutator_mono (commutator_mono le_rfl hh) le_rfl).trans_eq
        (remaining_edge_full_seed_quadratic h e hz hk u hR rfl hat₁)

omit hk in
include h e hz in
/-- The exceptional whole-core reduction supplies normalized selectors on each
original small critical path in both remaining cubic radical branches. -/
theorem coreExhaustion_or_cubic_normalized_plane_selectors :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) = D.map (MulAut.conj u).toMonoidHom ∨
          (Rg).map (CubicAction.projection h e hz hk) = borel.map (MulAut.conj u).toMonoidHom) ∧
        ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
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
              x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) :
                Set (FreeAmalgam Rg)) ∧
              Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ∧
              ⁅⁅Z Rg (alpha Rg),Z Rg z ⊔ Z Rg (act Rg x z)⁆,
                edgeOffenderJoin (alpha Rg) (p.walk.getVert 1)⁆ = ⊥ := by
  rcases coreExhaustion_or_cubic_plane_or_borel h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hR⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,hR,fun z p hsmall =>
      remaining_small_critical_normalized_plane_selectors h e hz hk u hR p hsmall⟩


omit hk in
include h e hz in
/-- Literal C.1.32 application of the normalized plane selectors, with the
original projection and both complete moving covers retained. -/
theorem rankTwo_or_cubic_normalized_plane_selectors :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) = D.map (MulAut.conj u).toMonoidHom ∨
          (Rg).map (CubicAction.projection h e hz hk) = borel.map (MulAut.conj u).toMonoidHom) ∧
        ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
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
              x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) :
                Set (FreeAmalgam Rg)) ∧
              Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ∧
              ⁅⁅Z Rg (alpha Rg),Z Rg z ⊔ Z Rg (act Rg x z)⁆,
                edgeOffenderJoin (alpha Rg) (p.walk.getVert 1)⁆ = ⊥ :=
  (coreExhaustion_or_cubic_normalized_plane_selectors h e hz).imp
    (rankTwo_of_exhaustion h e hz) id


end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
