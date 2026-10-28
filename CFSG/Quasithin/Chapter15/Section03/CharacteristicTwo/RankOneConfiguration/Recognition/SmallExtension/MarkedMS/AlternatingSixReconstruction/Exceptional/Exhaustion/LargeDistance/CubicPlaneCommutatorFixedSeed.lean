module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneDerivedAction
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneCriticalPlane
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlanePairedFixedSeeds
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneCrossCommutator

/-!
# Fixed subgroup of the paired radius commutator

For the retained paths a--v--c--t--z and b--v'--c'--t'--z, set
Y = V_a intersect Q_c, Y' = V_b intersect Q_c', and W = [Y,Y'].
The full endpoint seed satisfies
C_{Z_z}(W) = C_{Z_z}(Y join Y') = Z_t intersect Z_t'.
This subgroup is properly contained in the common full critical kernel
I = (Z_z intersect Q_a) intersect (Z_z intersect Q_b), and has index
at least eight in Z_z.

The reciprocal critical actions are recovered from the literal disjoint
kernel supplements. Thus the seed commutator fixes exactly I, and its
containment in W puts C_{Z_z}(W) inside I. Each radius normalizes this
fixed subgroup. Its commutator with that subgroup consequently lies both
in I and in the radius line, which is disjoint from the opposite kernel.
Both radii therefore centralize it. The existing full fixed-seed formulas
identify the two last-edge seeds. Their fixed index on I gives the strict
containment and the lower bound of eight.

The paired application starts from one full-kernel selection. The original
opposite-edge conjugator, whose square centralizes Z_z, supplies the reverse
supplement and escape on those same paths. No separate existential selections
are identified. Whole-core and literal C.1.32 applications retain the
actual cubic projection with kernel E, its odd nontrivial E/Q, the original
proper odd-index radical and both moving covers of orders sixteen and
thirty-two. All full central attachments remain in the fixed subgroups.
This comparison does not establish the shifted-path or terminal exclusion;
the other branches, both core exhaustions and unconditional reconstruction
remain required. Internal imports reuse the checked path and transport lemmas.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), paired comparisons toward (5.12), printed pp.924--927;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem reciprocal_action_of_disjoint_kernel
    {a b z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) b z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hq : (Q Rg z).relIndex (Z Rg b) < 4)
    (hdis : ⁅Z Rg b,Z Rg z⁆ ⊓ (Z Rg z ⊓ Q Rg a) = ⊥) :
    ⁅Z Rg a,⁅Z Rg b,Z Rg z⁆⁆ = ⁅Z Rg a,Z Rg z⁆ := by
  let T := ⁅Z Rg a,Z Rg z⁆
  let T' := ⁅Z Rg b,Z Rg z⁆
  let H := ⁅Z Rg a,T'⁆
  have hTZ := (critical_commutator_le_seed h q).trans inf_le_right
  have hcard : Nat.card T = 2 := small_critical_commutator_card h e hz hk p hp
  have hcard' : Nat.card T' = 2 := small_critical_commutator_card h e hz hk q hq
  have hHT : H ≤ T := commutator_mono le_rfl hTZ
  let : Finite T := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let : Finite H := Finite.of_injective (inclusion hHT) (inclusion_injective _)
  have hne : H ≠ ⊥ := by
    intro he
    have hC : T' ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
    let pr := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color
      (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        a p.start_color (by
          rw [(sourceGeometry h).distance_constant _ p.start_color]
          exact sourceDistance_pos h) z p.end_color p.critical)
    have hf := critical_seed_centralizer_intersection h e pr
    have hTF : T' ≤ Z Rg z ⊓ Q Rg a := (le_inf hTZ hC).trans_eq hf
    have he' : T' = ⊥ := (inf_eq_left.mpr hTF).symm.trans hdis
    rw [he',card_bot] at hcard'
    omega
  exact eq_of_le_of_card_ge hHT (by
    change Nat.card T ≤ Nat.card H
    have hh := (one_lt_card_iff_ne_bot H).mpr hne
    omega)

private theorem fixed_of_normalized_fixed_kernel {J : Type*} [Group J]
    (Y K I F H : Subgroup J) (hKI : K ≤ I)
    (hIK : Y ≤ normalizer (K : Set J)) (hIF : I ≤ F)
    (hmove : ⁅Y,I⁆ = H) (hdis : H ⊓ F = ⊥) :
    K ≤ centralizer (Y : Set J) := by
  apply le_centralizer_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply le_bot_iff.mp
  exact (le_inf ((commutator_mono le_rfl hKI).trans_eq hmove)
    ((le_normalizer_iff_commutator_le_right.mp hIK).trans (hKI.trans hIF))).trans_eq hdis

include h e hz hk in
/-- The paired radius commutator has the same fixed subgroup in the full
endpoint seed as both radii together: the intersection of their last-edge
seeds. Its fixed index is at least eight, strictly beyond the common kernel. -/
theorem plane_radius_commutator_fixed_seed
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a b z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) b z)
    (hp : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a)
    (hq : ¬ ⁅V Rg b ⊓ Q Rg (q.walk.getVert 2),Z Rg z⁆ ≤ Z Rg b)
    (hs : (Z Rg z ⊓ Q Rg b) ⊔ ⁅Z Rg a,Z Rg z⁆ = Z Rg z)
    (hd : ⁅Z Rg a,Z Rg z⁆ ⊓ (Z Rg z ⊓ Q Rg b) = ⊥)
    (hs' : (Z Rg z ⊓ Q Rg a) ⊔ ⁅Z Rg b,Z Rg z⁆ = Z Rg z)
    (hd' : ⁅Z Rg b,Z Rg z⁆ ⊓ (Z Rg z ⊓ Q Rg a) = ⊥) :
    let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
    let Y' := V Rg b ⊓ Q Rg (q.walk.getVert 2)
    let W := ⁅Y,Y'⁆
    let I := (Z Rg z ⊓ Q Rg a) ⊓ (Z Rg z ⊓ Q Rg b)
    let C := Z Rg z ⊓ centralizer (W : Set (FreeAmalgam Rg))
    C = Z Rg z ⊓ centralizer ((Y ⊔ Y' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      C = Z Rg (p.walk.getVert 3) ⊓ Z Rg (q.walk.getVert 3) ∧
      C < I ∧ 8 ≤ C.relIndex (Z Rg z) := by
  let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
  let Y' := V Rg b ⊓ Q Rg (q.walk.getVert 2)
  let W := ⁅Y,Y'⁆
  let F := Z Rg z ⊓ Q Rg a
  let F' := Z Rg z ⊓ Q Rg b
  let I := F ⊓ F'
  let C := Z Rg z ⊓ centralizer (W : Set (FreeAmalgam Rg))
  have hcross := reciprocal_action_of_disjoint_kernel h e hz hk p q
    (hsmall _ _ p) (hsmall _ _ q) hd'
  have hcross' := reciprocal_action_of_disjoint_kernel h e hz hk q p
    (hsmall _ _ q) (hsmall _ _ p) hd
  obtain ⟨_,_,_,hfixed,_⟩ := plane_reciprocal_seed_derived_action h e hz hk p q
    (hsmall _ _ p) (hsmall _ _ q) hcross hcross'
  obtain ⟨_,_,_,hIi,hm,hH,hdH,_,hidx,_,_,_⟩ :=
    plane_radius_common_kernel_control h e hz hk u hR hb4 hsmall p q hp hs hd
  obtain ⟨_,_,_,_,hm',_,hdH',_,_,_,_,_⟩ :=
    plane_radius_common_kernel_control h e hz hk u hR hb4 hsmall q p hq hs' hd'
  have hpR := four_radius_at_endpoint h hb4 p
  have hqR := four_radius_at_endpoint h hb4 q
  have hCI : C ≤ I :=
    (inf_le_inf_left _ (centralizer_le (commutator_mono hpR.2 hqR.2))).trans_eq hfixed
  have hYC : Y ≤ normalizer (C : Set (FreeAmalgam Rg)) :=
    (le_inf (hpR.1.trans (Z_normalized Rg z))
      ((normalizer_commutator_ge_left Y Y').trans (normalizer_le_normalizer_centralizer W))).trans
        inf_normalizer_le_normalizer_inf
  have hYC' : Y' ≤ normalizer (C : Set (FreeAmalgam Rg)) :=
    (le_inf (hqR.1.trans (Z_normalized Rg z))
      ((normalizer_commutator_ge_right Y Y').trans (normalizer_le_normalizer_centralizer W))).trans
        inf_normalizer_le_normalizer_inf
  have hCY : C ≤ centralizer (Y : Set (FreeAmalgam Rg)) :=
    fixed_of_normalized_fixed_kernel Y C I F' ⁅Y,F⁆ hCI hYC inf_le_right hm hdH
  have hCY' : C ≤ centralizer (Y' : Set (FreeAmalgam Rg)) := by
    apply fixed_of_normalized_fixed_kernel Y' C I F ⁅Y',F'⁆ hCI hYC' inf_le_left
    · change ⁅Y',F' ⊓ F⁆ = ⁅Y',F'⁆ at hm'
      simpa only [inf_comm F' F] using hm'
    · exact hdH'
  have heq : C = Z Rg z ⊓ centralizer ((Y ⊔ Y' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
    apply le_antisymm
    · exact le_inf inf_le_left (le_centralizer_iff.mpr
        (sup_le (le_centralizer_iff.mp hCY) (le_centralizer_iff.mp hCY')))
    · exact inf_le_inf_left _ (centralizer_le (commutator_le_sup (H₁ := Y) (H₂ := Y')))
  have hpfix := (radius_fixed_seed h e hz hk u hR hb4 hsmall p hp).1
  have hqfix := (radius_fixed_seed h e hz hk u hR hb4 hsmall q hq).1
  have hseeds : C = Z Rg (p.walk.getVert 3) ⊓ Z Rg (q.walk.getVert 3) := by
    rw [←hpfix,←hqfix]
    apply le_antisymm
    · exact le_inf (le_inf inf_le_left hCY) (le_inf inf_le_left hCY')
    · intro x hx
      apply heq.symm.le
      exact ⟨hx.1.1,le_centralizer_iff.mpr
        (sup_le (le_centralizer_iff.mp (zpowers_le.mpr hx.1.2))
          (le_centralizer_iff.mp (zpowers_le.mpr hx.2.2))) (mem_zpowers x)⟩
  have hproper : C < I := lt_of_le_of_ne hCI (by
    intro he
    have hh : I ≤ centralizer (Y : Set (FreeAmalgam Rg)) := he ▸ hCY
    have hzH : ⁅Y,F⁆ = ⊥ := hm.symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
    rw [hzH,card_bot] at hH
    omega)
  let E := I ⊓ centralizer (Y : Set (FreeAmalgam Rg))
  have hCE : C ≤ E := le_inf hCI hCY
  have hEi : E.relIndex (Z Rg z) = 8 := by
    have ht := relIndex_mul_relIndex E I (Z Rg z) inf_le_left
      (show I ≤ Z Rg z from inf_le_left.trans inf_le_left)
    have hei : E.relIndex I = 2 := by
      rw [show E = I ⊓ centralizer (Y : Set (FreeAmalgam Rg)) from rfl,inf_relIndex_left]
      exact hidx
    rw [hei,hIi] at ht
    exact ht.symm
  let := finite_Z Rg z
  have hbound := relIndex_le_of_le_left (L := Z Rg z) hCE
    (index_ne_zero_of_finite (H := C.subgroupOf (Z Rg z)))
  rw [hEi] at hbound
  exact ⟨heq,hseeds,hproper,hbound⟩


include h e hz hk in
/-- The original paired radius commutator fixes exactly the intersection of
the two full last-edge seeds. This is a proper subgroup of the common full
kernel, with fixed index at least eight in the endpoint seed. -/
theorem plane_small_four_paired_commutator_fixed_seed
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      ∃ s, Adjacent Rg z s ∧
        Q Rg s ⊔ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) = stabilizer Rg z ∧
        ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
            (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
            (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
              (4-i) + (4-j)) ∧
            let b := act Rg g⁻¹ a
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let Y' := V Rg b ⊓ Q Rg (q.walk.getVert 2)
            let W := ⁅Y,Y'⁆
            let I := (Z Rg z ⊓ Q Rg a) ⊓ (Z Rg z ⊓ Q Rg b)
            let C := Z Rg z ⊓ centralizer (W : Set (FreeAmalgam Rg))
            C = Z Rg z ⊓ centralizer ((Y ⊔ Y' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
              C = Z Rg (p.walk.getVert 3) ⊓ Z Rg (q.walk.getVert 3) ∧
              C < I ∧ 8 ≤ C.relIndex (Z Rg z) := by
  obtain ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,
    hsupp,hdis,_,_,_,_,_,_,_,_,hescape,_,_⟩ :=
    plane_small_four_full_kernel_comparison h e hz hk u hR hb4 hsmall
  let F := Z Rg z ⊓ Q Rg a
  let F' := Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)
  let f := (MulAut.conj g).toMonoidHom
  have hZz : (Z Rg z).map f = Z Rg z := by
    simpa only [inv_inv,hfix] using (Z_act Rg g⁻¹ z).symm
  have hF : F.map f = F' := by
    rw [show F = Z Rg z ⊓ Q Rg a from rfl,
      Subgroup.map_inf _ _ f (MulAut.conj g).injective,hZz]
    simp only [F',Q_act,inv_inv,f]
  have hFF : (F.map f).map f = F :=
    map_conj_twice_of_square_centralizes F g
      (centralizer_le inf_le_left
        (plane_edge_square_centralizes_seed h e hz hk u hR p.end_color hzs g hg))
  have hsupp' : F ⊔ ⁅Z Rg (act Rg g⁻¹ a),Z Rg z⁆ = Z Rg z := by
    have hh := congrArg (Subgroup.map f) hsupp
    change (F' ⊔ ⁅Z Rg a,Z Rg z⁆).map f = (Z Rg z).map f at hh
    rw [Subgroup.map_sup,←hF,hFF,map_commutator,hZz] at hh
    simpa only [Z_act,inv_inv,f] using hh
  have hdis' : ⁅Z Rg (act Rg g⁻¹ a),Z Rg z⁆ ⊓ F = ⊥ := by
    have hh := congrArg (Subgroup.map f) hdis
    change (⁅Z Rg a,Z Rg z⁆ ⊓ F').map f = (⊥ : Subgroup (FreeAmalgam Rg)).map f at hh
    rw [Subgroup.map_inf _ _ f (MulAut.conj g).injective,←hF,hFF,
      map_commutator,hZz,Subgroup.map_bot] at hh
    simpa only [Z_act,inv_inv,f] using hh
  have hescape' : ¬ ⁅V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2),Z Rg z⁆ ≤
      Z Rg (act Rg g⁻¹ a) := by
    intro hh
    apply hescape
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp
    rw [map_commutator,hZz,Subgroup.map_inf _ _ f (MulAut.conj g).injective]
    simpa only [hverts 2,V_act,Q_act,Z_act,inv_inv,f] using hh
  exact ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,
    plane_radius_commutator_fixed_seed h e hz hk u hR hb4 hsmall p q
      hescape hescape' hsupp hdis hsupp' hdis'⟩

omit hk in
include h e hz in
/-- Whole-core application of the exact paired commutator fixed subgroup,
retaining the original projection and both moving covers. -/
theorem coreExhaustion_or_cubic_paired_commutator_fixed_seed :
    CoreExhaustion L R ∨
    ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      ∃ s, Adjacent Rg z s ∧
        Q Rg s ⊔ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) = stabilizer Rg z ∧
        ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
            (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
            (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
              (4-i) + (4-j)) ∧
            let b := act Rg g⁻¹ a
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let Y' := V Rg b ⊓ Q Rg (q.walk.getVert 2)
            let W := ⁅Y,Y'⁆
            let I := (Z Rg z ⊓ Q Rg a) ⊓ (Z Rg z ⊓ Q Rg b)
            let C := Z Rg z ⊓ centralizer (W : Set (FreeAmalgam Rg))
            C = Z Rg z ⊓ centralizer ((Y ⊔ Y' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
              C = Z Rg (p.walk.getVert 3) ⊓ Z Rg (q.walk.getVert 3) ∧
              C < I ∧ 8 ≤ C.relIndex (Z Rg z))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_paired_commutator_fixed_seed h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application with the original odd-index radical, odd
extension kernel quotient, full fixed subgroup and both moving covers. -/
theorem rankTwo_or_cubic_paired_commutator_fixed_seed :
    RankTwoAlternatives L R ∨
    ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      ∃ s, Adjacent Rg z s ∧
        Q Rg s ⊔ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) = stabilizer Rg z ∧
        ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
            (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
            (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
              (4-i) + (4-j)) ∧
            let b := act Rg g⁻¹ a
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let Y' := V Rg b ⊓ Q Rg (q.walk.getVert 2)
            let W := ⁅Y,Y'⁆
            let I := (Z Rg z ⊓ Q Rg a) ⊓ (Z Rg z ⊓ Q Rg b)
            let C := Z Rg z ⊓ centralizer (W : Set (FreeAmalgam Rg))
            C = Z Rg z ⊓ centralizer ((Y ⊔ Y' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
              C = Z Rg (p.walk.getVert 3) ⊓ Z Rg (q.walk.getVert 3) ∧
              C < I ∧ 8 ≤ C.relIndex (Z Rg z))) :=
  (coreExhaustion_or_cubic_paired_commutator_fixed_seed h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
