module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusTransfer

/-!
# Reciprocal critical planes on the displaced cubic paths

For the original critical path from a to z, let T = [Z_a,Z_z]. The
opposite-edge conjugator already chosen by `CubicPlaneRadiusTransfer`
produces the second path from b to z. Write T' = [Z_b,Z_z]. We prove
[Z_a,T'] = T and [Z_b,T] = T'. Thus T and T' generate a literal elementary
four-group. Each starting seed fixes exactly its own critical line in
that four-group, and their join has no nonidentity common fixed element.
A two-group action on a four-group has a nonidentity fixed element, so
already the join of the two starting seeds is not a two-group. Its unique
fixed vertex and its full normalizer are controlled by the same endpoint z.

The comparison retains the full endpoint center: the radius line need
only equal the critical line modulo that center. Escaping the full critical
kernel makes the transferred critical line noncentral under Z_a, so its
commutator is all of the order-two T. Plane-edge quadraticity makes the
square of the chosen conjugator centralize the entire endpoint seed.
Conjugating the first equality therefore gives the reciprocal equality.
The midpoint and whole last-edge radius kernels cannot normalize this
four-group: normalization would put their escaped commutators back in Z_a.

The actual whole-core and C.1.32 consumers preserve the cubic projection
kernel E, its odd E/Q, both moving covers of orders sixteen and thirty-two,
and the original proper odd-index radical. These are comparisons on the
same displaced paths, not a terminal contradiction. Small-image production,
the remaining distance and Borel cases, both core exhaustions and the final
unconditional reconstruction remain open.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the paired commutator comparisons toward (5.12), printed pp.924--927;
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
private theorem plane_edge_square_centralizes_seed
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z s : Vertex Rg} (hcol : color Rg z = false) (hzs : Adjacent Rg z s)
    (g : FreeAmalgam Rg) (hg : g ∈ Q Rg s) :
    g ^ 2 ∈ centralizer (Z Rg z : Set (FreeAmalgam Rg)) := by
  have hs : color Rg s = true := by
    have hh := adjacent_color_ne Rg hzs
    rw [hcol] at hh
    cases he : color Rg s <;> simp_all
  have hseed : Z Rg s ≤ centralizer (Q Rg s : Set (FreeAmalgam Rg)) := by
    intro x hx
    rw [Z,if_neg (by simp [hs])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z hcol
  intro x hx
  have hcs : ⁅g,x⁆ ∈ Z Rg s := by
    apply plane_edge_seed_commutator h e hz hk u hR hcol hzs
    rw [commutator_comm]
    exact commutator_mem_commutator hg hx
  have hcz := adjacent_Z_le Rg hcol hzs hcs
  have hcg : g * ⁅g,x⁆ * g⁻¹ = ⁅g,x⁆ :=
    mul_inv_eq_iff_eq_mul.mpr (hseed hcs g hg)
  have hpow := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hcz
  have he : ⁅g^2,x⁆ = 1 := by
    rw [pow_two,commutatorElement_mul_left_eq_conj_mul,hcg,←pow_two,hpow]
  exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm

private theorem map_conj_twice_of_square_centralizes {F : Type*} [Group F]
    (A : Subgroup F) (g : F) (hg : g^2 ∈ centralizer (A : Set F)) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom = A := by
  have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g^2)).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,pow_two]
    group
  rw [map_map,he]
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    have hh : g^2*x*(g^2)⁻¹ = x := mul_inv_eq_iff_eq_mul.mpr (hg x hx).symm
    change g^2*x*(g^2)⁻¹ ∈ A
    rw [hh]
    exact hx
  · intro x hx
    refine ⟨x,hx,?_⟩
    exact mul_inv_eq_iff_eq_mul.mpr (hg x hx).symm

include h in
private theorem critical_commutator_le_seed {a z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z) :
    ⁅Z Rg a,Z Rg z⁆ ≤ Z Rg a ⊓ Z Rg z := by
  refine le_inf ?_ ?_
  · apply le_normalizer_iff_commutator_le_left.mp
    exact (critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      p.critical).trans (Z_normalized Rg a)
  · apply le_normalizer_iff_commutator_le_right.mp
    exact (Z_le_stabilizer_of_dist_le a _ p.critical.1.le).trans (Z_normalized Rg z)

private theorem line_inf_eq_bot {F : Type*} [Group F] (T K : Subgroup F)
    (hT : Nat.card T = 2) (hn : ¬ T ≤ K) : T ⊓ K = ⊥ := by
  let : Finite T := Nat.finite_of_card_ne_zero (by omega)
  let : Finite (T ⊓ K : Subgroup F) :=
    Finite.of_injective (inclusion (show T ⊓ K ≤ T from inf_le_left)) (inclusion_injective _)
  have hcard := card_le_of_le (show T ⊓ K ≤ T from inf_le_left)
  have hne : Nat.card (T ⊓ K : Subgroup F) ≠ 2 := by
    intro he
    have heq : T ⊓ K = T := eq_of_le_of_card_ge inf_le_left (by omega)
    exact hn (heq ▸ inf_le_right)
  exact eq_bot_of_card_le _ (by omega)

private theorem reciprocal_lines_plane {F : Type*} [Group F]
    (Z A B T U : Subgroup F) [IsMulCommutative Z]
    (hTZ : T ≤ Z) (hUZ : U ≤ Z)
    (hT : Nat.card T = 2) (hU : Nat.card U = 2)
    (hTA : T ≤ centralizer (A : Set F)) (hUB : U ≤ centralizer (B : Set F))
    (hAU : ⁅A,U⁆ = T) (hBT : ⁅B,T⁆ = U) :
    T ⊓ U = ⊥ ∧ Nat.card (T ⊔ U : Subgroup F) = 4 ∧
      A ⊔ B ≤ normalizer ((T ⊔ U : Subgroup F) : Set F) ∧
      (T ⊔ U) ⊓ centralizer (A : Set F) = T ∧
      (T ⊔ U) ⊓ centralizer (B : Set F) = U ∧
      (T ⊔ U) ⊓ centralizer ((A ⊔ B : Subgroup F) : Set F) = ⊥ ∧
      ¬ IsPGroup 2 (A ⊔ B : Subgroup F) := by
  have hTne : T ≠ ⊥ := by intro he; rw [he,card_bot] at hT; omega
  have hUne : U ≠ ⊥ := by intro he; rw [he,card_bot] at hU; omega
  have hnUA : ¬ U ≤ centralizer (A : Set F) := by
    intro hh
    exact hTne (hAU.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp hh)))
  have hnTB : ¬ T ≤ centralizer (B : Set F) := by
    intro hh
    exact hUne (hBT.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp hh)))
  have hUT : U ≤ normalizer (T : Set F) :=
    ((hUZ.trans (le_centralizer (H := Z))).trans (centralizer_le hTZ)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hTU : T ≤ normalizer (U : Set F) :=
    ((hTZ.trans (le_centralizer (H := Z))).trans (centralizer_le hUZ)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hdis : T ⊓ U = ⊥ := line_inf_eq_bot T U hT (fun hh => hnTB (hh.trans hUB))
  have hc : Nat.card (T ⊔ U : Subgroup F) = 4 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint T U hUT (disjoint_iff.mpr hdis),hT,hU]
  have hFA : (T ⊔ U) ⊓ centralizer (A : Set F) = T := by
    rw [inf_centralizer_sup_of_centralizing T U A hTU hTA,
      line_inf_eq_bot U _ hU hnUA,sup_bot_eq]
  have hFB : (T ⊔ U) ⊓ centralizer (B : Set F) = U := by
    rw [sup_comm,inf_centralizer_sup_of_centralizing U T B hUT hUB,
      line_inf_eq_bot T _ hT hnTB,sup_bot_eq]
  have hN : A ⊔ B ≤ normalizer ((T ⊔ U : Subgroup F) : Set F) := by
    apply sup_le
    · apply le_normalizer_iff_commutator_le_right.mpr
      rw [commutator_comm]
      apply commutator_sup_le_of_relative_normal (T ⊔ U) T U A (T ⊔ U)
        (T ⊔ U).le_normalizer le_sup_left le_sup_right
      · exact (commutator_eq_bot_iff_le_centralizer.mpr hTA).le.trans bot_le
      · rw [commutator_comm,hAU]; exact le_sup_left
    · apply le_normalizer_iff_commutator_le_right.mpr
      rw [commutator_comm]
      apply commutator_sup_le_of_relative_normal (T ⊔ U) T U B (T ⊔ U)
        (T ⊔ U).le_normalizer le_sup_left le_sup_right
      · rw [commutator_comm,hBT]; exact le_sup_right
      · exact (commutator_eq_bot_iff_le_centralizer.mpr hUB).le.trans bot_le
  have hF : (T ⊔ U) ⊓ centralizer ((A ⊔ B : Subgroup F) : Set F) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have ha : x ∈ T := hFA ▸ ⟨hx.1,fun y hy => hx.2 y (mem_sup_left hy)⟩
    have hb : x ∈ U := hFB ▸ ⟨hx.1,fun y hy => hx.2 y (mem_sup_right hy)⟩
    exact hdis ▸ ⟨ha,hb⟩
  refine ⟨hdis,hc,hN,hFA,hFB,hF,?_⟩
  intro hp
  let J := T ⊔ U
  let P := A ⊔ B
  let : Finite J := Nat.finite_of_card_ne_zero (by change Nat.card (T ⊔ U : Subgroup F) ≠ 0; omega)
  let : MulAction P J := {
    smul := fun g x => ⟨(g : F)*(x : F)*(g : F)⁻¹,
      (mem_normalizer_iff.mp (hN g.property) (x : F)).mp x.property⟩
    one_smul := by
      intro x
      apply Subtype.ext
      change (1 : F) * (x : F) * (1 : F)⁻¹ = (x : F)
      simp
    mul_smul := by
      intro g k x
      apply Subtype.ext
      change ((g : F)*(k : F))*(x : F)*((g : F)*(k : F))⁻¹ =
        (g : F)*((k : F)*(x : F)*(k : F)⁻¹)*(g : F)⁻¹
      group }
  obtain ⟨x,hx,hne⟩ := hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := J) (a := 1) (by change 2 ∣ Nat.card (T ⊔ U : Subgroup F); rw [hc]; decide)
    (by
      intro g
      apply Subtype.ext
      change (g : F) * 1 * (g : F)⁻¹ = 1
      simp)
  have hxC : (x : F) ∈ centralizer (P : Set F) := by
    intro g hg
    have he := congrArg Subtype.val (hx (⟨g,hg⟩ : P))
    exact mul_inv_eq_iff_eq_mul.mp he
  have hx1 : (x : F) = 1 := mem_bot.mp (hF ▸ ⟨x.property,hxC⟩)
  exact hne (Subtype.ext hx1.symm)

include h e hz hk in
/-- An opposite-edge transfer acts reciprocally on the two genuine critical
commutator lines. The radius line is compared modulo the full endpoint
center; it is never identified with the critical line itself. -/
theorem plane_transferred_critical_plane
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z s : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (Y : Subgroup (FreeAmalgam Rg)) (hYV : Y ≤ V Rg a)
    (hYt : Y ≤ Q Rg (p.walk.getVert (p.walk.length-1)))
    (hAY : Z Rg a ≤ Y) (hnot : ¬ ⁅Y,Z Rg z⁆ ≤ Z Rg a)
    (hzs : Adjacent Rg z s) (g : FreeAmalgam Rg) (hg : g ∈ Q Rg s)
    (hescape : ¬ (⁅Y,Z Rg z ⊓ Q Rg a⁆ : Subgroup (FreeAmalgam Rg)).map
      (MulAut.conj g).toMonoidHom ≤ Q Rg a)
    (hfullEscape : ¬ ⁅Y,(⁅Y,Z Rg z ⊓ Q Rg a⁆ : Subgroup (FreeAmalgam Rg)).map
      (MulAut.conj g).toMonoidHom⁆ ≤ Z Rg a) :
    let b := act Rg g⁻¹ a
    let T := ⁅Z Rg a,Z Rg z⁆
    let T' := ⁅Z Rg b,Z Rg z⁆
    ⁅Z Rg a,T'⁆ = T ∧ ⁅Z Rg b,T⁆ = T' ∧
      T ⊓ T' = ⊥ ∧ Nat.card (T ⊔ T' : Subgroup (FreeAmalgam Rg)) = 4 ∧
      IsElementaryAbelian 2 (T ⊔ T' : Subgroup (FreeAmalgam Rg)) ∧
      Z Rg a ⊔ Z Rg b ≤ normalizer ((T ⊔ T' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      (T ⊔ T') ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) = T ∧
      (T ⊔ T') ⊓ centralizer (Z Rg b : Set (FreeAmalgam Rg)) = T' ∧
      (T ⊔ T') ⊓ centralizer ((Z Rg a ⊔ Z Rg b : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) = ⊥ ∧
      ¬ IsPGroup 2 (Z Rg a ⊔ Z Rg b : Subgroup (FreeAmalgam Rg)) ∧
      ¬ Y ≤ normalizer ((T ⊔ T' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
  let b := act Rg g⁻¹ a
  let T := ⁅Z Rg a,Z Rg z⁆
  let T' := ⁅Z Rg b,Z Rg z⁆
  let H := ⁅Y,Z Rg z ⊓ Q Rg a⁆
  let C := stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
  let f := (MulAut.conj g).toMonoidHom
  have hgG : g ∈ stabilizer Rg z := hg.2 _ (adjacent_symm Rg hzs)
  have hfix : act Rg g⁻¹ z = z := (stabilizer Rg z).inv_mem hgG
  have hZmap : (Z Rg z).map f = Z Rg z :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized Rg z hgG)
  have hAmap : (Z Rg a).map f = Z Rg b := by rw [Z_act,inv_inv]
  have hTmap : T.map f = T' := by rw [map_commutator,hZmap,hAmap]
  have hTle := critical_commutator_le_seed h p
  have hTZ : T ≤ Z Rg z := hTle.trans inf_le_right
  have hT'Z : T' ≤ Z Rg z := hTmap ▸ (map_mono hTZ).trans_eq hZmap
  have hAZ : Z Rg a ≤ stabilizer Rg z := Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hCZ : C ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    inf_le_right.trans (centralizer_le hAZ)
  have hCmap : C.map f = C := by
    apply mem_normalizer_iff_map_conj_eq.mp
    apply Subgroup.centralizer_le_normalizer
    exact (le_centralizer_iff.mp (show C ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) from
      inf_le_right)) hgG
  obtain ⟨_,_,hHA,_,_,halign⟩ := plane_radius_kernel_alignment h e hz hk u hR p hp Y
    hYV hYt hAY hnot
  have halign' : H.map f ⊔ C = T' ⊔ C := by
    have hh : (H ⊔ C).map f = (T ⊔ C).map f := congrArg (Subgroup.map f) halign
    rwa [Subgroup.map_sup,Subgroup.map_sup,hCmap,hTmap] at hh
  have hzt : Adjacent Rg z (p.walk.getVert (p.walk.length-1)) := by
    have hl : 0 < p.walk.length := p.length_eq_b ▸ sourceDistance_pos h
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hYG : Y ≤ stabilizer Rg z := hYt.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hzt))
  have hHle : H ≤ Z Rg z := (commutator_mono le_rfl inf_le_left).trans
    (le_normalizer_iff_commutator_le_right.mp (hYG.trans (Z_normalized Rg z)))
  have hH'Z : H.map f ≤ Z Rg z := (map_mono hHle).trans_eq hZmap
  have hT'not : ¬ T' ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) := by
    intro hc
    have hh : H.map f ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      (show H.map f ≤ T' ⊔ C from halign' ▸ le_sup_left).trans (sup_le hc hCZ)
    apply hescape
    have hr := critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      a p.start_color (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      z p.end_color p.critical
    have hf := critical_seed_centralizer_intersection h e
      (CriticalPath.ofPair p.end_color hr)
    exact (show H.map f ≤ Z Rg z ⊓ Q Rg a from hf ▸ le_inf hH'Z hh).trans inf_le_right
  have hcT : Nat.card T = 2 := small_critical_commutator_card h e hz hk p hp
  have hcT' : Nat.card T' = 2 := by rw [←hTmap,card_map_of_injective (MulAut.conj g).injective,hcT]
  have hcross : ⁅Z Rg a,T'⁆ = T := by
    have hle : ⁅Z Rg a,T'⁆ ≤ T := commutator_mono le_rfl hT'Z
    let : Finite T := Nat.finite_of_card_ne_zero (by omega)
    let : Finite (⁅Z Rg a,T'⁆ : Subgroup (FreeAmalgam Rg)) :=
      Finite.of_injective (inclusion hle) (inclusion_injective _)
    have hn : ⁅Z Rg a,T'⁆ ≠ ⊥ := by
      intro he
      exact hT'not (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
    have hlo := (Subgroup.one_lt_card_iff_ne_bot _).mpr hn
    exact eq_of_le_of_card_ge hle (by omega)
  have hTT : T'.map f = T := by
    rw [←hTmap]
    exact map_conj_twice_of_square_centralizes T g
      (centralizer_le hTZ (plane_edge_square_centralizes_seed h e hz hk u hR p.end_color hzs g hg))
  have hcross' : ⁅Z Rg b,T⁆ = T' := by
    have hh := congrArg (Subgroup.map f) hcross
    rwa [map_commutator,hAmap,hTT,hTmap] at hh
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) b
    (by rw [action_preserves_color]; exact p.start_color)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have hTA : T ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    (hTle.trans inf_le_left).trans (le_centralizer (H := Z Rg a))
  have hT'B : T' ≤ centralizer (Z Rg b : Set (FreeAmalgam Rg)) :=
    (show T' ≤ Z Rg b from hTmap ▸ (map_mono (hTle.trans inf_le_left)).trans_eq hAmap).trans
      (le_centralizer (H := Z Rg b))
  obtain ⟨hd,hcard,hN,hFA,hFB,hF,hn⟩ := reciprocal_lines_plane (Z Rg z) (Z Rg a) (Z Rg b)
    T T' hTZ hT'Z hcT hcT' hTA hT'B hcross hcross'
  refine ⟨hcross,hcross',hd,hcard,IsElementaryAbelian.of_le (sup_le hTZ hT'Z),hN,hFA,hFB,hF,hn,?_⟩
  intro hYN
  let J := T ⊔ T'
  have hJG : J ≤ stabilizer Rg z := (sup_le hTZ hT'Z).trans (Z_le_stabilizer Rg z)
  have hCJ : C ≤ normalizer (J : Set (FreeAmalgam Rg)) :=
    (show C ≤ centralizer (J : Set (FreeAmalgam Rg)) from
      inf_le_right.trans (centralizer_le hJG)).trans (Subgroup.centralizer_le_normalizer _)
  have hCY : C ≤ centralizer (Y : Set (FreeAmalgam Rg)) :=
    inf_le_right.trans (centralizer_le hYG)
  have hcomm : ⁅Y,H.map f⁆ ≤ J := by
    rw [commutator_comm]
    apply (commutator_mono (show H.map f ≤ T' ⊔ C from halign' ▸ le_sup_left) le_rfl).trans
    apply commutator_sup_le_of_relative_normal (J ⊔ C) T' C Y J
      (sup_le J.le_normalizer hCJ) (le_sup_right.trans le_sup_left) le_sup_right
    · exact (commutator_mono le_sup_right le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hYN)
    · exact (commutator_eq_bot_iff_le_centralizer.mpr hCY).le.trans bot_le
  have hYA : Y ≤ Q Rg a := hYV.trans ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) a p.start_color)
  have hH'n : H.map f ≤ normalizer (Q Rg a : Set (FreeAmalgam Rg)) :=
    (hH'Z.trans (critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      p.critical)).trans (Q_normalized Rg a)
  have hcommQ : ⁅Y,H.map f⁆ ≤ Q Rg a :=
    (commutator_mono hYA le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hH'n)
  have hQA : Q Rg a ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color))
  apply hfullEscape
  exact ((le_inf hcomm (hcommQ.trans hQA)).trans hFA.le).trans (hTle.trans inf_le_left)

include h e hz hk in
/-- On the same displaced critical paths, the starting seeds act on a
literal four-group with reciprocal nonzero critical commutators. Their join
is not a two-group, has exactly the original endpoint as a fixed vertex,
and has its full normalizer inside that endpoint stabilizer. -/
theorem plane_small_four_paired_critical_plane
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
            let b := act Rg g⁻¹ a
            let T := ⁅Z Rg a,Z Rg z⁆
            let T' := ⁅Z Rg b,Z Rg z⁆
            ⁅Z Rg a,T'⁆ = T ∧ ⁅Z Rg b,T⁆ = T' ∧
              T ⊓ T' = ⊥ ∧ Nat.card (T ⊔ T' : Subgroup (FreeAmalgam Rg)) = 4 ∧
              IsElementaryAbelian 2 (T ⊔ T' : Subgroup (FreeAmalgam Rg)) ∧
              Z Rg a ⊔ Z Rg b ≤ normalizer ((T ⊔ T' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
              (T ⊔ T') ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) = T ∧
              (T ⊔ T') ⊓ centralizer (Z Rg b : Set (FreeAmalgam Rg)) = T' ∧
              (T ⊔ T') ⊓ centralizer ((Z Rg a ⊔ Z Rg b : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) = ⊥ ∧
              ¬ IsPGroup 2 (Z Rg a ⊔ Z Rg b : Subgroup (FreeAmalgam Rg)) ∧
              ¬ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) ≤
                normalizer ((T ⊔ T' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
              ¬ (V Rg a ⊓ Q Rg (p.walk.getVert 3)) ≤
                normalizer ((T ⊔ T' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
              (∀ v, Z Rg a ⊔ Z Rg b ≤ stabilizer Rg v ↔ v = z) ∧
              normalizer ((Z Rg a ⊔ Z Rg b : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ≤ stabilizer Rg z ∧
              (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
                (4-i) + (4-j)) := by
  obtain ⟨a,z,p,_,s,hzs,hgen,_,_,g,hg,hfix,hescape,_,hesc,_,q,hverts,_,_,_,hgeom⟩ :=
    plane_small_four_radius_line_transfer h e hz hk u hR hb4 hsmall
  let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg (p.walk.getVert 3) = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg (p.walk.getVert 3) <;> simp_all
  have hYt : Y ≤ Q Rg (p.walk.getVert (p.walk.length-1)) := by
    rw [hl]
    exact inf_le_right.trans (Q_le_adjacent_h Rg ht hct)
  have hAY : Z Rg a ≤ Y := by
    refine le_inf (Z_le_VBall Rg _ 2) ?_
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (by omega)]
    exact distance_gt_two h e hz hk
  have hXZ := (plane_small_four_omega_generated h e hz hk u hR hb4 hsmall z p.end_color).2
  rw [hXZ] at hescape hesc
  have hYG : Y ≤ stabilizer Rg z := by
    have hh : Y ≤ Q Rg (p.walk.getVert 3) := by simpa only [hl,Nat.reduceSub] using hYt
    exact hh.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hzt))
  have hHZ : ⁅Y,Z Rg z ⊓ Q Rg a⁆ ≤ Z Rg z :=
    (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp (hYG.trans (Z_normalized Rg z)))
  have hH'Z : (⁅Y,Z Rg z ⊓ Q Rg a⁆ : Subgroup (FreeAmalgam Rg)).map
      (MulAut.conj g).toMonoidHom ≤ Z Rg z :=
    (map_mono hHZ).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (Z_normalized Rg z (hg.2 _ (adjacent_symm Rg hzs))))
  have hnot : ¬ ⁅Y,Z Rg z⁆ ≤ Z Rg a :=
    fun hh => hesc ((commutator_mono le_rfl hH'Z).trans hh)
  obtain ⟨hcross,hcross',hd,hcard,hel,hN,hFA,hFB,hF,hn,hYN⟩ :=
    plane_transferred_critical_plane h e hz hk u hR p (hsmall _ _ p) Y inf_le_left hYt hAY
      hnot hzs g hg hescape hesc
  have hgeometry := radius_pair_path_geometry_of_not_two h p.end_color p.walk q.walk
    p.shortest q.shortest (Z Rg a) (Z Rg (act Rg g⁻¹ a))
    (Z_le_stabilizer Rg a) (Z_le_stabilizer_of_dist_le a _ p.critical.1.le)
    (Z_le_stabilizer Rg _) (Z_le_stabilizer_of_dist_le _ _ q.critical.1.le) hn
  exact ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hcross,hcross',hd,hcard,hel,hN,hFA,hFB,hF,hn,
    hYN,(fun hh => hYN ((le_inf inf_le_left (show Y ≤ Q Rg (p.walk.getVert 3) from
      by simpa only [hl,Nat.reduceSub] using hYt)).trans hh)),hgeometry.1,hgeometry.2.1,hgeom⟩

omit hk in
include h e hz in
/-- Whole-core application of the reciprocal critical plane and full-radius
normalizer obstruction, with the original cubic kernel and both covers. -/
theorem coreExhaustion_or_cubic_paired_critical_plane :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
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
                    let b := act Rg g⁻¹ a
                    let T := ⁅Z Rg a,Z Rg z⁆
                    let T' := ⁅Z Rg b,Z Rg z⁆
                    ⁅Z Rg a,T'⁆ = T ∧ ⁅Z Rg b,T⁆ = T' ∧
                      T ⊓ T' = ⊥ ∧ Nat.card (T ⊔ T' : Subgroup (FreeAmalgam Rg)) = 4 ∧
                      IsElementaryAbelian 2 (T ⊔ T' : Subgroup (FreeAmalgam Rg)) ∧
                      Z Rg a ⊔ Z Rg b ≤ normalizer ((T ⊔ T' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
                      (T ⊔ T') ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) = T ∧
                      (T ⊔ T') ⊓ centralizer (Z Rg b : Set (FreeAmalgam Rg)) = T' ∧
                      (T ⊔ T') ⊓ centralizer ((Z Rg a ⊔ Z Rg b : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) = ⊥ ∧
                      ¬ IsPGroup 2 (Z Rg a ⊔ Z Rg b : Subgroup (FreeAmalgam Rg)) ∧
                      ¬ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) ≤
                        normalizer ((T ⊔ T' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
                      ¬ (V Rg a ⊓ Q Rg (p.walk.getVert 3)) ≤
                        normalizer ((T ⊔ T' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
                      (∀ v, Z Rg a ⊔ Z Rg b ≤ stabilizer Rg v ↔ v = z) ∧
                      normalizer ((Z Rg a ⊔ Z Rg b : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ≤ stabilizer Rg z ∧
                      (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
                        (4-i) + (4-j)))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_paired_critical_plane h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application. The original Borel, distance and image
branches and both full-core exhaustions still require their source proofs. -/
theorem rankTwo_or_cubic_paired_critical_plane :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
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
                    let b := act Rg g⁻¹ a
                    let T := ⁅Z Rg a,Z Rg z⁆
                    let T' := ⁅Z Rg b,Z Rg z⁆
                    ⁅Z Rg a,T'⁆ = T ∧ ⁅Z Rg b,T⁆ = T' ∧
                      T ⊓ T' = ⊥ ∧ Nat.card (T ⊔ T' : Subgroup (FreeAmalgam Rg)) = 4 ∧
                      IsElementaryAbelian 2 (T ⊔ T' : Subgroup (FreeAmalgam Rg)) ∧
                      Z Rg a ⊔ Z Rg b ≤ normalizer ((T ⊔ T' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
                      (T ⊔ T') ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) = T ∧
                      (T ⊔ T') ⊓ centralizer (Z Rg b : Set (FreeAmalgam Rg)) = T' ∧
                      (T ⊔ T') ⊓ centralizer ((Z Rg a ⊔ Z Rg b : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) = ⊥ ∧
                      ¬ IsPGroup 2 (Z Rg a ⊔ Z Rg b : Subgroup (FreeAmalgam Rg)) ∧
                      ¬ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) ≤
                        normalizer ((T ⊔ T' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
                      ¬ (V Rg a ⊓ Q Rg (p.walk.getVert 3)) ≤
                        normalizer ((T ⊔ T' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
                      (∀ v, Z Rg a ⊔ Z Rg b ≤ stabilizer Rg v ↔ v = z) ∧
                      normalizer ((Z Rg a ⊔ Z Rg b : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ≤ stabilizer Rg z ∧
                      (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
                        (4-i) + (4-j)))) :=
  (coreExhaustion_or_cubic_paired_critical_plane h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
