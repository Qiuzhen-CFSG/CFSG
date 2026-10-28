module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ThompsonGeneration
public import Theory.GroupTheory.NormalModuleCore
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CoreCentrality
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.ElementaryThompsonCentralizerTransport

/-!
# Local Thompson generation at the original nonsingular point

The fixed space C_V(L) is fixed pointwise by LT. Nonsingular vectors are
conjugate modulo that fixed space, so their centralizers inside LT, and
their moved subgroups, are conjugate by the same element of L.

Suppose J(T_v) centralizes V_v. A maximal elementary subgroup A of T_v
then centralizes every weight-two point u in V_v. Conjugate C_LT(u) to
C_LT(v) and apply Sylow conjugacy: A centralizes V_u as well. The proved
12.6.10 says the L_u generate L; hence their moved subgroups generate V.
Thus J(T_v) centralizes V and lies in the actual Q. Conversely, movement
outside Q has nontrivial normal image in A₆; simplicity and perfectness
lift this to L_v=[L_v,J(T_v)]. This proves 12.6.9 and the alternatives of
12.6.6 without assuming a local generation or offender-classification input.

The earlier T-invariance premise retains producer qt-d-1222-source and
final discharge owner qt-d-12634-source. All conjugation maps and the
original projection V→V/C_V(L) are preserved. The remaining module
contradiction of 12.6.11 and the later source branches are not asserted here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
Lemmas 12.6.6 and 12.6.9, printed pp.824--825.
-/

public section
open Subgroup Theory.GroupTheory Representation BinaryPermutation BinaryPermutation.EightNonsingular
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original fixed space is fixed pointwise by LT. -/
theorem OrthogonalMarking.join_centralizes_fixed
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    LT T L ≤ centralizer (ZV L V : Set G) := by
  intro g hg z hz
  obtain ⟨l,hl⟩ := D.normalizer_orbit_control chosen g
    ((sup_le L.le_normalizer chosen.sylow_normalizes_component) hg)
    ((sup_le chosen.normalizes hTV) hg) ⟨z,hz.1⟩
  have he : g*z*g⁻¹ = z := by
    rw [hl,mem_centralizer_iff.mp hz.2 l l.property,mul_inv_cancel_right]
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

omit [IsElementaryAbelian 2 V] in
/-- The full original LT action kernel is Q. -/
theorem SourceHypothesis.join_centralizer_eq_core
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    LT T L ⊓ centralizer (V : Set G) = Q T L :=
  ambient_centralizer_eq_core_of_normal_supplement L V (T : Subgroup G)
    H.chosen.sylow_normalizes_component (H.chosen.le_component.trans le_sup_left)
    (sup_le H.chosen.normalizes hTV) T.isPGroup' H.centralizer_eq_core H.chosen.core_centralizes

private theorem same_projection_localCentralizer
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (v w : V)
    (hp : (Submodule.Quotient.mk (Additive.ofMul v) : Vhat L V chosen.normalizes) =
      Submodule.Quotient.mk (Additive.ofMul w)) :
    LT T L ⊓ Gv (v : G) = LT T L ⊓ Gv (w : G) := by
  have hd : (v : G)*(w : G)⁻¹ ∈ ZV L V := by
    apply (mem_fixedSeed_iff L V chosen.normalizes (Additive.ofMul (v*w⁻¹))).mp
    apply (Submodule.Quotient.mk_eq_zero _).mp
    rw [ofMul_mul,ofMul_inv,←sub_eq_add_neg]
    change (Submodule.Quotient.mk (Additive.ofMul v - Additive.ofMul w) : Vhat L V chosen.normalizes) = 0
    rw [Submodule.Quotient.mk_sub,hp,sub_self]
  ext g
  change (g ∈ LT T L ∧ g ∈ centralizer ({(v : G)} : Set G)) ↔
    (g ∈ LT T L ∧ g ∈ centralizer ({(w : G)} : Set G))
  simp only [mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hg,hv⟩
    refine ⟨hg,?_⟩
    have hc := D.join_centralizes_fixed chosen hTV hg _ hd
    have hh : g * (w : G)⁻¹ = (w : G)⁻¹ * g := by
      apply mul_left_cancel (a := (v : G))
      simpa only [←mul_assoc,hv] using hc.symm
    exact (Commute.inv_right_iff.mp hh).eq
  · rintro ⟨hg,hw⟩
    refine ⟨hg,?_⟩
    have hc := D.join_centralizes_fixed chosen hTV hg _ hd
    have hh := (Commute.inv_right (show Commute g (w : G) from hw)).eq
    apply mul_right_cancel (b := (w : G)⁻¹)
    simpa only [mul_assoc,hh] using hc.symm

omit [Finite G] in
private theorem same_projection_Lv
    (chosen : Section02.ChosenModule T L V) (v w : V)
    (hp : (Submodule.Quotient.mk (Additive.ofMul v) : Vhat L V chosen.normalizes) =
      Submodule.Quotient.mk (Additive.ofMul w)) : Lv L (v : G) = Lv L (w : G) := by
  have hd : (v : G)*(w : G)⁻¹ ∈ ZV L V := by
    apply (mem_fixedSeed_iff L V chosen.normalizes (Additive.ofMul (v*w⁻¹))).mp
    apply (Submodule.Quotient.mk_eq_zero _).mp
    rw [ofMul_mul,ofMul_inv,←sub_eq_add_neg]
    change (Submodule.Quotient.mk (Additive.ofMul v - Additive.ofMul w) : Vhat L V chosen.normalizes) = 0
    rw [Submodule.Quotient.mk_sub,hp,sub_self]
  have he : CLv L (v : G) = CLv L (w : G) := by
    ext l
    change (l ∈ L ∧ l ∈ centralizer ({(v : G)} : Set G)) ↔
      (l ∈ L ∧ l ∈ centralizer ({(w : G)} : Set G))
    simp only [mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hl,hv⟩
      refine ⟨hl,?_⟩
      have hc := mem_centralizer_iff.mp hd.2 l hl
      have hh : l * (w : G)⁻¹ = (w : G)⁻¹ * l := by
        apply mul_left_cancel (a := (v : G))
        simpa only [←mul_assoc,hv] using hc
      exact (Commute.inv_right_iff.mp hh).eq
    · rintro ⟨hl,hw⟩
      refine ⟨hl,?_⟩
      have hc := mem_centralizer_iff.mp hd.2 l hl
      have hh := (Commute.inv_right (show Commute l (w : G) from hw)).eq
      apply mul_right_cancel (b := (w : G)⁻¹)
      simpa only [mul_assoc,hh] using hc
  exact congrArg (fun B : Subgroup G => (pResidual 2 B).map B.subtype) he

private theorem pair_weight' (i j : Fin 8) (hij : i ≠ j) :
    wordWeight (pair i j).val = 2 := by
  classical
  have hs : (Finset.univ.filter fun k => (pair i j).val k ≠ 0) = {i,j} := by
    ext k
    by_cases hki : k = i
    · subst k; simp [pair,hij,Finset.mem_filter,Pi.single_apply]
    by_cases hkj : k = j
    · subst k; simp [pair,hij.symm,Finset.mem_filter,Pi.single_apply]
    simp [pair,Pi.single_apply,hki,hkj]
  change (Finset.univ.filter _).card = 2
  rw [hs]
  simp [hij]

omit [Finite G] in
private theorem nonsingular_conjugate_projection
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (v u : V) (hv : D.Nonsingular v) (hu : D.Nonsingular u) :
    ∃ l : L, (Submodule.Quotient.mk
      (Additive.ofMul (conjugation L V chosen.normalizes l v)) : Vhat L V chosen.normalizes) =
        Submodule.Quotient.mk (Additive.ofMul u) := by
  obtain ⟨i,j,hij,hp⟩ := nonsingular_pair _ hv
  obtain ⟨a,b,hab,hq⟩ := nonsingular_pair _ hu
  have hm : pair a b ∈ (Set.range fun g : alternatingGroup (Fin 8) =>
      alternatingCoreRepresentation (Fin 8) g (pair i j)) := by
    rw [even_core_orbit_eq_weight (by decide)]
    exact (pair_weight' a b hab).trans (pair_weight' i j hij).symm
  obtain ⟨g,hg⟩ := hm
  obtain ⟨l,rfl⟩ := D.actorMap_surjective g
  refine ⟨l,D.coordinates.injective ?_⟩
  change D.coordinates ((fixedSeed L V chosen.normalizes).quotientRepresentation l
    (Submodule.Quotient.mk (Additive.ofMul v))) = _
  rw [D.equivariant,←hp,←hq]
  exact (coreToNatural_equivariant (D.actorMap l).val (pair i j)).symm.trans (congrArg _ hg)

/-- Nonsingular local centralizers and their moved modules are conjugate in L,
even when the two vectors differ by the original fixed space. -/
theorem OrthogonalMarking.nonsingular_local_pair_conjugate
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (v u : V) (hv : D.Nonsingular v) (hu : D.Nonsingular u) :
    ∃ l : L,
      (LT T L ⊓ Gv (v : G)).map (MulAut.conj (l : G)).toMonoidHom = LT T L ⊓ Gv (u : G) ∧
      (Vv L V (v : G)).map (MulAut.conj (l : G)).toMonoidHom = Vv L V (u : G) := by
  obtain ⟨l,hl⟩ := nonsingular_conjugate_projection chosen D v u hv hu
  let w := conjugation L V chosen.normalizes l v
  have hLT : (LT T L).map (MulAut.conj (l : G)).toMonoidHom = LT T L :=
    mem_normalizer_iff_map_conj_eq.mp ((LT T L).le_normalizer (mem_sup_left l.property))
  have hL : L.map (MulAut.conj (l : G)).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer l.property)
  have hV : V.map (MulAut.conj (l : G)).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (chosen.normalizes l.property)
  have hpoint : (Gv (v : G)).map (MulAut.conj (l : G)).toMonoidHom = Gv (w : G) :=
    map_pointCentralizer (MulAut.conj (l : G)) (v : G)
  have hCL : (CLv L (v : G)).map (MulAut.conj (l : G)).toMonoidHom = CLv L (w : G) := by
    rw [CLv,map_inf _ _ _ (MulAut.conj (l : G)).injective,hL,hpoint]
    rfl
  refine ⟨l,?_,?_⟩
  · rw [map_inf _ _ _ (MulAut.conj (l : G)).injective,hLT,hpoint]
    exact same_projection_localCentralizer chosen D hTV w u hl
  · rw [Vv,map_commutator,hV,Lv,map_embedded_pResidual,hCL]
    change ⁅V,Lv L (w : G)⁆ = ⁅V,Lv L (u : G)⁆
    rw [same_projection_Lv chosen w u hl]
end CFSG.Quasithin.Chapter12.Section06


namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory Stellmacher Representation BinaryPermutation BinaryPermutation.EightNonsingular
open scoped IsMulCommutative commutatorElement
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] [IsElementaryAbelian 2 V] in
private theorem moved_span_centralized (chosen : Section02.ChosenModule T L V)
    {ι : Sort*} (F : ι → Subgroup G) (hFL : ∀ i, F i ≤ L) (hgen : (⨆ i, F i) = L)
    (A : Subgroup G) (hc : ∀ i, A ≤ centralizer ((⁅V,F i⁆ : Subgroup G) : Set G)) :
    A ≤ centralizer (V : Set G) := by
  let C := V ⊓ centralizer (A : Set G)
  have hcomm (i) : ⁅V,F i⁆ ≤ C :=
    le_inf (le_normalizer_iff_commutator_le_left.mp ((hFL i).trans chosen.normalizes))
      (le_centralizer_iff.mp (hc i))
  have hn : L ≤ normalizer (C : Set G) := by
    rw [←hgen]
    apply iSup_le
    intro i
    apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono inf_le_left le_rfl).trans (hcomm i)
  have hh := commutator_iSup_le_of_relative_normal L V C F hn hFL
    (fun i => (commutator_comm (F i) V).le.trans (hcomm i))
  rw [hgen,commutator_comm L V,←chosen.eq_commutator] at hh
  exact le_centralizer_iff.mpr (hh.trans inf_le_right)

/-- Local Thompson centralization propagates to the original chosen module. -/
theorem SourceHypothesis.local_thompson_centralizes_of_moved
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ centralizer (Vv L V (v : G) : Set G)) :
    elementaryAbelianMaxJ (Tv T (v : G)) ≤ centralizer (V : Set G) := by
  let B := LT T L ⊓ Gv (v : G)
  let W := Vv L V (v : G)
  have hn : B ≤ normalizer (W : Set G) := normalizes_Vv_of_normalizes B _
    (inf_le_left.trans (sup_le H.chosen.normalizes hTV))
    ((inf_le_inf (sup_le L.le_normalizer H.chosen.sylow_normalizes_component) le_rfl).trans
      (Mv_le_normalizer_Lv L (v : G)))
  obtain ⟨P,hP⟩ := hTv.restrict
    (show Tv T (v : G) ≤ B from inf_le_inf le_sup_right le_rfl)
    (show B ≤ Mv L (v : G) from
      inf_le_inf (sup_le L.le_normalizer H.chosen.sylow_normalizes_component) le_rfl)
  let := Vv_elementary H.chosen.normalizes (v : G)
  obtain ⟨i,j,hij,hp,E,hE,hproj,hgen⟩ := H.nonsingular_weightTwo_generation D v hv
  apply sSup_le
  intro A hA
  have hAW : A ≤ centralizer (W : Set G) := (le_sSup hA).trans hJ
  let F : (weightTwoPoints W E) → Subgroup G := fun u => Lv L u.val
  have hF : (⨆ u, F u) = L := by
    simpa only [F,iSup_subtype,weightTwoResiduals] using hgen
  apply moved_span_centralized H.chosen F (fun u => Lv_le_L _ _) hF A
  intro u
  have huW : u.val ∈ W := by
    obtain ⟨w,_,he⟩ := u.property
    exact he ▸ (E w).toMul.property
  let uV : V := ⟨u.val,Vv_le_V H.chosen.normalizes _ huW⟩
  have hu : D.Nonsingular uV := by
    obtain ⟨w,hw,he⟩ := u.property
    have hs : ∃ a b : Fin 6, a ≠ b ∧ sixPair a b = w := by
      have h : ∀ w : Full (Fin 6), hammingNorm w = 2 →
          ∃ a b : Fin 6, a ≠ b ∧ (sixPair a b).val = w := by decide +kernel
      obtain ⟨a,b,hab,hwe⟩ := h w.val hw
      exact ⟨a,b,hab,Subtype.ext hwe⟩
    obtain ⟨a,b,hab,rfl⟩ := hs
    have huE : uV = ⟨(E (sixPair a b)).toMul,Vv_le_V H.chosen.normalizes _ (E (sixPair a b)).toMul.property⟩ :=
      Subtype.ext he.symm
    rw [huE]
    change TerminalOrthogonal.Eight.form (D.coordinates (Submodule.Quotient.mk _)) ≠ 0
    rw [hproj,extendSix_pair]
    have hab' : complementLetters i j hij a ≠ complementLetters i j hij b :=
      fun h => hab ((complementLetters i j hij).injective h)
    rw [(EightGeometry.nonsingular_core_iff _).mpr (Or.inl (pair_weight' _ _ hab'))]
    exact one_ne_zero
  obtain ⟨l,hBl,hWl⟩ := D.nonsingular_local_pair_conjugate H.chosen hTV v uV hv hu
  let e := MulAut.conj (l : G)
  let A' := A.map e.symm.toMonoidHom
  have hback : A'.map e.toMonoidHom = A := by
    rw [map_map]
    have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by
      ext x
      exact e.apply_symm_apply x
    rw [he,map_id]
  have hAu : A ≤ LT T L ⊓ Gv (uV : G) := by
    intro a ha
    refine ⟨mem_sup_right ((hA.1 ha).1),?_⟩
    exact mem_centralizer_singleton_iff.mpr (hAW ha u.val huW).symm
  have hAB : A' ≤ B := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [hback]
    exact hAu.trans_eq hBl.symm
  have hc : Nat.card A = Nat.card A' := (card_map_of_injective e.symm.injective).symm
  have hAc := maxElementary_centralizes_of_local_card B (Tv T (v : G)) W A A'
    P hP hn hJ hA hAB (hA.2.1.map _) hc
  have hm := (map_mono (f := e.toMonoidHom) hAc).trans
    (map_centralizer_le_centralizer_image (W : Set G) e.toMonoidHom)
  rw [hback] at hm
  change A ≤ centralizer (W.map e.toMonoidHom : Set G) at hm
  rw [hWl] at hm
  exact hm

/-- The original local Thompson subgroup either moves V_v or lies in Q. -/
theorem SourceHypothesis.local_thompson_le_core_of_centralizes_moved
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ centralizer (Vv L V (v : G) : Set G)) :
    elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L := by
  rw [←H.join_centralizer_eq_core hTV]
  exact le_inf ((sSup_le fun _ h => h.1).trans (inf_le_left.trans le_sup_right))
    (H.local_thompson_centralizes_of_moved D v hv hTV hTv hJ)

/-- Source 12.6.9: movement outside Q generates the literal local residual. -/
theorem SourceHypothesis.local_thompson_generation
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : ¬ elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L) :
    Lv L (v : G) = ⁅Lv L (v : G),elementaryAbelianMaxJ (Tv T (v : G))⁆ := by
  let B := Lv L (v : G)
  let J := elementaryAbelianMaxJ (Tv T (v : G))
  let C := ⁅B,J⁆
  obtain ⟨e⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  let := Lv_isPerfect_of_A6 L (v : G) e
  have hJB : J ≤ normalizer (B : Set G) :=
    (sSup_le fun _ h => h.1).trans
      ((inf_le_inf H.chosen.sylow_normalizes_component le_rfl).trans (Mv_le_normalizer_Lv L _))
  have hCB : C ≤ B := le_normalizer_iff_commutator_le_left.mp hJB
  let N := C.subgroupOf B
  let : N.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left B J)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 B := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent f.ker := (hk ▸ pCore_isPGroup).isNilpotent
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : (N.map f).Normal := (inferInstance : N.Normal).map f hf
  rcases (inferInstance : (N.map f).Normal).eq_bot_or_eq_top with hz | ht
  · exfalso
    apply hJ
    apply H.local_thompson_le_core_of_centralizes_moved D v hv hTV hTv
    apply le_trans _ (D.local_moved_centralizer H.chosen H.source.quasisimple v hv)
    refine le_inf ?_ (normalizes_Vv_of_normalizes J _
      ((sSup_le fun _ h => h.1).trans (inf_le_left.trans hTV)) hJB)
    have hN := (Subgroup.map_eq_bot_iff N).mp hz
    rw [hk] at hN
    intro j hj
    apply (mem_coreQuotientCentralizer_iff B j).mpr
    refine ⟨hJB hj,?_⟩
    intro b hb
    have hc : ⁅j,b⁆ ∈ C := by
      dsimp only [C]
      rw [commutator_comm]
      exact commutator_mem_commutator hj hb
    exact ⟨⟨⁅j,b⁆,hCB hc⟩,hN hc,rfl⟩
  · have htop := eq_top_of_perfect_of_solvable_kernel_image f N ht
    apply le_antisymm ?_ hCB
    intro b hb
    exact (show (⟨b,hb⟩ : B) ∈ N from htop ▸ mem_top _)
end CFSG.Quasithin.Chapter12.Section06


namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Stellmacher
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The source 12.6.6 alternatives on the literal local Thompson group.
The Sylow transport argument also covers the case J(T)≤Q. -/
theorem SourceHypothesis.local_thompson_alternatives
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G))) :
    Lv L (v : G) = ⁅Lv L (v : G),elementaryAbelianMaxJ (Tv T (v : G))⁆ ∨
      elementaryAbelianMaxJ (Tv T (v : G)) = elementaryAbelianMaxJ (Q T L) := by
  by_cases hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L
  · exact Or.inr (elementaryAbelianMaxJ_eq_of_intermediate _ _ hJ (Q_le_Tv H.chosen v)).symm
  · exact Or.inl (H.local_thompson_generation D v hv hTV hTv hJ)
end CFSG.Quasithin.Chapter12.Section06


namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Stellmacher
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Both clauses of 12.6.9, together with the global generation consequence
of 12.6.7(2), on the original local and global Thompson subgroups. -/
theorem SourceHypothesis.nonsingular_thompson_generation
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : ¬ elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ Q T L ∧
      Lv L (v : G) = ⁅Lv L (v : G),elementaryAbelianMaxJ (Tv T (v : G))⁆ ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  have hlocal := H.local_thompson_generation D v hv hTV hTv hJ
  refine ⟨?_,hlocal,H.eq_commutator_thompson_of_local D v hv hlocal⟩
  intro hJT
  have he := elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G) (Tv T (v : G))
    (hJT.trans (Q_le_Tv H.chosen v)) inf_le_left
  exact hJ (he.le.trans hJT)
end CFSG.Quasithin.Chapter12.Section06
