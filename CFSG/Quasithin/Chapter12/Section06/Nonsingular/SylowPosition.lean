module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OrbitControl
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.Source
public import Theory.GroupTheory.SylowPointSelection
public import Theory.GroupTheory.PResidual.SylowSupplement
/-!
# The selected nonsingular centralizer and its local Sylow geometry

Every nonsingular point has an L-conjugate w with C_T(w) Sylow in C_M(w)
and index four in T. Work inside N_M(V): normalization preserves each
L-orbit on the actual V, so the point orbit has length 28. The earlier
TI property puts C_M(w) inside N_M(V). Sylow selection and the prime part
of that index give the required position.

The source application constructs the local Sylow S, its normalizer
intersection, both index bounds, the local residual factorization, and
all three clauses of 12.6.5 for the original canonical K_w and quotient
centralizer R. Conjugation preserves the original centralizer-control
target. A conditional 12.6.28 application uses the unchanged projection
V → V/C_V(L).

The T-invariance and TI inputs are the earlier structural conclusions
of 12.2.2, with final discharge owned by qt-d-1222-source. Component
recognition, block and splitting arguments, and fixed-space elimination
remain open: this module does not assert 12.6.2 or 12.6.23.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
opening of Theorem 12.6.2 and Lemmas 12.6.3--5, printed pp.823--824;
the singular-subspace application is 12.6.28, printed pp.834--835.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] [IsElementaryAbelian 2 V] in
theorem Mv_le_module_normalizer_of_TI
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : v ≠ 1) :
    Mv L (v : G) ≤ normalizer (V : Set G) := by
  intro g hg
  rcases hTI g hg.1 with hi | he
  · have hc := mem_centralizer_singleton_iff.mp hg.2
    have hm : (v : G) ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom := by
      refine ⟨v.property,v,v.property,?_⟩
      change g * (v : G) * g⁻¹ = v
      rw [hc,mul_inv_cancel_right]
    rw [hi,mem_bot] at hm
    exact (hv (Subtype.ext hm)).elim
  · exact mem_normalizer_iff_map_conj_eq.mpr he

/-- The original point has an L-conjugate in the source Sylow position. -/
theorem OrthogonalMarking.exists_nonsingular_sylow_position
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) :
    ∃ l : L, let w := conjugation L V chosen.normalizes l v
      D.Nonsingular w ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 := by
  let J := M L ⊓ normalizer (V : Set G)
  have hTJ : (T : Subgroup G) ≤ J :=
    le_inf chosen.sylow_normalizes_component hTV
  have hLJ : L ≤ J := le_inf L.le_normalizer chosen.normalizes
  obtain ⟨n,hn⟩ := exists_local_point_sylow T J hTJ (v : G)
  obtain ⟨l,hl⟩ := D.normalizer_orbit_control chosen n n.property.1 n.property.2 v
  let w := conjugation L V chosen.normalizes l v
  have hw : D.Nonsingular w := (nonsingular_conjugation D l v).mpr hv
  have hnw : (n : G)*(v : G)*(n : G)⁻¹ = (w : G) := hl
  rw [hnw] at hn
  have hC : J ⊓ Gv (w : G) = Mv L (w : G) := by
    apply le_antisymm (inf_le_inf inf_le_left le_rfl)
    exact le_inf (le_inf inf_le_left (Mv_le_module_normalizer_of_TI hTI w
      (nonsingular_ne_one D hw))) inf_le_right
  let C := J ⊓ Gv (w : G)
  let C' := C.subgroupOf J
  have hodd : ¬ 2 ∣ ((T : Subgroup G).subgroupOf J).relIndex C' := by
    rwa [relIndex_subgroupOf (show C ≤ J from inf_le_left)]
  have hindex : C'.index = 28 := by
    change (J ⊓ Gv (w : G)).relIndex J = 28
    rw [inf_relIndex_left,Gv,point_centralizer_index_of_orbit_control L J hLJ (w : G)
      (fun n => D.normalizer_orbit_control chosen n n.property.1 n.property.2 w)]
    have hi := D.nonsingular_centralizer_index chosen w hw
    simpa only [CLv,inf_relIndex_left,Gv] using hi
  have hi := (T.subtype hTJ).relIndex_eq_pow_factorization C' hodd
  rw [hindex] at hi
  have hf : (Nat.factorization 28) 2 = 2 := by
    rw [show 28 = 2 ^ 2 * 7 from rfl, Nat.factorization_mul (by decide) (by decide),
      Finsupp.add_apply, Nat.factorization_pow]
    norm_num [Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 7)]
  rw [hf] at hi
  have he : C'.relIndex (T.subtype hTJ) = (Tv T (w : G)).relIndex (T : Subgroup G) := by
    rw [Sylow.coe_subtype,relIndex_subgroupOf hTJ,Tv,inf_relIndex_left]
    apply congrArg Subgroup.index
    ext t
    change ((t : G) ∈ J ∧ (t : G) ∈ Gv (w : G)) ↔ (t : G) ∈ Gv (w : G)
    exact and_iff_right (hTJ t.property)
  rw [he] at hi
  have hTvC : Tv T (w : G) ≤ C := le_inf (inf_le_left.trans hTJ) inf_le_right
  have hp : IsPGroup 2 ((Tv T (w : G)).subgroupOf C) :=
    (T.isPGroup'.to_le (show Tv T (w : G) ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
  have hoddTv : ¬ 2 ∣ ((Tv T (w : G)).subgroupOf C).index := by
    change ¬ 2 ∣ (Tv T (w : G)).relIndex C
    rw [show Tv T (w : G) = (T : Subgroup G) ⊓ C from by
      dsimp only [Tv,C]; rw [← inf_assoc,inf_of_le_left hTJ],
      inf_relIndex_right]
    exact hn
  have hs : Chapter1.IsSylowIn 2 (Tv T (w : G)) C :=
    ⟨hp.toSylow hoddTv, map_subgroupOf_eq_of_le hTvC⟩
  exact ⟨l,hw,hC ▸ hs,hi⟩

theorem localCentralizer_eq_Lv_sup_Tv
    (hT : (T : Subgroup G) ≤ M L) (v : G)
    (hTv : Chapter1.IsSylowIn 2 (Tv T v) (LT T L ⊓ Gv v)) :
    LT T L ⊓ Gv v = Lv L v ⊔ Tv T v := by
  let B := LT T L ⊓ Gv v
  have hLB : Lv L v ≤ B :=
    le_inf ((Lv_le_L L v).trans le_sup_left) (Lv_le_Gv L v)
  let : ((Lv L v).subgroupOf B).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLB).mpr
      ((inf_le_inf (sup_le L.le_normalizer hT) le_rfl).trans (Mv_le_normalizer_Lv L v))
  have hp : IsPPerfect 2 ((Lv L v).subgroupOf B) :=
    (isPPerfect_embedded_pResidual 2 (CLv L v)).of_surjective
      (subgroupOfEquivOfLe hLB).symm.toMonoidHom
      (subgroupOfEquivOfLe hLB).symm.surjective
  have hr : pResidual 2 B = (Lv L v).subgroupOf B :=
    pResidual_eq_of_isPPerfect _ hp (localCentralizer_quotient_Lv_isPGroup T L hT v)
  obtain ⟨P,hP⟩ := hTv
  have hs := congrArg (Subgroup.map B.subtype) (pResidual_sup_sylow_eq_top P)
  rw [hr,Subgroup.map_sup,map_subgroupOf_eq_of_le hLB,hP,
    ← MonoidHom.range_eq_map,range_subtype] at hs
  exact hs.symm

theorem Rv_eq_core_Lv_sup_Tv
    (hT : (T : Subgroup G) ≤ M L) (v : G)
    (hTv : Chapter1.IsSylowIn 2 (Tv T v) (LT T L ⊓ Gv v)) :
    Rv T L v = (Lv L v ⊔ Tv T v).pCoreIn 2 := by
  rw [Rv,localCentralizer_eq_Lv_sup_Tv hT v hTv]

omit [Finite G] [IsElementaryAbelian 2 V] in
/-- Conjugating in L preserves the literal centralizer-control conclusion. -/
theorem centralizer_control_conjugation_iff
    (hn : L ≤ normalizer (V : Set G)) (l : L) (v : V) :
    Gv (conjugation L V hn l v : G) ≤ M L ↔ Gv (v : G) ≤ M L := by
  let e := MulAut.conj (l : G)
  have hM : (M L).map e.toMonoidHom = M L :=
    mem_normalizer_iff_map_conj_eq.mp ((M L).le_normalizer (L.le_normalizer l.property))
  have hc : (Gv (v : G)).map e.toMonoidHom = Gv (conjugation L V hn l v : G) :=
    map_pointCentralizer e (v : G)
  calc
    _ ↔ (Gv (v : G)).map e.toMonoidHom ≤ (M L).map e.toMonoidHom := by rw [hc,hM]
    _ ↔ _ := map_le_map_iff_of_injective e.injective

/-- All local Sylow and normalization inputs are constructed after an actual
L-conjugation. The normalization and TI assumptions are the earlier 12.2.2
clauses, whose source assembly is owned by qt-d-1222-source. The displayed
equivalence retains the original centralizer-control target. -/
theorem SourceHypothesis.selected_local_normalization
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) :
    ∃ l : L, let w := conjugation L V H.chosen.normalizes l v
      D.Nonsingular w ∧
      (Gv (w : G) ≤ M L ↔ Gv (v : G) ≤ M L) ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      LT T L ⊓ Gv (w : G) = Lv L (w : G) ⊔ Tv T (w : G) ∧
      Rv T L (w : G) = (Lv L (w : G) ⊔ Tv T (w : G)).pCoreIn 2 ∧
      ∃ S : Sylow 2 (Gv (w : G)),
        let S₀ := (S : Subgroup (Gv (w : G))).map (Gv (w : G)).subtype
        Tv T (w : G) ≤ S₀ ∧
        Chapter1.IsSylowIn 2 (S₀ ⊓ normalizer (Lv L (w : G) : Set G))
          (Gv (w : G) ⊓ normalizer (Lv L (w : G) : Set G)) ∧
        (Tv T (w : G)).relIndex S₀ ≤ 4 ∧
        (Rv T L (w : G)).relIndex (R L (Kv (w : G)) S₀ (w : G)) ≤ 4 ∧
        (Kv (w : G) ⊔ S₀).pCoreIn 2 ≤ R L (Kv (w : G)) S₀ (w : G) ∧
        R L (Kv (w : G)) S₀ (w : G) ⊓ Tv T (w : G) = Rv T L (w : G) ∧
        R L (Kv (w : G)) S₀ (w : G) ≤ normalizer (Lv L (w : G) : Set G) ∧
        ⁅Lv L (w : G), R L (Kv (w : G)) S₀ (w : G)⁆ ≤ (Lv L (w : G)).pCoreIn 2 ∧
        R L (Kv (w : G)) S₀ (w : G) = S₀ ⊓ coreQuotientCentralizer (Lv L (w : G)) := by
  obtain ⟨l,hw,hTv,hi⟩ := D.exists_nonsingular_sylow_position H.chosen hTV hTI v hv
  let w := conjugation L V H.chosen.normalizes l v
  have hT := H.chosen.sylow_normalizes_component
  have hTv' := hTv.restrict
    (show Tv T (w : G) ≤ LT T L ⊓ Gv (w : G) from inf_le_inf le_sup_right le_rfl)
    (show LT T L ⊓ Gv (w : G) ≤ Mv L (w : G) from
      inf_le_inf (sup_le L.le_normalizer hT) le_rfl)
  refine ⟨l,hw,centralizer_control_conjugation_iff H.chosen.normalizes l v,hTv,hi,
    localCentralizer_eq_Lv_sup_Tv hT _ hTv',Rv_eq_core_Lv_sup_Tv hT _ hTv',?_⟩
  obtain ⟨⟨e⟩,_,_,hLK⟩ := D.nonsingular_local_structure H.chosen H.source.quasisimple w hw
  obtain ⟨P,hP⟩ := hTv'
  obtain ⟨S,hS,hN,hR,hcomm,he⟩ :=
    exists_nonsingular_sylow_normalization T L (w : G) hT hLK e P hP hi
  have hcap := R_inf_Tv_eq_Rv T L (Kv (w : G)) _ (w : G) hT hLK hS P hP
    (Lv_coreQuotient_center_eq_bot_of_A6 L (w : G) e)
  obtain ⟨hSi,hRi⟩ := nonsingular_local_index_bounds T L (Kv (w : G)) (w : G)
    S hS hcap.symm hi
  exact ⟨S,hS,hN,hSi,hRi,core_le_R_of_sylow L _ _ S (Kv_le_Gv _),hcap,hR,hcomm,he⟩

/-- Reduction of 12.6.2 to the actual Sylow position constructed above.
The local centralizer theorem is still an explicit, undischarged input. -/
theorem SourceHypothesis.nonsingular_control_of_selected
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hlocal : ∀ w : V, D.Nonsingular w →
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) →
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 → Gv (w : G) ≤ M L) :
    ∀ v : V, D.Nonsingular v → Gv (v : G) ≤ M L := by
  intro v hv
  obtain ⟨l,hw,hTv,hi⟩ := D.exists_nonsingular_sylow_position H.chosen hTV hTI v hv
  exact (centralizer_control_conjugation_iff H.chosen.normalizes l v).mp
    (hlocal _ hw hTv hi)

/-- The literal 12.6.28 singular-subspace consumer now needs centralizer
control only in the selected position. Its component/block premise is not
asserted by this conditional application. -/
theorem SourceHypothesis.singular_subgroup_form_eq_zero_of_selected
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hlocal : ∀ w : V, D.Nonsingular w →
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) →
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 → Gv (w : G) ≤ M L)
    (E : Subgroup G) (hEV : E ≤ V)
    (hescape : ¬ centralizer (E : Set G) ≤ M L) :
    ∀ e : E,
      BinaryPermutation.TerminalOrthogonal.Eight.form
        (D.coordinates (Submodule.Quotient.mk
          (Additive.ofMul (show V from ⟨e.1,hEV e.2⟩)))) = 0 :=
  singular_subgroup_form_eq_zero H.chosen.normalizes D
    (H.nonsingular_control_of_selected D hTV hTI hlocal) E hEV hescape
end CFSG.Quasithin.Chapter12.Section06
