module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryLine
public import Theory.GroupTheory.AbelianCommutatorIndex
public import Theory.GroupTheory.PGroup.MaximalIndex

/-!
# Intersecting hyperplanes in the odd escaping graph

The two proved neighbors give hyperplanes Y in V and F in E, with
[V,F]=Z_S and [E,Y] in the distinct endpoint line Z'. Their common
commutator lies in Z_S intersect Z'. Extend that proper intersection to
a hyperplane of Z_S. Commutator evaluation in its order-two quotient
bounds the action of F on V by two: any element in the kernel has too
small a displacement to act nontrivially, by the actual global s-value.
Since F has index two in E, the action of E has order at most four.
The global s-value of E forces n<=2; the standing n>1 gives n=2.

Centralizer rigidity then identifies [Y,F] with the order-two intersection
of the endpoint lines. If the full escaping closure is abelian, the
moving neighbor intersects that closure in exactly its endpoint line.
The proofs retain the literal conjugators, normalizers and centralizers.

This proves the parameter and intersection steps of 6.1.19. The remaining
n=2 transvection argument, initial 6.1.4-5 and final 6.1.27 assembly remain
with qt-d-1222-rankone-recognition-natural.
Source: Aschbacher-Smith, 6.1.17(4-5), 6.1.19, printed pp.672-674.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph
variable {G : Type*} [Group G] [Finite G]

private def centralRow (X Z : Subgroup G) [IsMulCommutative Z]
    (hZX : Z ≤ centralizer (X : Set G)) (t : G)
    (hc : ∀ x ∈ X, ⁅x,t⁆ ∈ Z) : X →* Z where
  toFun x := ⟨⁅(x : G),t⁆,hc x x.property⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := by
    apply Subtype.ext
    change ⁅(x : G)*(y : G),t⁆ = ⁅(x : G),t⁆ * ⁅(y : G),t⁆
    rw [commutatorElement_mul_left_eq_conj_mul,
      mem_centralizer_iff.mp (hZX (hc y y.property)) x x.property,
      mul_inv_cancel_right]
    exact congrArg Subtype.val (mul_comm (⟨⁅(y : G),t⁆,hc y y.property⟩ : Z)
      ⟨⁅(x : G),t⁆,hc x x.property⟩)

private theorem small_row_centralizes
    (V A D : Subgroup G) [IsElementaryAbelian 2 V] {n : ℕ}
    (hs : globalS V = n) (hA : IsPGroup 2 A)
    {a : G} (ha : a ∈ A) (hn : a ∈ Subgroup.normalizer (V : Set G))
    (hcard : Nat.card D < 2 ^ n) (hc : ∀ v ∈ V, ⁅v,a⁆ ∈ D) :
    a ∈ centralizer (V : Set G) := by
  have hi := centralizer_relIndex_le_card_of_abelian_commutator V V D le_rfl a hn hc
  have hr : subgroupCorank V (V ⊓ centralizer ({a} : Set G)) < n := by
    unfold subgroupCorank
    rw [inf_relIndex_left]
    exact (Nat.log_lt_iff_lt_pow (by decide)
      ((centralizer ({a} : Set G)).subgroupOf V).index_ne_zero_of_finite).mpr
      (hi.trans_lt hcard)
  have he := centralizer_inf_eq_of_corank_lt_globalS
    (show V ⊓ centralizer ({a} : Set G) ≤ V from inf_le_left)
    (show (subgroupCorank V (V ⊓ centralizer ({a} : Set G)) : ℕ∞) < globalS V from by
      rw [hs]; exact_mod_cast hr) hA
  have hc' : a ∈ centralizer (V ⊓ centralizer ({a} : Set G) : Set G) := by
    intro v hv
    exact mem_centralizer_singleton_iff.mp hv.2
  exact (he.le ⟨ha,hc'⟩).2

/-- A proper common displacement of a hyperplane bounds the actor image by two. -/
private theorem hyperplane_actor_index
    (V Y A Z W : Subgroup G) [IsElementaryAbelian 2 V]
    (hZV : Z ≤ V) (hZA : Z ≤ centralizer (A : Set G))
    (hAN : A ≤ Subgroup.normalizer (V : Set G)) (hA : IsPGroup 2 A)
    {n : ℕ} (hs : globalS V = n) (hZcard : Nat.card Z = 2 ^ n)
    (_hYV : Y ≤ V) (hYindex : Y.relIndex V ≤ 2)
    (hcomm : ⁅V,A⁆ ≤ Z) (hsmall : ⁅Y,A⁆ ≤ W) (hW : W < Z) :
    (centralizer (V : Set G)).relIndex A ≤ 2 := by
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_le hZV
  let : CommGroup Z := IsMulCommutative.instCommGroup
  have hWtop : W.subgroupOf Z ≠ ⊤ := by
    intro he
    apply hW.not_ge
    intro w hw
    exact show (⟨w,hw⟩ : Z) ∈ W.subgroupOf Z from he ▸ mem_top _
  obtain ⟨D,hD,hWD⟩ := (eq_top_or_exists_le_coatom (W.subgroupOf Z)).resolve_left hWtop
  have hDi : D.index = 2 := (IsElementaryAbelian.isPGroup 2 Z).index_of_isCoatom D hD
  let P := D.map Z.subtype
  have hPZ : P < Z := by
    refine lt_of_le_of_ne (map_subtype_le D) ?_
    intro he
    apply hD.ne_top
    apply map_injective Z.subtype_injective
    simpa only [← MonoidHom.range_eq_map,range_subtype] using he
  have hWP : W ≤ P := by
    have hh := map_mono (f := Z.subtype) hWD
    rwa [map_subgroupOf_eq_of_le hW.le] at hh
  have hPcard : Nat.card P < 2 ^ n := by
    rw [←hZcard]
    exact Nat.lt_of_not_ge (fun hh => hPZ.ne (eq_of_le_of_card_ge hPZ.le hh))
  have hdiv : Y.relIndex V ∣ 2 := by
    have hp : Y.relIndex V ≠ 0 := (Y.subgroupOf V).index_ne_zero_of_finite
    have hh : Y.relIndex V = 1 ∨ Y.relIndex V = 2 := by omega
    rcases hh with hh | hh <;> simp [hh]
  obtain ⟨v,hv,hcosets⟩ := relIndex_dvd_two_iff.mp hdiv
  have hrow (a : G) (ha : a ∈ A) (x : G) (hx : x ∈ V) : ⁅x,a⁆ ∈ Z :=
    hcomm (commutator_mem_commutator hx ha)
  have hdual (a : G) (ha : a ∈ A) : ⁅a,v⁆ ∈ Z := by
    rw [←commutatorElement_inv]
    exact Z.inv_mem (hrow a ha v hv)
  let q := QuotientGroup.mk' D
  let f := q.comp (centralRow A Z hZA v hdual)
  have hk : f.ker ≤ (centralizer (V : Set G)).subgroupOf A := by
    intro a ha
    have hav : ⁅(a : G),v⁆ ∈ P := by
      exact mem_map_of_mem Z.subtype ((QuotientGroup.eq_one_iff _).mp ha)
    have hva : ⁅v,(a : G)⁆ ∈ P := by
      rw [←commutatorElement_inv]
      exact P.inv_mem hav
    let r := centralRow V Z (hZV.trans (le_centralizer V)) (a : G) (hrow a a.property)
    have hY : Y.subgroupOf V ≤ P.comap (Z.subtype.comp r) := by
      intro y hy
      exact hWP (hsmall (commutator_mem_commutator hy a.property))
    have hrv : (⟨v,hv⟩ : V) ∈ P.comap (Z.subtype.comp r) := hva
    have hall (x : G) (hx : x ∈ V) : ⁅x,(a : G)⁆ ∈ P := by
      rcases hcosets x hx with hxy | hy
      · exact (P.comap (Z.subtype.comp r)).mul_mem_cancel_right hrv |>.mp
          (hY (show (⟨x,hx⟩ : V) * ⟨v,hv⟩ ∈ Y.subgroupOf V from hxy))
      · exact hY (show (⟨x,hx⟩ : V) ∈ Y.subgroupOf V from hy)
    exact small_row_centralizes V A P hs hA a.property (hAN a.property) hPcard hall
  have hi : (centralizer (V : Set G)).relIndex A ≤ f.ker.index := index_antitone hk
  rw [index_ker] at hi
  exact hi.trans ((Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective).trans_eq hDi)


variable {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
namespace OddConfiguration
variable (d : OddConfiguration T L M R)

/-- The intersecting hyperplanes force the field parameter two and an
order-two intersection of the literal endpoint lines. -/
theorem parameter_and_intersection
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M) :
    n = 2 ∧ Nat.card (ZS (T : Subgroup G) L R ⊓
      (ZS (T : Subgroup G) L R).map (MulAut.conj d.representative).toMonoidHom : Subgroup G) = 2 := by
  obtain ⟨a,k,ha,hplace,hVA,hi,hline,hout,hFi,hrev⟩ :=
    d.exists_two_neighbors h hnat hE hs hNS
  let V := (layer L R).map (MulAut.conj (k : G)).toMonoidHom
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let Z := ZS (T : Subgroup G) L R
  let Z' := Z.map (MulAut.conj d.representative).toMonoidHom
  let Y := V ⊓ Subgroup.normalizer (E : Set G)
  let F := E ⊓ Subgroup.normalizer (V : Set G)
  let W := Z ⊓ Z'
  let := h.layer_elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le (show F ≤ E from inf_le_left)
  have hZcard : Nat.card Z = 2 ^ n :=
    (hnat.sylow_intersection_geometry T h.sylow_normalizes_L).1
  have hZ'card : Nat.card Z' = Nat.card Z := card_map_of_injective (MulAut.conj d.representative).injective
  have hW : W < Z := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro he
    have hZZ' : Z ≤ Z' := he.symm.le.trans inf_le_right
    exact d.endpoint_line_ne h hnat hE hNS
      (eq_of_le_of_card_ge hZZ' hZ'card.le).symm
  have hZV : Z ≤ V := by
    have hHZ : d.H ≤ Subgroup.normalizer (Z : Set G) := d.overgroup.trans
      (sup_le (Subgroup.centralizer_le_normalizer _) h.sylow_normalizes_ZS)
    have hZk : Z.map (MulAut.conj (k : G)).toMonoidHom = Z :=
      mem_normalizer_iff_map_conj_eq.mp (hHZ k.property)
    rw [←hZk]
    exact map_mono (show Z ≤ layer L R from inf_le_left)
  have hZE : Z ≤ centralizer (E : Set G) := le_centralizer_iff.mp
    (hplace.trans ((d.crossed_centralization h hnat hs).1.trans inf_le_right))
  have hsV : globalS V = n := by
    rw [globalS_map_equiv (layer L R) (MulAut.conj (k : G)),hs]
  have hsE : globalS E = n := by
    rw [globalS_map_equiv (layer L R) (MulAut.conj a),hs]
  have hYi : Y.relIndex V ≤ 2 := by
    rw [inf_relIndex_left]
    exact (relIndex_le_of_le_right hVA
      ((Subgroup.normalizer (E : Set G)).subgroupOf d.localClosure).index_ne_zero_of_finite).trans hi.le
  have hFi' : F.relIndex E = 2 := by rw [inf_relIndex_left]; exact hFi
  have hsmall : ⁅Y,F⁆ ≤ W := by
    apply le_inf
    · exact (commutator_mono inf_le_left le_rfl).trans hrev.le
    · rw [commutator_comm]
      apply (commutator_mono (show F ≤ E from inf_le_left)
        (le_inf (inf_le_left.trans hVA) inf_le_right)).trans hline.le
  have hidx : (centralizer (V : Set G)).relIndex F ≤ 2 :=
    hyperplane_actor_index V Y F Z W hZV
      (hZE.trans (centralizer_le inf_le_left)) inf_le_right
      (IsElementaryAbelian.isPGroup 2 F) hsV hZcard inf_le_left hYi hrev.le hsmall hW
  have hindex : (centralizer (V : Set G)).relIndex E ≤ 4 := by
    have he := relIndex_mul_relIndex (F ⊓ centralizer (V : Set G)) F E inf_le_left inf_le_left
    rw [inf_relIndex_left,hFi'] at he
    have hh := relIndex_le_of_le_left (show F ⊓ centralizer (V : Set G) ≤ centralizer (V : Set G) from inf_le_right)
      ((F ⊓ centralizer (V : Set G)).subgroupOf E).index_ne_zero_of_finite
    exact hh.trans (he ▸ (by omega : (centralizer (V : Set G)).relIndex F * 2 ≤ 4))
  have hn : n = 2 := by
    by_contra hn
    have h2n : 2 < n := by have := h.n_gt_one; omega
    have hr : subgroupCorank E (E ⊓ centralizer (V : Set G)) ≤ 2 := by
      unfold subgroupCorank
      rw [inf_relIndex_left]
      have hh := Nat.log_mono_right hindex (b := 2)
      norm_num at hh ⊢
      exact hh
    have he := centralizer_inf_eq_of_corank_lt_globalS
      (show E ⊓ centralizer (V : Set G) ≤ E from inf_le_left)
      (show (subgroupCorank E (E ⊓ centralizer (V : Set G)) : ℕ∞) < globalS E from by
        rw [hsE]; exact_mod_cast lt_of_le_of_lt hr h2n)
      (IsElementaryAbelian.isPGroup 2 V)
    have hc : V ≤ centralizer (E : Set G) := by
      have hvc : V ≤ centralizer (E ⊓ centralizer (V : Set G) : Set G) :=
        le_centralizer_iff.mp inf_le_right
      have hvv : V ≤ V ⊓ centralizer (E : Set G) := by
        rw [←he]; exact le_inf le_rfl hvc
      exact hvv.trans inf_le_right
    have hf1 := relIndex_eq_one.mpr
      ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _))
    rw [hFi] at hf1
    norm_num at hf1
  have hnon : ⁅Y,F⁆ ≠ ⊥ := by
    intro hz
    have hr : subgroupCorank V Y < n := by
      unfold subgroupCorank
      have hh := Nat.log_mono_right hYi (b := 2)
      norm_num at hh
      have := h.n_gt_one
      omega
    have he := centralizer_inf_eq_of_corank_lt_globalS (show Y ≤ V from inf_le_left)
      (show (subgroupCorank V Y : ℕ∞) < globalS V from by rw [hsV]; exact_mod_cast hr)
      (IsElementaryAbelian.isPGroup 2 F)
    have hc : F ≤ centralizer (V : Set G) := by
      have hh : F ≤ F ⊓ centralizer (V : Set G) := by
        rw [←he]
        exact le_inf le_rfl (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))
      exact hh.trans inf_le_right
    have hz' : ⁅V,F⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)
    exact h.ZS_ne_bot (hrev.symm.trans hz')
  have hWne : W ≠ ⊥ := ne_bot_of_le_ne_bot hnon hsmall
  have hWlo : 1 < Nat.card W := (one_lt_card_iff_ne_bot W).mpr hWne
  have hWlt : Nat.card W < 4 := by
    have hh : Nat.card W < Nat.card Z :=
      Nat.lt_of_not_ge (fun hh => hW.ne (eq_of_le_of_card_ge hW.le hh))
    rw [hZcard,hn] at hh
    exact hh
  have hd : Nat.card W ∣ 4 := by
    have hh := card_dvd_of_le hW.le
    rwa [hZcard,hn] at hh
  have hcard : Nat.card W = 2 := by
    have hh : Nat.card W = 2 ∨ Nat.card W = 3 := by omega
    rcases hh with hh | hh
    · exact hh
    · rw [hh] at hd
      norm_num at hd
  exact ⟨hn,hcard⟩

/-- The two actual neighboring natural modules have hyperplane normalizers.
Their crossed commutator is exactly the common order-two endpoint line. -/
theorem intersecting_hyperplanes
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M) :
    ∃ (a : G) (k : d.H), let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let V := (layer L R).map (MulAut.conj (k : G)).toMonoidHom
      let Z := ZS (T : Subgroup G) L R
      let Z' := Z.map (MulAut.conj d.representative).toMonoidHom
      let Y := V ⊓ Subgroup.normalizer (E : Set G)
      let F := E ⊓ Subgroup.normalizer (V : Set G)
      E ≤ d.localClosure.map (MulAut.conj d.representative).toMonoidHom ∧
      V ≤ d.localClosure ∧ ¬ E ≤ d.H.pCoreIn 2 ∧
      Y.relIndex V = 2 ∧ F.relIndex E = 2 ∧
      ⁅E,Y⁆ = Z' ∧ ⁅V,F⁆ = Z ∧ ⁅Y,F⁆ = Z ⊓ Z' := by
  obtain ⟨a,k,ha,hplace,hVA,hi,hline,hout,hFi,hrev⟩ :=
    d.exists_two_neighbors h hnat hE hs hNS
  let V := (layer L R).map (MulAut.conj (k : G)).toMonoidHom
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let Z := ZS (T : Subgroup G) L R
  let Z' := Z.map (MulAut.conj d.representative).toMonoidHom
  let Y := V ⊓ Subgroup.normalizer (E : Set G)
  let F := E ⊓ Subgroup.normalizer (V : Set G)
  let W := Z ⊓ Z'
  let := h.layer_elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le (show F ≤ E from inf_le_left)
  have hWcard : Nat.card W = 2 := (d.parameter_and_intersection h hnat hE hs hNS).2
  have hYi : Y.relIndex V ≤ 2 := by
    rw [inf_relIndex_left]
    exact (relIndex_le_of_le_right hVA
      ((Subgroup.normalizer (E : Set G)).subgroupOf d.localClosure).index_ne_zero_of_finite).trans hi.le
  have hsV : globalS V = n := by
    rw [globalS_map_equiv (layer L R) (MulAut.conj (k : G)),hs]
  have hsmall : ⁅Y,F⁆ ≤ W := by
    apply le_inf
    · exact (commutator_mono inf_le_left le_rfl).trans hrev.le
    · rw [commutator_comm]
      exact (commutator_mono (show F ≤ E from inf_le_left)
        (le_inf (inf_le_left.trans hVA) inf_le_right)).trans hline.le
  have hnon : ⁅Y,F⁆ ≠ ⊥ := by
    intro hz
    have hr : subgroupCorank V Y < n := by
      unfold subgroupCorank
      have hh := Nat.log_mono_right hYi (b := 2)
      norm_num at hh
      have := h.n_gt_one
      omega
    have he := centralizer_inf_eq_of_corank_lt_globalS (show Y ≤ V from inf_le_left)
      (show (subgroupCorank V Y : ℕ∞) < globalS V from by rw [hsV]; exact_mod_cast hr)
      (IsElementaryAbelian.isPGroup 2 F)
    have hc : F ≤ centralizer (V : Set G) := by
      have hh : F ≤ F ⊓ centralizer (V : Set G) := by
        rw [←he]
        exact le_inf le_rfl (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))
      exact hh.trans inf_le_right
    exact h.ZS_ne_bot (hrev.symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)))
  have hYi' : Y.relIndex V = 2 := by
    have hp : Y.relIndex V ≠ 0 := (Y.subgroupOf V).index_ne_zero_of_finite
    by_contra hn
    have he1 : Y.relIndex V = 1 := by omega
    have hVY : V ≤ Y := relIndex_eq_one.mp he1
    have hZW : Z ≤ W := hrev.symm.le.trans
      ((commutator_mono hVY le_rfl).trans hsmall)
    have hZZ' : Z ≤ Z' := hZW.trans inf_le_right
    exact d.endpoint_line_ne h hnat hE hNS
      (eq_of_le_of_card_ge hZZ' (by rw [card_map_of_injective (MulAut.conj d.representative).injective])).symm
  have hEY : ⁅E,Y⁆ = Z' := by
    have hYc : Y ≤ centralizer (Z' : Set G) :=
      (inf_le_left.trans hVA).trans
        (((d.crossed_centralization h hnat hs).2.trans
          (map_mono (f := (MulAut.conj d.representative).toMonoidHom) inf_le_right)).trans
          (map_centralizer_le_centralizer_image (Z : Set G) (MulAut.conj d.representative).toMonoidHom))
    have hc : Y ≤ centralizer (Z.map (MulAut.conj a).toMonoidHom : Set G) := by
      rw [d.neighbor_line_eq h ha]; exact hYc
    have hn : ⁅E,Y⁆ ≠ ⊥ := by
      intro hz
      apply hnon
      apply le_bot_iff.mp
      rw [←hz,commutator_comm E Y]
      exact commutator_mono le_rfl inf_le_left
    exact (conjugate_commutator_eq_line h hnat hs a
      ((IsElementaryAbelian.isPGroup 2 V).to_le inf_le_left) inf_le_right hc hn).trans
      (d.neighbor_line_eq h ha)
  refine ⟨a,k,hplace,hVA,hout,hYi',?_,hEY,hrev,?_⟩
  · rw [inf_relIndex_left]; exact hFi
  · apply eq_of_le_of_card_ge hsmall
    rw [hWcard]
    exact (one_lt_card_iff_ne_bot _).mpr hnon

/-- Under the contrary abelian assumption, the moving neighbor meets the
full escaping closure in precisely its endpoint line. This is the
intersection used before the transvection argument in 6.1.19. -/
theorem exists_neighbor_with_closure_intersection
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    ∃ a : G, let E := (layer L R).map (MulAut.conj a).toMonoidHom
      E ≤ Escape.I (T : Subgroup G) L R ∧
      ¬ E ≤ d.H.pCoreIn 2 ∧
      E ⊓ Escape.U (T : Subgroup G) L R =
        (ZS (T : Subgroup G) L R).map (MulAut.conj d.representative).toMonoidHom := by
  obtain ⟨hn,_⟩ := d.parameter_and_intersection h hnat hE hs hNS
  obtain ⟨a,k,hplace,hVA,hout,_,hFi,hEY,hVF,_⟩ :=
    d.intersecting_hyperplanes h hnat hE hs hNS
  let V := (layer L R).map (MulAut.conj (k : G)).toMonoidHom
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let Y := V ⊓ Subgroup.normalizer (E : Set G)
  let U := Escape.U (T : Subgroup G) L R
  let Z' := (ZS (T : Subgroup G) L R).map (MulAut.conj d.representative).toMonoidHom
  let C := E ⊓ U
  let := h.layer_elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hEI : E ≤ Escape.I (T : Subgroup G) L R :=
    hplace.trans ((d.crossed_centralization h hnat hs).1.trans inf_le_right)
  have hVU : V ≤ U := hVA.trans d.closure_le
  have hZE : Z' ≤ E := hEY.symm.le.trans
    (le_normalizer_iff_commutator_le_left.mp (show Y ≤ Subgroup.normalizer (E : Set G) from inf_le_right))
  have hZU : Z' ≤ U := by
    apply hEY.symm.le.trans
    rw [commutator_comm]
    exact (commutator_mono (inf_le_left.trans hVU) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        (hEI.trans (NaturalEscape.I_normalizes_U (T : Subgroup G) L R)))
  have hZC : Z' ≤ C := le_inf hZE hZU
  have hZcard : Nat.card Z' = 4 := by
    change Nat.card ((ZS (T : Subgroup G) L R).map
      (MulAut.conj d.representative).toMonoidHom) = 4
    have hz : Nat.card (ZS (T : Subgroup G) L R) = 2 ^ n :=
      (hnat.sylow_intersection_geometry T h.sylow_normalizes_L).1
    rw [card_map_of_injective (MulAut.conj d.representative).injective,hz,hn]
    norm_num
  have hCcard : Nat.card C ≤ Nat.card Z' := by
    by_contra hc
    have hClarge : 4 < Nat.card C := by omega
    have hEcard : Nat.card E = 16 := by
      rw [card_map_of_injective (MulAut.conj a).injective,hnat.card,hn]
      norm_num
    have hprod := relIndex_mul_relIndex (⊥ : Subgroup G) C E bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,hEcard] at hprod
    have hidx : C.relIndex E < 4 := by nlinarith
    have hr : subgroupCorank E C < 2 := by
      unfold subgroupCorank
      exact (Nat.log_lt_iff_lt_pow (by decide) (C.subgroupOf E).index_ne_zero_of_finite).mpr hidx
    have hsE : globalS E = 2 := by
      rw [globalS_map_equiv (layer L R) (MulAut.conj a),hs,hn]
      norm_num
    have he := centralizer_inf_eq_of_corank_lt_globalS (show C ≤ E from inf_le_left)
      (show (subgroupCorank E C : ℕ∞) < globalS E from by rw [hsE]; exact_mod_cast hr)
      (IsElementaryAbelian.isPGroup 2 V)
    have hVC : V ≤ centralizer (C : Set G) :=
      hVU.trans (hab.trans (centralizer_le inf_le_right))
    have hVE : V ≤ centralizer (E : Set G) := by
      have hh : V ≤ V ⊓ centralizer (E : Set G) := by
        rw [←he]; exact le_inf le_rfl hVC
      exact hh.trans inf_le_right
    have hEF : E ≤ E ⊓ Subgroup.normalizer (V : Set G) := le_inf le_rfl
      ((le_centralizer_iff.mp hVE).trans (Subgroup.centralizer_le_normalizer _))
    have he1 := relIndex_eq_one.mpr hEF
    rw [hFi] at he1
    norm_num at he1
  exact ⟨a,hEI,hout,(eq_of_le_of_card_ge hZC hCcard).symm⟩

end OddConfiguration

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph
