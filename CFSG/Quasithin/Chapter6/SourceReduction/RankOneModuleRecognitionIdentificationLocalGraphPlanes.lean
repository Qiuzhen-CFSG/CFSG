module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalNoncyclic
public import Theory.GroupTheory.AbelianCommutatorIndex
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryCentralizer

/-!
# Field planes of the moving graph pair in source 6.2.8

Let A and B be conjugates of the natural sixteen, with N_A(B) of index
two, B not normalizing A, and A inside an abelian group normalized by B.
Hyperplane-centralizer rigidity makes N_A(B) act nontrivially on B and
forces its commutator to have order at least four. This commutator lies
in C_B(A), whose order is at most four by the same rigidity. Hence it is
exactly C_B(A), an escaping field plane. The field-actor dichotomy then
forces C_A(B) to have order four as well, and this is the second field plane.

Both planes are transported through the literal original conjugation maps.
If the reverse normalizer also has index two, the two hyperplanes cannot
commute: otherwise one of order eight lies in a centralizer of order four.
Their commutator supplies a nonidentity point in A intersect B.

The Chapter 12 companion supplies the abelian closure and normalization
from the actual critical endpoints. The reverse neighbor and terminal
non-two pair remain necessary for the full core escape; neither is assumed
as an unconditional source theorem here.
Source: Aschbacher--Smith, 6.2.8, printed pp.684--685, using 6.1.10(1)
and 6.2.4(1--2), printed pp.670 and 680.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem graph_half_card {A B : Subgroup G}
    (hle : A ≤ B) (hc : Nat.card B = 16) (hi : A.relIndex B = 2) :
    Nat.card A = 8 := by
  have hh := (A.subgroupOf B).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at hh
  change Nat.card A * A.relIndex B = Nat.card B at hh
  rw [hi,hc] at hh
  omega

omit [Finite G] in
private theorem small_subgroup_card {A B : Subgroup G}
    (hle : A ≤ B) (hB : Nat.card B = 16) (hlt : Nat.card A < 8) :
    Nat.card A ≤ 4 := by
  have hd : Nat.card A ∣ 2 ^ 4 := by
    have hd := card_dvd_of_le hle
    rw [hB] at hd
    exact hd
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases k <;> norm_num only [Nat.reducePow] at he <;> omega

private theorem large_commutator_of_rigid_hyperplanes
    (B F : Subgroup G) [IsMulCommutative B] (hB : Nat.card B = 16)
    (hlarge : ∀ U ≤ B, 8 ≤ Nat.card U → centralizer (U : Set G) = centralizer (B : Set G))
    (hFN : F ≤ normalizer (B : Set G)) (hnon : ¬ F ≤ centralizer (B : Set G)) :
    4 ≤ Nat.card (⁅F,B⁆ : Subgroup G) := by
  obtain ⟨y,hy,hyn⟩ := SetLike.not_le_iff_exists.mp hnon
  let C := B ⊓ centralizer ({y} : Set G)
  have hi := centralizer_relIndex_le_card_of_abelian_commutator B B ⁅F,B⁆ le_rfl y (hFN hy)
    (fun x hx => by rw [commutator_comm]; exact commutator_mem_commutator hx hy)
  have hClarge : ¬ 8 ≤ Nat.card C := by
    intro hc
    have he := hlarge C inf_le_left hc
    apply hyn
    rw [←he]
    intro c hc
    exact (mem_centralizer_singleton_iff.mp hc.2)
  have hcb := (C.subgroupOf B).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show C ≤ B from inf_le_left)).toEquiv] at hcb
  change Nat.card C * C.relIndex B = Nat.card B at hcb
  have hrel : C.relIndex B = (centralizer ({y} : Set G)).relIndex B := by
    simp only [C,inf_relIndex_left]
  rw [hB,hrel] at hcb
  have hcommB : ⁅F,B⁆ ≤ B := le_normalizer_iff_commutator_le_right.mp hFN
  by_contra hn
  have hsmall : Nat.card (⁅F,B⁆ : Subgroup G) ≤ 2 := by
    have hd : Nat.card (⁅F,B⁆ : Subgroup G) ∣ 2 ^ 4 := by
      have hd := card_dvd_of_le hcommB
      rw [hB] at hd
      exact hd
    obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    interval_cases k <;> norm_num only [Nat.reducePow] at he <;> omega
  have hCpos : 0 < Nat.card C := Nat.card_pos
  nlinarith

private theorem graph_pair_first_plane
    (B A U : Subgroup G) [IsMulCommutative B] [IsMulCommutative U]
    (hB : Nat.card B = 16) (hA : Nat.card A = 16)
    (hlargeB : ∀ C ≤ B, 8 ≤ Nat.card C → centralizer (C : Set G) = centralizer (B : Set G))
    (hlargeA : ∀ C ≤ A, 8 ≤ Nat.card C → centralizer (C : Set G) = centralizer (A : Set G))
    (hAU : A ≤ U) (hBU : B ≤ normalizer (U : Set G))
    (hi : (A ⊓ normalizer (B : Set G)).relIndex A = 2)
    (hBnA : ¬ B ≤ normalizer (A : Set G)) :
    ⁅A ⊓ normalizer (B : Set G),B⁆ = B ⊓ centralizer (A : Set G) ∧
      Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) = 4 := by
  let F := A ⊓ normalizer (B : Set G)
  let C := B ⊓ centralizer (A : Set G)
  have hF : Nat.card F = 8 := graph_half_card inf_le_left hA hi
  have hn : ¬ F ≤ centralizer (B : Set G) := by
    intro hh
    have hc := le_centralizer_iff.mp hh
    rw [hlargeA F inf_le_left hF.ge] at hc
    exact hBnA (hc.trans (Subgroup.centralizer_le_normalizer _))
  have hc : ⁅F,B⁆ ≤ C := le_inf
    (le_normalizer_iff_commutator_le_right.mp (show F ≤ normalizer (B : Set G) from inf_le_right))
    (((commutator_mono (inf_le_left.trans hAU) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hBU)).trans
        (U.le_centralizer.trans (centralizer_le hAU)))
  have hlo := large_commutator_of_rigid_hyperplanes B F hB hlargeB inf_le_right hn
  have hlt : Nat.card C < 8 := by
    by_contra hh
    have hh := hlargeB C inf_le_left (Nat.le_of_not_gt hh)
    have hAC : A ≤ centralizer (C : Set G) := le_centralizer_iff.mpr inf_le_right
    rw [hh] at hAC
    have hAN := hAC.trans (Subgroup.centralizer_le_normalizer _)
    rw [inf_eq_left.mpr hAN,relIndex_self] at hi
    contradiction
  have hhi := small_subgroup_card (show C ≤ B from inf_le_left) hB hlt
  have hcard : Nat.card C = 4 := le_antisymm hhi (hlo.trans (card_le_of_le hc))
  exact ⟨eq_of_le_of_card_ge hc (by rw [hcard]; exact hlo),hcard⟩

omit [Finite G] in
private theorem field_plane_actor_index
    {L M B C F : Subgroup G} {n : ℕ}
    (hnat : IsNaturalModule L B n)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G))
    (hfield : IsInvolutoryFieldFixedSpace L M B C n) (hCne : C ≠ ⊥)
    (hFN : F ≤ normalizer (B : Set G)) (hFC : F ≤ centralizer (C : Set G)) :
    (F ⊓ centralizer (B : Set G)).relIndex F ≤ 2 := by
  classical
  obtain ⟨t,_,htB,hC,hfield⟩ := hfield
  let f : F →* MulAut B := B.normalizerMonoidHom.comp (inclusion hFN)
  have hall (x : f.range) : x.val = 1 ∨ x.val = B.normalizerMonoidHom ⟨t,htB⟩ := by
    obtain ⟨r,hr⟩ := x.property
    rw [←hr]
    exact field_fixedSpace_actor_dichotomy hnat t htB hC hCne hfield
      ⟨r,hNL (hFN r.property)⟩ (hFN r.property) (hFC r.property)
  have hcard : Nat.card f.range ≤ 2 := by
    have hinj : Function.Injective (fun x : f.range => decide (x.val = 1)) := by
      intro x y he
      apply Subtype.ext
      have hx := hall x
      have hy := hall y
      by_cases hx1 : x.val = 1 <;> by_cases hy1 : y.val = 1 <;> simp_all
    exact (Nat.card_le_card_of_injective _ hinj).trans_eq (by simp : Nat.card Bool = 2)
  have hk : f.ker = (F ⊓ centralizer (B : Set G)).subgroupOf F := by
    ext x
    change B.normalizerMonoidHom ⟨x,hFN x.property⟩ = 1 ↔ _
    rw [←MonoidHom.mem_ker,normalizerMonoidHom_ker]
    exact ⟨fun hx => ⟨x.property,hx⟩,fun hx => hx.2⟩
  change ((F ⊓ centralizer (B : Set G)).subgroupOf F).index ≤ 2
  rw [←hk,index_ker]
  exact hcard

variable {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- The field planes of the first moving pair in 6.2.8. The containing
abelian closure is normalized by the opposite seed, as supplied by the
critical graph endpoints. Both planes retain the original conjugation. -/
theorem local_graph_pair_planes
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (g : G) (U : Subgroup G) [IsMulCommutative U]
    (hAU : (layer L R).map (MulAut.conj g).toMonoidHom ≤ U)
    (hBU : layer L R ≤ normalizer (U : Set G))
    (hi : ((layer L R).map (MulAut.conj g).toMonoidHom ⊓ normalizer (layer L R : Set G)).relIndex
      ((layer L R).map (MulAut.conj g).toMonoidHom) = 2)
    (hBnA : ¬ layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    let C := B ⊓ centralizer (A : Set G)
    let D := A ⊓ centralizer (B : Set G)
    ⁅A ⊓ normalizer (B : Set G),B⁆ = C ∧ Nat.card C = 4 ∧
      IsInvolutoryFieldFixedSpace L M B C n ∧ Nat.card D = 4 ∧
      IsInvolutoryFieldFixedSpace L M B (D.map (MulAut.conj g⁻¹).toMonoidHom) n := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let C := B ⊓ centralizer (A : Set G)
  let D := A ⊓ centralizer (B : Set G)
  let F := A ⊓ normalizer (B : Set G)
  let := h.layer_elementary
  have hB : Nat.card B = 16 := hnatural.2.1.card
  have hA : Nat.card A = 16 := (card_map_of_injective (MulAut.conj g).injective).trans hB
  have hlargeB := fun C hCB hCc => local_large_subgroup_centralizer h hnatural hE (U := C) hCB hCc
  have hlargeA := fun C hCA hCc => local_conjugate_large_subgroup_centralizer h hnatural hE g (U := C) hCA hCc
  obtain ⟨hcomm,hC⟩ := graph_pair_first_plane B A U hB hA hlargeB hlargeA hAU hBU hi hBnA
  change Nat.card C = 4 at hC
  have hAC : A ≤ centralizer (C : Set G) := le_centralizer_iff.mpr inf_le_right
  have hAN : ¬ A ≤ normalizer (B : Set G) := by
    intro hh
    rw [inf_eq_left.mpr hh,relIndex_self] at hi
    contradiction
  have hfield := local_escaping_plane_field h hnatural hE
    (show C ≤ B from inf_le_left) hC (fun hh => hAN (hAC.trans hh))
  have hF : Nat.card F = 8 := graph_half_card inf_le_left hA hi
  have hCne : C ≠ ⊥ := by intro he; rw [he,card_bot] at hC; omega
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hNL := hE.normalizer_le.trans
    ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal)
  have hidx := field_plane_actor_index hnat hNL hfield hCne
    (show F ≤ normalizer (B : Set G) from inf_le_right) (inf_le_left.trans hAC)
  have hker : F ⊓ centralizer (B : Set G) = D := by
    exact inf_assoc _ _ _ |>.trans (congrArg (fun X => A ⊓ X)
      (inf_eq_right.mpr (Subgroup.centralizer_le_normalizer _)))
  rw [hker] at hidx
  have hDF : D ≤ F := le_inf inf_le_left
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  have hDc := (D.subgroupOf F).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hDF).toEquiv] at hDc
  change Nat.card D * D.relIndex F = Nat.card F at hDc
  rw [hF] at hDc
  have hDlo : 4 ≤ Nat.card D := by nlinarith
  have hDsmall : Nat.card D < 8 := by
    by_contra hh
    have he := hlargeA D inf_le_left (Nat.le_of_not_gt hh)
    have hh : B ≤ centralizer (D : Set G) := le_centralizer_iff.mpr inf_le_right
    exact hBnA ((hh.trans_eq he).trans (Subgroup.centralizer_le_normalizer _))
  have hD : Nat.card D = 4 := le_antisymm
    (small_subgroup_card (show D ≤ A from inf_le_left) hA hDsmall) hDlo
  let E := D.map (MulAut.conj g⁻¹).toMonoidHom
  have hEeq : E = B ⊓ centralizer (B.map (MulAut.conj g⁻¹).toMonoidHom : Set G) :=
    fusion_pullback_centralizer B g
  have hEc : Nat.card E = 4 := (card_map_of_injective (MulAut.conj g⁻¹).injective).trans hD
  have hback : ¬ B.map (MulAut.conj g⁻¹).toMonoidHom ≤ normalizer (B : Set G) := by
    intro hh
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hh
    rw [map_equiv_normalizer_eq,show (B.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = B from by simpa using fusion_map_conj_inverse B g⁻¹] at hm
    exact hBnA hm
  have hEfield := local_escaping_plane_field h hnatural hE
    (hEeq.le.trans inf_le_left) hEc (fun hh => hback ((le_centralizer_iff.mpr
      (hEeq.le.trans inf_le_right)).trans hh))
  exact ⟨hcomm,hC,hfield,hD,hEfield⟩

/-- Transport both field planes to two literal conjugates of the source
layer. The displayed inverse conjugations specify their field coordinates. -/
theorem local_conjugate_graph_pair_planes
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (a b : G) (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hYU : (layer L R).map (MulAut.conj b).toMonoidHom ≤ U)
    (hXU : (layer L R).map (MulAut.conj a).toMonoidHom ≤ normalizer (U : Set G))
    (hi : ((layer L R).map (MulAut.conj b).toMonoidHom ⊓
        normalizer ((layer L R).map (MulAut.conj a).toMonoidHom : Set G)).relIndex
      ((layer L R).map (MulAut.conj b).toMonoidHom) = 2)
    (hXnY : ¬ (layer L R).map (MulAut.conj a).toMonoidHom ≤
      normalizer ((layer L R).map (MulAut.conj b).toMonoidHom : Set G)) :
    let X := (layer L R).map (MulAut.conj a).toMonoidHom
    let Y := (layer L R).map (MulAut.conj b).toMonoidHom
    let C := X ⊓ centralizer (Y : Set G)
    let D := Y ⊓ centralizer (X : Set G)
    ⁅Y ⊓ normalizer (X : Set G),X⁆ = C ∧ Nat.card C = 4 ∧ Nat.card D = 4 ∧
      IsInvolutoryFieldFixedSpace L M (layer L R) (C.map (MulAut.conj a⁻¹).toMonoidHom) n ∧
      IsInvolutoryFieldFixedSpace L M (layer L R) (D.map (MulAut.conj b⁻¹).toMonoidHom) n := by
  let B := layer L R
  let X := B.map (MulAut.conj a).toMonoidHom
  let Y := B.map (MulAut.conj b).toMonoidHom
  let A := B.map (MulAut.conj (a⁻¹*b)).toMonoidHom
  let U' := U.map (MulAut.conj a⁻¹).toMonoidHom
  let C := X ⊓ centralizer (Y : Set G)
  let D := Y ⊓ centralizer (X : Set G)
  let _ : IsElementaryAbelian 2 U' := IsElementaryAbelian.map _
  have hAU : A ≤ U' := by
    have hh := map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hYU
    rwa [fusion_map_conj_mul] at hh
  have hBU : B ≤ normalizer (U' : Set G) := by
    have hh := map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hXU
    rwa [fusion_map_conj_inverse,map_equiv_normalizer_eq] at hh
  have hidx : (A ⊓ normalizer (B : Set G)).relIndex A = 2 := by
    have hh := relIndex_map_map_of_injective (f := (MulAut.conj a⁻¹).toMonoidHom)
      (Y ⊓ normalizer (X : Set G)) Y (MulAut.conj a⁻¹).injective
    change _ = (Y ⊓ normalizer (X : Set G)).relIndex Y at hh
    rw [hi,map_inf _ _ _ (MulAut.conj a⁻¹).injective,map_equiv_normalizer_eq] at hh
    dsimp only [X,Y] at hh
    rw [fusion_map_conj_inverse,fusion_map_conj_mul] at hh
    exact hh
  have hn : ¬ B ≤ normalizer (A : Set G) := by
    intro hh
    have hm := map_mono (f := (MulAut.conj a).toMonoidHom) hh
    rw [map_equiv_normalizer_eq] at hm
    have he : A.map (MulAut.conj a).toMonoidHom = Y := by
      dsimp only [A,Y]
      rw [fusion_map_conj_mul,mul_inv_cancel_left]
    rw [he] at hm
    exact hXnY hm
  obtain ⟨hcomm,hC,hfield,hD,hfieldD⟩ :=
    local_graph_pair_planes h hnatural hE (a⁻¹*b) U' hAU hBU hidx hn
  have hCm : C.map (MulAut.conj a⁻¹).toMonoidHom = B ⊓ centralizer (A : Set G) := by
    dsimp only [C,X,Y,A]
    rw [map_inf _ _ _ (MulAut.conj a⁻¹).injective,Theory.Quasithin.map_centralizer,
      fusion_map_conj_inverse,fusion_map_conj_mul]
  have hDm : D.map (MulAut.conj a⁻¹).toMonoidHom = A ⊓ centralizer (B : Set G) := by
    dsimp only [D,X,Y,A]
    rw [map_inf _ _ _ (MulAut.conj a⁻¹).injective,Theory.Quasithin.map_centralizer,
      fusion_map_conj_inverse,fusion_map_conj_mul]
  have hDback : (A ⊓ centralizer (B : Set G)).map (MulAut.conj (a⁻¹*b)⁻¹).toMonoidHom =
      D.map (MulAut.conj b⁻¹).toMonoidHom := by
    rw [←hDm,fusion_map_conj_mul]
    congr 2
    group
  refine ⟨?_,?_,?_,hCm.symm ▸ hfield,hDback ▸ hfieldD⟩
  · apply (map_injective (f := (MulAut.conj a⁻¹).toMonoidHom) (MulAut.conj a⁻¹).injective)
    rw [hCm,map_commutator,map_inf _ _ _ (MulAut.conj a⁻¹).injective,
      map_equiv_normalizer_eq]
    rw [fusion_map_conj_inverse,fusion_map_conj_mul]
    exact hcomm
  · have hc : Nat.card (C.map (MulAut.conj a⁻¹).toMonoidHom) = Nat.card C :=
      card_map_of_injective (MulAut.conj a⁻¹).injective
    rw [hCm] at hc
    exact hc.symm.trans hC
  · have hc : Nat.card (D.map (MulAut.conj a⁻¹).toMonoidHom) = Nat.card D :=
      card_map_of_injective (MulAut.conj a⁻¹).injective
    rw [hDm] at hc
    exact hc.symm.trans hD

private theorem graph_pair_common_point
    (B A : Subgroup G) (hB : Nat.card B = 16) (hA : Nat.card A = 16)
    (hlarge : ∀ C ≤ B, 8 ≤ Nat.card C → centralizer (C : Set G) = centralizer (B : Set G))
    (hleft : (B ⊓ normalizer (A : Set G)).relIndex B = 2)
    (hright : (A ⊓ normalizer (B : Set G)).relIndex A = 2)
    (hC : Nat.card (A ⊓ centralizer (B : Set G) : Subgroup G) = 4) :
    ∃ x ∈ B ⊓ A, x ≠ (1 : G) := by
  let E := B ⊓ normalizer (A : Set G)
  let F := A ⊓ normalizer (B : Set G)
  have hE : Nat.card E = 8 := graph_half_card inf_le_left hB hleft
  have hF : Nat.card F = 8 := graph_half_card inf_le_left hA hright
  have hcomm : ⁅F,E⁆ ≤ B ⊓ A := le_inf
    ((commutator_mono le_rfl (show E ≤ B from inf_le_left)).trans
      (le_normalizer_iff_commutator_le_right.mp (show F ≤ normalizer (B : Set G) from inf_le_right)))
    ((commutator_mono (show F ≤ A from inf_le_left) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (show E ≤ normalizer (A : Set G) from inf_le_right)))
  have hn : ⁅F,E⁆ ≠ ⊥ := by
    intro hh
    have hc := commutator_eq_bot_iff_le_centralizer.mp hh
    rw [hlarge E inf_le_left hE.ge] at hc
    have hh := card_le_of_le (le_inf (show F ≤ A from inf_le_left) hc)
    rw [hF,hC] at hh
    omega
  obtain ⟨x,hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hn
  exact ⟨x,hcomm x.property,fun he => hx (Subtype.ext he)⟩

/-- The source common point after the reverse index-two neighbor has been
selected. Its existence follows from hyperplane rigidity and the already
identified order-four centralizer, without an extra point hypothesis. -/
theorem local_conjugate_graph_pair_common_point
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (a b : G)
    (hleft : ((layer L R).map (MulAut.conj a).toMonoidHom ⊓
        normalizer ((layer L R).map (MulAut.conj b).toMonoidHom : Set G)).relIndex
      ((layer L R).map (MulAut.conj a).toMonoidHom) = 2)
    (hright : ((layer L R).map (MulAut.conj b).toMonoidHom ⊓
        normalizer ((layer L R).map (MulAut.conj a).toMonoidHom : Set G)).relIndex
      ((layer L R).map (MulAut.conj b).toMonoidHom) = 2)
    (hC : Nat.card ((layer L R).map (MulAut.conj b).toMonoidHom ⊓
      centralizer ((layer L R).map (MulAut.conj a).toMonoidHom : Set G) : Subgroup G) = 4) :
    ∃ x ∈ (layer L R).map (MulAut.conj a).toMonoidHom ⊓
      (layer L R).map (MulAut.conj b).toMonoidHom, x ≠ (1 : G) := by
  apply graph_pair_common_point _ _
    ((card_map_of_injective (MulAut.conj a).injective).trans hnatural.2.1.card)
    ((card_map_of_injective (MulAut.conj b).injective).trans hnatural.2.1.card)
    (fun C hCB hCc => local_conjugate_large_subgroup_centralizer h hnatural hE a hCB hCc)
    hleft hright hC

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
