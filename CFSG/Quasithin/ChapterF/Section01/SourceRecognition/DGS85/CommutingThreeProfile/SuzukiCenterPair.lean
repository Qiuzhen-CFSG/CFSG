module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanFixedIndex
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanFixedIndex

public import Theory.GroupTheory.CentralizerInjectiveImage
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanPair

/-!
# Two critical centers at a nonbinary Suzuki endpoint

On the critical path a--x--m--y, transport the proved intersection indices
through the linear neighbor action. This gives [V_y : V_y ∩ Q_a] ≤ q²;
two conjugate centers therefore have common-centralizer index at most q⁴.

The image of Z_a in the Suzuki quotient is central in the image Sylow Q_m.
Consequently Q_m normalizes Z_a Q_y. Its transitivity on the neighbors of
x other than m then proves V_x Q_y = Z_a Q_y. Applying this to the existing
two-span generation constructs two actual critical centers generating the
starred endpoint modulo Q_y. The final theorem combines this generation
with the q⁴ bound, also after the original completion inclusion.

The Suzuki and linear markings, common parameter and common Sylows are
retained earlier-source inputs. These results provide the geometric
center-pair step of (12.6); they do not assert Suzuki selection, identify
the full second kernel, or identify the endpoint-fixed subgroup with Z_y.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.1), (12.3), (12.5)--(12.6), printed pp.178--183.
The implementation import reuses the private linear neighbor swap within
this source family without changing its public interface.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual critical center has fixed index at most q² in the opposite span. -/
theorem source_suzuki_center_seed_index
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    {n : ℕ} (hn : 0 < n) (hq : Nat.card k = 2^(2*n+1))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      SL(2,k))
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    (Q F a).relIndex (V F (base F i) 1) ≤ (2^(2*n+1))^2 ∧
      (centralizer (Z F a : Set (G₀ L S))).relIndex (V F (base F i) 1) ≤
        (2^(2*n+1))^2 := by
  let F := reducedFamily L S
  let y := base F i
  let m := base F (!i)
  let Vy := V F y 1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite Vy := Finite.of_injective (inclusion
    ((V_le_Q F (reduced_triple h).generate
      (fun z => (source_Z_Q_U (reduced_triple h) z).1) (reduced_kernel_sylow h) hb y).trans
        (Q_le_stabilizer F y))) (inclusion_injective _)
  let : Finite (Q F x) := Finite.of_injective (inclusion (Q_le_stabilizer F x))
    (inclusion_injective _)
  have hadj : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hxy : x ≠ y := by
    intro he
    have hs := (Z_neighbor_le_V F hxa).trans (V_le_Q F (reduced_triple h).generate
      (fun z => (source_Z_Q_U (reduced_triple h) z).1) (reduced_kernel_sylow h) hb x)
    rw [he] at hs
    exact hc.2 (hs.trans (source_Z_Q_U (reduced_triple h) y).2)
  obtain ⟨g,hgm,hgx,hgy⟩ := linear_neighbor_swap h (!i) eLin hxm.symm hadj.symm hxy
  have hfirst : (Q F x).relIndex Vy = 2^(2*n+1) := by
    have hi := (source_suzuki_first_index h i hb hc hxa hxm hadj hn eSuz eLin R hR).1
    rw [inf_relIndex_left] at hi
    have hh := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) (Q F y) (V F x 1) (MulAut.conj g).injective
    rw [←Q_translate F,←V_translate F,hgy,hgx] at hh
    exact hh.trans hi
  obtain ⟨P,_,hi,_⟩ := source_common_sylow_core_index h (!i) eLin T hT
  have hlin : (Q F m).relIndex (Q F x) = 2^(2*n+1) := by
    rw [inf_relIndex_left] at hi
    exact hi.trans ((Nat.card_congr
      (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 P).symm.toEquiv).trans hq)
  obtain ⟨t,ht,hta⟩ := locally_transitive F hxm hxa
  have htx : t • x = x := ht
  have hlast : (Q F a).relIndex (Q F x) = 2^(2*n+1) := by
    have hh := relIndex_map_map_of_injective (f := (MulAut.conj t).toMonoidHom) (Q F m) (Q F x) (MulAut.conj t).injective
    rw [←Q_translate F,←Q_translate F,hta,htx] at hh
    exact hh.trans hlin
  have hbound : (Q F a).relIndex Vy ≤ (2^(2*n+1))^2 := by
    have hsmall : (Q F a).relIndex (Q F x ⊓ Vy) ≤ 2^(2*n+1) :=
      (relIndex_le_of_le_right inf_le_left
        (show (Q F a).relIndex (Q F x) ≠ 0 from index_ne_zero_of_finite)).trans_eq hlast
    have hh : (Q F a ⊓ Q F x).relIndex Vy ≤ (2^(2*n+1))^2 := by
      rw [←relIndex_inf_mul_relIndex, hfirst,pow_two]
      exact Nat.mul_le_mul_right _ hsmall
    exact (relIndex_le_of_le_left inf_le_left
      (show (Q F a ⊓ Q F x).relIndex Vy ≠ 0 from index_ne_zero_of_finite)).trans hh
  refine ⟨hbound,?_⟩
  have hcentral : Q F a ≤ centralizer (Z F a : Set (G₀ L S)) :=
    le_centralizer_iff.mp (Z_centralizes_Q F a (source_Z_Q_U (reduced_triple h) a).1)
  exact (relIndex_le_of_le_left hcentral
    (show (Q F a).relIndex Vy ≠ 0 from index_ne_zero_of_finite)).trans hbound


/-- Two conjugate centers have common-centralizer index at most q⁴, in both completions. -/
theorem source_suzuki_center_pair_upper
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    {n : ℕ} (hn : 0 < n) (hq : Nat.card k = 2^(2*n+1))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      SL(2,k))
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    ∀ g ∈ stabilizer F (base F i),
      let E := Z F a ⊔ Z F (g • a)
      let D := V F (base F i) 1
      (centralizer (E : Set (G₀ L S))).relIndex D ≤ (2^(2*n+1))^4 ∧
        (centralizer (E.map (G₀ L S).subtype : Set G)).relIndex
          (D.map (G₀ L S).subtype) ≤ (2^(2*n+1))^4 := by
  let F := reducedFamily L S
  let y := base F i
  let D := V F y 1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hi := (source_suzuki_center_seed_index h i hb hc hxa hxm hn hq eSuz eLin T hT R hR).2
  dsimp only
  intro g hg
  let f := (MulAut.conj g).toMonoidHom
  let C := D ⊓ centralizer (Z F a : Set (G₀ L S))
  have hD : D.map f = D := mem_normalizer_iff_map_conj_eq.mp
    (stabilizer_normalizes_V F y 1 hg)
  have hC : D ⊓ centralizer (Z F (g • a) : Set (G₀ L S)) = C.map f := by
    rw [Z_translate,←hD]
    exact map_inf_centralizer_of_injective f (MulAut.conj g).injective D (Z F a)
  have hi' : (centralizer (Z F (g • a) : Set (G₀ L S))).relIndex D ≤ (2^(2*n+1))^2 := by
    rw [←inf_relIndex_left, hC, ←hD, relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
      inf_relIndex_left]
    exact hi
  have hcent : centralizer ((Z F a ⊔ Z F (g • a) : Subgroup (G₀ L S)) : Set (G₀ L S)) =
      centralizer (Z F a : Set (G₀ L S)) ⊓ centralizer (Z F (g • a) : Set (G₀ L S)) := by
    apply le_antisymm
    · exact le_inf (centralizer_le (show Z F a ≤ Z F a ⊔ Z F (g • a) from le_sup_left))
        (centralizer_le (show Z F (g • a) ≤ Z F a ⊔ Z F (g • a) from le_sup_right))
    · apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)
  have hupper : (centralizer ((Z F a ⊔ Z F (g • a) : Subgroup (G₀ L S)) : Set (G₀ L S))).relIndex D ≤
      (2^(2*n+1))^4 := by
    rw [hcent]
    exact relIndex_inf_le.trans ((Nat.mul_le_mul hi hi').trans_eq (by ring))
  refine ⟨hupper,?_⟩
  rw [←inf_relIndex_left, map_inf_centralizer_of_injective _ (G₀ L S).subtype_injective,
    relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective, inf_relIndex_left]
  exact hupper


/-- A critical center and its neighboring span have the same image modulo Q_y. -/
theorem source_suzuki_critical_center_saturation
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      SL(2,k))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    V F x 1 ⊔ Q F (base F i) = Z F a ⊔ Q F (base F i) := by
  let F := reducedFamily L S
  let y := base F i
  let m := base F (!i)
  let A := star L S i
  let Vx := V F x 1
  let D := Q F y
  let H := Z F a ⊔ D
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun z => (source_Z_Q_U (reduced_triple h) z).1
  have hSyl := reduced_kernel_sylow h
  have hadj : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hVm : Vx ≤ Q F m := V_le_neighbor_Q F (reduced_triple h).generate hZ hSyl hb hxm
  have hQA : Q F m ≤ A := (le_sup_left.trans hR.ge).trans (map_subtype_le _)
  have hVA : Vx ≤ A := hVm.trans hQA
  have hZA : Z F a ≤ A := (Z_neighbor_le_V F hxa).trans hVA
  have hDA : D ≤ A := (le_sup_right.trans hR.ge).trans (map_subtype_le _)
  let f := ((originalQuotient h i).symm.trans eSuz).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 A))
  have hk : f.ker = pCore 2 A := by
    ext v
    change eSuz ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) v)) = 1 ↔ v ∈ pCore 2 A
    rw [map_eq_one_iff _ eSuz.injective,map_eq_one_iff _ (originalQuotient h i).symm.injective]
    exact QuotientGroup.eq_one_iff v
  let E := ((Z F a).subgroupOf A).map f
  have hH : (E.comap f).map A.subtype = H := by
    rw [comap_map_eq,Subgroup.map_sup,map_subgroupOf_eq_of_le hZA,hk]
    change Z F a ⊔ A.pCoreIn 2 = H
    rw [star_core h i]
  obtain ⟨P,hP,_,_⟩ := source_common_sylow_core_index h i eSuz R hR
  have hEP : E ≤ P := by
    rw [←hP]
    exact map_mono (subgroupOf_mono A ((Z_neighbor_le_V F hxa).trans hVm))
  let := Z_elementary F hZ a
  let : IsElementaryAbelian 2 ((Z F a).subgroupOf A) := IsElementaryAbelian.subgroupOf hZA
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map f
  have hEZ : E ≤ (center P).map (P : Subgroup (SuzukiMatrixGroup n)).subtype := by
    rw [←suzukiSylow_omega_eq_center hn (MulEquiv.refl _) P,←omegaOneAmbient_eq_self E]
    exact omegaOneAmbient_mono hEP
  have hPC : (P : Subgroup (SuzukiMatrixGroup n)) ≤ centralizer (E : Set _) := by
    apply le_centralizer_iff.mpr
    rintro e he p hp
    obtain ⟨z,hz,rfl⟩ := hEZ he
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨p,hp⟩)
  have hnH : Q F m ≤ normalizer (H : Set (G₀ L S)) := by
    intro q hq
    let qA : A := ⟨q,hQA hq⟩
    have hP' : ((Q F m).subgroupOf A).map f = (P : Subgroup (SuzukiMatrixGroup n)) := hP
    have hqP : f qA ∈ P := hP'.le
      (mem_map_of_mem f (show qA ∈ (Q F m).subgroupOf A from hq))
    have hn : qA ∈ normalizer (E.comap f : Set A) :=
      le_normalizer_comap f (show qA ∈ (normalizer (E : Set (SuzukiMatrixGroup n))).comap f from
        Subgroup.centralizer_le_normalizer (E : Set (SuzukiMatrixGroup n)) (hPC hqP))
    have hh := (E.comap f).le_normalizer_map A.subtype (mem_map_of_mem A.subtype hn)
    rwa [hH] at hh
  have hxy : x ≠ y := by
    intro he
    have hh := (Z_neighbor_le_V F hxa).trans (V_le_Q F (reduced_triple h).generate hZ hSyl hb x)
    rw [he] at hh
    exact hc.2 (hh.trans (source_Z_Q_U (reduced_triple h) y).2)
  have ham : a ≠ m := by
    intro he
    have hh := (Z_neighbor_le_V F hadj).trans (V_le_Q F (reduced_triple h).generate hZ hSyl hb y)
    exact hc.2 (he ▸ hh.trans (source_Z_Q_U (reduced_triple h) y).2)
  obtain ⟨g,hgm,hgx,hgy⟩ := linear_neighbor_swap h (!i) eLin hxm.symm hadj.symm hxy
  have hgm' : g • m = m := hgm
  have horbit : ∀ z, (graph F).Adj x z → z ≠ m → ∃ t ∈ Q F m, t • a = z := by
    intro z hz hzm
    have hga : (graph F).Adj y (g • a) := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hxa
      change (graph F).Adj (g • x) (g • a) at hh
      rwa [hgx] at hh
    have hgz : (graph F).Adj y (g • z) := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hz
      change (graph F).Adj (g • x) (g • z) at hh
      rwa [hgx] at hh
    obtain ⟨t,ht,hatz⟩ := suzuki_neighbor_core_transitive h i hn eSuz R hR hga hgz
      (fun he => ham ((MulAction.injective g) (he.trans hgm'.symm)))
      (fun he => hzm ((MulAction.injective g) (he.trans hgm'.symm)))
    refine ⟨g⁻¹*t*g,?_,?_⟩
    · have hh := (mem_normalizer_iff.mp
        (((stabilizer F m).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F m))))
          ((stabilizer F m).inv_mem hgm)) t).mp ht
      change g⁻¹ * t * (g⁻¹)⁻¹ ∈ Q F m at hh
      simpa only [inv_inv] using hh
    · rw [mul_smul,mul_smul,hatz,inv_smul_smul]
  have hV : Vx ≤ H := by
    apply iSup_le
    intro z
    apply iSup_le
    intro hz
    rcases (mem_ball_one F x z).mp hz with hz | rfl
    · by_cases hzm : z = m
      · subst z
        exact ((Z_neighbor_le_V F hadj).trans
          (V_le_Q F (reduced_triple h).generate hZ hSyl hb y)).trans le_sup_right
      · obtain ⟨t,ht,htz⟩ := horbit z hz hzm
        have hh := map_mono (f := (MulAut.conj t).toMonoidHom)
          (show Z F a ≤ H from le_sup_left)
        have hHt : H.map (MulAut.conj t).toMonoidHom = H :=
          mem_normalizer_iff_map_conj_eq.mp (hnH ht)
        rw [←Z_translate F,htz,hHt] at hh
        exact hh
    · exact ((Z_neighbor_le_V F hxm.symm).trans
        (V_le_neighbor_Q F (reduced_triple h).generate hZ hSyl hb hadj.symm)).trans le_sup_right
  exact le_antisymm (sup_le hV le_sup_right)
    (sup_le_sup (Z_neighbor_le_V F hxa) le_rfl)


/-- Construct the source pair of centers and its geometric q⁴ bound. -/
theorem source_suzuki_center_pair
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    {n : ℕ} (hn : 0 < n) (hq : Nat.card k = 2^(2*n+1))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      SL(2,k))
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    ∃ g ∈ star L S i,
      (Z F a ⊔ Z F (g • a)) ⊔ Q F (base F i) = star L S i ∧
      (centralizer (↑(Z F a ⊔ Z F (g • a)) : Set (G₀ L S))).relIndex
        (V F (base F i) 1) ≤ (2^(2*n+1))^4 ∧
      (centralizer ((Z F a ⊔ Z F (g • a)).map (G₀ L S).subtype : Set G)).relIndex
        ((V F (base F i) 1).map (G₀ L S).subtype) ≤ (2^(2*n+1))^4 := by
  let F := reducedFamily L S
  let y := base F i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hadj : (graph F).Adj y (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hs := source_suzuki_critical_center_saturation h i hb hc hxa hxm hn eSuz eLin R hR
  obtain ⟨g,hg,hgen⟩ := source_suzuki_span_pair_generation h i hb hc hxa hxm hadj hn eSuz eLin R hR
  have hgy : g • y = y := star_le_stabilizer i hg
  have hs' := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hs
  rw [Subgroup.map_sup,Subgroup.map_sup,←V_translate F,←Z_translate F,←Q_translate F,hgy] at hs'
  have he : (Z F a ⊔ Z F (g • a)) ⊔ Q F y = star L S i := by
    calc
      _ = (Z F a ⊔ Q F y) ⊔ (Z F (g • a) ⊔ Q F y) := by
        rw [sup_sup_sup_comm, sup_idem]
      _ = (V F x 1 ⊔ Q F y) ⊔ (V F (g • x) 1 ⊔ Q F y) := by rw [←hs,←hs']
      _ = (V F x 1 ⊔ V F (g • x) 1) ⊔ Q F y := by
        rw [sup_sup_sup_comm, sup_idem]
      _ = _ := hgen
  exact ⟨g,hg,he,source_suzuki_center_pair_upper h i hb hc hxa hxm hn hq eSuz eLin T hT R hR
    g (star_le_stabilizer i hg)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
