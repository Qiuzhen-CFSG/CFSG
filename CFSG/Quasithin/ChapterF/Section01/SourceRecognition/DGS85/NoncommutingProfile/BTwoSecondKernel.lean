module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoAbelianSection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SecondKernel

/-!
# The second-kernel bound from the abelian supplement

The abelian supplement W acts transitively on the other beta neighbors.
An element of W in one opposite core therefore belongs to every neighboring
core. Two successive index bounds put a subgroup of order at least q_beta
squared in that intersection. The intersection is the embedded two-core of
the full radius-two kernel, by the source kernel-Sylow theorem.

Its conjugation description also proves normalization under the full
original beta parabolic: the reduced endpoint is normal there, and the
original Borel preserves the alpha core. All maps are the original inclusion.
The full kernel is never identified with its two-core.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.10)(d), printed p.165, with the kernel conventions on pp.71--75.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting
open CommutingOneProfile
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P

private theorem abelian_intersection_le_neighbor_cores
    {v m u : Vertex F} 
    (W : Subgroup G) [IsMulCommutative W] (hWQ : W≤Q F v)
    (htrans : ∀ z, (graph F).Adj m z → z≠v → ∃ g∈W, g • u=z) :
    W⊓Q F u≤neighborCoreIntersection F m := by
  intro x hx
  apply mem_iInf.mpr
  intro z
  by_cases hz : z.val=v
  · simpa only [hz] using hWQ hx.1
  obtain ⟨g,hg,hgz⟩ := htrans z z.property hz
  have hcomm : g*x=x*g := congrArg Subtype.val (mul_comm (⟨g,hg⟩:W) ⟨x,hx.1⟩)
  have hh := mem_map_of_mem (MulAut.conj g).toMonoidHom hx.2
  rw [←Q_translate,hgz] at hh
  simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,hcomm,mul_inv_cancel_right] using hh

private theorem neighbor_core_mem_iff {v m : Vertex F} (hvm : (graph F).Adj v m)
    (x : G) :
    x∈neighborCoreIntersection F m ↔ ∀ g∈stabilizer F m, g*x*g⁻¹∈Q F v := by
  constructor
  · intro hx g hg
    exact neighborCoreIntersection_le F hvm
      ((mem_normalizer_iff.mp (neighborCoreIntersection_normalized F m hg) x).mp hx)
  intro hx
  apply mem_iInf.mpr
  intro z
  obtain ⟨g,hg,hgz⟩ := locally_transitive F hvm.symm z.property
  have hh := mem_map_of_mem (MulAut.conj g).toMonoidHom (hx g⁻¹ ((stabilizer F m).inv_mem hg))
  rw [←Q_translate,hgz] at hh
  simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,mul_assoc,mul_inv_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hh

namespace Reduction
open DGS85.Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local notation "ι" => Subgroup.subtype (G₀ L S)

private theorem original_neighbor_core_mem_iff (h : HypothesisF11 L S) (x : G) :
    x∈(neighborCoreIntersection F₀ β).map ι ↔
      ∀ g∈P₀ L S 1, g*x*g⁻¹∈(parabolic L S 0).pCoreIn 2 := by
  have hab : (graph F₀).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hP : P₀ L S 1≤G₀ L S := le_sup_right
  have hQa : (Q F₀ α).map ι=(parabolic L S 0).pCoreIn 2 := reduced_base_Q_map h false
  constructor
  · rintro ⟨a,ha,rfl⟩ g hg
    have hg' : (⟨g,hP hg⟩:G₀ L S)∈stabilizer F₀ β := by
      rw [Subgroup.CosetGeometry.RankTwo.stabilizer,Subgroup.CosetGeometry.stabilizer_base]
      exact hg
    have hh := (neighbor_core_mem_iff hab a).mp ha _ hg'
    exact hQa ▸ mem_map_of_mem ι hh
  · intro hx
    have hxQ : x∈(parabolic L S 0).pCoreIn 2 := by simpa using hx 1 (one_mem _)
    have hxG : x∈G₀ L S := map_subtype_le (Q F₀ α) (hQa.symm ▸ hxQ)
    refine ⟨⟨x,hxG⟩,(neighbor_core_mem_iff hab _).mpr ?_,rfl⟩
    intro g hg
    have hg' : (g:G)∈P₀ L S 1 := by
      change g ∈ MulAction.stabilizer (G₀ L S) β at hg
      rw [Subgroup.CosetGeometry.stabilizer_base] at hg
      exact hg
    have hh := hx g hg'
    rw [←hQa] at hh
    exact (mem_map_iff_mem (G₀ L S).subtype_injective).mp hh

/-- The original full beta parabolic normalizes the mapped neighboring-core
intersection, hence the two-core of the literal second ball kernel. -/
theorem original_second_core_normalized (h : HypothesisF11 L S) :
    parabolic L S 1≤normalizer
      ((neighborCoreIntersection F₀ β).map ι:Set G) := by
  let I := (neighborCoreIntersection F₀ β).map ι
  have hs : P₀ L S 1⊔commonBorel L S=parabolic L S 1 := by
    rw [P₀,sup_assoc,sup_eq_right.mpr (B₀_le h)]
    exact h.starredParabolic_supplement 1
  rw [←hs]
  apply sup_le
  · have hh := (map_mono (f:=ι) (neighborCoreIntersection_normalized F₀ β)).trans
      (le_normalizer_map ι)
    have he : (stabilizer F₀ β).map ι=P₀ L S 1 := by
      rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base]
      exact map_subgroupOf_eq_of_le le_sup_right
    rwa [he] at hh
  · apply le_normalizer_iff.mpr
    intro g hg x hx
    apply (original_neighbor_core_mem_iff h _).mpr
    intro a ha
    have hnP := (normal_subgroupOf_iff_le_normalizer (P₀_le h 1)).mp (P₀_normal h 1)
    have ha' : g⁻¹*a*g∈P₀ L S 1 := by
      simpa only [inv_inv] using (mem_normalizer_iff.mp
        (hnP (commonBorel_le_parabolic 1 ((commonBorel L S).inv_mem hg))) a).mp ha
    have hqa := (original_neighbor_core_mem_iff h x).mp hx _ ha'
    have hnQ : commonBorel L S≤normalizer ((parabolic L S 0).pCoreIn 2:Set G) :=
      (commonBorel_le_parabolic 0).trans ((parabolic L S 0).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
    have hh := (mem_normalizer_iff.mp (hnQ hg) _).mp hqa
    convert hh using 1
    simp [mul_assoc]

/-- The abelian supplement forces a noncentral part of the full second-kernel
two-core. Both original endpoint maps and the full beta normalizer are retained. -/
theorem original_abelian_supplement_second_core_bound
    (h : HypothesisF11 L S) {u t : Vertex F₀}
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆≠⊥)
    (hb : b F₀=2) (hβu : (graph F₀).Adj β u)
    (ht : (graph F₀).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F₀ t).map ι≠(Z F₀ α).map ι)
    (heq : Nat.card (K false)=Nat.card (K true))
    (W₀ : Subgroup G) [IsMulCommutative W₀]
    (hWcard : Nat.card W₀=Nat.card (K true)^4)
    (hWsup : W₀⊔((parabolic L S 1).pCoreIn 2⊓(Q F₀ t).map ι)=
      (parabolic L S 0).pCoreIn 2) :
    Nat.card (K true)^2≤Nat.card ((ballKernel F₀ β 2).pCoreIn 2) := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F₀ i) := finite_endpoints H
  have hab : (graph F₀).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have hQa : (Q F₀ α).map ι=(parabolic L S 0).pCoreIn 2 := reduced_base_Q_map h false
  have hQb : (Q F₀ β).map ι=(parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
  have hDm : (D F₀ β t).map ι=(parabolic L S 1).pCoreIn 2⊓(Q F₀ t).map ι := by
    rw [D,map_inf _ _ _ (G₀ L S).subtype_injective,hQb]
  let W := W₀.subgroupOf (G₀ L S)
  have hWQa : W₀≤(parabolic L S 0).pCoreIn 2 := hWsup ▸ le_sup_left
  have hWm : W.map ι=W₀ := map_subgroupOf_eq_of_le
    (hWQa.trans (hQa.symm ▸ map_subtype_le _))
  have hWQ : W≤Q F₀ α := by
    apply (map_le_map_iff_of_injective (f:=ι) (G₀ L S).subtype_injective).mp
    rwa [hWm,hQa]
  have hWD : W⊔D F₀ β t=Q F₀ α := by
    apply map_injective (G₀ L S).subtype_injective
    rwa [Subgroup.map_sup,hWm,hDm,hQa]
  have hWc : Nat.card W=Nat.card (K true)^4 := by
    rw [←card_map_of_injective (f:=ι) (G₀ L S).subtype_injective,hWm,hWcard]
  let J := Q F₀ α⊓Q F₀ β
  obtain ⟨_,hDQ,_,_,_,hDc,hQac,hQbc,_⟩ := original_bTwo_strict_core_orders h hc hne hb hβu ht htne K e hD
  have hDQ' : D F₀ β t≤Q F₀ α := by
    apply (map_le_map_iff_of_injective (f:=ι) (G₀ L S).subtype_injective).mp
    rwa [hDm,hQa]
  have hDI : D F₀ β t≤J := le_inf hDQ' inf_le_left
  have hidx : (D F₀ β t).relIndex J=Nat.card (K true) := by
    have hh := (original_bTwo_linear_seed_and_indices h hb c ht htne
      (reduced_graph_core_obstruction h α β hab) (e true)).2.2
    have hm : J.map ι=(parabolic L S 0).pCoreIn 2⊓(parabolic L S 1).pCoreIn 2 := by
      rw [map_inf _ _ _ (G₀ L S).subtype_injective,hQa,hQb]
    rw [←hDm,←hm,relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective] at hh
    exact hh
  have hDc' : Nat.card (D F₀ β t)=Nat.card (K true)^3 := by
    rw [←card_map_of_injective (f:=ι) (G₀ L S).subtype_injective,hDm,hDc,heq]
    ring
  have hJc : Nat.card J=Nat.card (K true)^4 := by
    have hh := relIndex_mul_card_of_le hDI
    rw [hidx,hDc'] at hh
    calc Nat.card J = Nat.card (K true)*Nat.card (K true)^3 := hh.symm
         _ = _ := by ring
  have hQac' : Nat.card (Q F₀ α)=Nat.card (K true)^5 := by
    rw [←card_map_of_injective (f:=ι) (G₀ L S).subtype_injective,hQa,hQac,heq]
    ring
  have hQbc' : Nat.card (Q F₀ β)=Nat.card (K true)^5 := by
    rw [←card_map_of_injective (f:=ι) (G₀ L S).subtype_injective,hQb,hQbc,heq]
    ring
  have hindex (Q₀ : Subgroup (G₀ L S)) (hJQ : J≤Q₀) (hcard : Nat.card Q₀=Nat.card (K true)^5) :
      J.relIndex Q₀=Nat.card (K true) := by
    have hh := relIndex_mul_card_of_le hJQ
    rw [hJc,hcard] at hh
    apply Nat.eq_of_mul_eq_mul_right (Nat.pow_pos Nat.card_pos : 0<Nat.card (K true)^4)
    calc J.relIndex Q₀*Nat.card (K true)^4 = Nat.card (K true)^5 := hh
         _ = _ := by ring
  have hia : (Q F₀ β).relIndex (Q F₀ α)=Nat.card (K true) := by
    have hh := hindex _ inf_le_left hQac'
    rwa [inf_relIndex_left] at hh
  have hib : (Q F₀ α).relIndex (Q F₀ β)=Nat.card (K true) := by
    have hh := hindex _ inf_le_right hQbc'
    rwa [inf_relIndex_right] at hh
  have hiu : (Q F₀ u).relIndex (Q F₀ β)=Nat.card (K true) := by
    obtain ⟨a,ha,hau⟩ := locally_transitive F₀ hab.symm hβu
    have hh := relIndex_map_map_of_injective (f:=(MulAut.conj a).toMonoidHom)
      (Q F₀ α) (Q F₀ β) (MulAut.conj a).injective
    rw [←Q_translate,←Q_translate,hau,show a • β=β from ha] at hh
    exact hh.trans hib
  let A := W⊓Q F₀ β
  let T := A⊓Q F₀ u
  let : Finite (Q F₀ α) := Finite.of_injective (inclusion (Q_le_stabilizer F₀ α)) (inclusion_injective _)
  let : Finite W := Finite.of_injective (inclusion hWQ) (inclusion_injective _)
  let : Finite A := Finite.of_injective (inclusion (show A≤W from inf_le_left)) (inclusion_injective _)
  let : Finite T := Finite.of_injective (inclusion (show T≤A from inf_le_left)) (inclusion_injective _)
  have hiA : A.relIndex W≤Nat.card (K true) := by
    rw [inf_relIndex_left]
    exact (relIndex_le_of_le_right hWQ (hia ▸ Nat.ne_of_gt Nat.card_pos)).trans_eq hia
  have hiT : T.relIndex A≤Nat.card (K true) := by
    rw [inf_relIndex_left]
    exact (relIndex_le_of_le_right (show A≤Q F₀ β from inf_le_right)
      (hiu ▸ Nat.ne_of_gt Nat.card_pos)).trans_eq hiu
  have hiTW : T.relIndex W≤Nat.card (K true)^2 := by
    rw [←relIndex_mul_relIndex T A W inf_le_left inf_le_left,pow_two]
    exact Nat.mul_le_mul hiT hiA
  have hTc : Nat.card (K true)^2≤Nat.card T := by
    have hh := relIndex_mul_card_of_le (show T≤W from inf_le_left.trans inf_le_left)
    rw [hWc] at hh
    have hm : Nat.card (K true)^2*Nat.card (K true)^2≤Nat.card (K true)^2*Nat.card T := by
      calc Nat.card (K true)^2*Nat.card (K true)^2 = Nat.card (K true)^4 := by ring
           _ = T.relIndex W*Nat.card T := hh.symm
           _ ≤ _ := Nat.mul_le_mul_right _ hiTW
    exact Nat.le_of_mul_le_mul_left hm (Nat.pow_pos Nat.card_pos)
  have hWgen : W⊔Q F₀ β=(stabilizer F₀ α⊓stabilizer F₀ β).pCoreIn 2 := by
    have he : Q F₀ β⊔Q F₀ α=(stabilizer F₀ β⊓stabilizer F₀ α).pCoreIn 2 :=
      c.core_product_eq_edge_core H
    calc W⊔Q F₀ β = (W⊔D F₀ β t)⊔Q F₀ β := by
           rw [sup_assoc,sup_eq_right.mpr (show D F₀ β t≤Q F₀ β from inf_le_left)]
         _ = Q F₀ α⊔Q F₀ β := by rw [hWD]
         _ = _ := by rw [sup_comm,he,inf_comm]
  have htrans : ∀ z, (graph F₀).Adj β z → z≠α → ∃ a∈W, a • u=z := by
    intro z hz hzne
    have hua : u≠α := by
      intro he
      subst u
      have hh := hc.1
      rw [SimpleGraph.dist_self,hb] at hh
      omega
    let eb := (e true).trans (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL (K true)).symm
    obtain ⟨a,ha,haz⟩ := CommutingThreeProfile.ReducedLayer.linear_incident_core_transitive
      h true eb hab.symm hβu hz hua hzne
    have hn : W≤normalizer (Q F₀ β:Set (G₀ L S)) :=
      (hWQ.trans ((source_Z_Q_U H α).2.trans ((ballKernel_one_le_edge F₀ hab).trans inf_le_right))).trans
        (CommutingNontrivial.stabilizer_normalizes_Q F₀ β)
    have hm : a∈(W:Set (G₀ L S))*(Q F₀ β:Set (G₀ L S)) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ hn,hWgen]
      exact ha
    obtain ⟨w,hw,y,hy,hwy⟩ := hm
    have hyu : y • u=u := (source_Z_Q_U H β).2 hy u ((mem_ball_one F₀ β u).mpr (Or.inl hβu))
    exact ⟨w,hw,by rwa [←hwy,mul_smul,hyu] at haz⟩
  have hTI : T≤neighborCoreIntersection F₀ β :=
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans
      (abelian_intersection_le_neighbor_cores W hWQ htrans)
  rw [←reduced_neighborCoreIntersection_eq_second_core h hab]
  let : Finite (neighborCoreIntersection F₀ β) :=
    Finite.of_injective (inclusion (neighborCoreIntersection_le F₀ hab)) (inclusion_injective _)
  exact hTc.trans (card_le_of_le hTI)

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
