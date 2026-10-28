module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearCoreOrbit
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiEscapingCentralizer
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiEscapingCentralizer

/-!
# Linear transitivity of the two conjugated source intersections

A subgroup of an incoming core whose image has order q in the literal
SL₂(q) quotient has the same image as the full incoming Sylow. For two
distinct neighbors these Sylow images generate the starred endpoint.
The vertex core fixes every neighbor, so the two subgroups themselves
act transitively on the neighborhood. A single edge conjugation carries
both subgroups, their indices and their actions to an arbitrary vertex.

The last theorem applies this to the two conjugated span--core intersections
in the untrapped branch of (12.7). It retains the exact second indices from
(12.3)(a) and the actual conjugators fixing their opposite vertices.
SuzukiUntrappedExclusion constructs those conjugators on the original
nine-path and applies the faithful-graph contradiction. The implementation
import reuses the existing private starred-supplement orbit lemma without
altering its public boundary.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.3)(a), (12.7), printed pp.179,184.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem linear_full_index_sup_core
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    {x : Vertex (reducedFamily L S)}
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (D : Subgroup (G₀ L S)) (hD : D ≤ Q (reducedFamily L S) x)
    (hi : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex D = Nat.card k) :
    D ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i) =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i) := by
  let F := reducedFamily L S
  let P := star L S i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite P := Finite.of_injective (inclusion (star_le_stabilizer i)) (inclusion_injective _)
  let f := ((originalQuotient h i).symm.trans e).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P))
  have hk : f.ker = (Q F (base F i)).subgroupOf P := by
    have he : f.ker = pCore 2 P := by
      ext t
      change e ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 P) t)) = 1 ↔ t ∈ pCore 2 P
      rw [map_eq_one_iff _ e.injective,map_eq_one_iff _ (originalQuotient h i).symm.injective]
      exact QuotientGroup.eq_one_iff t
    rw [he,←star_core h i]
    exact (comap_map_eq_self_of_injective P.subtype_injective _).symm
  have hxP : Q F x ≤ P := (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  have hyP : Q F (base F i) ≤ P := (le_sup_right.trans hT.ge).trans (map_subtype_le _)
  have hDP := hD.trans hxP
  obtain ⟨R,hR,_,_⟩ := source_common_sylow_core_index h i e T hT
  have hc : Nat.card ((D.subgroupOf P).map f) = Nat.card k := by
    rw [←relIndex_ker,hk,relIndex_subgroupOf hDP]
    exact hi
  have he : (D.subgroupOf P).map f = ((Q F x).subgroupOf P).map f := by
    apply eq_of_le_of_card_ge (map_mono (subgroupOf_mono P hD))
    rw [hc,hR]
    exact (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 R).toEquiv).ge
  have hh := congrArg (Subgroup.comap f) he
  rw [comap_map_eq,comap_map_eq,hk] at hh
  have hm := congrArg (Subgroup.map P.subtype) hh
  rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hDP,
    map_subgroupOf_eq_of_le hxP,map_subgroupOf_eq_of_le hyP] at hm
  exact hm

/-- Two subgroups with full linear root images at distinct neighbors are
transitive at the middle vertex. -/
theorem linear_full_index_pair_transitive
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    {w : Vertex (reducedFamily L S)}
    (hw : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) w)
    (hne : w ≠ base (reducedFamily L S) (!i))
    (D E : Subgroup (G₀ L S))
    (hD : D ≤ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hE : E ≤ Q (reducedFamily L S) w)
    (hiD : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex D = Nat.card k)
    (hiE : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex E = Nat.card k) :
    ∀ z, (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z →
      ∃ g ∈ D ⊔ E, g • base (reducedFamily L S) (!i) = z := by
  let F := reducedFamily L S
  let P := star L S i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite P := Finite.of_injective (inclusion (star_le_stabilizer i)) (inclusion_injective _)
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨g,hg,hgw⟩ := star_locally_transitive h i hadj hw
  have hgi : g • base F i = base F i := star_le_stabilizer i hg
  let R := T.mapSurjective (f := (MulAut.conj (⟨g,hg⟩ : P)).toMonoidHom)
    (MulAut.conj (⟨g,hg⟩ : P)).surjective
  have hf : P.subtype.comp (MulAut.conj (⟨g,hg⟩ : P)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp P.subtype := by ext u; rfl
  have hR : (R : Subgroup P).map P.subtype = Q F w ⊔ Q F (base F i) := by
    change ((T : Subgroup P).map _).map P.subtype = _
    rw [Subgroup.map_map,hf,←Subgroup.map_map,hT,Subgroup.map_sup,←Q_translate F,←Q_translate F,hgw,hgi]
  have hgen : (D ⊔ E) ⊔ Q F (base F i) = P := by
    calc
      (D ⊔ E) ⊔ Q F (base F i) =
          (D ⊔ Q F (base F i)) ⊔ (E ⊔ Q F (base F i)) := by ac_rfl
      _ = (Q F (base F (!i)) ⊔ Q F (base F i)) ⊔ (Q F w ⊔ Q F (base F i)) := by
        rw [linear_full_index_sup_core h i e T hT D hD hiD,
          linear_full_index_sup_core h i e R hR E hE hiE]
      _ = P := by
        have hh := star_three_core_generation h i hw hne T R hT hR
        calc
          _ = (Q F (base F (!i)) ⊔ Q F w) ⊔ (Q F (base F i) ⊔ Q F (base F i)) := by ac_rfl
          _ = P := by rw [sup_idem]; exact hh.symm
  exact fun z hz => star_supplement_transitive h i (D ⊔ E) hgen hz


/-- The same two-root argument at any linear vertex, using one common
transport for both subgroups, their cores, and their original action. -/
theorem linear_full_index_pair_transitive_at
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    {u v w : Vertex (reducedFamily L S)} (hu : u.type = i)
    (hv : (graph (reducedFamily L S)).Adj u v)
    (hw : (graph (reducedFamily L S)).Adj u w) (hne : w ≠ v)
    (D E : Subgroup (G₀ L S))
    (hD : D ≤ Q (reducedFamily L S) v) (hE : E ≤ Q (reducedFamily L S) w)
    (hiD : (Q (reducedFamily L S) u).relIndex D = Nat.card k)
    (hiE : (Q (reducedFamily L S) u).relIndex E = Nat.card k) :
    ∀ z, (graph (reducedFamily L S)).Adj u z → ∃ g ∈ D ⊔ E, g • v = z := by
  let F := reducedFamily L S
  obtain ⟨a,ha,hav⟩ := incident_common_translate F hv.2
  have ht : v.type = !i := Bool.eq_not_iff.mpr (hu ▸ hv.1.symm)
  rw [hu] at ha
  rw [ht] at hav
  have hau : a⁻¹ • u = base F i := by rw [←ha,inv_smul_smul]
  have hai : a⁻¹ • v = base F (!i) := by rw [←hav,inv_smul_smul]
  let c := (MulAut.conj a⁻¹).toMonoidHom
  have hD' : D.map c ≤ Q F (base F (!i)) := by
    have hh := map_mono (f := c) hD
    change D.map c ≤ (Q F v).map (MulAut.conj a⁻¹).toMonoidHom at hh
    rwa [←Q_translate F,hai] at hh
  have hE' : E.map c ≤ Q F (a⁻¹ • w) := by
    have hh := map_mono (f := c) hE
    change E.map c ≤ (Q F w).map (MulAut.conj a⁻¹).toMonoidHom at hh
    rwa [←Q_translate F] at hh
  have hi (A : Subgroup (G₀ L S)) (hA : (Q F u).relIndex A = Nat.card k) :
      (Q F (base F i)).relIndex (A.map c) = Nat.card k := by
    have hh := relIndex_map_map_of_injective (Q F u) A (f := c) (MulAut.conj a⁻¹).injective
    change ((Q F u).map (MulAut.conj a⁻¹).toMonoidHom).relIndex (A.map c) = _ at hh
    rw [←Q_translate F,hau] at hh
    exact hh.trans hA
  have hadj {z : Vertex F} (hz : (graph F).Adj u z) :
      (graph F).Adj (base F i) (a⁻¹ • z) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F a⁻¹).map_adj_iff.mpr hz
    change (graph F).Adj (a⁻¹ • u) (a⁻¹ • z) at hh
    rwa [hau] at hh
  have hne' : a⁻¹ • w ≠ base F (!i) := by
    rw [←hai]
    exact fun he => hne ((MulAction.injective a⁻¹) he)
  intro z hz
  obtain ⟨g,hg,he⟩ := linear_full_index_pair_transitive h i e T hT (hadj hw) hne'
    (D.map c) (E.map c) hD' hE' (hi D hiD) (hi E hiE) _ (hadj hz)
  rw [←Subgroup.map_sup] at hg
  obtain ⟨d,hd,rfl⟩ := hg
  refine ⟨d,hd,?_⟩
  apply (MulAction.injective a⁻¹)
  change (a⁻¹ * d * (a⁻¹)⁻¹) • base F (!i) = a⁻¹ • z at he
  rw [inv_inv,mul_smul,mul_smul,hav] at he
  simpa only [mul_smul] using he

/-- The two conjugated intersections on printed p.184 act transitively
at the intervening linear vertex. Their full root images are the earlier
second indices of (12.3)(a); the conjugators fix the actual opposite vertices. -/
theorem source_linear_conjugate_intersections_transitive
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    {m y z w c : Vertex (reducedFamily L S)} (hz : z.type = i)
    (hzy : (graph (reducedFamily L S)).Adj z y)
    (hzw : (graph (reducedFamily L S)).Adj z w) (hwy : w ≠ y)
    (hiY : (Q (reducedFamily L S) c).relIndex
      (V (reducedFamily L S) y 1 ⊓ Q (reducedFamily L S) w) = Nat.card k)
    (hiW : (Q (reducedFamily L S) m).relIndex
      (V (reducedFamily L S) w 1 ⊓ Q (reducedFamily L S) y) = Nat.card k)
    (a b : G₀ L S) (haw : a • w = w) (hac : a • c = z)
    (hby : b • y = y) (hbm : b • m = z) :
    let F := reducedFamily L S
    let D := (V F y 1).map (MulAut.conj a).toMonoidHom ⊓ Q F w
    let E := (V F w 1).map (MulAut.conj b).toMonoidHom ⊓ Q F y
    ∀ v, (graph F).Adj z v → ∃ g ∈ D ⊔ E, g • w = v := by
  let F := reducedFamily L S
  have hD : (V F y 1 ⊓ Q F w).map (MulAut.conj a).toMonoidHom =
      (V F y 1).map (MulAut.conj a).toMonoidHom ⊓ Q F w := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj a).injective,←Q_translate F,haw]
  have hE : (V F w 1 ⊓ Q F y).map (MulAut.conj b).toMonoidHom =
      (V F w 1).map (MulAut.conj b).toMonoidHom ⊓ Q F y := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj b).injective,←Q_translate F,hby]
  have hiD := relIndex_map_map_of_injective (Q F c) (V F y 1 ⊓ Q F w)
    (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).injective
  rw [←Q_translate F,hac,hD,hiY] at hiD
  have hiE := relIndex_map_map_of_injective (Q F m) (V F w 1 ⊓ Q F y)
    (f := (MulAut.conj b).toMonoidHom) (MulAut.conj b).injective
  rw [←Q_translate F,hbm,hE,hiW] at hiE
  exact linear_full_index_pair_transitive_at h i e T hT hz hzw hzy hwy.symm
    _ _ inf_le_right inf_le_right hiD hiE

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
