module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.UnitaryIndices
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.UnitarySelectionRoot
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ResidualGeneration
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.UnitaryIndices
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.UnitarySelectionRoot

/-!
# Full omega and a nonsquare-one element in the selected centralizer

Keep the same nonidentity involution t selected in the two remote cores
and V_y. Since V_y is elementary, it lies in C(t), as well as in both
interior cores. The newly proved reversed span index identifies its image
in the actual opposite local quotient with the whole Sylow omega, of
order q. The already proved q² lower bound makes the centralizer image
strictly larger. Choose an element outside that omega and lift it through
the literal quotient map: its square is nonidentity in that same quotient.

No center-image, noncentral-element or index premise is added. The original
field, common Sylows, critical pair, full kernels and completion inclusion
are retained. The subsequent remote-center transitivity and unitary
contradiction, exhaustive Suzuki selection, binary alternatives and earlier
Chapter 12/13.1 premise discharge remain with this theorem family.
The implementation imports reuse its local unitary marking and omega data.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.5), printed p.182, the centralizer used to generate L.
-/

public noncomputable section
open Subgroup SimpleGraph BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- In the original unitary contradiction, the same selected centralizer
contains the full Sylow omega and a literal element with nontrivial square
in the opposite local quotient. -/
theorem source_unitary_selection_centralizer_omega
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmx : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) (!i)) x)
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) i))
    {n : ℕ} (hn : 2 ≤ n) (hfield : Nat.card k = 2^n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (hu : ClassicalGroup.IsPSU (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) 3 (2^n) ∨
      IsSU (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) 3 (2^n))
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = 2^n)
    (T : Sylow 2 (star L S i)) (R : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    {u v d e : Vertex (reducedFamily L S)}
    (hyu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) u)
    (hyv : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) v)
    (p : (graph (reducedFamily L S)).Walk u d) (hp : p.length = 4)
    (r : (graph (reducedFamily L S)).Walk v e) (hr : r.length = 2)
    (hs : 3 < sourceS (P := fun j => (P₀ L S j).subgroupOf (G₀ L S))) :
    let F := reducedFamily L S
    let y := base F i
    let m := base F (!i)
    let A := graphLocalGroup F x
    let I := Q F y ⊓ Q F m
    let f := QuotientGroup.mk' (pCore 2 A)
    ∃ t : G₀ L S, t ∈ V F y 1 ⊓ (Q F d ⊓ Q F e) ∧ t ≠ 1 ∧ t^2 = 1 ∧
      Z F y ⊔ Z F d ⊔ Z F e ≤ centralizer ({t} : Set (G₀ L S)) ∧
      ∃ U : Sylow 2 (A ⧸ pCore 2 A),
        (I.subgroupOf A).map f = U ∧
        ((V F y 1).subgroupOf A).map f = omegaOneAmbient (U : Subgroup (A ⧸ pCore 2 A)) ∧
        omegaOneAmbient (U : Subgroup (A ⧸ pCore 2 A)) <
          (((I ⊓ centralizer ({t} : Set (G₀ L S))).subgroupOf A).map f) ∧
        ∃ u : A, u.val ∈ I ⊓ centralizer ({t} : Set (G₀ L S)) ∧ (f u)^2 ≠ 1 ∧
          (u.val : G) ∈ (I ⊓ centralizer ({t} : Set (G₀ L S))).map (G₀ L S).subtype := by
  let F := reducedFamily L S
  let y := base F i
  let m := base F (!i)
  let A := graphLocalGroup F x
  let I := Q F y ⊓ Q F m
  let f := QuotientGroup.mk' (pCore 2 A)
  let d₀ := reducedFullEarlierLocalTheorems h
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (d₀.local_le x))
    (inclusion_injective _)
  let := V_elementary F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb y
  obtain ⟨t,ht,ht1,ht2,hZ,⟨U,hIU,hindex⟩,hlower,hcard,htG,hmap⟩ :=
    source_unitary_selection_centralizer_root h i hb hc hxa hmx hzy hcomm hn hfield eLin hu
      hcard T R hT hR hyu hyv p hp r hr hs
  have hadj : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hVA : V F y 1 ≤ A :=
    (V_le_neighbor_Q F (reduced_triple h).generate
      (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb hadj).trans
      (CommutingTrivial.neighbor_core_le_localGroup (reduced_triple h)
        (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hmx.symm)
  have hVI : V F y 1 ≤ I := le_inf
    (V_le_Q F (reduced_triple h).generate
      (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb y)
    (V_le_neighbor_Q F (reduced_triple h).generate
      (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb hadj)
  have hVC : V F y 1 ≤ I ⊓ centralizer ({t} : Set (G₀ L S)) := by
    apply le_inf hVI
    intro v hv z hz
    have hz : z = t := Set.mem_singleton_iff.mp hz
    subst z
    exact congrArg (fun w : V F y 1 => (w : G₀ L S))
      (mul_comm (⟨t,ht.1⟩ : V F y 1) ⟨v,hv⟩)
  have hk : f.ker = (Q F x).subgroupOf A := by
    rw [QuotientGroup.ker_mk',←localGroup_core_eq F d₀ x]
    exact (comap_map_eq_self_of_injective A.subtype_injective _).symm
  have hvcard : Nat.card (((V F y 1).subgroupOf A).map f) = 2^n := by
    rw [←relIndex_ker,hk,relIndex_subgroupOf hVA]
    exact (source_unitary_reverse_first_index h i hb hc hxa hmx.symm hadj hn hu eLin T hT).1
  have hx : x.type = i := by
    have hx' : x.type ≠ !i := hmx.1.symm
    simpa only [Bool.not_not] using Bool.eq_not_iff.mpr hx'
  have hunitary := unitary_marking_at h i hn hu x hx
  have homega := unitary_sylow_omega hn hunitary U
  let E := ((V F y 1).subgroupOf A).map f
  let D := ((I ⊓ centralizer ({t} : Set (G₀ L S))).subgroupOf A).map f
  let : IsElementaryAbelian 2 ((V F y 1).subgroupOf A) := IsElementaryAbelian.subgroupOf hVA
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map f
  have hEU : E ≤ U := hIU ▸ map_mono (subgroupOf_mono A hVI)
  have hEO : E ≤ omegaOneAmbient (U : Subgroup (A ⧸ pCore 2 A)) := by
    rw [←omegaOneAmbient_eq_self E]
    exact omegaOneAmbient_mono hEU
  have hE : E = omegaOneAmbient (U : Subgroup (A ⧸ pCore 2 A)) :=
    eq_of_le_of_card_ge hEO (by rw [homega.2.2]; exact hvcard.ge)
  have hOD : omegaOneAmbient (U : Subgroup (A ⧸ pCore 2 A)) ≤ D :=
    hE ▸ map_mono (subgroupOf_mono A hVC)
  have hnot : ¬D ≤ omegaOneAmbient (U : Subgroup (A ⧸ pCore 2 A)) := by
    intro hle
    have hh := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective _)
    rw [homega.2.2] at hh
    have hq : 1 < 2^n := one_lt_pow₀ (by decide) (by omega)
    have hsquare : 2^n < (2^n)^2 := by nlinarith
    exact (not_le_of_gt hsquare) (hcard.trans hh)
  obtain ⟨z,hz,hzO⟩ := Set.not_subset.mp hnot
  obtain ⟨u,hu,rfl⟩ := hz
  have huU : f u ∈ (U : Subgroup (A ⧸ pCore 2 A)) :=
    hIU ▸ mem_map_of_mem f (show u ∈ I.subgroupOf A from hu.1)
  have hsquare : (f u)^2 ≠ 1 := by
    intro he
    exact hzO ((omegaOneAmbient_le_iff _ _).mp le_rfl _ huU he)
  exact ⟨t,ht,ht1,ht2,hZ,U,hIU,hE,lt_of_le_not_ge hOD hnot,u,hu,hsquare,
    mem_map_of_mem (G₀ L S).subtype hu⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
