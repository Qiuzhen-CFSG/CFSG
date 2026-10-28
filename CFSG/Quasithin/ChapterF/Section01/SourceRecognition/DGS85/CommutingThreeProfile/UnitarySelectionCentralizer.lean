module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.UnitarySelectionPaths
public import Theory.GroupTheory.Commutator.CentralSingletonIndex

/-!
# The actual centralizer element in the unitary selection argument

In the nonbinary unitary alternative, the constructed center quotient gives
|V_y| ≥ q⁷. The two actual walks from neighbors of y have lengths four and
two, and the original local quotient markings give remote-core indices at
most q⁴ and q². The literal intersection V_y ∩ Q_d ∩ Q_e therefore has order
at least q. Choose its nonidentity involution t. The source commutator bound
[V_y,Q_y] ≤ Z_y gives |Q_y:C_(Q_y)(t)| ≤ q. Membership in the three cores
makes all three corresponding centers centralize t. Their original images
centralize the same nonidentity element in the original completion.

Thus the nonidentity element and both numerical bounds in the middle of
(12.5) are constructed, with no such bounds as additional premises. The
original common-Sylow data, natural center order, commutator bound and
critical pair are retained. The final unitary contradiction still needs
the subsequent three-path Sylow placement and centralizer-transitivity
arguments. The binary cases, exhaustive Suzuki selection and full original
Chapter 12/13.1 assembly remain obligations of this theorem family.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.5), printed p.182, from the q⁷ estimate through the centralizer index.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Construct the nonidentity involution used in the unitary contradiction
of (12.5), with both remote-core indices derived from the actual paths. -/
theorem source_unitary_selection_centralizer
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
    (r : (graph (reducedFamily L S)).Walk v e) (hr : r.length = 2) :
    let F := reducedFamily L S
    let y := base F i
    let D := V F y 1 ⊓ (Q F d ⊓ Q F e)
    (Q F d).relIndex (V F y 1) ≤ (2^n)^4 ∧
    (Q F e).relIndex (V F y 1) ≤ (2^n)^2 ∧
    2^n ≤ Nat.card D ∧
    2^n ≤ Nat.card (D.map (G₀ L S).subtype) ∧
    ∃ t : G₀ L S, t ∈ D ∧ t ≠ 1 ∧ t^2 = 1 ∧
      (centralizer ({t} : Set (G₀ L S))).relIndex (Q F y) ≤ 2^n ∧
      Z F y ⊔ Z F d ⊔ Z F e ≤ centralizer ({t} : Set (G₀ L S)) ∧
      (t : G) ≠ 1 ∧
      (Z F y ⊔ Z F d ⊔ Z F e).map (G₀ L S).subtype ≤ centralizer ({(t : G)} : Set G) := by
  let F := reducedFamily L S
  let y := base F i
  let W := V F y 1
  let D := W ⊓ (Q F d ⊓ Q F e)
  let q := 2^n
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let := V_elementary F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb y
  have hWQ : W ≤ Q F y := V_le_Q F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb y
  let : Finite W := Finite.of_injective (inclusion (hWQ.trans (Q_le_stabilizer F y)))
    (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion (show D ≤ W from inf_le_left))
    (inclusion_injective _)
  let : Finite (Z F y) := Finite.of_injective (inclusion (Z_le_stabilizer F y))
    (inclusion_injective _)
  have hlow : q^7 ≤ Nat.card W :=
    (source_unitary_selection_layer h i hb hc hxa hmx hzy hcomm hn hu hcard).2.1
  have hd : (Q F d).relIndex W ≤ q^4 := by
    simpa only [hp] using source_unitary_span_path_index h i hb (by omega) hfield eLin hu T R hT hR hyu p
  have he : (Q F e).relIndex W ≤ q^2 := by
    simpa only [hr] using source_unitary_span_path_index h i hb (by omega) hfield eLin hu T R hT hR hyv r
  have hi : D.relIndex W ≤ q^6 := by
    calc D.relIndex W = (Q F d ⊓ Q F e).relIndex W := inf_relIndex_left _ _
         _ ≤ (Q F d).relIndex W * (Q F e).relIndex W := relIndex_inf_le
         _ ≤ q^4*q^2 := Nat.mul_le_mul hd he
         _ = q^6 := by ring
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) D W bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left] at hmul
  have hD : q ≤ Nat.card D := by
    apply Nat.le_of_mul_le_mul_right (c := q^6)
    · calc q*q^6 = q^7 := by ring
           _ ≤ Nat.card W := hlow
           _ = Nat.card D * D.relIndex W := hmul.symm
           _ ≤ Nat.card D * q^6 := Nat.mul_le_mul_left _ hi
    · exact pow_pos (pow_pos (by decide) _) _
  have hq : 1 < q := one_lt_pow₀ (by decide) (by omega)
  have hDb : D ≠ ⊥ := by
    intro hbot
    rw [hbot,card_bot] at hD
    omega
  obtain ⟨t,ht,ht1⟩ := D.bot_or_exists_ne_one.resolve_left hDb
  have htQ : t ∈ Q F y := hWQ ht.1
  have hcenter {z : Vertex F} (htz : t ∈ Q F z) :
      Z F z ≤ centralizer ({t} : Set (G₀ L S)) := by
    intro c hc a ha
    have ha : a=t := Set.mem_singleton_iff.mp ha
    subst a
    exact Z_centralizes_Q F z (source_Z_Q_U (reduced_triple h) z).1 hc t htz
  have hZC : Z F y ⊔ Z F d ⊔ Z F e ≤ centralizer ({t} : Set (G₀ L S)) :=
    sup_le (sup_le (hcenter htQ) (hcenter ht.2.1)) (hcenter ht.2.2)
  have hidx : (centralizer ({t} : Set (G₀ L S))).relIndex (Q F y) ≤ q := by
    change (centralizer ({t} : Set (G₀ L S))).relIndex (Q F y) ≤ 2^n
    rw [←hcard]
    exact central_singleton_centralizer_index_le (Q F y) (Z F y)
      ((Z_le_V F y 1).trans hWQ) (Z_centralizes_Q F y (source_Z_Q_U (reduced_triple h) y).1)
      htQ ((commutator_mono (zpowers_le.mpr ht.1) le_rfl).trans hcomm)
  refine ⟨hd,he,hD,?_,t,ht,ht1,elemPow_eq_one_of_isElementaryAbelian t ht.1,hidx,hZC,?_,?_⟩
  · rwa [card_map_of_injective (G₀ L S).subtype_injective]
  · intro hh
    exact ht1 (Subtype.ext hh)
  · rintro c ⟨z,hz,rfl⟩ a ha
    have ha : a=(t : G) := Set.mem_singleton_iff.mp ha
    subst a
    exact congrArg (fun w : G₀ L S => (w : G)) (hZC hz t (Set.mem_singleton t))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
