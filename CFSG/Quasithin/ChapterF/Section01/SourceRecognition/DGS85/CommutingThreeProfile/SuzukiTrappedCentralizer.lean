module
public import Theory.GroupTheory.Commutator.AbelianCentralizerIndex
public import Theory.Representation.QuotientCentralizer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSymmetricIndex
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.NinePathCentralizer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiIntersectionOrder
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanFixedIndex

/-!
# The trapped centralizer in DGS (12.7)

Use the source path a--x--m--y--z--w--c, with m linear and y Suzuki,
and let A = C_(V_x)(t) for t in Q_x. In the branch A <= Q_y, the
abelian commutator map and the proved first index force
A = V_x intersect Q_y. Put D = A intersect Q_w.

Suppose D <= Q_c. The remote centers Z_a and Z_c generate the actual
star at y modulo Q_y. Every element of D intersect V_y centralizes
both centers: it belongs to the abelian V_x and to Q_c. Construct the
literal conjugation action on V_y/Z_y, apply its proved faithful
minimal-degree theorem, and conclude D intersect V_y <= Z_y.
But |V_x intersect V_y| = q^3 and the reversed first index bounds its
intersection with Q_w by index q. This contradicts |Z_y| = q.
Thus D is not contained in Q_c, as required on printed p.185.

The center and intersection orders are discharged here by the existing
source (12.6) proofs. Remote-center generation and the reversed index
are also derived, not assumed. The retained common-Sylow, natural-center,
commutator and parameter inputs are the same genuine (12.1)--(12.3)
inputs as SuzukiCenterApplication. The additional critical pairs record
the placements used in (12.7). Both orientations and original inclusions
are retained. The opposite A-not-contained branch, the final graph
transitivity contradiction, binary cases, Suzuki selection, and the
remaining (12.8)--(12.9)/(13.1) assembly are not asserted here.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.7), printed pp.184--185, using (12.3)(a) and (12.6)(a)--(c).
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Identify the actual trapped centralizer and prove that its remote-core
intersection escapes the next core, also after the original inclusion. -/
theorem source_suzuki_trapped_centralizer_escape
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    {c w z : Vertex (reducedFamily L S)}
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) (!i)) z)
    (hwz : (graph (reducedFamily L S)).Adj w z)
    (hwc : (graph (reducedFamily L S)).Adj w c)
    (hzn : z ≠ base (reducedFamily L S) i)
    (hcc : IsCriticalPair (reducedFamily L S) c (base (reducedFamily L S) (!i)))
    (Rz : Sylow 2 (star L S (!i)))
    (hRz : (Rz : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) z ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (t : G₀ L S) (ht : t ∈ Q (reducedFamily L S) x)
    (htrapped : V (reducedFamily L S) x 1 ⊓ centralizer ({t} : Set (G₀ L S)) ≤
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))) :
    let F := reducedFamily L S
    let A := V F x 1 ⊓ centralizer ({t} : Set (G₀ L S))
    let D := A ⊓ Q F w
    A = V F x 1 ⊓ Q F (base F (!i)) ∧
      ¬ D ≤ Q F c ∧
      A.map (G₀ L S).subtype =
        (V F x 1).map (G₀ L S).subtype ⊓ (Q F (base F (!i))).map (G₀ L S).subtype ∧
      ¬ D.map (G₀ L S).subtype ≤ (Q F c).map (G₀ L S).subtype := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let P := star L S (!i)
  let X := V F x 1
  let Y := V F y 1
  let C := Z F y
  let E := Z F a ⊔ Z F c
  let A := X ⊓ centralizer ({t} : Set (G₀ L S))
  let D := A ⊓ Q F w
  let H := X ⊓ Y
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hQU := fun v => (source_Z_Q_U (reduced_triple h) v).2
  let := V_elementary F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x
  let := V_elementary F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb y
  let : (C.subgroupOf Y).Normal := normal_of_isMulCommutative _
  have hXQ := V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x
  have hYQ := V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb y
  let : Finite X := Finite.of_injective
    (inclusion (hXQ.trans (Q_le_stabilizer F x))) (inclusion_injective _)
  let : Finite Y := Finite.of_injective
    (inclusion (hYQ.trans (Q_le_stabilizer F y))) (inclusion_injective _)
  let : Finite (Z F x) := Finite.of_injective
    (inclusion (Z_le_V F x 1)) (inclusion_injective _)
  let : Finite C := Finite.of_injective
    (inclusion (Z_le_V F y 1)) (inclusion_injective _)
  let : Finite H := Finite.of_injective
    (inclusion (show H ≤ Y from inf_le_right)) (inclusion_injective _)
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨g,_,hgx,_⟩ := linear_neighbor_swap h i e hxadj hadj hne
  have hCcard : Nat.card C = 2^(2*n+1) := hcardy.trans hfield
  have hZxcard : Nat.card (Z F x) = 2^(2*n+1) := by
    have he : Nat.card ((Z F x).map (MulAut.conj g).toMonoidHom) = Nat.card (Z F x) :=
      card_map_of_injective (MulAut.conj g).injective
    rw [←Z_translate F,hgx] at he
    exact he.symm.trans hCcard
  have hXi : (Q F y).relIndex X = 2^(2*n+1) := by
    simpa only [inf_relIndex_left] using (source_suzuki_first_index h (!i) hb hc hxa
      hxadj.symm hadj.symm hn eSuz (by cases i <;> exact e) Ry
        (by simpa only [Bool.not_not] using hRy)).1
  have hA : A = X ⊓ Q F y := abelian_singleton_centralizer_eq_intersection
    X (Q F x) (Z F x) (Q F y) (Z_le_V F x 1) hcommx ht
      (hXi.trans hZxcard.symm) htrapped
  have hYi : (Q F w).relIndex Y = 2^(2*n+1) :=
    (source_suzuki_reverse_first_index h (!i) hb hcc hwc hwz hyz hn eSuz
      (by cases i <;> exact e) Rz hRz).1
  have hHcard : Nat.card H = (2^(2*n+1))^3 :=
    (source_suzuki_intersection_card h i hb hxadj hne T R hT hR e hz hcard hcardy
      hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat).1
  obtain ⟨_,_,_,ρ₀,_,_,hYcard,_⟩ := source_suzuki_center_layer_of_intersection
    h i hb hxadj hne T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy
      hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
  have hZa : Z F a ≤ Q F m := CommutingNontrivial.Z_le_Q_of_dist_lt_b F hZ a m
    (lt_of_le_of_lt (SimpleGraph.dist_le (SimpleGraph.Walk.cons hxa.symm
      (SimpleGraph.Walk.cons hxadj.symm .nil))) hb) (reduced_kernel_sylow h m)
  have hZc : Z F c ≤ Q F z := CommutingNontrivial.Z_le_Q_of_dist_lt_b F hZ c z
    (lt_of_le_of_lt (SimpleGraph.dist_le (SimpleGraph.Walk.cons hwc.symm
      (SimpleGraph.Walk.cons hwz .nil))) hb) (reduced_kernel_sylow h z)
  have hia := source_suzuki_critical_center_index h (!i) hb hc hxa hxadj.symm hadj.symm
    hn eSuz (by cases i <;> exact e) Ry hRy
  have hic := source_suzuki_critical_center_index h (!i) hb hcc hwc hwz hyz
    hn eSuz (by cases i <;> exact e) Rz hRz
  have hgen : E ⊔ Q F y = P :=
    (source_suzuki_remote_center_pair h (!i) hn eSuz hyz
      (by simpa only [Bool.not_not] using hzn) Ry Rz
      (by simpa only [Bool.not_not] using hRy) hRz (by simpa only [Bool.not_not] using hZa) hZc hia hic).1
  have hEP : E ≤ P := le_sup_left.trans hgen.le
  have hQP : Q F y ≤ P := le_sup_right.trans hgen.le
  have hPY := star_normalizes_span h (!i)
  obtain ⟨σ,hσ⟩ := exists_center_layer_action F (reduced_triple h).generate hZ
    (reduced_kernel_sylow h) hb y P (star_le_stabilizer (!i)) (star_core h (!i)).le hcommy.le
  have hPC : P ≤ centralizer (C : Set (G₀ L S)) := le_centralizer_iff.mp
    (source_center_centralizes_star_of_neighbor_inclusion h (!i)
      (by simpa only [Bool.not_not] using hzy) Ry
      (by simpa only [Bool.not_not] using hRy))
  have hfσ := central_quotient_conjugation_faithful P Y C hPY hPC
    (source_suzuki_span_centralizer_le_core h (!i) eSuz) σ hσ
  let eP := (originalQuotient h (!i)).symm.trans eSuz
  let f := eP.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P))
  have hf : Function.Surjective f := eP.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 P := by
    ext u
    change eP (QuotientGroup.mk' (pCore 2 P) u) = 1 ↔ u ∈ pCore 2 P
    rw [map_eq_one_iff _ eP.injective]
    exact QuotientGroup.eq_one_iff u
  have hgen' : E.subgroupOf P ⊔ pCore 2 P = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hEP,
      ←MonoidHom.range_eq_map,range_subtype]
    change E ⊔ P.pCoreIn 2 = P
    rw [star_core h (!i)]
    exact hgen
  have himage : (E.subgroupOf P).map f = ⊤ := by
    have he := congrArg (Subgroup.map f) hgen'
    rw [Subgroup.map_sup,←hk,Subgroup.map_ker_self,sup_bot_eq,
      Subgroup.map_top_of_surjective _ hf] at he
    exact he
  let ρ : Representation (ZMod 2) (SuzukiMatrixGroup n)
      (Additive (Y ⧸ C.subgroupOf Y)) := σ.comp eP.symm.toMonoidHom
  have hfρ : Function.Injective ρ := hfσ.comp eP.symm.injective
  let : ρ.IsIrreducible := (Representation.Suzuki.irreducible_of_faithful_small_card
    ρ hfρ hYcard.le).1
  have hdim : 2 ≤ Module.finrank (ZMod 2) (Additive (Y ⧸ C.subgroupOf Y)) := by
    have hh := Representation.Suzuki.finrank_ge (by omega : 1 ≤ n) ρ hfρ
    change 4 * (2*n+1) ≤ Module.finrank (ZMod 2) (Additive (Y ⧸ C.subgroupOf Y)) at hh
    omega
  have hCE : Y ⊓ centralizer (E : Set (G₀ L S)) ≤ C :=
    centralizer_le_layer_of_irreducible_quotient P Y C E hPY f himage ρ hdim (by
      intro u v
      change (σ (eP.symm (eP (QuotientGroup.mk u))) _).toMul = _
      rw [eP.symm_apply_apply]
      exact hσ u v)
  have hescape : ¬ D ≤ Q F c := by
    intro hD
    have hHD : H ⊓ Q F w ≤ D := by
      intro u hu
      refine ⟨?_,hu.2⟩
      rw [hA]
      exact ⟨hu.1.1,hYQ hu.1.2⟩
    have hEC : H ⊓ Q F w ≤ centralizer (E : Set (G₀ L S)) := by
      apply le_centralizer_iff.mpr
      apply sup_le
      · intro u hu v hv
        have huX : u ∈ X := Z_neighbor_le_V F hxa hu
        exact congrArg Subtype.val (mul_comm (⟨v,hv.1.1⟩ : X) ⟨u,huX⟩)
      · exact (Z_centralizes_Q F c (hZ c)).trans (centralizer_le (hHD.trans hD))
    have hHC : H ⊓ Q F w ≤ C := (le_inf (inf_le_left.trans inf_le_right) hEC).trans hCE
    apply inf_not_le_of_card_gt_index_mul_card H Y (Q F w) C inf_le_right hYi.le ?_ hHC
    rw [hCcard,hHcard]
    calc
      (2^(2*n+1)) * (2^(2*n+1)) = (2^(2*n+1))^2 := by ring
      _ < (2^(2*n+1))^3 := Nat.pow_lt_pow_right (by exact Nat.one_lt_pow (by omega) (by decide)) (by decide)
  refine ⟨hA,hescape,?_,?_⟩
  · change A.map (G₀ L S).subtype = X.map (G₀ L S).subtype ⊓ (Q F y).map (G₀ L S).subtype
    rw [hA,Subgroup.map_inf _ _ _ (G₀ L S).subtype_injective]
  · intro hle
    apply hescape
    intro u hu
    obtain ⟨v,hv,he⟩ := hle (mem_map_of_mem (G₀ L S).subtype hu)
    exact (G₀ L S).subtype_injective he ▸ hv

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
