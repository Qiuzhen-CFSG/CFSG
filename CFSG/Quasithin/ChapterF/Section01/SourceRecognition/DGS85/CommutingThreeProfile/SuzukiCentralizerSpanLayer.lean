module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiDerivedCoreIdentity
/-!
# The actual centralizer quotient over the elementary span

At the linear vertex m put H = G_m^(3), C = C_(Q_m)(H), and let W
be the source span of V_y intersect Q_x. The sharp centralizer placement
writes C as V_x (C intersect Q_y). The new identity [Q_y,Q_y] = V_y,
together with the old bound [C,Q_m] <= G_m^(2), puts commutators with
Q_m intersect Q_y into W: their two factors lie respectively in
V_x intersect G_m^(2) and V_y intersect G_m^(2). Neighbor transport
and the middle-core product extend this to [C,Q_m] <= W.

The same factorization and Phi(Q_y) = V_y put every square in C inside
W, using the already proved Phi(C) <= G_m^(2). Hence Phi(C) <= W and
the literal quotient C/W is elementary. Its actual conjugation action
descends through Q_m to the original endpoint quotient, with the original
actor formula retained. The commutator containment is also transported
by the original completion inclusion.

All earlier source hypotheses remain explicit. Irreducibility of C/W,
the equality G_m^(2) = W, Suzuki selection, the binary alternatives and
final Chapter 12/13.1 discharge remain separate obligations.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (12.9), printed pp.188--190, the module E = C_(Q_alpha)(H)/W.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative MatrixGroups commutatorElement
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- The original span W contains the centralizer Frattini subgroup and
its commutator with the entire middle core. -/
theorem source_suzuki_centralizer_span_frattini
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
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
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hnear : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let y := base F (!i)
    let C := Q F m ⊓ centralizer (ballKernel F m 3 : Set (G₀ L S))
    let W := conjugateSpanBy (V F y 1 ⊓ Q F x) (stabilizer F m)
    (frattini C).map C.subtype ≤ W ∧ ⁅C,Q F m⁆ ≤ W ∧
      ⁅C.map (G₀ L S).subtype,(Q F m).map (G₀ L S).subtype⁆ ≤ W.map (G₀ L S).subtype := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let Qm := Q F m
  let Qy := Q F y
  let X := V F x 1
  let Y := V F y 1
  let H := ballKernel F m 3
  let N := ballKernel F m 2
  let C := Qm ⊓ centralizer (H : Set (G₀ L S))
  let W := conjugateSpanBy (Y ⊓ Q F x) (stabilizer F m)
  let P := C ⊓ Qy
  let B := Qm ⊓ Qy
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite C := Finite.of_injective
    (inclusion (show C ≤ stabilizer F m from inf_le_left.trans (Q_le_stabilizer F m)))
    (inclusion_injective _)
  let : Finite Qy := Finite.of_injective (inclusion (Q_le_stabilizer F y)) (inclusion_injective _)
  have hpC : IsPGroup 2 C := (isPGroup_pCoreIn 2 _).to_le (show C ≤ Qm from inf_le_left)
  let : Fact (IsPGroup 2 C) := ⟨hpC⟩
  let : Fact (IsPGroup 2 Qy) := ⟨isPGroup_pCoreIn 2 _⟩
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  let : IsElementaryAbelian 2 X := V_elementary F (reduced_triple h).generate hZ
    (reduced_kernel_sylow h) hb x
  obtain ⟨hCD,hNC,hphiOld,hCQold⟩ := source_suzuki_centralizer_second_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
  have hNC' : N ≤ C := hNC
  have hNQz (z : Vertex F) (hz : (graph F).Adj m z) : N ≤ Q F z :=
    CommutingTrivial.two_subgroup_le_Q F z (reduced_kernel_sylow h z)
      (hpC.to_le hNC') (ballKernel_succ_le F hz 1)
  have hspan := source_suzuki_second_kernel_span_order h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hnear
  have hWY : W ⊓ Y = Y ⊓ Q F x := hspan.2.2.1
  have hWX : W ⊓ X = X ⊓ Qy := hspan.2.2.2.1
  have hYW : Y ⊓ N ≤ W := ((inf_le_inf_left Y (hNQz x hxadj)).trans hWY.ge).trans inf_le_left
  have hXW : X ⊓ N ≤ W := ((inf_le_inf_left X (hNQz y hadj)).trans hWX.ge).trans inf_le_left
  have hnW : stabilizer F m ≤ normalizer (W : Set (G₀ L S)) :=
    (source_linear_second_kernel_span h i hb hxadj hne T hT e hcommy.le hnear).2.2.2.1
  have hQW : Qm ≤ normalizer (W : Set (G₀ L S)) := (Q_le_stabilizer F m).trans hnW
  have hCW : C ≤ normalizer (W : Set (G₀ L S)) := inf_le_left.trans hQW
  have hQmx : Qm ≤ stabilizer F x :=
    ((source_Z_Q_U (reduced_triple h) m).2.trans (ballKernel_one_le_edge F hxadj)).trans inf_le_right
  have hQX : Qm ≤ normalizer (X : Set (G₀ L S)) := hQmx.trans (stabilizer_normalizes_V F x 1)
  have hXQ : X ≤ Qm := V_le_neighbor_Q F (reduced_triple h).generate hZ
    (reduced_kernel_sylow h) hb hxadj.symm
  have hfull := (source_suzuki_full_linear_third_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch).1
  have hXC : X ≤ C := le_inf hXQ ((le_centralizer X).trans (centralizer_le (hfull.le.trans inf_le_left)))
  have hgen : X ⊔ P = C := by
    apply le_antisymm (sup_le hXC inf_le_left)
    intro c hc
    have hh : c ∈ X ⊔ B := hCD hc
    rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left X B (inf_le_left.trans hQX)] at hh
    obtain ⟨u,hu,v,hv,hprod⟩ := hh
    have hvC : v ∈ C := by
      have hh := C.mul_mem (C.inv_mem (hXC hu)) hc
      rw [←hprod] at hh
      simpa only [inv_mul_cancel_left] using hh
    rw [←hprod]
    exact mul_mem_sup hu (show v ∈ P from ⟨hvC,hv.2⟩)
  have hcore := source_suzuki_core_derived_eq_span h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  have hderQ : ⁅Qy,Qy⁆ = Y := hcore.1
  have hphiQ : (frattini Qy).map Qy.subtype = Y := hcore.2.1
  have hXB : ⁅X,B⁆ ≤ W := (le_inf
    (le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans hQX))
    ((commutator_mono hXC inf_le_left).trans hCQold)).trans hXW
  have hPB : ⁅P,B⁆ ≤ W := (le_inf
    ((commutator_mono inf_le_right inf_le_right).trans hderQ.le)
    ((commutator_mono inf_le_left inf_le_left).trans hCQold)).trans hYW
  have hCB : ⁅C,B⁆ ≤ W := by
    conv_lhs => rw [←hgen]
    exact commutator_sup_le_of_relative_normal C X P B W hCW hXC inf_le_left hXB hPB
  have hNormC : stabilizer F m ≤ normalizer (C : Set (G₀ L S)) :=
    (le_inf (CommutingTrivial.stabilizer_normalizes_Q F m)
      ((stabilizer_le_normalizer_ballKernel F m 3).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  obtain ⟨g,hg,hgy⟩ := star_locally_transitive h i hadj hxadj
  have hgm : g ∈ stabilizer F m := star_le_stabilizer i hg
  have hCg : C.map (MulAut.conj g).toMonoidHom = C := mem_normalizer_iff_map_conj_eq.mp (hNormC hgm)
  have hWg : W.map (MulAut.conj g).toMonoidHom = W := mem_normalizer_iff_map_conj_eq.mp (hnW hgm)
  have hQmg : Qm.map (MulAut.conj g).toMonoidHom = Qm :=
    mem_normalizer_iff_map_conj_eq.mp (CommutingTrivial.stabilizer_normalizes_Q F m hgm)
  have hCBx : ⁅C,Qm ⊓ Q F x⁆ ≤ W := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hCB
    change (⁅C,Qm ⊓ Q F y⁆).map _ ≤ W.map _ at hh
    rwa [map_commutator,hCg,hWg,map_inf _ _ _ (MulAut.conj g).injective,hQmg,←Q_translate F,hgy] at hh
  have hprod : Qm = (Q F x ⊓ Qm) ⊔ (Qy ⊓ Qm) := (source_suzuki_product_and_intersection_commutator h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin).1
  have hCQ : ⁅C,Qm⁆ ≤ W := by
    rw [hprod,commutator_comm]
    apply commutator_sup_le_of_relative_normal Qm (Q F x ⊓ Qm) (Qy ⊓ Qm) C W
      hQW inf_le_right inf_le_right
    · simpa only [commutator_comm,inf_comm] using hCBx
    · simpa only [commutator_comm,inf_comm] using hCB
  have hphi : (frattini C).map C.subtype ≤ W := by
    apply frattini_image_le_of_square_cover C X P W hpC hgen
      ((commutator_mono le_rfl inf_le_left).trans hCQ)
    · intro u hu
      rw [elemPow_eq_one_of_isElementaryAbelian u hu]
      exact W.one_mem
    · intro u hu
      have huY : u^2 ∈ Y := hphiQ.le (mem_map_of_mem Qy.subtype
        (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨u,hu.2⟩ : Qy)))
      have huN : u^2 ∈ N := hphiOld (mem_map_of_mem C.subtype
        (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨u,hu.1⟩ : C)))
      exact hYW ⟨huY,huN⟩
  refine ⟨hphi,hCQ,?_⟩
  have hh := map_mono (f := (G₀ L S).subtype) hCQ
  rwa [map_commutator] at hh

/-- The literal centralizer quotient C/W is elementary, and its conjugation
action factors through the original linear endpoint quotient. -/
theorem source_suzuki_centralizer_span_action
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
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
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hnear : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let y := base F (!i)
    let A := star L S i
    let C := Q F m ⊓ centralizer (ballKernel F m 3 : Set (G₀ L S))
    let W := conjugateSpanBy (V F y 1 ⊓ Q F x) (stabilizer F m)
    ∃ hAC : A ≤ normalizer (C : Set (G₀ L S)),
    ∃ hW : (W.subgroupOf C).Normal,
      let := hW
      W ≤ C ∧ IsElementaryAbelian 2 (C ⧸ W.subgroupOf C) ∧
      ∃ ρ : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) →*
        MulAut (C ⧸ W.subgroupOf C),
        ∀ u : L (if i then 1 else 0), ∀ c : C,
          ρ (QuotientGroup.mk u) (QuotientGroup.mk c) =
            QuotientGroup.mk ⟨(originalActor (L := L) (S := S) i u : G₀ L S) * c *
              (originalActor (L := L) (S := S) i u : G₀ L S)⁻¹,
              (mem_normalizer_iff.mp (hAC
                (originalActor (L := L) (S := S) i u).property) c).mp c.property⟩ := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let A := star L S i
  let C := Q F m ⊓ centralizer (ballKernel F m 3 : Set (G₀ L S))
  let W := conjugateSpanBy (V F y 1 ⊓ Q F x) (stabilizer F m)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite C := Finite.of_injective
    (inclusion (show C ≤ stabilizer F m from inf_le_left.trans (Q_le_stabilizer F m)))
    (inclusion_injective _)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hspan := source_linear_second_kernel_span h i hb hxadj hne T hT e hcommy.le hnear
  have hWC : W ≤ C := hspan.2.1.trans
    (source_suzuki_centralizer_second_kernel h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch).2.1
  have hnW : stabilizer F m ≤ normalizer (W : Set (G₀ L S)) := hspan.2.2.2.1
  have hAC : A ≤ normalizer (C : Set (G₀ L S)) := (star_le_stabilizer i).trans
    ((le_inf (CommutingTrivial.stabilizer_normalizes_Q F m)
      ((stabilizer_le_normalizer_ballKernel F m 3).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf)
  have hAW : A ≤ normalizer (W : Set (G₀ L S)) := (star_le_stabilizer i).trans hnW
  let hW : (W.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
    ((inf_le_left.trans (Q_le_stabilizer F m)).trans hnW)
  let := hW
  obtain ⟨hphi,hCQ,_⟩ := source_suzuki_centralizer_span_frattini h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  have hel : IsElementaryAbelian 2 (C ⧸ W.subgroupOf C) :=
    elementary_quotient_of_frattini_le ((isPGroup_pCoreIn 2 _).to_le (show C ≤ Q F m from inf_le_left))
      (W.subgroupOf C) (map_le_iff_le_comap.mp hphi)
  obtain ⟨α,hα⟩ := exists_quotient_conjugation_action A C W hAC hAW hW
  have hkill := quotient_conjugation_action_kills_commutator_layer A C W (Q F m) hW hAC hCQ α hα
  have hk : pCore 2 A ≤ α.ker := by
    intro a ha
    apply hkill
    change (a : G₀ L S) ∈ Q F m
    rw [←star_core h i]
    exact mem_map_of_mem A.subtype ha
  let β := QuotientGroup.lift (pCore 2 A) α hk
  let ρ := β.comp (originalQuotient h i).toMonoidHom
  refine ⟨hAC,hW,hWC,hel,ρ,?_⟩
  intro u c
  change β ((originalQuotient h i) (QuotientGroup.mk u)) (QuotientGroup.mk c) = _
  rw [originalQuotient_mk h i u]
  exact hα (originalActor (L := L) (S := S) i u) c
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
