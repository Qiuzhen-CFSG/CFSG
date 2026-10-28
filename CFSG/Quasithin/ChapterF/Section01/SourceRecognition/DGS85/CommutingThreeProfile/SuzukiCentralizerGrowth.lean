module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCentralizerSpanLayer
public import Theory.Representation.Suzuki.MovedSection
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SecondKernelAction
/-!
# Strict growth of the linear radius-two span

Put U = V_m^(2), N = G_m^(2), H = G_m^(3), and C = C_(Q_m)(H)
in the nonbinary Suzuki branch. The literal neighboring span X = V_x
induces a full Sylow omega on the faithful Suzuki section Q_y/G_y^(2).
The dual Suzuki square bound puts at least q² moved elements in the image
of U intersect Q_y, since Q_y normalizes U. Its kernel contains V_y of
order q⁵, and X has image of order q modulo Q_y. Consequently |U| >= q⁸.
Together with |W| = q⁵ this gives |U/W| >= q³ > q², the strict growth
step (6) in the proof of DGS (12.9).

The source consumer puts U inside C by the actual third-kernel intersection
over all neighbors. It also proves [N,star_m] <= W: the derived-core identity
at y puts [N,Q_y] in V_y intersect N <= W; neighbor transport and three-core
generation give the full star. Both inequalities retain the original
completion inclusion. Thus C/W has order at least q³, while N/W is fixed
by the middle star.

The implementation import reuses the existing private construction of the
actual second-kernel conjugation action, without changing its public API.
All original source markings, natural-center and reciprocal-commutator
premises remain explicit. The remaining torus centralizer argument,
irreducibility of C/W, N = W, binary cases and final Chapter 12/13.1 assembly
are not asserted here.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (12.9), printed pp.188--190, especially (6) on p.189. The
nonbinary argument uses the already proved Suzuki square bound in place
of the printed two-neighbor generation contradiction.
-/
public noncomputable section
open Subgroup
open scoped IsMulCommutative MatrixGroups commutatorElement
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- The actual radius-two center span has order at least q⁸ and its
literal quotient over W has order at least q³, also after completion inclusion. -/
theorem source_suzuki_radius_two_span_growth
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
    let W := conjugateSpanBy (V F y 1 ⊓ Q F x) (stabilizer F m)
    Nat.card k ^ 8 ≤ Nat.card (V F m 2) ∧
    Nat.card k ^ 3 ≤ W.relIndex (V F m 2) ∧
    Nat.card k ^ 2 < W.relIndex (V F m 2) ∧
    Nat.card k ^ 3 ≤ (W.map (G₀ L S).subtype).relIndex ((V F m 2).map (G₀ L S).subtype) := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let A := star L S (!i)
  let D := Q F y
  let K := ballKernel F y 2
  let X := V F x 1
  let Y := V F y 1
  let U := V F m 2
  let P := U ⊓ D
  let W := conjugateSpanBy (Y ⊓ Q F x) (stabilizer F m)
  let q := 2^(2*n+1)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer (!i))) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion (Q_le_stabilizer F y)) (inclusion_injective _)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hUQ : U ≤ Q F m := Noncommuting.graph_V_le_Q_of_short
    (reduced_triple h) (reduced_kernel_sylow h) m hb
  let : Finite U := Finite.of_injective (inclusion (hUQ.trans (Q_le_stabilizer F m))) (inclusion_injective _)
  let : Finite P := Finite.of_injective (inclusion (show P ≤ D from inf_le_right)) (inclusion_injective _)
  have hXV : X ≤ U := Noncommuting.graph_V_adjacent_le hxadj 1
  have hYV : Y ≤ U := Noncommuting.graph_V_adjacent_le hadj 1
  have hYD : Y ≤ D := V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb y
  have hYK : Y ≤ K := V_le_ballKernel F (reduced_triple h).generate y
    (by change 3 ≤ b (reducedFamily L S); omega)
  have hXQ : X ≤ Q F m := V_le_neighbor_Q F (reduced_triple h).generate hZ
    (reduced_kernel_sylow h) hb hxadj.symm
  have hXA : X ≤ A := (hXQ.trans (le_sup_left.trans hRy.ge)).trans (map_subtype_le _)
  have hXD : X ≤ normalizer (D : Set (G₀ L S)) :=
    hXA.trans ((star_le_stabilizer (!i)).trans (CommutingTrivial.stabilizer_normalizes_Q F y))
  have hplace : D ≤ star L S i := (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  have hnormU : D ≤ normalizer (U : Set (G₀ L S)) :=
    (hplace.trans (star_le_stabilizer i)).trans (stabilizer_normalizes_V F m 2)
  have hcomm : ⁅D,X⁆ ≤ P := le_inf
    ((commutator_mono le_rfl hXV).trans (le_normalizer_iff_commutator_le_right.mp hnormU))
    (le_normalizer_iff_commutator_le_left.mp hXD)
  let : (K.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    ((Q_le_stabilizer F y).trans (stabilizer_le_normalizer_ballKernel F y 2))
  have hplace' : D ≤ star L S (!(!i)) := by simpa only [Bool.not_not] using hplace
  have hnat' : Noncommuting.HasNaturalCenter (star L S (!(!i)))
      (Z F (base F (!(!i)))) (Q F (base F (!(!i)))) := by simpa only [Bool.not_not] using hnat
  let := source_second_kernel_elementary h (!i) hplace' hnat' hcommy.le
  obtain ⟨σ₀,hσ⟩ := second_kernel_action h (!i) hplace' hnat' hcommy.le
  have hfull := (source_suzuki_product_and_intersection_commutator h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin).2.2.2.1
  have hcent := source_center_centralizes_star_of_neighbor_inclusion h (!i)
    (by simpa only [Bool.not_not] using hzy) Ry (by simpa only [Bool.not_not] using hRy)
  have hnt := second_kernel_action_nontrivial h (!i) hplace' hnat' hcommy hcent hfull σ₀ hσ
  let eA := (originalQuotient h (!i)).symm.trans eSuz
  let π := eA.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  let ρ := σ₀.comp eA.symm.toMonoidHom
  have hρnt : ρ ≠ 1 := by
    intro he
    apply hnt
    apply MonoidHom.ext
    intro z
    apply LinearMap.ext
    intro v
    have hh := DFunLike.congr_fun (DFunLike.congr_fun he (eA z)) v
    change σ₀ (eA.symm (eA z)) v = v at hh
    change σ₀ z v = v
    simpa only [eA.symm_apply_apply] using hh
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 n hn).1
  have hf : Function.Injective ρ := ρ.ker_eq_bot_iff.mp
    (ρ.normal_ker.eq_bot_or_eq_top.resolve_right
      (fun hk => hρnt (MonoidHom.ker_eq_top_iff.mp hk)))
  let f := π.comp (inclusion hXA)
  obtain ⟨hi,_,J,hJ⟩ := source_suzuki_first_index h (!i) hb hc hxa hxadj.symm hadj.symm hn
    eSuz (by cases i <;> exact e) Ry hRy
  have hJ' : f.range = omegaOneAmbient (J : Subgroup _) := by
    rw [MonoidHom.range_comp,inclusion_range]
    exact hJ
  have hact : ∀ u : X, ∀ v : D,
      ρ (f u) (Additive.ofMul (QuotientGroup.mk v)) =
        Additive.ofMul (QuotientGroup.mk ⟨(u : G₀ L S) * v * (u : G₀ L S)⁻¹,
          le_normalizer_iff.mp hXD u u.property v v.property⟩) := by
    intro u v
    change σ₀ (eA.symm (eA (QuotientGroup.mk (inclusion hXA u)))) _ = _
    rw [eA.symm_apply_apply]
    exact congrArg Additive.ofMul (hσ (inclusion hXA u) v)
  have hlow : q^2 ≤ K.relIndex P := suzuki_commutator_section_index_lower
    D K X P inf_le_right hXD hn ρ hf f J hJ' hact hcomm
  have hYcard : Nat.card Y = q^5 :=
    (source_suzuki_center_layer_of_intersection h i hb hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat).2.1
  let : Finite (K ⊓ P : Subgroup (G₀ L S)) := Finite.of_injective
    (inclusion (show K ⊓ P ≤ P from inf_le_right)) (inclusion_injective _)
  have hsmallcard : q^5 ≤ Nat.card (K ⊓ P : Subgroup (G₀ L S)) := by
    rw [←hYcard]
    exact Nat.card_le_card_of_injective (inclusion (le_inf hYK (le_inf hYV hYD))) (inclusion_injective _)
  have hPcard : q^7 ≤ Nat.card P := by
    have hm := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) (K ⊓ P) P bot_le inf_le_right
    rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right] at hm
    calc q^7 = q^5*q^2 := by ring
         _ ≤ Nat.card (K ⊓ P : Subgroup (G₀ L S)) * K.relIndex P := Nat.mul_le_mul hsmallcard hlow
         _ = Nat.card P := hm
  have hiU : q ≤ P.relIndex U := by
    change q ≤ (U ⊓ D).relIndex U
    rw [inf_relIndex_left]
    have hiX : D.relIndex X = q := by simpa only [inf_relIndex_left] using hi
    rw [←hiX]
    exact relIndex_le_of_le_right hXV index_ne_zero_of_finite
  have hUcard : q^8 ≤ Nat.card U := by
    have hm := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) P U bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left] at hm
    calc q^8 = q^7*q := by ring
         _ ≤ Nat.card P * P.relIndex U := Nat.mul_le_mul hPcard hiU
         _ = Nat.card U := hm
  obtain ⟨_,_,_,_,hWcard,_⟩ := source_suzuki_span_natural h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  have hWV : W ≤ U :=
    (source_linear_second_kernel_span h i hb hxadj hne T hT e hcommy.le hnear).2.2.1
  have hindex : q^3 ≤ W.relIndex U := by
    have hm := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) W U bot_le hWV
    rw [relIndex_bot_left,relIndex_bot_left,hWcard,hfield] at hm
    apply Nat.le_of_mul_le_mul_left (c := q^5) _ (by dsimp [q]; positivity)
    calc q^5*q^3 = q^8 := by ring
         _ ≤ Nat.card U := hUcard
         _ = q^5*W.relIndex U := hm.symm
  have hq : 1 < q := Nat.one_lt_pow (by omega) (by decide)
  refine ⟨by simpa only [hfield] using hUcard,by simpa only [hfield] using hindex,?_,?_⟩
  · rw [hfield]
    exact (Nat.pow_lt_pow_right hq (by decide : 2 < 3)).trans_le hindex
  · rw [relIndex_map_map_of_injective W U (G₀ L S).subtype_injective,hfield]
    exact hindex

/-- The radius-two span lies in the third-kernel centralizer and forces
its quotient over W to have order at least q³. The entire second kernel
is fixed modulo W by the actual middle star. -/
theorem source_suzuki_centralizer_growth_and_fixed_kernel
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
    let N := ballKernel F m 2
    let C := Q F m ⊓ centralizer (ballKernel F m 3 : Set (G₀ L S))
    let W := conjugateSpanBy (V F y 1 ⊓ Q F x) (stabilizer F m)
    V F m 2 ≤ C ∧ Nat.card k ^ 3 ≤ W.relIndex C ∧
    ⁅N,star L S i⁆ ≤ W ∧
    ⁅N.map (G₀ L S).subtype,starredParabolic L S (if i then 1 else 0)⁆ ≤
      W.map (G₀ L S).subtype := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let A := star L S i
  let H := ballKernel F m 3
  let N := ballKernel F m 2
  let C := Q F m ⊓ centralizer (H : Set (G₀ L S))
  let Y := V F y 1
  let W := conjugateSpanBy (Y ⊓ Q F x) (stabilizer F m)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite C := Finite.of_injective
    (inclusion (show C ≤ stabilizer F m from inf_le_left.trans (Q_le_stabilizer F m)))
    (inclusion_injective _)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have ht := source_suzuki_third_kernel_layer h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
  have hfull := (source_suzuki_full_linear_third_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch).1
  have hHC (z : Vertex F) (hz : (graph F).Adj m z) :
      V F z 1 ≤ centralizer (H : Set (G₀ L S)) := by
    let : IsElementaryAbelian 2 (V F z 1) := V_elementary F (reduced_triple h).generate hZ
      (reduced_kernel_sylow h) hb z
    have hHz : H ≤ V F z 1 := by
      change ballKernel F m 3 ≤ V F z 1
      rw [hfull,ht.2.1]
      exact iInf_le_of_le z (iInf_le _ hz)
    exact (le_centralizer (V F z 1)).trans (centralizer_le hHz)
  have hVC : V F m 2 ≤ C := by
    apply le_inf (Noncommuting.graph_V_le_Q_of_short (reduced_triple h) (reduced_kernel_sylow h) m hb)
    apply iSup_le
    intro z
    apply iSup_le
    intro hz
    have hdist : (graph F).edist m z ≠ ⊤ := ne_top_of_le_ne_top
      (by simp : ((2 : ℕ) : ℕ∞) ≠ ⊤) hz
    obtain ⟨p,hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hdist
    have hlen : p.length ≤ 2 := ENat.natCast_le_natCast.mp (hp ▸ hz)
    cases p with
    | nil => exact (Z_neighbor_le_V F hadj.symm).trans (hHC y hadj)
    | @cons _ u _ hu p =>
      have hzu : z ∈ ball F u 1 := p.edist_le.trans
        (ENat.natCast_le_natCast.mpr (by have hh : p.length + 1 ≤ 2 := hlen; omega))
      have hzV : Z F z ≤ V F u 1 := le_iSup_of_le z (le_iSup_of_le hzu le_rfl)
      exact hzV.trans (hHC u hu)
  have hsize : Nat.card k ^ 3 ≤ W.relIndex C :=
    (source_suzuki_radius_two_span_growth h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).2.1.trans
        (relIndex_le_of_le_right hVC index_ne_zero_of_finite)
  have hNC : N ≤ C := (source_suzuki_centralizer_second_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch).2.1
  have hNQz (z : Vertex F) (hz : (graph F).Adj m z) : N ≤ Q F z :=
    CommutingTrivial.two_subgroup_le_Q F z (reduced_kernel_sylow h z)
      ((isPGroup_pCoreIn 2 _).to_le (hNC.trans inf_le_left)) (ballKernel_succ_le F hz 1)
  have hspan := source_linear_second_kernel_span h i hb hxadj hne T hT e hcommy.le hnear
  have hnW : stabilizer F m ≤ normalizer (W : Set (G₀ L S)) := hspan.2.2.2.1
  have hWY : W ⊓ Y = Y ⊓ Q F x := hspan.2.2.2.2.1
  have hYW : Y ⊓ N ≤ W := ((inf_le_inf_left Y (hNQz x hxadj)).trans hWY.ge).trans inf_le_left
  have hQyA : Q F y ≤ A := (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  have hQxA : Q F x ≤ A := (le_sup_left.trans hR.ge).trans (map_subtype_le _)
  have hQmA : Q F m ≤ A := (le_sup_right.trans hT.ge).trans (map_subtype_le _)
  have hder := (source_suzuki_core_derived_eq_span h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).1
  have hNy : ⁅N,Q F y⁆ ≤ W := (le_inf
    ((commutator_mono (hNQz y hadj) le_rfl).trans hder.le)
    (le_normalizer_iff_commutator_le_left.mp
      ((hQyA.trans (star_le_stabilizer i)).trans (stabilizer_le_normalizer_ballKernel F m 2)))).trans hYW
  obtain ⟨g,hg,hgy⟩ := star_locally_transitive h i hadj hxadj
  have hgm : g ∈ stabilizer F m := star_le_stabilizer i hg
  have hNg : N.map (MulAut.conj g).toMonoidHom = N :=
    mem_normalizer_iff_map_conj_eq.mp (stabilizer_le_normalizer_ballKernel F m 2 hgm)
  have hWg : W.map (MulAut.conj g).toMonoidHom = W := mem_normalizer_iff_map_conj_eq.mp (hnW hgm)
  have hNx : ⁅N,Q F x⁆ ≤ W := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hNy
    rwa [map_commutator,hNg,hWg,←Q_translate F,hgy] at hh
  have hNm : ⁅N,Q F m⁆ ≤ W := (commutator_mono hNC le_rfl).trans
    (source_suzuki_centralizer_span_frattini h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).2.1
  have hAW : A ≤ normalizer (W : Set (G₀ L S)) := (star_le_stabilizer i).trans hnW
  have hNA : ⁅N,A⁆ ≤ W := by
    change ⁅N,star L S i⁆ ≤ W
    rw [star_three_core_generation h i hxadj hne T R hT hR,commutator_comm]
    exact commutator_sup_le_of_relative_normal A (Q F y ⊔ Q F x) (Q F m) N W hAW
      (sup_le hQyA hQxA) hQmA
      (commutator_sup_le_of_relative_normal A (Q F y) (Q F x) N W hAW hQyA hQxA
        (by rwa [commutator_comm]) (by rwa [commutator_comm]))
      (by rwa [commutator_comm])
  refine ⟨hVC,hsize,hNA,?_⟩
  have hh := map_mono (f := (G₀ L S).subtype) hNA
  rw [map_commutator] at hh
  change ⁅N.map (G₀ L S).subtype,
    ((starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S)).map (G₀ L S).subtype⁆ ≤ _ at hh
  rwa [map_subgroupOf_eq_of_le (star_le_completion _)] at hh
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
