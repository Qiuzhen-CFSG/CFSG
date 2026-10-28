module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCentralizerSecondKernel
public import Theory.GroupAction.RankTwoCosetGeometry.SuccessorBallKernel
/-!
# The second-to-third kernel central series

At the linear vertex of the nonbinary Suzuki branch, put N = G_m^(2),
H = G_m^(3), and C = C_(Q_m)(H). We prove Phi(N) ≤ H and [N,C] ≤ H.
The first containment follows because N acts on the neighboring elementary
span with commutators in its fixed center line, so Phi(N) centralizes that
span and belongs to the neighbor's second kernel. For the second containment,
the sharp placement C ≤ V_x (Q_m ∩ Q_y) and the elementary quotient of Q_y
put [N,C] into that same neighbor kernel. Both groups are normal in the full
middle stabilizer; the successive-ball normal-core formula puts them in H.

Since C centralizes the elementary group H, the same square calculation also
shows that Phi(C) centralizes N. The literal quotient N/H is therefore
an elementary layer on which the actual endpoint action factors through
star/C. The final theorem retains conjugation by each original endpoint
actor and transports [N,C] ≤ H through the original completion inclusion.

All earlier source hypotheses remain explicit. These results do not yet
identify N with W or prove that C/W is elementary or irreducible.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (12.9), printed pp.188–189, the kernel series preceding the
irreducibility argument for C_(Q_alpha)(H)/W.
-/
public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- The full second kernel has elementary quotient over the full third kernel,
and the third-kernel centralizer acts trivially on this layer. -/
theorem source_suzuki_second_kernel_central_series
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
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let H := ballKernel F m 3
    let N := ballKernel F m 2
    let C := Q F m ⊓ centralizer (H : Set (G₀ L S))
    (frattini N).map N.subtype ≤ H ∧ ⁅N,C⁆ ≤ H ∧
      (frattini C).map C.subtype ≤ centralizer (N : Set (G₀ L S)) := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let H := ballKernel F m 3
  let N := ballKernel F m 2
  let C := Q F m ⊓ centralizer (H : Set (G₀ L S))
  let K := ballKernel F y 2
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite N := Finite.of_injective (inclusion (ballKernel_le_stabilizer F m 2))
    (inclusion_injective _)
  let : Finite C := Finite.of_injective
    (inclusion (show C ≤ stabilizer F m from inf_le_left.trans (Q_le_stabilizer F m)))
    (inclusion_injective _)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨hCD,hNC,hphi,hCQ⟩ := source_suzuki_centralizer_second_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
  have hNC' : N ≤ C := hNC
  have hNQ : N ≤ Q F m := hNC'.trans inf_le_left
  have hpN : IsPGroup 2 N := (isPGroup_pCoreIn 2 _).to_le hNQ
  have hpC : IsPGroup 2 C := (isPGroup_pCoreIn 2 _).to_le (show C ≤ Q F m from inf_le_left)
  have hNQz (z : Vertex F) (hz : (graph F).Adj m z) : N ≤ Q F z :=
    CommutingTrivial.two_subgroup_le_Q F z (reduced_kernel_sylow h z)
      hpN (ballKernel_succ_le F hz 1)
  have hnormN := stabilizer_le_normalizer_ballKernel F m 2
  have hnormC : stabilizer F m ≤ normalizer (C : Set (G₀ L S)) :=
    (le_inf (CommutingTrivial.stabilizer_normalizes_Q F m)
      ((stabilizer_le_normalizer_ballKernel F m 3).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hQmy : Q F m ≤ stabilizer F y :=
    ((source_Z_Q_U (reduced_triple h) m).2.trans (ballKernel_one_le_edge F hadj)).trans inf_le_right
  have hq4 : 4 ≤ Nat.card k := by
    rw [hfield]
    exact (by decide : 4 ≤ 2^2).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hQyA : Q F y ≤ star L S i := (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  have hcent : Q F y ⊓ centralizer (V F y 1 : Set (G₀ L S)) = K :=
    source_suzuki_second_kernel_centralizer h (!i) eSuz
      (by cases i <;> exact e) hq4 (by cases i <;> exact hQyA) (by cases i <;> exact hnat)
  have normal_into_third (J : Subgroup (G₀ L S)) (hJN : J ≤ N) (hJK : J ≤ K)
      (hJ : stabilizer F m ≤ normalizer (J : Set (G₀ L S))) : J ≤ H := by
    have hJm := hJN.trans (ballKernel_le_stabilizer F m 2)
    let : (J.subgroupOf (stabilizer F m)).Normal := normal_subgroupOf_of_le_normalizer hJ
    have hh : J.subgroupOf (stabilizer F m) ≤ H.subgroupOf (stabilizer F m) := by
      rw [ballKernel_succ_eq_normalCore F hadj 2]
      apply normal_le_normalCore.mpr
      intro j hj
      exact ⟨hJN hj,hJK hj⟩
    intro j hj
    exact hh (show (⟨j,hJm hj⟩ : stabilizer F m) ∈ J.subgroupOf (stabilizer F m) from hj)
  let : IsElementaryAbelian 2 (Z F y) := Z_elementary F hZ y
  have hphic : (frattini N).map N.subtype ≤ centralizer (V F y 1 : Set (G₀ L S)) :=
    frattini_image_le_centralizer_of_elementary_commutator N (V F y 1) (Z F y) hpN
      (by rw [commutator_comm]; exact (commutator_mono le_rfl (hNQz y hadj)).trans hcommy.le)
      (hNQ.trans (le_centralizer_iff.mp (hzy.trans (Z_centralizes_Q F m (hZ m)))))
  have hphiN : (frattini N).map N.subtype ≤ H := normal_into_third _ (map_subtype_le _)
    ((le_inf ((map_subtype_le _).trans (hNQz y hadj)) hphic).trans hcent.le)
    (hnormN.trans (normalizer_le_normalizer_characteristic_image N (frattini N)))
  have hder : ⁅Q F y,Q F y⁆ ≤ K := by
    let : ((ballKernel F y 2).subgroupOf (Q F y)).Normal :=
      normal_subgroupOf_of_le_normalizer
        ((Q_le_stabilizer F y).trans (stabilizer_le_normalizer_ballKernel F y 2))
    let : IsElementaryAbelian 2 (Q F y ⧸ (ballKernel F y 2).subgroupOf (Q F y)) :=
      source_second_kernel_elementary h (!i) (by cases i <;> exact hQyA)
        (by cases i <;> exact hnat) hcommy.le
    have hd := Normal.quotient_commutative_iff_commutator_le.mp
      (inferInstance : IsMulCommutative (Q F y ⧸ (ballKernel F y 2).subgroupOf (Q F y)))
    apply commutator_le.mpr
    intro u hu v hv
    exact hd (commutator_mem_commutator (mem_top (⟨u,hu⟩ : Q F y))
      (mem_top (⟨v,hv⟩ : Q F y)))
  have hfull := (source_suzuki_full_linear_third_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch).1
  have ht := source_suzuki_third_kernel_layer h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
  have hZxK : Z F x ≤ K := (hzx.trans ht.2.2.2.2.2.2.1).trans
    (hfull.ge.trans (ballKernel_succ_le F hadj 2))
  have hXQ : V F x 1 ≤ Q F m := V_le_neighbor_Q F (reduced_triple h).generate
    hZ (reduced_kernel_sylow h) hb hxadj.symm
  have hcommK : ⁅N,C⁆ ≤ K := by
    rw [commutator_comm]
    apply (commutator_mono hCD le_rfl).trans
    apply commutator_sup_le_of_relative_normal (Q F m) (V F x 1)
      (Q F m ⊓ Q F y) N K
      (hQmy.trans (stabilizer_le_normalizer_ballKernel F y 2)) hXQ inf_le_left
    · exact ((commutator_mono le_rfl (hNQz x hxadj)).trans hcommx).trans hZxK
    · exact (commutator_mono inf_le_right (hNQz y hadj)).trans hder
  have hcommN : ⁅N,C⁆ ≤ N := le_normalizer_iff_commutator_le_left.mp
    ((inf_le_left.trans (Q_le_stabilizer F m)).trans hnormN)
  have hcomm : ⁅N,C⁆ ≤ H := normal_into_third _ hcommN hcommK (by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hnormN hg),
      mem_normalizer_iff_map_conj_eq.mp (hnormC hg)])
  let : IsElementaryAbelian 2 H := by
    rw [show H = V F x 1 ⊓ V F y 1 from hfull]
    let : IsElementaryAbelian 2 (V F x 1) := V_elementary F (reduced_triple h).generate hZ
      (reduced_kernel_sylow h) hb x
    exact IsElementaryAbelian.of_le inf_le_left
  exact ⟨hphiN,hcomm,
    frattini_image_le_centralizer_of_elementary_commutator C N H hpC
      (by rwa [commutator_comm]) inf_le_right⟩

/-- The elementary N/H layer with its actual star/C action, original endpoint
conjugation, and original-completion commutator containment. -/
theorem source_suzuki_second_third_kernel_action
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
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let H := ballKernel F m 3
    let N := ballKernel F m 2
    let C := Q F m ⊓ centralizer (H : Set (G₀ L S))
    let A := star L S i
    ∃ hAN : A ≤ normalizer (N : Set (G₀ L S)),
    ∃ hC : (C.subgroupOf A).Normal,
    ∃ hH : (H.subgroupOf N).Normal,
      let := hC
      let := hH
      IsElementaryAbelian 2 (N ⧸ H.subgroupOf N) ∧
      ⁅N.map (G₀ L S).subtype,C.map (G₀ L S).subtype⁆ ≤ H.map (G₀ L S).subtype ∧
      ∃ ρ : (A ⧸ C.subgroupOf A) →* MulAut (N ⧸ H.subgroupOf N),
        ∀ a : L (if i then 1 else 0), ∀ v : N,
          ρ (QuotientGroup.mk (originalActor (L := L) (S := S) i a)) (QuotientGroup.mk v) =
            QuotientGroup.mk ⟨(originalActor (L := L) (S := S) i a : G₀ L S) * v *
              (originalActor (L := L) (S := S) i a : G₀ L S)⁻¹,
              (mem_normalizer_iff.mp (hAN
                (originalActor (L := L) (S := S) i a).property) v).mp v.property⟩ := by
  let F := reducedFamily L S
  let m := base F i
  let H := ballKernel F m 3
  let N := ballKernel F m 2
  let C := Q F m ⊓ centralizer (H : Set (G₀ L S))
  let A := star L S i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite N := Finite.of_injective (inclusion (ballKernel_le_stabilizer F m 2))
    (inclusion_injective _)
  obtain ⟨hphi,hcomm,_⟩ := source_suzuki_second_kernel_central_series h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
  have hNC : N ≤ C := (source_suzuki_centralizer_second_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch).2.1
  have hAN : A ≤ normalizer (N : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans (stabilizer_le_normalizer_ballKernel F m 2)
  have hAH : A ≤ normalizer (H : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans (stabilizer_le_normalizer_ballKernel F m 3)
  have hAC : A ≤ normalizer (C : Set (G₀ L S)) :=
    (le_inf ((star_le_stabilizer i).trans (CommutingTrivial.stabilizer_normalizes_Q F m))
      (hAH.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  let hC : (C.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hAC
  let hH : (H.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer
    ((ballKernel_le_stabilizer F m 2).trans (stabilizer_le_normalizer_ballKernel F m 3))
  let := hC
  let := hH
  have hel : IsElementaryAbelian 2 (N ⧸ H.subgroupOf N) :=
    elementary_quotient_of_frattini_le
      ((isPGroup_pCoreIn 2 _).to_le (hNC.trans inf_le_left)) _ (map_le_iff_le_comap.mp hphi)
  obtain ⟨α,hα⟩ := exists_quotient_conjugation_action A N H hAN hAH hH
  have hkill : C.subgroupOf A ≤ α.ker :=
    quotient_conjugation_action_kills_commutator_layer A N H C hH hAN hcomm α hα
  let ρ := QuotientGroup.lift (C.subgroupOf A) α hkill
  refine ⟨hAN,hC,hH,hel,?_,ρ,?_⟩
  · have hh := map_mono (f := (G₀ L S).subtype) hcomm
    rwa [map_commutator] at hh
  · intro a v
    exact hα (originalActor (L := L) (S := S) i a) v

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
