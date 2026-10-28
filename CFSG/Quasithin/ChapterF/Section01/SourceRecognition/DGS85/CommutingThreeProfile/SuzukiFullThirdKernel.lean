module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiKernelOmega
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiFullThirdKernelUpper
public import Theory.Representation.SL2.SmallTwoGroupAction
public import Theory.GroupTheory.SolvableResidual.PerfectQuotient
public import Theory.GroupTheory.AmalgamGraph.NormalTwoDetection
public import Theory.Frattini.QuadraticCentralizer
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# The full linear third kernel

Let N be the radius-three kernel and H the intersection of the neighboring
Suzuki spans. The earlier geometry makes H elementary and central in N,
with [N:H] at most q. The perfect residual of the actual starred parabolic
has two-core quotient SL₂(q). Its action on N/H is trivial by the binary
minimum-degree bound, so the Frattini subgroup of N centralizes that residual.

The Frattini subgroup is normal in the full vertex stabilizer. If it were
nontrivial, Sylow-center detection and minimality would put the natural
center inside it. The faithful natural-center action would then put the
perfect residual in the two-core, contradicting its SL₂(q) quotient.
Thus N is elementary, and the proved omega identity identifies N with H.
The theorem retains exactly the full-third-upper-bound hypotheses and the
literal original completion inclusion; no central or order-only shortcut
is used.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.9), printed p.188. The natural W/H action and the remaining profile
clauses are separate obligations.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem small_central_quotient_frattini
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (A N H : Subgroup G) [Finite A] [Finite N] [IsElementaryAbelian 2 H]
    (hN : IsPGroup 2 N)
    (hNH : N ≤ centralizer (H : Set G))
    (hAN : A ≤ normalizer (N : Set G)) (hAH : A ≤ normalizer (H : Set G))
    (e : (A ⧸ pCore 2 A) ≃* SL(2,k))
    {d : ℕ} (hd : 1 < d) (hk : Nat.card k = 2^d)
    (hi : H.relIndex N ≤ 2^d) :
    (frattini N).map N.subtype ≤ centralizer ((solvableResidual A).map A.subtype : Set G) := by
  have hlarge : 3 < Nat.card k := by
    rw [hk]
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ d)
    norm_num at hh
    omega
  let : Group.IsPerfect SL(2,k) := GorensteinWalter.sl2_isPerfect_of_card_gt_three k hlarge
  let : Group.IsPerfect (A ⧸ pCore 2 A) := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let R := solvableResidual A
  let P := N ⧸ H.subgroupOf N
  let : (H.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer
    (hNH.trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨ρ,hρ⟩ := exists_quotient_conjugation_action A N H hAN hAH inferInstance
  let eR := (solvableResidualPCoreQuotientEquiv (G := A) 2).trans e
  have hp : IsPGroup 2 P := hN.to_quotient _
  have hsmall : primeRank 2 (P ⧸ frattini P) < 2*d := by
    have hcard : Nat.card (P ⧸ frattini P) ≤ 2^d :=
      (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (frattini P))).trans hi
    have hr : primeRank 2 (P ⧸ frattini P) ≤ d :=
      (primeRank_le_iff_elementary_card_le _).mpr (by
        intro D _
        exact D.card_le_card_group.trans hcard)
    omega
  have hzero := Representation.SL2.action_eq_one_of_small_frattini eR (by omega) hk hp hsmall
    (ρ.comp R.subtype)
  have hcomm : ⁅N,R.map A.subtype⁆ ≤ H := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro r hr n hn
    obtain ⟨s,hs,rfl⟩ := hr
    have hh := DFunLike.congr_fun (DFunLike.congr_fun hzero (⟨s,hs⟩ : R))
      (QuotientGroup.mk' (H.subgroupOf N) (⟨n,hn⟩ : N))
    change ρ s (QuotientGroup.mk' (H.subgroupOf N) ⟨n,hn⟩) =
      QuotientGroup.mk' (H.subgroupOf N) ⟨n,hn⟩ at hh
    rw [hρ] at hh
    have hc := QuotientGroup.eq_iff_div_mem.mp hh
    change (s : G) * n * (s : G)⁻¹ / n ∈ H at hc
    simpa only [commutatorElement_def, div_eq_mul_inv, Subgroup.subtype_apply] using hc
  exact frattini_image_le_centralizer_of_elementary_commutator N (R.map A.subtype) H hN hcomm hNH

/-- The full radius-three kernel is the geometric intersection, in both completions. -/
theorem source_suzuki_full_linear_third_kernel
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
    let y := base F (!i)
    ballKernel F m 3 = V F x 1 ⊓ V F y 1 ∧
    (ballKernel F m 3).map (G₀ L S).subtype =
      (V F x 1 ⊓ V F y 1).map (G₀ L S).subtype := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let A := star L S i
  let N := ballKernel F m 3
  let H := V F x 1 ⊓ V F y 1
  let D := (frattini N).map N.subtype
  let Zm := Z F m
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer i))
    (inclusion_injective _)
  let : Finite N := Finite.of_injective (inclusion (ballKernel_le_stabilizer F m 3))
    (inclusion_injective _)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hk : 4 ≤ Nat.card k := by
    rw [hfield]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ 2*n+1)
  have hNQ : N ≤ Q F m := (ballKernel_antitone F m (by omega : 2 ≤ 3)).trans
    (source_suzuki_second_kernel_le_core h (!i) eSuz (by cases i <;> exact e) hk m)
  have hpN : IsPGroup 2 N := (isPGroup_pCoreIn 2 _).to_le hNQ
  have hNA : N ≤ A := hNQ.trans (by rw [←star_core h i]; exact pCoreIn_le 2 _)
  let : IsElementaryAbelian 2 (V F y 1) := V_elementary F
    (reduced_triple h).generate (fun v => (source_Z_Q_U (reduced_triple h) v).1)
    (reduced_kernel_sylow h) hb y
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.of_injective
    (inclusion (show H ≤ V F y 1 from inf_le_right)) (inclusion_injective _)
  have hu := source_suzuki_full_linear_third_kernel_upper h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
  have ht := source_suzuki_third_kernel_layer h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
  have hAN : A ≤ normalizer (N : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans (stabilizer_le_normalizer_ballKernel F m 3)
  have hAH : A ≤ normalizer (H : Set (G₀ L S)) := (star_le_stabilizer i).trans ht.1
  have hNH : N ≤ centralizer (H : Set (G₀ L S)) := by
    intro u huN
    apply mem_centralizer_iff.mpr
    intro z hzH
    have he := mem_center_iff.mp (hu.2.1 (show (⟨z,hu.1 hzH⟩ : N) ∈ H.subgroupOf N from hzH))
      (⟨u,huN⟩ : N)
    exact (congrArg N.subtype he).symm
  let eA := (originalQuotient h i).symm.trans e
  have hDC : D ≤ centralizer ((solvableResidual A).map A.subtype : Set (G₀ L S)) :=
    small_central_quotient_frattini A N H hpN hNH hAN hAH eA
      (by omega : 1 < 2*n+1) hfield hu.2.2.1
  have hDA : D ≤ A := (map_subtype_le _).trans hNA
  have hAZ : A ≤ normalizer (Zm : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans (stabilizer_normalizes_Z F m)
  have hAD : A ≤ normalizer (D : Set (G₀ L S)) :=
    hAN.trans (normalizer_le_normalizer_characteristic_image N (frattini N))
  let I := (D ⊓ Zm).subgroupOf A
  let : I.Normal := normal_subgroupOf_of_le_normalizer
    (le_trans (le_inf hAD hAZ) inf_normalizer_le_normalizer_inf)
  have hZbot : D ⊓ Zm = ⊥ := by
    rcases hmin I inferInstance (subgroupOf_mono A inf_le_right) with hi | hi
    · have hm := congrArg (Subgroup.map A.subtype) hi
      change ((D ⊓ Zm).subgroupOf A).map A.subtype = (⊥ : Subgroup A).map A.subtype at hm
      rwa [map_subgroupOf_eq_of_le (inf_le_left.trans hDA),Subgroup.map_bot] at hm
    · have hZD : Zm ≤ D := by
        intro z hz
        have hzA : z ∈ A := (ht.2.2.2.2.2.2.1.trans (hu.1.trans hNA)) hz
        have hzI : (⟨z,hzA⟩ : A) ∈ I := hi ▸ hz
        exact hzI.1
      have hRC : (solvableResidual A).map A.subtype ≤ centralizer (Zm : Set (G₀ L S)) :=
        le_centralizer_iff.mpr (hZD.trans hDC)
      have hRQ : (solvableResidual A).map A.subtype ≤ Q F m :=
        le_trans (le_inf (map_subtype_le _) hRC) (natural_center_centralizer_le_core _ _ _ hnat)
      have hRA : solvableResidual A ≤ pCore 2 A := by
        intro r hr
        have hh := hRQ (mem_map.mpr ⟨r,hr,rfl⟩)
        rw [←star_core h i] at hh
        obtain ⟨t,ht,he⟩ := mem_map.mp hh
        exact (A.subtype_injective he) ▸ ht
      have hlarge : 3 < Nat.card k := by
        rw [hfield]
        have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 3 ≤ 2*n+1)
        norm_num at hh
        omega
      let : Group.IsPerfect SL(2,k) := GorensteinWalter.sl2_isPerfect_of_card_gt_three k hlarge
      let : Group.IsPerfect (A ⧸ pCore 2 A) :=
        Group.IsPerfect.ofSurjective (f := eA.symm.toMonoidHom) eA.symm.surjective
      have htriv : ∀ t : A ⧸ pCore 2 A, t = 1 := by
        intro t
        obtain ⟨r,rfl⟩ := residual_core_quotient_surjective (G := A) 2 t
        exact (QuotientGroup.eq_one_iff r.val).mpr (hRA r.property)
      let : Nontrivial SL(2,k) := Function.Injective.nontrivial
        (Matrix.SpecialLinearGroup.upperUnipotentHom_injective k)
      have : Subsingleton SL(2,k) := ⟨fun u v => eA.symm.injective
        ((htriv _).trans (htriv _).symm)⟩
      exact False.elim (not_subsingleton (α := SL(2,k)) this)
  have hDbot : D = ⊥ := normal_two_eq_bot_of_disjoint_sylowCenterSpan
    (stabilizer F m) D (hDA.trans (star_le_stabilizer i))
    ((hpN.to_subgroup (frattini N)).map N.subtype)
    ((stabilizer_le_normalizer_ballKernel F m 3).trans
      (normalizer_le_normalizer_characteristic_image N (frattini N)))
    (disjoint_iff.mpr hZbot)
  let : Fact (IsPGroup 2 N) := ⟨hpN⟩
  let : IsElementaryAbelian 2 N := frattini_eq_bot_iff_isElementaryAbelian.mp
    ((map_eq_bot_iff_of_injective (frattini N) N.subtype_injective).mp hDbot)
  have hω := source_suzuki_full_kernel_omegas h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
  have heq : N = H := (omegaOneAmbient_eq_self N).symm.trans hω.2.1
  exact ⟨heq,congrArg (Subgroup.map (G₀ L S).subtype) heq⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
