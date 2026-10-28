module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCentralizerNatural
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.MarkedComplementIndex
public import Theory.Representation.SL2.NaturalCoprimeCentralizer
public import Theory.GroupTheory.CoprimeFixedLayer
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.SpecificGroups.SL2.SylowNormalizerCard
/-!
# Odd-torus centralizers in the Suzuki third-kernel layers

At the linear vertex m put H = G_m^(3) and C = C_(Q_m)(H).
Every nontrivial odd subgroup D of the starred parabolic acts without
fixed points on the natural center Z_m. The actual equivariant
isomorphism Q_m/C ≃ Z_m then puts C_(Q_m)(D) inside C.

The already established identity [H,star_m] = Z_m and coprime splitting
now give [H,D] = Z_m and |C_H(D)| = q. In particular these conclusions
hold for the literal intersection of a full-edge complement with star_m:
its image supplements a Sylow in the marked SL₂ normalizer, whose order
q(q-1) proves that this intersection is nontrivial for q > 2. The final
consumer preserves the original completion inclusion in both the
centralizer and commutator formulas.

The stronger bound C_(Q_m)(D) ≤ H still requires control of fixed
elements in C outside H. Neither this module nor the order-q calculation
asserts that bound, irreducibility of C/W, or G_m^(2) = W. All earlier
source markings, natural-center and reciprocal-commutator inputs remain
explicit; the full Chapter 12/13.1 assembly remains outstanding.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (12.9), printed pp.188--189, the nonbinary torus-centralizer step.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- The literal natural center and centralizer quotient determine the odd actor's
fixed subgroup in the full third kernel. -/
theorem source_suzuki_odd_centralizer_layers
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
    (D : Subgroup (G₀ L S)) (hDA : D ≤ star L S i)
    (hodd : Odd (Nat.card D)) (hneD : D ≠ ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let H := ballKernel F m 3
    let Zm := Z F m
    let C := Q F m ⊓ centralizer (H : Set (G₀ L S))
    Q F m ⊓ centralizer (D : Set (G₀ L S)) ≤ C ∧
      Zm ⊓ centralizer (D : Set (G₀ L S)) = ⊥ ∧
      ⁅H,D⁆ = Zm ∧
      Nat.card (H ⊓ centralizer (D : Set (G₀ L S)) : Subgroup (G₀ L S)) = Nat.card k := by
  let F := reducedFamily L S
  let m := base F i
  let A := star L S i
  let Qm := Q F m
  let Zm := Z F m
  let H := ballKernel F m 3
  let C := Qm ⊓ centralizer (H : Set (G₀ L S))
  let J := centralizer (D : Set (G₀ L S))
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer i)) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion hDA) (inclusion_injective _)
  let : Finite Qm := Finite.of_injective (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  let : Finite Zm := Finite.of_injective (inclusion (Z_le_stabilizer F m)) (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion (ballKernel_le_stabilizer F m 3)) (inclusion_injective _)
  let : IsElementaryAbelian 2 Zm := Noncommuting.graph_Z_elementary (reduced_triple h) m
  let : IsElementaryAbelian 2 (V F x 1) := V_elementary F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h)
    (by change 2 < b (reducedFamily L S); omega) x
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hZQ : Zm ≤ Qm := (hZ m).trans (map_subtype_le _)
  have hcop (U : Subgroup (G₀ L S)) [Finite U] (hu : IsPGroup 2 U) :
      Nat.Coprime (Nat.card D) (Nat.card U) := by
    obtain ⟨r,hr⟩ := hu.exists_card_eq
    rw [hr]
    exact (Nat.coprime_two_right.mpr hodd).pow_right r
  have hDQ : Disjoint D Qm := disjoint_of_coprime_natCard (hcop Qm (isPGroup_pCoreIn 2 _))
  obtain ⟨t,ht,ht1⟩ : ∃ t ∈ D, t ≠ 1 := by
    by_contra! hh
    exact hneD (eq_bot_iff.mpr fun t ht => mem_bot.mpr (hh t ht))
  let tA : A := ⟨t,hDA ht⟩
  have hto : Odd (orderOf tA) := by
    rw [←Subgroup.orderOf_coe]
    exact hodd.of_dvd_nat (D.orderOf_dvd_natCard ht)
  have htQ : t ∉ Qm := fun htq => ht1 (mem_bot.mp (hDQ.eq_bot ▸ (show t ∈ D ⊓ Qm from ⟨ht,htq⟩)))
  obtain ⟨κ,_,_,_,π,hπ,hker,⟨d⟩⟩ := hnat
  have hω : Stellmacher.omegaOneCenterAmbient A = ⊥ := by
    apply bot_unique
    intro z hz'
    obtain ⟨hzA,_,hzc⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz'
    have hm : (⟨z,hzA⟩ : A) ∈ center A := mem_center_iff.mpr (fun a => Subtype.ext (hzc a a.property))
    rw [hz,mem_bot] at hm
    exact congrArg Subtype.val hm
  let d₀ : Representation.BinaryConjugationSection A Zm ⊥
      (Representation.SL2NaturalOffenders.NoStrong.natural.comp π) := hω ▸ d
  have hπt : π tA ≠ 1 := by
    intro he
    have hm : tA ∈ π.ker := he
    rw [hker] at hm
    exact htQ hm
  have hZJ : Zm ⊓ J = ⊥ := by
    apply bot_unique
    exact (inf_le_inf_left Zm (centralizer_le (Set.singleton_subset_iff.mpr ht))).trans
      (Representation.SL2.natural_section_odd_centralizer_le π d₀ tA hto hπt)
  obtain ⟨hN,_,E,hE⟩ := source_suzuki_centralizer_quotient h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin
    ⟨κ,inferInstance,inferInstance,inferInstance,π,hπ,hker,⟨d⟩⟩ hbranch
  let := hN
  have hQJ : Qm ⊓ J ≤ C := by
    rintro u ⟨hu,huj⟩
    let uQ : Qm := ⟨u,hu⟩
    let z := E (QuotientGroup.mk uQ)
    have hzJ : (z : G₀ L S) ∈ J := by
      intro a ha
      let aA : A := ⟨a,hDA ha⟩
      have hh := hE aA uQ
      have he : (⟨a*u*a⁻¹,
          (mem_normalizer_iff.mp (CommutingTrivial.stabilizer_normalizes_Q F m
            (star_le_stabilizer i aA.property)) u).mp hu⟩ : Qm) = uQ := by
        apply Subtype.ext
        exact (mul_inv_eq_iff_eq_mul).mpr (huj a ha)
      change (E (QuotientGroup.mk _) : G₀ L S) = a * (z : G₀ L S) * a⁻¹ at hh
      rw [he] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh.symm
    have hz1 : z = 1 := Subtype.ext (mem_bot.mp (hZJ ▸ (show (z : G₀ L S) ∈ Zm ⊓ J from ⟨z.property,hzJ⟩)))
    have hu1 : QuotientGroup.mk uQ = (1 : Qm ⧸ (centralizer (H : Set (G₀ L S))).subgroupOf Qm) :=
      E.injective (hz1.trans E.map_one.symm)
    exact ⟨hu,(QuotientGroup.eq_one_iff uQ).mp hu1⟩
  have hnat' : Noncommuting.HasNaturalCenter A Zm Qm :=
    ⟨κ,inferInstance,inferInstance,inferInstance,π,hπ,hker,⟨d⟩⟩
  have ht := source_suzuki_third_kernel_layer h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat'
  have hf := (source_suzuki_full_linear_third_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat' hbranch).1
  have hZH : Zm ≤ H := ht.2.2.2.2.2.2.1.trans hf.ge
  have hHA : ⁅H,A⁆ = Zm := by rw [show H = V F x 1 ⊓ V F (base F (!i)) 1 from hf]; exact ht.2.2.2.2.2.1
  have hHcard : Nat.card H = Nat.card k ^ 3 := by rw [show H = V F x 1 ⊓ V F (base F (!i)) 1 from hf,ht.2.2.2.2.2.2.2.2.1,←hfield]
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.of_le (hf.le.trans inf_le_left)
  have hHD : D ≤ normalizer (H : Set (G₀ L S)) := hDA.trans ((star_le_stabilizer i).trans (stabilizer_le_normalizer_ballKernel F m 3))
  have hZD : D ≤ normalizer (Zm : Set (G₀ L S)) := hDA.trans d₀.normalized
  have hZsplit := eq_commutator_sup_centralizer_of_finite_solvable_coprime Zm D hZD
    (Group.isSolvable_of_comm fun a b => mul_comm a b) (hcop Zm ((isPGroup_pCoreIn 2 _).to_le hZQ))
  have hZDcomm : ⁅Zm,D⁆ = Zm := by
    change Zm = ⁅Zm,D⁆ ⊔ (Zm ⊓ J) at hZsplit
    simpa only [hZJ,sup_bot_eq] using hZsplit.symm
  have hHDcomm : ⁅H,D⁆ = Zm := le_antisymm ((commutator_mono le_rfl hDA).trans hHA.le)
    (hZDcomm.ge.trans (commutator_mono hZH le_rfl))
  have hHsplit : H = Zm ⊔ (H ⊓ J) := by
    have hh := eq_commutator_sup_centralizer_of_finite_solvable_coprime H D hHD
      (Group.isSolvable_of_comm fun a b => mul_comm a b) (hcop H (IsElementaryAbelian.isPGroup 2 H))
    simpa only [hHDcomm] using hh
  have hd : Disjoint Zm (H ⊓ J) := disjoint_iff.mpr (le_antisymm
    ((inf_le_inf_left Zm inf_le_right).trans hZJ.le) bot_le)
  have hnz : H ⊓ J ≤ normalizer (Zm : Set (G₀ L S)) :=
    (inf_le_left.trans ((le_centralizer H).trans (centralizer_le hZH))).trans (Subgroup.centralizer_le_normalizer _)
  have hh := card_sup_eq_mul_of_normalizes_of_disjoint Zm (H ⊓ J) hnz hd
  rw [←hHsplit,hHcard,show Nat.card Zm = Nat.card k ^ 2 from hcard] at hh
  have hsize : Nat.card (H ⊓ J : Subgroup (G₀ L S)) = Nat.card k := by
    have hp : 0 < Nat.card k := Nat.card_pos
    nlinarith [pow_pos hp 2]
  exact ⟨hQJ,hZJ,hHDcomm,hsize⟩
/-- The linear part of the actual full-edge complement is nontrivial when q > 2. -/
theorem source_nonbinary_linear_complement_ne_bot
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hq : 2 < Nat.card k)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    {y : Vertex (reducedFamily L S)}
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (K : Subgroup (stabilizer (reducedFamily L S) y ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i) : Subgroup (G₀ L S)))
    (hK : (pCore 2 (stabilizer (reducedFamily L S) y ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i) :
      Subgroup (G₀ L S))).IsComplement' K)
    (hodd : Odd (Nat.card K)) :
    (K.map (stabilizer (reducedFamily L S) y ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i) : Subgroup (G₀ L S)).subtype) ⊓ star L S i ≠ ⊥ := by
  let F := reducedFamily L S
  let A := star L S i
  let E := stabilizer F y ⊓ stabilizer F (base F i)
  let D := K.map E.subtype
  let q := ((originalQuotient h i).symm.trans e).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  obtain ⟨T,_,hs⟩ := source_marked_edge_complement_supplement h i hy e K hK hodd
  intro hd
  have hda : D.subgroupOf A = ⊥ := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_bot,subgroupOf_map_subtype]
    exact hd
  change (T : Subgroup SL(2,k)) ⊔ (D.subgroupOf A).map q = normalizer (T : Set SL(2,k)) at hs
  rw [hda,Subgroup.map_bot,sup_bot_eq] at hs
  have hc : Nat.card T = Nat.card k := (Nat.card_congr (T.equiv (Matrix.SpecialLinearGroup.upperUnipotentSylow k 2)).toEquiv).trans
    (Matrix.SpecialLinearGroup.card_upperUnipotent k)
  have hh := Matrix.SpecialLinearGroup.card_sylow_normalizer_even T
  simp only [Sylow.coe_coe] at hh
  rw [←hs,hc] at hh
  have hp : 0 < Nat.card k := Nat.card_pos
  have hsub : Nat.card k - 1 + 1 = Nat.card k := Nat.sub_add_cancel (by omega)
  nlinarith

/-- The actual full-edge complement has the computed third-kernel centralizer,
with the literal original completion inclusion. -/
theorem source_suzuki_edge_torus_centralizer_layers
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
    (K : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i) : Subgroup (G₀ L S)))
    (hK : (pCore 2 (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i) :
      Subgroup (G₀ L S))).IsComplement' K)
    (hoddK : Odd (Nat.card K)) :
    let F := reducedFamily L S
    let m := base F i
    let y := base F (!i)
    let A := star L S i
    let D := K.map (stabilizer F y ⊓ stabilizer F m : Subgroup (G₀ L S)).subtype ⊓ A
    let H := ballKernel F m 3
    let Zm := Z F m
    let C := Q F m ⊓ centralizer (H : Set (G₀ L S))
    D ≠ ⊥ ∧ Odd (Nat.card D) ∧
      Q F m ⊓ centralizer (D : Set (G₀ L S)) ≤ C ∧
      Zm ⊓ centralizer (D : Set (G₀ L S)) = ⊥ ∧
      ⁅H,D⁆ = Zm ∧
      Nat.card (H ⊓ centralizer (D : Set (G₀ L S)) : Subgroup (G₀ L S)) = Nat.card k ∧
      (Q F m).map (G₀ L S).subtype ⊓ centralizer (D.map (G₀ L S).subtype : Set G) ≤
        C.map (G₀ L S).subtype ∧
      ⁅H.map (G₀ L S).subtype,D.map (G₀ L S).subtype⁆ = Zm.map (G₀ L S).subtype ∧
      Nat.card (H.map (G₀ L S).subtype ⊓ centralizer (D.map (G₀ L S).subtype : Set G) : Subgroup G) = Nat.card k := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let A := star L S i
  let E := stabilizer F y ⊓ stabilizer F m
  let D := K.map E.subtype ⊓ A
  let H := ballKernel F m 3
  let Zm := Z F m
  let C := Q F m ⊓ centralizer (H : Set (G₀ L S))
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer F m from inf_le_right)) (inclusion_injective _)
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hq : 2 < Nat.card k := by
    rw [hfield]
    have hh := Nat.pow_lt_pow_right (by decide : 1 < 2) (show 1 < 2*n+1 by omega)
    simpa only [pow_one] using hh
  have hneD : D ≠ ⊥ := source_nonbinary_linear_complement_ne_bot h i hq e hadj K hK hoddK
  have hoddD : Odd (Nat.card D) := by
    have hoddMap : Odd (Nat.card (K.map E.subtype)) := by
      rwa [card_map_of_injective E.subtype_injective]
    exact hoddMap.of_dvd_nat (card_dvd_of_le (show D ≤ K.map E.subtype from inf_le_left))
  obtain ⟨hQ,hZ,hHD,hsize⟩ := source_suzuki_odd_centralizer_layers h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
    D inf_le_right hoddD hneD
  refine ⟨hneD,hoddD,hQ,hZ,hHD,hsize,?_,?_,?_⟩
  · have hh := map_mono (f := (G₀ L S).subtype) hQ
    rwa [←map_inf_centralizer_of_injective _ (G₀ L S).subtype_injective] at hh
  · rw [←map_commutator,hHD]
  · rw [map_inf_centralizer_of_injective _ (G₀ L S).subtype_injective,
      card_map_of_injective (G₀ L S).subtype_injective]
    exact hsize

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
