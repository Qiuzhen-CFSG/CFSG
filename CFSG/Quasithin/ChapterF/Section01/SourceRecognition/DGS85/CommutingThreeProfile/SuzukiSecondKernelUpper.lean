module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanPair
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanFixedIndex
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SecondKernelFixedPoints
public import Theory.GroupTheory.TwoSeedFixedIndex
public import Theory.Representation.Suzuki.MinimalDegree

/-!
# The geometric q⁴ bound and the actual irreducible second-kernel layer

Two literal neighboring spans generate the marked Suzuki action modulo Q.
Each has fixed index at most q², and reciprocal three-subgroups rotation
has already removed the fixed cosets of the whole action. Their intersection
therefore gives [Q:Q ∩ G²] ≤ q⁴. Combined with the previously constructed
faithful original action and Suzuki minimum degree, this proves equality
and irreducibility on the same quotient, retaining every conjugation map.

This proves the nonbinary restricted second-kernel layer in (12.6), with
no geometric upper bound or generation premise. The original Suzuki/linear
marks, common parameter, natural center, common Sylows and earlier source
commutator identities remain explicit. In particular the denominator is
still the restriction of the full G² to Q; full-kernel containment, Suzuki
selection, the binary layer and the rest of (12.6)--(12.9)/(13.1) remain
separate obligations of this same source family.

Source: DGS85, Groups and Graphs, (12.1), (12.3), (12.6),
printed pp.178--183.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Derive the q⁴ upper bound from the source geometry on the actual second kernel. -/
theorem source_suzuki_second_kernel_upper
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    {n : ℕ} (hn : 0 < n) (hq : Nat.card k = 2^(2*n+1))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      SL(2,k))
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) i))
    (T₀ : Sylow 2 (star L S (!i)))
    (hT₀ : (T₀ : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hnat : Noncommuting.HasNaturalCenter (star L S (!i))
      (Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i))))
    (hfull : V (reducedFamily L S) (base (reducedFamily L S) i) 1 =
      ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1, star L S i⁆) :
    let F := reducedFamily L S
    (ballKernel F (base F i) 2).relIndex (Q F (base F i)) ≤ (2^(2*n+1))^4 := by
  let F := reducedFamily L S
  let v := base F i
  let A := star L S i
  let D := Q F v
  let N := ballKernel F v 2
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite D := Finite.of_injective (inclusion (Q_le_stabilizer F v))
    (inclusion_injective _)
  have hplace : D ≤ star L S (!i) :=
    (le_sup_left.trans hT₀.ge).trans (map_subtype_le _)
  let : (N.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    ((Q_le_stabilizer F v).trans (stabilizer_le_normalizer_ballKernel F v 2))
  let := source_second_kernel_elementary h i hplace hnat hcomm
  have hDD : ⁅D,D⁆ ≤ N := by
    have hd : _root_.commutator D ≤ N.subgroupOf D :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N.subgroupOf D)).mp
        inferInstance
    have hm := map_mono (f := D.subtype) hd
    rw [map_subtype_commutator,subgroupOf_map_subtype] at hm
    exact hm.trans inf_le_left
  have hadj : (graph F).Adj v (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨g,hg,hgen⟩ := source_suzuki_span_pair_generation h i hb hc hxa hxm hadj hn eSuz eLin R hR
  have hV : V F x 1 ≤ A := (V_le_neighbor_Q F (reduced_triple h).generate
    (fun z => (source_Z_Q_U (reduced_triple h) z).1) (reduced_kernel_sylow h) hb hxm).trans
      ((le_sup_left.trans hR.ge).trans (map_subtype_le _))
  have hi := index_le_sq_of_two_conjugate_seeds A D (V F x 1) N
    (by change Q F v ≤ A; rw [←star_core h i]; exact pCoreIn_le 2 _) hV
    ((star_le_stabilizer i).trans (CommutingTrivial.stabilizer_normalizes_Q F v))
    ((star_le_stabilizer i).trans (stabilizer_le_normalizer_ballKernel F v 2)) hDD
    (source_second_kernel_fixed_preimage h i T₀ hT₀ R hR hnat hzy hcomm hfull)
    g hg (by rwa [←V_translate F])
    (source_suzuki_span_fixed_index h i hb hc hxa hxm hn hq eSuz eLin T hT R hR hzy hcomm)
  simpa only [←pow_mul,Nat.mul_assoc] using hi


/-- The literal nonbinary second-kernel section has order q⁴ and its original action is irreducible. -/
theorem source_suzuki_second_kernel_layer
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    {n : ℕ} (hn : 0 < n) (hq : Nat.card k = 2^(2*n+1))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      SL(2,k))
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) i))
    (T₀ : Sylow 2 (star L S (!i)))
    (hT₀ : (T₀ : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hnat : Noncommuting.HasNaturalCenter (star L S (!i))
      (Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i))))
    (hfull : V (reducedFamily L S) (base (reducedFamily L S) i) 1 =
      ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1, star L S i⁆) :
    let F := reducedFamily L S
    let v := base F i
    let hplace : Q F v ≤ ReducedLayer.star L S (!i) :=
      (le_sup_left.trans hT₀.ge).trans (map_subtype_le _)
    let : ((ballKernel F v 2).subgroupOf (Q F v)).Normal :=
      normal_subgroupOf_of_le_normalizer
        ((Q_le_stabilizer F v).trans (stabilizer_le_normalizer_ballKernel F v 2))
    let := source_second_kernel_elementary h i hplace hnat hcomm.le
    ∃ ρ : Representation (ZMod 2)
      (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0)))
      (Additive (Q F v ⧸ (ballKernel F v 2).subgroupOf (Q F v))),
      Function.Injective ρ ∧ ρ.IsIrreducible ∧
      Nat.card (Q F v ⧸ (ballKernel F v 2).subgroupOf (Q F v)) = (2 ^ (2 * n + 1)) ^ 4 ∧
      ∀ a : L (if i then 1 else 0), ∀ x : Q F v,
        (ρ (QuotientGroup.mk a) (Additive.ofMul (QuotientGroup.mk x))).toMul =
          QuotientGroup.mk ⟨(ReducedLayer.originalActor (L := L) (S := S) i a : G₀ L S) * x *
            (ReducedLayer.originalActor (L := L) (S := S) i a : G₀ L S)⁻¹,
            (mem_normalizer_iff.mp
              ((ReducedLayer.star_le_stabilizer i).trans
                (CommutingTrivial.stabilizer_normalizes_Q F v)
                  (ReducedLayer.originalActor (L := L) (S := S) i a).property) x).mp x.property⟩ := by
  let F := reducedFamily L S
  let v := base F i
  let D := Q F v
  let N := ballKernel F v 2
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite D := Finite.of_injective (inclusion (Q_le_stabilizer F v))
    (inclusion_injective _)
  have hplace : D ≤ star L S (!i) :=
    (le_sup_left.trans hT₀.ge).trans (map_subtype_le _)
  let : (N.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    ((Q_le_stabilizer F v).trans (stabilizer_le_normalizer_ballKernel F v 2))
  let := source_second_kernel_elementary h i hplace hnat hcomm.le
  obtain ⟨ρ,hf,_,hρ⟩ := source_suzuki_second_kernel_faithful h i hb eSuz T₀ hT₀ R hR
    hnat hzy hcomm hfull
  have hsmall : Nat.card (D ⧸ N.subgroupOf D) ≤ (2^(2*n+1))^4 :=
    source_suzuki_second_kernel_upper h i hb hc hxa hxm hn hq eSuz eLin T hT R hR
      hzy hcomm.le T₀ hT₀ hnat hfull
  obtain ⟨hirr,hcard⟩ := Representation.Suzuki.irreducible_of_faithful_small_card
    (ρ.comp eSuz.symm.toMonoidHom) (hf.comp eSuz.symm.injective) hsmall
  exact ⟨ρ,hf,(Representation.irreducible_comp_surjective_iff
    eSuz.symm.toMonoidHom eSuz.symm.surjective ρ).mp hirr,hcard,hρ⟩


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
