module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiFullThirdKernel
public import Theory.GroupTheory.Commutator.CentralizerQuotient
public import Theory.Representation.BinaryConjugationSection.EquivariantQuotient
/-!
# The natural action on the full-third-kernel centralizer quotient

Write H = G_m^(3) = V_x ∩ V_y. The subgroup
D = V_x (Q_m ∩ Q_y) has index q in Q_m and [D,H] lies in Z_y.
Conjugating D across the middle vertex gives the other displacement line
Z_x. These lines have trivial intersection: a common element centralizes
all three generating cores and hence the centerless starred parabolic.
The two commutator preimages therefore bound |Q_m/C_(Q_m)(H)| by q².

The identities [H,Q_m] = Z_m and [H,star_m] = Z_m make a nonzero
commutator row an equivariant map onto the minimal natural center Z_m.
The bound makes its kernel exactly C_(Q_m)(H). This constructs an
isomorphism with Z_m, preserving every star conjugation. Transport of the
existing natural-center coordinates proves the literal natural action,
with coefficient field of the original order q. The final consumer retains
the original endpoint actor and maps the centralizer into the actual
original parabolic two-core.

All earlier source hypotheses remain explicit. No naturality or index
assumption on the new quotient is added. The remaining centralizer/W
series, exhaustive Suzuki selection, binary alternatives and final
Chapter 12/13.1 premise discharge remain separate obligations.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.9), printed p.188(5), using (12.6)(c) and the preceding kernel identities.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- The full third-kernel centralizer quotient is equivariantly the natural center. -/
theorem source_suzuki_centralizer_quotient
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
    ∃ hN : ((centralizer (H : Set (G₀ L S))).subgroupOf (Q F m)).Normal,
      let := hN
      Nat.card (Q F m ⧸ (centralizer (H : Set (G₀ L S))).subgroupOf (Q F m)) = Nat.card k ^ 2 ∧
      ∃ E : (Q F m ⧸ (centralizer (H : Set (G₀ L S))).subgroupOf (Q F m)) ≃* Z F m,
        ∀ u : star L S i, ∀ q : Q F m,
          (E (QuotientGroup.mk ⟨(u : G₀ L S) * q * (u : G₀ L S)⁻¹,
            (mem_normalizer_iff.mp (CommutingTrivial.stabilizer_normalizes_Q F m
              (star_le_stabilizer i u.property)) q).mp q.property⟩) : G₀ L S) =
            (u : G₀ L S) * E (QuotientGroup.mk q) * (u : G₀ L S)⁻¹ := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let H := V F x 1 ⊓ V F y 1
  let A := star L S i
  let Qm := Q F m
  let Zm := Z F m
  let D := V F x 1 ⊔ (Qm ⊓ Q F y)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite Qm := Finite.of_injective (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  let : Finite Zm := Finite.of_injective (inclusion (Z_le_stabilizer F m)) (inclusion_injective _)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hXm : V F x 1 ≤ Qm := V_le_neighbor_Q F (reduced_triple h).generate hZ
    (reduced_kernel_sylow h) hb hxadj.symm
  have hQA : Qm ≤ A := (le_sup_right.trans hT.ge).trans (map_subtype_le _)
  have hAQ : A ≤ normalizer (Qm : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans (CommutingTrivial.stabilizer_normalizes_Q F m)
  have hZQ : Zm ≤ Qm := (hZ m).trans (map_subtype_le _)
  have hZC : Zm ≤ centralizer (Qm : Set (G₀ L S)) := Z_centralizes_Q F m (hZ m)
  have ht := source_suzuki_third_kernel_layer h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
  have hp := source_suzuki_product_and_intersection_commutator h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin
  have hi : D.relIndex Qm = Nat.card k := by
    have hh := (source_suzuki_middle_core_bounds (k := k) h (!i) hb hc hxa
      (by simpa only [Bool.not_not] using hxadj.symm) hn eSuz
      (by cases i <;> exact e) Ry (by simpa only [Bool.not_not] using hRy)).2.2.1
    simpa only [Bool.not_not,←hfield] using hh
  have hD : D ≤ Qm := sup_le hXm inf_le_left
  have hQC : Qm ≤ centralizer (Z F y : Set (G₀ L S)) := le_centralizer_iff.mp (hzy.trans hZC)
  have hDH : ⁅D,H⁆ ≤ Z F y := by
    apply commutator_sup_le_of_relative_normal Qm (V F x 1) (Qm ⊓ Q F y) H (Z F y)
      (hQC.trans (Subgroup.centralizer_le_normalizer _)) hXm inf_le_left
    · have hX : IsElementaryAbelian 2 (V F x 1) := V_elementary F
        (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x
      let := hX
      exact (commutator_mono le_rfl inf_le_left).trans
        ((commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer _)).le.trans bot_le)
    · rw [commutator_comm]
      exact (commutator_mono inf_le_right inf_le_right).trans hcommy.le
  obtain ⟨g,hg,hgy⟩ := star_locally_transitive h i hadj hxadj
  let f := (MulAut.conj g).toMonoidHom
  have hQf : Qm.map f = Qm := mem_normalizer_iff_map_conj_eq.mp (hAQ hg)
  have hHf : H.map f = H := mem_normalizer_iff_map_conj_eq.mp ((star_le_stabilizer i).trans ht.1 hg)
  have hZf : (Z F y).map f = Z F x := by rw [←Z_translate F,hgy]
  have hEH : ⁅D.map f,H⁆ ≤ Z F x := by
    have hh := map_mono (f := f) hDH
    rwa [map_commutator,hHf,hZf] at hh
  have hEQ : D.map f ≤ Qm := (map_mono hD).trans_eq hQf
  have hj : (D.map f).relIndex Qm = Nat.card k := by
    rw [←hQf,relIndex_map_map_of_injective D Qm (MulAut.conj g).injective,hi]
  have hdisj : Z F y ⊓ Z F x = ⊥ := by
    apply bot_unique
    intro z hz'
    have hzQ : z ∈ Qm := hZQ (hzy hz'.1)
    have hzA : z ∈ A := hQA hzQ
    have hzC : z ∈ centralizer (A : Set (G₀ L S)) := by
      have hgeneration := star_three_core_generation h i hxadj hne T R hT hR
      have hh : A ≤ centralizer ({z} : Set (G₀ L S)) := by
        change star L S i ≤ _
        rw [hgeneration]
        exact sup_le (sup_le
          (fun t ht => mem_centralizer_singleton_iff.mpr ((Z_centralizes_Q F y (hZ y) hz'.1) t ht))
          (fun t ht => mem_centralizer_singleton_iff.mpr ((Z_centralizes_Q F x (hZ x) hz'.2) t ht)))
          (fun t ht => mem_centralizer_singleton_iff.mpr (hZC (hzy hz'.1) t ht))
      exact fun t ht => mem_centralizer_singleton_iff.mp (hh ht)
    have hh : (⟨z,hzA⟩ : A) ∈ center A := mem_center_iff.mpr (fun a => Subtype.ext (hzC a a.property))
    have hh' := mem_bot.mp (hz ▸ hh)
    exact mem_bot.mpr (congrArg Subtype.val hh')
  have hbound : (centralizer (H : Set (G₀ L S))).relIndex Qm ≤ Nat.card Zm := by
    rw [show Nat.card Zm = Nat.card k ^ 2 from hcard,pow_two]
    exact centralizer_index_le_of_transverse_displacements Qm H (Z F y) (Z F x) D (D.map f)
      (hQC.trans (Subgroup.centralizer_le_normalizer _))
      ((le_centralizer_iff.mp (hzx.trans hZC)).trans (Subgroup.centralizer_le_normalizer _))
      hdisj hD hEQ hDH hEH hi.le hj.le
  have hminimal : ∀ N : Subgroup (G₀ L S), A ≤ normalizer (N : Set (G₀ L S)) →
      N ≤ Zm → N = ⊥ ∨ N = Zm := by
    intro N hnN hNZ
    let : (N.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hnN
    have hh := hmin (N.subgroupOf A) inferInstance (subgroupOf_mono A hNZ)
    rcases hh with hh | hh
    · left
      have hm := congrArg (Subgroup.map A.subtype) hh
      simpa only [map_subgroupOf_eq_of_le (hNZ.trans (hZQ.trans hQA)),Subgroup.map_bot] using hm
    · right
      change N.subgroupOf A = Zm.subgroupOf A at hh
      have hm := congrArg (Subgroup.map A.subtype) hh
      simpa only [map_subgroupOf_eq_of_le (hNZ.trans (hZQ.trans hQA)),
        map_subgroupOf_eq_of_le (hZQ.trans hQA)] using hm
  have hnonzero : ⁅H,Qm⁆ ≠ ⊥ := by
    rw [hp.2.1]
    intro he
    have hh := hcard
    rw [he,Nat.card_unique] at hh
    have hq : 1 < Nat.card k := Finite.one_lt_card
    nlinarith
  obtain ⟨hN,E,hE⟩ := exists_equivariant_centralizer_quotient A Qm H Zm hAQ
    hp.2.1.le ht.2.2.2.2.2.1.le hZQ hZC hminimal hnonzero hbound
  have hfull := (source_suzuki_full_linear_third_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch).1
  dsimp only
  rw [hfull]
  refine ⟨hN,(Nat.card_congr E.toEquiv).trans hcard,E,?_⟩
  intro u q
  exact hE u q

/-- DGS85 p.188(5), with actual natural coordinates and original completion maps. -/
theorem source_suzuki_centralizer_natural
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
    let C := Q F m ⊓ centralizer (H : Set (G₀ L S))
    C.map (G₀ L S).subtype = (parabolic L S (if i then 1 else 0)).pCoreIn 2 ⊓
      centralizer (H.map (G₀ L S).subtype : Set G) ∧
    ∃ (κ : Type u) (_ : Field κ) (_ : Finite κ) (_ : Algebra (ZMod 2) κ),
      ∃ π : star L S i →* Matrix.SpecialLinearGroup (Fin 2) κ,
        Function.Surjective π ∧ π.ker = (Q F m).subgroupOf (star L S i) ∧
        Nat.card κ = Nat.card k ∧
        ∃ d : Representation.BinaryConjugationSection (star L S i) (Q F m) C
          (Representation.SL2NaturalOffenders.NoStrong.natural.comp π),
          ∀ u : L (if i then 1 else 0), ∀ q : Q F m,
            (d.coordinates ⟨(originalActor (L := L) (S := S) i u : G₀ L S) * q *
              (originalActor (L := L) (S := S) i u : G₀ L S)⁻¹,
                (mem_normalizer_iff.mp (d.normalized
                  (originalActor (L := L) (S := S) i u).property) q).mp q.property⟩).toAdd =
              Matrix.mulVec (π (originalActor (L := L) (S := S) i u)).val (d.coordinates q).toAdd := by
  let F := reducedFamily L S
  let m := base F i
  let A := star L S i
  let Qm := Q F m
  let H := ballKernel F m 3
  let C := Qm ⊓ centralizer (H : Set (G₀ L S))
  have hQA : Qm ≤ A := (le_sup_right.trans hT.ge).trans (map_subtype_le _)
  have hAQ : A ≤ normalizer (Qm : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans (CommutingTrivial.stabilizer_normalizes_Q F m)
  obtain ⟨hN,horder,E,hE⟩ := source_suzuki_centralizer_quotient h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
  let := hN
  have hden : C.subgroupOf Qm = (centralizer (H : Set (G₀ L S))).subgroupOf Qm := by
    ext q
    exact and_iff_right q.property
  let : (C.subgroupOf Qm).Normal := hden.symm ▸ hN
  let E' : (Qm ⧸ C.subgroupOf Qm) ≃* Z F m :=
    (QuotientGroup.quotientMulEquivOfEq hden).trans E
  have hE' : ∀ a : A, ∀ q : Qm,
      (E' (QuotientGroup.mk ⟨(a : G₀ L S)*q*(a : G₀ L S)⁻¹,
        (mem_normalizer_iff.mp (hAQ a.property) q).mp q.property⟩) : G₀ L S) =
        (a : G₀ L S) * E' (QuotientGroup.mk q) * (a : G₀ L S)⁻¹ := hE
  obtain ⟨κ,_,_,_,π,hπ,hker,⟨d⟩⟩ := hnat
  have hω : Stellmacher.omegaOneCenterAmbient A = ⊥ := by
    apply bot_unique
    intro z hz'
    obtain ⟨hzA,_,hzc⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz'
    have hm : (⟨z,hzA⟩ : A) ∈ center A := mem_center_iff.mpr (fun a => Subtype.ext (hzc a a.property))
    rw [hz,mem_bot] at hm
    exact congrArg Subtype.val hm
  let d₀ : Representation.BinaryConjugationSection A (Z F m) ⊥
      (Representation.SL2NaturalOffenders.NoStrong.natural.comp π) := hω ▸ d
  have hk : Nat.card κ = Nat.card k := by
    have hh := d₀.card_section
    rw [hcard,Nat.card_fun,Nat.card_fin,
      (show Nat.card (⊥ : Subgroup (G₀ L S)) = 1 from Nat.card_unique),mul_one] at hh
    nlinarith
  let dQ := Representation.BinaryConjugationSection.of_equivariant_quotient
    A Qm C (Z F m) d₀ hQA inf_le_left hAQ E' hE'
  have hQmap : Qm.map (G₀ L S).subtype = (parabolic L S (if i then 1 else 0)).pCoreIn 2 := by
    change (Q (reducedFamily L S) (base (reducedFamily L S) i)).map _ = _
    rw [←star_core h i,←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 _ (G₀ L S).subtype_injective,map_subgroupOf_eq_of_le (star_le_completion _)]
    exact h.starredParabolic_same_core _
  refine ⟨?_,κ,inferInstance,inferInstance,inferInstance,π,hπ,hker,hk,dQ,?_⟩
  · change (Qm ⊓ centralizer (H : Set (G₀ L S))).map _ = _
    rw [←map_inf_centralizer_of_injective _ (G₀ L S).subtype_injective,hQmap]
  · intro u q
    exact dQ.equivariant (originalActor (L := L) (S := S) i u) q
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
