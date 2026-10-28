module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalPairCore
public import Theory.GroupTheory.ConjugatePairSeed.OrthogonalAction
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Kernel
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.SingularInvolutionPairs
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.FixedSingularPlane
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.ElementaryStabilizerSign

/-!
# The orthogonal action of the source non-two pair

For the actual order-32 quaternion core of two conjugate natural layers, this
module constructs the action of their generated subgroup on the quotient by
the center. Its kernel is the core times the center of the generated pair.
Each layer contributes its literal order-two image; the fixed singular plane
recovers its normalizer hyperplane inside the quaternion quotient. Singular
displacement then identifies the generated image as S₃ under the source
non-two hypothesis. The central kernel is retained explicitly; this argument
does not infer that the ambient action is faithful.

Source: Aschbacher--Smith, 6.2.6(2), printed p.682; the fixed-plane
calculation is the orthogonal model of F.9.5(6).
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem half_card {A B : Subgroup G}
    (hle : A ≤ B) (hc : Nat.card B = 16) (hi : A.relIndex B = 2) :
    Nat.card A = 8 := by
  have hh := (A.subgroupOf B).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at hh
  change Nat.card A * A.relIndex B = Nat.card B at hh
  rw [hi, hc] at hh
  omega

omit [Finite G] in
private theorem pair_core_le_normalizers (B A : Subgroup G)
    [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 A] :
    localPairCore B A ≤ normalizer (B : Set G) ⊓ normalizer (A : Set G) := by
  exact sup_le
    (le_inf (inf_le_left.trans B.le_normalizer) inf_le_right)
    (le_inf inf_le_right (inf_le_left.trans A.le_normalizer))

omit [Finite G] in
private theorem pair_centralizer_eq (B A : Subgroup G)
    (hB : centralizer ((B ⊓ normalizer (A : Set G) : Subgroup G) : Set G) = centralizer (B : Set G))
    (hA : centralizer ((A ⊓ normalizer (B : Set G) : Subgroup G) : Set G) = centralizer (A : Set G)) :
    centralizer (localPairCore B A : Set G) = centralizer ((B ⊔ A : Subgroup G) : Set G) := by
  apply le_antisymm
  · apply le_centralizer_iff.mp
    apply sup_le
    · apply le_centralizer_iff.mpr
      exact (centralizer_le (show B ⊓ normalizer (A : Set G) ≤ localPairCore B A from le_sup_left)).trans_eq hB
    · apply le_centralizer_iff.mpr
      exact (centralizer_le (show A ⊓ normalizer (B : Set G) ≤ localPairCore B A from le_sup_right)).trans_eq hA
  · exact centralizer_le (show localPairCore B A ≤ B ⊔ A from
      sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right))

private theorem pair_outer_kernel (B A : Subgroup G)
    (hn : B ⊔ A ≤ normalizer (localPairCore B A : Set G))
    (d : QuaternionCentralProductData (localPairCore B A))
    (hc : centralizer (localPairCore B A : Set G) = centralizer ((B ⊔ A : Subgroup G) : Set G)) :
    ((seedOrthogonalAction (B ⊔ A) (localPairCore B A) hn d).ker).map (B ⊔ A).subtype =
      localPairCore B A ⊔ ((B ⊔ A) ⊓ centralizer ((B ⊔ A : Subgroup G) : Set G)) := by
  let J := B ⊔ A
  let Q := localPairCore B A
  let α := seedConjugation J Q hn
  let f := seedOrthogonalAction J Q hn d
  have hQJ : Q ≤ J := sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)
  apply le_antisymm
  · rintro x ⟨j, hj, rfl⟩
    have hi : α j ∈ (MulAut.conj : Q →* MulAut Q).range :=
      (d.quotientAut_eq_one_iff_inner _).mp ((d.quotientWreathAction_eq_one_iff _).mp hj)
    obtain ⟨q, hq⟩ := hi
    have hfix : q.val⁻¹ * j.val ∈ centralizer (Q : Set G) := by
      intro u hu
      have he := congrArg (fun a : MulAut Q => (a ⟨u, hu⟩ : G)) hq
      change q.val * u * q.val⁻¹ = j.val * u * j.val⁻¹ at he
      have ht : (q.val⁻¹ * j.val) * u * (q.val⁻¹ * j.val)⁻¹ = u := by
        calc
          _ = q.val⁻¹ * (j.val * u * j.val⁻¹) * q.val := by group
          _ = q.val⁻¹ * (q.val * u * q.val⁻¹) * q.val := by rw [← he]
          _ = u := by group
      exact (mul_inv_eq_iff_eq_mul.mp ht).symm
    have hcentral : q.val⁻¹ * j.val ∈ J ⊓ centralizer (J : Set G) :=
      ⟨J.mul_mem (J.inv_mem (hQJ q.property)) j.property, hc ▸ hfix⟩
    have hm := (Q ⊔ (J ⊓ centralizer (J : Set G))).mul_mem
      (mem_sup_left q.property) (mem_sup_right hcentral)
    change (j : G) ∈ Q ⊔ (J ⊓ centralizer (J : Set G))
    simpa only [mul_inv_cancel_left] using hm
  · apply sup_le
    · intro q hq
      refine ⟨⟨q, hQJ hq⟩, ?_, rfl⟩
      apply (d.quotientWreathAction_eq_one_iff _).mpr
      apply (d.quotientAut_eq_one_iff_inner _).mpr
      exact ⟨⟨q, hq⟩, by ext x; rfl⟩
    · intro c hc'
      refine ⟨⟨c, hc'.1⟩, ?_, rfl⟩
      have he : α ⟨c, hc'.1⟩ = 1 := by
        apply MulEquiv.ext
        intro q
        apply Subtype.ext
        change c * q.val * c⁻¹ = q.val
        rw [← hc'.2 q (hQJ q.property), mul_inv_cancel_right]
      change d.quotientWreathAction (α ⟨c, hc'.1⟩) = 1
      rw [he, map_one]

omit [Finite G] in
private theorem pair_outer_image {J Q X Y : Subgroup G}
    (f : J →* BinaryFourPlus.Wreath) (hXJ : X ≤ J)
    (hQK : Q ≤ f.ker.map J.subtype)
    (hKN : f.ker.map J.subtype ≤ normalizer (Y : Set G))
    (hUQ : X ⊓ normalizer (Y : Set G) ≤ Q)
    (hi : (X ⊓ normalizer (Y : Set G)).relIndex X = 2) :
    Nat.card ((X.subgroupOf J).map f) = 2 := by
  let K := f.ker.map J.subtype
  have he : X ⊓ K = X ⊓ normalizer (Y : Set G) :=
    le_antisymm (inf_le_inf_left _ hKN) (le_inf inf_le_left (hUQ.trans hQK))
  rw [← relIndex_ker]
  have hmap := relIndex_map_map_of_injective
    (f := J.subtype) f.ker (X.subgroupOf J) J.subtype_injective
  rw [map_subgroupOf_eq_of_le hXJ] at hmap
  rw [← hmap]
  change K.relIndex X = 2
  rw [← inf_relIndex_right, inf_comm K X, he]
  exact hi

private theorem pair_actor_singular (J Q X : Subgroup G)
    [IsElementaryAbelian 2 X]
    (hn : J ≤ normalizer (Q : Set G))
    (d : QuaternionCentralProductData Q) (hnX : Q ≤ normalizer (X : Set G))
    (x : J) (hx : (x : G) ∈ X) :
    BinaryFourPlus.SingularDisplacements (seedOrthogonalAction J Q hn d x) := by
  apply d.wreath_singular_displacement
  intro q
  apply Subtype.ext
  change (⁅(x : G), (q : G)⁆) ^ 2 = 1
  apply elemPow_eq_one_of_isElementaryAbelian (A := X)
  exact (le_normalizer_iff_commutator_le_left.mp hnX)
      (commutator_mem_commutator hx q.property)

private theorem fixed_elementary_eight
    {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)
    (E : Subgroup Q) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (hz : center Q ≤ E)
    (a : MulAut Q) (ha : d.quotientWreathAction a ≠ 1)
    (hfix : ∀ x ∈ E, a x = x) :
    (d.quotientWreathAction a).right ≠ 1 ∧
      ∀ x : Q, quotientAut (center Q) a (QuotientGroup.mk' (center Q) x) =
        QuotientGroup.mk' (center Q) x ↔ x ∈ E := by
  let π := QuotientGroup.mk' (center Q)
  let H := E.map π
  have hindex : H.index = E.index := E.index_map_eq
    (QuotientGroup.mk'_surjective (center Q)) (by rw [QuotientGroup.ker_mk']; exact hz)
  have hEindex : E.index = 4 := by
    have hh := E.card_mul_index
    rw [hE, d.card] at hh
    omega
  have hHcard : Nat.card H = 4 := by
    have hh := H.card_mul_index
    rw [hindex, hEindex, d.quotient_card] at hh
    omega
  let W : Submodule (ZMod 2) d.SquareSpace := {
    carrier := {v | v.toMul ∈ H}
    zero_mem' := H.one_mem
    add_mem' := fun hx hy => H.mul_mem hx hy
    smul_mem' := by
      intro r v hv
      have hb : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
      rcases hb r with rfl | rfl
      · rw [zero_smul]; exact H.one_mem
      · simpa only [one_smul] using hv }
  have hcW : Nat.card W = 4 := by
    let e : W ≃ H := {
      toFun := fun v => ⟨v.val.toMul, v.property⟩
      invFun := fun v => ⟨Additive.ofMul v.val, v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Nat.card_congr e).trans hHcard
  have hdW : Module.finrank (ZMod 2) W = 2 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [hcW, Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc.symm
  have hsW : ∀ v ∈ W, d.quadraticForm v = 0 := by
    intro v hv
    obtain ⟨x, hx, he⟩ := hv
    have hs : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hx
    have hev : v = Additive.ofMul (π x) := congrArg Additive.ofMul he.symm
    rw [hev, d.quadraticForm_apply, d.binarySquare_mk]
    have hsq : (⟨x ^ 2, d.square_mem_center x⟩ : center Q) = 1 := Subtype.ext hs
    rw [hsq, map_one]
    rfl
  let S := W.map d.squareCoordinates.toLinearMap
  have hdS : Module.finrank (ZMod 2) S = 2 := by
    rw [LinearEquiv.finrank_map_eq]
    exact hdW
  have hsS : ∀ v ∈ S, BinaryFourPlus.q v = 0 := by
    rintro v ⟨w, hw, rfl⟩
    have he := d.squareFormIsometry.map_app' w
    change BinaryFourPlus.q (d.squareFormIsometry w) = d.quadraticForm w at he
    rw [d.squareFormIsometry_apply] at he
    exact he.trans (hsW w hw)
  have hiS : ∀ v ∈ S,
      (BinaryFourPlus.wreathToIsometry (d.quotientWreathAction a)).val v = v := by
    rintro v ⟨w, hw, rfl⟩
    change (BinaryFourPlus.wreathToIsometry (d.quotientWreathAction a)).val
      (d.squareCoordinates w) = d.squareCoordinates w
    obtain ⟨x, hx, he⟩ := hw
    have hwe : w = Additive.ofMul (π x) := congrArg Additive.ofMul he.symm
    rw [hwe, ← d.squareCoordinates_quotientAut, quotientAut_apply_mk, hfix x hx]
  obtain ⟨hswap, hfixed⟩ := BinaryFourPlus.fixed_singular_plane
    (d.quotientWreathAction a) ha S (by rw [hdS]) hsS hiS
  refine ⟨hswap, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · have hm := hfixed (d.squareCoordinates (Additive.ofMul (π x))) (by
      rw [← d.squareCoordinates_quotientAut, hx])
    obtain ⟨w, hw, he⟩ := hm
    have he' : w = Additive.ofMul (π x) := d.squareCoordinates.injective he
    have hxH : π x ∈ H := he' ▸ hw
    have hh : H.comap π = E := E.comap_map_eq_self
      (by rw [QuotientGroup.ker_mk']; exact hz)
    exact hh ▸ hxH
  · rw [quotientAut_apply_mk, hfix x hx]

private theorem two_generated_outer_image_not_two
    {F : Type*} [Group F] (Q B A : Subgroup G) (f : G →* F)
    (hker : f.ker = Q ⊔ center G) (hQ : IsPGroup 2 Q)
    (hB : IsPGroup 2 B) (hA : IsPGroup 2 A) (hgen : B ⊔ A = ⊤)
    (hnon : ¬ IsPGroup 2 G) : ¬ IsPGroup 2 f.range := by
  intro hp
  have hZ : center G ≤ f.ker := hker.symm ▸ le_sup_right
  let f' := QuotientGroup.lift (center G) f hZ
  have hk : IsPGroup 2 f'.ker := by
    have he : f'.ker = Q.map (QuotientGroup.mk' (center G)) := by
      rw [QuotientGroup.ker_lift, hker, Subgroup.map_sup,
        QuotientGroup.map_mk'_self, sup_bot_eq]
    rw [he]
    exact hQ.map _
  have hr : f'.range = f.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center G) x
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨QuotientGroup.mk' (center G) g, rfl⟩
  have hquot : IsPGroup 2 (G ⧸ center G) := by
    have hh := (hr ▸ hp).comap_of_ker_isPGroup f' hk
    rw [MonoidHom.comap_range_self] at hh
    exact hh.of_equiv topEquiv
  let : Group.IsNilpotent (G ⧸ center G) := hquot.isNilpotent
  let : Group.IsNilpotent G := Group.of_quotient_center_nilpotent inferInstance
  let S : Sylow 2 G := Classical.choice inferInstance
  have hBS : B ≤ S := by
    have he := S.is_maximal' (S.isPGroup'.to_sup_of_normal_left hB) le_sup_left
    exact le_sup_right.trans_eq he
  have hAS : A ≤ S := by
    have he := S.is_maximal' (S.isPGroup'.to_sup_of_normal_left hA) le_sup_left
    exact le_sup_right.trans_eq he
  have he : (S : Subgroup G) = ⊤ := top_unique (hgen ▸ sup_le hBS hAS)
  exact hnon ((he ▸ S.isPGroup').of_equiv topEquiv)

variable {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- Hyperplane rigidity identifies the centralizer of the source pair core
with the centralizer of the whole generated pair. -/
theorem local_pair_core_centralizer
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (g : G)
    (hleft : (layer L R ⊓ normalizer
      ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)).relIndex (layer L R) = 2)
    (hright : ((layer L R).map (MulAut.conj g).toMonoidHom ⊓
      normalizer (layer L R : Set G)).relIndex
        ((layer L R).map (MulAut.conj g).toMonoidHom) = 2) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    centralizer (localPairCore B A : Set G) = centralizer ((B ⊔ A : Subgroup G) : Set G) := by
  apply pair_centralizer_eq
  · exact local_large_subgroup_centralizer h hnatural hE inf_le_left (by
      rw [half_card inf_le_left hnatural.2.1.card hleft])
  · exact local_conjugate_large_subgroup_centralizer h hnatural hE g inf_le_left (by
      rw [half_card inf_le_left
        ((card_map_of_injective (MulAut.conj g).injective).trans hnatural.2.1.card) hright])

/-- The two actual layer images are involutions with singular displacement.
The action kernel includes the quaternion core and is exactly its product
with the center of the generated pair; faithfulness is not assumed. -/
theorem local_non_two_pair_outer_action
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (g : G)
    (hleft : (layer L R ⊓ normalizer
      ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)).relIndex (layer L R) = 2)
    (hright : ((layer L R).map (MulAut.conj g).toMonoidHom ⊓
      normalizer (layer L R : Set G)).relIndex
        ((layer L R).map (MulAut.conj g).toMonoidHom) = 2)
    (hnon : ¬ IsPGroup 2 (layer L R ⊔
      (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    let J := B ⊔ A
    let Q := localPairCore B A
    ∃ (hn : J ≤ normalizer (Q : Set G)) (d : QuaternionCentralProductData Q),
      let f := seedOrthogonalAction J Q hn d
      f.ker.map J.subtype = Q ⊔ (J ⊓ centralizer (J : Set G)) ∧
      Nat.card ((B.subgroupOf J).map f) = 2 ∧
      Nat.card ((A.subgroupOf J).map f) = 2 ∧
      (∀ x : J, (x : G) ∈ B ∨ (x : G) ∈ A →
        (f x)^2 = 1 ∧ BinaryFourPlus.SingularDisplacements (f x)) ∧
      (∀ x : J, (x : G) ∈ B → f x ≠ 1 →
        (f x).right ≠ 1 ∧ ∀ q : Q,
          quotientAut (center Q) (seedConjugation J Q hn x)
              (QuotientGroup.mk' (center Q) q) = QuotientGroup.mk' (center Q) q ↔
            (q : G) ∈ B ⊓ normalizer (A : Set G)) ∧
      (∀ x : J, (x : G) ∈ A → f x ≠ 1 →
        (f x).right ≠ 1 ∧ ∀ q : Q,
          quotientAut (center Q) (seedConjugation J Q hn x)
              (QuotientGroup.mk' (center Q) q) = QuotientGroup.mk' (center Q) q ↔
            (q : G) ∈ A ⊓ normalizer (B : Set G)) := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let J := B ⊔ A
  let Q := localPairCore B A
  let := h.layer_elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  obtain ⟨hI, hcomm, hQ, hn, hZ, ⟨d⟩⟩ :=
    local_non_two_pair_quaternion_core h hnatural hE g hleft hright hnon
  let f := seedOrthogonalAction J Q hn d
  have hc : centralizer (Q : Set G) = centralizer (J : Set G) :=
    local_pair_core_centralizer h hnatural hE g hleft hright
  have hK : f.ker.map J.subtype = Q ⊔ (J ⊓ centralizer (J : Set G)) :=
    pair_outer_kernel B A hn d hc
  have hQK : Q ≤ f.ker.map J.subtype := hK.symm ▸ le_sup_left
  have hKN : f.ker.map J.subtype ≤ normalizer (B : Set G) ⊓ normalizer (A : Set G) := by
    rw [hK]
    refine sup_le (pair_core_le_normalizers B A) (le_inf ?_ ?_)
    · exact (inf_le_right.trans (centralizer_le (show B ≤ J from le_sup_left))).trans
        (Subgroup.centralizer_le_normalizer _)
    · exact (inf_le_right.trans (centralizer_le (show A ≤ J from le_sup_right))).trans
        (Subgroup.centralizer_le_normalizer _)
  refine ⟨hn, d, hK,
    pair_outer_image f le_sup_left hQK (hKN.trans inf_le_right) le_sup_left hleft,
    pair_outer_image f le_sup_right hQK (hKN.trans inf_le_left) le_sup_right hright, ?_, ?_, ?_⟩
  · intro x hx
    have hx2 : x^2=1 := Subtype.ext (hx.elim
      (fun hb => elemPow_eq_one_of_isElementaryAbelian (A := B) (x : G) hb)
      (fun ha => elemPow_eq_one_of_isElementaryAbelian (A := A) (x : G) ha))
    refine ⟨by rw [← map_pow, hx2, map_one], ?_⟩
    rcases hx with hx | hx
    · exact pair_actor_singular J Q B hn d ((pair_core_le_normalizers B A).trans inf_le_left) x hx
    · exact pair_actor_singular J Q A hn d ((pair_core_le_normalizers B A).trans inf_le_right) x hx
  · intro x hx hxne
    let E := (B ⊓ normalizer (A : Set G)).subgroupOf Q
    have hEQ : B ⊓ normalizer (A : Set G) ≤ Q := le_sup_left
    let : IsElementaryAbelian 2 (B ⊓ normalizer (A : Set G) : Subgroup G) :=
      IsElementaryAbelian.of_le (show B ⊓ normalizer (A : Set G) ≤ B from inf_le_left)
    let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hEQ
    have hEc : Nat.card E = 8 := (Nat.card_congr (subgroupOfEquivOfLe hEQ).toEquiv).trans
      (half_card inf_le_left hnatural.2.1.card hleft)
    have hZE : center Q ≤ E := by
      intro q hq
      have hi : (q : G) ∈ B ⊓ A := hZ ▸ mem_map_of_mem Q.subtype hq
      exact ⟨hi.1, A.le_normalizer hi.2⟩
    exact fixed_elementary_eight d E hEc hZE (seedConjugation J Q hn x) hxne
      (fun q hq => Subtype.ext (by
        change (x : G) * (q : G) * (x : G)⁻¹ = (q : G)
        rw [← (B.le_centralizer hx) q hq.1, mul_inv_cancel_right]))
  · intro x hx hxne
    let E := (A ⊓ normalizer (B : Set G)).subgroupOf Q
    have hEQ : A ⊓ normalizer (B : Set G) ≤ Q := le_sup_right
    let : IsElementaryAbelian 2 (A ⊓ normalizer (B : Set G) : Subgroup G) :=
      IsElementaryAbelian.of_le (show A ⊓ normalizer (B : Set G) ≤ A from inf_le_left)
    let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hEQ
    have hAc : Nat.card A = 16 := (card_map_of_injective (MulAut.conj g).injective).trans hnatural.2.1.card
    have hEc : Nat.card E = 8 := (Nat.card_congr (subgroupOfEquivOfLe hEQ).toEquiv).trans
      (half_card inf_le_left hAc hright)
    have hZE : center Q ≤ E := by
      intro q hq
      have hi : (q : G) ∈ B ⊓ A := hZ ▸ mem_map_of_mem Q.subtype hq
      exact ⟨hi.2, B.le_normalizer hi.1⟩
    exact fixed_elementary_eight d E hEc hZE (seedConjugation J Q hn x) hxne
      (fun q hq => Subtype.ext (by
        change (x : G) * (q : G) * (x : G)⁻¹ = (q : G)
        rw [← (A.le_centralizer hx) q hq.1, mul_inv_cancel_right]))

/-- The actual quotient action of the non-two pair is symmetric three.
This identifies the image, retaining the possible central kernel explicitly. -/
theorem local_non_two_pair_outer_symmetricThree
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (g : G)
    (hleft : (layer L R ⊓ normalizer
      ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)).relIndex (layer L R) = 2)
    (hright : ((layer L R).map (MulAut.conj g).toMonoidHom ⊓
      normalizer (layer L R : Set G)).relIndex
        ((layer L R).map (MulAut.conj g).toMonoidHom) = 2)
    (hnon : ¬ IsPGroup 2 (layer L R ⊔
      (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    let J := B ⊔ A
    let Q := localPairCore B A
    ∃ (hn : J ≤ normalizer (Q : Set G)) (d : QuaternionCentralProductData Q),
      let f := seedOrthogonalAction J Q hn d
      f.ker.map J.subtype = Q ⊔ (J ⊓ centralizer (J : Set G)) ∧
      Nonempty (f.range ≃* Equiv.Perm (Fin 3)) := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let J := B ⊔ A
  let Q := localPairCore B A
  let := h.layer_elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  obtain ⟨hn, d, hK, hB, hA, hsing, hfixB, hfixA⟩ :=
    local_non_two_pair_outer_action h hnatural hE g hleft hright hnon
  let f := seedOrthogonalAction J Q hn d
  let BJ := B.subgroupOf J
  let AJ := A.subgroupOf J
  have hBJ : B ≤ J := le_sup_left
  have hAJ : A ≤ J := le_sup_right
  have hQJ : Q ≤ J := sup_le (inf_le_left.trans hBJ) (inf_le_left.trans hAJ)
  have hgen : BJ ⊔ AJ = ⊤ := by rw [← subgroupOf_sup hBJ hAJ, subgroupOf_self]
  have hker : f.ker = Q.subgroupOf J ⊔ center J := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hQJ,
      map_center_subtype_eq_inf_centralizer]
    exact hK
  have hpQ : IsPGroup 2 (Q.subgroupOf J) :=
    (IsPGroup.of_card (n := 5) d.card).comap_subtype
  have hnot : ¬ IsPGroup 2 f.range := two_generated_outer_image_not_two
    (Q.subgroupOf J) BJ AJ f hker hpQ
    (IsElementaryAbelian.isPGroup 2 B).comap_subtype
    (IsElementaryAbelian.isPGroup 2 A).comap_subtype hgen hnon
  obtain ⟨b, hb1, hball⟩ := (Nat.card_eq_two_iff' (1 : BJ.map f)).mp hB
  obtain ⟨a, ha1, haall⟩ := (Nat.card_eq_two_iff' (1 : AJ.map f)).mp hA
  obtain ⟨v, hv, hvb⟩ := b.property
  obtain ⟨w, hw, hwa⟩ := a.property
  have hBi : BJ.map f = zpowers (f v) := by
    apply le_antisymm
    · intro y hy
      by_cases he : y = 1
      · exact he ▸ (zpowers (f v)).one_mem
      · have he' := congrArg Subtype.val (hball ⟨y, hy⟩ (by
          intro hy1
          exact he (congrArg Subtype.val hy1)))
        have he'' : y = (b : BinaryFourPlus.Wreath) := he'
        rw [he'', ← hvb]
        exact mem_zpowers (f v)
    · exact zpowers_le.mpr (mem_map_of_mem f hv)
  have hAi : AJ.map f = zpowers (f w) := by
    apply le_antisymm
    · intro y hy
      by_cases he : y = 1
      · exact he ▸ (zpowers (f w)).one_mem
      · have he' := congrArg Subtype.val (haall ⟨y, hy⟩ (by
          intro hy1
          exact he (congrArg Subtype.val hy1)))
        have he'' : y = (a : BinaryFourPlus.Wreath) := he'
        rw [he'', ← hwa]
        exact mem_zpowers (f w)
    · exact zpowers_le.mpr (mem_map_of_mem f hw)
  have hr : f.range = zpowers (f v) ⊔ zpowers (f w) := by
    rw [← hBi, ← hAi, ← Subgroup.map_sup, hgen, ← MonoidHom.range_eq_map]
  refine ⟨hn, d, hK, ?_⟩
  rw [hr]
  exact BinaryFourPlus.symmetricThree_of_singular_involutions (f v) (f w)
    (hsing v (Or.inl hv)).1 (hsing w (Or.inr hw)).1
    (hsing v (Or.inl hv)).2 (hsing w (Or.inr hw)).2 (hr ▸ hnot)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
