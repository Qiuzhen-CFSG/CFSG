module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.OverlapCubicAction
public import Theory.GroupTheory.SpecificGroups.DihedralFiveInnerAutomorphisms
public import Theory.SpecificGroups.ProjectiveLinear.OrderFiveConjugacy
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.NoncentralThreeOrderSix

/-!
# The literal second Baumeister parabolic

The characteristic dihedral factor of the actual overlap is acted on by
inner automorphisms: projective conjugation cannot square a five-rotation.
It splits off its centralizer locally. The latter has order six and the
literal cubic is noncentral there, giving the required symmetric factor.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

private theorem factor_data {H : Type*} [Group H]
    (L : Subgroup H) [L.Normal]
    (e : L ≃* Multiplicative (ZMod 3) × DihedralGroup 5) :
    ∃ (B : Subgroup H) (_eB : B ≃* DihedralGroup 5),
      B.Normal ∧ ∀ x : H, x ∈ B ↔ x ∈ L ∧ x ^ 10 = 1 := by
  let b : DihedralGroup 5 →* H := L.subtype.comp
    (e.symm.toMonoidHom.comp (MonoidHom.inr (Multiplicative (ZMod 3)) (DihedralGroup 5)))
  have hb : Function.Injective b := by
    intro x y hxy
    have hh := congrArg e (L.subtype_injective hxy)
    simpa only [MonoidHom.comp_apply, MonoidHom.inr_apply, MulEquiv.coe_toMonoidHom,
      e.apply_symm_apply] using congrArg Prod.snd hh
  let B := b.range
  let eB : B ≃* DihedralGroup 5 := (MonoidHom.ofInjective hb).symm
  have hmem (x : H) : x ∈ B ↔ x ∈ L ∧ x ^ 10 = 1 := by
    constructor
    · rintro ⟨d, rfl⟩
      refine ⟨(e.symm (1, d)).property, ?_⟩
      rw [← map_pow]
      have hd : d ^ 10 = 1 := by
        simpa only [DihedralGroup.nat_card] using pow_card_eq_one' (x := d)
      rw [hd, map_one]
    · rintro ⟨hx, hp⟩
      let y : L := ⟨x, hx⟩
      have hy : y ^ 10 = 1 := Subtype.ext hp
      have hc : (e y).1 = 1 := by
        have hh : (e y).1 ^ 10 = 1 := by
          have h := congrArg (fun z : L => (e z).1) hy
          simpa only [map_pow, map_one, Prod.pow_fst, Prod.fst_one] using h
        exact (show ∀ c : Multiplicative (ZMod 3), c ^ 10 = 1 → c = 1 by decide +kernel)
          _ hh
      refine ⟨(e y).2, ?_⟩
      have hh : (1, (e y).2) = e y := by ext <;> simp [hc]
      change (e.symm (1, (e y).2) : H) = x
      rw [hh, e.symm_apply_apply]
  have hnormal : B.Normal := by
    constructor
    intro x hx g
    obtain ⟨hxL, hx10⟩ := (hmem x).mp hx
    apply (hmem _).mpr
    refine ⟨Subgroup.Normal.conj_mem inferInstance x hxL g, ?_⟩
    rw [conj_pow, hx10, mul_one, mul_inv_cancel]
  exact ⟨B, eB, hnormal, hmem⟩

private theorem normal_action_no_square {H : Type*} [Group H]
    (B : Subgroup H) [B.Normal] (e : B ≃* DihedralGroup 5)
    (f : H →* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F)
    (hf : Function.Injective (f.comp B.subtype)) (g : H) :
    (e.symm.trans ((MulAut.conjNormal g).trans e)) (DihedralGroup.r 1) ≠
      (DihedralGroup.r 1) ^ 2 := by
  intro he
  let r : B := e.symm (DihedralGroup.r 1)
  have hr : orderOf (f r) = 5 := by
    rw [show f r = (f.comp B.subtype) r from rfl, orderOf_injective _ hf,
      ← e.orderOf_eq r]
    simp only [r, e.apply_symm_apply, DihedralGroup.orderOf_r_one]
  apply Matrix.ProjGenLinGroup.not_conjugate_square_of_order_five
    (by decide +kernel : (5 : Atlas.Comparisons.Exceptional.Nine.F) ≠ 0) (f r) (f g) hr
  have hh : MulAut.conjNormal g r = r ^ 2 := by
    apply e.injective
    simpa [r] using he
  have hraw : g * (r : H) * g⁻¹ = (r : H) ^ 2 := congrArg (fun x : B => (x : H)) hh
  have h := congrArg f hraw
  simpa only [map_mul, map_inv, map_pow] using h

private theorem factor_product {H : Type*} [Group H]
    (B : Subgroup H) [B.Normal] (eB : B ≃* DihedralGroup 5)
    (f : H →* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F)
    (hf : Function.Injective (f.comp B.subtype)) :
    ∃ e : centralizer (B : Set H) × DihedralGroup 5 ≃* H,
      ∀ c d, e (c, d) = (c : H) * (eB.symm d : H) := by
  let C := centralizer (B : Set H)
  have hs : C ⊔ B = ⊤ := by
    apply top_unique
    intro g _
    let a : MulAut (DihedralGroup 5) := eB.symm.trans ((MulAut.conjNormal g).trans eB)
    have ha := normal_action_no_square B eB f hf g
    have hai : a.symm (DihedralGroup.r 1) ≠ (DihedralGroup.r 1) ^ 2 := by
      have hh := normal_action_no_square B eB f hf g⁻¹
      exact hh
    obtain ⟨d, hd⟩ := DihedralGroup.five_aut_inner_of_no_square a ha hai
    let b := eB.symm d
    have he (x : B) : g * (x : H) * g⁻¹ = (b : H) * x * (b : H)⁻¹ := by
      change ((MulAut.conjNormal g x : B) : H) = ((b * x * b⁻¹ : B) : H)
      apply congrArg (fun z : B => (z : H))
      apply eB.injective
      have hh := DFunLike.congr_fun hd (eB x)
      simpa [a, b, MulAut.conj_apply] using hh
    have hc : (b : H)⁻¹ * g ∈ C := by
      apply mem_centralizer_iff.mpr
      intro x hx
      have hh := congrArg (fun z : H => (b : H)⁻¹ * z * g) (he ⟨x, hx⟩)
      simpa [mul_assoc] using hh.symm
    have hh := (C ⊔ B).mul_mem (mem_sup_right b.property) (mem_sup_left hc)
    simpa only [mul_inv_cancel_left] using hh
  have hd : Disjoint C B := by
    apply disjoint_def.mpr
    intro x hxC hxB
    have hz : eB ⟨x, hxB⟩ ∈ center (DihedralGroup 5) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨z, rfl⟩ := eB.surjective y
      have hh : z * (⟨x, hxB⟩ : B) = (⟨x, hxB⟩ : B) * z :=
        Subtype.ext (hxC z z.property)
      simpa only [map_mul] using congrArg eB hh
    rw [DihedralGroup.five_center_eq_bot, mem_bot] at hz
    exact congrArg (fun z : B => (z : H)) (eB.injective (hz.trans eB.map_one.symm))
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting C B hd le_rfl
  refine ⟨((MulEquiv.refl C).prodCongr eB.symm).trans
    (e.trans ((MulEquiv.subgroupCongr hs).trans topEquiv)), ?_⟩
  exact fun c d => he c (eB.symm d)

variable {G : Type*} [Group G] [Finite G]

set_option maxHeartbeats 800000 in
/-- The actual overlap normalizer is the second Baumeister parabolic. -/
theorem literal_overlap_pair_equiv
    {D : Seed G} (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane) (j : SingerField.Model →* G)
    (hj : PlaneTransport.FieldEmbedding A C a j) :
    Nonempty (normalizer (overlap j : Set G) ≃*
      (Equiv.Perm (Fin 3) × DihedralGroup 5)) := by
  obtain ⟨eQ, hq, hk, hkc, hkL, hD, hDc, hpre, hK, hmap, hambient, hcount⟩ :=
    literal_overlap_normalizer_descent P hc A C a j hj
  let N := normalizer (zpowers (j cubic) : Set G)
  let q := eQ.toMonoidHom.comp (QuotientGroup.mk' (cubicNormalizerKernel (j cubic)))
  let H := normalizer (overlap j : Set G)
  let L := (overlap j).subgroupOf H
  have hHN : H ≤ N := overlap_normalizer_le_cubic j hj.1
  let f := q.comp (inclusion hHN)
  let eL : L ≃* Multiplicative (ZMod 3) × DihedralGroup 5 :=
    (subgroupOfEquivOfLe (overlap j).le_normalizer).trans (overlapEquiv j hj.1)
  obtain ⟨B, eB, hBn, hmem⟩ := factor_data L eL
  let : B.Normal := hBn
  have hf : Function.Injective (f.comp B.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    let y : N := inclusion hHN (x : H)
    have hy : y ∈ q.ker := hx
    have hh := pow_card_eq_one' (x := (⟨y, hy⟩ : q.ker))
    rw [hkc] at hh
    have hy3 : y ^ 3 = 1 := congrArg Subtype.val hh
    have hx3 : (x : H) ^ 3 = 1 := Subtype.ext (congrArg (fun z : N => (z : G)) hy3)
    have hx10 : (x : H) ^ 10 = 1 := ((hmem (x : H)).mp x.property).2
    have hx9 : (x : H) ^ 9 = 1 := by
      rw [show 9 = 3 * 3 from rfl, pow_mul, hx3, one_pow]
    apply Subtype.ext
    change (x : H) = 1
    simpa only [show 10 = 9 + 1 from rfl, pow_succ, hx9, one_mul] using hx10
  obtain ⟨eP, heP⟩ := factor_product B eB f hf
  let Z := centralizer (B : Set H)
  have hHc : Nat.card H = 60 := literal_overlap_normalizer_card P hc A C a j hj
  have hZc : Nat.card Z = 6 := by
    have hh := Nat.card_congr eP.toEquiv
    rw [Nat.card_prod, DihedralGroup.nat_card, hHc] at hh
    change Nat.card Z * (2 * 5) = 60 at hh
    omega
  have hsL : j cubic ∈ overlap j := mem_map_of_mem j cubic_mem
  let sH : H := ⟨j cubic, (overlap j).le_normalizer hsL⟩
  have hcomm (x : H) (hx : x ∈ L) : Commute x sH := by
    apply Subtype.ext
    obtain ⟨y, hy, he⟩ := (show (x : G) ∈ overlap j from hx)
    have hh := ((cubic_commutes_complement ⟨y, hy⟩).map j).symm
    simpa only [he, Subgroup.coe_mul, sH] using hh.eq
  have hsZ : sH ∈ Z := by
    apply mem_centralizer_iff.mpr
    intro x hx
    exact (hcomm x ((hmem x).mp hx).1).eq
  let sZ : Z := ⟨sH, hsZ⟩
  have hs3 : orderOf sZ = 3 := by
    simpa only [sZ, sH, Subgroup.orderOf_mk] using
      (orderOf_injective j hj.1 cubic).trans cubic_order
  have hnoncentral : sZ ∉ center Z := by
    intro hscenter
    have hHC : H ≤ centralizer ({j cubic} : Set G) := by
      intro x hx
      obtain ⟨⟨c, d⟩, he⟩ := eP.surjective (⟨x, hx⟩ : H)
      have heval := heP c d
      rw [he] at heval
      have hccomm : Commute (c : H) sH := by
        exact congrArg (fun z : Z => (z : H)) ((mem_center_iff.mp hscenter) c)
      have hdcomm : Commute (eB.symm d : H) sH :=
        hcomm _ ((hmem _).mp (eB.symm d).property).1
      have hh := hccomm.mul_left hdcomm
      rw [← heval] at hh
      exact mem_centralizer_singleton_iff.mpr (congrArg (fun z : H => (z : G)) hh.eq)
    have hHL : H ≤ overlap j := by
      rw [← literal_overlap_cubic_centralizer_eq P hc A C a j hj]
      exact le_inf le_rfl hHC
    have hLc : Nat.card (overlap j) = 30 := by
      rw [Nat.card_congr (overlapEquiv j hj.1).toEquiv]
      norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        DihedralGroup.card, Sporadic.Janko3.SourceRecognition.Seventeen.Complement]
    have hh := card_le_of_le hHL
    rw [hHc, hLc] at hh
    omega
  obtain ⟨eZ⟩ := Theory.GroupTheory.nonempty_perm_three_of_card_six_noncentral_three
    hZc sZ hs3 hnoncentral
  exact ⟨eP.symm.trans (eZ.prodCongr (MulEquiv.refl (DihedralGroup 5)))⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
