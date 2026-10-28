module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.Source
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Intersection

/-!
# The lower intersection bound for the two source56 partners

Inside the natural four-space, membership in U, Uʸ, and Uʸᵗ forces
orthogonality to Z, Zʸ, and Zʸᵗ. The selected two orbit planes span
Z-perpendicular, so the intersection lies in its double perpendicular Z.
A small kernel-checked determinant calculation proves this last implication;
the source54 quadratic marking transports invariance through the original
ambient action. Together with the independent upper bound E ∩ Eᵗ ≤ V,
this proves the literal E ∩ Eᵗ = Z used by the source56 consumer.

Source: Aschbacher–Smith, proof of 15.3.56(5), printed p.1148.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open ClassicalOrthogonal.FourPlusMatrix
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open OrthogonalGeometry.Source50Model
attribute [local instance] FourGroupMatrixCoordinates.naturalAction orthogonalAction
variable {G : Type*} [Group G] {M V Z U W : Subgroup G}

private def polarPair (c : V ≃* Multiplicative (Mat (F := ZMod 2))) (v w : V) : ZMod 2 :=
  determinantForm.polarBilin (c v).toAdd (c w).toAdd

private def polarKernel (c : V ≃* Multiplicative (Mat (F := ZMod 2))) (v : V) : Subgroup V where
  carrier w := polarPair c v w = 0
  one_mem' := by
    change polarPair c v 1 = 0
    simp [polarPair]
  mul_mem' := by
    intro a b ha hb
    change polarPair c v (a*b) = 0
    change polarPair c v a = 0 at ha
    change polarPair c v b = 0 at hb
    dsimp only [polarPair] at *
    rw [map_mul]
    change determinantForm.polarBilin (c v).toAdd ((c a).toAdd + (c b).toAdd) = 0
    rw [map_add, ha, hb, add_zero]
  inv_mem' := by
    intro a ha
    change polarPair c v a⁻¹ = 0
    change polarPair c v a = 0 at ha
    dsimp only [polarPair] at *
    rw [map_inv]
    change determinantForm.polarBilin (c v).toAdd (-(c a).toAdd) = 0
    rw [map_neg, ha, neg_zero]

private def ambientAction (d : NaturalOrthogonalAction M V) : M →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion d.normalizes)

private theorem pair_invariant (d : NaturalOrthogonalAction M V)
    (c : V ≃* Multiplicative (Mat (F := ZMod 2)))
    (hq : ∀ v : V, determinantForm (c v).toAdd =
      FusionCore.orthogonalCoordinateValue (d.coordinates v))
    (m : M) (v w : V) :
    polarPair c (ambientAction d m v) (ambientAction d m w) = polarPair c v w := by
  have hi (x : V) : determinantForm (c (ambientAction d m x)).toAdd =
      determinantForm (c x).toAdd := by
    rw [hq, hq]
    change FusionCore.orthogonalCoordinateValue
      (d.coordinates (V.normalizerMonoidHom ⟨m, d.normalizes m.property⟩ x)) = _
    rw [d.compatible, quadratic_invariant]
  simp only [polarPair, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  change determinantForm (c (ambientAction d m v) * c (ambientAction d m w)).toAdd -
    determinantForm (c (ambientAction d m v)).toAdd -
    determinantForm (c (ambientAction d m w)).toAdd =
      determinantForm (c v * c w).toAdd - determinantForm (c v).toAdd -
        determinantForm (c w).toAdd
  rw [← map_mul, ← map_mul, hi, hi, hi, map_mul]

set_option maxRecDepth 10000 in
private theorem matrix_double_perp (z x : Mat (F := ZMod 2))
    (h : ∀ w : Mat (F := ZMod 2), determinantForm.polarBilin w z = 0 →
      determinantForm.polarBilin x w = 0) : x = 0 ∨ x = z := by
  exact (show ∀ z x : Mat (F := ZMod 2),
    (∀ w : Mat (F := ZMod 2), determinantForm.polarBilin w z = 0 →
      determinantForm.polarBilin x w = 0) → x = 0 ∨ x = z by decide +kernel) z x h

private theorem conjugate_point_le_kernel (d : NaturalOrthogonalAction M V)
    (c : V ≃* Multiplicative (Mat (F := ZMod 2)))
    (hq : ∀ v : V, determinantForm (c v).toAdd =
      FusionCore.orthogonalCoordinateValue (d.coordinates v))
    (hZV : Z ≤ V)
    (hperp : ∀ v : V, (v : G) ∈ U ↔ ∀ z : Z,
      polarPair c v (inclusion hZV z) = 0)
    (m : M) (v : V) (hv : (v : G) ∈ rightConjugate U m) :
    rightConjugate Z m ≤ (polarKernel c v).map V.subtype := by
  have hvm : (ambientAction d m v : G) ∈ U := by
    obtain ⟨u, hu, he⟩ := hv
    change (m : G)⁻¹ * u * ((m : G)⁻¹)⁻¹ = (v : G) at he
    change (m : G) * (v : G) * (m : G)⁻¹ ∈ U
    have hh : (m : G) * (v : G) * (m : G)⁻¹ = u := by rw [← he]; group
    exact hh.symm ▸ hu
  rintro _ ⟨z, hz, rfl⟩
  let zv : V := inclusion hZV ⟨z, hz⟩
  let zg : V := ambientAction d m⁻¹ zv
  refine ⟨zg, ?_, rfl⟩
  change polarPair c v zg = 0
  have hi := pair_invariant d c hq m v zg
  have he : ambientAction d m zg = zv := by
    change ambientAction d m (ambientAction d m⁻¹ zv) = zv
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  rw [he] at hi
  exact hi.symm.trans ((hperp _).mp hvm ⟨z,hz⟩)

private theorem double_perp_point
    (c : V ≃* Multiplicative (Mat (F := ZMod 2)))
    (hZV : Z ≤ V) (hZcard : Nat.card Z = 2)
    (hperp : ∀ v : V, (v : G) ∈ U ↔ ∀ z : Z,
      polarPair c v (inclusion hZV z) = 0)
    (x : V) (hx : V ⊓ U ≤ (polarKernel c x).map V.subtype) : (x : G) ∈ Z := by
  obtain ⟨z, hz, hall⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZcard
  let zv : V := inclusion hZV z
  have hi : ∀ w : Mat (F := ZMod 2), determinantForm.polarBilin w (c zv).toAdd = 0 →
      determinantForm.polarBilin (c x).toAdd w = 0 := by
    intro w hw
    let v : V := c.symm (Multiplicative.ofAdd w)
    have hv : (v : G) ∈ U := by
      apply (hperp v).mpr
      intro a
      by_cases ha : a = 1
      · subst a
        simp [polarPair]
      · have he : a = z := hall a ha
        rw [he]
        change determinantForm.polarBilin (c (c.symm (Multiplicative.ofAdd w))).toAdd
          (c zv).toAdd = 0
        rw [c.apply_symm_apply]
        exact hw
    have hh := hx ⟨v.property, hv⟩
    have hvk : v ∈ polarKernel c x := (mem_map_iff_mem V.subtype_injective).mp hh
    change polarPair c x v = 0 at hvk
    simpa only [polarPair, v, c.apply_symm_apply, toAdd_ofAdd] using hvk
  rcases matrix_double_perp (c zv).toAdd (c x).toAdd hi with he | he
  · have hx1 : x = 1 := c.injective (Multiplicative.toAdd.injective (by simpa using he))
    simpa only [hx1, coe_one] using Z.one_mem
  · have hxz : x = zv := c.injective (Multiplicative.toAdd.injective he)
    exact hxz ▸ z.property

/-- Triple-conjugate containment from the three marked points spanning their
perpendicular hyperplane, in the literal right-conjugation convention. -/
theorem triple_intersection_le_point (d : NaturalOrthogonalAction M V)
    (c : V ≃* Multiplicative (Mat (F := ZMod 2)))
    (hq : ∀ v : V, determinantForm (c v).toAdd =
      FusionCore.orthogonalCoordinateValue (d.coordinates v))
    (hZV : Z ≤ V) (hZcard : Nat.card Z = 2)
    (hperp : ∀ v : V, (v : G) ∈ U ↔ ∀ z : Z,
      determinantForm.polarBilin (c v).toAdd (c (inclusion hZV z)).toAdd = 0)
    (y t : M)
    (hspan : Z ⊔ rightConjugate Z y ⊔ rightConjugate Z ((y : G)*(t : G)) = V ⊓ U) :
    V ⊓ (U ⊓ rightConjugate U y ⊓ rightConjugate U ((y : G)*(t : G))) ≤ Z := by
  intro x hx
  let xv : V := ⟨x,hx.1⟩
  apply double_perp_point c hZV hZcard hperp xv
  rw [← hspan]
  apply sup_le
  · apply sup_le
    · intro z hz
      exact ⟨inclusion hZV ⟨z,hz⟩, (hperp xv).mp hx.2.1.1 ⟨z,hz⟩, rfl⟩
    · exact conjugate_point_le_kernel d c hq hZV hperp y xv hx.2.1.2
  · exact conjugate_point_le_kernel d c hq hZV hperp (y*t) xv hx.2.2

private theorem conjugate_product (A : Subgroup G) (y t : G) :
    rightConjugate (rightConjugate A y) t = rightConjugate A (y*t) := by
  unfold rightConjugate
  rw [Subgroup.map_map]
  congr 1
  ext a
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc]

/-- The two source planes give exactly the three marked points, since the
chosen Sylow element fixes the original point. -/
theorem triple_point_span (V₀ : Subgroup G) (y t : G)
    (hplane : V₀ = Z ⊔ rightConjugate Z y)
    (ht : rightConjugate Z t = Z)
    (hjoin : V₀ ⊔ rightConjugate V₀ t = W) :
    Z ⊔ rightConjugate Z y ⊔ rightConjugate Z (y*t) = W := by
  have hc : rightConjugate (Z ⊔ rightConjugate Z y) t =
      rightConjugate Z t ⊔ rightConjugate (rightConjugate Z y) t :=
    Subgroup.map_sup _ _ _
  rw [hplane, hc, ht, conjugate_product] at hjoin
  simpa only [sup_assoc, sup_left_comm, sup_idem, sup_left_idem] using hjoin

/-- The original source's E meets its t-conjugate in Z once the independent
quotient calculation puts the intersection in the natural four-space. -/
theorem intersection_conjugate_eq_point (d : NaturalOrthogonalAction M V)
    (c : V ≃* Multiplicative (Mat (F := ZMod 2)))
    (hq : ∀ v : V, determinantForm (c v).toAdd =
      FusionCore.orthogonalCoordinateValue (d.coordinates v))
    (hZV : Z ≤ V) (hZcard : Nat.card Z = 2)
    (hperp : ∀ v : V, (v : G) ∈ U ↔ ∀ z : Z,
      determinantForm.polarBilin (c v).toAdd (c (inclusion hZV z)).toAdd = 0)
    (E V₀ : Subgroup G) (y t : M)
    (hE : E = U ⊓ rightConjugate U y)
    (hZE : Z ≤ E) (htZ : rightConjugate Z t = Z)
    (hplane : V₀ = Z ⊔ rightConjugate Z y)
    (hjoin : V₀ ⊔ rightConjugate V₀ t = V ⊓ U)
    (hupper : E ⊓ rightConjugate E t ≤ V) :
    E ⊓ rightConjugate E t = Z := by
  apply le_antisymm
  · apply le_trans ?_ (triple_intersection_le_point d c hq hZV hZcard hperp y t
      (triple_point_span V₀ y t hplane htZ hjoin))
    intro x hx
    have he : x ∈ U ⊓ rightConjugate U y := hE ▸ hx.1
    have hyt : rightConjugate E t ≤ rightConjugate U ((y : G)*(t : G)) := by
      rw [← conjugate_product]
      exact map_mono (hE ▸ inf_le_right)
    exact ⟨hupper hx, he, hyt hx.2⟩
  · refine le_inf hZE ?_
    rw [← htZ]
    exact map_mono hZE

variable [Finite G]

/-- Source54's marked determinant coordinates discharge the perpendicular
input to the literal source56 intersection. The geometric plane join comes
from the selected tensor factor; the natural-space upper bound comes from
the separate quotient intersection argument. -/
theorem source_intersection_conjugate_eq_point
    (d : CharacteristicTwo.LocalData G) (Zperp : Subgroup G) (g : G)
    (h26 : Hypothesis (Chapter15.setup d.Z Zperp d.Y d.T) g)
    (hspan : localSpan d.Z d.Y = d.V)
    (hmark : ∀ v : (Chapter15.setup d.Z Zperp d.Y d.T).VL,
      determinantForm (h26.coordinates v).toAdd =
        FusionCore.orthogonalCoordinateValue
          (d.action.coordinates ((MulEquiv.subgroupCongr hspan) v)))
    (hperp : Zperp = d.V ⊓ closureU d.Z d.ZS)
    (V₀ : Subgroup G) (y t : G) (hy : y ∈ d.M) (ht : t ∈ d.T)
    (hE : intersectionE d.Z d.ZS y =
      closureU d.Z d.ZS ⊓ rightConjugate (closureU d.Z d.ZS) y)
    (hZE : d.Z ≤ intersectionE d.Z d.ZS y)
    (hplane : V₀ = d.Z ⊔ rightConjugate d.Z y)
    (hjoin : V₀ ⊔ rightConjugate V₀ t = Zperp)
    (hupper : intersectionE d.Z d.ZS y ⊓
      rightConjugate (intersectionE d.Z d.ZS y) t ≤ d.V) :
    intersectionE d.Z d.ZS y ⊓ rightConjugate (intersectionE d.Z d.ZS y) t = d.Z := by
  have htZ : rightConjugate d.Z t = d.Z := by
    have hTC : (d.T : Subgroup G) ≤ centralizer (d.Z : Set G) :=
      le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow d.T)
    exact mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer _ (hTC (d.T.inv_mem ht)))
  let e : (Chapter15.setup d.Z Zperp d.Y d.T).VL ≃* d.V :=
    MulEquiv.subgroupCongr hspan
  let c := e.symm.trans h26.coordinates
  have hZV : d.Z ≤ d.V := hspan ▸ point_le_VL (Chapter15.setup d.Z Zperp d.Y d.T)
  have hq (v : d.V) : determinantForm (c v).toAdd =
      FusionCore.orthogonalCoordinateValue (d.action.coordinates v) := by
    exact (hmark (e.symm v)).trans (congrArg
      (fun w : d.V => FusionCore.orthogonalCoordinateValue (d.action.coordinates w))
      (e.apply_symm_apply v))
  have hp (v : d.V) : (v : G) ∈ closureU d.Z d.ZS ↔ ∀ z : d.Z,
      determinantForm.polarBilin (c v).toAdd (c (inclusion hZV z)).toAdd = 0 := by
    have hh := h26.perpendicular (e.symm v)
    change (v : G) ∈ Zperp ↔ ∀ z : d.Z,
      determinantForm.polarBilin (c v).toAdd (c (inclusion hZV z)).toAdd = 0 at hh
    have hm : (v : G) ∈ Zperp ↔ (v : G) ∈ closureU d.Z d.ZS := by
      rw [hperp]
      exact and_iff_right v.property
    exact hm.symm.trans hh
  exact intersection_conjugate_eq_point d.action c hq hZV h26.point_card hp
    (intersectionE d.Z d.ZS y) V₀ ⟨y,hy⟩ ⟨t,d.sylow_le ht⟩ hE hZE htZ hplane
    (hjoin.trans hperp) hupper


end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
