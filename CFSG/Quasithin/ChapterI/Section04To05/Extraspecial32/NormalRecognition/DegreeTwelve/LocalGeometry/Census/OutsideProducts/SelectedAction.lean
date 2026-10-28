module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.LocalData
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Fusion.Count.LocalOrbit.Action
public import Theory.GroupTheory.QuaternionCentralProductC2Rank

/-!
# The selected inverter is outer on both quaternion factors

Write H = C_G(z) and Q = F*(H). Relative quaternion normality preserves
both actual factors of Q. Restricting conjugation to either factor gives
an H-action on that quaternion group. A generator of the original Sylow
three-subgroup acts nontrivially: otherwise the whole factor lies in
C_Q(X) = ⟨z⟩, contradicting its order eight.

The selected involution inverts this cubic action. An inner inverter would
make the square of the cubic inner. Every inner automorphism of a quaternion
factor has square one, since all squares are central in Q. The cubic would
then have both fourth and third power one, a contradiction.

This proves preservation and non-innerness for each supplied factor, without
an orbit profile, product count, ambient order, or recognition assumption.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 2.2–2.3(2)(b), especially the fixed-point and
inversion argument on printed pp.33–34.
-/

open Subgroup

private theorem cubic_eq_one_of_inner_inverts {D : Type*} [Group D]
    (hsq : ∀ c : D, (MulAut.conj c) ^ 2 = 1)
    (β : MulAut D) (hβ : β ^ 3 = 1) (c : D)
    (hinv : MulAut.conj c * β * (MulAut.conj c)⁻¹ = β⁻¹) : β = 1 := by
  have hnat : β * MulAut.conj c * β⁻¹ = MulAut.conj (β c) := by
    ext x
    simp [MulAut.mul_apply, MulAut.conj_apply]
  have hrel : β * MulAut.conj c * β = MulAut.conj c := by
    have he := mul_inv_eq_iff_eq_mul.mp hinv
    calc
      β * MulAut.conj c * β = β * (MulAut.conj c * β) := mul_assoc _ _ _
      _ = β * (β⁻¹ * MulAut.conj c) := by rw [he]
      _ = MulAut.conj c := by group
  have hβ2 : β ^ 2 = MulAut.conj ((β c)⁻¹ * c) := by
    apply mul_left_cancel (a := MulAut.conj (β c))
    calc
      MulAut.conj (β c) * β ^ 2 = (β * MulAut.conj c * β⁻¹) * β ^ 2 := by rw [hnat]
      _ = β * MulAut.conj c * β := by group
      _ = MulAut.conj c := hrel
      _ = MulAut.conj (β c) * MulAut.conj ((β c)⁻¹ * c) := by
        rw [← map_mul, mul_inv_cancel_left]
  have hβ4 := hsq ((β c)⁻¹ * c)
  rw [← hβ2, ← pow_mul] at hβ4
  have he : β ^ 4 = β := by rw [show 4 = 3 + 1 from rfl, pow_succ, hβ, one_mul]
  exact he.symm.trans hβ4

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.Census
variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem selected_factor_outer (h : Hypotheses z)
    (a : SelectedFusionData h) (q : QuaternionCentralProductData (Core z))
    (R : Subgroup (Core z)) (hR : Nonempty (R ≃* QuaternionGroup 2))
    (hpres : ∀ c : Centralizer z, R.map (MulAut.conjNormal c).toMonoidHom = R) :
    ¬ ∃ b : R, ∀ x : R,
      MulAut.conjNormal (⟨a.u, a.u_centralizes⟩ : Centralizer z) (x : Core z) =
        (b : Core z) * x * (b : Core z)⁻¹ := by
  let σ : Centralizer z →* MulAut R :=
    { toFun c := ((MulAut.conjNormal c : MulAut (Core z)).subgroupMap R).trans
        (MulEquiv.subgroupCongr (hpres c))
      map_one' := by
        apply MulEquiv.ext
        intro x
        apply Subtype.ext
        exact DFunLike.congr_fun (map_one (MulAut.conjNormal : Centralizer z →* MulAut (Core z))) (x : Core z)
      map_mul' c d := by
        apply MulEquiv.ext
        intro x
        apply Subtype.ext
        exact DFunLike.congr_fun (map_mul (MulAut.conjNormal : Centralizer z →* MulAut (Core z)) c d) (x : Core z) }
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := h.X) 3 (by rw [h.sylow_three_card])
  have hr1 : r ≠ 1 := by intro he; simp [he] at hr
  have hr3 : (r : Centralizer z) ^ 3 = 1 := congrArg Subtype.val
    (show r ^ 3 = 1 by simpa only [hr] using pow_orderOf_eq_one r)
  have hσ3 : (σ (r : Centralizer z)) ^ 3 = 1 := by rw [← map_pow, hr3, map_one]
  have hσne : σ (r : Centralizer z) ≠ 1 := by
    intro he
    have hle : R ≤ center (Core z) := by
      intro x hx
      have hfix : MulAut.conjNormal (r : Centralizer z) x = x :=
        congrArg Subtype.val (DFunLike.congr_fun he (⟨x, hx⟩ : R))
      have hcomm : Commute (r : Centralizer z) (x : Centralizer z) :=
        mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hfix)
      have hc : (x : Centralizer z) ∈ centralizer (h.X : Set (Centralizer z)) := by
        intro y hy
        obtain ⟨n, hn⟩ := mem_zpowers_iff.mp
          (mem_zpowers_of_prime_card h.sylow_three_card hr1 (g' := (⟨y, hy⟩ : h.X)))
        have hyn : (r : Centralizer z) ^ n = y := congrArg Subtype.val hn
        rw [← hyn]
        exact (hcomm.zpow_left n).eq
      have hz : (x : Centralizer z) ∈ (center (Core z)).map (Core z).subtype := by
        rw [h.core_center_image, ← h.fixed]
        exact ⟨x.property, hc⟩
      obtain ⟨x', hx', he⟩ := hz
      exact (show x' = x from Subtype.ext he) ▸ hx'
    have hc := card_le_of_le hle
    rw [q.center_card, Nat.card_congr hR.some.toEquiv,
      show Nat.card (QuaternionGroup 2) = 8 by
        rw [Nat.card_eq_fintype_card, QuaternionGroup.card]] at hc
    omega
  rintro ⟨b, hb⟩
  let u : Centralizer z := ⟨a.u, a.u_centralizes⟩
  have hinner : σ u = MulAut.conj b := by
    apply MulEquiv.ext
    intro x
    exact Subtype.ext (hb x)
  have hinv : MulAut.conj b * σ (r : Centralizer z) * (MulAut.conj b)⁻¹ =
      (σ (r : Centralizer z))⁻¹ := by
    rw [← hinner, ← map_inv, ← map_mul, ← map_mul]
    rw [← map_inv]
    apply congrArg σ
    exact Subtype.ext (a.u_inverts_X r)
  apply hσne
  apply cubic_eq_one_of_inner_inverts _ _ hσ3 b hinv
  intro c
  rw [← map_pow]
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change (c : Core z) ^ 2 * (x : Core z) * ((c : Core z) ^ 2)⁻¹ = x
  have hc := (mem_center_iff.mp (q.square_mem_center (c : Core z)) (x : Core z)).symm
  rw [hc, mul_inv_cancel_right]

/-- The selected inverter is outer on each of the two actual quaternion factors. -/
public theorem selected_bothOuter (h : Hypotheses z) (hn : QuaternionSubgroupsNormal z)
    (a : SelectedFusionData h) (q : QuaternionCentralProductData (Core z)) :
    q.BothOuter (MulAut.conjNormal (⟨a.u, a.u_centralizes⟩ : Centralizer z)) := by
  have hp := h.localOrbit_factor_preserved hn q
  exact ⟨(hp _).1, (hp _).2,
    selected_factor_outer h a q q.left q.left_model (fun c => (hp c).1),
    selected_factor_outer h a q q.right q.right_model (fun c => (hp c).2)⟩

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.Census
