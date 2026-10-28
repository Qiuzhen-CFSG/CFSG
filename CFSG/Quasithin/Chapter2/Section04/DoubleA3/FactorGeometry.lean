module

public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.QuotientFusion

/-!
# Separating the kernel from the pure dihedral factor

For a factor E disjoint from K, an involution of E projecting into the
image of K must lie in the cyclic centralizer kernel B. Write it kb with
k in K and b in B. Commutation makes b² lie in K ∩ B, so b is the unique
kernel involution. Disjointness then removes k. No containment B ≤ E is
assumed: the cyclic centralizer may be diagonally embedded in R.

This supplies the missing partition condition in the corrected final count
on printed p.550 of Aschbacher–Smith. The literal two-factor fusion
containment from 2.4.37 is retained explicitly.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2.DoubleA3
open Subgroup

variable {G : Type*} [Group G]

private theorem cyclic_four_involutions_equal (B : Subgroup G)
    (eB : B ≃* Multiplicative (ZMod 4))
    {a b : G} (haB : a ∈ B) (hbB : b ∈ B)
    (ha : a ^ 2 = 1) (ha1 : a ≠ 1) (hb : b ^ 2 = 1) (hb1 : b ≠ 1) : a = b := by
  have hc : ∀ x y : Multiplicative (ZMod 4),
      x ^ 2 = 1 → x ≠ 1 → y ^ 2 = 1 → y ≠ 1 → x = y := by decide +kernel
  have he : eB ⟨a, haB⟩ = eB ⟨b, hbB⟩ := hc _ _
    (by rw [← map_pow]; exact eB.map_eq_one_iff.mpr (Subtype.ext ha))
    (fun h => ha1 (congrArg Subtype.val (eB.map_eq_one_iff.mp h)))
    (by rw [← map_pow]; exact eB.map_eq_one_iff.mpr (Subtype.ext hb))
    (fun h => hb1 (congrArg Subtype.val (eB.map_eq_one_iff.mp h)))
  exact congrArg Subtype.val (eB.injective he)

/-- In a factor disjoint from K, an involution cannot project into K
except through the cyclic centralizer kernel. -/
theorem pure_factor_quotient_separation (B K E : Subgroup G) [B.Normal]
    (hcentral : B ≤ centralizer (K : Set G)) (hBK : Disjoint B K)
    (hEK : Disjoint E K) (eB : B ≃* Multiplicative (ZMod 4))
    (z : G) (hzB : z ∈ B) (hzE : z ∈ E) (hz : z ^ 2 = 1) (hz1 : z ≠ 1)
    (a : G) (haE : a ∈ E) (ha : a ^ 2 = 1) (haK : a ∉ K) (haB : a ∉ B) :
    QuotientGroup.mk' B a ∉ K.map (QuotientGroup.mk' B) := by
  intro hmap
  obtain ⟨k, hk, hka⟩ := hmap
  let b := k⁻¹ * a
  have hbB : b ∈ B := by
    apply (QuotientGroup.eq_one_iff b).mp
    change QuotientGroup.mk' B (k⁻¹ * a) = 1
    rw [map_mul, map_inv, hka, inv_mul_cancel]
  have hab : a = k * b := by simp [b]
  have hcomm : Commute k b := hcentral hbB k hk
  have hsquare : k ^ 2 * b ^ 2 = 1 := by rw [← hcomm.mul_pow, ← hab, ha]
  have hb2K : b ^ 2 ∈ K := by
    have he : b ^ 2 = (k ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hsquare
    rw [he]
    exact K.inv_mem (K.pow_mem hk 2)
  have hb2 : b ^ 2 = 1 := disjoint_def.mp hBK (B.pow_mem hbB 2) hb2K
  have hb1 : b ≠ 1 := by
    intro h
    apply haK
    rw [hab, h, mul_one]
    exact hk
  have hbz : b = z := cyclic_four_involutions_equal B eB hbB hzB hb2 hb1 hz hz1
  have hkE : k ∈ E := by
    have he : k = a * z⁻¹ := by rw [hab, ← hbz]; group
    rw [he]
    exact E.mul_mem haE (E.inv_mem hzE)
  have hk1 := disjoint_def.mp hEK hkE hk
  have haz : a = z := by simpa only [hk1, hbz, one_mul] using hab
  exact haB (haz ▸ hzB)

/-- The pure-factor fusion containment identifies the literal outside set
with the class intersection in the other factor; disjointness excludes
its identity automatically. -/
theorem fusionOutside_eq_factor (H : Subgroup G) (z : G) (hz1 : z ≠ 1)
    (R K E : Subgroup H) (hER : E ≤ R) (hEK : Disjoint E K)
    (hpure : ∀ a : H, IsConj z (a : G) → a ∈ R → a ∈ K ∨ a ∈ E) :
    fusionOutside H z R K = {a : H | IsConj z (a : G) ∧ a ∈ E} := by
  ext a
  constructor
  · rintro ⟨ha, haR, haK⟩
    exact ⟨ha, (hpure a ha haR).resolve_left haK⟩
  · rintro ⟨ha, haE⟩
    refine ⟨ha, hER haE, ?_⟩
    intro haK
    have ha1 : a = 1 := disjoint_def.mp hEK haE haK
    obtain ⟨g, hg⟩ := isConj_iff.mp ha
    apply hz1
    apply (MulAut.conj g).map_eq_one_iff.mp
    exact hg.trans (congrArg Subtype.val ha1)

/-- The terminal two-A₃ counting contradiction, with both counts derived.
The remaining premises are subgroup recognition and the pure-factor
fusion containment; there is no numerical or fiber-size premise. -/
theorem false_of_terminal_geometry [Finite G] (H : Subgroup G)
    (B R K E : Subgroup H) [B.Normal]
    (hcentral : B ≤ centralizer (K : Set H)) (hBK : Disjoint B K)
    (hBR : B ≤ R) (hER : E ≤ R) (hEK : Disjoint E K)
    (z : H) (hz : z ^ 2 = 1) (hz1 : z ≠ 1) (hzB : z ∈ B) (hzK : z ∉ K)
    (eB : B ≃* Multiplicative (ZMod 4)) (eE : E ≃* DihedralGroup 4)
    (eQ : (H ⧸ B) ≃* AlternatingSix.ShadowLocal.AutA6)
    (hinner : (K.map (QuotientGroup.mk' B)).map eQ.toMonoidHom =
      AlternatingSix.ShadowLocal.inner)
    (hnatural : (R.map (QuotientGroup.mk' B)).map eQ.toMonoidHom ≤
      AlternatingSix.ShadowLocal.natural)
    (eR : R.map (QuotientGroup.mk' B) ≃*
      Multiplicative (ZMod 2) × DihedralGroup 4)
    (hmark : ∀ q : R.map (QuotientGroup.mk' B),
      (q : H ⧸ B) ∈ K.map (QuotientGroup.mk' B) ↔ (eR q).1 = 1)
    (hpure : ∀ a : H, IsConj (z : G) (a : G) → a ∈ R → a ∈ K ∨ a ∈ E)
    (hEfuse : ∀ a : E, a ^ 2 = 1 → a ≠ 1 → IsConj (z : G) ((a : H) : G)) :
    False := by
  have hzE : z ∈ E := (hpure z (IsConj.refl _) (hBR hzB)).resolve_left hzK
  obtain ⟨u, hu⟩ := exists_uniform_quotient_fusion B R K eQ hinner hnatural
  have hcount := terminal_count H B R K z hz hz1 hzB hzK hBR eB u eR hmark hu
    (fun a ha haR haK haB => pure_factor_quotient_separation B K E hcentral hBK
      hEK eB z hzB hzE hz hz1 a ((hpure a ha haR).resolve_left haK)
      (by
        obtain ⟨g, hg⟩ := isConj_iff.mp ha
        apply Subtype.ext
        change (a : G) ^ 2 = 1
        have hh : ((MulAut.conj g) (z : G)) ^ 2 = 1 := by
          rw [← map_pow, show (z : G) ^ 2 = 1 from congrArg Subtype.val hz, map_one]
        simpa only [MulAut.conj_apply, hg] using hh) haK haB)
  have hzG1 : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hcard : Nat.card (fusionOutside H (z : G) R K) = 5 := by
    rw [fusionOutside_eq_factor H (z : G) hzG1 R K E hER hEK hpure]
    exact dihedral_fusion_card H E (z : G) (congrArg Subtype.val hz) hzG1 eE hEfuse
  omega

end CFSG.Quasithin.Chapter2.DoubleA3
