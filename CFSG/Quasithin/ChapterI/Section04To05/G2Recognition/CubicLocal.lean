module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.ExtensionInvolution
public import Theory.SpecificGroups.SL2.ThreeCubicCentralizer

/-!
# Cubic centralizers in the marked involution centralizer

The simultaneous outer factor action forces C_H(H₁)=H₂. An automorphism
of SL₂(3) fixing a nonidentity cubic element is inner, so for x∈H₁ of
order three one obtains C_H(x)=H₂⟨x⟩, of order72. The shared central
involution and both original inclusions are retained. Interchanging the
marked factors supplies the same calculation for the other factor.

This is the local input to `CubicCentralizer`, following Fong–Wong,
Nagoya Math. J.36 (1969), §3B–C, p.156, for the configuration in
Aschbacher–Smith I.4.5, printed p.417.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)
attribute [local instance] G2ThreeConfiguration.H₁_normal G2ThreeConfiguration.H₂_normal

/-- Interchange the two normal factors while preserving both local embeddings. -/
def swapFactors : G2ThreeConfiguration G := {
  c with
  H₁ := c.H₂, H₂ := c.H₁
  H₁_normal := c.H₂_normal, H₂_normal := c.H₁_normal
  H₁_model := c.H₂_model, H₂_model := c.H₁_model
  commute := fun a ha b hb => (c.commute b hb a ha).symm
  index := by simpa only [sup_comm] using c.index
  intersection_model := ⟨(MulEquiv.subgroupCongr (inf_comm c.H₂ c.H₁)).trans
    c.intersection_model.some⟩
  centralizer := by simpa only [inf_comm] using c.centralizer }

theorem left_factor_centralizer : centralizer (c.H₁ : Set c.H) = c.H₂ := by
  apply le_antisymm
  · intro h hh
    have hK : h ∈ c.H₁ ⊔ c.H₂ := by
      by_contra hn
      apply (outside_bothOuter c h hn).left_outer
      refine ⟨1, ?_⟩
      intro x
      apply Subtype.ext
      change h * ((x : quaternionCore c) : c.H) * h⁻¹ = _
      have hx : ((x : quaternionCore c) : c.H) ∈ c.H₁ := c.H₁.pCoreIn_le 2 x.property
      rw [← hh _ hx]
      simp
    have he := (markedResidual c).centralizer_descriptions.2
    change c.H₂ = _ at he
    rw [he]
    refine ⟨?_, ?_⟩
    · rwa [H_residual c]
    · rintro q ⟨r,hr,rfl⟩
      exact hh r (c.H₁.pCoreIn_le 2 hr)
  · intro h hh a ha
    exact c.commute a ha h hh

theorem left_factor_center : (center c.H₁).map c.H₁.subtype = c.H₁ ⊓ c.H₂ := by
  apply le_antisymm
  · rintro x ⟨a,ha,rfl⟩
    refine ⟨a.property, ?_⟩
    rw [← left_factor_centralizer c]
    intro b hb
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨b,hb⟩)
  · intro x hx
    exact ⟨⟨x,hx.1⟩,mem_center_iff.mpr (fun y =>
      Subtype.ext (c.commute y y.property x hx.2)),rfl⟩

theorem left_cubic_local_centralizer (x : c.H₁) (hx : orderOf x = 3) :
    centralizer ({(x:c.H)} : Set c.H) = c.H₂ ⊔ zpowers (x:c.H) := by
  apply le_antisymm
  · intro h hh
    let a : MulAut c.H₁ := MulAut.conjNormal h
    have hax : a x = x := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hh)
    obtain ⟨y,hy⟩ := Matrix.SpecialLinearGroup.cubic_fixer_inner_of_equiv
      c.H₁_model.some a x hx hax
    have hky : (y:c.H)⁻¹*h ∈ centralizer (c.H₁ : Set c.H) := by
      intro t ht
      have he := congrArg (fun f : MulAut c.H₁ => (f ⟨t,ht⟩ : c.H)) hy
      change h*t*h⁻¹=(y:c.H)*t*(y:c.H)⁻¹ at he
      have he' : ((y:c.H)⁻¹*h)*t*((y:c.H)⁻¹*h)⁻¹=t := by
        calc
          _ = (y:c.H)⁻¹*(h*t*h⁻¹)*(y:c.H) := by group
          _ = t := by rw [he]; group
      exact (mul_inv_eq_iff_eq_mul.mp he').symm
    have hyx : y ∈ centralizer ({x} : Set c.H₁) := by
      rw [hy] at hax
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hax)
    rw [Matrix.SpecialLinearGroup.cubic_centralizer_of_equiv c.H₁_model.some x hx] at hyx
    have hmap : (center c.H₁ ⊔ zpowers x).map c.H₁.subtype ≤ c.H₂ ⊔ zpowers (x:c.H) := by
      rw [Subgroup.map_sup, left_factor_center c, MonoidHom.map_zpowers]
      exact sup_le_sup inf_le_right le_rfl
    have hyJ : (y:c.H) ∈ c.H₂ ⊔ zpowers (x:c.H) :=
      hmap (mem_map_of_mem c.H₁.subtype hyx)
    have hkJ : (y:c.H)⁻¹*h ∈ c.H₂ ⊔ zpowers (x:c.H) :=
      mem_sup_left (left_factor_centralizer c ▸ hky)
    simpa only [mul_inv_cancel_left] using
      (c.H₂ ⊔ zpowers (x:c.H)).mul_mem hyJ hkJ
  · refine sup_le ?_ (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
    intro h hh
    exact mem_centralizer_singleton_iff.mpr (c.commute x x.property h hh).symm

theorem left_cubic_local_centralizer_card (x : c.H₁) (hx : orderOf x = 3) :
    Nat.card (centralizer ({(x:c.H)} : Set c.H)) = 72 := by
  have hc : Nat.card c.H₂ = 24 := (Nat.card_congr c.H₂_model.some.toEquiv).trans
    GLS3.Chapter5.SchurPresentation.sl23_card_eq
  have hi : c.H₂ ⊓ zpowers (x:c.H) = ⊥ := by
    have hle : c.H₂ ⊓ zpowers (x:c.H) ≤ c.H₁ ⊓ c.H₂ :=
      le_inf ((inf_le_right).trans (zpowers_le.mpr x.property)) inf_le_left
    have hd : Nat.card (c.H₂ ⊓ zpowers (x:c.H) : Subgroup c.H) ∣ 1 := by
      have h2 := card_dvd_of_le hle
      rw [intersection_card c] at h2
      have h3 := card_dvd_of_le (show c.H₂ ⊓ zpowers (x:c.H) ≤ zpowers (x:c.H) from inf_le_right)
      rw [Nat.card_zpowers,orderOf_coe,hx] at h3
      simpa using Nat.dvd_gcd h2 h3
    exact card_eq_one.mp (Nat.dvd_one.mp hd)
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes c.H₂ (zpowers (x:c.H))
    (show zpowers (x:c.H) ≤ normalizer (c.H₂:Set c.H) from le_normalizer_of_normal)
  rw [hc,Nat.card_zpowers,orderOf_coe,hx,hi,Nat.card_unique,one_mul] at hh
  rw [left_cubic_local_centralizer c x hx]
  exact hh.symm
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
