module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.HallNormalizer

/-!
# Suzuki's cubic relation for the original marked linear endpoints

A central-line intersection determines a unique Hall coset. Hence among the
odd-order elements of the Hall normalizer there are at most two nontrivial
cosets: the disjoint and root-plane cases contain involutions and therefore
have trivial odd-order images. Apply this to the first three powers of the
same marked Weyl product. If its cube were outside the Hall subgroup, two
of these three powers would have the same exceptional line. Their quotient
is the first or second power; odd order makes either generate the same
cyclic subgroup, a contradiction.

Thus the cube belongs to the actual full Hall subgroup in original G, not
merely to a torus centralizer or a quotient replacement. This is the prepared
linear specialization of Aschbacher–Smith F.4.49(3), printed p.299 of
`refs/quasithin.pdf`, including q=4 and both comparison orientations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
open Subgroup.OddHall CFSG.Quasithin.Chapter5.Section03LinearSource
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include d h hH hp hm hF he hmax


variable (c : ChapterF.SourceCompletion.LinearThreeEven.NativeCompletion F G)
    (i : Bool)
    (hleft : c.family i=ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0)
    (hright : c.family (!i)=ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1)
    (hmid : c.middle.range=ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
include hleft hright hmid


/-- Two exceptional Hall cosets of the same marked line are equal. -/
theorem Preparation.linear_hall_same_line_coset
    (j : Bool) (g u : G)
    (hg : g∈normalizer ((normalizer (T : Set G) ⊓ normalizer (c.torusHom.range : Set G) : Subgroup G) : Set G))
    (hu : u∈normalizer ((normalizer (T : Set G) ⊓ normalizer (c.torusHom.range : Set G) : Subgroup G) : Set G))
    (hgi : (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g=(centerIn (sourceS L H)).conjBy (c.weyl j))
    (hui : (T : Subgroup G) ⊓ (T : Subgroup G).conjBy u=(centerIn (sourceS L H)).conjBy (c.weyl j))
    (hgn : (centerIn (sourceS L H)).conjBy (c.weyl j)≠(centerIn (sourceS L H)).conjBy g)
    (hun : (centerIn (sourceS L H)).conjBy (c.weyl j)≠(centerIn (sourceS L H)).conjBy u) :
    g⁻¹*u∈normalizer (T : Set G) ⊓ normalizer (c.torusHom.range : Set G) := by
  let Z := centerIn (sourceS L H)
  let B₀ := normalizer (T : Set G) ⊓ normalizer (c.torusHom.range : Set G)
  have hcent (x : G)
      (hx : x∈normalizer (B₀ : Set G))
      (hxi : (T : Subgroup G) ⊓ (T : Subgroup G).conjBy x=Z.conjBy (c.weyl j))
      (hxn : Z.conjBy (c.weyl j)≠Z.conjBy x) :
      Z.conjBy x=Z.conjBy (c.weyl j*c.weyl (!j)) := by
    by_cases hj : j=i
    · subst j
      exact d.linear_hall_line_case_center h hH hp F hm hF he hmax c i hleft hright hmid
        i 0 hleft (by simpa [ChapterF.Source.other] using hright) x hx hxi hxn
    · have hj' : j=(!i) := by cases i <;> cases j <;> simp_all
      subst j
      exact d.linear_hall_line_case_center h hH hp F hm hF he hmax c i hleft hright hmid
        (!i) 1 hright (by simpa [ChapterF.Source.other] using hleft) x hx hxi hxn
  have heq : Z.conjBy u=Z.conjBy g :=
    (hcent u hu hui hun).trans (hcent g hg hgi hgn).symm
  have hNZ : g⁻¹*u∈normalizer (Z : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change Z.conjBy (g⁻¹*u)=Z
    rw [←conjBy_conjBy,heq,conjBy_conjBy,inv_mul_cancel,conjBy_one]
  have hZN : normalizer (Z : Set G)=normalizer (T : Set G) :=
    (d.linear_center_normalizer h hH hp F hm hF he hmax).trans
      (d.linear_sylow_normalizer_eq_inter h hH hp F hm hF he hmax).symm
  obtain ⟨_,_,_,_,_,hstab⟩ := d.linear_native_full_hall h hH hp F hm hF he hmax c i hleft hright hmid
  exact hstab.le ⟨hZN ▸ hNZ,(normalizer _).mul_mem ((normalizer _).inv_mem hg) hu⟩

/-- Suzuki's two exceptional cosets force the cube of the same odd-order
native Weyl product into the actual full odd Hall subgroup. -/
theorem Preparation.linear_native_weyl_cube_mem_hall :
    (c.weyl i*c.weyl (!i))^3∈normalizer (T : Set G) ⊓ normalizer (c.torusHom.range : Set G) := by
  let B₀ := normalizer (T : Set G) ⊓ normalizer (c.torusHom.range : Set G)
  let r := c.weyl i*c.weyl (!i)
  obtain ⟨_,_,_,_,hsB,_⟩ := d.linear_native_full_hall h hH hp F hm hF he hmax c i hleft hright hmid
  have hr : r∈normalizer (B₀ : Set G) := (normalizer _).mul_mem (hsB i) (hsB (!i))
  have hm' : 1<m := (d.linear_core_structure h hH hp F hm hF he).1 ▸ h.exponent
  have ho : Odd (orderOf r) := c.weyl_product_odd hF hm'
    (fun z hz => by
      obtain ⟨P,_,hP⟩ := d.linear_involution_centralizer_sylow h hH hp F hm hF he hmax z hz
      exact ⟨P,hP⟩) i
  have hsq (hh : r^2∈B₀) : r∈B₀ :=
    (zpowers_le.mpr hh) (mem_zpowers_pow_iff.mpr (Nat.coprime_two_left.mpr ho))
  by_contra hc
  have hn1 : r^1∉B₀ := by
    simpa only [pow_one] using (show r∉B₀ from fun hh => hc (B₀.pow_mem hh 3))
  have hn2 : r^2∉B₀ := fun hh => hc (B₀.pow_mem (hsq hh) 3)
  have hn3 : r^3∉B₀ := hc
  have hcases (a : ℕ) (ha : r^a∉B₀) :
      ∃ j : Bool, (T : Subgroup G) ⊓ (T : Subgroup G).conjBy (r^a)=
        (centerIn (sourceS L H)).conjBy (c.weyl j) ∧
        (centerIn (sourceS L H)).conjBy (c.weyl j)≠(centerIn (sourceS L H)).conjBy (r^a) := by
    have hh := d.linear_hall_coset_alternatives h hH hp F hm hF he hmax c i hleft hright hmid
      (r^a) ((normalizer _).pow_mem hr a)
    rcases hh with hh | ⟨w,hw,hwc⟩ | hh
    · exact (ha hh).elim
    · exact (ha (odd_element_mem_of_involution_coset B₀ (r^a) w ((normalizer _).pow_mem hr a)
        (ho.of_dvd_nat (orderOf_pow_dvd a)) hw hwc)).elim
    · exact hh
  obtain ⟨j₁,h₁,hn₁⟩ := hcases 1 hn1
  obtain ⟨j₂,h₂,hn₂⟩ := hcases 2 hn2
  obtain ⟨j₃,h₃,hn₃⟩ := hcases 3 hn3
  have hdup : j₁=j₂ ∨ j₁=j₃ ∨ j₂=j₃ := by
    cases j₁ <;> cases j₂ <;> cases j₃ <;> decide
  have hsame (a b : ℕ) (j : Bool)
      (ha : (T : Subgroup G) ⊓ (T : Subgroup G).conjBy (r^a)=(centerIn (sourceS L H)).conjBy (c.weyl j))
      (hb : (T : Subgroup G) ⊓ (T : Subgroup G).conjBy (r^b)=(centerIn (sourceS L H)).conjBy (c.weyl j))
      (hna : (centerIn (sourceS L H)).conjBy (c.weyl j)≠(centerIn (sourceS L H)).conjBy (r^a))
      (hnb : (centerIn (sourceS L H)).conjBy (c.weyl j)≠(centerIn (sourceS L H)).conjBy (r^b)) :
      (r^a)⁻¹*r^b∈B₀ :=
    d.linear_hall_same_line_coset h hH hp F hm hF he hmax c i hleft hright hmid j (r^a) (r^b)
      ((normalizer _).pow_mem hr a) ((normalizer _).pow_mem hr b) ha hb hna hnb
  have hrB : r∈B₀ := by
    rcases hdup with hdup | hdup | hdup
    · subst j₂
      have hh := hsame 1 2 j₁ h₁ h₂ hn₁ hn₂
      simpa only [pow_one,pow_two,inv_mul_cancel_left] using hh
    · subst j₃
      have hh := hsame 1 3 j₁ h₁ h₃ hn₁ hn₃
      apply hsq
      have heq : (r^1)⁻¹*r^3=r^2 := by group
      exact heq ▸ hh
    · subst j₃
      have hh := hsame 2 3 j₂ h₂ h₃ hn₂ hn₃
      have heq : (r^2)⁻¹*r^3=r := by group
      exact heq ▸ hh
  exact hc (B₀.pow_mem hrB 3)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
