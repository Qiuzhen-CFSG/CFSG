module

public import Theory.GroupTheory.SaturatedCentralizerTransport
public import Theory.GroupTheory.PGroup.NormalExtraspecialDerivedCenter

/-!
# Local fusion forced by a saturated derived-center line

Suppose the saturated Sylow centralizer of `x` has derived-center line
`⟨z⟩`. For a conjugate `y`, first assume local saturation in `C_G(z)`.
If a subgroup `D ≤ C_S(y)` has `z` in its derived group and centralizer
contained in `⟨z,y⟩`, Sylow transport can be adjusted to fix `z`.

Indeed transport the central line back into `C_G(y)`. It centralizes the
transported Sylow centralizer, so local saturation places it in `S`. The
double-centralizer bound puts it in `⟨z,y⟩`. Since `x ≠ z`, this makes the
image of `z` central and derived in the target, hence equal to `z`.

Source: Janko–Thompson (1970), §4, case (c), printed p.392, the core-fusion
exclusion following saturation of the nonabelian fixed-eight centralizer.
-/

open Subgroup
open scoped commutatorElement

namespace Sylow

/-- A fixed subgroup with the specified derived element and double centralizer
forces fusion into the central involution centralizer. -/
public theorem exists_local_conjugator_of_saturated_derived_center
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (z x y : S) (hz : orderOf z = 2) (hy : orderOf y = 2)
    (hzc : z ∈ center S) (hxz : x ≠ z)
    (hline : let E := (centralizer ({x} : Set S)).map (S : Subgroup G).subtype
      (_root_.commutator E ⊓ center E).map E.subtype = zpowers (z : G))
    (hmax : ∀ V : Subgroup G, IsPGroup 2 V →
      (centralizer ({x} : Set S)).map (S : Subgroup G).subtype ≤ V →
      V ≤ centralizer ({(x : G)} : Set G) →
      V = (centralizer ({x} : Set S)).map (S : Subgroup G).subtype)
    (hlocal : ∀ V : Subgroup G, IsPGroup 2 V →
      (centralizer ({y} : Set S)).map (S : Subgroup G).subtype ≤ V →
      V ≤ centralizer ({(z : G)} : Set G) →
      V ≤ centralizer ({(y : G)} : Set G) →
      V = (centralizer ({y} : Set S)).map (S : Subgroup G).subtype)
    (D : Subgroup S) (hDy : D ≤ centralizer ({y} : Set S))
    (hzD : z ∈ ⁅D, D⁆)
    (hDC : centralizer (D : Set S) ≤ closure ({z, y} : Set S))
    (hconj : IsConj (y : G) (x : G)) :
    ∃ g ∈ centralizer ({(z : G)} : Set G), (MulAut.conj g) (y : G) = x := by
  classical
  let E := (centralizer ({x} : Set S)).map (S : Subgroup G).subtype
  let R := (centralizer ({y} : Set S)).map (S : Subgroup G).subtype
  have hEx : E ≤ centralizer ({(x : G)} : Set G) := by
    dsimp only [E]
    rw [map_subtype_centralizer_singleton]
    exact inf_le_right
  have hRy : R ≤ centralizer ({(y : G)} : Set G) := by
    dsimp only [R]
    rw [map_subtype_centralizer_singleton]
    exact inf_le_right
  have hEp : IsPGroup 2 E := (S.isPGroup'.to_subgroup _).map _
  obtain ⟨g, hgy, hgR⟩ := exists_conj_into_saturated_centralizer
    (x : G) (y : G) E R hEp ((S.isPGroup'.to_subgroup _).map _) hEx hRy hmax hconj
  let f := MulAut.conj g
  have hfy : f (y : G) = x := hgy
  have hfR : ∀ r ∈ R, f r ∈ E := fun r hr => hgR (mem_map_of_mem _ hr)
  have hzE : (z : G) ∈ E := mem_map_of_mem _
    (mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hzc x).symm)
  have hzR : (z : G) ∈ R := mem_map_of_mem _
    (mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hzc y).symm)
  have hzcentral : ∀ e ∈ E, e * (z : G) = (z : G) * e := by
    rintro e ⟨s, _, rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp hzc s)
  let v : G := f.symm (z : G)
  have hfv : f v = z := f.apply_symm_apply _
  have hvcomm : ∀ r ∈ R, r * v = v * r := by
    intro r hr
    apply f.injective
    simpa only [map_mul, hfv] using hzcentral (f r) (hfR r hr)
  let F := E.comap f.toMonoidHom
  let V := F ⊓ centralizer ({(z : G)} : Set G)
  have hVR : V = R := hlocal V (hEp.comap_of_injective _ f.injective).to_inf_left
    (le_inf (fun r hr => hfR r hr) (by
      rintro r ⟨s, _, rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_center_iff.mp hzc s)))) inf_le_right (by
      intro r hr
      apply mem_centralizer_singleton_iff.mpr
      apply f.injective
      have hh : f r * (x : G) = (x : G) * f r := mem_centralizer_singleton_iff.mp (hEx hr.1)
      simpa only [map_mul, hfy] using hh)
  have hvR : v ∈ R := by
    rw [← hVR]
    exact ⟨by change f v ∈ E; rw [hfv]; exact hzE,
      mem_centralizer_singleton_iff.mpr (hvcomm z hzR).symm⟩
  obtain ⟨s, hs, hsv⟩ := hvR
  change (s : G) = v at hsv
  have hsD : s ∈ centralizer (D : Set S) := by
    intro d hd
    apply Subtype.ext
    change (d : G) * (s : G) = (s : G) * (d : G)
    rw [hsv]
    exact hvcomm d (mem_map_of_mem _ (hDy hd))
  have hzs : z * z = 1 := by simpa only [pow_two, hz] using pow_orderOf_eq_one z
  have hys : y * y = 1 := by simpa only [pow_two, hy] using pow_orderOf_eq_one y
  have hzy : Commute z y := (mem_center_iff.mp hzc y).symm
  have hfzcentral : ∀ e ∈ E, e * f (z : G) = f (z : G) * e := by
    rcases (mem_closure_pair_iff z y hzs hys hzy s).mp (hDC hsD) with h1 | hsz | hsy | hszy
    · have hv1 : v = 1 := hsv.symm.trans (congrArg Subtype.val h1)
      have hz1 : z = 1 := Subtype.ext (by simpa only [hv1, map_one, OneMemClass.coe_one] using hfv.symm)
      simp [hz1] at hz
    · have hvz : v = z := hsv.symm.trans (congrArg Subtype.val hsz)
      rw [hvz] at hfv
      simpa only [hfv] using hzcentral
    · have hvy : v = y := hsv.symm.trans (congrArg Subtype.val hsy)
      rw [hvy, hfy] at hfv
      exact (hxz (Subtype.ext hfv)).elim
    · have hvzy : v = (z : G) * (y : G) := hsv.symm.trans (congrArg Subtype.val hszy)
      have hfz : f (z : G) = (z : G) * (x : G)⁻¹ := by
        apply eq_mul_inv_iff_mul_eq.mpr
        simpa only [hvzy, map_mul, hfy] using hfv
      intro e he
      rw [hfz]
      exact ((show Commute e (z : G) from hzcentral e he).mul_right
        (show Commute e (x : G) from mem_centralizer_singleton_iff.mp (hEx he)).inv_right).eq
  have hfD : D.map (f.toMonoidHom.comp (S : Subgroup G).subtype) ≤ E := by
    rintro _ ⟨d, hd, rfl⟩
    exact hfR d (mem_map_of_mem _ (hDy hd))
  have hfzder : f (z : G) ∈ ⁅E, E⁆ := by
    have hm := mem_map_of_mem (f.toMonoidHom.comp (S : Subgroup G).subtype) hzD
    rw [map_commutator] at hm
    exact commutator_mono hfD hfD hm
  have hfzline : f (z : G) ∈ zpowers (z : G) := by
    rw [← map_subtype_commutator] at hfzder
    obtain ⟨a, ha, hea⟩ := hfzder
    change (a : G) = f (z : G) at hea
    rw [← hline]
    refine ⟨a, ⟨ha, mem_center_iff.mpr ?_⟩, hea⟩
    intro b
    apply Subtype.ext
    change (b : G) * (a : G) = (a : G) * (b : G)
    rw [hea]
    exact hfzcentral b b.property
  have hfzne : f (z : G) ≠ 1 := by
    intro he
    have hz1 : z = 1 := Subtype.ext (f.injective (he.trans (map_one f).symm))
    simp [hz1] at hz
  have hfz : f (z : G) = z := by
    rw [mem_zpowers_iff_mem_range_orderOf, orderOf_coe, hz] at hfzline
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hfzline
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · exact (hfzne (by simpa using he.symm)).elim
    · simpa using he.symm
  exact ⟨g, mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfz), hgy⟩

end Sylow
