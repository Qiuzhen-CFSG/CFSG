module
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.Setup
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.SylowImageIntersection

/-!
# The actual inner subgroup in the Sylow upgrade

The defining omega containment of Delta-zero transfers to every chosen
relative Sylow by conjugacy inside the relative normalizer. Sylow
intersections distribute over products of normal subgroups; applying this
inside the actual normalizer of `L` gives `R₀ ≤ T_C L`. The two-cover
center is a normal two-subgroup of that normalizer and hence lies in `T_C`.
Together these construct the projection configuration without extra
coordinate or chosen-Sylow premises.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 16.4.10, printed pp.1192–1193. The two-group property of the cover
center remains the precise earlier model input.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- Sylow conjugacy retains the actual ambient embeddings. -/
theorem SylowIn.exists_conjugate {P Q H : Subgroup G}
    (hP : SylowIn P H) (hQ : SylowIn Q H) :
    ∃ a : G, a ∈ H ∧ P.conjBy a = Q := by
  obtain ⟨P₀, rfl⟩ := hP
  obtain ⟨Q₀, rfl⟩ := hQ
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq H P₀ Q₀
  refine ⟨a, a.property, ?_⟩
  change ((P₀ : Subgroup H).map H.subtype).map (MulAut.conj (a : G)).toMonoidHom =
    ((P₀ : Subgroup H).map (MulAut.conj a).toMonoidHom).map H.subtype
  rw [map_map, map_map]
  congr 1

/-- A normalized omega containment is independent of the chosen relative Sylow. -/
theorem SylowIn.omega_le_of_conjugate {P Q H D : Subgroup G}
    (hP : SylowIn P H) (hQ : SylowIn Q H)
    (hD : H ≤ normalizer (D : Set G)) (hPomega : omegaOneAmbient P ≤ D) :
    omegaOneAmbient Q ≤ D := by
  obtain ⟨a, ha, rfl⟩ := hP.exists_conjugate hQ
  apply (omegaOneAmbient_le_iff _ _).mpr
  rintro x ⟨y, hy, rfl⟩ hx2
  have hy2 : y ^ 2 = 1 := (MulAut.conj a).injective (by simpa using hx2)
  have hyD := (omegaOneAmbient_le_iff _ _).mp hPomega y hy hy2
  exact (mem_normalizer_iff.mp (hD ha) y).mp hyD

variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

/-- Delta-zero supplies omega containment for the Sylow actually chosen in the setup. -/
theorem IntersectionSetup.omega_le_of_mem_deltaZero
    (h : IntersectionSetup T z L g R)
    (hd : (centralizer (L : Set G)).conjBy g ∈ deltaZero L) :
    omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L := by
  obtain ⟨_, P, hP, hPO⟩ := hd
  apply hP.omega_le_of_conjugate h.sylow _ hPO
  apply le_trans inf_le_right
  apply le_normalizer_iff.mpr
  intro a ha x hx
  have haL : a ∈ normalizer (L : Set G) := h.normalizers_eq ▸ ha
  have hnK := mem_normalizer_iff_map_conj_eq.mp ha
  have hnL := mem_normalizer_iff_map_conj_eq.mp haL
  have hn : (centralizer (L : Set G) ⊔ L).conjBy a = centralizer (L : Set G) ⊔ L := by
    change (centralizer (L : Set G) ⊔ L).map (MulAut.conj a).toMonoidHom = _
    rw [Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) hnK hnL
  exact hn ▸ (mem_map_of_mem (MulAut.conj a).toMonoidHom hx)

namespace SylowSymmetry.NormalFour

/-- Sylow intersections distribute over a product of normal subgroups. -/
theorem inf_sup_normal (P : Sylow 2 G) (K D : Subgroup G) [K.Normal] [D.Normal] :
    (P : Subgroup G) ⊓ (K ⊔ D) =
      ((P : Subgroup G) ⊓ K) ⊔ ((P : Subgroup G) ⊓ D) := by
  obtain ⟨Q, hQ⟩ := P.exists_sylow_map_eq_inf_of_normal K
  let q := QuotientGroup.mk' D
  have hmap := P.map_image_eq_inf K ((P : Subgroup G) ⊓ K) Q hQ inf_le_left q
  apply le_antisymm
  · intro x hx
    have himg : q x ∈ K.map q := by
      have hm := mem_map_of_mem q hx.2
      simpa only [q, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] using hm
    have hximg : q x ∈ ((P : Subgroup G) ⊓ K).map q := by
      rw [hmap]
      exact ⟨mem_map_of_mem q hx.1, himg⟩
    obtain ⟨k, hk, he⟩ := hximg
    have hd : k⁻¹ * x ∈ D := by
      apply (QuotientGroup.eq_one_iff (k⁻¹ * x)).mp
      change q (k⁻¹ * x) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    have heq : x = k * (k⁻¹ * x) := (mul_inv_cancel_left k x).symm
    rw [heq]
    exact mul_mem_sup hk ⟨(P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem hk.1) hx.1, hd⟩
  · exact sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)

end SylowSymmetry.NormalFour

/-- The actual inner part has multiplication coordinates in `T_C L`. -/
theorem IntersectionSetup.innerPart_le_factors (h : IntersectionSetup T z L g R) :
    innerPart L R ≤ commutingSylow T L ⊔ L := by
  let H := normalizer (L : Set G)
  let K := centralizer (L : Set G)
  let P := T.subtype h.sylow_normalizes
  let K₀ := K.subgroupOf H
  let L₀ := L.subgroupOf H
  have hKH : K ≤ H := centralizer_le_normalizer _
  have hLH : L ≤ H := L.le_normalizer
  let : K₀.Normal := normal_subgroupOf_centralizer_normalizer (L : Set G)
  let : L₀.Normal := normal_in_normalizer
  have he := SylowSymmetry.NormalFour.inf_sup_normal P K₀ L₀
  intro r hr
  have hrH : r ∈ H := h.sylow_normalizes (h.le_sylow hr.1)
  have hr₀ : (⟨r, hrH⟩ : H) ∈ (P : Subgroup H) ⊓ (K₀ ⊔ L₀) := by
    refine ⟨h.le_sylow hr.1, ?_⟩
    rw [← subgroupOf_sup hKH hLH]
    exact hr.2
  rw [he] at hr₀
  have hm := mem_map_of_mem H.subtype hr₀
  rw [Subgroup.map_sup] at hm
  have hkmap : ((P : Subgroup H) ⊓ K₀).map H.subtype ≤ commutingSylow T L := by
    rintro x ⟨a, ha, rfl⟩
    exact ⟨ha.1, ha.2⟩
  have hlmap : ((P : Subgroup H) ⊓ L₀).map H.subtype ≤ L := by
    rintro x ⟨a, ha, rfl⟩
    exact ha.2
  exact sup_le_sup hkmap hlmap hm

/-- The two-cover center lies in `T_C`; normality here is inside `N_G(L)`. -/
theorem StandardSetup.center_le_commutingSylow (h : StandardSetup T z L)
    (hZ : IsPGroup 2 ↥(L ⊓ centralizer (L : Set G))) :
    L ⊓ centralizer (L : Set G) ≤ commutingSylow T L := by
  let H := normalizer (L : Set G)
  let Z := L ⊓ centralizer (L : Set G)
  have hZH : Z ≤ H := inf_le_left.trans L.le_normalizer
  let : (Z.subgroupOf H).Normal := by
    change ((L ⊓ centralizer (L : Set G)).subgroupOf H).Normal
    change ((L.subgroupOf H) ⊓ ((centralizer (L : Set G)).subgroupOf H)).Normal
    infer_instance
  have hz := (hZ.of_equiv (subgroupOfEquivOfLe hZH).symm).le_sylow_of_normal
    (T.subtype h.sylow_normalizes)
  exact fun x hx => ⟨hz (show (⟨x, hZH hx⟩ : H) ∈ Z.subgroupOf H from hx), hx.2⟩

/-- The genuine configuration, with coordinates and chosen-Sylow omega containment discharged. -/
theorem IntersectionSetup.projection_configuration_of_deltaZero
    (h : IntersectionSetup T z L g R)
    (hd : (centralizer (L : Set G)).conjBy g ∈ deltaZero L)
    (hn : commutingSylow T L ⊓ normalizer ((centralizer (L : Set G)).conjBy g : Set G) =
      commutingSylow T L ⊓ centralizer (R : Set G))
    (hp : commutingSylow T L ⊓ centralizer (R : Set G) < commutingSylow T L)
    (hZ : IsPGroup 2 ↥(L ⊓ centralizer (L : Set G))) :
    SylowSymmetry.ProjectionConfiguration (commutingSylow T L) L (innerPart L R)
      (commutingSylow T L ⊓ centralizer (R : Set G)) :=
  h.projection_configuration hn hp (h.omega_le_of_mem_deltaZero hd)
    h.innerPart_le_factors (h.toStandardSetup.center_le_commutingSylow hZ)

end CFSG.Quasithin.Chapter16.Intersections
