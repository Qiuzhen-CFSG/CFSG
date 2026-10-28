module

public import Theory.GroupTheory.PerfectCentralCover
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Schreier

/-!
# Existence of universal perfect central covers

For a perfect group `G`, take the free group `F` on its underlying type, with
relation subgroup `R`, and form `E = F / [F,R]`. The derived subgroup of `E`
is perfect and maps centrally onto `G`. It lifts uniquely to every central
extension of `G`; when `G` is finite, Schur's theorem makes this cover finite.

The central-extension arguments are adapted from
`Theory.Alternating.proposition_5_2_4` (A1 33.3--33.9) and the free-central
construction in `Theory.Alternating.theorem_5_2_1_2` (Suzuki 9.2).
-/

namespace PerfectCentralCovering

open scoped commutatorElement

private theorem commutatorElement_mul_center
    {E : Type*} [Group E] (kx ky dx dy : E)
    (hkx : kx ∈ Subgroup.center E) (hky : ky ∈ Subgroup.center E) :
    ⁅kx * dx, ky * dy⁆ = ⁅dx, dy⁆ := by
  have hkxComm (z : E) : Commute kx z := by
    change kx * z = z * kx
    exact (Subgroup.mem_center_iff.mp hkx z).symm
  have hkyComm (z : E) : Commute ky z := by
    change ky * z = z * ky
    exact (Subgroup.mem_center_iff.mp hky z).symm
  calc
    ⁅kx * dx, ky * dy⁆ =
        kx * ⁅dx, ky * dy⁆ * kx⁻¹ * ⁅kx, ky * dy⁆ :=
      commutatorElement_mul_left_eq_conj_mul kx dx (ky * dy)
    _ = ⁅dx, ky * dy⁆ := by
      rw [(hkxComm (ky * dy)).commutator_eq]
      simp [(hkxComm ⁅dx, ky * dy⁆).eq, mul_assoc]
    _ = ⁅dx, ky⁆ * ky * ⁅dx, dy⁆ * ky⁻¹ :=
      commutatorElement_mul_right_eq_mul_conj dx ky dy
    _ = ⁅dx, dy⁆ := by
      rw [(hkyComm dx).symm.commutator_eq]
      simp [(hkyComm ⁅dx, dy⁆).eq, mul_assoc]

/-- A1 33.3: the derived subgroup of a central extension of a perfect group
is itself perfect. -/
public theorem commutator_isPerfect_of_surjective_of_ker_le_center
    {E B : Type*} [Group E] [Group B] [Group.IsPerfect B]
    (f : E →* B) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) :
    Group.IsPerfect (commutator E) := by
  let D := commutator E
  have hmap : D.map f = ⊤ := by
    dsimp [D]
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    exact Group.IsPerfect.commutator_eq_top
  have hdecomp (x : E) :
      ∃ k ∈ f.ker, ∃ d ∈ D, x = k * d := by
    have hx : f x ∈ D.map f := by
      rw [hmap]
      trivial
    obtain ⟨d, hd, hdx⟩ := hx
    refine ⟨x * d⁻¹, ?_, d, hd, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, hdx]
      simp
    · simp
  change Group.IsPerfect D
  rw [Subgroup.isPerfect_iff]
  apply le_antisymm
  · exact Subgroup.commutator_le_left D D
  · dsimp [D]
    rw [commutator_eq_closure, Subgroup.closure_le]
    intro z hz
    obtain ⟨x, y, hxy⟩ := mem_commutatorSet_iff.mp hz
    obtain ⟨kx, hkx, dx, hdx, rfl⟩ := hdecomp x
    obtain ⟨ky, hky, dy, hdy, rfl⟩ := hdecomp y
    have hdx' : dx ∈ commutator E := by simpa [D] using hdx
    have hdy' : dy ∈ commutator E := by simpa [D] using hdy
    have hdx'' : dx ∈ Subgroup.closure (commutatorSet E) := by
      rw [← commutator_eq_closure]
      exact hdx'
    have hdy'' : dy ∈ Subgroup.closure (commutatorSet E) := by
      rw [← commutator_eq_closure]
      exact hdy'
    rw [← hxy, commutatorElement_mul_center kx ky dx dy (hker hkx) (hker hky)]
    exact Subgroup.commutator_mem_commutator hdx'' hdy''

/-- A1 33.9 in the form needed here: if a group has a finite central
quotient, then its derived subgroup is finite. -/
public theorem finite_commutator_of_surjective_of_ker_le_center
    {E B : Type*} [Group E] [Group B] [Finite B]
    (f : E →* B) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) :
    Finite (commutator E) := by
  let s : B → E := fun b => Classical.choose (hf b)
  have hs (b : B) : f (s b) = b := Classical.choose_spec (hf b)
  let φ : B × B → commutatorSet E := fun p =>
    ⟨⁅s p.1, s p.2⁆,
      commutator_mem_commutatorSet (s p.1) (s p.2)⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨z, hz⟩
    obtain ⟨x, y, hxy⟩ := mem_commutatorSet_iff.mp hz
    let kx := x * (s (f x))⁻¹
    let ky := y * (s (f y))⁻¹
    have hkx : kx ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      change f (x * (s (f x))⁻¹) = 1
      rw [map_mul, map_inv, hs]
      simp
    have hky : ky ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      change f (y * (s (f y))⁻¹) = 1
      rw [map_mul, map_inv, hs]
      simp
    have hx : x = kx * s (f x) := by simp [kx]
    have hy : y = ky * s (f y) := by simp [ky]
    refine ⟨(f x, f y), ?_⟩
    apply Subtype.ext
    change ⁅s (f x), s (f y)⁆ = z
    rw [← hxy]
    calc
      ⁅s (f x), s (f y)⁆ =
          ⁅kx * s (f x), ky * s (f y)⁆ :=
        (commutatorElement_mul_center kx ky (s (f x)) (s (f y))
          (hker hkx) (hker hky)).symm
      _ = ⁅x, y⁆ := by rw [← hx, ← hy]
  let : Finite (commutatorSet E) := Finite.of_surjective φ hφ
  infer_instance

/-- A1 33.4 uniqueness core: two maps from a perfect group to a central
extension that agree after projection are equal. -/
public theorem monoidHom_eq_of_isPerfect_of_comp_eq
    {L M B : Type*} [Group L] [Group.IsPerfect L] [Group M] [Group B]
    (g : M →* B) (hker : g.ker ≤ Subgroup.center M)
    (h₁ h₂ : L →* M) (hfac : g.comp h₁ = g.comp h₂) :
    h₁ = h₂ := by
  apply MonoidHom.eq_of_eqOn_dense
    (s := commutatorSet L)
  · rw [← commutator_eq_closure]
    exact Group.IsPerfect.commutator_eq_top
  · intro z hz
    obtain ⟨x, y, rfl⟩ := mem_commutatorSet_iff.mp hz
    have hfacx := congrArg (fun f : L →* B => f x) hfac
    have hfacy := congrArg (fun f : L →* B => f y) hfac
    let kx := h₁ x * (h₂ x)⁻¹
    let ky := h₁ y * (h₂ y)⁻¹
    have hkx : kx ∈ g.ker := by
      rw [MonoidHom.mem_ker]
      change g (h₁ x * (h₂ x)⁻¹) = 1
      rw [map_mul, map_inv]
      change g (h₁ x) * (g (h₂ x))⁻¹ = 1
      change g (h₁ x) = g (h₂ x) at hfacx
      rw [hfacx]
      simp
    have hky : ky ∈ g.ker := by
      rw [MonoidHom.mem_ker]
      change g (h₁ y * (h₂ y)⁻¹) = 1
      rw [map_mul, map_inv]
      change g (h₁ y) * (g (h₂ y))⁻¹ = 1
      change g (h₁ y) = g (h₂ y) at hfacy
      rw [hfacy]
      simp
    have hx : h₁ x = kx * h₂ x := by simp [kx]
    have hy : h₁ y = ky * h₂ y := by simp [ky]
    simp only [map_commutatorElement]
    rw [hx, hy, commutatorElement_mul_center kx ky (h₂ x) (h₂ y)
      (hker hkx) (hker hky)]

/-- A1 33.6: a morphism onto a perfect central extension is surjective. -/
public theorem surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    {L M B : Type*} [Group L] [Group M] [Group.IsPerfect M] [Group B]
    (g : M →* B) (h : L →* M)
    (hcomp : Function.Surjective (g.comp h))
    (hker : g.ker ≤ Subgroup.center M) :
    Function.Surjective h := by
  have hdecomp (x : M) :
      ∃ k ∈ g.ker, ∃ l : L, x = k * h l := by
    obtain ⟨l, hl⟩ := hcomp (g x)
    refine ⟨x * (h l)⁻¹, ?_, l, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv]
      change g x * (g (h l))⁻¹ = 1
      change g (h l) = g x at hl
      rw [hl]
      simp
    · simp
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← Group.IsPerfect.commutator_eq_top,
    commutator_eq_closure, Subgroup.closure_le]
  intro z hz
  obtain ⟨x, y, hxy⟩ := mem_commutatorSet_iff.mp hz
  obtain ⟨kx, hkx, lx, hx⟩ := hdecomp x
  obtain ⟨ky, hky, ly, hy⟩ := hdecomp y
  rw [← hxy, hx, hy,
    commutatorElement_mul_center kx ky (h lx) (h ly)
      (hker hkx) (hker hky), ← map_commutatorElement]
  exact ⟨⁅lx, ly⁆, rfl⟩

public section

universe u v

variable (G : Type u) [Group G]

/-- Evaluation of the free group on the underlying set of `G`. -/
@[expose] def freeEvaluation : FreeGroup G →* G := FreeGroup.lift id

theorem freeEvaluation_surjective : Function.Surjective (freeEvaluation G) := by
  intro g
  exact ⟨FreeGroup.of g, FreeGroup.lift_apply_of⟩

/-- Relations imposing centrality on the kernel of free evaluation. -/
@[expose] def centralRelations : Subgroup (FreeGroup G) :=
  ⁅(⊤ : Subgroup (FreeGroup G)), (freeEvaluation G).ker⁆

instance centralRelations_normal : (centralRelations G).Normal := by
  unfold centralRelations
  infer_instance

/-- The free central extension associated to the tautological presentation. -/
abbrev FreeCentralGroup := FreeGroup G ⧸ centralRelations G

/-- Projection from the free central extension. -/
@[expose] def freeCentralProjection : FreeCentralGroup G →* G :=
  QuotientGroup.lift (centralRelations G) (freeEvaluation G)
    (Subgroup.commutator_le_right _ _)

@[simp] theorem freeCentralProjection_mk (x : FreeGroup G) :
    freeCentralProjection G (QuotientGroup.mk' (centralRelations G) x) =
      freeEvaluation G x := rfl

theorem freeCentralProjection_surjective :
    Function.Surjective (freeCentralProjection G) := by
  intro g
  obtain ⟨x, hx⟩ := freeEvaluation_surjective G g
  exact ⟨QuotientGroup.mk' (centralRelations G) x, hx⟩

theorem freeCentralProjection_ker_le_center :
    (freeCentralProjection G).ker ≤ Subgroup.center (FreeCentralGroup G) := by
  intro x hx
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (centralRelations G) x
  have hxR : x ∈ (freeEvaluation G).ker := hx
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (centralRelations G) y
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← map_commutatorElement]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top y) hxR

/-- The universal perfect central covering group. -/
abbrev UniversalGroup := commutator (FreeCentralGroup G)

instance universalGroup_isPerfect [Group.IsPerfect G] : Group.IsPerfect (UniversalGroup G) :=
  commutator_isPerfect_of_surjective_of_ker_le_center
    (freeCentralProjection G) (freeCentralProjection_surjective G)
    (freeCentralProjection_ker_le_center G)

instance universalGroup_finite [Finite G] : Finite (UniversalGroup G) :=
  finite_commutator_of_surjective_of_ker_le_center
    (freeCentralProjection G) (freeCentralProjection_surjective G)
    (freeCentralProjection_ker_le_center G)

/-- Restriction of the free central projection to the derived subgroup. -/
@[expose] def universalProjection : UniversalGroup G →* G :=
  (freeCentralProjection G).comp (commutator (FreeCentralGroup G)).subtype

theorem universalProjection_surjective [Group.IsPerfect G] :
    Function.Surjective (universalProjection G) := by
  have hmap : (commutator (FreeCentralGroup G)).map (freeCentralProjection G) = ⊤ := by
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.mpr (freeCentralProjection_surjective G)]
    exact Group.IsPerfect.commutator_eq_top
  intro y
  have hy : y ∈ (commutator (FreeCentralGroup G)).map (freeCentralProjection G) := by
    rw [hmap]
    trivial
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, hxy⟩

theorem universalProjection_ker_le_center :
    (universalProjection G).ker ≤ Subgroup.center (UniversalGroup G) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (freeCentralProjection_ker_le_center G hx) y

/-- A concrete universal perfect central cover. -/
@[expose] def universalCover [Group.IsPerfect G] : Cover (UniversalGroup G) G where
  toMonoidHom := universalProjection G
  surjective := universalProjection_surjective G
  isPerfect := inferInstance
  ker_le_center := universalProjection_ker_le_center G

variable {G} {M : Type v} [Group M]

/-- The free central extension lifts through every central extension. -/
theorem freeCentralProjection_exists_lift (g : M →* G)
    (hg : Function.Surjective g) (hker : g.ker ≤ Subgroup.center M) :
    ∃ h : FreeCentralGroup G →* M, g.comp h = freeCentralProjection G := by
  let s : G → M := fun x => Classical.choose (hg x)
  have hs (x : G) : g (s x) = x := Classical.choose_spec (hg x)
  let t : FreeGroup G →* M := FreeGroup.lift s
  have ht : g.comp t = freeEvaluation G := by
    ext x
    simpa [t, freeEvaluation] using hs x
  have hkill : centralRelations G ≤ t.ker := by
    rw [centralRelations, Subgroup.commutator_le]
    intro x _ r hr
    rw [MonoidHom.mem_ker, map_commutatorElement]
    apply commutatorElement_eq_one_iff_commute.mpr
    have htr : t r ∈ g.ker := by
      rw [MonoidHom.mem_ker]
      exact (DFunLike.congr_fun ht r).trans hr
    exact Subgroup.mem_center_iff.mp (hker htr) (t x)
  let h : FreeCentralGroup G →* M := QuotientGroup.lift (centralRelations G) t hkill
  refine ⟨h, ?_⟩
  apply MonoidHom.ext
  intro x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (centralRelations G) x
  exact DFunLike.congr_fun ht x

/-- Strong universality: neither finiteness nor perfectness of the target
central extension is required, and its universe is arbitrary. -/
theorem universalProjection_existsUnique_lift [Group.IsPerfect G]
    (g : M →* G) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center M) :
    ∃! h : UniversalGroup G →* M, g.comp h = universalProjection G := by
  obtain ⟨h, hh⟩ := freeCentralProjection_exists_lift g hg hker
  refine ⟨h.comp (commutator (FreeCentralGroup G)).subtype, ?_, ?_⟩
  · change g.comp (h.comp _) = _
    rw [← MonoidHom.comp_assoc, hh]
    rfl
  · intro k hk
    apply monoidHom_eq_of_isPerfect_of_comp_eq g hker
    rw [hk, ← MonoidHom.comp_assoc, hh]
    rfl

/-- The concrete cover is universal in every target universe. -/
theorem universalCover_isUniversal [Finite G] [Group.IsPerfect G] :
    IsUniversal.{u, u, v} (universalCover G) := by
  intro M _ _ g
  exact universalProjection_existsUnique_lift g.toMonoidHom g.surjective g.ker_le_center

end
end PerfectCentralCovering
