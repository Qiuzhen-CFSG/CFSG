module
public import CFSG.Quasithin.ChapterG.Section10.Components.Homogeneous
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.Geometry

/-!
# Centralizer displacements in the marked homogeneous G.10 branch

Restrict a centralizing actor's displacement to a simple constituent. Its
nonzero image is simple. The marked hyperplane puts all but at most one
image dimension in W; G.10.12 excludes an image avoiding the marked point.
Thus all images equal the marked constituent, and homogeneity exhausts V.
Faithfulness gives equality for each nonidentity actor. The invariant
alternating form identifies its kernel as the orthogonal complement.

These are the literal linear maps needed for the multiplicity-space rank
argument following Aschbacher--Smith G.11.7, printed pp.368--369. The proof
uses G.10.12, printed p.360, and does not assume a counterexample to G.11.2.
The original A₆ consumer is SmallRows.AlternatingSixActionSourceMultiplicityDisplacement.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem irrPlus_of_simple_of_fixed_eq_bot (H : Subgroup G)
    (hfix : fixedSpace ρ H = ⊥) (J : Subrepresentation (ρ.comp H.subtype))
    (hj : IsIrreducible J.toRepresentation) : IsIrrPlus ρ H J.toSubmodule := by
  have ha := (Subrepresentation.irreducible_iff_isAtom J).mp hj
  have hs : H ≤ subspaceStabilizer ρ J.toSubmodule :=
    le_subspaceStabilizer ρ _ (fun a ha u hu => J.apply_mem_toSubmodule ⟨a,ha⟩ hu)
  have hn : ¬ J.toSubmodule ≤ fixedSpace ρ H := by
    rw [hfix]
    exact fun he => ha.ne_bot (Subrepresentation.toSubmodule_injective (le_bot_iff.mp he))
  have hcs := subspaceCommutator_invariant_normalizer ρ hs H.le_normalizer
  let C : Subrepresentation (ρ.comp H.subtype) :=
    ⟨subspaceCommutator ρ J.toSubmodule H, fun a u hu => (hcs a.property u).2 hu⟩
  have hCJ : C ≤ J := subspaceCommutator_le_of_invariant ρ hs
  have hC : C ≠ ⊥ := by
    intro he
    exact hn ((subspaceCommutator_eq_bot_iff ρ J.toSubmodule H).mp
      (congrArg Subrepresentation.toSubmodule he))
  apply isIrrPlus_of_minimal ρ hs
  · exact congrArg Subrepresentation.toSubmodule ((ha.le_iff_eq hC).mp hCJ)
  · exact hn
  · intro U hU hUJ
    let Q : Subrepresentation (ρ.comp H.subtype) := ⟨U, fun a u hu => (hU a.property u).2 hu⟩
    by_cases hQ : Q = ⊥
    · right
      rw [show U = ⊥ from congrArg Subrepresentation.toSubmodule hQ]
      exact bot_le
    · exact Or.inl (congrArg Subrepresentation.toSubmodule ((ha.le_iff_eq hQ).mp hUJ))

include h

private theorem simple_displacement_image_le (hi : ρ.IsIrreducible)
    (H : Subgroup G) [H.Normal] (hfix : fixedSpace ρ H = ⊥)
    (I J : Subrepresentation (ρ.comp H.subtype))
    (hI : IsIrreducible I.toRepresentation) (hJ : IsIrreducible J.toRepresentation)
    (hv : v ∈ I.toSubmodule) (hd : 3 ≤ finrank (ZMod 2) J.toSubmodule)
    (c : X) (hc : (c : G) ∈ centralizer (H : Set G)) :
    ∀ u ∈ J.toSubmodule, ρ c u - u ∈ I.toSubmodule := by
  let d : IntertwiningMap J.toRepresentation (ρ.comp H.subtype) := {
    toLinearMap := (ρ c - LinearMap.id).comp J.toSubmodule.subtype
    isIntertwining' a := by
      ext u
      change ρ c (ρ (a : G) u.val) - ρ (a : G) u.val =
        ρ (a : G) (ρ c u.val - u.val)
      rw [map_sub, ← Module.End.mul_apply, ← map_mul,
        ← mem_centralizer_iff.mp hc a a.property, map_mul, Module.End.mul_apply] }
  let := hJ
  rcases IsIrreducible.injective_or_eq_zero d with hinj | hz
  · let q : IntertwiningMap J.toRepresentation d.range.toRepresentation := {
      toLinearMap := d.toLinearMap.rangeRestrict
      isIntertwining' a := by
        ext u
        exact LinearMap.congr_fun (d.isIntertwining' a) u }
    have hq : Function.Bijective q :=
      ⟨fun x y he => hinj (congrArg Subtype.val he), d.toLinearMap.surjective_rangeRestrict⟩
    have hr : IsIrreducible d.range.toRepresentation :=
      (RepEquiv.irreducible_euqiv (RepEquiv.ofRepresentationEquiv (q.ofBijective hq))).mp hJ
    have hvir : v ∈ d.range.toSubmodule := by
      by_contra hvd
      have hb := h.constituent_inter_W_finrank_le_one hi H
        (irrPlus_of_simple_of_fixed_eq_bot H hfix d.range hr) hvd
      let p : J.toSubmodule →ₗ[ZMod 2] ZMod 2 := (B v).comp J.toSubmodule.subtype
      let f := d.toLinearMap.comp p.ker.subtype
      have hf : Function.Injective f := hinj.comp Subtype.val_injective
      have hle : f.range ≤ d.range.toSubmodule ⊓ W := by
        rintro _ ⟨u,rfl⟩
        exact ⟨⟨u.val,rfl⟩,h.displacement c u.val.val u.property⟩
      have he := p.finrank_range_add_finrank_ker
      have hp : finrank (ZMod 2) p.range ≤ 1 := by simpa using p.range.finrank_le
      have hm := Submodule.finrank_mono hle
      rw [LinearMap.finrank_range_of_inj hf] at hm
      omega
    have he : d.range = I := by
      by_contra hne
      have hdis := ((Subrepresentation.irreducible_iff_isAtom _).mp hr).disjoint_of_ne
        ((Subrepresentation.irreducible_iff_isAtom _).mp hI) hne
      exact h.point_ne_zero (show v ∈ (⊥ : Subrepresentation (ρ.comp H.subtype)) from
        hdis.eq_bot ▸ ⟨hvir,hv⟩)
    intro u hu
    exact (congrArg Subrepresentation.toSubmodule he) ▸
      (show d ⟨u,hu⟩ ∈ d.range.toSubmodule from ⟨⟨u,hu⟩,rfl⟩)
  · intro u hu
    have hz' : ρ c u - u = 0 := congrArg (fun f => (f : IntertwiningMap
      J.toRepresentation (ρ.comp H.subtype)) ⟨u,hu⟩) hz
    exact hz' ▸ I.toSubmodule.zero_mem

/-- A centralizing elementary actor has all of its displacement in the
marked homogeneous constituent. -/
theorem centralizer_displacement_le_marked_constituent
    (hi : ρ.IsIrreducible) (H : Subgroup G) [H.Normal]
    (hH : H ≠ ⊥) (I : Subrepresentation (ρ.comp H.subtype))
    (hI : IsIrreducible I.toRepresentation)
    (hh : Homogeneous.homogeneousPart I ⊤ = ⊤)
    (hv : v ∈ I.toSubmodule) (hd : 3 ≤ finrank (ZMod 2) I.toSubmodule)
    (c : X) (hc : (c : G) ∈ centralizer (H : Set G)) :
    LinearMap.range (ρ c - LinearMap.id) ≤ I.toSubmodule := by
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful hi H hH
  have hle : Homogeneous.homogeneousPart I ⊤ ≤ I.toSubmodule.comap (ρ c - LinearMap.id) := by
    refine iSup_le fun J => iSup_le fun hj => ?_
    have hdJ : finrank (ZMod 2) I.toSubmodule = finrank (ZMod 2) J.toSubmodule := hj.2.choose.finrank_eq
    exact h.simple_displacement_image_le hi H hfix I J hI (hj.2.irreducible hI)
      hv (by omega) c hc
  rw [hh] at hle
  rintro _ ⟨u,rfl⟩
  exact hle Submodule.mem_top


omit [FiniteDimensional (ZMod 2) V] in
/-- The original alternating form identifies the fixed space of an involution
with the orthogonal complement of its displacement space. -/
theorem displacement_ker_eq_orthogonal_range (c : X) :
    LinearMap.ker (ρ c - LinearMap.id) =
      B.orthogonal (LinearMap.range (ρ c - LinearMap.id)) := by
  have hc : (c : G) * c = 1 := by
    have hc2 : c ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 X) c
    have he := congrArg Subtype.val hc2
    simpa only [Subgroup.coe_pow,Subgroup.coe_one,pow_two,Subgroup.coe_mul] using he
  have hsq (u : V) : ρ c (ρ c u) = u := by
    rw [← Module.End.mul_apply,← map_mul,hc,map_one,Module.End.one_apply]
  have hb (u w : V) : B (ρ c u - u) w = B u (ρ c w - w) := by
    have hh := h.preserves c u (ρ c w)
    rw [hsq] at hh
    simp only [map_sub,LinearMap.sub_apply]
    rw [hh]
  ext w
  constructor
  · intro hw
    rintro _ ⟨u,rfl⟩
    change B (ρ c u - u) w = 0
    rw [hb,show ρ c w - w = 0 from hw,map_zero]
  · intro hw
    apply h.nondegenerate.2
    intro u
    change B u (ρ c w - w) = 0
    rw [← hb]
    exact hw _ ⟨u,rfl⟩

/-- Every nonidentity centralizing actor has exactly the same image and kernel.
No bound on its rank is assumed. -/
theorem centralizer_displacement_range_and_ker
    (hi : ρ.IsIrreducible) (H : Subgroup G) [H.Normal]
    (hH : H ≠ ⊥) (I : Subrepresentation (ρ.comp H.subtype))
    (hI : IsIrreducible I.toRepresentation)
    (hh : Homogeneous.homogeneousPart I ⊤ = ⊤)
    (hv : v ∈ I.toSubmodule) (hd : 3 ≤ finrank (ZMod 2) I.toSubmodule)
    (c : X) (hc : (c : G) ∈ centralizer (H : Set G)) (hc1 : c ≠ 1) :
    LinearMap.range (ρ c - LinearMap.id) = I.toSubmodule ∧
      LinearMap.ker (ρ c - LinearMap.id) = B.orthogonal I.toSubmodule := by
  let R : Subrepresentation (ρ.comp H.subtype) := {
    toSubmodule := LinearMap.range (ρ c - LinearMap.id)
    apply_mem_toSubmodule a u hu := by
      obtain ⟨w,rfl⟩ := hu
      refine ⟨ρ (a : G) w,?_⟩
      change ρ c (ρ (a : G) w) - ρ (a : G) w = ρ (a : G) (ρ c w - w)
      rw [map_sub,← Module.End.mul_apply,← map_mul,
        ← mem_centralizer_iff.mp hc a a.property,map_mul,Module.End.mul_apply] }
  have hR : R ≠ ⊥ := by
    intro he
    apply hc1
    apply Subtype.ext
    apply h.faithful
    rw [Subgroup.coe_one,map_one]
    apply LinearMap.ext
    intro u
    change ρ (c : G) u = u
    have hz : ρ (c : G) u - u ∈ R.toSubmodule := ⟨u,rfl⟩
    rw [he] at hz
    exact sub_eq_zero.mp hz
  have he : LinearMap.range (ρ c - LinearMap.id) = I.toSubmodule :=
    congrArg Subrepresentation.toSubmodule
      (((Subrepresentation.irreducible_iff_isAtom I).mp hI).le_iff_eq hR |>.mp
        (h.centralizer_displacement_le_marked_constituent hi H hH I hI hh hv hd c hc))
  exact ⟨he,(h.displacement_ker_eq_orthogonal_range c).trans (congrArg B.orthogonal he)⟩

end CFSG.Quasithin.ChapterG.Section10.Hypothesis
