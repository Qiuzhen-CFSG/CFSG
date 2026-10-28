module
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Even
public import Theory.GroupTheory.PPerfectHom

/-!
# Detecting natural A₆ cocycles on a transitive subgroup

Every cocycle on the binary natural A₆ module is a displacement of a full
six-point permutation vector. If it vanishes on a transitive two-perfect
subgroup, the constant displacement defines a trivial binary character;
the permutation vector is then constant. This proves vanishing of the
whole cocycle, including its possible nonprincipal cohomology class.

Consequently the nonsplit permutation extension introduces no additional
vectors fixed by a transitive A₄. The actual moved-section application
retains both central and trivial-quotient attachments.

Source: Aschbacher–Smith B.3, I.1.6(1), and15.3.21, pp.83,408,1127.
-/
public section
open Subgroup Representation Representation.OneCohomology Equiv Equiv.Perm
namespace BinaryPermutation

/-- Every cocycle of the actual natural A₆ module is the displacement of a
full permutation vector, including the nonprincipal cohomology class. -/
theorem alternatingSix_naturalDisplacement_surjective :
    Function.Surjective (naturalDisplacement (Fin 6)) := by
  intro f
  obtain ⟨v,hv⟩ := alternatingNatural_normalize_pointStabilizer 6 (Or.inl rfl) 0 f
  obtain ⟨a,ha⟩ := alternatingNatural_normalized_eq_coordinate 6 (Or.inl rfl) 0
    (f - principal (alternatingNaturalRepresentation (Fin 6)) v) (by
      intro g hg
      change f.val g - (alternatingNaturalRepresentation (Fin 6) g v - v) = 0
      rw [hv g hg,sub_self])
  obtain ⟨u,hu,he⟩ := v.property
  let u' : core (Fin 6) := ⟨u,hu⟩
  have hvu : coreToNatural (Fin 6) u' = v := Subtype.ext he
  refine ⟨a • Pi.single 0 1 + u,?_⟩
  rw [map_add,map_smul]
  change a • naturalCoordinateCocycle (Fin 6) 0 + naturalDisplacement (Fin 6) u' = f
  rw [naturalDisplacement_core,hvu]
  exact ((sub_eq_iff_eq_add (a := f)
    (b := principal (alternatingNaturalRepresentation (Fin 6)) v)
    (c := a • naturalCoordinateCocycle (Fin 6) 0)).mp ha).symm

/-- A transitive two-perfect permutation group has no extra fixed vector
modulo the constants. The constant displacement is a binary character. -/
theorem mem_constants_of_transitive_twoPerfect_displacement
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (A : Subgroup (alternatingGroup Ω)) (hA : IsPPerfect 2 A)
    (ht : ∀ i j : Ω, ∃ g : A, g.val.val i = j)
    (w : Full Ω)
    (hw : ∀ g : A, representation Ω g.val.val w - w ∈ constants Ω) :
    w ∈ constants Ω := by
  classical
  let b : Ω := Classical.choice inferInstance
  have hconst (g : A) (i : Ω) :
      (representation Ω g.val.val w - w) i =
        (representation Ω g.val.val w - w) b := by
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hw g)
    rw [←hc]
    rfl
  let φ : A →* Multiplicative (ZMod 2) :=
    { toFun := fun g => Multiplicative.ofAdd ((representation Ω g.val.val w - w) b)
      map_one' := by simp
      map_mul' := fun g h => by
        change w ((g*h).val.val.symm b) - w b =
          (w (g.val.val.symm b) - w b) + (w (h.val.val.symm b) - w b)
        have he := hconst h (g.val.val.symm b)
        change w (h.val.val.symm (g.val.val.symm b)) - w (g.val.val.symm b) =
          w (h.val.val.symm b) - w b at he
        change w (h.val.val.symm (g.val.val.symm b)) - w b = _
        rw [sub_eq_iff_eq_add.mp he]
        abel }
  have hφ : φ = 1 := hA.hom_eq_one_of_isPGroup
    (IsPGroup.of_card (n := 1) (by simp)) φ
  have hfix (g : A) : representation Ω g.val.val w = w := by
    funext i
    apply sub_eq_zero.mp
    exact (hconst g i).trans
      (congrArg Multiplicative.toAdd (DFunLike.congr_fun hφ g))
  apply Submodule.mem_span_singleton.mpr
  refine ⟨w b,?_⟩
  funext i
  obtain ⟨g,hg⟩ := ht i b
  have hi : g.val.val.symm b = i := (Equiv.symm_apply_eq _).mpr hg.symm
  have he := congrFun (hfix g) b
  simpa [representation_apply,hi,allOne] using he.symm

/-- Vanishing on a transitive two-perfect subgroup already annihilates a
natural A₆ cocycle. This detects the nonsplit permutation extension as well
as principal cocycles. -/
theorem alternatingSix_cocycle_eq_zero_of_transitive
    (A : Subgroup (alternatingGroup (Fin 6))) (hA : IsPPerfect 2 A)
    (ht : ∀ i j : Fin 6, ∃ g : A, g.val.val i = j)
    (f : cocycles (alternatingNaturalRepresentation (Fin 6)))
    (hf : ∀ g : A, f.val g = 0) : f = 0 := by
  obtain ⟨w,rfl⟩ := alternatingSix_naturalDisplacement_surjective f
  apply (naturalDisplacement_eq_zero_iff (Fin 6) (by simp) w).mpr
  apply mem_constants_of_transitive_twoPerfect_displacement A hA ht w
  intro g
  apply (Submodule.Quotient.mk_eq_zero _).mp
  exact congrArg (fun v : natural (Fin 6) => (v : Deleted (Fin 6))) (hf g)

end BinaryPermutation
