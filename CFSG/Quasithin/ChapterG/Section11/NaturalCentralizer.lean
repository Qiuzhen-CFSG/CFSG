module

public import CFSG.Quasithin.ChapterG.Section11.NaturalConstituent
public import Theory.Representation.BinaryAlternatingSixModels.Schur
public import Theory.Representation.BinaryPermutation.SevenCommutant
public import Theory.Representation.BinaryPermutation.EightCommutant
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models

/-!
# The centralizer of a doubled natural component

The proper marked constituent branch leaves an actual doubled natural
alternating action on the original module.  The scalar commutant of the
natural six- and seven-letter modules, together with the trivial invertible
commutant in degree eight, makes the ambient centralizer act faithfully on
the two-dimensional multiplicity space.  Over `ZMod 2` this is the literal
linear action of `GL₂(2) ≃ S₃`.

This is the centralizer input for the remaining G.11.2 whole-module
recognition.  It retains the original component subgroup and the actual
intertwining coordinates; no abstract constituent group is substituted for
the source action.

Source: Aschbacher--Smith G.11.7--8, printed pp.366--368.
-/

@[expose] public section
open Subgroup Module Representation
namespace CFSG.Quasithin.ChapterG.Section11

private theorem doubled_centralizer_embedding
    {G D U V : Type*} [Group G] [Group D]
    [AddCommGroup U] [Module (ZMod 2) U] [Nontrivial U]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (H : Subgroup G) (σ : Representation (ZMod 2) D U)
    (e : H ≃* D) (f : V ≃ₗ[ZMod 2] (U × U))
    (hf : ∀ (h : H) v, f (ρ h v) = (σ.prod σ) (e h) (f v))
    (hs : ∀ t : IntertwiningMap σ σ, ∃ a : ZMod 2, ∀ u, t u = a • u) :
    ∃ j : centralizer (H : Set G) →* Equiv.Perm (Fin 3), Function.Injective j := by
  classical
  let M := IntertwiningMap σ (σ.prod σ)
  let l : (ZMod 2 × ZMod 2) →ₗ[ZMod 2] M := {
    toFun := fun a => a.1 • IntertwiningMap.inl (ZMod 2) σ σ +
      a.2 • IntertwiningMap.inr (ZMod 2) σ σ
    map_add' := by intros; simp [add_smul]; abel
    map_smul' := by intros; simp [smul_add,smul_smul] }
  have hl (a : ZMod 2 × ZMod 2) (u : U) : l a u = (a.1 • u,a.2 • u) := by
    change a.1 • (u,(0 : U)) + a.2 • ((0 : U),u) = _
    simp
  have hbij : Function.Bijective l := by
    constructor
    · intro a b hab
      obtain ⟨u,hu⟩ := exists_ne (0 : U)
      have he := congrArg (fun t : M => t u) hab
      rw [hl,hl] at he
      exact Prod.ext ((smul_left_injective (R := ZMod 2) hu) (congrArg Prod.fst he))
        ((smul_left_injective (R := ZMod 2) hu) (congrArg Prod.snd he))
    · intro t
      obtain ⟨a,ha⟩ := hs ((IntertwiningMap.fst (ZMod 2) σ σ).comp t)
      obtain ⟨b,hb⟩ := hs ((IntertwiningMap.snd (ZMod 2) σ σ).comp t)
      refine ⟨(a,b),?_⟩
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro u
      exact (hl (a,b) u).trans (Prod.ext (ha u).symm (hb u).symm)
  let c := LinearEquiv.ofBijective l hbij
  let τ : Representation (ZMod 2) G (U × U) := f.conjRingEquiv.toMonoidHom.comp ρ
  have hτ (g : G) (w : U × U) : τ g w = f (ρ g (f.symm w)) := rfl
  have ht (g : G) (hg : g ∈ centralizer (H : Set G)) (d : D) (w : U × U) :
      τ g ((σ.prod σ) d w) = (σ.prod σ) d (τ g w) := by
    obtain ⟨h,rfl⟩ := e.surjective d
    obtain ⟨v,rfl⟩ := f.surjective w
    rw [← hf, hτ, f.symm_apply_apply, hτ, f.symm_apply_apply, ← hf]
    rw [← Module.End.mul_apply,← map_mul, ← mem_centralizer_iff.mp hg h h.property,
      map_mul,Module.End.mul_apply]
  let κ : Representation (ZMod 2) (centralizer (H : Set G)) M := {
    toFun := fun g => {
      toFun := fun t => {
        toLinearMap := (τ g).comp t.toLinearMap
        isIntertwining' d := by
          apply LinearMap.ext
          intro u
          change τ g (t (σ d u)) = (σ.prod σ) d (τ g (t u))
          rw [t.isIntertwining,ht g g.property] }
      map_add' := by
        intro a b
        apply IntertwiningMap.ext
        apply LinearMap.ext
        intro u
        exact map_add (τ g) _ _
      map_smul' := by
        intro a b
        apply IntertwiningMap.ext
        apply LinearMap.ext
        intro u
        exact map_smul (τ g) _ _ }
    map_one' := by
      apply LinearMap.ext
      intro t
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro u
      exact LinearMap.congr_fun τ.map_one (t u)
    map_mul' := by
      intro a b
      apply LinearMap.ext
      intro t
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro u
      exact LinearMap.congr_fun (τ.map_mul a b) (t u) }
  have hκ : Function.Injective κ := by
    intro a b hab
    have he (u : U) : τ a (u,0) = τ b (u,0) :=
      congrArg (fun t : Module.End (ZMod 2) M => t (IntertwiningMap.inl (ZMod 2) σ σ) u) hab
    have he' (u : U) : τ a (0,u) = τ b (0,u) :=
      congrArg (fun t : Module.End (ZMod 2) M => t (IntertwiningMap.inr (ZMod 2) σ σ) u) hab
    apply Subtype.ext
    apply hρ
    ext v
    apply f.injective
    have hadd (g : G) : τ g (f v) = τ g ((f v).1,0) + τ g (0,(f v).2) := by
      rw [← map_add]; simp
    have hh := (hadd a).trans ((congrArg₂ (· + ·) (he (f v).1) (he' (f v).2)).trans (hadd b).symm)
    simpa only [hτ,f.symm_apply_apply] using hh
  let q := (LinearEquiv.piFinTwo (ZMod 2) (fun _ : Fin 2 => ZMod 2)).trans c
  let A := LinearMap.GeneralLinearGroup.congrLinearEquiv q.symm
  let L := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 2 → ZMod 2)
  let j := BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree.toMonoidHom.comp
    (L.toMonoidHom.comp (A.toMonoidHom.comp κ.asGroupHom))
  refine ⟨j,?_⟩
  apply BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree.injective.comp
  apply L.injective.comp
  apply A.injective.comp
  intro a b hab
  exact hκ (congrArg Units.val hab)

private theorem natural_commutant_scalar_six :
    ∀ t : IntertwiningMap (BinaryPermutation.alternatingNaturalRepresentation (Fin 6))
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)),
      ∃ a : ZMod 2, ∀ u, t u = a • u := by
  intro t
  obtain ⟨a,ha⟩ := BinaryAlternatingSix.Schur.natural_commuting_scalar
    t.toLinearMap t.isIntertwining
  exact ⟨a, ha⟩

private theorem natural_commutant_scalar_seven :
    ∀ t : IntertwiningMap (BinaryPermutation.alternatingNaturalRepresentation (Fin 7))
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 7)),
      ∃ a : ZMod 2, ∀ u, t u = a • u := by
  intro t
  obtain ⟨a,ha⟩ := BinaryPermutation.SevenCommutant.commuting_scalar
    t.toLinearMap t.isIntertwining
  exact ⟨a, ha⟩

private theorem natural_commutant_scalar_eight :
    ∀ t : IntertwiningMap (BinaryPermutation.alternatingNaturalRepresentation (Fin 8))
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)),
      ∃ a : ZMod 2, ∀ u, t u = a • u := by
  intro t
  let : IsIrreducible (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) :=
    BinaryPermutation.alternatingNatural_isIrreducible (by decide)
  by_cases hz : t = 0
  · exact ⟨0, fun u => by rw [hz]; simp⟩
  · have hi : Function.Injective t :=
      (Representation.IsIrreducible.injective_or_eq_zero t).resolve_right hz
    have hsur : Function.Surjective t.toLinearMap :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rfl)).mp hi
    let e : BinaryPermutation.natural (Fin 8) ≃ₗ[ZMod 2]
        BinaryPermutation.natural (Fin 8) := LinearEquiv.ofBijective t.toLinearMap ⟨hi,hsur⟩
    have he_apply (x : BinaryPermutation.natural (Fin 8)) : e x = t x :=
      LinearEquiv.ofBijective_apply t.toLinearMap x
    have he := BinaryPermutation.EightCommutant.commuting_eq_refl e (by
      intro g x
      rw [he_apply,he_apply]
      exact LinearMap.congr_fun (t.isIntertwining' g) x)
    refine ⟨1, fun u => ?_⟩
    rw [one_smul, ← he_apply]
    exact LinearEquiv.congr_fun he u

/-- A doubled natural A₆, A₇ or A₈ component has faithful centralizer action
on its two-copy multiplicity space, hence an explicit embedding into S₃. -/
theorem natural_centralizer_embedding
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (H : Subgroup G) (n : ℕ)
    (hmodel : Section09.Quasiequivalent (ρ.comp H.subtype)
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin n)).prod
        (BinaryPermutation.alternatingNaturalRepresentation (Fin n))))
    (hn : n = 6 ∨ n = 7 ∨ n = 8) :
    ∃ j : centralizer (H : Set G) →* Equiv.Perm (Fin 3), Function.Injective j := by
  let : IsIrreducible (BinaryPermutation.alternatingNaturalRepresentation (Fin n)) :=
    BinaryPermutation.alternatingNatural_isIrreducible (by simp only [Fintype.card_fin]; omega)
  let : Nontrivial (BinaryPermutation.natural (Fin n)) :=
    Subrepresentation.irreducible_module_nontrivial
      (BinaryPermutation.alternatingNaturalRepresentation (Fin n))
  obtain ⟨e,f,hf⟩ := hmodel
  rcases hn with rfl | rfl | rfl
  · exact doubled_centralizer_embedding ρ hρ H
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) e f hf
      natural_commutant_scalar_six
  · exact doubled_centralizer_embedding ρ hρ H
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 7)) e f hf
      natural_commutant_scalar_seven
  · exact doubled_centralizer_embedding ρ hρ H
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) e f hf
      natural_commutant_scalar_eight

end CFSG.Quasithin.ChapterG.Section11
