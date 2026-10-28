module

public import Theory.Representation.EndFieldRep
public import Theory.Representation.SubspaceQuotient
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.RepresentationTheory.Invariants

/-!
# Perfect actions in degree at most three

Over a finite field, two commuting perfect groups cannot both act nontrivially
on a vector space of dimension at most three. The fixed subspace of a
nontrivial perfect action has dimension at most one. If it is nonzero, the
quotient is irreducible of dimension two. If it is zero, an irreducible
submodule has dimension at least two and every commuting operator preserves
it: its map to the smaller quotient must vanish. Schur's lemma and the finite
endomorphism field kill the second perfect action on this constituent. Its
remaining subquotient has dimension at most one. An action trivial on both a
subspace and its quotient has abelian image, so perfectness kills it too.

This argument uses literal invariant subspaces and quotient actions and does
not require complete reducibility. Applied to a centralizer's solvable
residual it gives solvability. For a central quotient, the perfect residual
of the inverse image lifts projective commutation to actual commutation;
arbitrary chosen lifts need not commute.

Source: the constituent and Schur-lemma step in GLS3, proof of Theorem 6.5.3,
`refs/KGroup/GLS3/chapter6.tex`, printed p.347.
-/

open scoped MonoidAlgebra
namespace Representation
namespace PerfectDegreeThree

variable {F G H V : Type*} [Field F] [Group G] [Group H]
  [AddCommGroup V] [Module F V]

-- Perfect groups have no nontrivial commuting image, even in a monoid.
private theorem eq_one_of_commuting [Group.IsPerfect G] {M : Type*} [Monoid M]
    (f : G →* M) (hc : ∀ g h, f g * f h = f h * f g) : f = 1 := by
  let f' := f.toHomUnits
  let : Group.IsPerfect f'.range := Group.IsPerfect.range f'
  let : IsMulCommutative f'.range := ⟨⟨by
    rintro ⟨_, g, rfl⟩ ⟨_, h, rfl⟩
    apply Subtype.ext
    exact Units.ext (hc g h)⟩⟩
  let : Subsingleton f'.range := inferInstance
  ext g
  exact congrArg (fun x : f'.range => (x.val : M))
    (Subsingleton.elim (⟨f' g, g, rfl⟩ : f'.range) 1)

private theorem eq_one_of_finrank_le_one [Group.IsPerfect G] [FiniteDimensional F V]
    (ρ : Representation F G V) (hdim : Module.finrank F V ≤ 1) : ρ = 1 := by
  rcases Nat.eq_zero_or_pos (Module.finrank F V) with hz | hp
  · let : Subsingleton V := Module.finrank_zero_iff.mp hz
    ext g v
    exact Subsingleton.elim _ _
  · have he : Module.finrank F V = 1 := by omega
    apply eq_one_of_commuting ρ
    intro g h
    obtain ⟨a, ha, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one he (ρ g)
    obtain ⟨b, hb, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one he (ρ h)
    rw [ha, hb]
    simp [smul_smul, mul_comm]

-- No semisimplicity is needed here: the subgroup acting trivially on the
-- subspace and quotient is abelian, and perfectness kills this image.
private theorem eq_one_of_trivial_subquotient [Group.IsPerfect G]
    (ρ : Representation F G V) (W : Subrepresentation ρ)
    (hW : W.toRepresentation = 1) (hQ : W.quotientRepresentation = 1) : ρ = 1 := by
  have hfix (g : G) (v : V) (hv : v ∈ W) : ρ g v = v :=
    congrArg Subtype.val (DFunLike.congr_fun (DFunLike.congr_fun hW g) (⟨v, hv⟩ : W))
  have hdiff (g : G) (v : V) : ρ g v - v ∈ W := by
    apply (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp
    change W.toSubmodule.mkQ (ρ g v - v) = 0
    rw [map_sub, ← W.quotientRepresentation_mk]
    have he := DFunLike.congr_fun (DFunLike.congr_fun hQ g) (W.toSubmodule.mkQ v)
    exact sub_eq_zero.mpr he
  apply eq_one_of_commuting ρ
  intro g h
  ext v
  have hg := hfix g (ρ h v - v) (hdiff h v)
  have hh := hfix h (ρ g v - v) (hdiff g v)
  simp only [map_sub] at hg hh
  change ρ g (ρ h v) = ρ h (ρ g v)
  rw [sub_eq_iff_eq_add] at hg hh
  rw [hg, hh]
  abel

set_option backward.isDefEq.respectTransparency false in
private theorem commuting_eq_one_of_irreducible [Finite F] [FiniteDimensional F V]
    [Group.IsPerfect H] (ρ : Representation F G V) [IsIrreducible ρ]
    (σ : Representation F H V) (hc : ∀ g h, ρ g * σ h = σ h * ρ g) : σ = 1 := by
  let t : H →* IntertwiningMap ρ ρ :=
    { toFun := fun h => ⟨σ h, fun g => (hc g h).symm⟩
      map_one' := by ext v; exact DFunLike.congr_fun (map_one σ) v
      map_mul' := by intro a b; ext v; exact DFunLike.congr_fun (map_mul σ a b) v }
  let e := IntertwiningMap.equivAlgEnd ρ
  have he : e.toMonoidHom.comp t = 1 :=
    eq_one_of_commuting _ (fun _ _ => mul_comm _ _)
  ext h v
  have ht : t h = 1 := e.toMulEquiv.injective (by
    rw [map_one]
    exact DFunLike.congr_fun he h)
  exact DFunLike.congr_fun (congrArg IntertwiningMap.toLinearMap ht) v


variable [FiniteDimensional F V]

private theorem irreducible_of_nontrivial_finrank_le_two [Group.IsPerfect G]
    (ρ : Representation F G V) (hnt : ρ ≠ 1) (hd : Module.finrank F V ≤ 2) :
    IsIrreducible ρ := by
  have : Nontrivial V := by
    by_contra! h
    let : Subsingleton V := h
    exact hnt (by ext g v; exact Subsingleton.elim _ _)
  refine ⟨?_⟩
  intro W
  by_contra! hw
  have hb : W.toSubmodule ≠ ⊥ := fun h => hw.1 (Subrepresentation.toSubmodule_injective h)
  have ht : W.toSubmodule ≠ ⊤ := fun h => hw.2 (Subrepresentation.toSubmodule_injective h)
  have hpos : 0 < Module.finrank F W.toSubmodule := by
    exact Nat.pos_of_ne_zero (fun h => hb (Submodule.finrank_eq_zero.mp h))
  have hlt := Submodule.finrank_lt ht
  have hsum := Submodule.finrank_quotient_add_finrank W.toSubmodule
  exact hnt (eq_one_of_trivial_subquotient ρ W
    (eq_one_of_finrank_le_one _ (by omega))
    (eq_one_of_finrank_le_one _ (by omega)))


-- Restriction to a common invariant subspace and its literal quotient.
private abbrev otherActor (ρ : Representation F G V) (σ : Representation F H V)
    (W : Subrepresentation ρ) (hs : ∀ h v, v ∈ W → σ h v ∈ W) :
    Subrepresentation σ := ⟨W.toSubmodule, fun h _ hv => hs h _ hv⟩

omit [FiniteDimensional F V] in
private theorem commuting_restriction (ρ : Representation F G V) (σ : Representation F H V)
    (hc : ∀ g h, ρ g * σ h = σ h * ρ g)
    (W : Subrepresentation ρ) (hs : ∀ h v, v ∈ W → σ h v ∈ W) (g : G) (h : H) :
    W.toRepresentation g * (otherActor ρ σ W hs).toRepresentation h =
      (otherActor ρ σ W hs).toRepresentation h * W.toRepresentation g := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact DFunLike.congr_fun (hc g h) v.val

omit [FiniteDimensional F V] in
private theorem commuting_quotient (ρ : Representation F G V) (σ : Representation F H V)
    (hc : ∀ g h, ρ g * σ h = σ h * ρ g)
    (W : Subrepresentation ρ) (hs : ∀ h v, v ∈ W → σ h v ∈ W) (g : G) (h : H) :
    W.quotientRepresentation g * (otherActor ρ σ W hs).quotientRepresentation h =
      (otherActor ρ σ W hs).quotientRepresentation h * W.quotientRepresentation g := by
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with | _ v =>
    exact congrArg W.toSubmodule.mkQ (DFunLike.congr_fun (hc g h) v)

-- An irreducible submodule larger than its quotient is preserved by the commutant.
private theorem stable_of_irreducible_large (ρ : Representation F G V) (σ : Representation F H V)
    (hc : ∀ g h, ρ g * σ h = σ h * ρ g)
    (W : Subrepresentation ρ) [IsIrreducible W.toRepresentation]
    (hd : Module.finrank F (V ⧸ W.toSubmodule) < Module.finrank F W.toSubmodule) :
    ∀ h v, v ∈ W → σ h v ∈ W := by
  intro h v hv
  let t : IntertwiningMap W.toRepresentation W.quotientRepresentation :=
    ⟨W.toSubmodule.mkQ ∘ₗ σ h ∘ₗ W.toSubmodule.subtype, fun g => by
      ext w
      exact congrArg W.toSubmodule.mkQ (DFunLike.congr_fun (hc g h).symm w.val)⟩
  have ht : t = 0 := (IsIrreducible.injective_or_eq_zero t).resolve_left fun hi =>
    (not_le_of_gt hd) (LinearMap.finrank_le_finrank_of_injective hi)
  exact (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp
    (DFunLike.congr_fun (congrArg IntertwiningMap.toLinearMap ht)
      (⟨v, hv⟩ : W.toSubmodule))

-- The canonical fixed subspace is invariant under every commuting actor.
private noncomputable def fixedSubrepresentation (ρ : Representation F G V) : Subrepresentation ρ :=
  ⟨ρ.invariants, fun g _ hv => by simpa only [hv g] using hv⟩

omit [FiniteDimensional F V] in
private theorem fixedSubrepresentation_trivial (ρ : Representation F G V) :
    (fixedSubrepresentation ρ).toRepresentation = 1 := by
  ext g v
  exact v.property g

omit [FiniteDimensional F V] in
private theorem stable_fixed (ρ : Representation F G V) (σ : Representation F H V)
    (hc : ∀ g h, ρ g * σ h = σ h * ρ g) :
    ∀ h v, v ∈ fixedSubrepresentation ρ → σ h v ∈ fixedSubrepresentation ρ := by
  intro h v hv g
  change ρ g (σ h v) = σ h v
  calc
    _ = σ h (ρ g v) := DFunLike.congr_fun (hc g h) v
    _ = σ h v := congrArg (σ h) (hv g)

/-- Two commuting perfect actions in degree at most three cannot both be nontrivial. -/
public theorem commuting_eq_one_of_finrank_le_three [Finite F]
    [Group.IsPerfect G] [Group.IsPerfect H]
    (ρ : Representation F G V) (σ : Representation F H V)
    (hnt : ρ ≠ 1) (hd : Module.finrank F V ≤ 3)
    (hc : ∀ g h, ρ g * σ h = σ h * ρ g) : σ = 1 := by
  let I := fixedSubrepresentation ρ
  have hIt : I.toRepresentation = 1 := fixedSubrepresentation_trivial ρ
  have hIq : I.quotientRepresentation ≠ 1 := fun h =>
    hnt (eq_one_of_trivial_subquotient ρ I hIt h)
  have hIle : Module.finrank F I.toSubmodule ≤ 1 := by
    have hsum := Submodule.finrank_quotient_add_finrank I.toSubmodule
    by_contra! h
    exact hIq (eq_one_of_finrank_le_one _ (by omega))
  by_cases hIb : I.toSubmodule = ⊥
  · have : Nontrivial V := by
      by_contra! h
      let : Subsingleton V := h
      exact hnt (by ext g v; exact Subsingleton.elim _ _)
    obtain ⟨W, hW⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρ
    let := hW
    have hWlarge : 2 ≤ Module.finrank F W.toSubmodule := by
      by_contra! h
      have ht := eq_one_of_finrank_le_one W.toRepresentation (by omega)
      have hwle : W.toSubmodule ≤ I.toSubmodule := by
        intro v hv g
        exact congrArg Subtype.val
          (DFunLike.congr_fun (DFunLike.congr_fun ht g) (⟨v, hv⟩ : W.toSubmodule))
      have hwb : W = ⊥ := Subrepresentation.toSubmodule_injective
        (le_bot_iff.mp (hwle.trans_eq hIb))
      exact (Subrepresentation.irreducible_iff_isAtom W).mp hW |>.ne_bot hwb
    have hQle : Module.finrank F (V ⧸ W.toSubmodule) ≤ 1 := by
      have := Submodule.finrank_quotient_add_finrank W.toSubmodule
      omega
    have hs := stable_of_irreducible_large ρ σ hc W (by omega)
    exact eq_one_of_trivial_subquotient σ (otherActor ρ σ W hs)
      (commuting_eq_one_of_irreducible W.toRepresentation _
        (commuting_restriction ρ σ hc W hs))
      (eq_one_of_finrank_le_one _ hQle)
  · have hIpos : 0 < Module.finrank F I.toSubmodule :=
      Nat.pos_of_ne_zero fun h => hIb (Submodule.finrank_eq_zero.mp h)
    have hQle : Module.finrank F (V ⧸ I.toSubmodule) ≤ 2 := by
      have := Submodule.finrank_quotient_add_finrank I.toSubmodule
      omega
    let := irreducible_of_nontrivial_finrank_le_two I.quotientRepresentation hIq hQle
    have hs := stable_fixed ρ σ hc
    exact eq_one_of_trivial_subquotient σ (otherActor ρ σ I hs)
      (eq_one_of_finrank_le_one _ hIle)
      (commuting_eq_one_of_irreducible I.quotientRepresentation _
        (commuting_quotient ρ σ hc I hs))


/-- A nontrivial perfect matrix subgroup in degree at most three has solvable centralizer. -/
public theorem centralizer_isSolvable [Finite F] [Finite G]
    (ρ : Representation F G V) (hfaith : Function.Injective ρ)
    (hd : Module.finrank F V ≤ 3)
    (P : Subgroup G) [Group.IsPerfect P] (hne : P ≠ ⊥) :
    Group.IsSolvable (Subgroup.centralizer (P : Set G)) := by
  let C := Subgroup.centralizer (P : Set G)
  let R := Subgroup.solvableResidual C
  let τ := ρ.comp P.subtype
  let σ := ρ.comp (C.subtype.comp R.subtype)
  have hnt : τ ≠ 1 := by
    intro h
    apply hne
    apply le_bot_iff.mp
    intro p hp
    apply hfaith
    calc
      ρ p = 1 := DFunLike.congr_fun h (⟨p, hp⟩ : P)
      _ = ρ 1 := (map_one ρ).symm
  have hc (p : P) (r : R) : τ p * σ r = σ r * τ p := by
    change ρ p.val * ρ r.val.val = ρ r.val.val * ρ p.val
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subgroup.mem_centralizer_iff.mp r.val.property p.val p.property)
  have hs : σ = 1 := commuting_eq_one_of_finrank_le_three τ σ hnt hd hc
  have hsi : Function.Injective σ :=
    hfaith.comp (C.subtype_injective.comp R.subtype_injective)
  have hr : R = ⊥ := by
    apply le_bot_iff.mp
    intro r hr
    have he : (⟨r, hr⟩ : R) = 1 := hsi (by rw [hs]; rfl)
    exact congrArg Subtype.val he
  obtain ⟨n, hn⟩ := Subgroup.exists_derivedSeries_eq_solvableResidual (G := C)
  exact ⟨n, hn.trans hr⟩


/-- Central quotients of faithful degree-three groups have solvable centralizers
of nonsolvable subgroups. The perfect residual removes the scalar commutator. -/
public theorem quotient_centralizer_isSolvable [Finite F] [Finite G]
    (ρ : Representation F G V) (hfaith : Function.Injective ρ)
    (hd : Module.finrank F V ≤ 3)
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G)
    (N : Subgroup H) (hN : ¬ Group.IsSolvable N) :
    Group.IsSolvable (Subgroup.centralizer (N : Set H)) := by
  let A := N.comap f
  have hA : ¬ Group.IsSolvable A := by
    intro ha
    let := ha
    exact hN (Group.isSolvable_of_surjective
      (f.subgroupComap_surjective_of_surjective N hf))
  let P := (Subgroup.solvableResidual A).map A.subtype
  have : Group.IsPerfect P := Group.IsPerfect.map A.subtype
  have hP : P ≠ ⊥ := by
    intro hp
    have hr := ((Subgroup.solvableResidual A).map_eq_bot_iff_of_injective
      A.subtype_injective).mp hp
    obtain ⟨n, hn⟩ := Subgroup.exists_derivedSeries_eq_solvableResidual (G := A)
    exact hA ⟨n, hn.trans hr⟩
  let C := Subgroup.centralizer (N : Set H)
  have hle : C.comap f ≤ Subgroup.centralizer (P : Set G) := by
    rw [← Subgroup.comap_centralizer_map_eq_of_perfect f P
      (hker.trans (Subgroup.center_le_centralizer _))]
    apply Subgroup.comap_mono
    apply Subgroup.centralizer_le
    change P.map f ≤ N
    apply Subgroup.map_le_iff_le_comap.mpr
    rintro _ ⟨a, _, rfl⟩
    exact a.property
  let : Group.IsSolvable (Subgroup.centralizer (P : Set G)) :=
    centralizer_isSolvable ρ hfaith hd P hP
  let : Group.IsSolvable (C.comap f) := Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hle)
  exact Group.isSolvable_of_surjective (f.subgroupComap_surjective_of_surjective C hf)

end PerfectDegreeThree
end Representation
