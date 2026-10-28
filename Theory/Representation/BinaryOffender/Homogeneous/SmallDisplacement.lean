module
public import Theory.Representation.NormalComponentConstituents.Homogeneous
public import Theory.Representation.NormalConstituentDisplacement
public import Theory.Representation.BinaryOffender.FaithfulInvariantSection
public import Theory.Representation.BinaryOffender.Homogeneous.DoubleCoordinates
/-!
# Rank-two displacement on a homogeneous normal restriction

An actor whose displacement has dimension at most two stabilizes every
simple constituent of degree at least three. In a faithful homogeneous
restriction it moves every such constituent: fixing one would centralize
the normal subgroup, making its nonzero displacement a smaller submodule.
Three independent simple copies therefore give three independent nonzero
displacements, a contradiction. A proper constituent consequently occurs
exactly twice, with rank-one displacement on each copy.

The equivalence in the conclusion intertwines the original normal-subgroup
action. Source: Aschbacher--Smith G.10.16(4) and G.11.8, printed pp.363--364,
368. The G.11 low-rank application is in ChapterG.Section11.Multiplicity.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender
namespace Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (H : Subgroup G) [H.Normal]

omit [FiniteDimensional (ZMod 2) V] [H.Normal] in
private theorem faithful_of_same (I J : Subrepresentation (ρ.comp H.subtype))
    (hf : Function.Injective I.toRepresentation) (he : SameModule I J) :
    Function.Injective J.toRepresentation := by
  obtain ⟨e,he⟩ := he
  intro a b hab
  apply hf
  apply LinearMap.ext
  intro u
  apply e.injective
  rw [he,he]
  exact LinearMap.congr_fun hab (e u)

private theorem constituent_moved (I : Subrepresentation (ρ.comp H.subtype))
    (hf : Function.Injective I.toRepresentation)
    (hsame : ∀ J : Subrepresentation (ρ.comp H.subtype),
      IsIrreducible J.toRepresentation → SameModule I J)
    (hd : 3 ≤ finrank (ZMod 2) I.toSubmodule) (a : G)
    (hp : 0 < finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)))
    (hr : finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 2)
    (J : Subrepresentation (ρ.comp H.subtype)) (hJ : IsIrreducible J.toRepresentation) :
    J.toSubmodule.map (ρ a - LinearMap.id) ≠ ⊥ := by
  intro hz
  have hsmall (Q : Subrepresentation (ρ.comp H.subtype)) (hQ : IsIrreducible Q.toRepresentation) :
      finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) <
        finrank (ZMod 2) Q.toSubmodule := by
    have he := (hsame Q hQ).choose.finrank_eq
    omega
  have hnot := not_le_centralizer_of_small_displacement ρ H a hsmall hp
  have hfaith := faithful_of_same ρ H I J hf (hsame J hJ)
  have hcent : a ∈ centralizer (H : Set G) := by
    apply centralizes_of_fixes_faithful_section ρ H J.toSubmodule
      (le_subspaceStabilizer ρ _ (fun k hk u hu => J.apply_mem_toSubmodule ⟨k,hk⟩ hu))
    · intro k hk hfix
      have he : J.toRepresentation ⟨k,hk⟩ = J.toRepresentation 1 := by
        ext u
        exact (hfix u u.property).trans (by simp)
      exact congrArg Subtype.val (hfaith he)
    · rw [H.normalizer_eq_top]
      exact mem_top a
    · intro u hu
      have hm := Submodule.mem_map_of_mem (f := ρ a - LinearMap.id) hu
      rw [hz] at hm
      exact sub_eq_zero.mp hm
  apply hnot
  intro k hk x hx
  subst x
  exact ((mem_centralizer_iff.mp hcent) k hk).symm

omit [FiniteDimensional (ZMod 2) V] in
private theorem displacement_le (a : G) (U : Submodule (ZMod 2) V)
    (hu : U.map (ρ a) = U) : U.map (ρ a - LinearMap.id) ≤ U := by
  rintro _ ⟨u,hu',rfl⟩
  exact U.sub_mem (hu ▸ (Submodule.mem_map_of_mem hu')) hu'

private theorem displacement_add (a : G) (U W : Submodule (ZMod 2) V)
    (hd : Disjoint U W) (hu : U.map (ρ a) = U) (hw : W.map (ρ a) = W) :
    finrank (ZMod 2) ((U ⊔ W).map (ρ a - LinearMap.id)) =
      finrank (ZMod 2) (U.map (ρ a - LinearMap.id)) +
      finrank (ZMod 2) (W.map (ρ a - LinearMap.id)) := by
  have hm := hd.mono (displacement_le ρ a U hu) (displacement_le ρ a W hw)
  have he := Submodule.finrank_sup_add_finrank_inf_eq
    (U.map (ρ a - LinearMap.id)) (W.map (ρ a - LinearMap.id))
  rw [hm.eq_bot,finrank_bot,add_zero,← Submodule.map_sup] at he
  exact he

/-- A faithful homogeneous normal restriction with a nonzero displacement of
rank at most two has multiplicity at most two. -/
theorem degree_le_double_of_small_displacement
    (I : Subrepresentation (ρ.comp H.subtype)) (hi : IsIrreducible I.toRepresentation)
    (hh : homogeneousPart I ⊤ = ⊤)
    (hf : Function.Injective I.toRepresentation)
    (hsame : ∀ J : Subrepresentation (ρ.comp H.subtype),
      IsIrreducible J.toRepresentation → SameModule I J)
    (hd : 3 ≤ finrank (ZMod 2) I.toSubmodule) (a : G)
    (hp : 0 < finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)))
    (hr : finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 2) :
    finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) I.toSubmodule := by
  classical
  have hstable (J : Subrepresentation (ρ.comp H.subtype)) (hJ : IsIrreducible J.toRepresentation) :
      J.toSubmodule.map (ρ a) = J.toSubmodule := by
    apply map_constituent_eq_self_of_displacement_lt ρ H a J hJ
    have he := (hsame J hJ).choose.finrank_eq
    omega
  have hpos (J : Subrepresentation (ρ.comp H.subtype)) (hJ : IsIrreducible J.toRepresentation) :
      0 < finrank (ZMod 2) (J.toSubmodule.map (ρ a - LinearMap.id)) := by
    exact Nat.pos_of_ne_zero (fun hz => constituent_moved ρ H I hf hsame hd a hp hr J hJ
      (Submodule.finrank_eq_zero.mp hz))
  have hex (N : Subrepresentation (ρ.comp H.subtype)) (hN : N.toSubmodule ≠ ⊤) :
      ∃ J : Subrepresentation (ρ.comp H.subtype), SameModule I J ∧ ¬ J ≤ N := by
    by_contra! h
    apply hN
    apply top_unique
    rw [← hh]
    exact iSup_le fun J => iSup_le fun hJ => h J hJ.2
  by_cases ht : I.toSubmodule = ⊤
  · rw [ht,finrank_top]
    omega
  obtain ⟨J,hJ,hJI⟩ := hex I ht
  have hj := hJ.irreducible hi
  have hdis : Disjoint J.toSubmodule I.toSubmodule := by
    rw [disjoint_iff]
    exact congrArg Subrepresentation.toSubmodule
      ((((Subrepresentation.irreducible_iff_isAtom J).mp hj).not_le_iff_disjoint.mp hJI).eq_bot)
  have hdimJ : finrank (ZMod 2) J.toSubmodule = finrank (ZMod 2) I.toSubmodule :=
    hJ.choose.finrank_eq.symm
  have hdimIJ : finrank (ZMod 2) (I ⊔ J).toSubmodule =
      2 * finrank (ZMod 2) I.toSubmodule := by
    have hs := Submodule.finrank_sup_add_finrank_inf_eq I.toSubmodule J.toSubmodule
    rw [hdis.symm.eq_bot,finrank_bot,add_zero,hdimJ] at hs
    change finrank (ZMod 2) (I.toSubmodule ⊔ J.toSubmodule : Submodule (ZMod 2) V) = _
    omega
  by_cases htop : (I ⊔ J).toSubmodule = ⊤
  · rw [htop,finrank_top] at hdimIJ
    omega
  obtain ⟨K,hK,hKIJ⟩ := hex (I ⊔ J) htop
  have hk := hK.irreducible hi
  have hdisK : Disjoint K.toSubmodule (I ⊔ J).toSubmodule := by
    rw [disjoint_iff]
    exact congrArg Subrepresentation.toSubmodule
      ((((Subrepresentation.irreducible_iff_isAtom K).mp hk).not_le_iff_disjoint.mp hKIJ).eq_bot)
  have hIJ : (I ⊔ J).toSubmodule.map (ρ a) = (I ⊔ J).toSubmodule := by
    change (I.toSubmodule ⊔ J.toSubmodule).map (ρ a) = _
    rw [Submodule.map_sup,hstable I hi,hstable J hj]
    rfl
  have hsIJ := displacement_add ρ a I.toSubmodule J.toSubmodule hdis.symm
    (hstable I hi) (hstable J hj)
  have hsK := displacement_add ρ a K.toSubmodule (I ⊔ J).toSubmodule hdisK
    (hstable K hk) hIJ
  have hpI := hpos I hi
  have hpJ := hpos J hj
  have hpK := hpos K hk
  have hle := Submodule.finrank_mono
    (show (K.toSubmodule ⊔ (I ⊔ J).toSubmodule).map (ρ a - LinearMap.id) ≤
      LinearMap.range (ρ a - LinearMap.id) from by
        rintro _ ⟨u,_,rfl⟩
        exact ⟨u,rfl⟩)
  change finrank (ZMod 2) ((I ⊔ J).toSubmodule.map (ρ a - LinearMap.id)) = _ at hsIJ
  omega

/-- On a proper homogeneous constituent, displacement rank at most two is
exactly one on each of two copies, and the two copies fill the module. -/
theorem double_and_rank_one_of_small_displacement
    (I : Subrepresentation (ρ.comp H.subtype)) (hi : IsIrreducible I.toRepresentation)
    (hh : homogeneousPart I ⊤ = ⊤)
    (hf : Function.Injective I.toRepresentation)
    (hsame : ∀ J : Subrepresentation (ρ.comp H.subtype),
      IsIrreducible J.toRepresentation → SameModule I J)
    (hd : 3 ≤ finrank (ZMod 2) I.toSubmodule) (a : G)
    (hp : 0 < finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)))
    (hr : finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 2)
    (hproper : I.toSubmodule ≠ ⊤) :
    finrank (ZMod 2) V = 2 * finrank (ZMod 2) I.toSubmodule ∧
      Nonempty (Representation.Equiv (ρ.comp H.subtype) (I.toRepresentation.prod I.toRepresentation)) ∧
      I.toSubmodule.map (ρ a) = I.toSubmodule ∧
      finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 2 ∧
      finrank (ZMod 2) (I.toSubmodule.map (ρ a - LinearMap.id)) = 1 := by
  classical
  have hbound := degree_le_double_of_small_displacement ρ H I hi hh hf hsame hd a hp hr
  have hequiv := double_coordinates_of_degree_le I hi hh hproper hbound
  have hdim : finrank (ZMod 2) V = 2 * finrank (ZMod 2) I.toSubmodule := by
    obtain ⟨e⟩ := hequiv
    simpa only [Module.finrank_prod, two_mul] using e.toLinearEquiv.finrank_eq
  have hstable (J : Subrepresentation (ρ.comp H.subtype)) (hJ : IsIrreducible J.toRepresentation) :
      J.toSubmodule.map (ρ a) = J.toSubmodule := by
    apply map_constituent_eq_self_of_displacement_lt ρ H a J hJ
    have he := (hsame J hJ).choose.finrank_eq
    omega
  have hpos (J : Subrepresentation (ρ.comp H.subtype)) (hJ : IsIrreducible J.toRepresentation) :
      0 < finrank (ZMod 2) (J.toSubmodule.map (ρ a - LinearMap.id)) :=
    Nat.pos_of_ne_zero (fun hz => constituent_moved ρ H I hf hsame hd a hp hr J hJ
      (Submodule.finrank_eq_zero.mp hz))
  obtain ⟨J,hJ,hJI⟩ : ∃ J : Subrepresentation (ρ.comp H.subtype), SameModule I J ∧ ¬ J ≤ I := by
    by_contra! h
    apply hproper
    apply top_unique
    rw [← hh]
    exact iSup_le fun J => iSup_le fun hJ => h J hJ.2
  have hj := hJ.irreducible hi
  have hdis : Disjoint J.toSubmodule I.toSubmodule := by
    rw [disjoint_iff]
    exact congrArg Subrepresentation.toSubmodule
      ((((Subrepresentation.irreducible_iff_isAtom J).mp hj).not_le_iff_disjoint.mp hJI).eq_bot)
  have hs := displacement_add ρ a J.toSubmodule I.toSubmodule hdis (hstable J hj) (hstable I hi)
  have hle := Submodule.finrank_mono
    (show (J.toSubmodule ⊔ I.toSubmodule).map (ρ a - LinearMap.id) ≤
      LinearMap.range (ρ a - LinearMap.id) from by
        rintro _ ⟨u,_,rfl⟩
        exact ⟨u,rfl⟩)
  have hpI := hpos I hi
  have hpJ := hpos J hj
  exact ⟨hdim,hequiv,hstable I hi,by omega,by omega⟩
end Representation.BinaryOffender.Homogeneous
