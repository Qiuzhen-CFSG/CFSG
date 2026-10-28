module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.Obstruction
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import Theory.SpecificGroups.SymmetricFourSolvable


/-!
# The action-kernel obstruction to excluding inside C-components

The actual four-dimensional orthogonal action has solvable actor
SL₂(2) ≀ C₂. Hence every perfect subgroup of M centralizes V. If a
C-component K of I lies in M, characteristic two of M ∩ I shows that K
is nonordinary. The extension argument in `Obstruction` puts every
I-conjugate of K inside M as well. Its intrinsic normal closure therefore
centralizes V, and normality in I then makes it centralize U_I = ⟨Z^I⟩.

Consequently, using 15.3.11(2), K lies in M exactly when it lies in
C_I(U_I). Since this centralizer is normal in I, the exclusion of all
inside C-components is equivalent to its solvability. This equivalence
is a reduction of the remaining obligation, not a proof of 15.3.33(3).
In particular, neither solvability nor exclusion is assumed below.

The consumed local conclusions are the natural action of 15.3.2(1),
15.3.11(1) (Sylow control), (2) (the action kernel is inside M), (4)
(the relative normalizer of Y₊), (5) (the three-group quotient of Y₊),
(7) (characteristic two of M ∩ I), (8) (trivial odd core), and 15.3.25.
The last theorem uses `CharacteristicTwo.LocalData` to retain the literal
S = N_T(V₁), Y = O²(⟨O₂(M ∩ M_c)^M⟩), and Hypothesis 15.3.10.
It does not identify M with M_c. Other standing hypotheses and earlier
conclusions remain available to the source assembly; they are not replaced
by an assertion that this kernel is solvable. No later 15.3.34–44 result
is used.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
printed pp.1121–1125 and 1134; Definition A.3.1 and Proposition A.3.3,
pp.41–43. The printed 1.1.5(3), pp.501–503, concerns ordinary components.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure.InsideExclusion

private theorem planeActor_solvable : Group.IsSolvable OrthogonalPlaneActor := by
  let := FourGroupMatrixCoordinates.naturalAction
  let := FourGroupMatrixCoordinates.naturalAction_faithful
  let e : OrthogonalPlaneVector ≃ Fin 4 :=
    Fintype.equivOfCardEq (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm OrthogonalPlaneVector) :=
    Group.isSolvable_of_isSolvable_injective (f := e.permCongrHom.toMonoidHom) e.permCongrHom.injective
  exact Group.isSolvable_of_isSolvable_injective
    (f := MulAction.toPermHom OrthogonalPlaneActor OrthogonalPlaneVector)
    MulAction.toPerm_injective

private theorem orthogonalActor_solvable : Group.IsSolvable OrthogonalActor := by
  let := planeActor_solvable
  let j : OrthogonalPlaneIndex := Multiplicative.ofAdd (1 : ZMod 2)
  let f : (OrthogonalPlaneIndex → OrthogonalPlaneActor) →*
      OrthogonalPlaneActor × OrthogonalPlaneActor :=
    { toFun := fun a => (a 1, a j)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b h
    funext i
    have hi : i = 1 ∨ i = j := by revert i; decide
    rcases hi with rfl | rfl
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  let : Group.IsSolvable (OrthogonalPlaneIndex → OrthogonalPlaneActor) :=
    Group.isSolvable_of_isSolvable_injective hf
  let b : (OrthogonalPlaneIndex → OrthogonalPlaneActor) →* OrthogonalActor :=
    { toFun := fun a => ⟨a, 1⟩
      map_one' := rfl
      map_mul' := fun _ _ => by ext <;> simp }
  apply Group.isSolvable_of_ker_le_range b RegularWreathProduct.rightHom
  intro a ha
  exact ⟨a.left, by ext; rfl; exact ha.symm⟩

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Every perfect subgroup inside M acts trivially on the actual orthogonal module. -/
theorem perfect_centralizes_module {M V D : Subgroup G}
    (a : NaturalOrthogonalAction M V) [Group.IsPerfect D] (hDM : D ≤ M) :
    D ≤ centralizer (V : Set G) := by
  let := orthogonalActor_solvable
  let : Group.IsPerfect (D.subgroupOf M) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hDM).symm.toMonoidHom)
      (subgroupOfEquivOfLe hDM).symm.surjective
  let : Group.IsPerfect (a.image D) := Group.IsPerfect.map a.actor
  apply (a.image_eq_bot_iff hDM).mp
  by_contra hn
  let : Nontrivial (a.image D) := (nontrivial_iff_ne_bot _).mpr hn
  exact Group.IsPerfect.not_isSolvable (a.image D) inferInstance

/-- All conjugates are still nonordinary C-components of I. The proved extension argument places them inside M, where their perfectness kills the orthogonal action. -/
theorem inside_normalClosure_centralizes_module {Yplus S M I V : Subgroup G}
    (a : NaturalOrthogonalAction M V)
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (h25 : ∀ J ∈ outsideFamily Yplus S M, generalizedFitting J ≠ pCore 2 J)
    (hodd : ∀ J ∈ outsideFamily Yplus S M, pPrimeCore 2 J = ⊥)
    (hSM : S ≤ M) (hMI : I ⊓ normalizer (Yplus : Set G) = M ⊓ I)
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (hFMI : generalizedFitting (M.subgroupOf I) = pCore 2 (M.subgroupOf I))
    {K : Subgroup I} (hK : K.IsCComponent) (hKM : K.map I.subtype ≤ M) :
    (normalClosure (K : Set I)).map I.subtype ≤ centralizer (V : Set G) := by
  have hn : ¬ IsComponent I K := by
    intro ho
    exact component_not_le_characteristicTwo ho hFMI (map_le_iff_le_comap.mp hKM)
  apply map_le_iff_le_comap.mpr
  apply (closure_le _).mpr
  intro x hx
  obtain ⟨k, hk, hx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨g, rfl⟩ := isConj_iff.mp hx
  let Kg := K.map (MulAut.conj g).toMonoidHom
  have hKg : Kg.IsCComponent := hK.map_equiv (MulAut.conj g)
  have hgn : ¬ IsComponent I Kg := by rwa [isComponent_map_equiv_iff]
  have hgM : Kg.map I.subtype ≤ M :=
    nonordinary_cComponent_le_M hI hSylow h25 hodd hSM hMI hY hKg hgn
  let := hKg.perfect
  let : Group.IsPerfect (Kg.map I.subtype) := Group.IsPerfect.map I.subtype
  exact perfect_centralizes_module a hgM
    (mem_map.mpr ⟨g * k * g⁻¹, mem_map.mpr ⟨k, hk, rfl⟩, rfl⟩)

/-- The whole normal closure, taken inside I, lies in C_I(U_I). This uses normality to pass from centralizing Z to centralizing its I-conjugates. -/
theorem inside_normalClosure_le_actionKernel {Yplus S M I : Subgroup G}
    (T : Sylow 2 G) (a : NaturalOrthogonalAction M (localModule T M))
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (h25 : ∀ J ∈ outsideFamily Yplus S M, generalizedFitting J ≠ pCore 2 J)
    (hodd : ∀ J ∈ outsideFamily Yplus S M, pPrimeCore 2 J = ⊥)
    (hSM : S ≤ M) (hMI : I ⊓ normalizer (Yplus : Set G) = M ⊓ I)
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (hFMI : generalizedFitting (M.subgroupOf I) = pCore 2 (M.subgroupOf I))
    {K : Subgroup I} (hK : K.IsCComponent) (hKM : K.map I.subtype ≤ M) :
    normalClosure (K : Set I) ≤ localActionKernel (centralInvolutions T) I := by
  let N := normalClosure (K : Set I)
  let D := N.map I.subtype
  have hNV : D ≤ centralizer (localModule T M : Set G) :=
    inside_normalClosure_centralizes_module a hI hSylow h25 hodd hSM hMI hY hFMI hK hKM
  have hIN : I ≤ normalizer (D : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using N.le_normalizer_map I.subtype
  have hZ : centralInvolutions T ≤ centralizer (D : Set G) :=
    le_centralizer_iff.mp (hNV.trans (centralizer_le (le_conjugateSpanBy _ _)))
  have hU : localSpan (centralInvolutions T) I ≤ centralizer (D : Set G) :=
    conjugateSpanBy_le hZ (hIN.trans (normalizer_le_normalizer_centralizer _))
  exact map_le_iff_le_comap.mp (le_centralizer_iff.mp hU)

/-- For a source C-component, containment in M is exactly containment in the normal action kernel. The reverse direction uses precisely 15.3.11(2). -/
theorem inside_iff_le_actionKernel {Yplus S M I : Subgroup G}
    (T : Sylow 2 G) (a : NaturalOrthogonalAction M (localModule T M))
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (h25 : ∀ J ∈ outsideFamily Yplus S M, generalizedFitting J ≠ pCore 2 J)
    (hodd : ∀ J ∈ outsideFamily Yplus S M, pPrimeCore 2 J = ⊥)
    (hSM : S ≤ M) (hMI : I ⊓ normalizer (Yplus : Set G) = M ⊓ I)
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (hFMI : generalizedFitting (M.subgroupOf I) = pCore 2 (M.subgroupOf I))
    (hC : I ⊓ centralizer (localSpan (centralInvolutions T) I : Set G) ≤ M ⊓ I)
    {K : Subgroup I} (hK : K.IsCComponent) :
    K.map I.subtype ≤ M ↔ K ≤ localActionKernel (centralInvolutions T) I := by
  constructor
  · intro hKM
    exact le_normalClosure.trans
      (inside_normalClosure_le_actionKernel T a hI hSylow h25 hodd hSM hMI hY hFMI hK hKM)
  · intro hKC
    apply map_le_iff_le_comap.mpr
    intro k hk
    exact (hC ⟨k.property, hKC hk⟩).1

/-- An exact reformulation of the outstanding exclusion. A nonsolvable normal kernel supplies a C-component of I, and an inside C-component makes the kernel nonsolvable. -/
theorem exclusion_iff_actionKernel_solvable {Yplus S M I : Subgroup G}
    (T : Sylow 2 G) (a : NaturalOrthogonalAction M (localModule T M))
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (h25 : ∀ J ∈ outsideFamily Yplus S M, generalizedFitting J ≠ pCore 2 J)
    (hodd : ∀ J ∈ outsideFamily Yplus S M, pPrimeCore 2 J = ⊥)
    (hSM : S ≤ M) (hMI : I ⊓ normalizer (Yplus : Set G) = M ⊓ I)
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (hFMI : generalizedFitting (M.subgroupOf I) = pCore 2 (M.subgroupOf I))
    (hC : I ⊓ centralizer (localSpan (centralInvolutions T) I : Set G) ≤ M ⊓ I) :
    (∀ K : Subgroup I, K.IsCComponent → ¬ K.map I.subtype ≤ M) ↔
      Group.IsSolvable (localActionKernel (centralInvolutions T) I) := by
  let C := localActionKernel (centralInvolutions T) I
  constructor
  · intro h
    by_contra hn
    obtain ⟨K, hK⟩ := exists_isCComponent_of_not_isSolvable hn
    have hm := hK.map_subtype (inferInstance : C.Normal).isSubnormal
    apply h _ hm
    exact (inside_iff_le_actionKernel T a hI hSylow h25 hodd hSM hMI hY hFMI hC hm).mpr
      (map_subtype_le K)
  · intro hs K hK hKM
    let : Group.IsSolvable C := hs
    have hKC := (inside_iff_le_actionKernel T a hI hSylow h25 hodd hSM hMI hY hFMI hC hK).mp hKM
    exact hK.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective (inclusion_injective hKC))

/-- The reduction with the actual standing constructions, including the orthogonal planes, the residual Y, and the two choices of Hypothesis 15.3.10. Solvability on the right remains unproved. -/
theorem source_exclusion_iff_actionKernel_solvable (d : CharacteristicTwo.LocalData G)
    {I : Subgroup G} (hI : I ∈ d.Hplus)
    (hSylow : OutsideSylowControl d.Yplus d.S d.M)
    (h25 : ∀ J ∈ d.Hplus, generalizedFitting J ≠ pCore 2 J)
    (hodd : ∀ J ∈ d.Hplus, pPrimeCore 2 J = ⊥)
    (hMI : I ⊓ normalizer (d.Yplus : Set G) = d.M ⊓ I)
    (hY : IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus))
    (hFMI : generalizedFitting (d.M.subgroupOf I) = pCore 2 (d.M.subgroupOf I))
    (hC : I ⊓ centralizer (d.UI I : Set G) ≤ d.M ⊓ I) :
    (∀ K : Subgroup I, K.IsCComponent → ¬ K.map I.subtype ≤ d.M) ↔
      Group.IsSolvable (localActionKernel d.Z I) :=
  exclusion_iff_actionKernel_solvable d.T d.action hI hSylow h25 hodd
    (inf_le_left.trans d.sylow_le) hMI hY hFMI hC

end CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure.InsideExclusion
