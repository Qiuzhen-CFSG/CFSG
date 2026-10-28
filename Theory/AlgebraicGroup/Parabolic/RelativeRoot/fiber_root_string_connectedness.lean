module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.fiber_unique_max_root
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.source_rootspan_bridge

/-!
Root-string connectedness for a nonzero relative-root fiber.  We identify the
fiber with a rational root fiber, move each root to a minimal-height element of
its parabolic Weyl orbit, and apply the minimal-root lemma to the two resulting
roots.  A simple reflection in `J` is itself one edge of the required graph,
and the source span bridge turns the final rational subsystem root into an
actual `RootSubsystemSpan` root.

This is the rational root-system step used in the GLS3 section 1.14
representation argument.
-/

universe u

namespace Theory.AlgebraicGroup

open Set
local notation "Submodule" => _root_.Submodule

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] in
private lemma source_simple_set
    (S : RelativeRootRepresentationSource K) :
    (S.base.support : Set S.D.Root) = S.D.simple := by
  ext a
  exact (S.rootSystemRealization.2.2.2.1 a).symm

omit [IsAlgClosed k] in
private lemma source_J_subset_support
    (S : RelativeRootRepresentationSource K) :
    S.J ⊆ S.base.support := by
  intro a ha
  exact (S.rootSystemRealization.2.2.2.1 a).1 (S.J_simple ha)

omit [IsAlgClosed k] in
private lemma source_height_eq
    (S : RelativeRootRepresentationSource K) (a : S.D.Root) :
    RelativeRootHeight S.coeff S.base.support S.J a =
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J a := by
  have h : S.base.support = S.D.simple.toFinite.toFinset := by
    ext a
    simp only [Set.Finite.mem_toFinset]
    exact (S.rootSystemRealization.2.2.2.1 a).symm
  rw [h]

omit [IsAlgClosed k] in
private lemma source_fiber_iff
    (S : RelativeRootRepresentationSource K) (a : S.D.Root) :
    a ∈ relativeRootFiberAtHeight S.D S.coeff S.J S.height S.root ↔
      (S.pairing.root a - S.pairing.root S.root ∈
          Submodule.span ℚ (S.pairing.root '' S.J) ∧
        RelativeRootHeight S.coeff S.base.support S.J a = S.height) := by
  let _ := Fintype.ofFinite S.D.Root
  constructor
  · intro ha
    refine ⟨?_, ?_⟩
    · exact root_sub_mem_span_of_projection_eq S.pairing S.base S.J
        S.coeff S.simpleRootExpansion (by
          simpa [RelativeRootFiber, source_simple_set S] using ha.1.2)
    · exact (source_height_eq S a).trans ha.2
  · rintro ⟨hspan, hheight⟩
    refine ⟨⟨Set.mem_univ a, ?_⟩, (source_height_eq S a).symm.trans hheight⟩
    simpa [source_simple_set S] using
      projection_eq_of_root_sub_mem_span S.pairing S.base S.J
        (source_J_subset_support S) S.coeff S.simpleRootExpansion hspan

omit [IsAlgClosed k] in
private lemma source_rootFiber_mem
    (S : RelativeRootRepresentationSource K) {a : S.D.Root}
    (ha : a ∈ relativeRootFiberAtHeight S.D S.coeff S.J S.height S.root) :
    a ∈ rootFiber S.pairing S.J (S.pairing.root S.root) :=
  (source_fiber_iff S a).mp ha |>.1

omit [IsAlgClosed k] in
private lemma source_root_not_span
    (S : RelativeRootRepresentationSource K) :
    S.pairing.root S.root ∉
      Submodule.span ℚ (S.pairing.root '' S.J) := by
  let _ := Fintype.ofFinite S.D.Root
  intro hspan
  have hproj := root_mem_span_projection_zero S.pairing S.base S.J
    (source_J_subset_support S) S.coeff S.simpleRootExpansion hspan
  have hzero := relativeRootHeight_eq_zero_of_projection_eq_zero
    S.coeff S.base.support S.J hproj
  have hroot := (source_fiber_iff S S.root).mp
    (show S.root ∈ relativeRootFiberAtHeight S.D S.coeff S.J S.height S.root from
      ⟨⟨Set.mem_univ _, rfl⟩, S.root_height⟩)
  have hheight : RelativeRootHeight S.coeff S.base.support S.J S.root = S.height := hroot.2
  have hpos : (0 : ℤ) < S.height := by exact_mod_cast S.height_pos
  omega

omit [IsAlgClosed k] in
private lemma edge_symm
    (S : RelativeRootRepresentationSource K)
    {α β : {a : S.D.Root // a ∈
      relativeRootFiberAtHeight S.D S.coeff S.J S.height S.root}}
    (h : ∃ δ : S.D.Root, δ ∈ RootSubsystemSpan S.D S.J ∧
      ∃ n : ℤ, S.pairing.root β.1 =
        S.pairing.root α.1 + n • S.pairing.root δ) :
    ∃ δ : S.D.Root, δ ∈ RootSubsystemSpan S.D S.J ∧
      ∃ n : ℤ, S.pairing.root α.1 =
        S.pairing.root β.1 + n • S.pairing.root δ := by
  rcases h with ⟨δ, hδ, n, hroot⟩
  refine ⟨S.D.neg δ, ?_, n, ?_⟩
  · change S.D.rootWeight (S.D.neg δ) ∈
      Subgroup.closure (S.D.rootWeight '' S.J)
    change S.D.rootWeight δ ∈
      Subgroup.closure (S.D.rootWeight '' S.J) at hδ
    rw [S.isRealization.2.2.2.1 δ]
    exact Subgroup.inv_mem _ hδ
  · have hneg : S.pairing.root (S.D.neg δ) = -S.pairing.root δ := by
      rw [show S.D.neg δ = S.pairing.reflectionPerm δ δ by
        simpa using S.rootSystemRealization.2.2.1 δ,
        S.pairing.root_reflectionPerm, S.pairing.reflection_apply_self]
    rw [hneg, hroot]
    simp

omit [IsAlgClosed k] in
private lemma rtg_symm
    (S : RelativeRootRepresentationSource K)
    {α β : {a : S.D.Root // a ∈
      relativeRootFiberAtHeight S.D S.coeff S.J S.height S.root}}
    (h : Relation.ReflTransGen
      (fun α β => ∃ δ : S.D.Root, δ ∈ RootSubsystemSpan S.D S.J ∧
        ∃ n : ℤ, S.pairing.root β.1 =
          S.pairing.root α.1 + n • S.pairing.root δ) α β) :
    Relation.ReflTransGen
      (fun α β => ∃ δ : S.D.Root, δ ∈ RootSubsystemSpan S.D S.J ∧
        ∃ n : ℤ, S.pairing.root β.1 =
          S.pairing.root α.1 + n • S.pairing.root δ) β α := by
  induction h with
  | refl => exact .refl
  | tail hpath hstep ih =>
      exact (Relation.ReflTransGen.single (edge_symm S hstep)).trans ih

omit [IsAlgClosed k] in
private lemma fiber_of_weyl
    (S : RelativeRootRepresentationSource K)
    (x : S.pairing.weylGroup) (hx : x ∈ parabolicWeylSubgroup S.pairing S.J)
    {a : S.D.Root}
    (ha : a ∈ relativeRootFiberAtHeight S.D S.coeff S.J S.height S.root) :
    S.pairing.weylGroupToPerm x a ∈
      relativeRootFiberAtHeight S.D S.coeff S.J S.height S.root := by
  let _ := Fintype.ofFinite S.D.Root
  apply (source_fiber_iff S _).2
  have hroot := parabolicWeylSubgroup_rootFiber_invariant S.pairing S.J
    (S.pairing.root S.root) ⟨x, hx⟩ a (source_rootFiber_mem S ha)
  refine ⟨hroot, ?_⟩
  have hheight := parabolicWeylSubgroup_relativeRootHeight_eq S.pairing
    S.base S.J (source_J_subset_support S) S.coeff S.simpleRootExpansion
      ⟨x, hx⟩ a
  exact hheight.trans ((source_fiber_iff S a).mp ha).2

private lemma parabolic_path
    (S : RelativeRootRepresentationSource K)
    (a : {b : S.D.Root // b ∈
      relativeRootFiberAtHeight S.D S.coeff S.J S.height S.root})
    (x : S.pairing.weylGroup) (hx : x ∈ parabolicWeylSubgroup S.pairing S.J) :
      Relation.ReflTransGen
        (fun α β => ∃ δ : S.D.Root, δ ∈ RootSubsystemSpan S.D S.J ∧
          ∃ n : ℤ, S.pairing.root β.1 =
            S.pairing.root α.1 + n • S.pairing.root δ)
        a ⟨S.pairing.weylGroupToPerm x a.1, fiber_of_weyl S x hx a.2⟩ := by
  let _ := Fintype.ofFinite S.D.Root
  induction hx using Subgroup.closure_induction generalizing a with
  | mem x hx =>
      rcases hx with ⟨j, rfl⟩
      let b := a.1
      refine Relation.ReflTransGen.single ⟨j, ?_, -S.pairing.pairingIn ℤ b j, ?_⟩
      · apply (S.root_mem_span_iff_mem_rootSubsystemSpan j).mp
        exact Submodule.subset_span ⟨j, j.2, rfl⟩
      · change S.pairing.root (S.pairing.weylGroupToPerm
            (RootPairing.weylGroup.ofIdx S.pairing (j : S.D.Root)) b) =
          S.pairing.root b + -S.pairing.pairingIn ℤ b (j : S.D.Root) •
            S.pairing.root (j : S.D.Root)
        have hperm : S.pairing.weylGroupToPerm
            (RootPairing.weylGroup.ofIdx S.pairing (j : S.D.Root)) b =
            S.pairing.reflectionPerm (j : S.D.Root) b := by
          change (RootPairing.Equiv.reflection S.pairing (j : S.D.Root)).indexEquiv b = _
          rfl
        rw [hperm]
        rw [S.pairing.root_reflectionPerm, S.pairing.reflection_apply_root' ℤ]
        simp [sub_eq_add_neg]
  | one => exact Relation.ReflTransGen.refl
  | mul x y hx hy ihx ihy =>
      simpa [map_mul] using
        (ihy a).trans (ihx ⟨S.pairing.weylGroupToPerm y a.1,
          fiber_of_weyl S y hy a.2⟩)
  | inv x hx ihx =>
      apply rtg_symm S
      simpa using ihx ⟨S.pairing.weylGroupToPerm x⁻¹ a.1,
        fiber_of_weyl S x⁻¹ (Subgroup.inv_mem _ hx) a.2⟩

public theorem RelativeRootRepresentationSource.fiber_root_string_connected
    (S : RelativeRootRepresentationSource K)
    (alpha beta : {gamma : S.D.Root // gamma ∈
      relativeRootFiberAtHeight S.D S.coeff S.J S.height S.root}) :
    Relation.ReflTransGen
      (fun alpha beta => ∃ delta : S.D.Root, delta ∈ RootSubsystemSpan S.D S.J ∧
        ∃ n : Int, S.pairing.root beta.1 =
          S.pairing.root alpha.1 + n • S.pairing.root delta) alpha beta := by
  let _ := Fintype.ofFinite S.D.Root
  let P := S.pairing
  let base := S.base
  have hJ := source_J_subset_support S
  obtain ⟨wa, hwa⟩ := exists_parabolicWeylSubgroup_baseHeight_minimal
    P base S.J alpha.1
  obtain ⟨wb, hwb⟩ := exists_parabolicWeylSubgroup_baseHeight_minimal
    P base S.J beta.1
  let alpha' := P.weylGroupToPerm wa.1 alpha.1
  let beta' := P.weylGroupToPerm wb.1 beta.1
  have ha' : alpha' ∈ relativeRootFiberAtHeight S.D S.coeff S.J S.height S.root :=
    fiber_of_weyl S wa.1 wa.2 alpha.2
  have hb' : beta' ∈ relativeRootFiberAtHeight S.D S.coeff S.J S.height S.root :=
    fiber_of_weyl S wb.1 wb.2 beta.2
  have ha'min : ∀ w : parabolicWeylSubgroup P S.J,
      base.height alpha' ≤ base.height (P.weylGroupToPerm w.1 alpha') := by
    intro w
    simpa [alpha', map_mul] using hwa (w * wa)
  have hb'min : ∀ w : parabolicWeylSubgroup P S.J,
      base.height beta' ≤ base.height (P.weylGroupToPerm w.1 beta') := by
    intro w
    simpa [beta', map_mul] using hwb (w * wb)
  have hmid : Relation.ReflTransGen
      (fun α β : {a : S.D.Root // a ∈
        relativeRootFiberAtHeight S.D S.coeff S.J S.height S.root} =>
        ∃ δ : S.D.Root, δ ∈ RootSubsystemSpan S.D S.J ∧
          ∃ n : ℤ, P.root β.1 = P.root α.1 + n • P.root δ)
      ⟨alpha', ha'⟩ ⟨beta', hb'⟩ := by
    by_cases heq : alpha' = beta'
    · have hab : (⟨alpha', ha'⟩ : {a : S.D.Root // a ∈
          relativeRootFiberAtHeight S.D S.coeff S.J S.height S.root}) = ⟨beta', hb'⟩ := by
        exact Subtype.ext heq
      rw [hab]
    · obtain ⟨delta, hdelta, hspan⟩ := rootFiber_minimal_sub_isRoot_ordered
        P base S.J hJ (P.root S.root) (source_root_not_span S)
        alpha' beta'
        (source_rootFiber_mem S ha') (source_rootFiber_mem S hb')
        heq ha'min hb'min
      exact Relation.ReflTransGen.single ⟨delta,
        (S.root_mem_span_iff_mem_rootSubsystemSpan delta).mp hspan, -1, by
          rw [hdelta]
          abel⟩
  exact (parabolic_path S alpha wa.1 wa.2).trans
    (hmid.trans (rtg_symm S (parabolic_path S beta wb.1 wb.2)))

end Theory.AlgebraicGroup
