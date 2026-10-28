module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# K-groups and transport of simple sections

For a class `C` of groups, this file uses the section-theoretic formulation of
the K-group condition.  A finite group `G` is a `C`-K-group when every
simple quotient of a subgroup of `G` belongs to `C`.  Quantifying over
surjective homomorphisms makes the condition independent of choices of normal
subgroups and gives direct pullback proofs for subgroups and quotients.
For a simple ambient group, a surjection from the whole group onto a
nontrivial target is an isomorphism. This gives K-group membership for every
proper section from the proper-subgroup hypothesis alone.

The class parameter is deliberately arbitrary.  In particular, this module
does not identify `C` with all finite groups or use any classification theorem.
The concrete known-simple class used by the quasithin development is supplied
at the CFSG layer. Transport itself does not require finiteness.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*
(1 March 2004 manuscript), §0.1 (p. 4), §A.2–A.3 (pp. 32–42).
-/

@[expose] public section

namespace KGroup

universe u

variable (C : (S : Type u) → [Group S] → Prop)

/-- A class of groups is closed under multiplicative isomorphism. -/
def IsIsoClosed : Prop :=
  ∀ {G H : Type u} [Group G] [Group H], G ≃* H → C G → C H

/--
`IsKGroup C G` says that every simple section of `G` lies in `C`.

We represent a section by a surjective homomorphism from a subgroup to a
simple target.  Its kernel is automatically normal.  The class can
depend on the group structure, not just its carrier type.
-/
def IsKGroup (G : Type u) [Group G] : Prop :=
  ∀ (S : Type u) [Group S], IsSimpleGroup S →
    ∀ (U : Subgroup G) (f : U →* S), Function.Surjective f → C S

/-- The source's induction hypothesis: all proper subgroups are K-groups. -/
def HasProperKSubgroups (G : Type u) [Group G] : Prop :=
  ∀ U : Subgroup G, U ≠ ⊤ → IsKGroup C U

theorem isKGroup_of_injective {G H : Type u} [Group G] [Group H]
    (hH : IsKGroup C H) (i : G →* H) (hi : Function.Injective i) : IsKGroup C G := by
  intro S _ hs U f hf
  let e := Subgroup.equivMapOfInjective U i hi
  exact hH S hs (U.map i) (f.comp e.symm.toMonoidHom) (hf.comp e.symm.surjective)

theorem isKGroup_of_subgroup {G : Type u} [Group G]
    (hG : IsKGroup C G) (H : Subgroup G) : IsKGroup C H :=
  isKGroup_of_injective C hG H.subtype H.subtype_injective

theorem isKGroup_of_quotient {G Q : Type u} [Group G]
    [Group Q] (hG : IsKGroup C G) (q : G →* Q)
    (hq : Function.Surjective q) : IsKGroup C Q := by
  intro S _ hs U f hf
  let W : Subgroup G := U.comap q
  let g : W →* U := q.subgroupComap U
  exact hG S hs W (f.comp g)
    (hf.comp (MonoidHom.subgroupComap_surjective_of_surjective q U hq))

theorem isKGroup_of_mulEquiv {G H : Type u} [Group G]
    [Group H] (hG : IsKGroup C G) (e : G ≃* H) :
    IsKGroup C H := by
  exact isKGroup_of_quotient C hG e.toMonoidHom e.surjective

theorem isKGroup_iff_mulEquiv {G H : Type u} [Group G]
    [Group H] (e : G ≃* H) :
    IsKGroup C G ↔ IsKGroup C H := by
  constructor
  · intro h
    exact isKGroup_of_mulEquiv C h e
  · intro h
    exact isKGroup_of_mulEquiv C h e.symm

/-- Every section of a `C`-K-group is again a `C`-K-group.
The denominator is intersected with the numerator via `subgroupOf`. -/
theorem isKGroup_of_section {G : Type u} [Group G]
    (hG : IsKGroup C G) (H N : Subgroup G)
    (hN : (N.subgroupOf H).Normal) :
    IsKGroup C (H ⧸ N.subgroupOf H) := by
  exact isKGroup_of_quotient C (isKGroup_of_subgroup C hG H)
    (QuotientGroup.mk' (nN := hN) (N.subgroupOf H))
    (QuotientGroup.mk'_surjective (nN := hN) (N.subgroupOf H))

/-- Membership of a simple K-group in the given class is a consequence,
not an axiom or part of the definition of the class. -/
theorem mem_of_isKGroup {G : Type u} [Group G] [IsSimpleGroup G]
    (hG : IsKGroup C G) : C G :=
  hG G inferInstance ⊤ Subgroup.topEquiv.toMonoidHom Subgroup.topEquiv.surjective

/-- For an isomorphism-closed class it suffices to test actual simple quotients. -/
theorem isKGroup_iff_simple_quotients {G : Type u} [Group G] (hC : IsIsoClosed C) :
    IsKGroup C G ↔ ∀ (U : Subgroup G) (N : Subgroup U) [N.Normal],
      IsSimpleGroup (U ⧸ N) → C (U ⧸ N) := by
  constructor
  · intro h U N _ hs
    exact h (U ⧸ N) hs U (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  · intro h S _ hs U f hf
    let := hs
    let e := QuotientGroup.quotientKerEquivOfSurjective f hf
    exact hC e (h U f.ker e.isSimpleGroup)

/-- Sections of a proper subgroup are K-groups under the induction hypothesis. -/
theorem isKGroup_of_proper_subgroup_surjective {G Q : Type u} [Group G] [Group Q]
    (hG : HasProperKSubgroups C G) (U : Subgroup G) (hU : U ≠ ⊤)
    (f : U →* Q) (hf : Function.Surjective f) : IsKGroup C Q :=
  isKGroup_of_quotient C (hG U hU) f hf

/-- In particular, every simple section of a proper subgroup lies in `C`. -/
theorem mem_of_proper_subgroup_surjective {G S : Type u} [Group G] [Group S]
    [IsSimpleGroup S] (hG : HasProperKSubgroups C G) (U : Subgroup G) (hU : U ≠ ⊤)
    (f : U →* S) (hf : Function.Surjective f) : C S :=
  mem_of_isKGroup C (isKGroup_of_proper_subgroup_surjective C hG U hU f hf)

theorem isKGroup_of_proper_section {G : Type u} [Group G]
    (hG : HasProperKSubgroups C G) (U : Subgroup G) (hU : U ≠ ⊤)
    (N : Subgroup U) [N.Normal] : IsKGroup C (U ⧸ N) :=
  isKGroup_of_proper_subgroup_surjective C hG U hU
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

theorem hasProperKSubgroups_of_isKGroup {G : Type u} [Group G]
    (hG : IsKGroup C G) : HasProperKSubgroups C G :=
  fun U _ => isKGroup_of_subgroup C hG U

/-- A proper subgroup of a quotient pulls back to a proper subgroup.
Thus the proper-K induction hypothesis passes to every surjective image. -/
theorem hasProperKSubgroups_of_surjective {G Q : Type u} [Group G] [Group Q]
    (hG : HasProperKSubgroups C G) (q : G →* Q) (hq : Function.Surjective q) :
    HasProperKSubgroups C Q := by
  intro U hU
  have hW : U.comap q ≠ ⊤ := by
    intro htop
    apply hU
    apply Subgroup.comap_injective hq
    simpa only [Subgroup.comap_top] using htop
  exact isKGroup_of_quotient C (hG (U.comap q) hW) (q.subgroupComap U)
    (q.subgroupComap_surjective_of_surjective U hq)

theorem hasProperKSubgroups_iff_mulEquiv {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) : HasProperKSubgroups C G ↔ HasProperKSubgroups C H :=
  ⟨fun h => hasProperKSubgroups_of_surjective C h e.toMonoidHom e.surjective,
    fun h => hasProperKSubgroups_of_surjective C h e.symm.toMonoidHom e.symm.surjective⟩

/-- The trivial group has no simple sections, regardless of the chosen class. -/
theorem isKGroup_of_subsingleton {G : Type u} [Group G] [Subsingleton G] :
    IsKGroup C G := by
  intro S _ hs U f hf
  let := hs
  exact (not_subsingleton S (hf.subsingleton)).elim

private theorem simple_surjective_injective {G Q : Type u} [Group G] [Group Q]
    [IsSimpleGroup G] [Nontrivial Q] (f : G →* Q) (hf : Function.Surjective f) :
    Function.Injective f := by
  rcases f.normal_ker.eq_bot_or_eq_top with hk | hk
  · exact f.ker_eq_bot_iff.mp hk
  · have heq : f = 1 := MonoidHom.ker_eq_top_iff.mp hk
    obtain ⟨y, hy⟩ := exists_ne (1 : Q)
    obtain ⟨x, rfl⟩ := hf y
    exact (hy (by simp [heq])).elim

/-- A simple section of a simple group with proper K-subgroups is either
the whole group up to isomorphism or belongs to the class. -/
theorem simple_section_equiv_or_mem {G S : Type u} [Group G] [Group S]
    [IsSimpleGroup G] [IsSimpleGroup S] (hG : HasProperKSubgroups C G)
    (U : Subgroup G) (f : U →* S) (hf : Function.Surjective f) :
    Nonempty (G ≃* S) ∨ C S := by
  by_cases hU : U = ⊤
  · subst U
    let g : G →* S := f.comp Subgroup.topEquiv.symm.toMonoidHom
    have hg : Function.Surjective g := hf.comp Subgroup.topEquiv.symm.surjective
    exact Or.inl ⟨MulEquiv.ofBijective g ⟨simple_surjective_injective g hg, hg⟩⟩
  · exact Or.inr (mem_of_proper_subgroup_surjective C hG U hU f hf)

/-- Once proper subgroups are K-groups, the remaining condition for a simple
group is its own membership in the isomorphism-closed class. -/
theorem isKGroup_iff_mem_of_simple {G : Type u} [Group G] [IsSimpleGroup G]
    (hC : IsIsoClosed C) (hG : HasProperKSubgroups C G) : IsKGroup C G ↔ C G := by
  refine ⟨mem_of_isKGroup C, ?_⟩
  intro hmem S _ hs U f hf
  let := hs
  rcases simple_section_equiv_or_mem C hG U f hf with he | hS
  · obtain ⟨e⟩ := he
    exact hC e hmem
  · exact hS

/-- Every proper section of a simple group is a K-group if all proper
subgroups are K-groups. Properness is stated intrinsically as the absence
of an isomorphism to the ambient group. For finite groups this includes
every section of strictly smaller order. -/
theorem isKGroup_of_section_not_equiv {G Q : Type u} [Group G] [Group Q]
    [IsSimpleGroup G] (hG : HasProperKSubgroups C G)
    (U : Subgroup G) (f : U →* Q) (hf : Function.Surjective f)
    (hproper : ¬ Nonempty (G ≃* Q)) : IsKGroup C Q := by
  by_cases hU : U = ⊤
  · subst U
    rcases subsingleton_or_nontrivial Q with hQ | hQ
    · let := hQ
      exact isKGroup_of_subsingleton C
    · let := hQ
      let g : G →* Q := f.comp Subgroup.topEquiv.symm.toMonoidHom
      have hg : Function.Surjective g := hf.comp Subgroup.topEquiv.symm.surjective
      exact (hproper ⟨MulEquiv.ofBijective g
        ⟨simple_surjective_injective g hg, hg⟩⟩).elim
  · exact isKGroup_of_proper_subgroup_surjective C hG U hU f hf

end KGroup
