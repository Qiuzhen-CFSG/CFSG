module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.Statement
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity
public import Theory.Representation.BinaryOffender.FlagCodimension
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.TwoCore


/-!
# Noncentral factors of the literal natural seed

For an irreducible commutator U=[S,L], every invariant flag of S has at most
one noncentral section: once a flag member has nonzero commutator, that
commutator is U, and every later quotient is central. Perfectness excludes
an exhaustive flag consisting entirely of central sections. This proves an
exact count of one without a semisimplicity assumption or an assumed chief
factor count.

The applications retain the actual LA-seed, restrict only to L, and prove
that C_V(O₂(LA))/U is central. They compare arbitrary exhaustive flags of
this fixed space and U. After the local core is identified with C_A(L), the
same result gives the factor count needed at the end of B.5.9; it never
identifies U with the whole fixed space.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108. These lemmas discharge the final central-quotient count,
not the preceding second-component and sharp-codimension arguments.
-/

@[expose] public section

open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource Theory.GroupTheory
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

noncomputable def noncentralFactors (c : ℕ → Subrepresentation ρ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter fun i =>
    ¬ ∀ g v, sectionRepresentation ρ (c i) (c (i + 1)) g v = v

private def commutatorSpace (S : Subrepresentation ρ) : Subrepresentation ρ where
  toSubmodule := subspaceCommutator ρ S.toSubmodule ⊤
  apply_mem_toSubmodule g v hv :=
    (subspaceCommutator_invariant ρ S.toSubmodule ⊤ (Subgroup.mem_top g) v).2 hv

private theorem commutatorSpace_le (S : Subrepresentation ρ) : commutatorSpace ρ S ≤ S :=
  subspaceCommutator_le_of_invariant ρ
    (le_subspaceStabilizer ρ _ (fun g _ _ hv => S.apply_mem_toSubmodule g hv))

private theorem one_noncentral_factor [Group.IsPerfect G]
    (U : Subrepresentation ρ) (hU : IsAtom U)
    (c : ℕ → Subrepresentation ρ) (hc : Monotone c) (n : ℕ)
    (hzero : c 0 = ⊥) (hcomm : commutatorSpace ρ (c n) = U) :
    (noncentralFactors ρ c n).card = 1 := by
  classical
  have hmem (i : ℕ) : i ∈ noncentralFactors ρ c n ↔
      i < n ∧ ¬ ∀ g v, sectionRepresentation ρ (c i) (c (i + 1)) g v = v := by
    simp [noncentralFactors]
  have hupper {i : ℕ} (hi : i ∈ noncentralFactors ρ c n) : U ≤ c (i + 1) := by
    obtain ⟨hin, hnon⟩ := (hmem i).mp hi
    have hle : commutatorSpace ρ (c (i + 1)) ≤ U := by
      rw [← hcomm]
      exact subspaceCommutator_mono_left ρ (hc (by omega)) ⊤
    have hne : commutatorSpace ρ (c (i + 1)) ≠ ⊥ := by
      intro he
      apply hnon
      intro g
      apply (sectionRepresentation_trivial_iff ρ _ _ g).mpr
      intro v hv
      have hv' : ρ g v - v ∈ (commutatorSpace ρ (c (i + 1))).toSubmodule :=
        Submodule.subset_span ⟨g, Subgroup.mem_top g, v, hv, rfl⟩
      rw [he] at hv'
      have hz : ρ g v - v = 0 := hv'
      rw [hz]
      exact (c i).toSubmodule.zero_mem
    rw [← (hU.le_iff_eq hne).mp hle]
    exact commutatorSpace_le ρ _
  have hlower {i : ℕ} (hi : i ∈ noncentralFactors ρ c n) : ¬ U ≤ c i := by
    intro hui
    obtain ⟨hin, hnon⟩ := (hmem i).mp hi
    apply hnon
    intro g
    apply (sectionRepresentation_trivial_iff ρ _ _ g).mpr
    intro v hv
    apply hui
    rw [← hcomm]
    exact Submodule.subset_span ⟨g, Subgroup.mem_top g, v, hc (by omega) hv, rfl⟩
  have hone : (noncentralFactors ρ c n).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    rcases lt_trichotomy i j with hlt | he | hgt
    · exact (hlower hj ((hupper hi).trans (hc (by omega)))).elim
    · exact he
    · exact (hlower hi ((hupper hj).trans (hc (by omega)))).elim
  have hnonempty : (noncentralFactors ρ c n).Nonempty := by
    by_contra hn
    have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
    have htriv : ∀ i < n, ∀ g v, sectionRepresentation ρ (c i) (c (i + 1)) g v = v := by
      intro i hi
      by_contra hn
      have hh := (hmem i).mpr ⟨hi, hn⟩
      rw [hempty] at hh
      exact Finset.notMem_empty i hh
    let : Group.IsPerfect (⊤ : Subgroup G) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := G)).symm.toMonoidHom)
        Subgroup.topEquiv.symm.surjective
    have hfix := le_fixedSpace_of_central_flag ρ ⊤ c hzero n
      (fun i hi g _ => htriv i hi g)
    have hz := (subspaceCommutator_eq_bot_iff ρ (c n).toSubmodule ⊤).mpr hfix
    apply hU.ne_bot
    rw [← hcomm]
    exact Subrepresentation.toSubmodule_injective hz
  have := Finset.card_pos.mpr hnonempty
  omega

private theorem commutator_atom_self [Group.IsPerfect G]
    (S U : Subrepresentation ρ) (hU : IsAtom U) (hcomm : commutatorSpace ρ S = U) :
    commutatorSpace ρ U = U := by
  apply (hU.le_iff_eq _).mp (commutatorSpace_le ρ U)
  intro hz
  have hcentral : U.toSubmodule ≤ fixedSpace ρ ⊤ :=
    (subspaceCommutator_eq_bot_iff ρ U.toSubmodule ⊤).mp
      (congrArg Subrepresentation.toSubmodule hz)
  let : Group.IsPerfect (⊤ : Subgroup G) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := G)).symm.toMonoidHom)
      Subgroup.topEquiv.symm.surjective
  have hS := le_fixedSpace_of_commutator_le_fixedSpace ρ ⊤ S.toSubmodule
    (le_subspaceStabilizer ρ _ (fun g _ _ hv => S.apply_mem_toSubmodule g hv))
    (by change (commutatorSpace ρ S).toSubmodule ≤ _; rwa [hcomm])
  apply hU.ne_bot
  rw [← hcomm]
  exact Subrepresentation.toSubmodule_injective
    ((subspaceCommutator_eq_bot_iff ρ S.toSubmodule ⊤).mpr hS)

/-- The seed with its actual restricted L-action. -/
noncomputable def componentSpace {A L : Subgroup G} (seed : NaturalSeed ρ A L) :
    Subrepresentation (ρ.comp L.subtype) where
  toSubmodule := seed.space.toSubmodule
  apply_mem_toSubmodule l _ hv :=
    seed.space.apply_mem_toSubmodule ⟨l, (show L ≤ L ⊔ A from le_sup_left) l.property⟩ hv

/-- The compatible natural coordinates imply irreducibility on L. -/
theorem componentSpace_isAtom {A L : Subgroup G} (seed : NaturalSeed ρ A L) :
    IsAtom (componentSpace ρ seed) := by
  apply (Subrepresentation.irreducible_iff_isAtom _).mp
  exact ExtensionConsequences.irreducible_of_equiv seed.natural
    (ExtensionConsequences.linearNatural_irreducible seed.field (by decide))

private theorem core_normalized (A L : Subgroup G) :
    L ≤ normalizer (localTwoCore L A : Set G) := by
  have hn := (pCore 2 ↥(L ⊔ A)).le_normalizer_map (L ⊔ A).subtype
  rw [normalizer_eq_top_iff.mpr (inferInstance : (pCore 2 ↥(L ⊔ A)).Normal),
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hn
  exact le_sup_left.trans hn

/-- The two-core fixed space is invariant under L, without asserting G-invariance. -/
noncomputable def coreFixedSpace (A L : Subgroup G) : Subrepresentation (ρ.comp L.subtype) where
  toSubmodule := fixedSpace ρ (localTwoCore L A)
  apply_mem_toSubmodule l v hv := by
    exact (fixedSpace_invariant_normalizer ρ (core_normalized A L) l.property v).2 hv

private theorem restrict_commutator (L : Subgroup G) (S : Submodule (ZMod 2) V) :
    subspaceCommutator (ρ.comp L.subtype) S ⊤ = subspaceCommutator ρ S L := by
  unfold subspaceCommutator
  congr 1
  ext v
  constructor
  · rintro ⟨l, _, w, hw, he⟩
    exact ⟨l, l.property, w, hw, he⟩
  · rintro ⟨l, hl, w, hw, he⟩
    exact ⟨⟨l, hl⟩, Subgroup.mem_top _, w, hw, he⟩

private theorem seed_commutator {A L : Subgroup G} (seed : NaturalSeed ρ A L) :
    commutatorSpace (ρ.comp L.subtype) (coreFixedSpace ρ A L) = componentSpace ρ seed := by
  apply Subrepresentation.toSubmodule_injective
  change subspaceCommutator (ρ.comp L.subtype) _ ⊤ = seed.space.toSubmodule
  rw [restrict_commutator, seed.space_eq]
  rfl

/-- The natural seed is contained in the literal moved space W. -/
theorem seed_le_moved {A L : Subgroup G} (seed : NaturalSeed ρ A L) :
    seed.space.toSubmodule ≤ moved ρ L := by
  rw [seed.space_eq]
  exact subspaceCommutator_mono_left ρ le_top L

/-- The quotient C_V(O₂(LA))/U is central for L. This is the quotient
needed in the last sentence of B.5.9; the two spaces need not be equal. -/
theorem coreFixedSpace_quotient_central {A L : Subgroup G} (seed : NaturalSeed ρ A L)
    (l : L) (v) :
    sectionRepresentation (ρ.comp L.subtype) (componentSpace ρ seed)
      (coreFixedSpace ρ A L) l v = v := by
  apply (sectionRepresentation_trivial_iff (ρ.comp L.subtype) _ _ l).mpr
  intro w hw
  change ρ (l : G) w - w ∈ seed.space.toSubmodule
  rw [seed.space_eq]
  exact Submodule.subset_span ⟨l, l.property, w, hw, rfl⟩

/-- Every exhaustive invariant flag of C_V(O₂(LA)) has exactly one
noncentral L-section, as does its irreducible commutator U. -/
theorem coreFixedSpace_noncentralFactors {A L : Subgroup G}
    (seed : NaturalSeed ρ A L) [Group.IsPerfect L]
    (c : ℕ → Subrepresentation (ρ.comp L.subtype)) (hc : Monotone c) (n : ℕ)
    (hzero : c 0 = ⊥) (hstop : c n = coreFixedSpace ρ A L) :
    (noncentralFactors (ρ.comp L.subtype) c n).card = 1 := by
  apply one_noncentral_factor (ρ.comp L.subtype) (componentSpace ρ seed)
    (componentSpace_isAtom ρ seed) c hc n hzero
  rw [hstop]
  exact seed_commutator ρ seed

/-- The central quotient does not change the number of noncentral sections,
for any two exhaustive invariant flags of the fixed space and its seed. -/
theorem coreFixedSpace_noncentralFactors_eq_seed {A L : Subgroup G}
    (seed : NaturalSeed ρ A L) [Group.IsPerfect L]
    (c d : ℕ → Subrepresentation (ρ.comp L.subtype))
    (hc : Monotone c) (hd : Monotone d) (n r : ℕ)
    (hc0 : c 0 = ⊥) (hd0 : d 0 = ⊥)
    (hcn : c n = coreFixedSpace ρ A L) (hdr : d r = componentSpace ρ seed) :
    (noncentralFactors (ρ.comp L.subtype) c n).card =
      (noncentralFactors (ρ.comp L.subtype) d r).card := by
  rw [coreFixedSpace_noncentralFactors ρ seed c hc n hc0 hcn]
  symm
  apply one_noncentral_factor (ρ.comp L.subtype) (componentSpace ρ seed)
    (componentSpace_isAtom ρ seed) d hd r hd0
  rw [hdr]
  exact commutator_atom_self (ρ.comp L.subtype) (coreFixedSpace ρ A L)
    (componentSpace ρ seed) (componentSpace_isAtom ρ seed) (seed_commutator ρ seed)

/-- The source consumer after identifying O₂(LA)=C_A(L). Central summands
in C_V(C_A(L)) do not alter the one noncentral factor supplied by U. -/
theorem centralizerFixedSpace_noncentralFactors {A L : Subgroup G}
    (seed : NaturalSeed ρ A L) (hL : IsComponent G L)
    (hcore : localTwoCore L A = A ⊓ centralizer (L : Set G))
    (c : ℕ → Subrepresentation (ρ.comp L.subtype)) (hc : Monotone c) (n : ℕ)
    (hzero : c 0 = ⊥)
    (hstop : (c n).toSubmodule = fixedSpace ρ (A ⊓ centralizer (L : Set G))) :
    (noncentralFactors (ρ.comp L.subtype) c n).card = 1 := by
  let : Theory.GroupTheory.IsQuasisimple L := hL.2
  apply coreFixedSpace_noncentralFactors ρ seed c hc n hzero
  apply Subrepresentation.toSubmodule_injective
  change (c n).toSubmodule = fixedSpace ρ (localTwoCore L A)
  rw [hcore]
  exact hstop

/-- Once the rank equality splits the offender, C_V(C_A(L)) has exactly
one noncentral L-factor. Neither the core identity nor the factor count
is an input to this application. -/
theorem noncentralFactors_of_split [Finite G] {A L : Subgroup G}
    (seed : NaturalSeed ρ A L) (hL : IsComponent G L)
    (hA : IsMinimalBestOffender ρ A)
    (hsplit : A ≤ L ⊔ (A ⊓ centralizer (L : Set G)))
    (c : ℕ → Subrepresentation (ρ.comp L.subtype)) (hc : Monotone c) (n : ℕ)
    (hzero : c 0 = ⊥)
    (hstop : (c n).toSubmodule = fixedSpace ρ (A ⊓ centralizer (L : Set G))) :
    (noncentralFactors (ρ.comp L.subtype) c n).card = 1 :=
  centralizerFixedSpace_noncentralFactors ρ seed hL
    (localTwoCore_eq_centralizer_of_split ρ seed hL hA.1.1.2 hsplit)
    c hc n hzero hstop

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
