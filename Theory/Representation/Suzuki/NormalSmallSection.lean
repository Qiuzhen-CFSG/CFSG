module
public import Theory.Representation.Suzuki.SmallSection
public import Theory.Representation.Suzuki.BinaryDegree
public import Theory.Representation.Clifford
public import Mathlib.RepresentationTheory.Invariants

/-!
# Natural sections retaining a normal Suzuki actor

In an irreducible binary representation nontrivial on a normal Suzuki
subgroup, each simple constituent of that subgroup is faithful and has
degree at least 4(2m+1). Distinct Clifford conjugates would be disjoint
and require dimension at least 8(2m+1). Below that bound the constituent
is invariant under the entire actor, so restriction is irreducible.
The existing small-degree theorem then gives the natural module.

Perfect-section extraction applies this to an arbitrary small action,
retaining subspaces invariant under the entire actor. The consumer is the
actual HR_j radical action in Fong--Seitz I (6C), printed p.40. This is the
Clifford restriction step; it does not assume Cartan constituent weights.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Representation.SuzukiSmallDegree
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A nontrivial normal Suzuki restriction of an irreducible module of
dimension below twice the minimum degree is itself irreducible and natural. -/
theorem normal_restriction_natural (ρ : Representation (ZMod 2) G V)
    (hi : ρ.IsIrreducible) (K : Subgroup G) [K.Normal]
    {m : ℕ} (hm : 0 < m) (μ : K ≃* SuzukiMatrixGroup m)
    (hn : ¬ K ≤ ρ.ker) (hsmall : Module.finrank (ZMod 2) V < 8*(2*m+1)) :
    Representation.IsIrreducible (ρ.comp K.subtype) ∧
    Nonempty (Representation.Equiv (ρ.comp (K.subtype.comp μ.symm.toMonoidHom)) (SuzukiNatural.natural m)) := by
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : IsSimpleGroup K := μ.isSimpleGroup
  let := hi
  let := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨J,hJ⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp K.subtype)
  have hf : Function.Injective J.toRepresentation := by
    apply J.toRepresentation.ker_eq_bot_iff.mp
    rcases (inferInstance : J.toRepresentation.ker.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · let F : Subrepresentation ρ := {
        toSubmodule := Representation.invariants (ρ.comp K.subtype)
        apply_mem_toSubmodule := Representation.le_comap_invariants ρ K }
      have hJF : J.toSubmodule ≤ F.toSubmodule := by
        intro w hw k
        have he : J.toRepresentation k = 1 := show k ∈ J.toRepresentation.ker from ht ▸ mem_top _
        exact congrArg Subtype.val (LinearMap.congr_fun he (⟨w,hw⟩ : J))
      have hF : F ≠ ⊥ := by
        intro he
        have hb : J.toSubmodule = ⊥ := le_bot_iff.mp (by
          change J.toSubmodule ≤ (⊥ : Subrepresentation ρ).toSubmodule
          exact he ▸ hJF)
        exact ((Subrepresentation.irreducible_iff_isAtom J).mp hJ).ne_bot
          (Subrepresentation.toSubmodule_injective hb)
      have htF : F = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top F).resolve_left hF
      apply (hn ?_).elim
      intro k hk
      apply LinearMap.ext
      intro w
      have hw : w ∈ F.toSubmodule := by rw [htF]; trivial
      exact hw ⟨k,hk⟩
  have hdim : 4*(2*m+1) ≤ Module.finrank (ZMod 2) J.toSubmodule :=
    Representation.Suzuki.finrank_ge (by omega)
      (J.toRepresentation.comp μ.symm.toMonoidHom) (hf.comp μ.symm.injective)
  have he (g : G) : conjugateSubrepresentation ρ K J g = J := by
    by_contra hne
    have hJa := (Subrepresentation.irreducible_iff_isAtom J).mp hJ
    have hga : IsAtom (conjugateSubrepresentation ρ K J g) := by
      simpa only [conjugateSubrepresentationOrderIso_apply,inv_inv] using
        (((conjugateSubrepresentationOrderIso ρ K g⁻¹).isAtom_iff J).mpr hJa)
    have hd : Disjoint (conjugateSubrepresentation ρ K J g).toSubmodule J.toSubmodule :=
      disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule (hga.disjoint_of_ne hJa hne).eq_bot)
    have hdg := (conjugateSubrepresentationEquiv ρ K J g).toLinearEquiv.finrank_eq
    have hadd := Submodule.finrank_sup_add_finrank_inf_eq
      (conjugateSubrepresentation ρ K J g).toSubmodule J.toSubmodule
    rw [hd.eq_bot,finrank_bot,add_zero] at hadd
    have hle := Submodule.finrank_le
      ((conjugateSubrepresentation ρ K J g).toSubmodule ⊔ J.toSubmodule)
    omega
  have htop : J = ⊤ := by
    have hh := iSup_conjugateSubrepresentations_eq_top ρ K hi J hJ
    simpa only [he,ciSup_const] using hh
  have hir : Representation.IsIrreducible (ρ.comp K.subtype) :=
    isSimpleOrder_iff_isAtom_top.mpr (htop ▸ (Subrepresentation.irreducible_iff_isAtom J).mp hJ)
  have hinj : Function.Injective (ρ.comp K.subtype) := by
    apply (ρ.comp K.subtype).ker_eq_bot_iff.mp
    exact (inferInstance : (ρ.comp K.subtype).ker.Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => hn (fun k hk => show (⟨k,hk⟩ : K) ∈ (ρ.comp K.subtype).ker from ht ▸ mem_top _))
  have hir' : Representation.IsIrreducible (ρ.comp (K.subtype.comp μ.symm.toMonoidHom)) :=
    (Representation.irreducible_comp_surjective_iff μ.symm.toMonoidHom μ.symm.surjective
      (ρ.comp K.subtype)).mpr hir
  exact ⟨hir,natural_equiv_of_smallDegree (by omega) _ (hinj.comp μ.symm.injective) hir' (by omega)⟩

/-- A small action nontrivial on a normal Suzuki subgroup has a section
invariant under the whole actor, natural on restriction to the Suzuki group. -/
theorem exists_natural_normal_section (ρ : Representation (ZMod 2) G V)
    (K : Subgroup G) [K.Normal] {m : ℕ} (hm : 0 < m)
    (μ : K ≃* SuzukiMatrixGroup m) (hn : ¬ K ≤ ρ.ker)
    (hsmall : Module.finrank (ZMod 2) V < 8*(2*m+1)) :
    ∃ U : Subrepresentation ρ, ∃ N : Subrepresentation U.toRepresentation,
      N.quotientRepresentation.IsIrreducible ∧
      Representation.IsIrreducible (N.quotientRepresentation.comp K.subtype) ∧
      Nonempty (Representation.Equiv (N.quotientRepresentation.comp (K.subtype.comp μ.symm.toMonoidHom))
        (SuzukiNatural.natural m)) := by
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : Group.IsPerfect (SuzukiMatrixGroup m) := ⟨by
    rcases (inferInstance : (commutator (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with hb | ht
    · let : IsMulCommutative (SuzukiMatrixGroup m) := (commutator_eq_bot_iff _).mp hb
      exact (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm inferInstance).elim
    · exact ht⟩
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := μ.symm.toMonoidHom) μ.symm.surjective
  obtain ⟨U,N,hi,hn⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect K hn
  have hd : Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) < 8*(2*m+1) :=
    ((Submodule.finrank_quotient_le _).trans (Submodule.finrank_le U.toSubmodule)).trans_lt hsmall
  obtain ⟨hK,he⟩ := normal_restriction_natural N.quotientRepresentation hi K hm μ hn hd
  exact ⟨U,N,hi,hK,he⟩

end Representation.SuzukiSmallDegree
