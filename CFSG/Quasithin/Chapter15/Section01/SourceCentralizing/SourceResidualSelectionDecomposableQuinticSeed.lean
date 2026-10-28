module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableMaximal
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ProperOrbitFactors
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OrbitUniqueness
public import Theory.Representation.CyclotomicPrimeCyclicity

/-!
# The original starred seed span in the quintic decomposable row

The two literal quintic factors are irreducible on their four-dimensional
supports. If the original central seed had proper span under J-hat, the
proved proper-orbit argument would produce a nonzero proper invariant
subspace on one of these same factors. Hence J-hat's actual preimage already
spans the full original module. The ordering uniqueness theorem then forbids
an intersection with a distinct maximal local from containing all of J-hat.

This argument retains the original two supports and permits additional cubic
actors outside J-hat. It uses neither global residual control nor maximality
of the whole Sylow action image.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

private theorem irreducible_of_restriction
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (A : Subgroup D)
    (hi : IsIrreducible (ρ.comp A.subtype)) : IsIrreducible ρ := by
  let : Nontrivial W := by
    let := hi
    exact Subrepresentation.irreducible_module_nontrivial (ρ.comp A.subtype)
  refine ⟨fun S => ?_⟩
  let R : Subrepresentation (ρ.comp A.subtype) := {
    toSubmodule := S.toSubmodule
    apply_mem_toSubmodule := fun g v hv => S.apply_mem_toSubmodule g hv }
  rcases hi.eq_bot_or_eq_top R with h | h
  · have hh : S.toSubmodule = ⊥ :=
      congrArg (fun X : Subrepresentation (ρ.comp A.subtype) => X.toSubmodule) h
    exact Or.inl (Subrepresentation.toSubmodule_injective hh)
  · have hh : S.toSubmodule = ⊤ :=
      congrArg (fun X : Subrepresentation (ρ.comp A.subtype) => X.toSubmodule) h
    exact Or.inr (Subrepresentation.toSubmodule_injective hh)

/-- The original prime-five factors make the actual J-hat preimage span the
whole chosen module from its unchanged central seed. -/
theorem PreparedChosenModule.decomposable_five_starred_seed_span
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π → s.prime = 5 →
      V = conjugateSpanBy (centralInvolutions T ⊓ V)
        (((Jhat (imageRepresentation M V h.normalized)).comap
          (actionHom M V h.normalized).rangeRestrict).map M.subtype) := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hfive
  let V := localModule T M
  let D := internalActionImage M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  let f := (actionHom M V h.normalized).rangeRestrict
  let K := Jhat ρ
  let Z := AddSubgroup.toZModSubmodule 2 ((centralInvolutions T).subgroupOf V).toAddSubgroup
  have hirr (k : d.Index) : IsIrreducible (d.factor k).action := by
    let l := s.marking k
    apply irreducible_of_restriction (d.factor k).action l.kernel
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hc : Nat.card l.kernel = 5 := (s.dihedral k).card_kernel.trans hfive
    apply CyclotomicPrimeCyclicity.irreducible_of_prime_card (r := 5) hc
      (by decide) (by norm_num) ((d.factor k).action.comp l.kernel.subtype)
      ((d.factor k).faithful.comp l.kernel.subtype_injective)
    norm_num only [ZMod.card,Nat.cast_ofNat]
    rw [BinaryPrimeDegree.orderOf_two_mod_five,
      (s.dihedral k).dimension]
  obtain ⟨_,_,_,_,_,i,j,_,_,hgen,_,_,hcompl,t,_,htij,_⟩ := hdec
  have hOA : c.orbitActor d π i = K := by
    apply le_antisymm (c.orbitActor_le d π i)
    apply hgen.ge.trans
    apply sup_le
    · simpa only [map_one,Equiv.Perm.one_apply,FactorData.orbitActor,FactorData.orbitSpace] using
        le_iSup (fun g : D => (c.ambientFactor d (π g i)).actor) 1
    · exact htij ▸ le_iSup (fun g : D => (c.ambientFactor d (π g i)).actor) (f t)
  have hOS : c.orbitSpace d π i = ⊤ := by
    apply top_unique
    rw [←hcompl.sup_eq_top]
    apply sup_le
    · simpa only [map_one,Equiv.Perm.one_apply,FactorData.orbitActor,FactorData.orbitSpace] using
        le_iSup (fun g : D => (c.ambientFactor d (π g i)).space) 1
    · exact htij ▸ le_iSup (fun g : D => (c.ambientFactor d (π g i)).space) (f t)
  have hspan : Homogeneous.orbitSpan ρ K Z = ⊤ := by
    by_contra hn
    have hproper : Homogeneous.orbitSpan ρ (c.orbitActor d π i)
        (Z ⊓ c.orbitSpace d π i) < c.orbitSpace d π i := by
      rw [hOA,hOS,inf_top_eq]
      exact lt_top_iff_ne_top.mpr hn
    obtain ⟨k,_,B,hB0,hB,hstable⟩ :=
      source_localAction_proper_orbit_factor_reducible hG T hM U c d hd π hp hs i hproper
    exact (c.ambientFactor d k).not_irreducible_of_proper_subspace B hB0 hB
      (le_sup_left.trans hstable) (hirr k)
  let X := (K.comap f).map M.subtype
  let L := conjugateSpanBy (centralInvolutions T ⊓ V) X
  let C := AddSubgroup.toZModSubmodule 2 (L.subgroupOf V).toAddSubgroup
  have hseed : Z ≤ C := by
    intro z hz
    exact le_conjugateSpanBy _ _ ⟨hz,z.toMul.property⟩
  have hstable : K ≤ subspaceStabilizer ρ C := by
    apply le_subspaceStabilizer
    intro a ha v hv
    obtain ⟨m,rfl⟩ := (actionHom M V h.normalized).rangeRestrict_surjective a
    exact le_normalizer_iff.mp (le_normalizer_conjugateSpanBy _ _)
      (m : G) (mem_map_of_mem M.subtype ha) (v.toMul : G) hv
  have htop : (⊤ : Submodule (ZMod 2) (Additive V)) ≤ C :=
    hspan ▸ Homogeneous.orbitSpan_le ρ hseed hstable
  apply le_antisymm
  · intro v hv
    exact htop (show Additive.ofMul (⟨v,hv⟩ : V) ∈
      (⊤ : Submodule (ZMod 2) (Additive V)) from Submodule.mem_top)
  · exact conjugateSpanBy_le inf_le_right ((map_subtype_le _).trans h.normalized)

/-- An actual intersection with a distinct maximal two-local cannot contain
all of the original J-hat in the prime-five decomposable row. -/
theorem PreparedChosenModule.decomposable_five_third_image_not_contains
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π → s.prime = 5 →
      N ∈ maximalTwoLocalOvergroups (T : Subgroup G) → N ≠ M →
      ¬ Jhat (imageRepresentation M V h.normalized) ≤
        ((M ⊓ N).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hfive hN hNM hKA
  let f := (actionHom M V h.normalized).rangeRestrict
  let K := Jhat (imageRepresentation M V h.normalized)
  let X := (K.comap f).map M.subtype
  let H := M ⊓ N
  have hXM : X ≤ M := map_subtype_le _
  have hspan := h.decomposable_five_starred_seed_span hG T hM hfull
    c d hd s π hp hs hdec hfive
  have himage : (X.subgroupOf M).map (actionHom M V h.normalized) ≤
      (H.subgroupOf M).map (actionHom M V h.normalized) := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hyx⟩ := hx
    have hxy : y = x := Subtype.ext hyx
    subst y
    obtain ⟨z,hz,hzx⟩ := hKA hy
    exact ⟨z,hz,congrArg Subtype.val hzx⟩
  have huniq := Section02.source_unique_overgroup_of_action_image hG T hempty hM hJ h
    (le_inf hM.1.2 hN.2) inf_le_left hXM hspan himage
  exact hNM (Set.mem_singleton_iff.mp (huniq ▸
    (show N ∈ maximalTwoLocalOvergroups H from ⟨hN.1,inf_le_right⟩)))

end CFSG.Quasithin.Chapter15.Section01
