module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.ExceptionalSplitting.Preparation
public import Theory.Representation.BinaryOffender.SingleNoncentralFlag

/-!
# An invariant complement from bounded indecomposable constituents

A perfect actor with one noncentral natural chief factor cannot have two
disjoint noncentral invariant subspaces. The literal flag supplies a central
cover of its natural factor; two such subspaces would both surject onto that
factor, and their disjointness would force the factor to be central.

Consequently a supplement to the fixed space of minimum dimension is
indecomposable, in the source's subrepresentation sense. The assumed bound
makes its dimension at most four. The specified upper space has a fixed
quotient of dimension four, so the ambient fixed quotient also has dimension
four. Minimize once more among supplements contained in that upper space.
The dimension equality makes this last supplement disjoint from all fixed
vectors, giving the required complement with literal containment.

This uses the source definition of indecomposability directly, without a
group-algebra or Krull–Schmidt conversion. Both the chief flag and the
indecomposable dimension bound remain explicit hypotheses. The latter is the
conclusion supplied by genuine B.4.8(4), not an assumed splitting.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.8(4),
printed p.91, and its application in the B.5.6 endgame, printed p.110.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit.ExceptionalSplitting
variable {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] {σ : Representation (ZMod 2) D U}

omit [FiniteDimensional (ZMod 2) U] in
/-- A central cover of a nontrivial simple module excludes two disjoint
noncentral submodules of the original representation. -/
private theorem disjoint_central_of_cover [Group.IsPerfect D]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) D W) [IsIrreducible τ]
    (hn : ∃ g w, τ g w ≠ w)
    (J : Subrepresentation σ) (hJ : moved σ ⊤ ≤ J.toSubmodule)
    (p : J.toSubmodule →ₗ[ZMod 2] W)
    (hp : ∀ g v, p (J.toRepresentation g v) = τ g (p v))
    (hk : p.ker ≤ J.toRepresentation.invariants)
    (A B : Subrepresentation σ) (hd : Disjoint A.toSubmodule B.toSubmodule) :
    A.toSubmodule ≤ σ.invariants ∨ B.toSubmodule ≤ σ.invariants := by
  let : Group.IsPerfect (⊤ : Subgroup D) := Group.IsPerfect.top_iff.mpr inferInstance
  have alt (A : Subrepresentation σ) :
      (∀ w, ∃ v : J.toSubmodule, (v : U) ∈ A.toSubmodule ∧ p v = w) ∨
        A.toSubmodule ≤ σ.invariants := by
    let C : Subrepresentation J.toRepresentation :=
      ⟨A.toSubmodule.comap J.toSubmodule.subtype, by
        intro g v hv
        exact A.apply_mem_toSubmodule g hv⟩
    let f : Representation.IntertwiningMap C.toRepresentation τ :=
      (p.comp C.toSubmodule.subtype).intertwiningMap_of_isIntertwiningMap _ _
        (fun g v => hp g v)
    rcases Representation.IsIrreducible.surjective_or_eq_zero f with hs | hz
    · left
      intro w
      obtain ⟨v,hv⟩ := hs w
      exact ⟨v, v.property, hv⟩
    · right
      have hC : subspaceCommutator σ A.toSubmodule ⊤ ≤ fixedSpace σ ⊤ := by
        intro v hv
        have hvJ : v ∈ J.toSubmodule :=
          hJ (subspaceCommutator_mono_left σ le_top ⊤ hv)
        have hvA : v ∈ A.toSubmodule :=
          subspaceCommutator_le_of_invariant σ
            (le_subspaceStabilizer σ _ (fun g _ w hw => A.apply_mem_toSubmodule g hw)) hv
        have hpv : p ⟨v,hvJ⟩ = 0 :=
          congrArg (fun t : Representation.IntertwiningMap C.toRepresentation τ =>
            t ⟨⟨v,hvJ⟩,hvA⟩) hz
        intro g
        exact congrArg Subtype.val (hk hpv g)
      have ha := le_fixedSpace_of_commutator_le_fixedSpace σ ⊤ A.toSubmodule
        (le_subspaceStabilizer σ _ (fun g _ w hw => A.apply_mem_toSubmodule g hw)) hC
      intro v hv g
      exact ha hv ⟨g,mem_top _⟩
  rcases alt A with ha | ha
  · rcases alt B with hb | hb
    · exfalso
      obtain ⟨g,w,hw⟩ := hn
      obtain ⟨a,ha,hpa⟩ := ha w
      obtain ⟨b,hb,hpb⟩ := hb w
      have hab : p (a - b) = 0 := by rw [map_sub,hpa,hpb,sub_self]
      have he : σ g (a : U) - (a : U) = σ g (b : U) - (b : U) := by
        have hh := congrArg Subtype.val (hk hab g)
        change σ g ((a : U) - (b : U)) = (a : U) - (b : U) at hh
        rw [map_sub] at hh
        exact sub_eq_sub_iff_sub_eq_sub.mp hh
      have hag : σ g (a : U) = a := by
        apply sub_eq_zero.mp
        apply Submodule.disjoint_def.mp hd
        · exact A.toSubmodule.sub_mem (A.apply_mem_toSubmodule g ha) ha
        · rw [he]
          exact B.toSubmodule.sub_mem (B.apply_mem_toSubmodule g hb) hb
      apply hw
      rw [← hpa, ← hp]
      exact congrArg p (Subtype.ext hag)
    · exact Or.inr hb
  · exact Or.inl ha

private theorem disjoint_central [Group.IsPerfect D]
    (hu : UniqueNoncentralNaturalFactor σ)
    (A B : Subrepresentation σ) (hd : Disjoint A.toSubmodule B.toSubmodule) :
    A.toSubmodule ≤ σ.invariants ∨ B.toSubmodule ≤ σ.invariants := by
  obtain ⟨n,c,i,hc,hzero,htop,_,hi,⟨e⟩,hcentral⟩ := hu
  let τ := sectionRepresentation σ (c i) (c (i+1))
  let : IsIrreducible τ := irreducible_of_equiv e
    (linearNatural_irreducible BinaryField.two (by decide : 2 ≤ 3))
  let : Nontrivial (((c (i+1)).toSubmodule ⧸ (sectionLower σ (c i) (c (i+1))).toSubmodule)) :=
    Subrepresentation.irreducible_module_nontrivial τ
  have hz : τ.invariants = ⊥ := invariants_of_equiv e
    (linearNatural_invariants BinaryField.two (by decide : 2 ≤ 3))
  have hn : ∃ g w, τ g w ≠ w := by
    by_contra h
    push Not at h
    obtain ⟨w,hw⟩ := exists_ne (0 : ((c (i+1)).toSubmodule ⧸ (sectionLower σ (c i) (c (i+1))).toSubmodule))
    have hwf : w ∈ τ.invariants := fun g => h g w
    rw [hz] at hwf
    exact hw hwf
  let et : ActionEquiv (τ.comp (⊤ : Subgroup D).subtype) (linearNatural BinaryField.two 3) :=
    ⟨Subgroup.topEquiv.trans e.groupEquiv, e.linearEquiv, fun g v => e.intertwines g v⟩
  let : Group.IsPerfect (⊤ : Subgroup D) := Group.IsPerfect.top_iff.mpr inferInstance
  obtain ⟨f⟩ := singleNoncentralFlag σ ⊤ c i n hc hzero htop hi
    (fun j hj hji g _ w => hcentral j hj hji g w)
    (irreducible_of_equiv et
      (linearNatural_irreducible BinaryField.two (by decide : 2 ≤ 3)))
    (by obtain ⟨g,w,hw⟩ := hn; exact ⟨g,mem_top _,w,hw⟩)
  exact disjoint_central_of_cover τ hn f.J (by rw [f.J_eq_commutator])
    f.map f.map_equivariant (fun v hv g => f.map_kernel_central hv ⟨g,mem_top _⟩) A B hd

private def liftSubrep (S : Subrepresentation σ) (A : Subrepresentation S.toRepresentation) :
    Subrepresentation σ where
  toSubmodule := A.toSubmodule.map S.toSubmodule.subtype
  apply_mem_toSubmodule g := by
    rintro v ⟨a,ha,rfl⟩
    exact ⟨S.toRepresentation g a, A.apply_mem_toSubmodule g ha, rfl⟩

omit [FiniteDimensional (ZMod 2) U] in
private theorem lift_sup (S : Subrepresentation σ) (A B : Subrepresentation S.toRepresentation)
    (hc : IsCompl A.toSubmodule B.toSubmodule) :
    (liftSubrep S A).toSubmodule ⊔ (liftSubrep S B).toSubmodule = S.toSubmodule := by
  change A.toSubmodule.map _ ⊔ B.toSubmodule.map _ = _
  rw [← Submodule.map_sup, hc.sup_eq_top, Submodule.map_top, Submodule.range_subtype]

/-- Minimize the dimension of an invariant supplement inside a prescribed
supplement. A central direct summand could be removed, contradicting minimality. -/
private theorem exists_indecomposable_supplement
    (hd : ∀ A B : Subrepresentation σ, Disjoint A.toSubmodule B.toSubmodule →
      A.toSubmodule ≤ σ.invariants ∨ B.toSubmodule ≤ σ.invariants)
    (hn : σ.invariants ≠ ⊤) (T : Subrepresentation σ)
    (hT : T.toSubmodule ⊔ σ.invariants = ⊤) :
    ∃ S : Subrepresentation σ, S ≤ T ∧
      S.toSubmodule ⊔ σ.invariants = ⊤ ∧ IsIndecomposable S.toRepresentation := by
  classical
  let P : ℕ → Prop := fun d => ∃ S : Subrepresentation σ,
    S ≤ T ∧ S.toSubmodule ⊔ σ.invariants = ⊤ ∧ Module.finrank (ZMod 2) S.toSubmodule = d
  have hex : ∃ d, P d := ⟨_,T,le_rfl,hT,rfl⟩
  obtain ⟨S,hST,hS,hSd⟩ := Nat.find_spec hex
  refine ⟨S,hST,hS,?_,?_⟩
  · apply Submodule.nontrivial_iff_ne_bot.mpr
    intro hb
    rw [hb,bot_sup_eq] at hS
    exact hn hS
  · intro A B hc
    have hdis : Disjoint (liftSubrep S A).toSubmodule (liftSubrep S B).toSubmodule := by
      apply Submodule.disjoint_def.mpr
      rintro v ⟨a,ha,rfl⟩ ⟨b,hb,he⟩
      have he' : b = a := S.toSubmodule.subtype_injective he
      subst b
      exact congrArg Subtype.val (Submodule.disjoint_def.mp hc.disjoint a ha hb)
    have central_zero (A B : Subrepresentation S.toRepresentation)
        (hc : IsCompl A.toSubmodule B.toSubmodule)
        (ha : (liftSubrep S A).toSubmodule ≤ σ.invariants) : A = ⊥ := by
      have hBS : liftSubrep S B ≤ S := by
        rintro v ⟨b,hb,rfl⟩
        exact b.property
      have hBt : (liftSubrep S B).toSubmodule ⊔ σ.invariants = ⊤ := by
        apply top_unique
        rw [← hS]
        apply sup_le _ le_sup_right
        rw [← lift_sup S A B hc]
        exact sup_le (ha.trans le_sup_right) le_sup_left
      have hmin := Nat.find_min' hex
        (show P (Module.finrank (ZMod 2) (liftSubrep S B).toSubmodule) from
          ⟨liftSubrep S B,hBS.trans hST,hBt,rfl⟩)
      have hdim := A.toSubmodule.finrank_sup_add_finrank_inf_eq B.toSubmodule
      rw [hc.sup_eq_top,hc.inf_eq_bot,finrank_top,finrank_bot,
        add_zero] at hdim
      have hmap : Module.finrank (ZMod 2) (liftSubrep S B).toSubmodule =
          Module.finrank (ZMod 2) B.toSubmodule :=
        Submodule.finrank_map_subtype_eq _ _
      have hAz : Module.finrank (ZMod 2) A.toSubmodule = 0 := by omega
      exact Subrepresentation.toSubmodule_injective (Submodule.finrank_eq_zero.mp hAz)
    rcases hd (liftSubrep S A) (liftSubrep S B) hdis with ha | hb
    · exact Or.inl (central_zero A B hc ha)
    · exact Or.inr (central_zero B A hc.symm hb)

omit [FiniteDimensional (ZMod 2) U] in
private theorem invariants_le_comap (R : Subrepresentation σ) :
    R.toRepresentation.invariants ≤ σ.invariants.comap R.toSubmodule.subtype := by
  intro v hv g
  exact congrArg Subtype.val (hv g)

/-- The map induced by the literal inclusion, modulo the respective fixed spaces. -/
private noncomputable def fixedQuotientInclusion (R : Subrepresentation σ) :
    (R.toSubmodule ⧸ R.toRepresentation.invariants) →ₗ[ZMod 2] (U ⧸ σ.invariants) :=
  R.toRepresentation.invariants.mapQ σ.invariants R.toSubmodule.subtype
    (invariants_le_comap R)

omit [FiniteDimensional (ZMod 2) U] in
private theorem fixedQuotientInclusion_injective (R : Subrepresentation σ) :
    Function.Injective (fixedQuotientInclusion R) := by
  apply LinearMap.ker_eq_bot.mp
  change LinearMap.ker (R.toRepresentation.invariants.mapQ _ _ _) = ⊥
  rw [Submodule.ker_mapQ]
  have he : σ.invariants.comap R.toSubmodule.subtype = R.toRepresentation.invariants := by
    ext v
    exact ⟨fun h g => Subtype.ext (h g),fun h g => congrArg Subtype.val (h g)⟩
  rw [he,Submodule.mkQ_map_self]

/-- The dimension bound on noncentral indecomposable submodules produces an
invariant complement to all fixed vectors inside the specified upper space. -/
theorem bounded_complement (s : CentralFourSection σ)
    (hu : UniqueNoncentralNaturalFactor σ) (hb : SmallNoncentralConstituents σ) :
    ∃ S : Subrepresentation σ, S ≤ s.upper ∧ IsCompl S.toSubmodule σ.invariants := by
  let : Group.IsPerfect D := s.isPerfect
  let Q := U ⧸ σ.invariants
  let ι := fixedQuotientInclusion s.upper
  have hi : Function.Injective ι := fixedQuotientInclusion_injective s.upper
  have hfour : Module.finrank (ZMod 2)
      (s.upper.toSubmodule ⧸ s.upper.toRepresentation.invariants) = 4 :=
    s.quotientSource.dimension
  have hlo : 4 ≤ Module.finrank (ZMod 2) Q := by
    have h := LinearMap.finrank_le_finrank_of_injective hi
    rwa [hfour] at h
  have hn : σ.invariants ≠ ⊤ := by
    intro ht
    have hd := σ.invariants.finrank_quotient_add_finrank
    change 4 ≤ Module.finrank (ZMod 2) (U ⧸ σ.invariants) at hlo
    rw [ht,finrank_top] at hd
    rw [ht] at hlo
    omega
  have choose_small (T : Subrepresentation σ) (hT : T.toSubmodule ⊔ σ.invariants = ⊤) :
      ∃ S : Subrepresentation σ, S ≤ T ∧ S.toSubmodule ⊔ σ.invariants = ⊤ ∧
        Module.finrank (ZMod 2) S.toSubmodule ≤ 4 := by
    obtain ⟨S,hST,hS,hSi⟩ := exists_indecomposable_supplement (disjoint_central hu) hn T hT
    refine ⟨S,hST,hS,?_⟩
    rcases hb S hSi with hc | hdim
    · have hsfix : S.toSubmodule ≤ σ.invariants := by
        intro v hv g
        exact congrArg Subtype.val (hc g ⟨v,hv⟩)
      exact (hn ((sup_eq_right.mpr hsfix).symm.trans hS)).elim
    · exact hdim
  obtain ⟨S₀,_,hS₀,hb₀⟩ := choose_small ⊤ (by exact top_unique le_sup_left)
  have hqdim := σ.invariants.finrank_quotient_add_finrank
  have hdim₀ := S₀.toSubmodule.finrank_sup_add_finrank_inf_eq σ.invariants
  rw [hS₀,finrank_top] at hdim₀
  have hQ : Module.finrank (ZMod 2) Q = 4 := by
    change Module.finrank (ZMod 2) Q + _ = _ at hqdim
    omega
  have hι : LinearMap.range ι = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_of_inj hi,hfour,hQ]
  have hR : s.upper.toSubmodule ⊔ σ.invariants = ⊤ := by
    change LinearMap.range (s.upper.toRepresentation.invariants.mapQ _ _ _) = ⊤ at hι
    rw [Submodule.range_mapQ,Submodule.range_subtype] at hι
    have h := (σ.invariants.map_mkQ_eq_top s.upper.toSubmodule).mp hι
    simpa only [sup_comm] using h
  obtain ⟨S,hSR,hS,hbS⟩ := choose_small s.upper hR
  refine ⟨S,hSR,?_,codisjoint_iff.mpr hS⟩
  have hdim := S.toSubmodule.finrank_sup_add_finrank_inf_eq σ.invariants
  rw [hS,finrank_top] at hdim
  have hz : Module.finrank (ZMod 2) ↥(S.toSubmodule ⊓ σ.invariants) = 0 := by
    change Module.finrank (ZMod 2) Q + _ = _ at hqdim
    omega
  exact disjoint_iff.mpr (Submodule.finrank_eq_zero.mp hz)

end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit.ExceptionalSplitting
