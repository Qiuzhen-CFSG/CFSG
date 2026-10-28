module
public import CFSG.Quasithin.ChapterG.Section05.Structure.PairQuotients
public import Theory.Representation.CosetOrbitQuotient
public import Theory.Representation.BinaryConjugacyOrbit
public import Theory.GroupAction.SurjectiveFlagCosets

/-!
# Natural quotients of marked alternating-six fixed-line orbits

A cyclic binary module with a parabolic-fixed generator is a quotient of
its literal fifteen-coset permutation module. Descend the action along the
specified surjection to A₆. Fixed-space vanishing kills the constant line,
so the even duad core still maps onto the module. Its proved submodule flag
then supplies a quotient onto the natural four-space and the possible whole
module dimensions. Graph transport gives the opposite natural quotient for
the syntheme parabolic, preserving the same original actor map.

The full kernel is retained in the coset identification; no S₆ extension is
assumed. The original amalgam application constructs both quotient maps in
`FixedCoreSource/Amalgam/AlternatingOrbitHeads`.
Source: Aschbacher--Smith G.5.3, printed pp.343--345, and 13.4.7, p.901.
-/

public noncomputable section
open Subgroup Representation BinaryPermutation BinaryDuadModule BinaryDuadStructure
open Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.ChapterG.Section05.Structure

local instance duadTransitive : MulAction.IsPretransitive A6 Duad where
  exists_smul_eq := a6_duad_transitive

variable {A M : Type*} [Group A] [AddCommGroup M] [Module (ZMod 2) M]

/-- The fixed vector supplies the actual fifteen-point permutation quotient. -/
theorem marked_duad_quotient (f : A →* A6) (hf : Function.Surjective f)
    (P : Subgroup A) (hk : f.ker ≤ P) (hP : P.map f = a6DuadStabilizer)
    (ρ : Representation (ZMod 2) A M) (w : M) (hw : ∀ a : P, ρ a w = w)
    (hs : Submodule.span (ZMod 2) (Set.range (fun a : A => ρ a w)) = ⊤) :
    ∃ q : Representation.IntertwiningMap (alternatingPointAction.comp f) ρ, Function.Surjective q := by
  classical
  have hfix : P.map f = MulAction.stabilizer A6 (0 : Duad) := by
    rw [hP, a6_duad_stabilizer_zero]
  let E := MulAction.surjectiveCosetEquiv P f hf hk (0 : Duad) hfix
  obtain ⟨q,hq,hm,he⟩ := exists_coset_orbit_map ρ P w hw hs
  let v : Duad → M := fun d => q (Finsupp.single (E.symm d) 1)
  have hv (a : A) (d : Duad) : v (f a • d) = ρ a (v d) := by
    have hE : E.symm (f a • d) = a • E.symm d := by
      apply E.injective
      rw [E.apply_symm_apply]
      exact (MulAction.surjectiveCosetEquiv_smul P f hf hk _ hfix a (E.symm d)).trans
        (congrArg (fun d : Duad => f a • d) (E.apply_symm_apply d)) |>.symm
    change q (Finsupp.single (E.symm (f a • d)) 1) = _
    rw [hE]
    simpa only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single] using
      he a (Finsupp.single (E.symm d) 1)
  have hvspan : Submodule.span (ZMod 2) (Set.range v) = ⊤ := by
    apply top_unique
    rw [←hs]
    apply Submodule.span_mono
    rintro _ ⟨a,rfl⟩
    exact ⟨E (QuotientGroup.mk a),by
      change q (Finsupp.single (E.symm (E (QuotientGroup.mk a))) 1) = ρ a w
      rw [E.symm_apply_apply,hm]⟩
  let α := (MulAction.toPermHom S6 Duad).comp (A6.subtype.comp f)
  let t := BinaryPermutation.orbitQuotient ρ α v hv
  change ∃ q : Representation.IntertwiningMap ((representation Duad).comp α) ρ,
    Function.Surjective q
  exact ⟨t, BinaryPermutation.orbitQuotient_surjective ρ α v hv hvspan⟩

/-- A fixed-free nonzero duad quotient has the marked natural head. -/
theorem marked_duad_natural_head [Nontrivial M]
    (f : A →* A6) (hf : Function.Surjective f)
    (ρ : Representation (ZMod 2) A M)
    (q : Representation.IntertwiningMap (alternatingPointAction.comp f) ρ) (hq : Function.Surjective q)
    (hfixed : ∀ v : M, (∀ a : A, ρ a v = v) → v = 0) :
    (∃ t : ρ.IntertwiningMap (alternatingNaturalAction.comp f), Function.Surjective t) ∧
    (Module.finrank (ZMod 2) M = 4 ∨ Module.finrank (ZMod 2) M = 5 ∨
      Module.finrank (ZMod 2) M = 9 ∨ Module.finrank (ZMod 2) M = 10 ∨
      Module.finrank (ZMod 2) M = 14) := by
  have hk : f.ker ≤ ρ.asGroupHom.ker := by
    intro a ha
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨x,rfl⟩ := hq v
    have hh := IntertwiningMap.isIntertwining _ _ q a x
    change q (alternatingPointAction (f a) x) = ρ a (q x) at hh
    rw [show f a = 1 from ha,map_one,Module.End.one_apply] at hh
    exact hh.symm
  let σ : Representation (ZMod 2) A6 M :=
    (Units.coeHom _).comp (f.liftOfSurjective hf ⟨ρ.asGroupHom,hk⟩)
  have he (a : A) : σ (f a) = ρ a :=
    congrArg Units.val (f.liftOfRightInverse_comp_apply (Function.surjInv hf)
      (Function.rightInverse_surjInv hf) ⟨ρ.asGroupHom,hk⟩ a)
  let qA : Representation.IntertwiningMap alternatingPointAction σ := {
    toLinearMap := q.toLinearMap
    isIntertwining' g := by
      obtain ⟨a,rfl⟩ := hf g
      rw [he]
      exact q.isIntertwining' a }
  let qC : coreAction.IntertwiningMap σ := {
    toLinearMap := qA.toLinearMap.comp (core Duad).subtype
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      exact IntertwiningMap.isIntertwining _ _ qA g v.val }
  have hconst (v : Full Duad) (hv : v ∈ constants Duad) : qA v = 0 := by
    apply hfixed
    intro a
    rw [←he,←IntertwiningMap.isIntertwining _ _ qA]
    congr 1
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hv
    ext d
    rfl
  have hqC : Function.Surjective qC := by
    intro v
    obtain ⟨x,rfl⟩ := hq v
    have hx : x ∈ core Duad ⊔ constants Duad := by
      rw [(core_isCompl_constants Duad (by decide)).sup_eq_top]
      trivial
    obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨⟨a,ha⟩,?_⟩
    change qA a = qA (a+b)
    rw [map_add,hconst b hb,add_zero]
  obtain ⟨hn,hd⟩ := duad_core_quotient_comparison σ qC hqC
  have head : ∃ t : σ.IntertwiningMap alternatingNaturalAction, Function.Surjective t := by
    rcases hn with hn | ⟨t,ht⟩
    · obtain ⟨E⟩ := hn
      exact ⟨E.symm.toIntertwiningMap,E.symm.toLinearEquiv.surjective⟩
    · exact ⟨coreNaturalProjection.comp t,coreNaturalProjection_isCover.1.comp ht⟩
  obtain ⟨t,ht⟩ := head
  refine ⟨⟨t.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ ?_,ht⟩,hd⟩
  intro a v
  rw [←he]
  exact IntertwiningMap.isIntertwining _ _ t (f a) v

/-- The original parabolic-fixed generator gives a natural head with the
same full quotient map and no representation-extension hypothesis. -/
theorem marked_fixed_line_natural_head [Nontrivial M]
    (f : A →* A6) (hf : Function.Surjective f)
    (P : Subgroup A) (hk : f.ker ≤ P) (hP : P.map f = a6DuadStabilizer)
    (ρ : Representation (ZMod 2) A M) (w : M) (hw : ∀ a : P, ρ a w = w)
    (hs : Submodule.span (ZMod 2) (Set.range (fun a : A => ρ a w)) = ⊤)
    (hfixed : ∀ v : M, (∀ a : A, ρ a v = v) → v = 0) :
    (∃ t : ρ.IntertwiningMap (alternatingNaturalAction.comp f), Function.Surjective t) ∧
    (Module.finrank (ZMod 2) M = 4 ∨ Module.finrank (ZMod 2) M = 5 ∨
      Module.finrank (ZMod 2) M = 9 ∨ Module.finrank (ZMod 2) M = 10 ∨
      Module.finrank (ZMod 2) M = 14) := by
  obtain ⟨q,hq⟩ := marked_duad_quotient f hf P hk hP ρ w hw hs
  exact marked_duad_natural_head f hf ρ q hq hfixed

/-- The opposite parabolic gives the graph-conjugate natural quotient under
exactly the same actor marking. -/
private theorem twisted_fixed_line_head [Nontrivial M]
    (δ : A6 ≃* A6) (hδ : ∀ a : A6, δ a ∈ a6DuadStabilizer ↔ a ∈ a6SynthemeStabilizer)
    (τ : Representation (ZMod 2) A6 NaturalModule)
    (hτ : ∀ a v, τ a v = alternatingNaturalAction (δ a) v)
    (f : A →* A6) (hf : Function.Surjective f)
    (P : Subgroup A) (hk : f.ker ≤ P) (hP : P.map f = a6SynthemeStabilizer)
    (ρ : Representation (ZMod 2) A M) (w : M) (hw : ∀ a : P, ρ a w = w)
    (hs : Submodule.span (ZMod 2) (Set.range (fun a : A => ρ a w)) = ⊤)
    (hfixed : ∀ v : M, (∀ a : A, ρ a v = v) → v = 0) :
    (∃ t : ρ.IntertwiningMap (τ.comp f),
      Function.Surjective t) ∧
    (Module.finrank (ZMod 2) M = 4 ∨ Module.finrank (ZMod 2) M = 5 ∨
      Module.finrank (ZMod 2) M = 9 ∨ Module.finrank (ZMod 2) M = 10 ∨
      Module.finrank (ZMod 2) M = 14) := by
  let f' := δ.toMonoidHom.comp f
  have hk' : f'.ker ≤ P := by
    intro a ha
    apply hk
    apply δ.injective
    exact ha.trans δ.map_one.symm
  have hP' : P.map f' = a6DuadStabilizer := by
    rw [show P.map f' = (P.map f).map δ.toMonoidHom from (map_map _ _ _).symm,hP]
    ext g
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact (hδ a).mpr ha
    · intro hg
      obtain ⟨a,rfl⟩ := δ.surjective g
      exact ⟨a,(hδ a).mp hg,rfl⟩
  obtain ⟨⟨t,ht⟩,hd⟩ := marked_fixed_line_natural_head f' (δ.surjective.comp hf)
    P hk' hP' ρ w hw hs hfixed
  refine ⟨⟨t.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ ?_,ht⟩,hd⟩
  intro a v
  change t (ρ a v) = τ (f a) (t v)
  rw [hτ]
  exact IntertwiningMap.isIntertwining _ _ t a v

/-- The syntheme-fixed generator gives the graph-conjugate natural head,
using the same original actor and quotient map. -/
theorem marked_syntheme_natural_head [Nontrivial M]
    (f : A →* A6) (hf : Function.Surjective f)
    (P : Subgroup A) (hk : f.ker ≤ P) (hP : P.map f = a6SynthemeStabilizer)
    (ρ : Representation (ZMod 2) A M) (w : M) (hw : ∀ a : P, ρ a w = w)
    (hs : Submodule.span (ZMod 2) (Set.range (fun a : A => ρ a w)) = ⊤)
    (hfixed : ∀ v : M, (∀ a : A, ρ a v = v) → v = 0) :
    (∃ t : ρ.IntertwiningMap (BinaryAlternatingSix.secondAlternating.comp f),
      Function.Surjective t) ∧
    (Module.finrank (ZMod 2) M = 4 ∨ Module.finrank (ZMod 2) M = 5 ∨
      Module.finrank (ZMod 2) M = 9 ∨ Module.finrank (ZMod 2) M = 10 ∨
      Module.finrank (ZMod 2) M = 14) := by
  exact twisted_fixed_line_head BinaryAlternatingSix.alternatingDiagramAut
    BinaryAlternatingSix.alternatingDiagramAut_mem_duad BinaryAlternatingSix.secondAlternating
    BinaryAlternatingSix.secondAlternating_apply f hf P hk hP ρ w hw hs hfixed

end CFSG.Quasithin.ChapterG.Section05.Structure
