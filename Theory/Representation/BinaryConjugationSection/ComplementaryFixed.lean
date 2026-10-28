module
public import Theory.Representation.BinaryConjugationSection.QuadraticCorePair
public import Theory.Representation.BinaryConjugationSection.FixedMoving
/-!
# Global fixed vectors from complementary Sylow-fixed conjugates

Suppose a binary SL₂ module is the direct sum of a Sylow-fixed subspace
and one conjugate. If the conjugator is outside the Sylow normalizer, the
two Sylows generate SL₂. Splitting a globally fixed vector shows both
components are globally fixed and hence in the intersection. If the
conjugator normalizes the Sylow, that Sylow fixes the whole module; normal
generation then makes the action trivial, and complementarity makes the
module zero. No irreducibility, quadraticity or semisimplicity is assumed.

The section application proves control of fixed preimages using literal
subgroup joins, intersections and conjugation. It removes a separate
fixed-vector assumption from the Q/Z calculation in DGS, *Groups and
Graphs* (1985), 10.6, printed pp.157--158.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups Pointwise commutatorElement
namespace Representation.BinaryConjugationSection

variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

omit [Finite k] [CharP k 2] in
private theorem fixed_bot_of_generating_pair
    (σ : Representation (ZMod 2) SL(2,k) W) (S : Sylow 2 SL(2,k))
    (A : Submodule (ZMod 2) W) (g : SL(2,k))
    (hA : A ≤ fixedSpace σ S) (hc : IsCompl A (A.map (σ g)))
    (hgen : (S : Subgroup SL(2,k)) ⊔
      (S : Subgroup SL(2,k)).map (MulAut.conj g).toMonoidHom = ⊤) :
    fixedSpace σ ⊤ = ⊥ := by
  let C := A.map (σ g)
  let T := (S : Subgroup SL(2,k)).map (MulAut.conj g).toMonoidHom
  have hC : C ≤ fixedSpace σ T := by
    rw [Representation.SL2SylowFixedRecognition.fixedSpace_conjugate]
    exact Submodule.map_mono hA
  have hi : fixedSpace σ S ⊓ fixedSpace σ T = fixedSpace σ ⊤ := by
    exact (σ.invariants_comp_sup (S : Subgroup SL(2,k)) T).symm.trans
      (congrArg (fixedSpace σ) hgen)
  have hz (v : W) (hv : v ∈ fixedSpace σ ⊤) (hvC : v ∈ C) : v = 0 := by
    obtain ⟨a,ha,he⟩ := hvC
    have hfix := hv ⟨g,mem_top _⟩
    have hva : v = a := (σ.apply_bijective g).injective (hfix.trans he.symm)
    exact hc.disjoint.le_bot ⟨hva ▸ ha,⟨a,ha,he⟩⟩
  apply bot_unique
  intro v hv
  have hvall : v ∈ A ⊔ C := hc.sup_eq_top.symm ▸ Submodule.mem_top
  obtain ⟨a,ha,c,hcC,rfl⟩ := Submodule.mem_sup.mp hvall
  have hcS : c ∈ fixedSpace σ S := by
    have hh := (fixedSpace σ S).sub_mem
      (σ.invariants_comp_subtype_antitone le_top hv) (hA ha)
    simpa only [add_sub_cancel_left] using hh
  have hc0 := hz c (hi ▸ ⟨hcS,hC hcC⟩) hcC
  have haF : a ∈ fixedSpace σ ⊤ := by simpa only [hc0,add_zero] using hv
  have haC : a ∈ C := ⟨a,ha,haF ⟨g,mem_top _⟩⟩
  have ha0 := hz a haF haC
  simp only [ha0,hc0,add_zero,Submodule.mem_bot]

/-- Complementarity of conjugate subspaces fixed by a binary SL₂ Sylow
eliminates the global fixed space. The conjugator need not be opposite. -/
theorem sl2_fixed_bot_of_complementary_conjugates
    (σ : Representation (ZMod 2) SL(2,k) W) (S : Sylow 2 SL(2,k))
    (A : Submodule (ZMod 2) W) (g : SL(2,k))
    (hA : A ≤ fixedSpace σ S) (hc : IsCompl A (A.map (σ g))) :
    fixedSpace σ ⊤ = ⊥ := by
  by_cases hg : g ∈ normalizer (S : Set SL(2,k))
  · have hC : A.map (σ g) ≤ fixedSpace σ S := by
      have hh := Submodule.map_mono (f := σ g) hA
      rw [←Representation.SL2SylowFixedRecognition.fixedSpace_conjugate] at hh
      have he : (S : Subgroup SL(2,k)).map (MulAut.conj g).toMonoidHom = S :=
        congrArg (fun T : Sylow 2 SL(2,k) => (T : Subgroup SL(2,k)))
          (Sylow.smul_eq_iff_mem_normalizer.mpr hg)
      rwa [he] at hh
    have hS : fixedSpace σ S = ⊤ := top_unique
      (hc.sup_eq_top ▸ sup_le hA hC)
    obtain ⟨t,ht⟩ := SetLike.exists_not_mem_of_ne_top
      (normalizer (S : Set SL(2,k)))
      (Matrix.SpecialLinearGroup.sylow_normalizer_ne_top S)
    have hT : fixedSpace σ ((S : Subgroup SL(2,k)).map
        (MulAut.conj t).toMonoidHom) = ⊤ := by
      rw [Representation.SL2SylowFixedRecognition.fixedSpace_conjugate,hS]
      rw [Submodule.map_top,LinearMap.range_eq_top.mpr (σ.apply_bijective t).surjective]
    have hfixed : fixedSpace σ ⊤ = ⊤ := by
      rw [←Matrix.SpecialLinearGroup.sylow_sup_conjugate_eq_top_of_not_mem_normalizer S ht]
      change invariants (σ.comp ((S : Subgroup SL(2,k)) ⊔
        (S : Subgroup SL(2,k)).map (MulAut.conj t).toMonoidHom).subtype) = ⊤
      rw [σ.invariants_comp_sup]
      change fixedSpace σ S ⊓ fixedSpace σ ((S : Subgroup SL(2,k)).map
        (MulAut.conj t).toMonoidHom) = ⊤
      rw [hS,hT,inf_idem]
    have hact (a : SL(2,k)) (v : W) : σ a v = v :=
      (show v ∈ fixedSpace σ ⊤ from hfixed.symm ▸ Submodule.mem_top) ⟨a,mem_top _⟩
    have he : A.map (σ g) = A := by
      ext v
      constructor
      · rintro ⟨a,ha,rfl⟩
        rwa [hact]
      · intro hv
        exact ⟨v,hv,hact g v⟩
    have hAtop : A = ⊤ := by simpa only [he,sup_idem] using hc.sup_eq_top
    have hAbot : A = ⊥ := by simpa only [he,inf_idem] using hc.inf_eq_bot
    exact hfixed.trans (hAtop.symm.trans hAbot)
  · exact fixed_bot_of_generating_pair σ S A g hA hc
      (Matrix.SpecialLinearGroup.sylow_sup_conjugate_eq_top_of_not_mem_normalizer S hg)

variable {G : Type*} [Group G]

/-- The actual complementary subgroup images prove fixed-preimage control
on the literal quotient. No fixed-space or irreducibility premise is needed. -/
theorem fixed_preimage_of_complementary_pair
    (L Q Z A C T : Subgroup G)
    (σ : Representation (ZMod 2) SL(2,k) W) (π : L →* SL(2,k))
    (hπ : Function.Surjective π) (d : BinaryConjugationSection L Q Z (σ.comp π))
    (hAQ : A ≤ Q) (hCQ : C ≤ Q)
    (hspan : Q = (A ⊔ C) ⊔ Z) (hinter : (A ⊔ Z) ⊓ (C ⊔ Z) = Z)
    (g : L) (hconj : C = A.conjBy (g : G))
    (S : Sylow 2 SL(2,k)) (hS : (T.subgroupOf L).map π = S)
    (hfixed : ⁅T,A⁆ ≤ Z) :
    ∀ x ∈ Q, (∀ a ∈ L, ⁅a,x⁆ ∈ Z) → x ∈ Z := by
  have hsum : Q = (A ⊔ Z) ⊔ (C ⊔ Z) := hspan.trans (by ac_rfl)
  have hc := d.isCompl_imageSpace (A ⊔ Z) (C ⊔ Z) hsum hinter.symm
  rw [d.imageSpace_sup_kernel A hAQ,d.imageSpace_sup_kernel C hCQ,
    hconj,d.imageSpace_conjBy A hAQ g] at hc
  have hA : d.imageSpace A ≤ fixedSpace σ S := by
    intro v hv t
    obtain ⟨a,ha,he⟩ := (show (t : SL(2,k)) ∈ (T.subgroupOf L).map π from
      hS.symm ▸ t.property)
    change σ t.val v = v
    rw [←he]
    exact d.fixed_on_imageSpace_of_commutator_le T A hfixed a ha v hv
  have hf := sl2_fixed_bot_of_complementary_conjugates σ S (d.imageSpace A) (π g) hA hc
  intro x hx hfix
  let q : Q := ⟨x,hx⟩
  have hq : (d.coordinates q).toAdd ∈ fixedSpace σ ⊤ := by
    intro a
    obtain ⟨l,hl⟩ := hπ a.val
    change σ a.val (d.coordinates q).toAdd = _
    rw [←hl]
    apply (d.fixed_coordinate_iff_commutator_mem l q).mpr
    have hh := Z.inv_mem (hfix l l.property)
    simpa only [commutatorElement_inv] using hh
  have hz : (d.coordinates q).toAdd = 0 := by simpa only [hf,Submodule.mem_bot] using hq
  exact (d.coordinates_eq_one_iff q).mp (Multiplicative.toAdd.injective hz)

end Representation.BinaryConjugationSection
