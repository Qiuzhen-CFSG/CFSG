module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.Generation
public import Theory.Representation.BinaryConjugationSection.ConjugationCoordinates
public import Theory.Representation.BinaryConjugationSection.Coinvariants
public import Theory.Representation.FirstCohomologyDuality.SimpleCover
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# Constructing the section and assembling the 14.7.63 datum

Abelian conjugate generation makes U elementary abelian. The coordinates
on the literal quotient U/V₁ and its H-conjugation representation are then
constructed. An arbitrary S₅ marking sends the actual O²(H) onto A₅.
The natural quotient is simple under this image; full commutator generation
therefore makes every central cover indecomposable.

`data_of_recognition` constructs the point, centralizer, residual product
and indecomposability. The uniqueness, relative component, and natural
quotient recognition remain explicit earlier source conclusions. It is a
conditional assembly, not a proof of those recognition results. Their
final discharge stays with qt-d-14763-source-data; the subsequent Rudvalis
assembly belongs to qt-d-14775-source.

Source: Aschbacher–Smith, 14.7.40, 14.7.48, 14.7.52–53 and 14.7.63,
printed pp.1061–1069.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction
open Subgroup Representation Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (F : InvariantFlag T V 3)

omit [Finite G] in
/-- Abelian closure of the elementary seed is elementary. -/
theorem elementary_U [IsElementaryAbelian 2 V] [IsMulCommutative F.U] :
    IsElementaryAbelian 2 F.U := by
  let : IsMulCommutative (conjugateSpanBy V F.H) := ‹IsMulCommutative F.U›
  exact conjugateSpanBy_elementary_of_commutative V F.H

omit [Finite G] in
/-- Construct the action on the literal section of the original flag. -/
theorem exists_section [IsElementaryAbelian 2 V] [IsMulCommutative F.U] :
    letI := elementary_U F
    ∃ ρ : Representation (ZMod 2) F.H (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)),
      Nonempty (BinaryConjugationSection F.H F.U (F.Vi 1) ρ) := by
  let := elementary_U F
  exact BinaryConjugationSection.exists_conjugation_coordinates F.H F.U (F.Vi 1)
    F.U_le_H (le_normalizer_conjugateSpanBy V F.H)
    ((F.le_seed 1).trans (le_conjugateSpanBy V F.H)) le_rfl

/-- The actual two-residual supplements the ambient Sylow in H. -/
theorem residual_product : F.H = K F ⊔ (T : Subgroup G) := by
  let S : Sylow 2 F.H := T.subtype (F.invariant 1)
  have h := congrArg (fun A : Subgroup F.H => A.map F.H.subtype)
    (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at h
  change K F ⊔ ((T : Subgroup G).subgroupOf F.H).map F.H.subtype = F.H at h
  rw [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ F.H from F.invariant 1)] at h
  exact h.symm

variable {F}

/-- The chosen coordinates on the literal star quotient. -/
def quotientMarking (e : HStar F.H ≃* ChapterJ.S5) : F.H →* ChapterJ.S5 :=
  e.toMonoidHom.comp (starMap F)

/-- The original residual maps onto the marked alternating subgroup. -/
theorem residual_image (e : HStar F.H ≃* ChapterJ.S5) :
    ((K F).subgroupOf F.H).map (quotientMarking e) = alternatingGroup (Fin 5) := by
  change (((pResidual 2 F.H).map F.H.subtype).comap F.H.subtype).map
    (quotientMarking e) = _
  rw [comap_map_eq_self_of_injective F.H.subtype_injective,
    map_pResidual_of_surjective 2 (quotientMarking e)
      (e.surjective.comp (QuotientGroup.mk'_surjective _)),
    Equiv.Perm.twoResidual_eq_alternating]

/-- Irreducibility follows from natural transitivity and the residual image. -/
theorem natural_simple (e : HStar F.H ≃* ChapterJ.S5) (a : ChapterJ.L2FourAction)
    (X : Submodule (ZMod 2) ChapterJ.FourSpace)
    (hX : ∀ k : (K F).subgroupOf F.H, ∀ w ∈ X,
      a.action (quotientMarking e k) w ∈ X) : X = ⊥ ∨ X = ⊤ := by
  by_cases hx : X = ⊥
  · exact Or.inl hx
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hx
  apply top_unique
  intro w _
  by_cases hw : w = 0
  · simpa only [hw] using X.zero_mem
  obtain ⟨g, hg⟩ := Representation.SL2FourNatural.transitive_nonzero v w hv0 hw
  have hm : alternatingActor a g ∈ ((K F).subgroupOf F.H).map (quotientMarking e) := by
    rw [residual_image]
    exact (a.marking g).property
  obtain ⟨k, hk, he⟩ := hm
  have hv' := hX ⟨k, hk⟩ v hv
  rw [he] at hv'
  change a.action (a.marking g) v ∈ X at hv'
  rw [a.restriction] at hv'
  exact hg ▸ hv'

variable {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) F.H W}

/-- Commutator generation and a natural central quotient force indecomposability. -/
theorem indecomposable_of_generation
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (e : HStar F.H ≃* ChapterJ.S5) (a : ChapterJ.L2FourAction)
    (p : ρ.IntertwiningMap (a.action.comp (quotientMarking e)))
    (hp : Function.Surjective p)
    (hk : p.toLinearMap.ker = Representation.invariants
      (ρ.comp ((K F).subgroupOf F.H).subtype))
    (hgen : ⁅F.U, K F⁆ = F.U)
    (A B : Submodule (ZMod 2) W)
    (hA : ∀ k : (K F).subgroupOf F.H, ∀ w ∈ A, ρ k w ∈ A)
    (hB : ∀ k : (K F).subgroupOf F.H, ∀ w ∈ B, ρ k w ∈ B)
    (hAB : IsCompl A B) : A = ⊥ ∨ B = ⊥ := by
  let σ : Representation (ZMod 2) ((K F).subgroupOf F.H) W :=
    ρ.comp ((K F).subgroupOf F.H).subtype
  let τ : Representation (ZMod 2) ((K F).subgroupOf F.H) ChapterJ.FourSpace :=
    (a.action.comp (quotientMarking e)).comp ((K F).subgroupOf F.H).subtype
  let p' : σ.IntertwiningMap τ := {
    toLinearMap := p.toLinearMap
    isIntertwining' := fun k => p.isIntertwining' k }
  have hKH : K F ≤ F.H := map_subtype_le _
  let r : K F →* (K F).subgroupOf F.H := (subgroupOfEquivOfLe hKH).symm.toMonoidHom
  have hfull : Coinvariants.ker σ = ⊤ :=
    c.coinvariants_eq_top_of_group_generation (K F) hKH σ r (fun _ _ => rfl) (by
      rw [commutator_comm, hgen, sup_eq_left.mpr c.kernel_le])
  have hcover : OneCohomology.IsCover p' := ⟨hp, by
    change p.toLinearMap.ker ≤ Representation.invariants _
    exact hk.le, hfull⟩
  exact OneCohomology.indecomposable_of_cover_of_simple p' hcover
    (natural_simple e a) A B hA hB hAB

/-- Assemble Data from the preceding recognition results, deriving its algebraic fields. -/
def data_of_recognition
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hunique : F.Hz L (normalizer (L : Set G)) = {F.H})
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (e : HStar F.H ≃* ChapterJ.S5) (a : ChapterJ.L2FourAction)
    (p : ρ.IntertwiningMap (a.action.comp (quotientMarking e)))
    (hp : Function.Surjective p)
    (hk : p.toLinearMap.ker = Representation.invariants
      (ρ.comp ((K F).subgroupOf F.H).subtype)) : Data T L V F W := by
  let z := Classical.choose (SetupFlagGeometry.exists_point_generator F (by decide))
  have hz := (Classical.choose_spec (SetupFlagGeometry.exists_point_generator F (by decide))).1
  have he := (Classical.choose_spec (SetupFlagGeometry.exists_point_generator F (by decide))).2
  exact {
    counterexample := d
    natural := h
    abelian := hab
    z := z
    z_ne_one := hz
    point := he
    centralizer_eq := F.H_eq_centralizer (by decide) z he
    unique_Hz := hunique
    residual_product := residual_product F
    component := hcomponent
    model := e
    action := ρ
    conjugationSection := c
    naturalQuotient := a
    projection := p
    projection_onto := hp
    fixed_kernel := hk
    indecomposable := indecomposable_of_generation c e a p hp hk (commutator_U h F) }

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction
