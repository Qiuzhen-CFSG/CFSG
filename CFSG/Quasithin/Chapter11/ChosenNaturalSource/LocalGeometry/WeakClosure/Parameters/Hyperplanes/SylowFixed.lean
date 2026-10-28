module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.FullFixed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalComplement
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The original Sylow-fixed intersection in the exceptional cover

The literal automizer representation and its faithful natural quotient
satisfy the full-actor lifting theorem for the symplectic orthogonal cover.
This gives a vector in C_V(T) outside C_V(L), with no splitting assumption.
When C_V(L) has order two it is fixed by T. If a binary hyperplane missed
C_V(T), its index would force that fixed space to equal C_V(L), a contradiction.

The final theorem applies this to the same escaping hyperplane and removes
the fixed-intersection premise from the existing E.6.14 consumer. Its cubic
actor and orthogonal maximal-stabilizer inputs remain with
qt-d-1222-natural-weak-parameters. The parent
qt-d-1222-natural-weak-closure-source retains final assembly of earlier inputs.

Source: Aschbacher--Smith 11.2.2, printed p.767, using I.2.3, printed p.413.
-/

public noncomputable section
open Matrix Representation
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
open FullAutomizer
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The full original Sylow fixes a vector outside the symplectic central kernel. -/
theorem sp4_sylow_fixed_not_le_central
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) :
    ¬ sylowFixedSpace (T : Subgroup G) V ≤ V ⊓ centralizer (L : Set G) := by
  let := D.elementary
  let := S.source.quasisimple
  let : Group.IsPerfect (Matrix.symplecticGroup (Fin 2) S.field.Carrier) :=
    Group.IsPerfect.ofSurjective (f := m.groupEquiv.toMonoidHom) m.groupEquiv.surjective
  let c := Coordinates.sp4 m
  let K := inducedAutomizer V L
  let : K.Normal := layer_normal D S
  let d : SymplecticFourOrthogonalCover.L (K := S.field.Carrier) ≃* c.ModelGroup :=
    (MulEquiv.subgroupCongr (Group.IsPerfect.commutator_eq_top)).trans Subgroup.topEquiv
  let e : SymplecticFourOrthogonalCover.L (K := S.field.Carrier) ≃* K :=
    d.trans (layerEquiv D S c).symm
  obtain ⟨ρ,hρ,he,hres⟩ := exists_faithful_quotient_action D S c
  let μ : Representation (ZMod 2) (Automizer V) (Additive V) := automizerRepresentation V
  let σ : Representation (ZMod 2) (SymplecticFourOrthogonalCover.L (K := S.field.Carrier)) (Additive V) :=
    μ.comp (K.subtype.comp e.toMonoidHom)
  have hbase (g : SymplecticFourOrthogonalCover.L (K := S.field.Carrier)) (v : c.Space) :
      ρ (e g) v = binaryNatural g v := by
    rw [hres, show (layerEquiv D S c) (e g) = d g from
      (layerEquiv D S c).apply_symm_apply (d g)]
    rfl
  let p : σ.IntertwiningMap (binaryNatural (K := S.field.Carrier)) :=
    (projectionLinear D S c).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g w
      exact (he (e g) w).trans (hbase g _))
  have hp : IsCover p := by
    refine ⟨projectionLinear_surjective D S c,?_,?_⟩
    · intro w hw g
      change w ∈ (projectionLinear D S c).ker at hw
      rw [projectionLinear_kernel] at hw
      exact hw (e g)
    · apply top_unique
      rw [←moved_eq_top D]
      apply Submodule.span_le.mpr
      rintro _ ⟨a,ha,w,_,rfl⟩
      have hh := Coinvariants.sub_mem_ker (ρ := σ) (e.symm ⟨a,ha⟩) w
      change μ (e (e.symm ⟨a,ha⟩)) w - w ∈ _ at hh
      rw [e.apply_symm_apply] at hh
      exact hh
  let b : T →* Automizer V :=
    V.normalizerMonoidHom.rangeRestrict.comp (inclusion S.sylow_normalizes)
  let τ : Representation (ZMod 2) T (Additive V) := μ.comp b
  let η : Representation (ZMod 2) T c.Space := ρ.comp b
  let a (t : T) : MulAut (SymplecticFourOrthogonalCover.L (K := S.field.Carrier)) :=
    (MulAut.congr e.symm) (MulAut.conjNormal (b t))
  have ha (t : T) (g : SymplecticFourOrthogonalCover.L (K := S.field.Carrier)) :
      (e (a t g) : Automizer V) = b t * (e g : Automizer V) * (b t)⁻¹ := by
    change (e (e.symm (MulAut.conjNormal (b t) (e g))) : Automizer V) = _
    rw [e.apply_symm_apply]
    rfl
  have hτ (t : T) (g : SymplecticFourOrthogonalCover.L (K := S.field.Carrier))
      (w : Additive V) : τ t (σ g w) = σ (a t g) (τ t w) := by
    change μ (b t) (μ (e g) w) = μ (e (a t g)) (μ (b t) w)
    rw [ha]
    simp only [←Module.End.mul_apply, ←map_mul, inv_mul_cancel_right]
  have hover (t : T) (w : Additive V) : p (τ t w) = η t (p w) := he (b t) w
  have hη (t : T) (g : SymplecticFourOrthogonalCover.L (K := S.field.Carrier))
      (v : c.Space) : η t (binaryNatural g v) = binaryNatural (a t g) (η t v) := by
    obtain ⟨w,rfl⟩ := hp.1 v
    rw [←p.isIntertwining, ←hover, hτ, p.isIntertwining, hover]
  obtain ⟨w,hw,hfixed⟩ := FullFixed.exists_fixed_noncentral σ p hp τ η a hτ hη hover
    T.isPGroup'
  intro hle
  have hf : (w.toMul : G) ∈ sylowFixedSpace (T : Subgroup G) V := by
    refine ⟨w.toMul.property,?_⟩
    intro t ht
    have hh := congrArg (fun z : Additive V => (z.toMul : G)) (hfixed ⟨t,ht⟩)
    change t * (w.toMul : G) * t⁻¹ = (w.toMul : G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hc := (hle hf).2
  apply hw
  change (c.projection w.toMul).toAdd = 0
  exact congrArg Multiplicative.toAdd ((c.projection_eq_one_iff w.toMul).mpr hc)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

include D S in
/-- The order-two kernel is fixed by the same original Sylow. -/
theorem central_kernel_le_sylow_fixed_of_card_two
    (hC : Nat.card ↥(V ⊓ centralizer (L : Set G)) = 2) :
    V ⊓ centralizer (L : Set G) ≤ sylowFixedSpace (T : Subgroup G) V := by
  let C := V ⊓ centralizer (L : Set G)
  have hn : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf S.sylow_normalizes (D.sylow_normalizes_component.trans
      (normalizer_le_normalizer_centralizer L))).trans inf_normalizer_le_normalizer_inf
  have hc := hn.trans (normalizer_le_centralizer_of_card_two C hC)
  intro v hv
  refine ⟨hv.1,?_⟩
  intro t ht
  exact (hc ht v hv).symm

/-- Every binary hyperplane meets the full Sylow-fixed space in the exceptional cover. -/
theorem sp4_hyperplane_sylow_fixed_intersection
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hC : Nat.card ↥(V ⊓ centralizer (L : Set G)) = 2)
    {U : Subgroup G} (hU : subgroupCorank V U = 1) :
    U ⊓ sylowFixedSpace (T : Subgroup G) V ≠ ⊥ := by
  let := D.elementary
  intro hint
  let Z := sylowFixedSpace (T : Subgroup G) V
  have hi : U.relIndex V = 2 := by
    rw [Subgroup.relIndex_eq_two_pow_quotient_finrank,
      ←subgroupCorank_eq_quotient_finrank,hU]
    rfl
  have hz : U.relIndex Z = Nat.card Z := by
    rw [←inf_relIndex_right,hint,relIndex_bot_left]
  have hbound := relIndex_le_of_le_right (show Z ≤ V from inf_le_left)
    (show U.relIndex V ≠ 0 from index_ne_zero_of_finite)
  rw [hi,hz] at hbound
  have he : V ⊓ centralizer (L : Set G) = Z :=
    eq_of_le_of_card_ge (central_kernel_le_sylow_fixed_of_card_two D S hC)
      (by simpa only [hC] using hbound)
  exact sp4_sylow_fixed_not_le_central D S m he.ge

/-- The original escaping hyperplane satisfies the actual E.6.6 fixed-intersection premise. -/
theorem escaping_hyperplane_sylow_fixed_intersection (c : Coordinates D S.field)
    (hE : HypothesisE61 CFSG.KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G)) :
    U ⊓ sylowFixedSpace (T : Subgroup G) V ≠ ⊥ := by
  obtain ⟨⟨m⟩,_,hC,_⟩ := escaping_hyperplane_sp4_four D S c hE hunique hUV hU hescape
  exact sp4_hyperplane_sylow_fixed_intersection D S m hC hU

/-- The natural E.6.14 application with its Sylow-fixed geometry now discharged. -/
theorem centralizer_le_of_natural_stabilizer_and_cubic (c : Coordinates D S.field)
    (hE : HypothesisE61 CFSG.KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1)
    (hthree : HasFaithfulThreeAction U)
    (hmax : localNormalizer (L ⊔ (T : Subgroup G)) U ⋖ L ⊔ (T : Subgroup G))
    (hindex : (localNormalizer (L ⊔ (T : Subgroup G)) U).relIndex
      (L ⊔ (T : Subgroup G)) ≠ 2) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  exact hescape (centralizer_le_of_natural_stabilizer D S c hE hunique hUV hU
    (escaping_hyperplane_sylow_fixed_intersection D S c hE hunique hUV hU hescape)
    hthree hmax hindex)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
