module
public import Theory.Representation.ScalarMultiplicity.Semilinear
public import Theory.Representation.SL2.NaturalIrrPlus
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.Semilinear

/-!
# Constructing the two-natural-copy multiplicity action

An equivariant identification of the original moved subgroup with two natural
SL₂ modules transports the full component stabilizer's conjugation action.
The canonical natural action of Aut(SL₂) removes the component action from
each block, leaving the scalar multiplicity representation. Its faithful
image kills L₀: L acts diagonally and the opposite component centralizes the
moved subgroup. The original odd-rank bound and semilinear descent therefore
construct an invariant Irr⁺ constituent, reconstruct the original seed in
either orientation, and exclude two copies by minimality.

Only the natural two-copy identification and source separation are inputs;
no coefficient action, field automorphism, normalizer quotient, or invariant
constituent is assumed. Earlier source decomposition and tensor exclusion
remain with qt-d-10-nona5-central-hall-orders. In particular this does not
assert SeedAnalysisAt or the unconditional central Hall theorem.
Source: Aschbacher--Smith D.3.21(3), 3.2.6, 10.1.1 and 10.2.3,
printed pp.204--207,581,741,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2
local instance : Finite (Module.End (ZMod 2) (Fin 2 → F)) :=
  Finite.of_injective (fun x : Module.End (ZMod 2) (Fin 2 → F) => (x : (Fin 2 → F) → (Fin 2 → F)))
    DFunLike.coe_injective

/-- The natural action inflated along the original two-core quotient marking. -/
@[expose] def naturalComponent (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    Representation (ZMod 2) L (Fin 2 → F) :=
  Representation.SL2AutomorphismNatural.action.comp
    (MulAut.conj.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))

private structure NaturalTwoCopyAction (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) where
  action : Representation (ZMod 2) ↥(D.maximalLocal ⊓ normalizer (L : Set G))
    (Fin 2 → (Fin 2 → F))
  componentAutomorphism : ↥(D.maximalLocal ⊓ normalizer (L : Set G)) →* MulAut (SL(2,F))
  covariant : ∀ n g x,
    action n (fun i => g.val.mulVec (x i)) =
      fun i => (componentAutomorphism n g).val.mulVec (action n x i)
  embedding : (Fin 2 → (Fin 2 → F)) →ₗ[ZMod 2]
    Additive (ReducedNormal.ModuleGroup (localJoin T L))
  injective : Function.Injective embedding
  moved : ReducedNormal.subspaceImage (localJoin T L) embedding.range ≤ ⁅D.fullModule,L⁆
  component_action : ∀ (l : L) x,
    embedding (fun i => naturalComponent e l (x i)) =
      ReducedNormal.representation (localJoin T L)
        (inclusion ((le_componentOrbit L T).trans le_sup_left) l) (embedding x)
  normalizer_action : ∀ n x,
    ((embedding (action n x)).toMul.val : G) =
      (n : G) * ((embedding x).toMul.val : G) * (n : G)⁻¹

private theorem naturalTwoCopyAction_of_embedding
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (j : (Fin 2 → (Fin 2 → F)) →ₗ[ZMod 2]
      Additive (ReducedNormal.ModuleGroup (localJoin T L)))
    (hj : Function.Injective j)
    (hW : ReducedNormal.subspaceImage (localJoin T L) j.range = ⁅D.fullModule,L⁆)
    (hL : ∀ (l : L) x,
      j (fun i => naturalComponent e l (x i)) =
        ReducedNormal.representation (localJoin T L)
          (inclusion ((le_componentOrbit L T).trans le_sup_left) l) (j x)) :
    Nonempty (NaturalTwoCopyAction D e) := by
  let N := D.maximalLocal ⊓ normalizer (L : Set G)
  let W := ReducedNormal.subspaceImage (localJoin T L) j.range
  have hNW : N ≤ normalizer (W : Set G) := by
    rw [show W = ⁅D.fullModule,L⁆ from hW]
    intro n hn
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hn.1),
      mem_normalizer_iff_map_conj_eq.mp hn.2]
  let E := (LinearEquiv.ofInjective j hj).trans
    (ReducedNormal.subspaceEquiv (localJoin T L) j.range)
  have hE (x) : ((E x).toMul : G) = ((j x).toMul.val : G) := rfl
  let r : Representation (ZMod 2) N (Additive W) :=
    Representation.elementaryRepresentation (W.normalizerMonoidHom.comp (inclusion hNW))
  let ρ := (E.symm.conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp r
  have hr (n : N) (x) : ((j (ρ n x)).toMul.val : G) =
      (n : G) * ((j x).toMul.val : G) * (n : G)⁻¹ := by
    rw [←hE]
    change ((E (E.symm (r n (E x)))).toMul : G) = _
    rw [E.apply_symm_apply]
    rfl
  let a : N →* MulAut (SL(2,F)) :=
    (MulAut.congr e).toMonoidHom.comp
      ((normalizerPCoreQuotientAction L).comp (inclusion inf_le_right))
  have hJ : Function.Injective (fun x => ((j x).toMul.val : G)) := by
    intro x y hh
    exact hj (Subtype.ext (Subtype.ext hh))
  have hcomponent (l : L) (x) :
      ((j (fun i => (e (QuotientGroup.mk' (pCore 2 L) l)).val.mulVec (x i))).toMul.val : G) =
        (l : G) * ((j x).toMul.val : G) * (l : G)⁻¹ := by
    have hx : (fun i => (e (QuotientGroup.mk' (pCore 2 L) l)).val.mulVec (x i)) =
        (fun i => naturalComponent e l (x i)) := by
      funext i
      exact (Representation.SL2AutomorphismNatural.action_conj _ _).symm
    rw [hx,hL]
    rfl
  refine ⟨{
    action := ρ
    componentAutomorphism := a
    covariant := ?_
    embedding := j
    injective := hj
    moved := hW.le
    component_action := hL
    normalizer_action := hr }⟩
  intro n g x
  obtain ⟨l,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) g
  let l' : L := L.normalizerMonoidHom (inclusion (show N ≤ normalizer (L : Set G) from inf_le_right) n) l
  have ha : a n (e (QuotientGroup.mk' (pCore 2 L) l)) =
      e (QuotientGroup.mk' (pCore 2 L) l') := by
    change e (normalizerPCoreQuotientAction L (inclusion inf_le_right n)
      (e.symm (e (QuotientGroup.mk' (pCore 2 L) l)))) = _
    rw [e.symm_apply_apply]
    change e (quotientAut (pCore 2 L) _ _) = _
    rw [quotientAut_apply_mk]
  dsimp only [Function.comp_apply]
  rw [ha]
  apply hJ
  dsimp only
  rw [hr,hcomponent,hcomponent,hr]
  change (n : G) * ((l : G) * _ * (l : G)⁻¹) * (n : G)⁻¹ =
    ((n : G) * (l : G) * (n : G)⁻¹) * ((n : G) * _ * (n : G)⁻¹) *
      ((n : G) * (l : G) * (n : G)⁻¹)⁻¹
  group

private theorem coordinates_of_natural_two_copy_action
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (C : NaturalTwoCopyAction D e) :
    ∃ μ : Representation (ZMod 2) ↥(D.maximalLocal ⊓ normalizer (L : Set G)) (Fin 2 → F),
      Nonempty (SemilinearTwoCopyCoordinates D (F := F) μ.asGroupHom.range (Fin 2 → F)) := by
  let N := D.maximalLocal ⊓ normalizer (L : Set G)
  let β := Representation.SL2AutomorphismNatural.action.comp C.componentAutomorphism
  let τ := Representation.SL2AutomorphismNatural.fieldAction.comp C.componentAutomorphism
  let σ := Representation.SL2AutomorphismNatural.action.comp (MulAut.conj : SL(2,F) →* _)
  have hσ (g : SL(2,F)) (v : Fin 2 → F) : σ g v = g.val.mulVec v :=
    Representation.SL2AutomorphismNatural.action_conj g v
  have hs : ∀ f : (Fin 2 → F) →ₗ[ZMod 2] (Fin 2 → F),
      (∀ g v, f (σ g v) = σ g (f v)) → ∃ b : F, ∀ v, f v = b • v := by
    intro f hf
    exact Representation.SL2NaturalOffenders.centralizer_scalar f.toAddMonoidHom
      (by intro g v; change f (g.val.mulVec v) = g.val.mulVec (f v); simpa only [hσ] using hf g v)
  obtain ⟨μ,hμ,hsemi⟩ := Representation.ScalarMultiplicity.exists_semilinear_multiplicity
    σ hs C.action β (fun n g => C.componentAutomorphism n g)
    (by simpa only [hσ] using C.covariant)
    (by intro n g v; simp only [hσ]; exact
      Representation.SL2AutomorphismNatural.action_intertwines (C.componentAutomorphism n) g v)
    τ (fun n b v => Representation.SL2AutomorphismNatural.action_semilinear
      (C.componentAutomorphism n) b v)
  let q := μ.asGroupHom.rangeRestrict
  let ν : Representation (ZMod 2) μ.asGroupHom.range (Fin 2 → F) :=
    (Units.coeHom _).comp μ.asGroupHom.range.subtype
  have hν : Function.Injective ν := by
    intro a b hh
    exact Subtype.ext (Units.ext hh)
  obtain ⟨τ',hτ',hsemi'⟩ := Representation.ScalarMultiplicity.exists_fieldAction_on_image μ τ hsemi
  have hdiag (n : N) (g : SL(2,F))
      (hn : ∀ x, C.action n x = fun i => g.val.mulVec (x i)) : q n = 1 := by
    have ha : C.componentAutomorphism n = MulAut.conj g :=
      Representation.SL2AutomorphismNatural.automorphism_eq_conj_of_diagonal
        _ g (by intro d x; simpa only [hn] using C.covariant n d x)
    have hb (v : Fin 2 → F) : β n v = g.val.mulVec v := by
      change Representation.SL2AutomorphismNatural.action (C.componentAutomorphism n) v = _
      rw [ha,Representation.SL2AutomorphismNatural.action_conj]
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    funext i
    change μ n v i = v i
    let z : Fin 2 → F := ![1,0]
    have hz : z ≠ 0 := by intro h; have hh := congrFun h 0; simp [z] at hh
    have hg : g.val.mulVec z ≠ 0 := by
      intro h
      apply hz
      exact (Matrix.SpecialLinearGroup.toLin' g).injective (h.trans (map_zero _).symm)
    apply smul_left_injective F hg
    have hh := congrFun (hμ n v z) i
    rw [hn,hb] at hh
    simpa only [Matrix.mulVec_smul] using hh.symm
  have hN : localOrbit T L ≤ N := le_inf (localOrbit T L).le_normalizer
    (source_nonnormal_orbit_le_normalizer D c.nonnormal)
  let K := q.ker.map N.subtype
  have hJ : Function.Injective (fun x => ((C.embedding x).toMul.val : G)) := by
    intro x y hh
    exact C.injective (Subtype.ext (Subtype.ext hh))
  have hLK : L ≤ K := by
    intro l hl
    let n : N := ⟨l,hN (le_componentOrbit L T hl)⟩
    have hnl : ∀ x, C.action n x = fun i => naturalComponent e ⟨l,hl⟩ (x i) := by
      intro x
      apply hJ
      dsimp only
      rw [C.normalizer_action,C.component_action]
      rfl
    have hn : ∀ x, C.action n x = fun i =>
        (e (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩)).val.mulVec (x i) := by
      intro x
      rw [hnl]
      funext i
      exact Representation.SL2AutomorphismNatural.action_conj _ _
    exact ⟨n,MonoidHom.mem_ker.mpr (hdiag n _ hn),rfl⟩
  have hp : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 c.nonnormal)
      inf_le_right ht htn
  have hLtK : L.map (MulAut.conj t).toMonoidHom ≤ K := by
    intro l hl
    let n : N := ⟨l,hN (hp ▸ mem_sup_right hl)⟩
    have hn (x) : C.action n x = x := by
      apply hJ
      dsimp only
      rw [C.normalizer_action]
      have hx : ((C.embedding x).toMul.val : G) ∈ ⁅D.fullModule,L⁆ :=
        C.moved ⟨(C.embedding x).toMul.val,⟨(C.embedding x).toMul,⟨x,rfl⟩,rfl⟩,rfl⟩
      have hc := mem_centralizer_iff.mp
        (full_moved_centralizes_opposite_of_seed_separated D ht htn hsep hx) l hl
      change l * _ * l⁻¹ = _
      rw [hc,mul_assoc,mul_inv_cancel,mul_one]
    exact ⟨n,MonoidHom.mem_ker.mpr (hdiag n 1 (by intro x; simpa using hn x)),rfl⟩
  have hOK : localOrbit T L ≤ K := by rw [hp]; exact sup_le hLK hLtK
  have hkill : (localOrbit T L).subgroupOf N ≤ q.ker := by
    intro n hn
    obtain ⟨m,hm,he⟩ := hOK hn
    have he' : m = n := Subtype.ext he
    exact he' ▸ hm
  refine ⟨μ,⟨{
    quotient := q
    onto := μ.asGroupHom.rangeRestrict_surjective
    orbit_killed := hkill
    multiplicity := ν
    faithful := hν
    coefficients := τ'
    semilinear := hsemi'
    model := naturalComponent e
    model_irrPlus := Representation.SL2AutomorphismNatural.natural_irrPlus_of_surjective
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
    embedding := C.embedding
    injective := C.injective
    moved := C.moved
    component_action := ?_
    model_normalizer := fun n v => β n v
    normalizer_action := ?_ }⟩⟩
  · intro l b v
    have hs' : (fun i => b i • naturalComponent e l v) =
        (fun i => naturalComponent e l (b i • v)) := by
      funext i
      change b i • Representation.SL2AutomorphismNatural.action (MulAut.conj _) v = _
      simp only [naturalComponent,MonoidHom.comp_apply,
        Representation.SL2AutomorphismNatural.action_conj,Matrix.mulVec_smul]
    rw [hs']
    exact C.component_action l _
  · intro n b v
    have hh := C.normalizer_action n (fun i => b i • v)
    rw [hμ] at hh
    exact hh
/-- The constructed invariant constituent reconstructs the same original seed. -/
theorem separatedSeed_of_two_natural_copies
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (j : (Fin 2 → (Fin 2 → F)) →ₗ[ZMod 2]
      Additive (ReducedNormal.ModuleGroup (localJoin T L)))
    (hj : Function.Injective j)
    (hW : ReducedNormal.subspaceImage (localJoin T L) j.range = ⁅D.fullModule,L⁆)
    (hL : ∀ (l : L) x,
      j (fun i => naturalComponent e l (x i)) =
        ReducedNormal.representation (localJoin T L)
          (inclusion ((le_componentOrbit L T).trans le_sup_left) l) (j x)) :
    SeparatedSeed D t := by
  obtain ⟨C⟩ := naturalTwoCopyAction_of_embedding D e j hj hW hL
  obtain ⟨μ,⟨S⟩⟩ := coordinates_of_natural_two_copy_action D c ht htn hsep e C
  exact separatedSeed_of_semilinear_two_copies D c ht htn hsep e S

/-- The actual two-natural-copy alternative is incompatible with original
minimality. No normalizer action, multiplicity quotient, field action, or
invariant constituent is supplied as an extra premise. -/
theorem no_two_natural_copies_of_separated
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (j : (Fin 2 → (Fin 2 → F)) →ₗ[ZMod 2]
      Additive (ReducedNormal.ModuleGroup (localJoin T L)))
    (hj : Function.Injective j)
    (hW : ReducedNormal.subspaceImage (localJoin T L) j.range = ⁅D.fullModule,L⁆)
    (hL : ∀ (l : L) x,
      j (fun i => naturalComponent e l (x i)) =
        ReducedNormal.representation (localJoin T L)
          (inclusion ((le_componentOrbit L T).trans le_sup_left) l) (j x)) : False := by
  obtain ⟨C⟩ := naturalTwoCopyAction_of_embedding D e j hj hW hL
  obtain ⟨μ,⟨S⟩⟩ := coordinates_of_natural_two_copy_action D c ht htn hsep e C
  exact no_semilinear_two_copies_of_separated D c ht htn hsep e S

/-- The constructed original-seed data feeds the literal Hall consumer.
The earlier source separation and module decomposition remain with this
module's owner, qt-d-10-nona5-central-hall-orders. -/
theorem hall_exponent_of_two_natural_copies
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (j : (Fin 2 → (Fin 2 → F)) →ₗ[ZMod 2]
      Additive (ReducedNormal.ModuleGroup (localJoin T L)))
    (hj : Function.Injective j)
    (hW : ReducedNormal.subspaceImage (localJoin T L) j.range = ⁅D.fullModule,L⁆)
    (hL : ∀ (l : L) x,
      j (fun i => naturalComponent e l (x i)) =
        ReducedNormal.representation (localJoin T L)
          (inclusion ((le_componentOrbit L T).trans le_sup_left) l) (j x)) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2 ^ n + 1 := by
  obtain ⟨C⟩ := naturalTwoCopyAction_of_embedding D e j hj hW hL
  obtain ⟨μ,⟨S⟩⟩ := coordinates_of_natural_two_copy_action D c ht htn hsep e C
  exact hall_exponent_of_semilinear_two_copies D c hnot ht htn hsep e S

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
