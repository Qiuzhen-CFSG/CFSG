module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.CriticalImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.ReciprocalCoordinates
public import Theory.Representation.SymplecticNaturalNormalizer.FixedSeedInner
public import Theory.SpecificGroups.SymplecticFour.QuadraticPlane

/-!
# Movement of the whole X-layer by the critical symplectic root

At a critical pair, the opposite moving cover lies in the starting vertex
stabilizer. Its subgroup fixed by Z_a is therefore contained in C_a = Q_a,
so X_a = Omega-one of the center of Q_a centralizes this entire subgroup.
Fixed-point lifting in the actual cover shows that the ambient X_a image
fixes the natural critical hyperplane. A fixed field line removes the outer
field automorphism, and symplectic orthogonality bounds the inner image by
the field order. The literal vertex quotient identifies its image order
with the original centralizer index.

This proves the movement estimate in MS93 (3.3)(ii)(2), printed p.867,
after the critical image has been shown to have one-dimensional displacement.
It keeps the whole central attachment and assumes no decomposition of X.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterB.QuasisimpleSource Representation.SymplecticFourOrthogonalCover

variable {H : Type*} [Group H] [Finite H] {R : Subgroup H}
  {geometry : Geometry R} {a z : Vertex R}

/-- The critical X-layer reaches the opposite stabilizer through the last edge. -/
theorem critical_X_le_endpoint_stabilizer
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hedge : EdgeCentralizerCondition R) : X R a ≤ stabilizer R z := by
  have hne : a ≠ z := by
    intro he
    have hc := path.critical.1
    rw [geometry.distance_constant a path.start_color] at hc
    change (cosetGraph R).dist a z = geometry.b R at hc
    have hz : (cosetGraph R).dist a z = 0 := by rw [he,SimpleGraph.dist_self]
    omega
  have hn : ¬ path.walk.Nil := fun hn => hne hn.eq
  have ht : Adjacent R path.walk.penultimate z :=
    (cosetGraph_adj R _ _).mp (path.walk.adj_penultimate hn)
  have hsmall : (cosetGraph R).dist a path.walk.penultimate <
      criticalDistance R a (geometry.exists_critical a path.start_color) := by
    have hl := path.walk.length_dropLast_add_one hn
    have hd := SimpleGraph.dist_le path.walk.dropLast
    have he := path.shortest
    have hc := path.critical.1
    omega
  exact (X_le_Q_of_dist_lt R geometry hedge a path.start_color _ hsmall).trans
    (fun _ hx => hx.2 z ht)

omit [Finite H] in
/-- The core centrality of X fixes the actual opposite moving subgroup fixed by Z. -/
theorem critical_X_centralizes_fixed_moving
    (path : CriticalPath R geometry a z) (hCa : C R a = Q R a) :
    X R a ≤ centralizer ((U R z ⊓ centralizer (Z R a : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  have hZa : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  intro x hx u hu
  have hQ : u ∈ Q R a := by
    rw [←hCa]
    exact ⟨hZa (U_le_Z z hu.1),hu.2⟩
  exact (Q_le_centralizer_X R a hQ x hx).symm

private theorem card_le_field_of_fixes_root_hyperplane
    {F : Type*} [Field F] [Finite F]
    (A B : Subgroup (Sp F))
    (hd : Module.finrank F (displacementSpace A) = 1)
    (hf : TwoLocalCover.fixedSpace A ≤ TwoLocalCover.fixedSpace B) :
    Nat.card B ≤ Nat.card F := by
  have hdim := Submodule.finrank_mono hf
  rw [←orthogonal_displacementSpace A,←orthogonal_displacementSpace B,
    LinearMap.BilinForm.finrank_orthogonal TwoLocalCover.form_nondegenerate,
    LinearMap.BilinForm.finrank_orthogonal TwoLocalCover.form_nondegenerate,hd] at hdim
  have hle := (displacementSpace B).finrank_le
  have hB : Module.finrank F (displacementSpace B) ≤ 1 := by omega
  have hc := card_actor_le_displacement_dimension B
  calc
    Nat.card B ≤ Nat.card F ^ (Module.finrank F (displacementSpace B))^2 := hc
    _ ≤ Nat.card F ^ 1 := Nat.pow_le_pow_right Nat.card_pos (by nlinarith)
    _ = Nat.card F := pow_one _

variable {J V F : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite H] in
/-- The specific critical root bounds movement of the whole X-layer.
The inner X marking is constructed from the fixed cover seed. -/
theorem critical_X_movement_bound_of_root_coordinates
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hCa : C R a = Q R a) (hF : 2 < Nat.card F)
    (s : MovedSection ρ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hcent : centralizer (B : Set J) = ⊥)
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = U R z)
    (δ : X R a →* J)
    (hδker : δ.ker = (centralizer (Z R z : Set (FreeAmalgam R))).subgroupOf (X R a))
    (hδ : ∀ x : X R a, ∀ w : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) w)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (x : FreeAmalgam R)⁻¹)
    (β : Z R a →* L (K := F))
    (hβ : ∀ x : Z R a, ∀ w : s.space.toSubmodule,
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β x) w)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (x : FreeAmalgam R)⁻¹)
    (hd : Module.finrank F
      (displacementSpace (β.range.map (commutator (Sp F)).subtype)) = 1) :
    (centralizer (Z R z : Set (FreeAmalgam R))).relIndex (X R a) ≤ Nat.card F := by
  let p := MovedSection.coverProjection s e
  let σ := MovedSection.coverAction s e
  let ψ := MovedSection.ambientAction s e
  have hfix (x : X R a) (w : s.space.toSubmodule)
      (hw : w ∈ OneCohomology.fixed (σ.comp β.range.subtype)) :
      s.space.toRepresentation (δ x) w = w := by
    have hjw : j (Multiplicative.ofAdd w) ∈ U R z := by
      rw [←hjr]
      exact ⟨Multiplicative.ofAdd w,rfl⟩
    have hc : j (Multiplicative.ofAdd w) ∈
        centralizer (Z R a : Set (FreeAmalgam R)) := by
      intro y hy
      have hh := hβ ⟨y,hy⟩ w
      have he := hw (⟨β ⟨y,hy⟩,⟨⟨y,hy⟩,rfl⟩⟩ : β.range)
      change σ (β ⟨y,hy⟩) w = w at he
      rw [show MovedSection.coverAction s e (β ⟨y,hy⟩) w = w from he] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm)
    apply Multiplicative.ofAdd.injective
    apply hj
    rw [hδ]
    have hc' := critical_X_centralizes_fixed_moving path hCa x.property
      (j (Multiplicative.ofAdd w)) ⟨hjw,hc⟩
    rw [←hc',mul_inv_cancel_right]
  let : IsElementaryAbelian 2 (Z R a) := geometry.Z_elementary hb a path.start_color
  have hP : IsPGroup 2 β.range :=
    (IsElementaryAbelian.isPGroup 2 (Z R a)).of_surjective β.rangeRestrict β.rangeRestrict_surjective
  let d : L (K := F) ≃* Sp F :=
    (MulEquiv.subgroupCongr
      (OneCohomology.SymplecticFour.LargeField.commutator_eq_top hF)).trans Subgroup.topEquiv
  have hinner (x : X R a) : δ x ∈ B :=
    SymplecticNaturalNormalizer.mem_component_of_fixes_cover_seed B
      (hcent ▸ bot_le) hF (e.groupEquiv.trans d) ψ
      (fun b v => MovedSection.ambientAction_component s e b v)
      p hp β.range hP (δ x) (s.space.toRepresentation (δ x))
      (fun w => MovedSection.coverProjection_ambient s e (δ x) w) (hfix x)
  let γ : X R a →* Sp F := (e.groupEquiv.trans d).toMonoidHom.comp
    (δ.codRestrict B hinner)
  have hγ (x : X R a) (v : Vector F) : ψ (δ x) v = γ x • v := by
    have he := MovedSection.ambientAction_component s e (⟨δ x,hinner x⟩ : B) v
    exact he
  have hγker : γ.ker = δ.ker := by
    ext x
    change (e.groupEquiv.trans d) ⟨δ x,hinner x⟩ = 1 ↔ δ x = 1
    rw [(e.groupEquiv.trans d).map_eq_one_iff]
    exact Subtype.ext_iff
  have hfixed : TwoLocalCover.fixedSpace (β.range.map (commutator (Sp F)).subtype) ≤
      TwoLocalCover.fixedSpace γ.range := by
    intro v hv g hg
    obtain ⟨x,rfl⟩ := hg
    obtain ⟨w,rfl⟩ := hp.1 v
    have hw : w ∈ OneCohomology.fixed (σ.comp β.range.subtype) := by
      rw [cover_fixed_preimage p hp]
      intro b
      exact hv b.val.val (mem_map_of_mem _ b.property)
    rw [←hγ,←MovedSection.coverProjection_ambient,hfix x w hw]
  have hc := card_le_field_of_fixes_root_hyperplane
    (β.range.map (commutator (Sp F)).subtype) γ.range hd hfixed
  change ((centralizer (Z R z : Set (FreeAmalgam R))).subgroupOf (X R a)).index ≤ _
  rw [←hδker,←hγker,index_ker]
  exact hc

/-- Apply the movement bound to the literal original vertex quotient,
retaining its exact centralizer kernel and its complete moved cover. -/
theorem critical_X_movement_bound_of_vertex_coordinates
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hedge : EdgeCentralizerCondition R)
    (hCa : C R a = Q R a) (hF : 2 < Nat.card F)
    (s : MovedSection ρ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hcent : centralizer (B : Set J) = ⊥)
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = U R z)
    (κ : stabilizer R z →* J)
    (hκC : κ.ker.map (stabilizer R z).subtype = C R z)
    (hκ : ∀ x : stabilizer R z, ∀ w : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (κ x) w)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (x : FreeAmalgam R)⁻¹)
    (β : Z R a →* L (K := F))
    (hβ : ∀ x : Z R a, ∀ w : s.space.toSubmodule,
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β x) w)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (x : FreeAmalgam R)⁻¹)
    (hd : Module.finrank F
      (displacementSpace (β.range.map (commutator (Sp F)).subtype)) = 1) :
    (centralizer (Z R z : Set (FreeAmalgam R))).relIndex (X R a) ≤ Nat.card F := by
  have hX := critical_X_le_endpoint_stabilizer path hb hedge
  let δ := κ.comp (inclusion hX)
  have hk : δ.ker = (centralizer (Z R z : Set (FreeAmalgam R))).subgroupOf (X R a) :=
    restricted_kernel_of_mapped_centralizer (X R a) (stabilizer R z) (Z R z) hX κ hκC
  exact critical_X_movement_bound_of_root_coordinates path hb hCa hF s e hp hcent
    j hj hjr δ hk (fun x w => hκ (inclusion hX x) w) β hβ hd

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
