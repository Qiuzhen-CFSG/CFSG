module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicCentrality
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CoreRestriction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CoreParity

/-!
# Restricted actors on the entire cubic central cover

The original six-letter action transports the natural and augmentation
calculations to the full initial moving subgroup. A controlling restriction
preserves the complete critical commutator. On the augmentation cover this
forces an even involution in the same marked reverse image.

The embedded forms measure indices modulo the actual two-core using the
odd-order kernel quotient; they never identify the cubic action kernel with
that two-core. CubicRestrictedActor applies these results to the original
critical paths and discharges the restricted-actor premise of radius centrality.
The proof adapts Natural.Exhaustion.LargeDistance.SectionFive.CoreRestriction
and RestrictedActor. Source: MS93 (3.3)(ii), pp.866--867, and (5.2), pp.914--915.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterB.Offenders
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open CubicAction
open AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "D" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le (commutator_le_left _ _)
private abbrev coverAction : Representation (ZMod 2) S (Additive D) := by
  let := h.relative_normal
  exact NormalElementaryQuotient.representation D π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)
local notation "σ" => coverAction h e hz hk
private theorem coverAction_conjugate (g : M) (v : Additive D) :
    ((σ (π g) v).toMul : M) = g * (v.toMul : M) * g⁻¹ := by
  let := h.relative_normal
  exact NormalElementaryQuotient.representation_apply D π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk) g v

private theorem cover_fixed_moved (A Y : Subgroup M)
    (hfix : ⁅D,A⁆ ≤ centralizer (Y : Set M)) :
    Y.map π ≤ subspaceKernel σ
      (subspaceCommutator σ ⊤ (A.map π)) ⊤ := by
  let := h.relative_normal
  intro y hy
  obtain ⟨x,hx,rfl⟩ := hy
  refine ⟨mem_top _,?_⟩
  intro v hv
  have hm := NormalElementaryQuotient.commutatorSpace_eq (D) π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk) A
  change NormalElementaryQuotient.commutatorSpace (D) A =
    subspaceCommutator σ ⊤ (A.map π) at hm
  rw [←hm] at hv
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [coverAction_conjugate]
  have hh : x * (v.toMul : M) = (v.toMul : M) * x := hfix hv x hx
  rw [hh,mul_inv_cancel_right]

private theorem cover_space_map {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (τ : Representation (ZMod 2) S V) (E : Additive (D) ≃ₗ[ZMod 2] V)
    (hE : ∀ g v, E (σ g v) = τ g (E v)) (A : Subgroup M) :
    (NormalElementaryQuotient.commutatorSpace (D) A).map E.toLinearMap =
      subspaceCommutator τ ⊤ (A.map π) := by
  let := h.relative_normal
  rw [NormalElementaryQuotient.commutatorSpace_eq (D) π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)]
  have hh := subspaceCommutator_map_embedding τ σ (MonoidHom.id S) E.toLinearMap
    (fun g v => (hE g v).symm) (A.map π) ⊤
  rw [Submodule.map_top,LinearMap.range_eq_top.mpr E.surjective,Subgroup.map_id] at hh
  exact hh.symm

private theorem coordinates_fixer {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (τ : Representation (ZMod 2) S V) (E : Additive (D) ≃ₗ[ZMod 2] V)
    (hE : ∀ g v, E (σ g v) = τ g (E v)) (A Y : Subgroup M)
    (hfix : ⁅D,A⁆ ≤ centralizer (Y : Set M)) :
    Y.map π ≤ subspaceKernel τ (subspaceCommutator τ ⊤ (A.map π)) ⊤ := by
  let := h.relative_normal
  intro y hy
  refine ⟨mem_top _,?_⟩
  intro v hv
  rw [←cover_space_map h e hz hk τ E hE A] at hv
  obtain ⟨w,hw,rfl⟩ := hv
  have hh := cover_fixed_moved h e hz hk A Y hfix hy
  have hm := NormalElementaryQuotient.commutatorSpace_eq (D) π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk) A
  change NormalElementaryQuotient.commutatorSpace (D) A =
    subspaceCommutator σ ⊤ (A.map π) at hm
  change τ y (E w) = E w
  rw [←hE,hh.2 w (hm ▸ hw)]

private theorem coordinates_commutator_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (τ : Representation (ZMod 2) S V) (E : Additive (D) ≃ₗ[ZMod 2] V)
    (hE : ∀ g v, E (σ g v) = τ g (E v))
    (P : Submodule (ZMod 2) (Additive (D))) (W : Submodule (ZMod 2) V)
    (hP : P.map E.toLinearMap ≤ W) (A Y : Subgroup M)
    (hc : subspaceCommutator τ W (Y.map π) ≤ subspaceCommutator τ ⊤ (A.map π)) :
    ⁅P.toAddSubgroup.toSubgroup'.map (D).subtype,Y⁆ ≤ ⁅D,A⁆ := by
  let := h.relative_normal
  rw [commutator_comm]
  apply commutator_le.mpr
  rintro y hy _ ⟨v,hv,rfl⟩
  have hvW : E (Additive.ofMul v) ∈ W := hP (Submodule.mem_map_of_mem hv)
  have hdiff : τ (π y) (E (Additive.ofMul v))-E (Additive.ofMul v) ∈
      subspaceCommutator τ ⊤ (A.map π) :=
    hc (Submodule.subset_span ⟨_,mem_map_of_mem π hy,_,hvW,rfl⟩)
  rw [←cover_space_map h e hz hk τ E hE A] at hdiff
  have hm : σ (π y) (Additive.ofMul v)-Additive.ofMul v ∈
      NormalElementaryQuotient.commutatorSpace (D) A := by
    obtain ⟨w,hw,he⟩ := hdiff
    have he' : w = σ (π y) (Additive.ofMul v)-Additive.ofMul v := by
      apply E.injective
      rw [map_sub,hE]
      exact he
    exact he' ▸ hw
  change (((σ (π y) (Additive.ofMul v)).toMul / v : D) : M) ∈
    ⁅D,A⁆ at hm
  simp only [div_eq_mul_inv,Subgroup.coe_mul,Subgroup.coe_inv] at hm
  rw [coverAction_conjugate] at hm
  exact hm


private theorem coordinates_movement_preserved {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (τ : Representation (ZMod 2) S V) (E : Additive (D) ≃ₗ[ZMod 2] V)
    (hE : ∀ g v, E (σ g v) = τ g (E v))
    (P : Submodule (ZMod 2) (Additive (D))) (W : Submodule (ZMod 2) V)
    (hP : P.map E.toLinearMap = W) (A : Subgroup M)
    (hm : subspaceCommutator τ W (A.map π) = subspaceCommutator τ ⊤ (A.map π)) :
    ⁅P.toAddSubgroup.toSubgroup'.map (D).subtype,A⁆ = ⁅D,A⁆ := by
  let := h.relative_normal
  let F := P.toAddSubgroup.toSubgroup'.map (D).subtype
  have hFU : F ≤ D := (map_le_range _ _).trans_eq (range_subtype _)
  let N := ⁅F,A⁆
  let C := AddSubgroup.toZModSubmodule 2 (N.subgroupOf (D)).toAddSubgroup
  have hbound : subspaceCommutator τ W (A.map π) ≤ C.map E.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨a,ha,rfl⟩,v,hv,rfl⟩
    rw [←hP] at hv
    obtain ⟨w,hw,rfl⟩ := hv
    refine ⟨σ (π a) w-w,?_,by
      change E (σ (π a) w-w) = _
      exact (map_sub E.toLinearMap _ _).trans
        (congrArg (fun z => z-E w) (hE (π a) w))⟩
    change (((σ (π a) w).toMul / w.toMul : D) : M) ∈ N
    simp only [div_eq_mul_inv,Subgroup.coe_mul,Subgroup.coe_inv]
    rw [coverAction_conjugate]
    change ⁅a,(w.toMul : M)⁆ ∈ ⁅F,A⁆
    rw [commutator_comm]
    exact commutator_mem_commutator ha (mem_map_of_mem _ hw)
  rw [hm,←cover_space_map h e hz hk τ E hE A] at hbound
  have hh : NormalElementaryQuotient.commutatorSpace (D) A ≤ C :=
    (Submodule.map_le_map_iff_of_injective E.injective _ _).mp hbound
  apply le_antisymm (commutator_mono hFU le_rfl)
  intro x hx
  exact hh (show Additive.ofMul (⟨x,(commutator_le_left _ _) hx⟩ : D) ∈
    NormalElementaryQuotient.commutatorSpace (D) A from hx)


/-- A controlling subactor retaining the complete original commutator. -/
theorem cover_restriction_preserving (A : Subgroup M) [IsElementaryAbelian 2 A]
    (hcard : 4 ≤ Nat.card (A.map π))
    (hquad : ⁅D,A⁆ ≤ centralizer (A : Set M)) :
    ∃ W : Subgroup M, W ≤ D ∧
      W.relIndex (D) ≤ 2 ∧
      ⁅W,A⁆ = ⁅D,A⁆ ∧
      ∀ Y : Subgroup M, ⁅D,A⁆ ≤ centralizer (Y : Set M) →
        ⁅W,Y⁆ ≤ ⁅D,A⁆ := by
  let := h.relative_normal
  let := IsElementaryAbelian.map (p:=2) (A:=A) π
  rcases moved_subgroup_cover_model h e hz hk with ⟨E,hE⟩ | ⟨E,hE⟩
  · refine ⟨D,le_rfl,by simp,rfl,?_⟩
    intro Y hY
    have hh := natural_moved_control _ _ hcard ((by
        intro a ha b hb v
        exact (coordinates_fixer h e hz hk _ E hE A A hquad ha).2 _
          (Submodule.subset_span ⟨b,hb,v,Submodule.mem_top,rfl⟩)))
      (coordinates_fixer h e hz hk _ E hE A Y hY)
    have hm : NormalElementaryQuotient.commutatorSpace (D) Y ≤
        NormalElementaryQuotient.commutatorSpace (D) A := by
      apply (Submodule.map_le_map_iff_of_injective (f:=E.toLinearMap) E.injective _ _).mp
      rwa [cover_space_map h e hz hk _ E hE Y,cover_space_map h e hz hk _ E hE A]
    intro x hx
    exact hm (show Additive.ofMul (⟨x,(commutator_le_left _ _) hx⟩ : D) ∈
      NormalElementaryQuotient.commutatorSpace (D) Y from hx)
  · have hq : CoreActor.Quadratic (A.map π) := by
      intro a ha b hb v
      exact (coordinates_fixer h e hz hk _ E hE A A hquad ha).2 _
        (Submodule.subset_span ⟨b,hb,v,Submodule.mem_top,rfl⟩)
    obtain ⟨W,hW,hpres,hcontrol⟩ := core_restriction_preserving _ hcard hq
    let P := W.comap E.toLinearMap
    let F := P.toAddSubgroup.toSubgroup'
    refine ⟨F.map (D).subtype,(map_le_range (D).subtype F).trans_eq (range_subtype _),?_,?_,?_⟩
    · have hP : Module.finrank (ZMod 2) P = Module.finrank (ZMod 2) W := by
        have hm : P.map E.toLinearMap = W := Submodule.map_comap_eq_of_surjective E.surjective W
        rw [←hm,E.finrank_map_eq]
      have hF : 16 ≤ Nat.card F := by
        change 16 ≤ Nat.card P
        rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,hP]
        exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hW
      have hU : Nat.card (D) = 32 := by
        change Nat.card (Additive (D)) = 32
        rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,finrank_core]
        decide
      have hc := F.card_mul_index
      rw [hU] at hc
      have hm : (⊤ : Subgroup (D)).map (D).subtype = D := by
        rw [←MonoidHom.range_eq_map,range_subtype]
      have hidx := relIndex_map_map_of_injective F ⊤ (D).subtype_injective
      rw [hm,relIndex_top_right] at hidx
      rw [hidx]
      have hpos := Nat.card_pos (α:=F)
      nlinarith
    · exact coordinates_movement_preserved h e hz hk _ E hE P W
        (Submodule.map_comap_eq_of_surjective E.surjective W) A hpres
    · intro Y hY
      apply coordinates_commutator_le h e hz hk _ E hE P W
      · exact (Submodule.map_comap_eq_of_surjective E.surjective W).le
      · exact hcontrol (Y.map π) (coordinates_fixer h e hz hk _ E hE A Y hY)

include h e hz hk in
/-- The restriction commutes with every injective ambient realization,
including conjugated vertex stabilizers in the actual amalgam. -/
theorem embedded_cover_restriction_preserving {H : Type*} [Group H]
    (i : M →* H) (hi : Function.Injective i)
    (A : Subgroup H) [IsElementaryAbelian 2 A] (hA : A ≤ i.range)
    (hcard : 4 ≤ ((pCore 2 M).map i).relIndex A)
    (hquad : ⁅(D).map i,A⁆ ≤ centralizer (A : Set H)) :
    ∃ W : Subgroup H, W ≤ (D).map i ∧
      W.relIndex ((D).map i) ≤ 2 ∧
      ⁅W,A⁆ = ⁅(D).map i,A⁆ ∧
      ∀ Y : Subgroup H, Y ≤ i.range →
        ⁅(D).map i,A⁆ ≤ centralizer (Y : Set H) →
        ⁅W,Y⁆ ≤ ⁅(D).map i,A⁆ := by
  let := h.relative_normal
  let A₀ := A.comap i
  let := IsElementaryAbelian.comap_of_injective (p:=2) i hi A
  have hmA : A₀.map i = A := map_comap_eq_self hA
  have hcard₀ : 4 ≤ Nat.card (A₀.map π) := by
    rw [CubicAction.permutation_image_card_of_two h e hz hk A₀
      (IsElementaryAbelian.isPGroup 2 A₀)]
    rw [←hmA,relIndex_map_map_of_injective _ _ hi] at hcard
    exact hcard
  have hfix (B : Subgroup H)
      (hc : ⁅(D).map i,A⁆ ≤ centralizer (B : Set H)) :
      ⁅D,A₀⁆ ≤ centralizer (B.comap i : Set M) := by
    intro x hx b hb
    apply hi
    simp only [map_mul]
    apply hc
    · rw [←hmA,←map_commutator]
      exact mem_map_of_mem i hx
    · exact hb
  obtain ⟨W,hW,hindex,hpres,hcontrol⟩ := cover_restriction_preserving h e hz hk A₀ hcard₀ (hfix A hquad)
  refine ⟨W.map i,map_mono hW,?_,?_,?_⟩
  · rwa [relIndex_map_map_of_injective _ _ hi]
  · have hh := congrArg (fun B : Subgroup M => B.map i) hpres
    simpa only [map_commutator,hmA] using hh
  · intro Y hY hc
    have hh := map_mono (f:=i) (hcontrol (Y.comap i) (hfix Y hc))
    rwa [map_commutator,map_commutator,map_comap_eq_self hY,hmA] at hh



private theorem core_coordinates_moved
    (E : Additive (D) ≃ₗ[ZMod 2] (core (Fin 6)))
    (hE : ∀ g v, E (σ g v) = (coreRepresentation (Fin 6)) g (E v)) (A : Subgroup M) :
    (NormalElementaryQuotient.commutatorSpace (D) A).map E.toLinearMap =
      subspaceCommutator (coreRepresentation (Fin 6)) ⊤ (A.map π) := by
  let := h.relative_normal
  rw [NormalElementaryQuotient.commutatorSpace_eq (D) π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)]
  have hh := subspaceCommutator_map_embedding (coreRepresentation (Fin 6)) σ (MonoidHom.id S)
    E.toLinearMap (fun g v => (hE g v).symm) (A.map π) ⊤
  rw [Submodule.map_top,LinearMap.range_eq_top.mpr E.surjective,Subgroup.map_id] at hh
  exact hh.symm

private theorem core_coordinates_quadratic
    (E : Additive (D) ≃ₗ[ZMod 2] (core (Fin 6)))
    (hE : ∀ g v, E (σ g v) = (coreRepresentation (Fin 6)) g (E v)) (A : Subgroup M)
    (hq : ⁅D,A⁆ ≤ centralizer (A : Set M)) :
    CoreActor.Quadratic (A.map π) := by
  let := h.relative_normal
  intro a ha b hb v
  obtain ⟨x,hx,rfl⟩ := ha
  have hmove : (coreRepresentation (Fin 6)) b v-v ∈ subspaceCommutator (coreRepresentation (Fin 6)) ⊤ (A.map π) :=
    Submodule.subset_span ⟨b,hb,v,Submodule.mem_top,rfl⟩
  rw [←core_coordinates_moved h e hz hk E hE A] at hmove
  obtain ⟨w,hw,he⟩ := hmove
  rw [←he]
  change (coreRepresentation (Fin 6)) (π x) (E w) = E w
  rw [←hE]
  congr 1
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [coverAction_conjugate]
  have hh : x * (w.toMul : M) = (w.toMul : M) * x := hq hw x hx
  rw [hh,mul_inv_cancel_right]

/-- On the original order-thirty-two cover, preserving the full commutator
of a large quadratic actor forces an actual even involution in its subactor. -/
theorem cover_preserving_actor_even (hcore : Nat.card (D) = 32)
    (A W : Subgroup M) [IsElementaryAbelian 2 A]
    (hW : W ≤ A) (hcard : 4 ≤ Nat.card (A.map π))
    (hq : ⁅D,A⁆ ≤ centralizer (A : Set M))
    (hpres : ⁅D,W⁆ = ⁅D,A⁆) :
    ∃ a ∈ W.map π, orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  let := h.relative_normal
  let := IsElementaryAbelian.map (p := 2) (A := A) π
  rcases moved_subgroup_cover_model h e hz hk with ⟨E,_⟩ | ⟨E,hE⟩
  · have hc : Nat.card (D) = 16 := by
      change Nat.card (Additive (D)) = 16
      rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,
        finrank_natural_even (Fin 6) (by decide)]
      decide
    omega
  · apply core_preserving_actor_even _ _ (map_mono hW) hcard
      (core_coordinates_quadratic h e hz hk E hE A hq)
    rw [←core_coordinates_moved h e hz hk E hE W,←core_coordinates_moved h e hz hk E hE A]
    congr 1
    unfold NormalElementaryQuotient.commutatorSpace
    rw [hpres]

include h e hz hk in
/-- The same marked even actor survives every injective endpoint realization. -/
theorem embedded_preserving_actor_even (hcore : Nat.card (D) = 32)
    {H : Type*} [Group H] (i : M →* H) (hi : Function.Injective i)
    (A W : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : A ≤ i.range) (hW : W ≤ A)
    (hcard : 4 ≤ ((pCore 2 M).map i).relIndex A)
    (hq : ⁅(D).map i,A⁆ ≤ centralizer (A : Set H))
    (hpres : ⁅(D).map i,W⁆ = ⁅(D).map i,A⁆) :
    ∃ a ∈ (W.comap i).map π, orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  let := h.relative_normal
  let A₀ := A.comap i
  let W₀ := W.comap i
  let := IsElementaryAbelian.comap_of_injective (p := 2) i hi A
  have hmA : A₀.map i = A := map_comap_eq_self hA
  have hmW : W₀.map i = W := map_comap_eq_self (hW.trans hA)
  have hcard₀ : 4 ≤ Nat.card (A₀.map π) := by
    rw [CubicAction.permutation_image_card_of_two h e hz hk A₀
      (IsElementaryAbelian.isPGroup 2 A₀)]
    rw [←hmA,relIndex_map_map_of_injective _ _ hi] at hcard
    exact hcard
  apply cover_preserving_actor_even h e hz hk hcore A₀ W₀ (comap_mono hW) hcard₀
  · intro x hx a ha
    apply hi
    simp only [map_mul]
    apply hq
    · rw [←hmA,←map_commutator]
      exact mem_map_of_mem i hx
    · exact ha
  · apply (map_injective hi)
    simpa only [map_commutator,hmA,hmW] using hpres


/-- On the natural cover, the complete moving group controls every fixer. -/
theorem natural_cover_commutator_control (hnat : Nat.card D = 16)
    (A Y : Subgroup M) [IsElementaryAbelian 2 A]
    (hcard : 4 ≤ Nat.card (A.map π))
    (hAA : ⁅D,A⁆ ≤ centralizer (A : Set M))
    (hAY : ⁅D,A⁆ ≤ centralizer (Y : Set M)) :
    ⁅D,Y⁆ ≤ ⁅D,A⁆ := by
  let := h.relative_normal
  let := IsElementaryAbelian.map (p := 2) (A := A) π
  rcases moved_subgroup_cover_model h e hz hk with ⟨E,hE⟩ | ⟨E,_⟩
  · have hq : QuadraticPointCore.Quadratic (A.map π) := by
      intro a ha b hb v
      exact (coordinates_fixer h e hz hk _ E hE A A hAA ha).2 _
        (Submodule.subset_span ⟨b,hb,v,Submodule.mem_top,rfl⟩)
    have hc := natural_moved_control _ _ hcard hq
      (coordinates_fixer h e hz hk _ E hE A Y hAY)
    have hm : NormalElementaryQuotient.commutatorSpace D Y ≤
        NormalElementaryQuotient.commutatorSpace D A := by
      apply (Submodule.map_le_map_iff_of_injective (f := E.toLinearMap) E.injective _ _).mp
      rwa [cover_space_map h e hz hk _ E hE Y,cover_space_map h e hz hk _ E hE A]
    intro x hx
    exact hm (show Additive.ofMul (⟨x,(commutator_le_left _ _) hx⟩ : D) ∈
      NormalElementaryQuotient.commutatorSpace D Y from hx)
  · have hc : Nat.card D = 32 := by
      change Nat.card (Additive D) = 32
      rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
        Nat.card_zmod,finrank_core]
      decide
    omega

include h e hz hk in
/-- Natural-cover control through the literal endpoint embedding, modulo Q. -/
theorem embedded_natural_commutator_control (hnat : Nat.card D = 16)
    {H : Type*} [Group H] (i : M →* H) (hi : Function.Injective i)
    (A Y : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : A ≤ i.range) (hY : Y ≤ i.range)
    (hcard : 4 ≤ ((pCore 2 M).map i).relIndex A)
    (hAA : ⁅(D).map i,A⁆ ≤ centralizer (A : Set H))
    (hAY : ⁅(D).map i,A⁆ ≤ centralizer (Y : Set H)) :
    ⁅(D).map i,Y⁆ ≤ ⁅(D).map i,A⁆ := by
  let := h.relative_normal
  let A₀ := A.comap i
  let Y₀ := Y.comap i
  let := IsElementaryAbelian.comap_of_injective (p := 2) i hi A
  have hmA : A₀.map i = A := map_comap_eq_self hA
  have hmY : Y₀.map i = Y := map_comap_eq_self hY
  have hcard₀ : 4 ≤ Nat.card (A₀.map π) := by
    rw [CubicAction.permutation_image_card_of_two h e hz hk A₀
      (IsElementaryAbelian.isPGroup 2 A₀)]
    rw [←hmA,relIndex_map_map_of_injective _ _ hi] at hcard
    exact hcard
  have hfix (B : Subgroup H)
      (hc : ⁅(D).map i,A⁆ ≤ centralizer (B : Set H)) :
      ⁅D,A₀⁆ ≤ centralizer (B.comap i : Set M) := by
    intro x hx b hb
    apply hi
    simp only [map_mul]
    apply hc
    · rw [←hmA,←map_commutator]
      exact mem_map_of_mem i hx
    · exact hb
  have hh := map_mono (f := i) (natural_cover_commutator_control h e hz hk hnat A₀ Y₀ hcard₀
    (hfix A hAA) (hfix Y hAY))
  simpa only [map_commutator,hmA,hmY] using hh

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
