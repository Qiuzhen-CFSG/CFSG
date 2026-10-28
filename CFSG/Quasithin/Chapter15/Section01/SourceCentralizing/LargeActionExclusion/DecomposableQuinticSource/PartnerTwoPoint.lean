module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.PartnerTwoFourLines
public import Theory.GroupAction.NormalFivePointStabilizer
public import Theory.GroupTheory.PResidual.QuotientCard

/-!
# Point stabilizers on the original quintic support

A nonzero point in a faithful normal-five support has a two-group stabilizer
image. Consequently a two-perfect actor fixing that point fixes the whole
support. This is the action-level input for transporting the original marked
residual to the actual support line in the second four-group.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u

private theorem quintic_point_image_two
    {D W : Type u} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} (F : Factor ρ)
    (hN : subspaceStabilizer ρ F.space ≤ normalizer (F.actor : Set D))
    (l : CyclicSource.LocalGeneration F.action) (hm : CyclicSource.DihedralMarking l 5 2)
    (A : Subgroup D)
    (w : W) (hw : w ∈ F.space) (hw0 : w ≠ 0)
    (hAw : ∀ a ∈ A, ρ a w = w) : IsPGroup 2 (restrictedSubgroup ρ F.space A) := by
  obtain ⟨k, J, hk, _, _, hn, _⟩ := F.faithful_normal_support_image_data hN
  let H := k.range
  let : H.Normal := hn
  let : FiniteDimensional (ZMod 2) F.space := Module.Finite.of_surjective J.toLinearMap J.surjective
  let e : F.Carrier ≃* H := MonoidHom.ofInjective hk
  let P := (pResidual 2 H).map H.subtype
  have hP : Nat.card P = 5 := by
    rw [card_map_of_injective H.subtype_injective,
      ← map_pResidual_of_surjective 2 e.toMonoidHom e.surjective,
      card_map_of_injective (f := e.toMonoidHom) e.injective, ← l.kernel_eq_twoResidual]
    exact hm.card_kernel
  let σ := subspaceImageRepresentation ρ F.space
  let : Finite F.space := Module.finite_of_finite (ZMod 2)
  let := BinaryGroupAction.action σ
  let := BinaryGroupAction.faithful σ (subspaceImageRepresentation_injective ρ F.space)
  let v : Multiplicative F.space := Multiplicative.ofAdd ⟨w, hw⟩
  have hv : v ≠ 1 := fun he => hw0 (congrArg Subtype.val he)
  have hV : Nat.card (Multiplicative F.space) = 16 := by
    change Nat.card F.space = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      J.finrank_eq.symm.trans hm.dimension]
    rfl
  have hcard := Theory.GroupAction.card_point_stabilizer_dvd_four_of_normal_five P hP hV v hv
  have htwo : IsPGroup 2 (MulAction.stabilizer (subspaceActionImage ρ F.space) v) :=
    IsPGroup.of_card_dvd_pow (n := 2) hcard
  have hle : restrictedSubgroup ρ F.space A ≤
      MulAction.stabilizer (subspaceActionImage ρ F.space) v := by
    rintro g ⟨a, ha, rfl⟩
    apply Subtype.ext
    change ρ a w = w
    exact hAw a ha
  exact htwo.to_le hle

private theorem quintic_point_residual_fixed
    {D W : Type u} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} (F : Factor ρ)
    (hN : subspaceStabilizer ρ F.space ≤ normalizer (F.actor : Set D))
    (l : CyclicSource.LocalGeneration F.action) (hm : CyclicSource.DihedralMarking l 5 2)
    (A : Subgroup D) (hAS : A ≤ subspaceStabilizer ρ F.space)
    (w : W) (hw : w ∈ F.space) (hw0 : w ≠ 0)
    (hAw : ∀ a ∈ A, ρ a w = w) :
    (pResidual 2 A).map A.subtype ≤ subspaceKernel ρ F.space A := by
  let f := subgroupActionHom ρ F.space A hAS
  have htwo : IsPGroup 2 f.range := by
    rw [show f.range = restrictedSubgroup ρ F.space A from subgroupActionHom_range ρ F.space A hAS]
    exact quintic_point_image_two F hN l hm A w hw hw0 hAw
  have hk : pResidual 2 A ≤ f.ker := fun a ha =>
    congrArg Subtype.val (pResidual_le_ker_of_isPGroup 2 f.rangeRestrict htwo ha)
  exact (map_mono hk).trans_eq (subgroupActionHom_ker ρ F.space A hAS)

variable {G : Type u} [Group G] [Finite G]

private theorem point_centralizer_le_supportNormalizer
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (a : G)
    (ha : a ∈ plane V (c.ambientFactor d s.first).space) (ha1 : a ≠ 1) :
    M ⊓ centralizer ({a} : Set G) ≤
      normalizer (plane V (c.ambientFactor d s.first).space : Set G) := by
  let V₁ := plane V (c.ambientFactor d s.first).space
  let V₂ := plane V (c.ambientFactor d s.second).space
  let fM := (actionHom M V hn).rangeRestrict

  intro x hx
  let y : M := ⟨x, hx.1⟩
  have hm : V₁.map (MulAut.conj x).toMonoidHom =
      plane V (c.ambientFactor d (π (fM y) s.first)).space :=
    (plane_conjugate hn _ y).trans (congrArg (plane V) (hs _ s.first))
  rcases s.covers (π (fM y) s.first) with hi | hi
  · exact mem_normalizer_iff_map_conj_eq.mpr
      (hm.trans (congrArg (fun k => plane V (c.ambientFactor d k).space) hi))
  · have he : V₁.map (MulAut.conj x).toMonoidHom = V₂ :=
      hm.trans (congrArg (fun k => plane V (c.ambientFactor d k).space) hi)
    have hxa : (MulAut.conj x) a = a := by
      change x*a*x⁻¹ = a
      rw [← hx.2 a (Set.mem_singleton a), mul_inv_cancel_right]
    have haB : a ∈ V₂ := hxa ▸ (he ▸ mem_map_of_mem (MulAut.conj x).toMonoidHom ha)
    exact (ha1 (mem_bot.mp (s.disjoint.le ⟨ha, haB⟩))).elim

/-- Fixing a nonidentity point of the original first support forces the
whole two-residual of its literal module centralizer to fix that support. -/
theorem DecomposableMarker.ThompsonPair.quintic_point_residual_centralizes_support
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hfive : s.prime = 5) (a : G)
    (ha : a ∈ plane V (c.ambientFactor d s.first).space) (ha1 : a ≠ 1) :
    let C := M ⊓ centralizer ({a} : Set G)
    (pResidual 2 C).map C.subtype ≤
      centralizer (plane V (c.ambientFactor d s.first).space : Set G) := by
  intro C
  let D := internalActionImage M V hn
  let ρ := imageRepresentation M V hn
  let F := c.ambientFactor d s.first
  let V₁ := plane V F.space
  let V₂ := plane V (c.ambientFactor d s.second).space
  let fM : M →* D := (actionHom M V hn).rangeRestrict
  let f : C →* D := fM.comp (inclusion (show C ≤ M from inf_le_left))
  let A := f.range
  have hCN : C ≤ normalizer (V₁ : Set G) :=
    point_centralizer_le_supportNormalizer hn c d s π hs a ha ha1
  have hAS : A ≤ subspaceStabilizer ρ F.space := by
    rintro g ⟨x, rfl⟩
    apply (subspace_map_eq_iff ρ F.space (f x)).mp
    apply plane_injective V
    exact (plane_conjugate hn F.space (inclusion (show C ≤ M from inf_le_left) x)).symm.trans
      (mem_normalizer_iff_map_conj_eq.mp (hCN x.property))
  obtain ⟨va, hva, hvaG⟩ := ha
  change (va : G) = a at hvaG
  let w : Additive V := Additive.ofMul va
  have hw : w ∈ F.space := hva
  have hw0 : w ≠ 0 := by
    intro he
    apply ha1
    exact hvaG.symm.trans (congrArg (fun v : Additive V => (v.toMul : G)) he)
  have hAw : ∀ g ∈ A, ρ g w = w := by
    rintro g ⟨x, rfl⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    change (x : G)*(va : G)*(x : G)⁻¹ = va
    rw [hvaG, ← x.property.2 a (Set.mem_singleton a), mul_inv_cancel_right]
  have hm : CyclicSource.DihedralMarking (s.marking s.first) 5 2 := by
    simpa only [hfive] using s.dihedral s.first
  have hfixed := quintic_point_residual_fixed F
    (c.support_stabilizer_normalizes_actor d π hp hs s.first) (s.marking s.first) hm
    A hAS w hw hw0 hAw
  rintro x ⟨r, hr, rfl⟩ v ⟨vv, hvv, rfl⟩
  have hrA : f.rangeRestrict r ∈ pResidual 2 A :=
    map_pResidual_le 2 f.rangeRestrict (mem_map_of_mem f.rangeRestrict hr)
  have he := (hfixed (mem_map_of_mem A.subtype hrA)).2 (Additive.ofMul vv) hvv
  have heG := congrArg (fun v : Additive V => (v.toMul : G)) he
  change (r : G)*(vv : G)*(r : G)⁻¹ = vv at heG
  exact (mul_inv_eq_iff_eq_mul.mp heG).symm

/-- A nonidentity point of the original marked plane has exactly the same
embedded two-residual as that plane's centralizer in M. -/
theorem DecomposableMarker.ThompsonPair.quintic_point_residual_eq_marked
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hfive : s.prime = 5) (a : G)
    (ha : a ∈ thompsonPlane T V (c.ambientFactor d s.first).space) (ha1 : a ≠ 1) :
    let C := M ⊓ centralizer ({a} : Set G)
    let C₁ := M ⊓ centralizer
      (thompsonPlane T V (c.ambientFactor d s.first).space : Set G)
    (pResidual 2 C).map C.subtype = (pResidual 2 C₁).map C₁.subtype := by
  intro C C₁
  apply (embedded_pResidual_eq_of_le_of_residual_le 2
    (show C₁ ≤ C from inf_le_inf_left M (centralizer_le
      (Set.singleton_subset_iff.mpr ha))) ?_).symm
  exact le_inf ((map_subtype_le _).trans inf_le_left)
    ((s.quintic_point_residual_centralizes_support hn c d π hp hs hfive a ha.1 ha1).trans
      (centralizer_le (show thompsonPlane T V (c.ambientFactor d s.first).space ≤
        plane V (c.ambientFactor d s.first).space from inf_le_left)))

/-- The original quotient residual order is preserved at every nonidentity
point of the marked plane, with the same module-centralizer denominator. -/
theorem DecomposableMarker.ThompsonPair.quintic_point_quotient_residual_card
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hfive : s.prime = 5) (a : G)
    (ha : a ∈ thompsonPlane T V (c.ambientFactor d s.first).space) (ha1 : a ≠ 1) :
    let C₁ := M ⊓ centralizer
      (thompsonPlane T V (c.ambientFactor d s.first).space : Set G)
    let N := M ⊓ centralizer (V : Set G)
    letI := caseI_module_centralizer_normal (Z1 := zpowers a) hn
    letI := caseI_module_centralizer_normal
      (Z1 := thompsonPlane T V (c.ambientFactor d s.first).space) hn
    Nat.card (pResidual 2 ((M ⊓ centralizer (zpowers a : Set G) : Subgroup G) ⧸
      N.subgroupOf (M ⊓ centralizer (zpowers a : Set G)))) =
      Nat.card (pResidual 2 (C₁ ⧸ N.subgroupOf C₁)) := by
  intro C₁ N
  let : (N.subgroupOf C₁).Normal := caseI_module_centralizer_normal hn
  let : (N.subgroupOf (M ⊓ centralizer (zpowers a : Set G))).Normal :=
    caseI_module_centralizer_normal hn
  have he := s.quintic_point_residual_eq_marked hn c d π hp hs hfive a ha ha1
  have hC : M ⊓ centralizer (zpowers a : Set G) = M ⊓ centralizer ({a} : Set G) := by
    simp only [zpowers_eq_closure, centralizer_closure]
  apply card_quotient_pResidual_eq_of_embedded_eq 2
  exact (congrArg (fun K : Subgroup G => (pResidual 2 K).map K.subtype) hC).trans he

/-- If the Sylow support stabilizer fixes a chosen point, its literal
point centralizer is Sylow in the point centralizer in M. -/
theorem DecomposableMarker.ThompsonPair.quintic_point_local_sylow
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (a : G)
    (ha : a ∈ plane V (c.ambientFactor d s.first).space) (ha1 : a ≠ 1)
    (he : (T : Subgroup G) ⊓ centralizer ({a} : Set G) =
      (T : Subgroup G) ⊓ normalizer (plane V (c.ambientFactor d s.first).space : Set G)) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({a} : Set G))
      (M ⊓ centralizer ({a} : Set G)) := by
  let A := plane V (c.ambientFactor d s.first).space
  let H := M ⊓ normalizer (A : Set G)
  let C := M ⊓ centralizer ({a} : Set G)
  have hHn : (H.subgroupOf M).Normal := by
    have hh : H.subgroupOf M = (normalizer (A : Set G)).subgroupOf M := by
      ext x
      exact and_iff_right x.property
    rw [hh]
    exact s.toSupportPair.supportNormalizer_normal hn c d π hs
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) M := ⟨T.subtype hTM, by simp [hTM]⟩
  have hTH := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hT
    (show H ≤ M from inf_le_left) hHn.isSubnormal
  have hSC : (T : Subgroup G) ⊓ H ≤ C := by
    intro x hx
    exact ⟨hTM hx.1, (he.ge ⟨hx.1, hx.2.2⟩).2⟩
  have hCH : C ≤ H := le_inf inf_le_left
    (point_centralizer_le_supportNormalizer hn c d s π hs a ha ha1)
  have hEq : (T : Subgroup G) ⊓ H = (T : Subgroup G) ⊓ centralizer ({a} : Set G) := by
    rw [he]
    exact le_antisymm (fun x hx => ⟨hx.1, hx.2.2⟩)
      (fun x hx => ⟨hx.1, hTM hx.1, hx.2⟩)
  exact hEq ▸ hTH.restrict hSC hCH

end CFSG.Quasithin.Chapter15.Section01
