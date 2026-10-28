module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.CoreCentralizer
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.PResidual.AutomorphismCentralizer

/-!
# Sylow and residual control in the full decomposable marked centralizer

Every element preserving the nontrivial Thompson marking preserves its
original support. The support stabilizer is the kernel of the action on
the two supports, hence normal in M. Sylow restriction through this
stabilizer, the marked normalizer and its centralizer proves that the
literal C_T(Z₁) is Sylow in C_M(Z₁).

The opposite original prime kernel is the residual of the centralizer
inside Jhat. It is therefore normalized by the full marked centralizer,
and its automorphism group is a two-group for either prime three or five.
Consequently the full residual contains and centralizes this same kernel.
Transport through the original action gives divisibility of the residual
order in C_M(Z₁)/C_M(V), the fixed and moved support bounds, and the central
seed containment needed for component selection.

The full residual order, marker generation and normality in T still need
their source arguments. The source consumer in the parent Decomposable
module supplies the Thompson marking and image equality from the actual
eight-dimensional prepared action.

Source: Aschbacher--Smith 15.1.16(a)--18, printed pp.1092--1093.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition Section03
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The literal support stabilizer is normal in M. -/
theorem SupportPair.supportNormalizer_normal {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : SupportPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space) :
    ((normalizer (plane V (c.ambientFactor d s.first).space : Set G)).subgroupOf M).Normal := by
  let f : M →* internalActionImage M V hn := (actionHom M V hn).rangeRestrict
  have hi := (c.ambient_spaces_independent d).injective (c.ambient_space_ne_bot d)
  have he : (normalizer (plane V (c.ambientFactor d s.first).space : Set G)).subgroupOf M =
      (π.comp f).ker := by
    ext x
    have hm : (plane V (c.ambientFactor d s.first).space).map (MulAut.conj (x : G)).toMonoidHom =
        plane V (c.ambientFactor d (π (f x) s.first)).space :=
      (plane_conjugate hn _ x).trans (congrArg (plane V) (hs (f x) s.first))
    change (x : G) ∈ normalizer (plane V (c.ambientFactor d s.first).space : Set G) ↔ π (f x) = 1
    rw [mem_normalizer_iff_map_conj_eq]
    rw [MulEquiv.toMonoidHom_eq_coe] at hm
    rw [hm]
    rw [(plane_injective V).eq_iff,hi.eq_iff]
    constructor
    · intro hfirst
      have hsecond : π (f x) s.second = s.second := by
        rcases s.covers (π (f x) s.second) with h | h
        · exact False.elim (s.distinct ((π (f x)).injective (hfirst.trans h.symm)))
        · exact h
      ext k
      rcases s.covers k with rfl | rfl
      · exact hfirst
      · exact hsecond
    · intro h
      exact congrArg (fun a : Equiv.Perm d.Index => a s.first) h
  rw [he]
  infer_instance

/-- A nontrivial marked subgroup cannot be preserved by an element
exchanging the two disjoint supports. -/
theorem ThompsonPair.markedNormalizer_le_supportNormalizer {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space) :
    M ⊓ normalizer (thompsonPlane T V (c.ambientFactor d s.first).space : Set G) ≤
      normalizer (plane V (c.ambientFactor d s.first).space : Set G) := by
  let A := plane V (c.ambientFactor d s.first).space
  let B := plane V (c.ambientFactor d s.second).space
  let Z := thompsonPlane T V (c.ambientFactor d s.first).space
  have hZA : Z ≤ A := inf_le_left
  intro x hx
  let y : M := ⟨x,hx.1⟩
  have hm : A.map (MulAut.conj x).toMonoidHom =
      plane V (c.ambientFactor d (π ((actionHom M V hn).rangeRestrict y) s.first)).space :=
    (plane_conjugate hn _ y).trans (congrArg (plane V) (hs _ s.first))
  rcases s.covers (π ((actionHom M V hn).rangeRestrict y) s.first) with h | h
  · apply mem_normalizer_iff_map_conj_eq.mpr
    exact hm.trans (congrArg (fun k => plane V (c.ambientFactor d k).space) h)
  · have he : A.map (MulAut.conj x).toMonoidHom = B :=
      hm.trans (congrArg (fun k => plane V (c.ambientFactor d k).space) h)
    have hz : Z.map (MulAut.conj x).toMonoidHom = Z := mem_normalizer_iff_map_conj_eq.mp hx.2
    have hZB : Z ≤ B := by
      rw [←hz,←he]
      exact map_mono hZA
    have hb : Z = ⊥ := bot_unique ((le_inf hZA hZB).trans s.disjoint.le)
    have hc := s.thompson_card s.first
    change Nat.card Z = 4 at hc
    rw [hb,card_bot] at hc
    omega

/-- The original Sylow intersection is Sylow in the full marked centralizer,
not only in the factor-product preimage. -/
theorem ThompsonPair.local_sylow {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hTM : (T : Subgroup G) ≤ M)
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space) :
    Chapter1.IsSylowIn 2
      ((T : Subgroup G) ⊓ centralizer (thompsonPlane T V (c.ambientFactor d s.first).space : Set G))
      (M ⊓ centralizer (thompsonPlane T V (c.ambientFactor d s.first).space : Set G)) := by
  let A := plane V (c.ambientFactor d s.first).space
  let Z := thompsonPlane T V (c.ambientFactor d s.first).space
  let H := M ⊓ normalizer (A : Set G)
  let N := M ⊓ normalizer (Z : Set G)
  let C := M ⊓ centralizer (Z : Set G)
  have hHn : (H.subgroupOf M).Normal := by
    have he : H.subgroupOf M = (normalizer (A : Set G)).subgroupOf M := by
      ext x
      exact and_iff_right x.property
    rw [he]
    exact s.toSupportPair.supportNormalizer_normal hn c d π hs
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) M := ⟨T.subtype hTM,by simp [hTM]⟩
  have hTH : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ H) H :=
    Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hT inf_le_left hHn.isSubnormal
  have hNH : N ≤ H := le_inf inf_le_left (s.markedNormalizer_le_supportNormalizer hn c d π hs)
  have hTN : (T : Subgroup G) ⊓ H ≤ N := by
    intro x hx
    exact ⟨hTM hx.1,(s.thompson_normalized ⟨hx.1,hx.2.2⟩).1⟩
  have hSN : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ H) N := hTH.restrict hTN hNH
  have hCN : C ≤ N := inf_le_inf_left M (Subgroup.centralizer_le_normalizer _)
  have hCn : (C.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_inf (inf_le_left.trans M.le_normalizer)
      (inf_le_right.trans (normalizer_le_normalizer_centralizer _)))
  have hSC := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSN hCN hCn.isSubnormal
  have he : ((T : Subgroup G) ⊓ H) ⊓ C = (T : Subgroup G) ⊓ centralizer (Z : Set G) := by
    apply le_antisymm
    · exact fun x hx => ⟨hx.1.1,hx.2.2⟩
    · intro x hx
      have hxC : x ∈ C := ⟨hTM hx.1,hx.2⟩
      exact ⟨⟨hx.1,hNH (hCN hxC)⟩,hxC⟩
  exact he ▸ hSC

/-- The four-subgroup is the plane of the literal intersection of fixed spaces. -/
theorem plane_thompson_intersection {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hTM : (T : Subgroup G) ≤ M)
    (hn : M ≤ normalizer (V : Set G))
    (W : Submodule (ZMod 2) (Additive V)) :
    plane V (W ⊓ fixedSpace (imageRepresentation M V hn)
      (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict)) = thompsonPlane T V W := by
  have he := Subgroup.map_inf (binarySubgroup W)
    (binarySubgroup (fixedSpace (imageRepresentation M V hn)
      (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict))) V.subtype V.subtype_injective
  exact he.trans (congrArg (fun X : Subgroup G => plane V W ⊓ X)
    (plane_thompson_image hTM hn))


/-- The full pointwise stabilizer normalizes the same original prime kernel.
Its two-residual contains and centralizes that kernel. -/
theorem ThompsonPair.full_image_residual {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hTM : (T : Subgroup G) ≤ M)
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn)) :
    let ρ := imageRepresentation M V hn
    let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
      (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict)
    let K := subspaceKernel ρ W ⊤
    let P := (s.marking s.second).kernel.map (c.ambientFactor d s.second).embedding.groupMap
    let R := (pResidual 2 K).map K.subtype
    P ≤ R ∧ K ≤ normalizer (P : Set (internalActionImage M V hn)) ∧
      R ≤ centralizer (P : Set (internalActionImage M V hn)) ∧
      s.prime ∣ Nat.card (pResidual 2 K) := by
  intro ρ W K P R
  let K0 := subspaceKernel ρ W (Jhat ρ)
  have hK : K0 ≤ K := fun x hx => ⟨trivial,hx.2⟩
  have he : (pResidual 2 K0).map K0.subtype = P := (s.core_centralizer hTM hn c d hJ).2
  have hPR : P ≤ R := he ▸ embedded_pResidual_mono 2 hK
  have hnorm : K ≤ normalizer (P : Set (internalActionImage M V hn)) := by
    rw [←he]
    apply le_trans ?_ (normalizer_le_normalizer_characteristic_image K0 (pResidual 2 K0))
    have hK0 : K0 = Jhat ρ ⊓ K := by
      ext x
      exact ⟨fun hx => ⟨hx.1,trivial,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
    rw [hK0]
    let : (Jhat ρ).Normal := Jhat_normal ρ
    exact le_normalizer_inf le_normalizer_of_normal K.le_normalizer
  have hcard : Nat.card P = s.prime := s.kernel_card s.second
  have hp : s.prime.Prime := by
    rcases s.prime_cases with h | h <;> rw [h] <;> decide
  let : Fact s.prime.Prime := ⟨hp⟩
  let : IsCyclic P := isCyclic_of_prime_card hcard
  have haut : IsPGroup 2 (MulAut P) := by
    rcases s.prime_cases with h | h
    · apply IsPGroup.of_card (n := 1)
      rw [IsCyclic.card_mulAut,hcard,h]
      decide
    · apply IsPGroup.of_card (n := 2)
      rw [IsCyclic.card_mulAut,hcard,h]
      decide
  refine ⟨hPR,hnorm,embedded_pResidual_le_centralizer_of_aut_isPGroup 2 K P hnorm haut,?_⟩
  have hd := card_dvd_of_le hPR
  rw [hcard,card_map_of_injective K.subtype_injective] at hd
  exact hd

/-- The same prime divides the residual order in the literal full quotient
C_M(Z₁)/C_M(V). The action kernel is not replaced by a two-core. -/
theorem ThompsonPair.full_quotient_residual_prime_dvd {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hTM : (T : Subgroup G) ≤ M)
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn)) :
    let Z := thompsonPlane T V (c.ambientFactor d s.first).space
    let C := M ⊓ centralizer (Z : Set G)
    letI := caseI_module_centralizer_normal (Z1 := Z) hn
    s.prime ∣ Nat.card (pResidual 2
      (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) := by
  let ρ := imageRepresentation M V hn
  let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
    (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict)
  let K := subspaceKernel ρ W ⊤
  let qcard (A : Subgroup G) : ℕ :=
    let C := M ⊓ centralizer (A : Set G)
    letI := caseI_module_centralizer_normal (Z1 := A) hn
    Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C))
  have hW : plane V W = thompsonPlane T V (c.ambientFactor d s.first).space :=
    plane_thompson_intersection hTM hn _
  have he : qcard (plane V W) = Nat.card (pResidual 2 K) :=
    ExtraspecialMarker.residual_card M V hn W
  change s.prime ∣ qcard (thompsonPlane T V (c.ambientFactor d s.first).space)
  rw [←congrArg qcard hW,he]
  exact (s.full_image_residual hTM hn c d hJ).2.2.2

/-- The full marked centralizer retains the original opposite odd kernel
in its residual image. Thus its fixed subgroup lies in the first support
and its moved subgroup contains the whole second support. -/
theorem ThompsonPair.full_residual_bounds {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hTM : (T : Subgroup G) ≤ M)
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn)) :
    let Z := thompsonPlane T V (c.ambientFactor d s.first).space
    let C := M ⊓ centralizer (Z : Set G)
    let R := (pResidual 2 C).map C.subtype
    V ⊓ centralizer (R : Set G) ≤ plane V (c.ambientFactor d s.first).space ∧
      plane V (c.ambientFactor d s.second).space ≤ ⁅V,R⁆ ∧
      centralInvolutions T ⊓ V ≤ Z ⊔ ⁅V,R⁆ := by
  let ρ := imageRepresentation M V hn
  let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
    (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict)
  let K := subspaceKernel ρ W ⊤
  have hP := (s.full_image_residual hTM hn c d hJ).1
  have hfixed : fixedSpace ρ ((pResidual 2 K).map K.subtype) ≤
      (c.ambientFactor d s.first).space := by
    rw [←s.kernel_fixed s.second s.first s.distinct.symm]
    exact fixedSpace_antitone ρ hP
  have hmoved : (c.ambientFactor d s.second).space ≤
      subspaceCommutator ρ ⊤ ((pResidual 2 K).map K.subtype) := by
    rw [←s.kernel_moved s.second]
    apply Submodule.span_mono
    rintro _ ⟨g,hg,v,hv,rfl⟩
    exact ⟨g,hP hg,v,hv,rfl⟩
  have hW : plane V W = thompsonPlane T V (c.ambientFactor d s.first).space :=
    plane_thompson_intersection hTM hn _
  intro Z C R
  have hspaces :
      (V ⊓ centralizer (R : Set G)).subgroupOf V =
        binarySubgroup (fixedSpace ρ ((pResidual 2 K).map K.subtype)) ∧
      ⁅V,R⁆.subgroupOf V =
        binarySubgroup (subspaceCommutator ρ ⊤ ((pResidual 2 K).map K.subtype)) := by
    have hR : R = (pResidual 2 (M ⊓ centralizer (plane V W : Set G) : Subgroup G)).map
        (M ⊓ centralizer (plane V W : Set G)).subtype := by
      apply congrArg (fun D : Subgroup G => (pResidual 2 D).map D.subtype)
      exact congrArg (fun A : Subgroup G => M ⊓ centralizer (A : Set G)) hW.symm
    rw [hR]
    exact ExtraspecialMarker.residual_spaces M V hn W
  have hRnorm : R ≤ normalizer (V : Set G) :=
    ((map_subtype_le _).trans inf_le_left).trans hn
  have hRle : ⁅V,R⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp hRnorm
  have hF : V ⊓ centralizer (R : Set G) ≤ plane V (c.ambientFactor d s.first).space := by
    rw [←map_subgroupOf_eq_of_le (show V ⊓ centralizer (R : Set G) ≤ V from inf_le_left),hspaces.1]
    exact map_mono (show binarySubgroup (fixedSpace ρ ((pResidual 2 K).map K.subtype)) ≤
      binarySubgroup (c.ambientFactor d s.first).space from hfixed)
  have hB : plane V (c.ambientFactor d s.second).space ≤ ⁅V,R⁆ := by
    rw [←map_subgroupOf_eq_of_le hRle,hspaces.2]
    exact map_mono (show binarySubgroup (c.ambientFactor d s.second).space ≤
      binarySubgroup (subspaceCommutator ρ ⊤ ((pResidual 2 K).map K.subtype)) from hmoved)
  refine ⟨hF,hB,?_⟩
  have hseed : centralInvolutions T ⊓ V ≤ thompsonFixed T V := by
    intro z hz
    exact ⟨hz.2,fun j hj => Section03.centralInvolutions_le_centralizer_sylow T hz.1 j
      (ChapterB.thompsonJ_le _ _ hj)⟩
  apply hseed.trans
  rw [s.thompson_split]
  exact sup_le_sup le_rfl (inf_le_left.trans hB)

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
