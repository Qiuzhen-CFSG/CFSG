module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Swapped.CubicBarrier
public import CFSG.Quasithin.ChapterD.Section02.Inheritance
public import Theory.Representation.BinaryOffender.CubicOrbitRestriction

/-!
# Starred actors on normalized odd rank-one components

A single starred cubic actor retains ratio at most two on each moving
homogeneous orbit quotient by D.2.7. The literal component centralizer is
the kernel, and the original component maps isomorphically onto F*.
Identifying this kernel with the two-core also transports SQTK through the
correct quotient. CubicBarrier then proves that a normalized component in
the remaining prime congruence classes must be centralized by the actor.
No irreducibility of the entire orbit is assumed. CommonActor supplies the
original pure-point application.

Source: Aschbacher--Smith A.1.42, D.2.7 and 12.1.4,
printed pp.32,190,790--791 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
open ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding Representation.BinaryOffender.Homogeneous
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Restriction of the same starred cubic actor to a normalized component's
homogeneous orbit, retaining the exact quotient and action kernel. -/
theorem normalized_component_cubic_section
    {Q U : Type*} [Group Q] [Finite Q] [AddCommGroup U]
    [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) Q U) (hf : Function.Injective ρ)
    (E C : Subgroup Q) [IsSimpleGroup C] [IsQuasisimple C]
    (hE : E ∈ ChapterD.QhatStar ρ)
    (hn : E ≤ normalizer (C : Set Q))
    (hm : ¬ E ≤ centralizer (C : Set Q)) :
    ∃ I, ∃ hI : IsIrrPlusWith ρ C E I,
      let σ := orbitSectionRepresentation ρ hI
      let q := KernelQuotient.projection σ
      let A := (E.subgroupOf (C ⊔ E)).map q
      σ.ker = centralizer (C.subgroupOf (C ⊔ E) : Set (C ⊔ E : Subgroup Q)) ∧
      generalizedFitting (KernelQuotient.Actor σ) = (C.subgroupOf (C ⊔ E)).map q ∧
      Nonempty (C ≃* (C.subgroupOf (C ⊔ E)).map q) ∧
      IsElementaryTwo A ∧ IsCubic (KernelQuotient.action σ) A ∧
      actionRatio (KernelQuotient.action σ) A ≤ 2 ∧
      cubicRatio (KernelQuotient.action σ) ≤ 2 := by
  let : IsElementaryAbelian 2 E := hE.1.2.1.2
  have hp : IsPGroup 2 E := IsElementaryAbelian.isPGroup 2 E
  have hne : C ≠ ⊥ := by
    intro he
    have hs : Subsingleton C := he ▸ inferInstance
    exact not_subsingleton C hs
  have hz : center C = ⊥ :=
    (inferInstance : (center C).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative C (center_eq_top_iff.mp he))
  obtain ⟨I,hI⟩ := exists_isIrrPlusWith_of_faithful ρ hf C E hne hn hp
  let W := orbitSpan ρ E I
  let σ := orbitSectionRepresentation ρ hI
  let q := KernelQuotient.projection σ
  let A := (E.subgroupOf (C ⊔ E)).map q
  have hk := orbitSection_kernel_eq_centralizer ρ hz hp hI
  have hmove : ¬ W ≤ fixedSpace ρ E := by
    intro hh
    apply hm
    intro a ha
    let aJ : (C ⊔ E : Subgroup Q) := ⟨a,(show E ≤ C ⊔ E from le_sup_right) ha⟩
    have haK : aJ ∈ σ.ker := by
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := ((fixedSpace ρ C).comap W.subtype).mkQ_surjective v
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      exact Subtype.ext (hh w.property ⟨a,ha⟩)
    have hac : aJ ∈ centralizer (C.subgroupOf (C ⊔ E) : Set (C ⊔ E : Subgroup Q)) :=
      hk ▸ haK
    intro c hc
    exact congrArg Subtype.val (hac ⟨c,(show C ≤ C ⊔ E from le_sup_left) hc⟩ hc)
  have hw : E ≤ subspaceStabilizer ρ W := orbitSpan_invariant ρ E I
  have hr := ChapterD.RPlusBound.restricted ρ
    (show E ∈ ChapterD.RPlusBound ρ 2 from
      ⟨⟨hE.1.2.1,hE.1.2.2.2.trans_le hE.1.1⟩,ChapterD.QhatStar.mem_RPlus ρ hE⟩)
    W hw hmove
  have hratio := orbitSection_cubicRatio_le_restricted_actionRatio ρ hp hI
    le_rfl hE.1.2.1 hE.1.2.2.1 hmove
  -- The transported actor itself, rather than a new minimum, has the same image rank.
  have hAJ : E ≤ C ⊔ E := le_sup_right
  let : IsElementaryAbelian 2 (E.subgroupOf (C ⊔ E)) :=
    IsElementaryAbelian.subgroupOf hAJ
  have hrank : rank A = rank (restrictedSubgroup ρ W E) :=
    orbitSection_image_rank ρ hp hI le_rfl
  have hA : IsElementaryTwo A := by
    refine ⟨?_,IsElementaryAbelian.map q⟩
    intro he
    have hh := hr.1.rank_pos
    have hzA : rank A = 0 := by simp [rank,he]
    omega
  let R := invariantSubspace ρ (C ⊔ E) W
    (orbitSection_stable ρ hI.normalizes hI.isIrrPlus)
  let N := centralSectionFixedSubspace ρ C (C ⊔ E) W
    (orbitSection_stable ρ hI.normalizes hI.isIrrPlus)
    (sup_le C.le_normalizer hI.normalizes)
  have hcR : IsCubic R.toRepresentation (E.subgroupOf (C ⊔ E)) :=
    cubic_subrepresentation (ρ.comp (C ⊔ E).subtype) R
      (fun a ha b hb c hc v => hE.1.2.2.1 a ha b hb c hc v)
  have hcσ : IsCubic σ (E.subgroupOf (C ⊔ E)) :=
    cubic_quotient R.toRepresentation N hcR
  have hcA : IsCubic (KernelQuotient.action σ) A :=
    hcσ.map_equivariant σ (KernelQuotient.action σ) q
      (LinearEquiv.refl _ _) (fun _ _ => rfl)
  have hfixed : fixedSpace R.toRepresentation (E.subgroupOf (C ⊔ E)) =
      fixedSpace (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W E) := by
    rw [fixedSpace_restrictedSubgroup ρ W E hw]
    ext v
    constructor
    · intro hv a
      exact congrArg Subtype.val (hv ⟨⟨a,hAJ a.property⟩,a.property⟩)
    · intro hv a
      exact Subtype.ext (hv ⟨a,a.property⟩)
  have hd : fixedCodim (KernelQuotient.action σ) A ≤
      fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W E) := by
    rw [←fixedCodim_map_equivariant σ (KernelQuotient.action σ) q
      (LinearEquiv.refl _ _) (fun _ _ => rfl) (E.subgroupOf (C ⊔ E))]
    have hq := fixedCodim_quotient_add_subrepresentation_le R.toRepresentation N
      (E.subgroupOf (C ⊔ E))
    have he : fixedCodim R.toRepresentation (E.subgroupOf (C ⊔ E)) =
        fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W E) :=
      congrArg (fun U => Module.finrank (ZMod 2) (W ⧸ U)) hfixed
    exact (Nat.le_add_right _ _).trans (hq.trans_eq he)
  have hbound : actionRatio (KernelQuotient.action σ) A ≤ 2 := by
    apply le_trans ?_ hr.2
    unfold actionRatio
    rw [hrank]
    exact ENNReal.div_le_div_right (by exact_mod_cast hd) _
  exact ⟨I,hI,hk,orbitSection_faithful_generalizedFitting ρ hz hp hI,
    ⟨orbitSectionComponentEquiv ρ hz hI⟩,hA,hcA,hbound,hratio.trans hr.2⟩

/-- A starred cubic actor centralizes every normalized component of the
remaining odd rank-one type. -/
theorem normalized_rank_one_component_centralized
    {Q U : Type*} [Group Q] [Finite Q] [AddCommGroup U]
    [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) Q U) (hf : Function.Injective ρ)
    (hsq : IsSQTK KnownSimple.IsKnownSimple Q)
    (E C : Subgroup Q) [IsSimpleGroup C] [IsQuasisimple C]
    (hE : E ∈ ChapterD.QhatStar ρ) (hn : E ≤ normalizer (C : Set Q))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSL C 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13) :
    E ≤ centralizer (C : Set Q) := by
  by_contra hc
  obtain ⟨I,hI,_,hfit,⟨e⟩,_,_,_,hbound⟩ :=
    normalized_component_cubic_section ρ hf E C hE hn hc
  let σ := orbitSectionRepresentation ρ hI
  let q := KernelQuotient.projection σ
  let M := (C.subgroupOf (C ⊔ E)).map q
  let : M.Normal := by
    change ((C.subgroupOf (C ⊔ E)).map (KernelQuotient.projection σ)).Normal
    rw [←hfit]
    infer_instance
  let : IsSimpleGroup M := e.symm.isSimpleGroup
  let : IsQuasisimple M := IsQuasisimple.of_mulEquiv e
  have hz : center M = ⊥ :=
    (inferInstance : (center M).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative M (center_eq_top_iff.mp he))
  have hcent : centralizer (M : Set (KernelQuotient.Actor σ)) = ⊥ := by
    apply bot_unique
    intro x hx
    have hxM : x ∈ M :=
      (hfit ▸ centralizer_generalizedFitting_le (KernelQuotient.Actor σ)) hx
    have hxZ : (⟨x,hxM⟩ : M) ∈ center M :=
      mem_center_iff.mpr (fun y => Subtype.ext (hx y y.property))
    exact congrArg (fun z : M => (z : KernelQuotient.Actor σ)) (mem_bot.mp (hz ▸ hxZ))
  have hs := hsq.subgroup (C ⊔ E)
  have hzC : center C = ⊥ :=
    (inferInstance : (center C).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative C (center_eq_top_iff.mp he))
  let : IsElementaryAbelian 2 E := hE.1.2.1.2
  have hk : (actionHom σ).ker = pCore 2 (C ⊔ E : Subgroup Q) :=
    (actionHom_ker_eq σ).trans (orbitSection_kernel_eq_twoCore ρ hzC
      (IsElementaryAbelian.isPGroup 2 E) hI)
  have hs' : IsSQTK KnownSimple.IsKnownSimple (KernelQuotient.Actor σ) :=
    (IsSQTK.equiv (QuotientGroup.quotientMulEquivOfEq hk)).mpr
      ⟨quotient_stronglyQuasithin hs.stronglyQuasithin,hs.isKGroup.quotient _⟩
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
  have hm' : ClassicalGroup.IsPSL M 2 p :=
    ⟨F,inferInstance,inferInstance,hF,⟨e.symm.trans a⟩⟩
  exact (not_lt_of_ge hbound) (normal_rank_one_cubic_barrier
    (KernelQuotient.action σ) (KernelQuotient.faithful σ) hs' M hcent hp ho hm' hmod)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
